//! Adversarial soundness probes for [`prove_by_nat_induction`].
//!
//! The corpus suite (`nat_induction_corpus.rs`) measures the route on twelve
//! benchmark-shaped instances. This suite attacks it: every probe here is a
//! shape chosen because a *plausible* implementation of the recogniser would
//! get it wrong, and each carries a hand-derived ground truth plus the witness
//! or the theorem that justifies it.
//!
//! The rule the route must obey is one-directional and absolute: it may return
//! `Some(Unsat)` only for an assertion set that really is unsatisfiable, and it
//! may decline (`None`) whenever it likes. So every probe asserts
//! `verdict != unsat` when the truth is `sat`, and merely *records* what
//! happens on the `unsat` probes — a decline there is incompleteness, which is
//! allowed.
//!
//! The guard family is the part that has already produced a wrong `unsat`
//! (`a32280b6a`): ℕ-induction establishes `∀n ≥ 0. C(n)`, so it refutes
//! `¬∀n. G(n) → C(n)` **only when `G(n)` implies `n ≥ 0`**. Every probe whose
//! name starts `guard_` varies `G` around that condition.
#![cfg(feature = "full")]

use std::sync::mpsc::{self, RecvTimeoutError};
use std::thread;
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, prove_by_nat_induction, solve_smtlib};

/// Per-probe wall-clock cap. Every probe is tiny; this only stops one hanging
/// obligation from taking the suite with it.
const CAP: Duration = Duration::from_secs(20);

/// What the route said, rendered for the table.
///
/// `-` is a decline. A **panic** is reported as `panic`, not folded into
/// `timeout`: an arity slip in the guard recogniser (`args[1]` on a
/// one-argument `not`) shows up exactly there, and a suite that could not tell
/// the two apart would report a crash as a slow probe.
fn induction_verdict(text: &'static str) -> String {
    let (tx, rx) = mpsc::channel();
    let handle = thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let verdict = {
                let mut parsed = match parse_script(text) {
                    Ok(p) => p,
                    Err(e) => return tx.send(format!("parse-error({e})")).ok(),
                };
                let assertions = parsed.assertions.clone();
                match prove_by_nat_induction(
                    &mut parsed.arena,
                    &assertions,
                    &SolverConfig::default(),
                    check_auto,
                ) {
                    Ok(Some(CheckResult::Unsat)) => "unsat".to_owned(),
                    Ok(Some(CheckResult::Sat(_))) => "sat".to_owned(),
                    Ok(Some(CheckResult::Unknown(_))) => "unknown".to_owned(),
                    Ok(None) => "-".to_owned(),
                    Err(e) => format!("error({e})"),
                }
            };
            tx.send(verdict).ok()
        })
        .expect("spawn probe worker");
    match rx.recv_timeout(CAP) {
        Ok(verdict) => verdict,
        // The sender was dropped without sending: the worker unwound.
        Err(RecvTimeoutError::Disconnected) => {
            let _ = handle.join();
            "panic".to_owned()
        }
        Err(RecvTimeoutError::Timeout) => "timeout".to_owned(),
    }
}

/// What the shipped front door said, rendered for the table.
///
/// Same capping and same panic/timeout distinction as [`induction_verdict`]; an
/// error is `error(…)`, which is a non-verdict and therefore never a violation
/// here — the front door legitimately reports front-end gaps that way.
fn front_door_verdict(text: &'static str) -> String {
    let (tx, rx) = mpsc::channel();
    let handle = thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let verdict = match solve_smtlib(text, &SolverConfig::default()) {
                Ok(outcome) => match outcome.result {
                    CheckResult::Unsat => "unsat".to_owned(),
                    CheckResult::Sat(_) => "sat".to_owned(),
                    CheckResult::Unknown(_) => "unknown".to_owned(),
                },
                Err(e) => format!("error({e})"),
            };
            tx.send(verdict).ok()
        })
        .expect("spawn front-door worker");
    match rx.recv_timeout(CAP) {
        Ok(verdict) => verdict,
        Err(RecvTimeoutError::Disconnected) => {
            let _ = handle.join();
            "panic".to_owned()
        }
        Err(RecvTimeoutError::Timeout) => "timeout".to_owned(),
    }
}

/// One probe: a name, the SMT-LIB text, the hand-derived truth, and why.
struct Probe {
    name: &'static str,
    text: &'static str,
    truth: &'static str,
    why: &'static str,
}

/// Every probe: the guard family, then binder structure, then implication
/// structure, then multiple goals, then the controls.
///
/// The function-shaped probes share one recurrence — `f(0) = 0` and
/// `f(k+1) = f(k) + 2` for `k ≥ 0` — which pins `f(n) = 2n` on ℕ and leaves `f`
/// entirely unconstrained below zero. That gap is what makes the unguarded
/// shapes satisfiable.
fn probes() -> Vec<Probe> {
    let mut all = guard_probes();
    all.extend(binder_and_implication_probes());
    all.extend(multi_goal_and_control_probes());
    all
}

/// The guard family: ℕ-induction establishes `∀n ≥ 0. C(n)`, so stripping a
/// guard `G` is sound exactly when `G(n)` implies `n ≥ 0`. Every probe here
/// varies `G` around that condition, and all but the last are `sat`.
fn guard_probes() -> Vec<Probe> {
    vec![
        Probe {
            name: "guard_le_zero_backwards",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (=> (<= n 0) (>= n 0)))))\n",
            truth: "sat",
            why: "`(<= n 0)` is n ≤ 0, the OPPOSITE half-line. n = -1 satisfies the \
                  guard and falsifies the conclusion, so the universal is false and \
                  its negation is true. Base (0 ≥ 0) and step (k ≥ 0 → k+1 ≥ 0) both \
                  discharge, so a recogniser that matches on `IntLe` without checking \
                  which side the zero is on answers unsat.",
        },
        Probe {
            name: "guard_ge_operands_reversed",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (=> (>= 0 n) (>= n 0)))))\n",
            truth: "sat",
            why: "`(>= 0 n)` is again n ≤ 0. Same witness n = -1. Catches a \
                  recogniser that matches `IntGe` and then looks for the variable \
                  and the zero in either position.",
        },
        Probe {
            name: "guard_ge_minus_five",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (=> (>= n (- 5)) (>= n 0)))))\n",
            truth: "sat",
            why: "n ≥ -5 does not imply n ≥ 0; witness n = -1. Catches a recogniser \
                  that accepts any `(>= n c)` without pinning c = 0.",
        },
        Probe {
            name: "guard_shifted_expression",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (=> (>= (+ n 1) 0) (>= n 0)))))\n",
            truth: "sat",
            why: "n + 1 ≥ 0 is n ≥ -1; witness n = -1. Catches a recogniser that \
                  accepts a guard whose left side merely *mentions* n.",
        },
        Probe {
            name: "guard_on_other_variable",
            text: "(set-logic LIA)\n(declare-const m Int)\n\
                   (assert (not (forall ((n Int)) (=> (>= m 0) (>= n 0)))))\n",
            truth: "sat",
            why: "The guard constrains m, not the induction variable. Model m = 0, \
                  n = -1 falsifies the body, so the negation holds. Catches a \
                  recogniser that checks the guard's *shape* but not that its \
                  variable is the bound one.",
        },
        Probe {
            name: "guard_true_constant",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (=> true (>= n 0)))))\n",
            truth: "sat",
            why: "A vacuous guard is the unguarded goal in disguise — the exact \
                  a32280b6a bug wearing an implication. Witness n = -1.",
        },
        Probe {
            name: "guard_negation_one_arg",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int)) (=> (not (= n 5)) (>= n 0)))))\n",
            truth: "sat",
            why: "n ≠ 5 does not imply n ≥ 0; witness n = -1. Also an ARITY probe: \
                  the guard is a one-argument `not`, so a recogniser that binds \
                  `(args[0], args[1])` before matching the operator panics on it.",
        },
        Probe {
            name: "guard_disjunction_two_args",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int)) (=> (or (>= n 0) (= n (- 1))) (>= n 0)))))\n",
            truth: "sat",
            why: "The guard admits n = -1, which falsifies the conclusion. A guard \
                  that is a *superset* of the non-negatives is exactly the unsound \
                  direction.",
        },
        Probe {
            name: "guard_ge_one_stricter",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 1) (= (f n) (* 2 n))))))\n",
            truth: "unsat",
            why: "f(n) = 2n holds on all of ℕ, so it holds on n ≥ 1 and the negation \
                  is unsat. Stripping `n >= 1` would be SOUND (it implies n ≥ 0), so \
                  a decline here is pure incompleteness — recorded, not required.",
        },
    ]
}

/// Binder structure and implication structure: shapes where the *recognition*
/// has to decline rather than the guard check — nested binders, a conclusion
/// carrying its own quantifier, a binder shadowing a free symbol, and
/// implications that are not the one the recogniser is looking for.
fn binder_and_implication_probes() -> Vec<Probe> {
    vec![
        // ---------------------------------------------------------------
        // Binder structure.
        // ---------------------------------------------------------------
        Probe {
            name: "two_bound_int_vars",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int) (m Int)) (=> (>= n 0) (>= m 0)))))\n",
            truth: "sat",
            why: "Two binders nest, so the induction variable's body is itself a \
                  quantifier. Witness n = 0, m = -1. The route must decline rather \
                  than induct on the outer binder and ignore the inner one.",
        },
        Probe {
            name: "second_binder_bool",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int) (b Bool)) (=> (>= n 0) (or b (>= n 1))))))\n",
            truth: "sat",
            why: "Witness n = 0, b = false. Same nesting hazard with a finite inner \
                  domain, which a `Sort::Int`-only nesting check would miss.",
        },
        Probe {
            name: "conclusion_has_own_quantifier",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (forall ((m Int)) (>= (f m) 0))))))\n",
            truth: "sat",
            why: "Take f ≡ -1: the inner universal is false, so the body is false at \
                  n = 0 and the outer universal is false. Substituting n := k+1 \
                  under a nested binder is where capture would occur, so the route \
                  must decline the shape outright.",
        },
        Probe {
            name: "binder_shadows_outer_constant",
            text: "(set-logic LIA)\n(declare-const n Int)\n(assert (>= n 0))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (> n 0)))))\n",
            truth: "sat",
            why: "The bound `n` shadows a free `n` that the other assertion \
                  constrains. Truth: the universal is false at n = 0, and the free \
                  n = 0 satisfies the first assertion. If the front end interned the \
                  binder and the constant to one symbol, the hypothesis would leak \
                  into the obligations.",
        },
        Probe {
            name: "binder_shadows_constrained_outer_constant",
            text: "(set-logic UFLIA)\n(declare-const n Int)\n(assert (= n (- 3)))\n\
                   (declare-fun f (Int) Int)\n(assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) n)))))\n",
            truth: "sat",
            why: "f(n) = 2n on ℕ, so f(1) = 2 ≠ 1 and the goal is false; n = -3 \
                  satisfies the rest. The shadowed free `n` is pinned negative, the \
                  worst case for a leak into the `n ≥ 0` reasoning.",
        },
        // ---------------------------------------------------------------
        // Implication structure.
        // ---------------------------------------------------------------
        Probe {
            name: "nested_implication_false_goal",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (=> (>= n 0) (>= n 1))))))\n",
            truth: "sat",
            why: "Witness n = 0: guard holds, inner guard holds, conclusion fails. \
                  A recogniser that peeled BOTH implications as guards would strip \
                  the goal to `n ≥ 1` and then fail its own base case, but one that \
                  peeled only the second would prove the wrong thing.",
        },
        Probe {
            name: "nary_implication_three_args",
            text: "(set-logic LIA)\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (>= n 1) (>= n 2)))))\n",
            truth: "sat",
            why: "SMT-LIB `=>` is n-ary and right-associative: this is \
                  n ≥ 0 → (n ≥ 1 → n ≥ 2). Witness n = 1. If the IR stored a \
                  three-argument implication and the recogniser read \
                  `(args[0], args[1])`, the conclusion would silently become \
                  `n ≥ 1` — provable by induction from a base that does not exist, \
                  and in any case not the goal.",
        },
    ]
}

/// Multiple goals, the positive controls, and the completeness the soundness
/// fix costs.
fn multi_goal_and_control_probes() -> Vec<Probe> {
    vec![
        // ---------------------------------------------------------------
        // Multiple goals.
        // ---------------------------------------------------------------
        Probe {
            name: "unguarded_goal_before_guarded_goal",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                   (assert (not (forall ((n Int)) (>= n 0))))\n\
                   (assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n",
            truth: "unsat",
            why: "The last assertion is refuted by the recurrence, so the set is \
                  unsat regardless of the first. Probes the recogniser's asymmetry: \
                  the unguarded goal is skipped by `continue` and never counted \
                  toward the two-goal bail-out.",
        },
        Probe {
            name: "guarded_goal_before_unguarded_goal",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                   (assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n\
                   (assert (not (forall ((n Int)) (>= n 0))))\n",
            truth: "unsat",
            why: "Same set, goals in the other order. Any difference in verdict is \
                  order-dependence in the recogniser — not unsound here, but worth \
                  pinning.",
        },
        Probe {
            name: "two_guarded_goals",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                   (assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (>= (f n) 0)))))\n",
            truth: "unsat",
            why: "Two recognised goals: the documented bail-out. Declining is \
                  correct-and-incomplete; answering unsat would mean the route chose \
                  which theorem to prove.",
        },
        // ---------------------------------------------------------------
        // Positive controls: the route must still decide these.
        // ---------------------------------------------------------------
        Probe {
            name: "control_guard_written_as_le",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (<= 0 k) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (<= 0 n) (>= (f n) 0)))))\n",
            truth: "unsat",
            why: "`(<= 0 n)` is the other accepted spelling of the guard. \
                  f(0) = 0 and each step adds 2, so f(n) ≥ 0 on ℕ.",
        },
        Probe {
            name: "control_recurrence_closed_form",
            text: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f 0) 0))\n\
                   (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                   (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n",
            truth: "unsat",
            why: "The route's reason to exist; also in the committed corpus.",
        },
        // ---------------------------------------------------------------
        // Unguarded, genuinely valid over all of Int: declining is the price
        // of the fix, and this pins that price.
        // ---------------------------------------------------------------
        Probe {
            name: "unguarded_but_valid_over_int",
            text: "(set-logic LIA)\n(assert (not (forall ((n Int)) (= (+ n 0) n))))\n",
            truth: "unsat",
            why: "True for every integer, so the negation is unsat. The route has no \
                  guard to recognise and must decline — the completeness the \
                  soundness fix costs. (`quant_valid_universal` is the route that \
                  should decide this one.)",
        },
    ]
}

#[test]
fn nat_induction_adversarial_probes_are_sound() {
    let probes = probes();
    assert!(
        probes.len() >= 20,
        "probe sweep built {} probes; a sweep that runs (nearly) nothing passes vacuously",
        probes.len()
    );

    let mut violations: Vec<String> = Vec::new();
    let mut declines = 0usize;
    let mut decided = 0usize;

    eprintln!(
        "\n| {:<44} | {:<6} | {:<9} |",
        "probe", "truth", "induction"
    );
    eprintln!("|{:-<46}|{:-<8}|{:-<11}|", "", "", "");
    for probe in &probes {
        let verdict = induction_verdict(probe.text);
        eprintln!(
            "| {:<44} | {:<6} | {:<9} |",
            probe.name, probe.truth, verdict
        );
        if verdict == "sat" || verdict == "unsat" {
            decided += 1;
            if verdict != probe.truth {
                violations.push(format!(
                    "  {}: truth {}, induction said {}\n      {}",
                    probe.name, probe.truth, verdict, probe.why
                ));
            }
        } else if verdict == "-" || verdict == "timeout" {
            // Declining and running out of clock are both "this route does not
            // apply", which it is always allowed to say.
            declines += 1;
        } else {
            // `panic`, `error(…)`, `parse-error(…)`: the route did not decline,
            // it fell over. Wiring a route that panics on a legal SMT-LIB shape
            // turns a decline into a crash at the front door.
            violations.push(format!(
                "  {}: route neither decided nor declined — it returned `{}`\n      {}",
                probe.name, verdict, probe.why
            ));
        }
    }
    eprintln!(
        "\nnat_induction_adversarial: {} probes | decided {} | declined {} | {} VIOLATIONS",
        probes.len(),
        decided,
        declines,
        violations.len()
    );

    assert!(
        violations.is_empty(),
        "SOUNDNESS FAILURE — prove_by_nat_induction is wrong on {} of {} adversarial probes:\n{}",
        violations.len(),
        probes.len(),
        violations.join("\n")
    );
}

/// The same probes through the **shipped front door**, now that the route is the
/// last rung of [`axeyum_solver::solve`]'s quantified ladder.
///
/// Testing the route in isolation was the right gate while it sat outside
/// dispatch. It is no longer sufficient: a verdict only counts as shipped if the
/// front door emits it, and the front door composes the rung with a dozen other
/// routes over an arena those routes have already rewritten. This runs the whole
/// composition and applies the identical rule — never a verdict that contradicts
/// the hand-derived truth.
#[test]
fn front_door_never_contradicts_an_adversarial_probe() {
    let probes = probes();
    let mut violations: Vec<String> = Vec::new();
    let mut decided = 0usize;

    eprintln!(
        "\n| {:<44} | {:<6} | {:<9} |",
        "probe", "truth", "front door"
    );
    eprintln!("|{:-<46}|{:-<8}|{:-<11}|", "", "", "");
    for probe in &probes {
        let verdict = front_door_verdict(probe.text);
        eprintln!(
            "| {:<44} | {:<6} | {:<9} |",
            probe.name, probe.truth, verdict
        );
        if verdict == "sat" || verdict == "unsat" {
            decided += 1;
            if verdict != probe.truth {
                violations.push(format!(
                    "  {}: truth {}, front door said {}\n      {}",
                    probe.name, probe.truth, verdict, probe.why
                ));
            }
        }
    }
    eprintln!(
        "\nnat_induction_adversarial front door: {} probes | decided {} | {} VIOLATIONS",
        probes.len(),
        decided,
        violations.len()
    );

    assert!(
        violations.is_empty(),
        "SOUNDNESS FAILURE — the front door is wrong on {} of {} adversarial probes:\n{}",
        violations.len(),
        probes.len(),
        violations.join("\n")
    );
}

/// The dispatch rung is **reached**, not merely present.
///
/// A route wired in behind a condition nothing satisfies is indistinguishable
/// from a route that was never wired in, and this repository has shipped that
/// exact shape more than once. The two positive controls are goals no other
/// route in `solve` decides — measured as `unknown` in the front-door column of
/// the `nat_induction_corpus` table — so a front-door `unsat` on them is
/// attributable to the rung and to nothing else. Delete the rung and this test
/// is what dies.
#[test]
fn front_door_decides_the_positive_controls_through_the_rung() {
    for name in [
        "control_guard_written_as_le",
        "control_recurrence_closed_form",
    ] {
        let probe = probes()
            .into_iter()
            .find(|p| p.name == name)
            .expect("control probe present");
        assert_eq!(
            front_door_verdict(probe.text),
            "unsat",
            "{name}: the front door no longer refutes a goal only ℕ-induction reaches, so the \
             rung in `solve` is gone, unreachable, or starved"
        );
    }
}

/// Running the route twice over the *same arena* must give the same answer.
///
/// The step introduces a fresh constant through `declare_internal("!ind_k", …)`,
/// and `declare_internal` **interns by name**: a second call over the same arena
/// hands back the *same* symbol. That is harmless only as long as no residue of
/// the first run constrains it. This pins that, because dispatch will call the
/// route on arenas other routes have already been over.
#[test]
fn nat_induction_is_stable_across_repeated_calls_on_one_arena() {
    let text = concat!(
        "(set-logic UFLIA)\n",
        "(declare-fun f (Int) Int)\n",
        "(assert (= (f 0) 0))\n",
        "(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n",
        "(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n"
    );
    let mut parsed = parse_script(text).expect("parses");
    let assertions = parsed.assertions.clone();
    let config = SolverConfig::default();

    let first = prove_by_nat_induction(&mut parsed.arena, &assertions, &config, check_auto)
        .expect("first call succeeds");
    let second = prove_by_nat_induction(&mut parsed.arena, &assertions, &config, check_auto)
        .expect("second call succeeds");
    let third = prove_by_nat_induction(&mut parsed.arena, &assertions, &config, check_auto)
        .expect("third call succeeds");

    assert!(
        matches!(first, Some(CheckResult::Unsat)),
        "positive control must be refuted on the first call"
    );
    assert!(
        matches!(second, Some(CheckResult::Unsat)),
        "second call over the same arena changed the verdict: {second:?}"
    );
    assert!(
        matches!(third, Some(CheckResult::Unsat)),
        "third call over the same arena changed the verdict: {third:?}"
    );
}

/// A satisfiable set must stay undecided no matter how many times it is asked.
#[test]
fn nat_induction_declines_satisfiable_set_repeatedly() {
    let text = concat!(
        "(set-logic UFLIA)\n",
        "(declare-fun f (Int) Int)\n",
        "(assert (= (f 0) 0))\n",
        "(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n",
        // f(n) = n is false already at n = 1 (f(1) = 2).
        "(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) n)))))\n"
    );
    let mut parsed = parse_script(text).expect("parses");
    let assertions = parsed.assertions.clone();
    let config = SolverConfig::default();
    for round in 0..3 {
        let verdict = prove_by_nat_induction(&mut parsed.arena, &assertions, &config, check_auto)
            .expect("call succeeds");
        assert!(
            verdict.is_none(),
            "round {round}: satisfiable set was decided {verdict:?}"
        );
    }
}
