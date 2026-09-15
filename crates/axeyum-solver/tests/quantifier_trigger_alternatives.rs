//! Auto trigger selection proposing SEVERAL alternatives (ADR-2113,
//! `AXEYUM_QINST_TRIGGER_ALTERNATIVES` / [`TriggerAlternativeCapGuard`]).
//!
//! Both references keep several alternatives per quantifier and we kept one:
//! z3 makes every full-cover candidate its own single-pattern
//! (`pattern_inference.cpp:458-467`) and cvc5 registers a `Trigger` per single
//! pattern term (`inst_strategy_e_matching.cpp:277-302`), while
//! `select_triggers` returned the FIRST full-cover candidate in pre-order and
//! the compile loop wrapped it in a one-element `vec!`. The lane's census is
//! what made that worth changing: over the 19 UFLIA reference-minimal cores
//! whose per-universal probe printed at all, **444 of 500 universals (88.8 %)
//! admitted no instance for the whole run and only 1 of 500 had no trigger** —
//! so the silence is not missing triggers, it is triggers that do not fire.
//!
//! **Soundness is structural and these tests do not establish it — they try to
//! REFUTE it.** Every instance the loop admits is `body[x⃗ := t⃗]`, and
//! `∀x⃗. B ⊨ B[x⃗ := t⃗]` for *every* ground `t⃗`; the entailment is a property
//! of `B` alone and cannot depend on what proposed `t⃗`. A trigger's only output
//! is a substitution. So the adversarial fixture below is a SATISFIABLE
//! quantified query run at a raised cap: if alternatives could manufacture a
//! refutation, this is where it would appear.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SolverConfig, TriggerAlternativeCapGuard, prove_quantified_unsat_via_egraph,
    solve_smtlib,
};

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// The E-matching refutation loop alone, so a verdict is attributable to the
/// trigger rather than to one of the front door's other routes.
fn ematch(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("parses");
    prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
        .expect("no solver error")
}

// ---------------------------------------------------------------------------
// SOUNDNESS-NEGATIVE. A satisfiable quantified query must not be refuted at any
// cap.
// ---------------------------------------------------------------------------

/// `∀x. f(x) = g(x)` together with `f(a) ≠ g(b)`, over an uninterpreted sort.
///
/// Satisfiable: the universal equates `f` and `g` pointwise, and `f(a) ≠ g(b)`
/// is consistent with that whenever `a ≠ b`.
///
/// The body carries TWO INCOMPARABLE full-cover candidates, `f(x)` and `g(x)`.
/// That is deliberate and it is what makes this fixture non-vacuous: a nested
/// pair like `g(x)` and `f(g(x))` collapses to ONE alternative under the
/// containment filter, so a raised cap would compile exactly the shipped
/// pattern and the assertion below would be comparing the shipped arm with
/// itself. `a_raised_cap_proposes_both_incomparable_candidates` in
/// `qinst_egraph.rs` is the control that the two arms really differ.
const SAT_TWO_CANDIDATES: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun f (U) U)
    (declare-fun g (U) U)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U)) (= (f x) (g x))))
    (assert (not (= (f a) (g b))))
    (check-sat)
";

/// The same shape carrying arithmetic — the UFLIA shape this lane measured — so
/// the ground closure is exercised and not only the congruence closure. `p(i)`
/// and `q(i)` are again incomparable full-cover candidates, and `c < 0` puts the
/// goal outside the universal's guard, so it is satisfiable.
const SAT_UFLIA: &str = r"
    (set-logic UFLIA)
    (declare-fun p (Int) Int)
    (declare-fun q (Int) Int)
    (declare-const c Int)
    (assert (forall ((i Int)) (=> (>= i 0) (= (p i) (q i)))))
    (assert (< c 0))
    (assert (not (= (p c) (q c))))
    (check-sat)
";

#[test]
fn a_satisfiable_query_is_not_refuted_at_any_cap() {
    // Every cap, not only the one an A/B would ship: a lever measured at 4 and
    // guarded at 4 is untested at 2, 8 and 32, and the compile path is the
    // same at all of them.
    for cap in [1usize, 2, 3, 4, 8, 32] {
        for (name, text) in [
            ("SAT_TWO_CANDIDATES", SAT_TWO_CANDIDATES),
            ("SAT_UFLIA", SAT_UFLIA),
        ] {
            let _guard = TriggerAlternativeCapGuard::set(cap);
            let verdict = ematch(text);
            assert!(
                !matches!(verdict, CheckResult::Unsat),
                "{name} at cap {cap}: a SATISFIABLE query was refuted -- \
                 alternatives may only add entailed instances, so an `unsat` \
                 here is a wrong ground closure or a wrong substitution, never \
                 an over-eager trigger"
            );
        }
    }
}

#[test]
fn the_front_door_also_refuses_the_satisfiable_query_at_a_raised_cap() {
    // The loop alone is the attributable instrument; the front door is what
    // ships. A lever tested only through the isolated route is a lever whose
    // shipped path has no soundness test.
    //
    // `solve_smtlib`, not `check_auto`: the latter is the quantifier-FREE
    // dispatch and returns `Unsupported("… unsupported pure-Rust BV operator
    // Forall")` on any of these, which an `assert!(!unsat)` would have swallowed
    // as a pass.
    //
    // This runs the front door on THIS thread, which is what makes the guard
    // apply at all — see `the_guard_does_not_cross_a_thread_boundary`.
    for cap in [1usize, 4, 32] {
        let _guard = TriggerAlternativeCapGuard::set(cap);
        let outcome = solve_smtlib(SAT_UFLIA, &config()).expect("no solver error");
        assert!(
            !matches!(outcome.result, CheckResult::Unsat),
            "front door at cap {cap}: a SATISFIABLE query was refuted"
        );
    }
}

/// The guard is a THREAD-LOCAL, so it is inert on any thread but the one that
/// set it — and the process cap (`AXEYUM_QINST_TRIGGER_ALTERNATIVES`) is not.
///
/// This is pinned rather than commented because the shipped consumer,
/// `smtcomp_cli`, runs the solve on a **watchdog worker thread**. An A/B that
/// set the guard and measured through a worker would read the SHIPPED arm on
/// both sides and publish a null that no value of the lever could have moved.
/// The A/B therefore uses the environment variable, and this test is what says
/// why it must.
#[test]
fn the_guard_does_not_cross_a_thread_boundary() {
    let outer = TriggerAlternativeCapGuard::set(32);
    let observed = std::thread::spawn(|| {
        // Any observable that depends on the cap would do; the guard's own
        // absence is the point, so this asks the loop for its instances on a
        // fixture whose alternative set differs between the two arms.
        let _inner_has_no_guard = ();
        let mut script = parse_script(UNSAT_REACHED_BY_BOTH).expect("parses");
        axeyum_solver::instantiate_forall_via_egraph(
            &mut script.arena,
            &script.assertions,
            script.assertions[0],
        )
        .len()
    })
    .join()
    .expect("worker finished");
    drop(outer);

    let shipped = {
        let mut script = parse_script(UNSAT_REACHED_BY_BOTH).expect("parses");
        axeyum_solver::instantiate_forall_via_egraph(
            &mut script.arena,
            &script.assertions,
            script.assertions[0],
        )
        .len()
    };
    assert_eq!(
        observed, shipped,
        "a worker thread saw something other than the SHIPPED cap, so this test \
         is not pinning what it claims"
    );
    assert!(
        shipped > 0,
        "the fixture proposed no instances on either side, so the equality above \
         held between two zeros"
    );
}

// ---------------------------------------------------------------------------
// The lever does what it says, and the OFF arm is unchanged.
// ---------------------------------------------------------------------------

/// `∀x. f(x) = g(x)` with the goal `f(b) ≠ g(b)`. The single instance `x := b`
/// refutes it, and BOTH alternatives reach that instance, so this pins that
/// raising the cap does not LOSE a decision — the direction a reordering or a
/// truncation could break silently.
const UNSAT_REACHED_BY_BOTH: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun f (U) U)
    (declare-fun g (U) U)
    (declare-const b U)
    (assert (forall ((x U)) (= (f x) (g x))))
    (assert (not (= (f b) (g b))))
    (check-sat)
";

#[test]
fn a_refutation_the_shipped_cap_finds_survives_every_raised_cap() {
    for cap in [1usize, 2, 4, 32] {
        let _guard = TriggerAlternativeCapGuard::set(cap);
        assert!(
            matches!(ematch(UNSAT_REACHED_BY_BOTH), CheckResult::Unsat),
            "cap {cap} lost a refutation the shipped cap finds"
        );
    }
}

#[test]
fn the_alternative_set_is_deterministic_across_runs() {
    // Determinism is a public API promise, and an alternative SET is where an
    // unordered candidate list would break it silently: a wrong order still
    // decides the same queries most of the time, so only a repeat comparison
    // catches it. The instance list is the direct observable.
    let mut seen: Option<Vec<String>> = None;
    for _ in 0..8 {
        let _guard = TriggerAlternativeCapGuard::set(4);
        let mut script = parse_script(UNSAT_REACHED_BY_BOTH).expect("parses");
        let instances = axeyum_solver::instantiate_forall_via_egraph(
            &mut script.arena,
            &script.assertions,
            script.assertions[0],
        );
        let rendered: Vec<String> = instances
            .iter()
            .map(|&t| axeyum_ir::render(&script.arena, t))
            .collect();
        match &seen {
            None => seen = Some(rendered),
            Some(first) => assert_eq!(
                first, &rendered,
                "the proposed instances changed between two identical runs"
            ),
        }
    }
    assert!(
        seen.is_some_and(|r| !r.is_empty()),
        "the fixture proposed NO instance, so the comparison above compared two \
         empty lists and could not have failed -- a vacuous determinism test"
    );
}

/// A body whose bound variable occurs in no function application at all: there
/// is no full-cover candidate, so the raised cap must fall back to
/// `select_triggers` and behave exactly as the shipped cap does.
#[test]
fn a_body_with_no_full_cover_candidate_falls_back_identically() {
    let text = r"
        (set-logic UFLIA)
        (declare-const a Int)
        (assert (forall ((x Int)) (or (>= x 0) (< x 0))))
        (assert (and (> a 0) (< a 0)))
        (check-sat)
    ";
    let mut baseline: Option<bool> = None;
    for cap in [1usize, 4, 32] {
        let _guard = TriggerAlternativeCapGuard::set(cap);
        let refuted = matches!(ematch(text), CheckResult::Unsat);
        match baseline {
            None => baseline = Some(refuted),
            Some(first) => assert_eq!(
                first, refuted,
                "cap {cap} changed the verdict on a body with no full-cover \
                 candidate, where the cap has nothing to select from"
            ),
        }
    }
    assert_eq!(
        baseline,
        Some(true),
        "the fixture was not refuted at ANY cap, so the equality above held \
         between two `false`s and pinned nothing"
    );
}

/// The guard restores the previous cap on drop, which every test above relies
/// on: a leaked override would make the NEXT test measure this one's arm.
#[test]
fn the_cap_guard_restores_the_previous_setting() {
    let mut arena = TermArena::new();
    let u = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
    let _ = arena.declare_fun("f", &[u], u).expect("f");
    // Observable through a decision that DEPENDS on the cap would be circular
    // here, so this pins the guard's own contract: nested guards unwind in
    // order and the outermost value is what survives.
    {
        let _outer = TriggerAlternativeCapGuard::set(7);
        {
            let _inner = TriggerAlternativeCapGuard::set(9);
            assert!(matches!(ematch(UNSAT_REACHED_BY_BOTH), CheckResult::Unsat));
        }
        assert!(matches!(ematch(UNSAT_REACHED_BY_BOTH), CheckResult::Unsat));
    }
    assert!(matches!(ematch(UNSAT_REACHED_BY_BOTH), CheckResult::Unsat));
}
