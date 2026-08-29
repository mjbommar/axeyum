//! The ℕ-induction route: goals that LIA+UF cannot decide and induction can.
//!
//! `docs/mathematics-2026-08/04-reachability.md` R3 ranks `induction-over-nat`
//! first among out-of-fragment requests, and it is the only entry on that list
//! that is not a missing logic — the kernel already checks induction proofs
//! (`axeyum-lean-kernel/tests/induction_arrow.rs`). This exercises the solver
//! side: producing the two obligations.
//!
//! Every instance here pins a function only by its recursion equations, which
//! is exactly where `quant_valid_universal`'s Skolemise-and-refute stops
//! working: `f(0) = 0` and `∀k ≥ 0. f(k+1) = f(k) + 2` do not entail
//! `∀n ≥ 0. f(n) = 2·n` in LIA+UF, because nothing forces the unrolling to
//! reach every `n`.
//!
//! The controls matter more than the positive case. A route that answered
//! `unsat` on everything would pass the first test, so a false base and a false
//! step are both driven through it and must NOT be refuted.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, prove_by_nat_induction, solve_smtlib};

/// `f` fixed at 0 and stepping by 2, with `goal` as the negated conclusion.
fn recurrence(goal: &str) -> String {
    format!(
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (assert (= (f 0) 0))\n\
         (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
         (assert (not (forall ((n Int)) (=> (>= n 0) {goal}))))\n\
         (check-sat)"
    )
}

fn induction_verdict(script: &str) -> Option<String> {
    let mut parsed = parse_script(script).expect("script parses");
    let assertions = parsed.assertions.clone();
    let config = SolverConfig::default();
    prove_by_nat_induction(&mut parsed.arena, &assertions, &config, check_auto)
        .expect("no hard backend error")
        .map(|result| match result {
            CheckResult::Unsat => "unsat".to_owned(),
            CheckResult::Sat(_) => "sat".to_owned(),
            CheckResult::Unknown(_) => "unknown".to_owned(),
        })
}

/// The positive case: `f(n) = 2n` follows from the recurrence by induction.
#[test]
fn a_recurrence_closed_form_is_refuted_by_induction() {
    assert_eq!(
        induction_verdict(&recurrence("(= (f n) (* 2 n))")).as_deref(),
        Some("unsat"),
        "base f(0)=0 and step f(k+1)=f(k)+2 give f(n)=2n"
    );
}

/// The same shape with a **false base**. `f(0) = 0`, not 1.
///
/// Without this the test above shows only that the route answers `unsat`; it
/// would pass identically against a route that always did.
#[test]
fn a_false_base_is_not_refuted() {
    assert_eq!(
        induction_verdict(&recurrence("(= (f n) (+ (* 2 n) 1))")).as_deref(),
        None,
        "f(0) = 1 is false, so the base obligation must not discharge"
    );
}

/// A **true base with a false step**: `f(0) = 0` holds, but `f` does not stay 0.
///
/// This is the case a base-only check would wrongly accept, so it separates
/// "does induction" from "checks the base and shrugs".
#[test]
fn a_true_base_with_a_false_step_is_not_refuted() {
    assert_eq!(
        induction_verdict(&recurrence("(= (f n) 0)")).as_deref(),
        None,
        "f(0)=0 holds but f(k+1)=f(k)+2 breaks the step"
    );
}

/// A goal with no induction shape at all is declined, not answered.
#[test]
fn a_query_without_a_negated_universal_is_declined() {
    let script = "(set-logic QF_LIA)\n\
                  (declare-fun x () Int)\n\
                  (assert (= x 1))\n\
                  (assert (= x 2))\n\
                  (check-sat)";
    assert_eq!(
        induction_verdict(script),
        None,
        "this is unsat, but not by induction — the route must not claim it"
    );
}

/// Two negated universals is a disjunctive obligation this route does not
/// model, and choosing one of them would be choosing which theorem to prove.
#[test]
fn two_goals_are_declined_rather_than_arbitrarily_chosen() {
    let script = "(set-logic UFLIA)\n\
                  (declare-fun f (Int) Int)\n\
                  (assert (= (f 0) 0))\n\
                  (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                  (assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))\n\
                  (assert (not (forall ((m Int)) (=> (>= m 0) (>= (f m) 0)))))\n\
                  (check-sat)";
    assert_eq!(induction_verdict(script), None);
}

/// **Liveness of the dispatch wiring.** The shipped front door refutes this,
/// and it can only be the induction rung doing it.
///
/// This test used to assert the opposite — that `solve_smtlib` did *not* return
/// `unsat` — because the route was built but deliberately left out of
/// [`axeyum_solver::solve`]'s ladder while its soundness was in question. That
/// question is settled (`a32280b6a` made the `n >= 0` guard mandatory;
/// `tests/nat_induction_adversarial.rs` probes twenty-two shapes around it), the
/// route is now the last rung of the quantified ladder, and the claim flips.
///
/// The attribution is not an assumption. `f(0) = 0` with `∀k ≥ 0. f(k+1) = f(k)+2`
/// does not entail `∀n ≥ 0. f(n) = 2n` in LIA+UF — no finite instantiation forces
/// the unrolling to reach every `n` — so every route above the rung reports
/// `unknown`, which is measured on this exact file in the
/// `nat_induction_corpus` table (front-door column, `guarded_linear_closed_form`).
/// The rung fires only on an `unknown`, so if it were removed or unreachable this
/// assertion is what dies.
#[test]
fn the_front_door_refutes_this_only_through_the_induction_rung() {
    let script = recurrence("(= (f n) (* 2 n))");
    let outcome = solve_smtlib(&script, &SolverConfig::default()).expect("front door runs");
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "the front door did not refute the recurrence closed form, so the ℕ-induction rung in \
         `solve` is either gone or never reached. Got: {:?}",
        outcome.result
    );
    // And the route itself decides it, so the verdict above is attributable.
    assert_eq!(
        induction_verdict(&script).as_deref(),
        Some("unsat"),
        "the front door refuted this but the induction route does not, so something else \
         decided it and the attribution in this test's docs is wrong"
    );
}

/// The front door must **not** inherit the bug the rung was quarantined for.
///
/// `∀n:Int. n ≥ 0` is false at `n = -1`, so the negation is satisfiable, and the
/// front door answered `sat` with that witness long before the rung existed.
/// Wiring a route that may only upgrade `unknown` → `unsat` cannot disturb a
/// verdict that is already `sat` — this pins that it does not.
#[test]
fn the_front_door_still_reports_sat_for_the_unguarded_int_universal() {
    let script = "(set-logic LIA)\n\
                  (assert (not (forall ((n Int)) (>= n 0))))\n\
                  (check-sat)";
    let outcome = solve_smtlib(script, &SolverConfig::default()).expect("front door runs");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "the front door stopped reporting sat for a satisfiable set after the induction rung \
         was wired in. Got: {:?}",
        outcome.result
    );
}

/// The soundness case that this route shipped without, found by building a
/// corpus before wiring it into dispatch.
///
/// `∀n:Int. n ≥ 0` is **false** — `n = -1` falsifies it, and this repository's
/// own front door returns exactly that witness. But base `0 ≥ 0` and step
/// `k ≥ 0 → k+1 ≥ 0` both discharge, so a route that applies ℕ-induction to an
/// `Int`-quantified goal answers `unsat` on a satisfiable set. Every test above
/// carries an explicit `(=> (>= n 0) …)` guard, so they exercise only the sound
/// branch and all six passed while this was broken.
#[test]
fn an_unguarded_int_universal_is_declined_not_proved() {
    let script = "(set-logic LIA)\n\
                  (assert (not (forall ((n Int)) (>= n 0))))\n\
                  (check-sat)";
    assert_eq!(
        induction_verdict(script),
        None,
        "ℕ-induction cannot establish a goal quantified over all of Int; \
         answering here is a wrong unsat"
    );
}

/// The same hole with a recursive function, so it cannot be dismissed as an
/// artefact of a trivial goal.
#[test]
fn an_unguarded_recurrence_goal_is_declined() {
    let script = "(set-logic UFLIA)\n\
                  (declare-fun f (Int) Int)\n\
                  (assert (= (f 0) 0))\n\
                  (assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))\n\
                  (assert (not (forall ((n Int)) (>= (f n) 0))))\n\
                  (check-sat)";
    assert_eq!(induction_verdict(script), None);
}

/// A guard this pass does not RECOGNISE is also declined.
///
/// `(> n (- 1))` is `n ≥ 0` over the integers, so proceeding would happen to be
/// sound — which is exactly why it must not be relied on. The rule is "a
/// recognised guard", not "a guard that turns out to be equivalent to one".
#[test]
fn an_unrecognised_guard_is_declined_rather_than_assumed_equivalent() {
    let script = "(set-logic LIA)\n\
                  (declare-fun g (Int) Int)\n\
                  (assert (= (g 0) 0))\n\
                  (assert (not (forall ((n Int)) (=> (> n (- 1)) (>= (g n) 0)))))\n\
                  (check-sat)";
    assert_eq!(induction_verdict(script), None);
}
