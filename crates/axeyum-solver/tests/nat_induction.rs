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
use axeyum_solver::{CheckResult, SolverConfig, prove_by_nat_induction, solve_smtlib};

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
    prove_by_nat_induction(&mut parsed.arena, &assertions, &config)
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

/// The claim this whole route rests on: the shipped front door does **not**
/// already decide these.
///
/// If `solve_smtlib` returned `unsat` here, the induction route would be
/// answering a question something else had already answered, and every test
/// above would be measuring nothing. `f(0) = 0` with `∀k ≥ 0. f(k+1) = f(k)+2`
/// does not entail `∀n ≥ 0. f(n) = 2n` in LIA+UF — nothing forces the
/// unrolling to reach every `n` — so this is the gap induction fills.
#[test]
fn the_ordinary_front_door_does_not_already_decide_this() {
    let script = recurrence("(= (f n) (* 2 n))");
    let outcome = solve_smtlib(&script, &SolverConfig::default()).expect("front door runs");
    assert!(
        !matches!(outcome.result, CheckResult::Unsat),
        "the front door answered unsat without induction; this route would then be redundant \
         and the tests above would prove nothing. Got: {:?}",
        outcome.result
    );
}
