//! The proving front door [`prove`]: prove a goal from hypotheses by refuting
//! its negation, with a re-checked certificate behind every `Proved`.

use std::time::Duration;

use axeyum_ir::{TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

#[test]
fn proves_a_real_implication() {
    // x > 0  ⊨  x >= 0. The negation (x > 0 ∧ x < 0) is unsatisfiable.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let hyp = arena.real_gt(x, zero).unwrap();
    let goal = arena.real_ge(x, zero).unwrap();

    let outcome = prove(&mut arena, &[hyp], goal, &config()).unwrap();
    let ProofOutcome::Proved(report) = outcome else {
        panic!("x > 0 should prove x >= 0, got {outcome:?}");
    };
    // The refutation re-validates independently against hyp ∧ ¬goal.
    let neg_goal = arena.not(goal).unwrap();
    assert!(report.evidence.check(&arena, &[hyp, neg_goal]).unwrap());
    assert!(report.evidence.is_certified());
}

#[test]
fn disproves_a_non_implication_with_a_countermodel() {
    // x > 0  does NOT entail  x > 1 (e.g. x = 1/2). The negation is satisfiable.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let hyp = arena.real_gt(x, zero).unwrap();
    let goal = arena.real_gt(x, one).unwrap();

    let outcome = prove(&mut arena, &[hyp], goal, &config()).unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("x > 0 should not prove x > 1, got {outcome:?}");
    };
    // The countermodel satisfies the hypothesis but falsifies the goal.
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, hyp, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, goal, &assignment).unwrap(), Value::Bool(false));
}

#[test]
fn proves_a_bitvector_tautology() {
    // ⊨  (x | x) == x  for every bit-vector x.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let x_or_x = arena.bv_or(x, x).unwrap();
    let goal = arena.eq(x_or_x, x).unwrap();

    let outcome = prove(&mut arena, &[], goal, &config()).unwrap();
    let ProofOutcome::Proved(report) = outcome else {
        panic!("(x | x) == x is a tautology, got {outcome:?}");
    };
    // A pure-QF_BV proof carries a DRAT certificate that re-checks.
    let neg_goal = arena.not(goal).unwrap();
    assert!(report.evidence.check(&arena, &[neg_goal]).unwrap());
    assert!(report.evidence.is_certified());
}

#[test]
fn disproves_a_bitvector_non_theorem() {
    // x == 5 is not valid (x can be anything else).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let goal = arena.eq(x, five).unwrap();

    let outcome = prove(&mut arena, &[], goal, &config()).unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("x == 5 is not a theorem, got {outcome:?}");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, goal, &assignment).unwrap(), Value::Bool(false));
}
