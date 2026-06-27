//! The proving front door [`prove`]: prove a goal from hypotheses by refuting
//! its negation, with a re-checked certificate behind every `Proved`.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{
    Evidence, ProofOutcome, SolverConfig, produce_evidence_minimized, prove, prove_minimized,
};

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

#[test]
fn produce_evidence_minimized_returns_small_sat_model() {
    let mut arena = TermArena::new();
    let flag_s = arena.declare("flag", Sort::Bool).unwrap();
    let x_s = arena.declare("x", Sort::BitVec(8)).unwrap();
    let flag = arena.var(flag_s);
    let x = arena.var(x_s);
    let seven = arena.bv_const(8, 7).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let x_ge_7 = arena.bv_uge(x, seven).unwrap();
    let flag_or_x_ge_7 = arena.or(flag, x_ge_7).unwrap();
    let x_le_10 = arena.bv_ule(x, ten).unwrap();

    let report = produce_evidence_minimized(
        &mut arena,
        &[flag_or_x_ge_7, x_le_10],
        &[flag_s, x_s],
        &config(),
    )
    .unwrap();
    let Evidence::Sat(model) = &report.evidence else {
        panic!("expected minimized sat evidence, got {:?}", report.evidence);
    };
    assert_eq!(model.get(flag_s), Some(Value::Bool(false)));
    assert_eq!(model.get(x_s), Some(Value::Bv { width: 8, value: 7 }));
    assert!(
        report
            .evidence
            .check(&arena, &[flag_or_x_ge_7, x_le_10])
            .unwrap()
    );
}

#[test]
fn prove_minimized_returns_small_countermodel() {
    let mut arena = TermArena::new();
    let x_s = arena.declare("px", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_s);
    let seven = arena.bv_const(8, 7).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let x_ge_7 = arena.bv_uge(x, seven).unwrap();
    let x_le_10 = arena.bv_ule(x, ten).unwrap();
    let goal = arena.eq(x, nine).unwrap();

    let outcome = prove_minimized(&mut arena, &[x_ge_7, x_le_10], goal, &[x_s], &config()).unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("x in [7,10] should not prove x == 9, got {outcome:?}");
    };
    assert_eq!(model.get(x_s), Some(Value::Bv { width: 8, value: 7 }));
    let assignment = model.to_assignment();
    assert_eq!(
        eval(&arena, x_ge_7, &assignment).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, x_le_10, &assignment).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval(&arena, goal, &assignment).unwrap(), Value::Bool(false));
}

#[test]
fn proves_function_congruence_with_a_checkable_certificate() {
    // x == y ⊨ f(x) == f(y) (congruence). The negation reduces (Ackermann) to
    // QF_BV, so the proof now carries a re-checkable DRAT certificate end to end
    // through the proving front door — proof-assistant-grade for the UF fragment.
    use axeyum_ir::Sort;

    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let hyp = arena.eq(x, y).unwrap();
    let goal = arena.eq(fx, fy).unwrap();

    let outcome = prove(&mut arena, &[hyp], goal, &config()).unwrap();
    let ProofOutcome::Proved(report) = outcome else {
        panic!("x==y should prove f(x)==f(y), got {outcome:?}");
    };
    // The proof carries a re-checkable certificate (not a bare unsat) and the
    // proving front door already re-validated it.
    assert!(report.evidence.is_certified(), "UF proof must be certified");
    let neg_goal = arena.not(goal).unwrap();
    assert!(report.evidence.check(&arena, &[hyp, neg_goal]).unwrap());
}
