//! Regression coverage for first-class SMT-LIB `declare-sort` carriers.
//!
//! These are pure EUF problems over a declared sort, not the older bounded-BV
//! modeling path. Every `sat` result is replayed through the ground evaluator.
#![cfg(feature = "full")]

use axeyum_ir::{Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

#[test]
fn declared_sort_disequality_sat_model_replays() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (not (= a b)))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected declared-sort disequality to be sat, got {result:?}");
    };
    let assignment = model.to_assignment();
    for &assertion in &script.assertions {
        assert_eq!(
            eval(&script.arena, assertion, &assignment).unwrap(),
            Value::Bool(true),
            "sat model must replay against the original declared-sort assertion"
        );
    }
}

#[test]
fn declared_sort_function_congruence_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn declared_sort_ufbv_sat_model_replays() {
    let mut script = parse_script(
        r"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun m (U) (_ BitVec 1))
        (declare-fun a (U) (_ BitVec 1))
        (declare-const s0 U)
        (assert (not (= (_ bv0 1) ((_ extract 0 0) (a s0)))))
        (assert (not (= (_ bv1 1) ((_ extract 0 0) (m s0)))))
        (declare-const s1 U)
        (assert (and (= (a s1) (_ bv0 1)) (= (m s1) (_ bv0 1))))
        (declare-const s U)
        (assert (= (_ bv1 1) ((_ extract 0 0) (m s))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected mixed declared-sort QF_UFBV SAT, got {result:?}");
    };
    let assignment = model.to_assignment();
    for &assertion in &script.assertions {
        assert_eq!(
            eval(&script.arena, assertion, &assignment).unwrap(),
            Value::Bool(true),
            "sat model must replay against the original declared-sort QF_UFBV assertion"
        );
    }
}
