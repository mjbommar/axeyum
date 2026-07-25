//! Public UFLIA regressions for replay-certified guarded universal models.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

#[test]
fn twosquares_public_guarded_model_is_sat() {
    let script = r"
        (set-logic UFLIA)
        (declare-sort S1 0)
        (declare-fun f1 () S1)
        (declare-fun f2 () S1)
        (declare-fun f3 () Int)
        (declare-fun f4 (Int) S1)
        (assert (not (= f1 f2)))
        (assert (not (<= 1 f3)))
        (assert
          (forall ((x Int))
            (=> (= (f4 x) f1)
                (=> (not (= x 2))
                    (=> (not (= x 3))
                        (<= 5 x))))))
        (check-sat)
    ";
    let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
    let outcome = solve_smtlib(script, &config).expect("the guarded model must not error");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "the exact public TwoSquares shape must have a replay-certified model"
    );
}

#[test]
fn guarded_model_does_not_hide_a_falsifying_explicit_point() {
    let script = r"
        (set-logic UFLIA)
        (declare-sort S1 0)
        (declare-fun f1 () S1)
        (declare-fun f4 (Int) S1)
        (assert (= (f4 0) f1))
        (assert
          (forall ((x Int))
            (=> (= (f4 x) f1)
                (=> (not (= x 2))
                    (=> (not (= x 3))
                        (<= 5 x))))))
        (check-sat)
    ";
    let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
    let outcome = solve_smtlib(script, &config).expect("the falsifying point must not error");
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "x = 0 makes the exact universal false when f4(0) = f1"
    );
}
