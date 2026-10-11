//! Signed integer input must survive the public solver front door.
#![cfg(feature = "full")]
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

#[test]
fn signed_integer_input_survives_public_solver_dispatch() {
    for (body, satisfiable) in [
        ("(declare-const x Int) (assert (= x -1))", true),
        (
            "(declare-const x Int) (assert (= x -1)) (assert (>= x 0))",
            false,
        ),
        ("(assert (distinct (abs -1) 1))", false),
        (
            "(declare-const |-1| Bool) (assert |-1|) (assert (= -1 (- 1)))",
            true,
        ),
        ("(declare-const -1 Bool) (assert -1)", true),
        ("(assert (= (+ -1 2.0) 1.0))", true),
    ] {
        let query = format!("{body} (check-sat)");
        let result = solve_smtlib(&query, &SolverConfig::default())
            .unwrap()
            .result;
        assert!(
            matches!(result, CheckResult::Sat(_)) && satisfiable
                || matches!(result, CheckResult::Unsat) && !satisfiable,
            "{query}: {result:?}"
        );
    }
}
