//! Mandatory source-bound negative-real multiplication proof regression.
#![cfg(feature = "full")]
use axeyum_cnf::parse_alethe;
use axeyum_solver::{SolverConfig, check_alethe_lra, solve_smtlib_get_proof};

#[test]
fn negative_real_product_has_a_checked_proof() {
    for (index, product) in [
        "(* (- 1.0) x)",
        "(* x (- 1.0))",
        "(- x)",
        "(* (- (- (- 1.0))) x)",
        "(* (- 0.5) x)",
    ]
    .into_iter()
    .enumerate()
    {
        let query = format!(
            "(set-logic QF_LRA) (declare-const x Real) (assert (> x 0.0)) (assert (> {product} 0.0)) (check-sat)"
        );
        let text = solve_smtlib_get_proof(&query, &SolverConfig::default())
            .unwrap()
            .expect("reported product proof gap must close");
        assert_eq!(check_alethe_lra(&parse_alethe(&text).unwrap()), Ok(true));
        if let Some(directory) = std::env::var_os("AXEYUM_REAL_PROOF_EXPORT") {
            let root = std::path::PathBuf::from(directory);
            std::fs::write(root.join(format!("real-{index}.smt2")), &query).unwrap();
            std::fs::write(root.join(format!("real-{index}.alethe")), &text).unwrap();
        }
    }
}

#[test]
fn closed_negative_scalar_is_linear_in_the_proof_checker() {
    let proof = parse_alethe("(assume h0 (> x 0.0)) (assume h1 (> (* (- 1.0) x) 0.0)) (step la (cl (not (> x 0.0)) (not (> (* (- 1.0) x) 0.0))) :rule la_generic :args (1.0 1.0)) (step end (cl) :rule resolution :premises (h0 h1 la))").unwrap();
    assert_eq!(check_alethe_lra(&proof), Ok(true));
}

#[test]
fn a_variable_coefficient_cannot_be_treated_as_a_scalar() {
    for coefficient in ["y", "(/ 1.0 0.0)", "(/ y 1.0)", "(* y y)"] {
        let text = format!(
            "(assume h0 (> x 0.0)) (assume h1 (< (* {coefficient} x) 0.0)) (step la (cl (not (> x 0.0)) (not (< (* {coefficient} x) 0.0))) :rule la_generic :args (1.0 1.0)) (step end (cl) :rule resolution :premises (h0 h1 la))"
        );
        assert!(
            check_alethe_lra(&parse_alethe(&text).unwrap()).is_err(),
            "{coefficient}"
        );
    }
}

#[test]
fn zero_and_positive_coefficients_have_replayed_sat_controls() {
    for product in ["(* 0.0 x)", "(* 1.0 x)", "(* x 0.5)"] {
        let query = format!(
            "(set-logic QF_LRA) (declare-const x Real) (assert (> x 0.0)) (assert (>= {product} 0.0)) (check-sat)"
        );
        let solved =
            axeyum_solver::solve_smtlib_with_model(&query, &SolverConfig::default()).unwrap();
        assert!(matches!(
            solved.outcome.result,
            axeyum_solver::CheckResult::Sat(_)
        ));
        assert_eq!(
            axeyum_solver::check_model(
                &solved.script.arena,
                &solved.assertions,
                solved.model.as_ref().expect("SAT arithmetic model")
            ),
            Ok(true)
        );
        assert!(
            solve_smtlib_get_proof(&query, &SolverConfig::default())
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn nested_scalar_normalization_bridge_is_required() {
    let query = "(declare-const x Real) (assert (> x 0.0)) (assert (> (* (- (- (- 1.0))) x) 0.0)) (check-sat)";
    let text = solve_smtlib_get_proof(query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    let mut proof = parse_alethe(&text).unwrap();
    let index = proof
        .iter()
        .position(|command| {
            matches!(command,
        axeyum_cnf::AletheCommand::Step { rule, .. } if rule == "minus_simplify")
        })
        .expect("nested scalar must carry a source-preserving rewrite bridge");
    proof.remove(index);
    assert!(check_alethe_lra(&proof).is_err());
}
