//! Mandatory integer-theory composition; these proofs remain internal-only.
#![cfg(feature = "full")]
use axeyum_cnf::{AletheCommand, check_alethe, parse_alethe};
use axeyum_solver::{
    CheckResult, SolverConfig, check_alethe_lra, solve_smtlib_get_proof, solve_smtlib_with_model,
};

const DECL: &str = "(set-logic QF_LIA) (declare-const p Bool) (declare-const x Int) ";

#[test]
fn boolean_integer_contradictions_have_closed_internal_proofs() {
    for body in [
        "(assert (or p (>= x 1))) (assert (not p)) (assert (<= x 0))",
        "(assert (or p (= (* 2 x) 1))) (assert (not p))",
        "(assert (=> p (= (* 2 x) 1))) (assert p)",
        "(assert (= p (= (* 2 x) 1))) (assert p)",
    ] {
        let query = format!("{DECL}{body} (check-sat)");
        let text = solve_smtlib_get_proof(&query, &SolverConfig::default())
            .unwrap()
            .expect("Boolean/integer proof required");
        let proof = parse_alethe(&text).unwrap();
        assert_eq!(check_alethe_lra(&proof), Ok(true));
        assert!(
            check_alethe(&proof).is_err(),
            "internal integer rule must not look portable"
        );
        assert!(text.contains(":rule lia_generic"));
        assert!(
            !text.contains("@axeyum_lia_atom"),
            "no unchecked abstraction may escape"
        );
        let assumptions = proof
            .iter()
            .filter(|command| matches!(command, AletheCommand::Assume { .. }))
            .count();
        assert_eq!(assumptions, body.matches("(assert").count());
        assert_eq!(
            solve_smtlib_get_proof(&query, &SolverConfig::default()).unwrap(),
            Some(text)
        );
    }
}

#[test]
fn satisfiable_boolean_integer_controls_replay_without_refutations() {
    for body in [
        "(assert (or p (= (* 2 x) 1))) (assert p)",
        "(assert (or p (>= x 1))) (assert (not p)) (assert (<= x 1))",
        "(assert (= p (= (* 2 x) 2))) (assert p)",
    ] {
        let query = format!("{DECL}{body} (check-sat)");
        let result = solve_smtlib_with_model(&query, &SolverConfig::default()).unwrap();
        assert!(matches!(result.outcome.result, CheckResult::Sat(_)));
        assert_eq!(
            axeyum_solver::check_model(
                &result.script.arena,
                &result.assertions,
                result.model.as_ref().unwrap()
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
fn changing_integer_lemma_or_deleting_resolution_premise_rejects() {
    let query = format!("{DECL}(assert (or p (= (* 2 x) 1))) (assert (not p)) (check-sat)");
    let text = solve_smtlib_get_proof(&query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    let mut proof = parse_alethe(&text).unwrap();
    let command = proof
        .iter_mut()
        .find(
            |command| matches!(command, AletheCommand::Step { rule, .. } if rule == "lia_generic"),
        )
        .unwrap();
    if let AletheCommand::Step { clause, .. } = command {
        clause.clear(); // Empty clause is not an integer tautology.
    }
    assert!(check_alethe_lra(&proof).is_err());
    let mut proof = parse_alethe(&text).unwrap();
    for command in &mut proof {
        if let AletheCommand::Step { rule, clause, .. } = command
            && rule == "lia_generic"
        {
            for literal in clause {
                if let axeyum_cnf::AletheTerm::App(head, args) = &mut literal.atom
                    && head == "="
                {
                    args[1] = axeyum_cnf::AletheTerm::Const("2".to_owned());
                }
            }
        }
    }
    assert!(
        check_alethe_lra(&proof).is_err(),
        "altered integer premise must reject"
    );
    let mut proof = parse_alethe(&text).unwrap();
    if let Some(AletheCommand::Step { premises, .. }) = proof.last_mut() {
        premises.clear();
    }
    assert!(check_alethe_lra(&proof).is_err());
}

#[test]
fn expired_budget_cannot_produce_a_boolean_integer_proof() {
    let query = format!("{DECL}(assert (or p (= (* 2 x) 1))) (assert (not p)) (check-sat)");
    let config = SolverConfig {
        timeout: Some(std::time::Duration::ZERO),
        ..SolverConfig::default()
    };
    assert!(solve_smtlib_get_proof(&query, &config).unwrap().is_none());
}

#[test]
fn quoted_names_and_abstraction_name_collision_preserve_source() {
    let query = "(declare-const |@axeyum_lia_atom_0| Bool) (declare-const |x space| Int) (assert (or |@axeyum_lia_atom_0| (= (* 2 |x space|) 1))) (assert (not |@axeyum_lia_atom_0|)) (check-sat)";
    let text = solve_smtlib_get_proof(query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    let proof = parse_alethe(&text).unwrap();
    assert_eq!(check_alethe_lra(&proof), Ok(true));
    // SMT-LIB |simple_name| and simple_name denote the same symbol.
    let expected = parse_alethe("(assume a (or @axeyum_lia_atom_0 (= (* 2 |x space|) 1))) (assume b (not @axeyum_lia_atom_0))").unwrap();
    let clauses: Vec<_> = proof
        .iter()
        .filter_map(|command| match command {
            AletheCommand::Assume { clause, .. } => Some(clause),
            AletheCommand::Step { .. } => None,
        })
        .collect();
    let expected_clauses: Vec<_> = expected
        .iter()
        .filter_map(|command| match command {
            AletheCommand::Assume { clause, .. } => Some(clause),
            AletheCommand::Step { .. } => None,
        })
        .collect();
    assert_eq!(clauses, expected_clauses);
}
