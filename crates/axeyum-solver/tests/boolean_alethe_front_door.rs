//! Mandatory source-bound Boolean proof regressions and negative controls.
#![cfg(feature = "full")]
use axeyum_cnf::{AletheCommand, check_alethe, parse_alethe};
use axeyum_solver::{SolverConfig, solve_smtlib_get_proof};

#[test]
fn boolean_refutations_require_closed_checked_proofs() {
    for (index, body) in [
        "(assert p) (assert (not p))",
        "(assert (or p q)) (assert (not p)) (assert (not q))",
        "(assert (and p q)) (assert (not q))",
        "(assert (= p q)) (assert p) (assert (not q))",
        "(assert (xor p q)) (assert p) (assert q)",
        "(assert false)",
        "(assert (not true))",
        "(assert (=> p q)) (assert p) (assert (not q))",
        "(assert (not (=> p q))) (assert (not p))",
        "(assert (ite p q r)) (assert p) (assert (not q))",
        "(assert (ite p q r)) (assert (not p)) (assert (not r))",
        "(assert (not (ite p q r))) (assert p) (assert q)",
        "(assert (not (ite p q r))) (assert (not p)) (assert r)",
    ]
    .into_iter()
    .enumerate()
    {
        let query = format!(
            "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) {body} (check-sat)"
        );
        let text = solve_smtlib_get_proof(&query, &SolverConfig::default())
            .unwrap()
            .expect(body);
        if let Some(directory) = std::env::var_os("AXEYUM_BOOLEAN_PROOF_EXPORT") {
            let root = std::path::PathBuf::from(directory);
            std::fs::write(root.join(format!("case-{index}.smt2")), &query).unwrap();
            std::fs::write(root.join(format!("case-{index}.alethe")), &text).unwrap();
        }
        let proof = parse_alethe(&text).unwrap();
        assert_eq!(check_alethe(&proof), Ok(true), "{body}");
        assert!(!text.contains(":rule hole"));
        assert_eq!(
            solve_smtlib_get_proof(&query, &SolverConfig::default()).unwrap(),
            Some(text)
        );
    }
}

#[test]
fn satisfiable_boolean_queries_cannot_emit_refutations() {
    for body in [
        "(assert p)",
        "(assert (or p q))",
        "(assert (= p q))",
        "(assert true)",
        "(assert (=> p q)) (assert (not p)) (assert (not q))",
        "(assert (not (=> p q))) (assert p)",
        "(assert (ite p q r)) (assert p) (assert q)",
        "(assert (ite p q r)) (assert (not p)) (assert r)",
        "(assert (not (ite p q r))) (assert (not p)) (assert (not r))",
    ] {
        let query = format!(
            "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) {body} (check-sat)"
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
                solved
                    .model
                    .as_ref()
                    .expect("SAT control has a replayable model"),
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
fn resolution_premise_corruption_rejects() {
    let query = "(declare-const p Bool) (assert p) (assert (not p)) (check-sat)";
    let text = solve_smtlib_get_proof(query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    let mut proof = parse_alethe(&text).unwrap();
    let closing = proof
        .iter_mut()
        .rev()
        .find_map(|command| match command {
            AletheCommand::Step { premises, .. } => Some(premises),
            AletheCommand::Assume { .. } => None,
        })
        .unwrap();
    closing.clear();
    assert!(check_alethe(&proof).is_err());
}

#[test]
fn changed_source_assumption_cannot_reuse_the_refutation() {
    let query = "(declare-const p Bool) (assert p) (assert (not p)) (check-sat)";
    let text = solve_smtlib_get_proof(query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    let mut proof = parse_alethe(&text).unwrap();
    let assumption = proof
        .iter_mut()
        .find_map(|command| match command {
            AletheCommand::Assume { clause, .. } => Some(clause),
            AletheCommand::Step { .. } => None,
        })
        .unwrap();
    assumption[0].atom = axeyum_cnf::AletheTerm::Const("different_source".to_owned());
    assert!(check_alethe(&proof).is_err());
}

#[test]
fn quoted_boolean_symbols_preserve_source_identity() {
    let query = "(declare-const |a b| Bool) (assert |a b|) (assert (not |a b|)) (check-sat)";
    let proof = solve_smtlib_get_proof(query, &SolverConfig::default())
        .unwrap()
        .unwrap();
    assert!(proof.contains("|a b|"));
    assert_eq!(check_alethe(&parse_alethe(&proof).unwrap()), Ok(true));
}

#[test]
fn exhausted_boolean_proof_budget_does_not_produce_evidence() {
    let query = "(declare-const p Bool) (assert p) (assert (not p)) (check-sat)";
    let config = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
    assert!(solve_smtlib_get_proof(query, &config).unwrap().is_none());
}
