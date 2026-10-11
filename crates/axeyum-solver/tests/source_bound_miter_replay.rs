//! Saved end-to-end certificates must bind both CNFs to the original query.
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_smtlib::{parse_script, write_script};
use axeyum_solver::{EndToEndUnsatOutcome, SolverError, certify_qf_bv_unsat_end_to_end};

fn fixture() -> (TermArena, [TermId; 2], EndToEndUnsatOutcome) {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let assertions = [arena.eq(x, zero).unwrap(), arena.eq(x, one).unwrap()];
    let certificate = certify_qf_bv_unsat_end_to_end(&arena, &assertions).unwrap();
    assert!(matches!(
        certificate,
        EndToEndUnsatOutcome::Certified { .. }
    ));
    (arena, assertions, certificate)
}

#[test]
fn honest_certificates_replay_in_original_and_reparsed_arenas() {
    let (arena, assertions, certificate) = fixture();
    assert!(
        certificate
            .recheck_for_bool_terms(&arena, &assertions)
            .unwrap()
    );
    let parsed = parse_script(&write_script(&arena, &assertions)).unwrap();
    assert!(
        certificate
            .recheck_for_bool_terms(&parsed.arena, &parsed.assertions)
            .unwrap()
    );
    let mut bool_arena = TermArena::new();
    let symbol = bool_arena.declare("p", Sort::Bool).unwrap();
    let p = bool_arena.var(symbol);
    let not_p = bool_arena.not(p).unwrap();
    let bool_certificate = certify_qf_bv_unsat_end_to_end(&bool_arena, &[p, not_p]).unwrap();
    assert!(
        bool_certificate
            .recheck_for_bool_terms(&bool_arena, &[p, not_p])
            .unwrap()
    );
}

#[test]
fn changed_original_query_and_unrelated_final_refutation_reject() {
    let (arena, assertions, certificate) = fixture();
    assert!(certificate.recheck().unwrap());
    assert!(
        !certificate
            .recheck_for_bool_terms(&arena, &assertions[..1])
            .unwrap()
    );
    let mut other = TermArena::new();
    let symbol = other.declare("p", Sort::Bool).unwrap();
    let p = other.var(symbol);
    let not_p = other.not(p).unwrap();
    let unrelated = certify_qf_bv_unsat_end_to_end(&other, &[p, not_p]).unwrap();
    let EndToEndUnsatOutcome::Certified {
        unsat: unrelated_unsat,
        ..
    } = unrelated
    else {
        panic!()
    };
    let mut forged = certificate;
    let EndToEndUnsatOutcome::Certified { unsat, .. } = &mut forged else {
        panic!()
    };
    *unsat = unrelated_unsat;
    assert!(
        forged.recheck().unwrap(),
        "both clausal refutations are independently valid"
    );
    assert!(!forged.recheck_for_bool_terms(&arena, &assertions).unwrap());
}

#[test]
fn unrelated_valid_refutation_cannot_replace_expected_miter() {
    let (arena, assertions, mut certificate) = fixture();
    let EndToEndUnsatOutcome::Certified {
        faithfulness_dimacs,
        faithfulness_drat,
        unsat,
    } = &mut certificate
    else {
        panic!()
    };
    assert_ne!(*faithfulness_dimacs, unsat.dimacs);
    *faithfulness_dimacs = unsat.dimacs.clone();
    *faithfulness_drat = unsat.drat.clone();
    assert!(
        certificate.recheck().unwrap(),
        "stored CNFs are still honestly refuted"
    );
    assert!(
        !certificate
            .recheck_for_bool_terms(&arena, &assertions)
            .unwrap()
    );
}

#[test]
fn missing_refutation_steps_and_invalid_final_hints_reject() {
    let (arena, assertions, certificate) = fixture();
    for miter in [true, false] {
        let mut broken = certificate.clone();
        let EndToEndUnsatOutcome::Certified {
            faithfulness_drat,
            unsat,
            ..
        } = &mut broken
        else {
            panic!()
        };
        if miter {
            faithfulness_drat.clear();
        } else {
            unsat.lrat = Some(String::new());
        }
        assert!(!matches!(
            broken.recheck_for_bool_terms(&arena, &assertions),
            Ok(true)
        ));
    }
}

#[test]
fn unsupported_source_is_an_explicit_error() {
    let (mut arena, _, certificate) = fixture();
    let x = arena.int_var("z").unwrap();
    let one = arena.int_const(1);
    let assertion = arena.eq(x, one).unwrap();
    assert!(matches!(
        certificate.recheck_for_bool_terms(&arena, &[assertion]),
        Err(SolverError::Unsupported(_))
    ));
}

#[test]
fn uncertified_outcomes_never_replay() {
    let (arena, assertions, _) = fixture();
    for outcome in [
        EndToEndUnsatOutcome::NotCertified,
        EndToEndUnsatOutcome::Satisfiable,
    ] {
        assert!(!outcome.recheck_for_bool_terms(&arena, &assertions).unwrap());
    }
}

#[test]
fn non_boolean_assertion_is_an_explicit_error() {
    let (mut arena, _, certificate) = fixture();
    let x = arena.bv_var("y", 4).unwrap();
    assert!(
        matches!(certificate.recheck_for_bool_terms(&arena, &[x]), Err(SolverError::NonBooleanAssertion(t)) if t == x)
    );
}
