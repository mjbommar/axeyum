//! ADR-0107/0123/0133 checked free-Boolean quantified SAT models.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{ArraySortKey, Sort, TermArena, Value};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    ArithDpllOutcome, CheckResult, Evidence, Model, QuantifiedBoolModelSatCertificate,
    QuantifiedBoolModelSatProof, SolverConfig, SolverError, certify_arith_dpll_unsat, check_model,
    check_quantified_bool_model_sat, export_qf_bv_unsat_proof, produce_evidence, solve,
};

const PSYCO_PP: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__015-psyco-pp.smt2"
);
const PSYCO_196: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__psyco-196.smt2"
);
const CBQI_ITE: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__006-cbqi-ite.smt2"
);
const MODEL_6_1_BV: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__model_6_1_bv.smt2"
);
const PSYCO_001_BV: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-001-bv.smt2"
);

fn assertions(script: &axeyum_smtlib::Script) -> Vec<axeyum_ir::TermId> {
    script
        .commands
        .iter()
        .filter_map(|command| match command {
            ScriptCommand::Assert(term) => Some(*term),
            _ => None,
        })
        .collect()
}

fn config(seconds: u64) -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(seconds))
}

fn cegis_bv_assertion(
    arena: &mut TermArena,
    width: u32,
) -> (axeyum_ir::TermId, axeyum_ir::SymbolId) {
    let p = arena.declare("cegis_p", Sort::Bool).unwrap();
    let b = arena.declare("cegis_b", Sort::Bool).unwrap();
    let x = arena.declare("cegis_x", Sort::BitVec(width)).unwrap();
    let p_term = arena.var(p);
    let b_term = arena.var(b);
    let x_term = arena.var(x);
    let zero = arena.bv_const(width, 0).unwrap();
    let not_p = arena.not(p_term).unwrap();
    let guard = arena.or(b_term, not_p).unwrap();
    let selected = arena.ite(b_term, x_term, zero).unwrap();
    let conclusion = arena.eq(selected, x_term).unwrap();
    let body = arena.implies(guard, conclusion).unwrap();
    let all_x = arena.forall(x, body).unwrap();
    (arena.forall(b, all_x).unwrap(), p)
}

fn qfbv_certificate(model: &Model) -> QuantifiedBoolModelSatCertificate {
    let certificate = model
        .quantified_bool_model_sat_certificates()
        .next()
        .expect("one quantified free-Boolean certificate")
        .clone();
    assert!(matches!(
        certificate.proof,
        QuantifiedBoolModelSatProof::PositiveUniversalQfBv { .. }
    ));
    certificate
}

#[test]
fn exact_model_blocking_finds_required_free_guard() {
    // The erased skeleton is `true`, whose completed first model sets p=false.
    // That candidate falsifies the universal at x=1 and is blocked; p=true is a
    // checked model of the untouched assertion.
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let p_term = arena.var(p);
    let x_term = arena.var(x);
    let zero = arena.int_const(0);
    let x_zero = arena.eq(x_term, zero).unwrap();
    let body = arena.or(p_term, x_zero).unwrap();
    let assertion = arena.forall(x, body).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[assertion], &config(2)).unwrap() else {
        panic!("Boolean guard search must find p=true");
    };
    assert_eq!(model.get(p), Some(Value::Bool(true)));
    assert_eq!(model.quantified_bool_model_sat_certificates().count(), 1);
    assert!(check_model(&arena, &[assertion], &model).unwrap());
}

#[test]
fn bound_bool_and_affine_ite_are_checked_for_all_values() {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let b = arena.declare("b", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let p_term = arena.var(p);
    let b_term = arena.var(b);
    let x_term = arena.var(x);
    let one = arena.int_const(1);
    let x_plus_one = arena.int_add(x_term, one).unwrap();
    let one_plus_x = arena.int_add(one, x_term).unwrap();
    let left = arena.ite(b_term, x_plus_one, x_term).unwrap();
    let right = arena.ite(b_term, one_plus_x, x_term).unwrap();
    let equality = arena.eq(left, right).unwrap();
    let body = arena.or(p_term, equality).unwrap();
    let all_x = arena.forall(x, body).unwrap();
    let assertion = arena.forall(b, all_x).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[assertion], &config(2)).unwrap() else {
        panic!("affine ITE identity must be checked SAT");
    };
    assert!(check_model(&arena, &[assertion], &model).unwrap());
}

#[test]
fn changed_or_incomplete_certificate_and_model_are_rejected() {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let p_term = arena.var(p);
    let x_term = arena.var(x);
    let zero = arena.int_const(0);
    let x_zero = arena.eq(x_term, zero).unwrap();
    let body = arena.or(p_term, x_zero).unwrap();
    let assertion = arena.forall(x, body).unwrap();

    let good = QuantifiedBoolModelSatCertificate {
        assertion,
        values: vec![(p, true)],
        proof: QuantifiedBoolModelSatProof::Structural,
    };
    assert!(check_quantified_bool_model_sat(&arena, assertion, &good));

    let changed = QuantifiedBoolModelSatCertificate {
        assertion,
        values: vec![(p, false)],
        proof: QuantifiedBoolModelSatProof::Structural,
    };
    assert!(!check_quantified_bool_model_sat(
        &arena, assertion, &changed
    ));
    let missing = QuantifiedBoolModelSatCertificate {
        assertion,
        values: Vec::new(),
        proof: QuantifiedBoolModelSatProof::Structural,
    };
    assert!(!check_quantified_bool_model_sat(
        &arena, assertion, &missing
    ));

    let mut tampered_model = Model::new();
    tampered_model.set(p, Value::Bool(false));
    tampered_model.set_quantified_bool_model_sat_certificate(good);
    assert!(!check_model(&arena, &[assertion], &tampered_model).unwrap());
}

#[test]
fn large_arith_dpll_closure_uses_source_bound_drat() {
    let mut arena = TermArena::new();
    let mut assertions = Vec::new();
    let mut first = None;
    for index in 0..23 {
        let symbol = arena.declare(&format!("p{index}"), Sort::Bool).unwrap();
        let term = arena.var(symbol);
        first.get_or_insert(term);
        assertions.push(term);
    }
    let not_first = arena.not(first.unwrap()).unwrap();
    assertions.push(not_first);

    let ArithDpllOutcome::Unsat(refutation) =
        certify_arith_dpll_unsat(&mut arena, &assertions, &config(2)).unwrap()
    else {
        panic!("propositional contradiction must refute");
    };
    assert!(refutation.propositional_proof.is_some());
    assert!(refutation.verify_for(&arena, &assertions).unwrap());
    let unrelated = [arena.bool_const(false)];
    assert!(!refutation.verify_for(&arena, &unrelated).unwrap());
}

#[test]
fn both_public_sat_rows_replay_and_produce_checked_evidence() {
    for (name, text) in [("015-psyco-pp", PSYCO_PP), ("psyco-196", PSYCO_196)] {
        let mut script = parse_script(text).unwrap_or_else(|error| panic!("parse {name}: {error}"));
        let assertions = assertions(&script);
        let CheckResult::Sat(model) = solve(&mut script.arena, &assertions, &config(10))
            .unwrap_or_else(|error| panic!("solve {name}: {error}"))
        else {
            panic!("{name} must be SAT");
        };
        assert_eq!(model.quantified_bool_model_sat_certificates().count(), 1);
        assert!(check_model(&script.arena, &assertions, &model).unwrap());

        let report = produce_evidence(&mut script.arena, &assertions, &config(10))
            .unwrap_or_else(|error| panic!("evidence {name}: {error}"));
        assert!(matches!(report.evidence, Evidence::Sat(_)));
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(report.trusted_steps.is_empty());
    }
}

#[test]
fn remaining_unsat_row_is_never_accepted_as_boolean_guard_sat() {
    let mut script = parse_script(CBQI_ITE).expect("parse 006-cbqi-ite");
    let assertions = assertions(&script);
    match solve(&mut script.arena, &assertions, &config(1)) {
        Ok(CheckResult::Sat(_)) => panic!("006-cbqi-ite must never be accepted as SAT"),
        Ok(CheckResult::Unsat | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {}
        Err(error) => panic!("unexpected error for 006-cbqi-ite: {error}"),
    }
}

#[test]
fn model_6_1_bv_is_structurally_discharged_without_bv_certificate_values() {
    let mut script = parse_script(MODEL_6_1_BV).expect("parse model_6_1_bv");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) = solve(&mut script.arena, &assertions, &config(10)).unwrap()
    else {
        panic!("model_6_1_bv must be checked SAT");
    };
    assert_eq!(model.quantified_bool_model_sat_certificates().count(), 1);
    let certificate = model
        .quantified_bool_model_sat_certificates()
        .next()
        .unwrap();
    assert_eq!(certificate.values.len(), 4);
    assert!(
        certificate
            .values
            .iter()
            .all(|&(symbol, _)| { script.arena.symbol(symbol).1 == Sort::Bool })
    );
    assert!(check_model(&script.arena, &assertions, &model).unwrap());

    let report = produce_evidence(&mut script.arena, &assertions, &config(10)).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn opaque_bv_closures_require_a_decisive_boolean_branch() {
    for width in [1, 8, 32, 129] {
        let mut arena = TermArena::new();
        let p = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.declare("x", Sort::BitVec(width)).unwrap();
        let y = arena.declare("y", Sort::BitVec(width)).unwrap();
        let x_term = arena.var(x);
        let y_term = arena.var(y);
        let p_term = arena.var(p);
        let opaque = arena.bv_ult(x_term, y_term).unwrap();
        let body = arena.or(opaque, p_term).unwrap();
        let assertion = arena.forall(x, body).unwrap();

        let good = QuantifiedBoolModelSatCertificate {
            assertion,
            values: vec![(p, true)],
            proof: QuantifiedBoolModelSatProof::Structural,
        };
        assert!(check_quantified_bool_model_sat(&arena, assertion, &good));
        let bad = QuantifiedBoolModelSatCertificate {
            assertion,
            values: vec![(p, false)],
            proof: QuantifiedBoolModelSatProof::Structural,
        };
        assert!(!check_quantified_bool_model_sat(&arena, assertion, &bad));

        let CheckResult::Sat(mut model) = solve(&mut arena, &[assertion], &config(2)).unwrap()
        else {
            panic!("width {width} Boolean discharge must find p=true");
        };
        assert_eq!(model.get(p), Some(Value::Bool(true)));
        let certificate = model
            .quantified_bool_model_sat_certificates()
            .next()
            .unwrap();
        assert_eq!(certificate.values, vec![(p, true)]);
        assert!(check_model(&arena, &[assertion], &model).unwrap());
        if width <= 128 {
            let value = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            model.set(y, Value::Bv { width, value });
            assert!(
                check_model(&arena, &[assertion], &model).unwrap(),
                "width {width} replay must be independent of free-BV defaults"
            );
        }
    }
}

#[test]
fn unresolved_or_negative_bv_closures_never_receive_sat_credit() {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x_term = arena.var(x);
    let y_term = arena.var(y);
    let p_term = arena.var(p);
    let opaque = arena.bv_ult(x_term, y_term).unwrap();
    let unresolved_body = arena.and(p_term, opaque).unwrap();
    let unresolved = arena.forall(x, unresolved_body).unwrap();
    let unresolved_cert = QuantifiedBoolModelSatCertificate {
        assertion: unresolved,
        values: vec![(p, true)],
        proof: QuantifiedBoolModelSatProof::Structural,
    };
    assert!(!check_quantified_bool_model_sat(
        &arena,
        unresolved,
        &unresolved_cert
    ));

    let discharged_body = arena.or(p_term, opaque).unwrap();
    let positive = arena.forall(x, discharged_body).unwrap();
    let negative = arena.not(positive).unwrap();
    let stale = QuantifiedBoolModelSatCertificate {
        assertion: positive,
        values: vec![(p, true)],
        proof: QuantifiedBoolModelSatProof::Structural,
    };
    assert!(!check_quantified_bool_model_sat(&arena, negative, &stale));
    assert!(!check_quantified_bool_model_sat(
        &arena,
        negative,
        &QuantifiedBoolModelSatCertificate {
            assertion: negative,
            values: vec![(p, true)],
            proof: QuantifiedBoolModelSatProof::Structural,
        }
    ));
}

#[test]
fn free_int_arrays_and_functions_remain_outside_bv_opaque_admission() {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let i = arena.declare("i", Sort::Int).unwrap();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let array = arena.declare("a", array_sort).unwrap();
    let function = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let p_term = arena.var(p);
    let x_term = arena.var(x);

    let int_term = arena.var(i);
    let int_eq = arena.eq(int_term, int_term).unwrap();
    let int_body = arena.or(p_term, int_eq).unwrap();
    let int_assertion = arena.forall(x, int_body).unwrap();

    let array_term = arena.var(array);
    let array_eq = arena.eq(array_term, array_term).unwrap();
    let array_body = arena.or(p_term, array_eq).unwrap();
    let array_assertion = arena.forall(x, array_body).unwrap();

    let application = arena.apply(function, &[x_term]).unwrap();
    let function_eq = arena.eq(application, application).unwrap();
    let function_body = arena.or(p_term, function_eq).unwrap();
    let function_assertion = arena.forall(x, function_body).unwrap();

    for assertion in [int_assertion, array_assertion, function_assertion] {
        assert!(!check_quantified_bool_model_sat(
            &arena,
            assertion,
            &QuantifiedBoolModelSatCertificate {
                assertion,
                values: vec![(p, true)],
                proof: QuantifiedBoolModelSatProof::Structural,
            }
        ));
    }
}

#[test]
fn public_psyco_001_bv_has_source_bound_qfbv_evidence() {
    let mut script = parse_script(PSYCO_001_BV).expect("parse psyco-001-bv");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) = solve(&mut script.arena, &assertions, &config(10)).unwrap()
    else {
        panic!("psyco-001-bv must be checked SAT");
    };
    let certificate = qfbv_certificate(&model);
    assert_eq!(certificate.values.len(), 14);
    assert!(check_quantified_bool_model_sat(
        &script.arena,
        assertions[0],
        &certificate
    ));
    assert!(check_model(&script.arena, &assertions, &model).unwrap());

    let report = produce_evidence(&mut script.arena, &assertions, &config(10)).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn residual_qfbv_certificate_model_source_and_proof_tampering_fail_closed() {
    let mut script = parse_script(PSYCO_001_BV).expect("parse psyco-001-bv");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) = solve(&mut script.arena, &assertions, &config(10)).unwrap()
    else {
        panic!("psyco-001-bv must be checked SAT");
    };
    let certificate = qfbv_certificate(&model);

    let mut changed = certificate.clone();
    changed.values[0].1 = !changed.values[0].1;
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        assertions[0],
        &changed
    ));

    let mut missing = certificate.clone();
    missing.values.pop();
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        assertions[0],
        &missing
    ));

    let mut reordered = certificate.clone();
    reordered.values.swap(0, 1);
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        assertions[0],
        &reordered
    ));

    let mut proof_tamper = certificate.clone();
    let QuantifiedBoolModelSatProof::PositiveUniversalQfBv { residual_proof } =
        &mut proof_tamper.proof
    else {
        unreachable!()
    };
    residual_proof.dimacs.push_str("c tampered\n");
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        assertions[0],
        &proof_tamper
    ));

    let (changed_symbol, changed_value) = certificate.values[0];
    let changed_term = script.arena.var(changed_symbol);
    let false_under_model = if changed_value {
        script.arena.not(changed_term).unwrap()
    } else {
        changed_term
    };
    let changed_assertion = script.arena.and(assertions[0], false_under_model).unwrap();
    let mut source_tamper = certificate.clone();
    source_tamper.assertion = changed_assertion;
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        changed_assertion,
        &source_tamper
    ));

    let false_assertion = script.arena.bool_const(false);
    let mut stale = certificate.clone();
    stale.assertion = false_assertion;
    assert!(!check_quantified_bool_model_sat(
        &script.arena,
        false_assertion,
        &stale
    ));

    let mut model_tamper = model;
    let (symbol, value) = certificate.values[0];
    model_tamper.set(symbol, Value::Bool(!value));
    assert!(!check_model(&script.arena, &assertions, &model_tamper).unwrap());
}

#[test]
fn residual_qfbv_search_honors_an_expired_deadline() {
    let mut arena = TermArena::new();
    let (assertion, _) = cegis_bv_assertion(&mut arena, 32);
    match solve(
        &mut arena,
        &[assertion],
        &SolverConfig::new().with_timeout(Duration::ZERO),
    ) {
        Ok(CheckResult::Sat(_)) => panic!("expired residual-QF_BV search must not return SAT"),
        Ok(CheckResult::Unsat | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {}
        Err(error) => panic!("unexpected expired-search error: {error}"),
    }
}

#[test]
fn residual_qfbv_rejects_free_and_bound_symbol_aliasing() {
    let mut arena = TermArena::new();
    let p = arena.declare("captured_p", Sort::Bool).unwrap();
    let p_term = arena.var(p);
    let shadowed = arena.forall(p, p_term).unwrap();
    let assertion = arena.and(p_term, shadowed).unwrap();
    let false_term = arena.bool_const(false);
    let axeyum_solver::UnsatProofOutcome::Proved(false_proof) =
        export_qf_bv_unsat_proof(&arena, &[false_term]).unwrap()
    else {
        panic!("false must have a QF_BV refutation");
    };

    // Substituting p globally would turn the false `forall p. p` into true.
    assert!(!check_quantified_bool_model_sat(
        &arena,
        assertion,
        &QuantifiedBoolModelSatCertificate {
            assertion,
            values: vec![(p, true)],
            proof: QuantifiedBoolModelSatProof::PositiveUniversalQfBv {
                residual_proof: false_proof,
            },
        }
    ));
}

#[test]
fn residual_qfbv_admission_and_resource_boundaries_fail_closed() {
    let mut arena = TermArena::new();
    let (assertion, p) = cegis_bv_assertion(&mut arena, 4);
    let CheckResult::Sat(model) = solve(&mut arena, &[assertion], &config(5)).unwrap() else {
        panic!("generated CEGIS formula must be checked SAT");
    };
    assert_eq!(model.get(p), Some(Value::Bool(true)));
    let certificate = qfbv_certificate(&model);
    let p_term = arena.var(p);

    let rejected = |arena: &TermArena, changed_assertion| {
        let mut changed = certificate.clone();
        changed.assertion = changed_assertion;
        assert!(!check_quantified_bool_model_sat(
            arena,
            changed_assertion,
            &changed
        ));
    };

    let negative = arena.not(assertion).unwrap();
    rejected(&arena, negative);

    let y = arena.declare("exists_y", Sort::BitVec(4)).unwrap();
    let y_term = arena.var(y);
    let zero = arena.bv_const(4, 0).unwrap();
    let y_zero = arena.eq(y_term, zero).unwrap();
    let exists_body = arena.or(p_term, y_zero).unwrap();
    let existential = arena.exists(y, exists_body).unwrap();
    rejected(&arena, existential);

    let free_bv = arena.declare("free_bv", Sort::BitVec(4)).unwrap();
    let bound_bv = arena.declare("bound_bv", Sort::BitVec(4)).unwrap();
    let free_term = arena.var(free_bv);
    let bound_term = arena.var(bound_bv);
    let free_eq_bound = arena.eq(free_term, bound_term).unwrap();
    let free_bv_body = arena.or(p_term, free_eq_bound).unwrap();
    let free_bv_assertion = arena.forall(bound_bv, free_bv_body).unwrap();
    rejected(&arena, free_bv_assertion);

    let integer = arena.declare("mixed_int", Sort::Int).unwrap();
    let integer_term = arena.var(integer);
    let int_zero = arena.int_const(0);
    let integer_eq = arena.eq(integer_term, int_zero).unwrap();
    let mixed_body = arena.or(p_term, integer_eq).unwrap();
    let mixed = arena.forall(integer, mixed_body).unwrap();
    rejected(&arena, mixed);

    let function = arena
        .declare_fun("boundary_f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let application = arena.apply(function, &[bound_term]).unwrap();
    let application_eq = arena.eq(application, bound_term).unwrap();
    let function_body = arena.or(p_term, application_eq).unwrap();
    let function_assertion = arena.forall(bound_bv, function_body).unwrap();
    rejected(&arena, function_assertion);

    let mut too_many_binders = assertion;
    for index in 0..129 {
        let binder = arena
            .declare(&format!("excess_binder_{index}"), Sort::Bool)
            .unwrap();
        too_many_binders = arena.forall(binder, too_many_binders).unwrap();
    }
    rejected(&arena, too_many_binders);

    let true_term = arena.bool_const(true);
    let mut too_deep = assertion;
    for _ in 0..257 {
        too_deep = arena.and(true_term, too_deep).unwrap();
    }
    rejected(&arena, too_deep);

    let node_binder = arena.declare("node_binder", Sort::BitVec(13)).unwrap();
    let node_var = arena.var(node_binder);
    let mut node_terms = (0..4097)
        .map(|value| {
            let constant = arena.bv_const(13, value).unwrap();
            arena.eq(node_var, constant).unwrap()
        })
        .collect::<Vec<_>>();
    while node_terms.len() > 1 {
        node_terms = node_terms
            .chunks(2)
            .map(|pair| {
                if let [left, right] = pair {
                    arena.and(*left, *right).unwrap()
                } else {
                    pair[0]
                }
            })
            .collect();
    }
    let oversized_body = arena.or(p_term, node_terms[0]).unwrap();
    let oversized = arena.forall(node_binder, oversized_body).unwrap();
    rejected(&arena, oversized);
}

#[cfg(feature = "z3")]
#[test]
fn generated_residual_qfbv_cegis_models_and_unsat_controls_match_z3() {
    use z3::ast::{Ast, BV, Bool};
    use z3::{Params, SatResult, Solver};

    for case in 0..32 {
        let width = [2, 4, 8, 16][case % 4];
        let unsat_control = case % 2 == 1;
        let mut arena = TermArena::new();
        let (assertion, p) = cegis_bv_assertion(&mut arena, width);
        let mut ax_assertions = vec![assertion];
        if unsat_control {
            let p_term = arena.var(p);
            ax_assertions.push(arena.not(p_term).unwrap());
        }
        let axeyum = solve(&mut arena, &ax_assertions, &config(5));

        let zp = Bool::new_const(format!("p_{case}"));
        let zb = Bool::new_const(format!("b_{case}"));
        let zx = BV::new_const(format!("x_{case}"), width);
        let zzero = BV::from_u64(0, width);
        let zguard = Bool::or(&[zb.clone(), zp.not()]);
        let zselected = zb.ite(&zx, &zzero);
        let zconclusion = zselected.eq(&zx);
        let zbody = zguard.implies(&zconclusion);
        let zforall = z3::ast::forall_const(&[&zb as &dyn Ast, &zx as &dyn Ast], &[], &zbody);
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 5_000);
        oracle.set_params(&params);
        oracle.assert(&zforall);
        if unsat_control {
            oracle.assert(zp.not());
        }
        let z3 = oracle.check();

        match (unsat_control, axeyum, z3) {
            (false, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                assert_eq!(model.get(p), Some(Value::Bool(true)));
                let certificate = qfbv_certificate(&model);
                assert!(check_quantified_bool_model_sat(
                    &arena,
                    assertion,
                    &certificate
                ));
                assert!(check_model(&arena, &ax_assertions, &model).unwrap());
            }
            (
                true,
                Ok(CheckResult::Unsat | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)),
                SatResult::Unsat,
            ) => {}
            (mode, result, oracle) => panic!(
                "generated residual-QF_BV case {case} (unsat={mode}) disagreed: axeyum={result:?}, z3={oracle:?}"
            ),
        }
    }
}
