//! ADR-0130/0131/0132 checked free-BV models with affine-LSB, witness replay,
//! signed-interval containment, and zero-product annihilation.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, QUANT_BV_MODEL_BINDER_CAP, QUANT_BV_MODEL_DEPTH_CAP,
    QUANT_BV_MODEL_NODE_CAP, QuantifiedBvModelSatCertificate, QuantifiedBvModelSatProof,
    SolverConfig, check_model, check_quantified_bv_model_sat, produce_evidence, solve,
};

const TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__smtcomp-qbv-053118.smt2"
);
const INTERVAL_TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__intersection-example-onelane.proof-node22337.smt2"
);
const ZERO_PRODUCT_TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress2__quantifiers__gn-wrong-091018.smt2"
);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

fn target_model() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    axeyum_solver::Model,
) {
    let mut script = parse_script(TARGET).expect("target parses");
    let assertions = script.assertions.clone();
    let result = solve(&mut script.arena, &assertions, &config()).expect("target solves");
    let CheckResult::Sat(model) = result else {
        panic!("target must be Sat, got {result:?}");
    };
    assert_eq!(model.quantified_bv_model_sat_certificates().count(), 2);
    assert!(check_model(&script.arena, &assertions, &model).expect("target model replays"));
    (script, assertions, model)
}

fn interval_target_model() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    axeyum_solver::Model,
) {
    let mut script = parse_script(INTERVAL_TARGET).expect("interval target parses");
    let assertions = script.assertions.clone();
    let result = solve(&mut script.arena, &assertions, &config()).expect("interval target solves");
    let CheckResult::Sat(model) = result else {
        panic!("interval target must be Sat, got {result:?}");
    };
    assert_eq!(model.quantified_bv_model_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("interval model replays"));
    (script, assertions, model)
}

fn zero_product_target_model() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    axeyum_solver::Model,
) {
    let mut script = parse_script(ZERO_PRODUCT_TARGET).expect("zero-product target parses");
    let assertions = script.assertions.clone();
    let result = solve(&mut script.arena, &assertions, &config()).expect("target solves");
    let CheckResult::Sat(model) = result else {
        panic!("zero-product target must be Sat, got {result:?}");
    };
    assert_eq!(model.quantified_bv_model_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("target model replays"));
    (script, assertions, model)
}

#[test]
fn public_gn_wrong_row_has_checked_zero_product_model_evidence() {
    let (mut script, assertions, model) = zero_product_target_model();
    let certificate = model
        .quantified_bv_model_sat_certificate(assertions[0])
        .expect("zero-product certificate");
    assert!(matches!(
        certificate.proof,
        QuantifiedBvModelSatProof::NegatedExistentialZeroProductImplication { .. }
    ));
    // The top-level declaration sharing the binder's printed name is shadowed
    // and unused; exact source coverage therefore has ten free symbols.
    assert_eq!(certificate.free_values.len(), 10);
    assert!(check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        certificate
    ));

    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("zero-product evidence production");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn zero_product_model_tampering_fails_closed() {
    let (script, assertions, model) = zero_product_target_model();
    let certificate = model
        .quantified_bv_model_sat_certificate(assertions[0])
        .expect("zero-product certificate")
        .clone();

    let mut wrong_binder = certificate.clone();
    let QuantifiedBvModelSatProof::NegatedExistentialZeroProductImplication { binder } =
        &mut wrong_binder.proof
    else {
        panic!("expected zero-product proof")
    };
    *binder = certificate.free_values[0].0;
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &wrong_binder
    ));

    let mut all_zero = certificate.clone();
    for (_, value) in &mut all_zero.free_values {
        *value = Value::Bv {
            width: 32,
            value: 0,
        };
    }
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &all_zero
    ));

    let mut missing = certificate;
    missing.free_values.pop();
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &missing
    ));
}

#[test]
fn zero_product_checker_requires_exact_annihilation_source_shape() {
    let mut arena = TermArena::new();
    let width = 129;
    let sort = Sort::BitVec(width);
    let binder = arena.declare("zero_product_binder", sort).unwrap();
    let bound = arena.var(binder);
    let zero = arena.bv_const(width, 0).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let zero_division = arena.bv_sdiv(one, two).unwrap();
    let nonlinear = arena.bv_mul(bound, bound).unwrap();
    let product = arena.bv_mul(nonlinear, zero_division).unwrap();
    let nonnegative = arena.bv_sge(product, zero).unwrap();
    let premise = arena.eq(bound, bound).unwrap();
    let inner = arena.implies(premise, nonnegative).unwrap();
    let false_term = arena.bool_const(false);
    let body = arena.implies(inner, false_term).unwrap();
    let exists = arena.exists(binder, body).unwrap();
    let assertion = arena.not(exists).unwrap();
    let certificate = QuantifiedBvModelSatCertificate {
        assertion,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::NegatedExistentialZeroProductImplication { binder },
    };
    assert!(check_quantified_bv_model_sat(
        &arena,
        assertion,
        &certificate
    ));

    let one_division = arena.bv_sdiv(two, two).unwrap();
    let nonzero_product = arena.bv_mul(one_division, bound).unwrap();
    let nonzero_comparison = arena.bv_sge(nonzero_product, zero).unwrap();
    let nonzero_inner = arena.implies(premise, nonzero_comparison).unwrap();
    let nonzero_body = arena.implies(nonzero_inner, false_term).unwrap();
    let nonzero_exists = arena.exists(binder, nonzero_body).unwrap();
    let nonzero_assertion = arena.not(nonzero_exists).unwrap();
    let nonzero_certificate = QuantifiedBvModelSatCertificate {
        assertion: nonzero_assertion,
        ..certificate.clone()
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        nonzero_assertion,
        &nonzero_certificate
    ));

    let literal_product = arena.bv_mul(zero, bound).unwrap();
    let literal_comparison = arena.bv_sge(literal_product, zero).unwrap();
    let literal_inner = arena.implies(premise, literal_comparison).unwrap();
    let literal_body = arena.implies(literal_inner, false_term).unwrap();
    let literal_exists = arena.exists(binder, literal_body).unwrap();
    let literal_assertion = arena.not(literal_exists).unwrap();
    let literal_certificate = QuantifiedBvModelSatCertificate {
        assertion: literal_assertion,
        ..certificate.clone()
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        literal_assertion,
        &literal_certificate
    ));

    let nonzero_bound = arena.bv_sge(product, one).unwrap();
    let nonzero_bound_inner = arena.implies(premise, nonzero_bound).unwrap();
    let nonzero_bound_body = arena.implies(nonzero_bound_inner, false_term).unwrap();
    let nonzero_bound_exists = arena.exists(binder, nonzero_bound_body).unwrap();
    let nonzero_bound_assertion = arena.not(nonzero_bound_exists).unwrap();
    let nonzero_bound_certificate = QuantifiedBvModelSatCertificate {
        assertion: nonzero_bound_assertion,
        ..certificate.clone()
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        nonzero_bound_assertion,
        &nonzero_bound_certificate
    ));

    let wrong_comparison = arena.bv_sle(product, zero).unwrap();
    let wrong_inner = arena.implies(premise, wrong_comparison).unwrap();
    let wrong_body = arena.implies(wrong_inner, false_term).unwrap();
    let wrong_exists = arena.exists(binder, wrong_body).unwrap();
    let wrong_assertion = arena.not(wrong_exists).unwrap();
    let wrong_certificate = QuantifiedBvModelSatCertificate {
        assertion: wrong_assertion,
        ..certificate
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        wrong_assertion,
        &wrong_certificate
    ));
}

#[test]
fn public_intersection_row_has_checked_interval_model_evidence() {
    let (mut script, assertions, model) = interval_target_model();
    let certificate = model
        .quantified_bv_model_sat_certificate(assertions[0])
        .expect("interval certificate");
    assert!(matches!(
        certificate.proof,
        QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication { .. }
    ));
    assert_eq!(certificate.free_values.len(), 12);
    assert!(check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        certificate
    ));

    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("interval evidence production");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn interval_model_tampering_fails_closed() {
    let (script, assertions, model) = interval_target_model();
    let certificate = model
        .quantified_bv_model_sat_certificate(assertions[0])
        .expect("interval certificate")
        .clone();

    let mut wrong_binder = certificate.clone();
    let QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication { binder } =
        &mut wrong_binder.proof
    else {
        panic!("expected interval proof")
    };
    *binder = certificate.free_values[0].0;
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &wrong_binder
    ));

    let mut all_zero = certificate.clone();
    for (_, value) in &mut all_zero.free_values {
        *value = Value::Bv {
            width: 32,
            value: 0,
        };
    }
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &all_zero
    ));

    let mut missing = certificate;
    missing.free_values.pop();
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &missing
    ));
}

#[test]
fn empty_interval_vacuity_and_binder_leakage_are_not_credited() {
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let binder = arena.declare("interval_binder", sort).unwrap();
    let bound = arena.var(binder);
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let lower = arena.bv_sle(one, bound).unwrap();
    let upper = arena.bv_sle(bound, zero).unwrap();
    let range = arena.and(lower, upper).unwrap();
    let contained = arena.bv_sle(bound, one).unwrap();
    let interval = arena.implies(range, contained).unwrap();
    let false_term = arena.bool_const(false);
    let body = arena.implies(interval, false_term).unwrap();
    let exists = arena.exists(binder, body).unwrap();
    let assertion = arena.not(exists).unwrap();
    let certificate = QuantifiedBvModelSatCertificate {
        assertion,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication { binder },
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        assertion,
        &certificate
    ));

    let leaked_conclusion = arena.eq(bound, bound).unwrap();
    let leaked_body = arena.implies(interval, leaked_conclusion).unwrap();
    let leaked_exists = arena.exists(binder, leaked_body).unwrap();
    let leaked = arena.not(leaked_exists).unwrap();
    let leaked_certificate = QuantifiedBvModelSatCertificate {
        assertion: leaked,
        ..certificate
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        leaked,
        &leaked_certificate
    ));
}

#[test]
fn public_smtcomp_row_has_checked_bv_model_evidence() {
    let (mut script, assertions, model) = target_model();
    let certificates = model
        .quantified_bv_model_sat_certificates()
        .cloned()
        .collect::<Vec<_>>();
    assert!(matches!(
        certificates[0].proof,
        QuantifiedBvModelSatProof::AffineLsbUniversal
    ));
    assert!(matches!(
        certificates[1].proof,
        QuantifiedBvModelSatProof::NegatedUniversalWitness { .. }
    ));
    assert_eq!(certificates[0].free_values, certificates[1].free_values);
    assert!(matches!(
        certificates[0].free_values.as_slice(),
        [(
            _,
            Value::Bv {
                width: 32,
                value: 0
            }
        )]
    ));

    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("target evidence production");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn free_model_and_witness_tampering_fail_closed() {
    let (mut script, assertions, model) = target_model();
    let parity = model
        .quantified_bv_model_sat_certificate(assertions[0])
        .expect("parity certificate")
        .clone();
    let witness = model
        .quantified_bv_model_sat_certificate(assertions[1])
        .expect("witness certificate")
        .clone();

    let mut wrong_free_value = parity.clone();
    wrong_free_value.free_values[0].1 = Value::Bv {
        width: 32,
        value: 1,
    };
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &wrong_free_value
    ));

    let mut missing_free_value = parity.clone();
    missing_free_value.free_values.clear();
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &missing_free_value
    ));

    let mut wrong_witness = witness.clone();
    let QuantifiedBvModelSatProof::NegatedUniversalWitness { values, .. } =
        &mut wrong_witness.proof
    else {
        panic!("second certificate must carry a witness")
    };
    values.fill(Value::Bv {
        width: 32,
        value: 0,
    });
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[1],
        &wrong_witness
    ));

    let mut stale = parity;
    stale.assertion = script.arena.bool_const(true);
    assert!(!check_quantified_bv_model_sat(
        &script.arena,
        assertions[0],
        &stale
    ));

    let mut extra_model = model;
    extra_model.set_quantified_bv_model_sat_certificate(stale);
    assert!(!check_model(&script.arena, &assertions, &extra_model).unwrap());
}

#[test]
fn nonlinear_lsb_and_changed_polarity_are_not_credited() {
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(8);
    let a = arena.declare("a", sort).unwrap();
    let av = arena.var(a);
    let square = arena.bv_mul(av, av).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let successor = arena.bv_add(square, one).unwrap();
    let equality = arena.eq(square, successor).unwrap();
    let disequality = arena.not(equality).unwrap();
    let valid_but_nonlinear = arena.forall(a, disequality).unwrap();
    let cert = QuantifiedBvModelSatCertificate {
        assertion: valid_but_nonlinear,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::AffineLsbUniversal,
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        valid_but_nonlinear,
        &cert
    ));

    let changed_polarity = arena.exists(a, disequality).unwrap();
    let changed = QuantifiedBvModelSatCertificate {
        assertion: changed_polarity,
        ..cert
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        changed_polarity,
        &changed
    ));
}

#[test]
fn source_binder_depth_and_node_caps_are_enforced() {
    let mut arena = TermArena::new();
    let mut body = arena.bool_const(true);
    for index in 0..=QUANT_BV_MODEL_BINDER_CAP {
        let binder = arena
            .declare(&format!("cap_binder_{index}"), Sort::Bool)
            .unwrap();
        body = arena.forall(binder, body).unwrap();
    }
    let over_binders = QuantifiedBvModelSatCertificate {
        assertion: body,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::AffineLsbUniversal,
    };
    assert!(!check_quantified_bv_model_sat(&arena, body, &over_binders));

    let binder = arena.declare("depth_cap_binder", Sort::Bool).unwrap();
    let mut deep = arena.bool_const(false);
    for _ in 0..=QUANT_BV_MODEL_DEPTH_CAP {
        deep = arena.not(deep).unwrap();
    }
    let over_depth_assertion = arena.forall(binder, deep).unwrap();
    let over_depth = QuantifiedBvModelSatCertificate {
        assertion: over_depth_assertion,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::AffineLsbUniversal,
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        over_depth_assertion,
        &over_depth
    ));

    let node_binder = arena.declare("node_cap_binder", Sort::Bool).unwrap();
    let mut level = (0..=(QUANT_BV_MODEL_NODE_CAP / 2))
        .map(|index| {
            let value = arena.bv_const(32, u128::try_from(index).unwrap()).unwrap();
            arena.eq(value, value).unwrap()
        })
        .collect::<Vec<_>>();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            next.push(if let [left, right] = pair {
                arena.and(*left, *right).unwrap()
            } else {
                pair[0]
            });
        }
        level = next;
    }
    let over_node_assertion = arena.forall(node_binder, level[0]).unwrap();
    let over_nodes = QuantifiedBvModelSatCertificate {
        assertion: over_node_assertion,
        free_values: Vec::new(),
        proof: QuantifiedBvModelSatProof::AffineLsbUniversal,
    };
    assert!(!check_quantified_bv_model_sat(
        &arena,
        over_node_assertion,
        &over_nodes
    ));
}

#[cfg(feature = "z3")]
#[test]
#[allow(clippy::many_single_char_names, clippy::too_many_lines)]
fn generated_affine_lsb_models_and_unsat_controls_match_z3() {
    use z3::ast::{Ast, BV};
    use z3::{Params, SatResult, Solver};

    const CASES: usize = 64;
    const WIDTHS: [u32; 8] = [1, 2, 4, 8, 16, 32, 64, 127];
    let mut certified_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_decline = 0usize;
    for case in 0..CASES {
        let width = WIDTHS[(case / 2) % WIDTHS.len()];
        let constant = u128::try_from((case * 13 + 1) & 1).unwrap();
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let two_value = 2 & mask;
        let witness_constant = u128::try_from(case * 7 + 3).unwrap() & mask;
        let expected_x = constant ^ 1;
        let unsat_control = case % 2 == 1;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let x = arena.declare("generated_x", sort).unwrap();
        let a = arena.declare("generated_a", sort).unwrap();
        let b = arena.declare("generated_b", sort).unwrap();
        let m = arena.declare("generated_m", sort).unwrap();
        let n = arena.declare("generated_n", sort).unwrap();
        let xv = arena.var(x);
        let av = arena.var(a);
        let bv = arena.var(b);
        let mv = arena.var(m);
        let nv = arena.var(n);
        let two = arena.bv_const(width, two_value).unwrap();
        let c = arena.bv_const(width, constant).unwrap();
        let k = arena.bv_const(width, witness_constant).unwrap();
        let left = arena.bv_mul(two, av).unwrap();
        let two_b = arena.bv_mul(two, bv).unwrap();
        let right_prefix = arena.bv_add(two_b, xv).unwrap();
        let right = arena.bv_add(right_prefix, c).unwrap();
        let equality = arena.eq(left, right).unwrap();
        let disequality = arena.not(equality).unwrap();
        let universal = arena.forall(b, disequality).unwrap();
        let universal = arena.forall(a, universal).unwrap();

        let m_plus_x = arena.bv_add(mv, xv).unwrap();
        let negative = arena.bv_neg(m_plus_x).unwrap();
        let witness_left = arena.bv_add(negative, k).unwrap();
        let witness_right = arena.bv_mul(two, nv).unwrap();
        let witness_eq = arena.eq(witness_left, witness_right).unwrap();
        let no_witness = arena.not(witness_eq).unwrap();
        let no_witness = arena.forall(n, no_witness).unwrap();
        let no_witness = arena.forall(m, no_witness).unwrap();
        let exists_witness = arena.not(no_witness).unwrap();
        let mut assertions = vec![universal, exists_witness];
        if unsat_control {
            let bad = arena.bv_const(width, expected_x ^ 1).unwrap();
            assertions.push(arena.eq(xv, bad).unwrap());
        }
        let axeyum = solve(
            &mut arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_millis(250)),
        );

        let zx = BV::new_const("generated_x", width);
        let za = BV::new_const("generated_a", width);
        let zb = BV::new_const("generated_b", width);
        let zm = BV::new_const("generated_m", width);
        let zn = BV::new_const("generated_n", width);
        let ztwo = BV::from_u64(u64::try_from(two_value).unwrap(), width);
        let zc = BV::from_u64(u64::try_from(constant).unwrap(), width);
        let zk = BV::from_u64(u64::try_from(witness_constant).unwrap(), width);
        let zleft = ztwo.bvmul(&za);
        let zright = ztwo.bvmul(&zb).bvadd(&zx).bvadd(&zc);
        let zuniversal_body = zleft.eq(&zright).not();
        let zuniversal =
            z3::ast::forall_const(&[&za as &dyn Ast, &zb as &dyn Ast], &[], &zuniversal_body);
        let zwitness_eq = zm.bvadd(&zx).bvneg().bvadd(&zk).eq(ztwo.bvmul(&zn));
        let zno_witness =
            z3::ast::forall_const(&[&zm as &dyn Ast, &zn as &dyn Ast], &[], &zwitness_eq.not());
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 250);
        oracle.set_params(&params);
        oracle.assert(&zuniversal);
        oracle.assert(zno_witness.not());
        if unsat_control {
            oracle.assert(zx.eq(BV::from_u64(u64::try_from(expected_x ^ 1).unwrap(), width)));
        }
        let z3 = oracle.check();

        match (unsat_control, axeyum, z3) {
            (false, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                assert_eq!(model.quantified_bv_model_sat_certificates().count(), 2);
                assert!(check_model(&arena, &assertions, &model).unwrap());
                certified_sat += 1;
            }
            (true, Ok(CheckResult::Unsat), SatResult::Unsat) => agreed_unsat += 1,
            (true, Ok(CheckResult::Unknown(_)) | Err(_), SatResult::Unsat)
            | (_, _, SatResult::Unknown) => safe_decline += 1,
            (mode, result, oracle) => panic!(
                "generated case {case} (unsat={mode}) disagreed: axeyum={result:?}, z3={oracle:?}"
            ),
        }
    }
    assert_eq!(certified_sat, CASES / 2);
    assert_eq!(certified_sat + agreed_unsat + safe_decline, CASES);
}

#[cfg(feature = "z3")]
#[test]
fn generated_interval_models_and_false_conclusion_controls_match_z3() {
    use z3::ast::{Ast, BV, Bool};
    use z3::{Params, SatResult, Solver};

    const CASES: usize = 32;
    const WIDTHS: [u32; 4] = [2, 4, 8, 16];
    let mut certified_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_decline = 0usize;
    for case in 0..CASES {
        let width = WIDTHS[(case / 2) % WIDTHS.len()];
        let unsat_control = case % 2 == 1;
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let lower_symbol = arena.declare("generated_interval_lower", sort).unwrap();
        let upper_symbol = arena.declare("generated_interval_upper", sort).unwrap();
        let cap_symbol = arena.declare("generated_interval_cap", sort).unwrap();
        let guard_symbol = arena.declare("generated_interval_guard", sort).unwrap();
        let binder = arena.declare("generated_interval_binder", sort).unwrap();
        let lower_value = arena.var(lower_symbol);
        let upper_value = arena.var(upper_symbol);
        let cap_value = arena.var(cap_symbol);
        let guard_value = arena.var(guard_symbol);
        let bound = arena.var(binder);
        let lower_bound = arena.bv_sle(lower_value, bound).unwrap();
        let upper_bound = arena.bv_sle(bound, upper_value).unwrap();
        let range = arena.and(lower_bound, upper_bound).unwrap();
        let contained = arena.bv_sle(bound, cap_value).unwrap();
        let interval = arena.implies(range, contained).unwrap();
        let ground = arena.eq(guard_value, guard_value).unwrap();
        let antecedent = arena.and(ground, interval).unwrap();
        let conclusion = arena.bool_const(unsat_control);
        let body = arena.implies(antecedent, conclusion).unwrap();
        let quantified = arena.exists(binder, body).unwrap();
        let assertion = arena.not(quantified).unwrap();
        let assertions = [assertion];
        let axeyum = solve(
            &mut arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_millis(500)),
        );

        let zlower = BV::new_const("generated_interval_lower", width);
        let zupper = BV::new_const("generated_interval_upper", width);
        let zcap = BV::new_const("generated_interval_cap", width);
        let zguard = BV::new_const("generated_interval_guard", width);
        let zbound = BV::new_const("generated_interval_binder", width);
        let zrange = Bool::and(&[zlower.bvsle(&zbound), zbound.bvsle(&zupper)]);
        let zinterval = zrange.implies(zbound.bvsle(&zcap));
        let zground = zguard.eq(&zguard);
        let zantecedent = Bool::and(&[zground, zinterval]);
        let zbody = zantecedent.implies(Bool::from_bool(unsat_control));
        let zquantified = z3::ast::exists_const(&[&zbound as &dyn Ast], &[], &zbody);
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 500);
        oracle.set_params(&params);
        oracle.assert(zquantified.not());
        let z3 = oracle.check();

        match (unsat_control, axeyum, z3) {
            (false, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                let certificate = model
                    .quantified_bv_model_sat_certificate(assertion)
                    .expect("generated interval certificate");
                assert!(matches!(
                    certificate.proof,
                    QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication { .. }
                ));
                assert!(check_model(&arena, &assertions, &model).unwrap());
                certified_sat += 1;
            }
            (true, Ok(CheckResult::Unsat), SatResult::Unsat) => agreed_unsat += 1,
            (true, Ok(CheckResult::Unknown(_)) | Err(_), SatResult::Unsat) => safe_decline += 1,
            (mode, result, oracle) => panic!(
                "generated interval case {case} (unsat={mode}) disagreed: axeyum={result:?}, z3={oracle:?}"
            ),
        }
    }
    assert_eq!(certified_sat, CASES / 2);
    assert_eq!(certified_sat + agreed_unsat + safe_decline, CASES);
}

#[cfg(feature = "z3")]
#[test]
fn generated_zero_product_models_and_nonzero_factor_controls_match_z3() {
    use z3::ast::{Ast, BV, Bool};
    use z3::{Params, SatResult, Solver};

    const CASES: usize = 32;
    const WIDTHS: [u32; 4] = [2, 4, 8, 16];
    let mut certified_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_decline = 0usize;
    for case in 0..CASES {
        let width = WIDTHS[(case / 2) % WIDTHS.len()];
        let unsat_control = case % 2 == 1;
        let numerator_value = u128::from(unsat_control) + 1;
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let numerator_symbol = arena.declare("generated_zero_numerator", sort).unwrap();
        let binder = arena.declare("generated_zero_binder", sort).unwrap();
        let numerator = arena.var(numerator_symbol);
        let bound = arena.var(binder);
        let expected_numerator = arena.bv_const(width, numerator_value).unwrap();
        let two = arena.bv_const(width, 2).unwrap();
        let zero = arena.bv_const(width, 0).unwrap();
        let ground = arena.eq(numerator, expected_numerator).unwrap();
        let factor = arena.bv_sdiv(numerator, two).unwrap();
        let product = if case % 4 < 2 {
            arena.bv_mul(factor, bound).unwrap()
        } else {
            arena.bv_mul(bound, factor).unwrap()
        };
        let nonnegative = arena.bv_sge(product, zero).unwrap();
        let premise = arena.eq(bound, bound).unwrap();
        let inner = arena.implies(premise, nonnegative).unwrap();
        let antecedent = arena.and(ground, inner).unwrap();
        let false_term = arena.bool_const(false);
        let body = arena.implies(antecedent, false_term).unwrap();
        let quantified = arena.exists(binder, body).unwrap();
        let assertion = arena.not(quantified).unwrap();
        let assertions = [assertion];
        let axeyum = solve(
            &mut arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_millis(500)),
        );

        let znumerator = BV::new_const("generated_zero_numerator", width);
        let zbound = BV::new_const("generated_zero_binder", width);
        let zexpected = BV::from_u64(u64::try_from(numerator_value).unwrap(), width);
        let ztwo = BV::from_u64(2, width);
        let oracle_zero = BV::from_u64(0, width);
        let zground = znumerator.eq(&zexpected);
        let zfactor = znumerator.bvsdiv(&ztwo);
        let zproduct = if case % 4 < 2 {
            zfactor.bvmul(&zbound)
        } else {
            zbound.bvmul(&zfactor)
        };
        let zinner = zbound.eq(&zbound).implies(zproduct.bvsge(&oracle_zero));
        let zantecedent = Bool::and(&[zground, zinner]);
        let zbody = zantecedent.implies(Bool::from_bool(false));
        let zquantified = z3::ast::exists_const(&[&zbound as &dyn Ast], &[], &zbody);
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 500);
        oracle.set_params(&params);
        oracle.assert(zquantified.not());
        let z3 = oracle.check();

        match (unsat_control, axeyum, z3) {
            (false, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                let certificate = model
                    .quantified_bv_model_sat_certificate(assertion)
                    .expect("generated zero-product certificate");
                assert!(matches!(
                    certificate.proof,
                    QuantifiedBvModelSatProof::NegatedExistentialZeroProductImplication { .. }
                ));
                assert!(check_model(&arena, &assertions, &model).unwrap());
                certified_sat += 1;
            }
            (true, Ok(CheckResult::Unsat), SatResult::Unsat) => agreed_unsat += 1,
            (true, Ok(CheckResult::Unknown(_)) | Err(_), SatResult::Unsat) => safe_decline += 1,
            (mode, result, oracle) => panic!(
                "generated zero-product case {case} (unsat={mode}) disagreed: axeyum={result:?}, z3={oracle:?}"
            ),
        }
    }
    assert_eq!(certified_sat, CASES / 2);
    assert_eq!(certified_sat + agreed_unsat + safe_decline, CASES);
}
