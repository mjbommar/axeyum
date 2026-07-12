//! ADR-0130 checked free-BV models with affine-LSB and witness replay.

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
