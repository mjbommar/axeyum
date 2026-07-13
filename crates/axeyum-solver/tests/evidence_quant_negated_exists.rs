//! ADR-0126 evaluator-replayed witnesses for negated existentials.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, NEGATED_EXISTENTIAL_BINDER_CAP, NEGATED_EXISTENTIAL_NODE_CAP,
    NegatedExistentialWitnessCertificate, ProofFragment, SolverConfig,
    check_negated_existential_witness, produce_evidence, prove_unsat_to_lean_module,
    reconstruct_negated_existential_witness_to_lean_module, scan_proof_fragment, solve,
};

const NUM878: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__NUM878.smt2"
);
const ARI_SYQI: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__ari-syqi.smt2"
);
const ARI118: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__ari118-bv-2occ-x.smt2"
);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

fn target_certificate(
    text: &str,
) -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    NegatedExistentialWitnessCertificate,
) {
    let mut script = parse_script(text).expect("target parses");
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &config()).expect("target evidence");
    let Evidence::UnsatNegatedExistentialWitness(certificate) = report.evidence else {
        panic!(
            "expected ADR-0126 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(report.trusted_steps.is_empty());
    assert!(check_negated_existential_witness(
        &script.arena,
        &assertions,
        &certificate
    ));
    (script, assertions, certificate)
}

#[test]
fn three_minimal_public_rows_gain_checked_evidence() {
    for (name, text, binding_count) in [
        ("NUM878", NUM878, 1),
        ("ari-syqi", ARI_SYQI, 1),
        ("ari118-bv-2occ-x", ARI118, 2),
    ] {
        let (mut script, assertions, certificate) = target_certificate(text);
        assert_eq!(certificate.assertion, assertions[0], "{name}");
        assert_eq!(certificate.bindings.len(), binding_count, "{name}");

        let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
        assert_eq!(
            report.evidence.kind_label(),
            "unsat-negated-existential-witness"
        );
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(matches!(
            solve(&mut script.arena, &assertions, &config()).unwrap(),
            CheckResult::Unsat
        ));
    }
}

#[test]
fn small_nested_bool_bv_witness_reconstructs_and_routes_deterministically() {
    let text = "(set-logic BV)
        (assert (not (exists ((b Bool) (x (_ BitVec 21)))
          (and b (= x x)))))
        (check-sat)";
    let (mut script, assertions, certificate) = target_certificate(text);
    let direct = reconstruct_negated_existential_witness_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("small typed witness reconstructs");
    assert!(direct.contains("theorem axeyum_refutation : False"));
    assert!(!direct.contains("sorryAx"));
    assert_eq!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::NegatedExistentialWitness
    );
    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("small typed witness routes");
    assert_eq!(fragment, ProofFragment::NegatedExistentialWitness);
    assert_eq!(routed, direct);
}

#[test]
#[ignore = "release-only public-corpus Lean reconstruction stress gate"]
fn three_public_rows_gain_genuine_typed_lean_reconstruction() {
    for (name, text) in [
        ("NUM878", NUM878),
        ("ari-syqi", ARI_SYQI),
        ("ari118-bv-2occ-x", ARI118),
    ] {
        let (script, assertions, certificate) = target_certificate(text);
        let direct = reconstruct_negated_existential_witness_to_lean_module(
            &script.arena,
            &assertions,
            &certificate,
        )
        .unwrap_or_else(|error| panic!("{name}: direct reconstruction failed: {error}"));
        assert!(
            direct.contains("theorem axeyum_refutation : False"),
            "{name}"
        );
        assert!(!direct.contains("sorryAx"), "{name}");
        assert_eq!(
            scan_proof_fragment(&script.arena, &assertions),
            ProofFragment::NegatedExistentialWitness,
            "{name}"
        );
    }
}

#[test]
fn tampered_witness_never_reconstructs_to_false() {
    let (script, assertions, mut certificate) = target_certificate(ARI_SYQI);
    certificate.bindings[0].1 = Value::Bv {
        width: 32,
        value: 12,
    };
    assert!(
        reconstruct_negated_existential_witness_to_lean_module(
            &script.arena,
            &assertions,
            &certificate,
        )
        .is_err()
    );
}

#[test]
fn binding_value_sort_order_count_and_assertion_mutations_fail_closed() {
    let (value_script, value_assertions, mut wrong_value) = target_certificate(ARI_SYQI);
    wrong_value.bindings[0].1 = Value::Bv {
        width: 32,
        value: 12,
    };
    assert!(!check_negated_existential_witness(
        &value_script.arena,
        &value_assertions,
        &wrong_value
    ));

    let (mut script, assertions, certificate) = target_certificate(ARI118);

    let mut wrong_sort = certificate.clone();
    wrong_sort.bindings[0].1 = Value::Bool(false);
    assert!(!check_negated_existential_witness(
        &script.arena,
        &assertions,
        &wrong_sort
    ));

    let mut reordered = certificate.clone();
    reordered.bindings.swap(0, 1);
    assert!(!check_negated_existential_witness(
        &script.arena,
        &assertions,
        &reordered
    ));

    let mut missing = certificate.clone();
    missing.bindings.pop();
    assert!(!check_negated_existential_witness(
        &script.arena,
        &assertions,
        &missing
    ));

    let mut extra = certificate.clone();
    extra.bindings.push(extra.bindings[0].clone());
    assert!(!check_negated_existential_witness(
        &script.arena,
        &assertions,
        &extra
    ));

    let mut stale = certificate;
    stale.assertion = script.arena.bool_const(true);
    assert!(!check_negated_existential_witness(
        &script.arena,
        &assertions,
        &stale
    ));
}

#[test]
fn open_nested_arithmetic_uf_wrong_polarity_and_duplicate_prefixes_decline() {
    for text in [
        "(set-logic BV) (declare-fun p () (_ BitVec 4)) \
         (assert (not (exists ((x (_ BitVec 4))) (= x p)))) (check-sat)",
        "(set-logic BV) \
         (assert (not (exists ((x (_ BitVec 4))) \
           (forall ((y (_ BitVec 4))) (= x y))))) (check-sat)",
        "(set-logic LIA) \
         (assert (not (exists ((x Int)) (= x 0)))) (check-sat)",
        "(set-logic UFBV) (declare-fun f ((_ BitVec 4)) (_ BitVec 4)) \
         (assert (not (exists ((x (_ BitVec 4))) (= (f x) x)))) (check-sat)",
        "(set-logic BV) \
         (assert (exists ((x (_ BitVec 4))) (= x x))) (check-sat)",
        "(set-logic BV) \
         (assert (or true (not (exists ((x (_ BitVec 4))) (= x x))))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("declined source parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .expect("declined source has an honest result");
        assert!(
            !matches!(report.evidence, Evidence::UnsatNegatedExistentialWitness(_)),
            "out-of-contract source received ADR-0126 evidence: {text}"
        );
    }

    let mut arena = TermArena::new();
    let x = arena.declare("duplicate", Sort::Bool).unwrap();
    let body = arena.var(x);
    let inner = arena.exists(x, body).unwrap();
    let outer = arena.exists(x, inner).unwrap();
    let assertion = arena.not(outer).unwrap();
    let certificate = NegatedExistentialWitnessCertificate {
        assertion,
        bindings: vec![(x, Value::Bool(true)), (x, Value::Bool(true))],
    };
    assert!(!check_negated_existential_witness(
        &arena,
        &[assertion],
        &certificate
    ));
}

#[test]
fn satisfiable_neighbor_is_never_refuted() {
    let text = "(set-logic BV) \
        (assert (not (exists ((x (_ BitVec 4))) (distinct x x)))) (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(!matches!(
        report.evidence,
        Evidence::UnsatNegatedExistentialWitness(_)
    ));
    assert!(!matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn binder_and_body_node_caps_fail_closed() {
    let mut arena = TermArena::new();
    let mut assertion = arena.bool_const(true);
    let mut bindings = Vec::new();
    for index in 0..=NEGATED_EXISTENTIAL_BINDER_CAP {
        let binder = arena
            .declare(&format!("cap_binder_{index}"), Sort::Bool)
            .unwrap();
        bindings.push((binder, Value::Bool(false)));
        assertion = arena.exists(binder, assertion).unwrap();
    }
    assertion = arena.not(assertion).unwrap();
    let certificate = NegatedExistentialWitnessCertificate {
        assertion,
        bindings,
    };
    assert!(!check_negated_existential_witness(
        &arena,
        &[assertion],
        &certificate
    ));

    let mut arena = TermArena::new();
    let binder = arena.declare("node_cap_binder", Sort::Bool).unwrap();
    let mut body = arena.var(binder);
    for _ in 0..=NEGATED_EXISTENTIAL_NODE_CAP {
        body = arena.not(body).unwrap();
    }
    let existential = arena.exists(binder, body).unwrap();
    let assertion = arena.not(existential).unwrap();
    let certificate = NegatedExistentialWitnessCertificate {
        assertion,
        bindings: vec![(binder, Value::Bool(false))],
    };
    assert!(!check_negated_existential_witness(
        &arena,
        &[assertion],
        &certificate
    ));
}

#[cfg(feature = "z3")]
#[test]
fn generated_negated_existentials_agree_with_direct_z3() {
    use z3::{Params, SatResult, Solver};

    for seed in 0u32..32 {
        let width = seed % 8 + 1;
        let modulus = 1u128 << width;
        let value = u128::from(seed.wrapping_mul(13).wrapping_add(7)) % modulus;
        let unsat = format!(
            "(set-logic BV) \
             (assert (not (exists ((x (_ BitVec {width}))) \
               (= x (_ bv{value} {width}))))) (check-sat)"
        );
        let sat = format!(
            "(set-logic BV) \
             (assert (not (exists ((x (_ BitVec {width}))) \
               (distinct x x)))) (check-sat)"
        );

        for (text, expected) in [(unsat, SatResult::Unsat), (sat, SatResult::Sat)] {
            let mut script = parse_script(&text).expect("generated source parses");
            let assertions = script.assertions.clone();
            let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
            let axeyum = match &report.evidence {
                Evidence::UnsatNegatedExistentialWitness(_) => {
                    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
                    SatResult::Unsat
                }
                Evidence::Sat(_) => SatResult::Sat,
                Evidence::Unsat(_) => SatResult::Unsat,
                other => panic!("unexpected generated evidence: {}", other.kind_label()),
            };

            let mut params = Params::new();
            params.set_u32("timeout", 2_000);
            let oracle = Solver::new();
            oracle.set_params(&params);
            oracle.from_string(text.as_str());
            let z3 = oracle.check();
            assert_eq!(z3, expected, "unexpected oracle result: {text}");
            assert_eq!(axeyum, z3, "axeyum/Z3 disagreement: {text}");
            assert_eq!(
                matches!(report.evidence, Evidence::UnsatNegatedExistentialWitness(_)),
                expected == SatResult::Unsat,
                "certificate polarity mismatch: {text}"
            );
        }
    }
}
