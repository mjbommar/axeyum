//! ADR-0127 source-bound conjunctive BV universal instances.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP, BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP,
    BvConjunctiveUniversalInstanceCertificate, CheckResult, Evidence, ProofFragment, SolverConfig,
    SolverError, check_bv_conjunctive_universal_instance, produce_evidence,
    prove_unsat_to_lean_module, reconstruct_bv_conjunctive_universal_instance_to_lean_module,
    scan_proof_fragment, solve,
};

const TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__cond-var-elim-binary.smt2"
);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

fn target_certificate() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    BvConjunctiveUniversalInstanceCertificate,
) {
    let mut script = parse_script(TARGET).expect("target parses");
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &config()).expect("target evidence");
    let Evidence::UnsatBvConjunctiveUniversalInstance(certificate) = report.evidence else {
        panic!(
            "expected ADR-0127 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(report.trusted_steps.is_empty());
    assert!(
        check_bv_conjunctive_universal_instance(&script.arena, &assertions, &certificate)
            .expect("source proof rechecks")
    );
    (script, assertions, certificate)
}

#[test]
fn public_conditional_variable_elimination_row_has_checked_evidence() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(certificate.assertion, assertions[0]);
    assert_eq!(certificate.bindings.len(), 2);
    assert_eq!(
        certificate.bindings[0].1,
        Value::Bv {
            width: 32,
            value: 1
        }
    );
    assert_eq!(
        certificate.bindings[1].1,
        Value::Bv {
            width: 32,
            value: 0
        }
    );

    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert_eq!(
        report.evidence.kind_label(),
        "unsat-bv-conjunctive-universal-instance"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn conjunctive_source_instance_reconstructs_directly_and_through_the_router() {
    let mut script = parse_script(
        "(set-logic BV)
         (declare-fun a () (_ BitVec 32))
         (assert (and (= a (_ bv0 32))
           (forall ((x (_ BitVec 32))) (not (= x a)))))
         (check-sat)",
    )
    .unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvConjunctiveUniversalInstance(certificate) = report.evidence else {
        panic!("expected ADR-0127 source instance");
    };

    let direct = reconstruct_bv_conjunctive_universal_instance_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("conjunctive source instance reconstructs");
    assert!(direct.contains("theorem axeyum_refutation : False"));
    assert!(!direct.contains("sorryAx"));
    assert_eq!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::BvConjunctiveUniversalInstance
    );
    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("conjunctive source-instance router reconstructs");
    assert_eq!(fragment, ProofFragment::BvConjunctiveUniversalInstance);
    assert_eq!(routed, direct);

    let mut tampered = certificate;
    tampered.bindings[0].1 = Value::Bv {
        width: 32,
        value: 1,
    };
    assert!(
        reconstruct_bv_conjunctive_universal_instance_to_lean_module(
            &script.arena,
            &assertions,
            &tampered,
        )
        .is_err()
    );
}

#[test]
#[ignore = "release-only public-corpus ADR-0127 Lean reconstruction stress gate"]
fn public_conditional_variable_elimination_reconstructs_from_untouched_source() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::BvConjunctiveUniversalInstance
    );
    let direct = reconstruct_bv_conjunctive_universal_instance_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("public conjunctive source instance reconstructs through compact RUP");
    assert!(direct.contains("theorem axeyum_refutation : False"));
    assert!(!direct.contains("sorryAx"));

    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("public conjunctive source-instance router reconstructs");
    assert_eq!(fragment, ProofFragment::BvConjunctiveUniversalInstance);
    assert_eq!(routed, direct);
}

#[test]
fn binding_source_and_proof_mutations_fail_closed() {
    let (mut script, assertions, certificate) = target_certificate();

    let mut wrong_value = certificate.clone();
    wrong_value.bindings[0].1 = Value::Bv {
        width: 32,
        value: 0,
    };
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &wrong_value)
            .unwrap_or(false)
    );

    let mut wrong_sort = certificate.clone();
    wrong_sort.bindings[0].1 = Value::Bool(false);
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &wrong_sort)
            .unwrap_or(false)
    );

    let mut reordered = certificate.clone();
    reordered.bindings.swap(0, 1);
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &reordered)
            .unwrap_or(false)
    );

    let mut missing = certificate.clone();
    missing.bindings.pop();
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &missing)
            .unwrap_or(false)
    );

    let mut stale_assertion = certificate.clone();
    stale_assertion.assertion = script.arena.bool_const(true);
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &stale_assertion)
            .unwrap_or(false)
    );

    let mut stale_universal = certificate.clone();
    stale_universal.universal = script.arena.bool_const(false);
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &stale_universal)
            .unwrap_or(false)
    );

    let mut bad_proof = certificate;
    bad_proof.residual_proof.dimacs = "p cnf 1 0\n".to_owned();
    assert!(
        !check_bv_conjunctive_universal_instance(&script.arena, &assertions, &bad_proof)
            .unwrap_or(false)
    );
}

#[test]
fn non_conjunctive_duplicate_nested_and_function_contexts_decline() {
    for text in [
        "(set-logic BV) (assert (or false (forall ((x (_ BitVec 4))) (= x x)))) (check-sat)",
        "(set-logic BV) (assert (not (forall ((x (_ BitVec 4))) (= x x)))) (check-sat)",
        "(set-logic BV) (assert (=> true (forall ((x (_ BitVec 4))) (= x x)))) (check-sat)",
        "(set-logic BV) (assert (and true (forall ((x (_ BitVec 4))) \
           (exists ((y (_ BitVec 4))) (= x y))))) (check-sat)",
        "(set-logic UFBV) (declare-fun f ((_ BitVec 4)) (_ BitVec 4)) \
         (assert (and true (forall ((x (_ BitVec 4))) (= (f x) x)))) (check-sat)",
        "(set-logic LIA) (assert (and true (forall ((x Int)) (= x x)))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("declined source parses");
        let assertions = script.assertions.clone();
        match produce_evidence(&mut script.arena, &assertions, &config()) {
            Ok(report) => assert!(
                !matches!(
                    report.evidence,
                    Evidence::UnsatBvConjunctiveUniversalInstance(_)
                ),
                "out-of-contract source received ADR-0127 evidence: {text}"
            ),
            Err(SolverError::Unsupported(_)) => {}
            Err(error) => panic!("unexpected decline error for {text}: {error}"),
        }
    }

    let mut arena = TermArena::new();
    let x = arena.declare("duplicate_x", Sort::BitVec(2)).unwrap();
    let x_term = arena.var(x);
    let body = arena.eq(x_term, x_term).unwrap();
    let universal = arena.forall(x, body).unwrap();
    let assertion = arena.and(universal, universal).unwrap();
    let (_, _, proof) = target_certificate();
    let duplicate = BvConjunctiveUniversalInstanceCertificate {
        assertion,
        universal,
        bindings: vec![(x, Value::Bv { width: 2, value: 0 })],
        residual_proof: proof.residual_proof,
    };
    assert!(
        !check_bv_conjunctive_universal_instance(&arena, &[assertion], &duplicate).unwrap_or(false)
    );

    let false_term = arena.bool_const(false);
    let hidden = arena.or(universal, false_term).unwrap();
    let hidden_duplicate_assertion = arena.and(universal, hidden).unwrap();
    let hidden_duplicate = BvConjunctiveUniversalInstanceCertificate {
        assertion: hidden_duplicate_assertion,
        universal,
        bindings: duplicate.bindings,
        residual_proof: duplicate.residual_proof,
    };
    assert!(
        !check_bv_conjunctive_universal_instance(
            &arena,
            &[hidden_duplicate_assertion],
            &hidden_duplicate
        )
        .unwrap_or(false)
    );
}

#[test]
fn satisfiable_conjunctive_neighbor_is_not_refuted() {
    let text = "(set-logic BV) \
        (declare-fun a () (_ BitVec 4)) (declare-fun b () (_ BitVec 4)) \
        (assert (and (bvult a b) (forall ((x (_ BitVec 4))) (= x x)))) (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(!matches!(
        report.evidence,
        Evidence::UnsatBvConjunctiveUniversalInstance(_)
    ));
    assert!(!matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn binder_and_assertion_node_caps_fail_closed() {
    let (_, _, target) = target_certificate();

    let mut arena = TermArena::new();
    let mut body = arena.bool_const(true);
    let mut bindings = Vec::new();
    for index in 0..=BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP {
        let binder = arena
            .declare(&format!("cap_binder_{index}"), Sort::Bool)
            .unwrap();
        bindings.push((binder, Value::Bool(false)));
        body = arena.forall(binder, body).unwrap();
    }
    bindings.reverse();
    let true_term = arena.bool_const(true);
    let assertion = arena.and(true_term, body).unwrap();
    let over_binders = BvConjunctiveUniversalInstanceCertificate {
        assertion,
        universal: body,
        bindings,
        residual_proof: target.residual_proof.clone(),
    };
    assert!(
        !check_bv_conjunctive_universal_instance(&arena, &[assertion], &over_binders)
            .unwrap_or(false)
    );

    let mut arena = TermArena::new();
    let binder = arena.declare("node_cap_binder", Sort::Bool).unwrap();
    let binder_term = arena.var(binder);
    let universal = arena.forall(binder, binder_term).unwrap();
    let mut assertion = universal;
    for index in 0..=BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP {
        let symbol = arena
            .declare(&format!("node_cap_{index}"), Sort::Bool)
            .unwrap();
        let symbol_term = arena.var(symbol);
        assertion = arena.and(assertion, symbol_term).unwrap();
    }
    let over_nodes = BvConjunctiveUniversalInstanceCertificate {
        assertion,
        universal,
        bindings: vec![(binder, Value::Bool(true))],
        residual_proof: target.residual_proof,
    };
    assert!(
        !check_bv_conjunctive_universal_instance(&arena, &[assertion], &over_nodes)
            .unwrap_or(false)
    );
}

#[cfg(feature = "z3")]
#[test]
fn generated_conjunctive_instances_agree_with_direct_z3() {
    use z3::{Params, SatResult, Solver};

    for seed in 0u32..32 {
        let width = seed % 8 + 2;
        let unsat = format!(
            "(set-logic BV) \
             (declare-fun a () (_ BitVec {width})) \
             (declare-fun b () (_ BitVec {width})) \
             (assert (and (bvult a b) \
               (forall ((x (_ BitVec {width}))) \
                 (or (not (= x (_ bv1 {width}))) \
                     (not (bvult a (bvmul x b))))))) (check-sat)"
        );
        let sat = format!(
            "(set-logic BV) \
             (declare-fun a () (_ BitVec {width})) \
             (declare-fun b () (_ BitVec {width})) \
             (assert (and (bvult a b) \
               (forall ((x (_ BitVec {width}))) \
                 (or (not (= x (_ bv1 {width}))) \
                     (bvult a (bvmul x b)))))) (check-sat)"
        );

        for (text, expected) in [(unsat, SatResult::Unsat), (sat, SatResult::Sat)] {
            let mut script = parse_script(&text).expect("generated source parses");
            let assertions = script.assertions.clone();
            let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
            let axeyum = match &report.evidence {
                Evidence::UnsatBvConjunctiveUniversalInstance(_) => {
                    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
                    SatResult::Unsat
                }
                Evidence::Sat(_) => SatResult::Sat,
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
                matches!(
                    report.evidence,
                    Evidence::UnsatBvConjunctiveUniversalInstance(_)
                ),
                expected == SatResult::Unsat,
                "certificate polarity mismatch: {text}"
            );
        }
    }
}
