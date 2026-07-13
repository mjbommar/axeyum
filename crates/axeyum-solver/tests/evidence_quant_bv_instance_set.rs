//! ADR-0134 query-scoped positive-universal Bool/BV instance sets.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    BV_POSITIVE_INSTANCE_SET_CAP, BvPositiveUniversalInstanceSetCertificate,
    BvPositiveUniversalSourceInstance, CheckResult, Evidence, ProofFragment, SolverConfig,
    SolverError, UnsatProofOutcome, check_bv_positive_universal_instance_set,
    export_qf_bv_unsat_proof, produce_evidence, prove_unsat_to_lean_module,
    reconstruct_bv_positive_universal_instance_set_to_lean_module, scan_proof_fragment, solve,
};

const TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-107-bv.smt2"
);

fn config(seconds: u64) -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(seconds))
}

fn target_certificate() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    BvPositiveUniversalInstanceSetCertificate,
) {
    let mut script = parse_script(TARGET).expect("target parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config(10))
        .expect("target produces evidence");
    let Evidence::UnsatBvPositiveUniversalInstanceSet(certificate) = report.evidence else {
        panic!(
            "expected ADR-0134 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(report.trusted_steps.is_empty());
    assert!(
        check_bv_positive_universal_instance_set(&script.arena, &assertions, &certificate)
            .expect("target certificate rechecks")
    );
    (script, assertions, certificate)
}

fn two_instance_formula(width: u32, contradictory: bool) -> String {
    let ground = if contradictory {
        "(assert (not (and p q)))"
    } else {
        "(assert true)"
    };
    format!(
        "(set-logic BV)
         (declare-fun p () Bool)
         (declare-fun q () Bool)
         (assert (forall ((x (_ BitVec {width})))
           (and (=> (= x (_ bv0 {width})) p)
                (=> (= x (_ bv1 {width})) q))))
         {ground}
         (check-sat)"
    )
}

#[test]
fn public_psyco_107_bv_has_checked_query_scoped_instances() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(certificate.assertions, assertions);
    assert!(!certificate.instances.is_empty());
    assert!(certificate.instances.len() <= BV_POSITIVE_INSTANCE_SET_CAP);
    assert!(
        certificate
            .instances
            .iter()
            .all(|instance| instance.assertion == assertions[0])
    );

    let report = produce_evidence(&mut script.arena, &assertions, &config(10)).unwrap();
    assert_eq!(
        report.evidence.kind_label(),
        "unsat-bv-positive-universal-instance-set"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
    assert!(matches!(
        solve(&mut script.arena, &assertions, &config(10)).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn exact_query_source_bindings_and_proof_are_bound() {
    let (mut script, assertions, certificate) = target_certificate();

    let mut reordered_query = certificate.clone();
    reordered_query.assertions.swap(0, 1);
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &reordered_query)
            .unwrap_or(false)
    );

    let mut stale_source = certificate.clone();
    stale_source.instances[0].assertion = assertions[1];
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &stale_source)
            .unwrap_or(false)
    );

    let mut missing_binding = certificate.clone();
    missing_binding.instances[0].bindings.pop();
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &missing_binding)
            .unwrap_or(false)
    );

    let mut reordered_binding = certificate.clone();
    reordered_binding.instances[0].bindings.swap(0, 1);
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &reordered_binding)
            .unwrap_or(false)
    );

    let mut wrong_sort = certificate.clone();
    wrong_sort.instances[0].bindings[0].1 = Value::Bool(false);
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &wrong_sort)
            .unwrap_or(false)
    );

    let mut duplicate = certificate.clone();
    duplicate.instances.push(duplicate.instances[0].clone());
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &duplicate)
            .unwrap_or(false)
    );

    let mut bad_proof = certificate.clone();
    bad_proof.residual_proof.dimacs = "p cnf 1 0\n".to_owned();
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &bad_proof)
            .unwrap_or(false)
    );

    let mut changed_assertions = assertions.clone();
    changed_assertions[1] = script.arena.bool_const(false);
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &changed_assertions, &certificate)
            .unwrap_or(false)
    );

    let mut over_cap = certificate;
    over_cap.instances = (0..=BV_POSITIVE_INSTANCE_SET_CAP)
        .map(|_| over_cap.instances[0].clone())
        .collect();
    assert!(
        !check_bv_positive_universal_instance_set(&script.arena, &assertions, &over_cap)
            .unwrap_or(false)
    );
}

#[test]
fn free_bound_capture_and_out_of_fragment_sources_fail_closed() {
    let mut arena = TermArena::new();
    let p = arena.declare("captured_p", Sort::Bool).unwrap();
    let p_term = arena.var(p);
    let shadowed = arena.forall(p, p_term).unwrap();
    let captured = arena.and(p_term, shadowed).unwrap();
    let false_term = arena.bool_const(false);
    let UnsatProofOutcome::Proved(false_proof) =
        export_qf_bv_unsat_proof(&arena, &[false_term]).unwrap()
    else {
        panic!("false must have a QF_BV proof");
    };
    let capture_certificate = BvPositiveUniversalInstanceSetCertificate {
        assertions: vec![captured],
        instances: vec![BvPositiveUniversalSourceInstance {
            assertion: captured,
            bindings: vec![(p, Value::Bool(true))],
        }],
        residual_proof: false_proof,
    };
    assert!(
        !check_bv_positive_universal_instance_set(&arena, &[captured], &capture_certificate)
            .unwrap_or(false)
    );

    for text in [
        "(set-logic BV) (declare-fun p () Bool) \
         (assert (not (forall ((x (_ BitVec 4))) (or p (= x x))))) (check-sat)",
        "(set-logic BV) (declare-fun p () Bool) \
         (assert (exists ((x (_ BitVec 4))) (or p (= x x)))) (check-sat)",
        "(set-logic UFBV) (declare-fun p () Bool) \
         (declare-fun f ((_ BitVec 4)) (_ BitVec 4)) \
         (assert (forall ((x (_ BitVec 4))) (or p (= (f x) x)))) (check-sat)",
        "(set-logic LIA) (declare-fun p () Bool) \
         (assert (forall ((x Int)) (or p (= x x)))) (check-sat)",
    ] {
        let script = parse_script(text).expect("out-of-fragment source parses");
        let assertion = script.assertions[0];
        let mut changed = capture_certificate.clone();
        changed.assertions = vec![assertion];
        changed.instances[0].assertion = assertion;
        assert!(
            !check_bv_positive_universal_instance_set(&script.arena, &[assertion], &changed)
                .unwrap_or(false)
        );
    }
}

#[test]
fn two_distinct_source_instances_are_required_and_checked() {
    let text = two_instance_formula(32, true);
    let mut script = parse_script(&text).unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config(5)).unwrap();
    let Evidence::UnsatBvPositiveUniversalInstanceSet(certificate) = report.evidence else {
        panic!("expected query-scoped instance set");
    };
    assert_eq!(certificate.instances.len(), 2);
    assert_ne!(
        certificate.instances[0].bindings,
        certificate.instances[1].bindings
    );
    assert!(
        check_bv_positive_universal_instance_set(&script.arena, &assertions, &certificate).unwrap()
    );

    for keep in 0..2 {
        let mut incomplete = certificate.clone();
        incomplete.instances = vec![incomplete.instances[keep].clone()];
        assert!(
            !check_bv_positive_universal_instance_set(&script.arena, &assertions, &incomplete)
                .unwrap_or(false)
        );
    }
}

#[test]
fn two_source_instances_reconstruct_from_the_original_universal() {
    let text = two_instance_formula(32, true);
    let mut script = parse_script(&text).unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config(5)).unwrap();
    let Evidence::UnsatBvPositiveUniversalInstanceSet(certificate) = report.evidence else {
        panic!("expected query-scoped instance set");
    };

    let direct = reconstruct_bv_positive_universal_instance_set_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("source instances reconstruct");
    assert!(direct.contains("theorem axeyum_refutation : False"));
    assert!(direct.contains("inductive "));
    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("source-instance router reconstructs");
    assert_eq!(fragment, ProofFragment::BvPositiveUniversalInstanceSet);
    assert_eq!(routed, direct);

    let mut tampered = certificate;
    tampered.instances[0].bindings[0].1 = Value::Bv {
        width: 32,
        value: 3,
    };
    assert!(
        reconstruct_bv_positive_universal_instance_set_to_lean_module(
            &script.arena,
            &assertions,
            &tampered,
        )
        .is_err()
    );
}

#[test]
fn bool_and_bv_source_witnesses_reconstruct() {
    let mut script = parse_script(
        "(set-logic BV)
         (declare-fun p () Bool)
         (declare-fun q () Bool)
         (assert (forall ((b Bool) (x (_ BitVec 32)))
           (and (or b (not b))
                (and (=> (= x (_ bv0 32)) p)
                     (=> (= x (_ bv1 32)) q)))))
         (assert (not (and p q)))
         (check-sat)",
    )
    .unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config(5)).unwrap();
    let Evidence::UnsatBvPositiveUniversalInstanceSet(certificate) = report.evidence else {
        panic!("expected query-scoped mixed Bool/BV instance set");
    };
    assert!(certificate.instances.iter().all(|instance| {
        instance
            .bindings
            .iter()
            .any(|(_, value)| matches!(value, Value::Bool(_)))
    }));
    let source = reconstruct_bv_positive_universal_instance_set_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("mixed Bool/BV source instances reconstruct");
    assert!(source.contains("theorem axeyum_refutation : False"));
}

#[test]
#[ignore = "corpus-scale reconstruction exceeds 3 minutes and 2 GiB in debug builds"]
fn public_psyco_107_bv_routes_through_source_instance_lean_reconstruction() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::BvPositiveUniversalInstanceSet
    );
    let direct = reconstruct_bv_positive_universal_instance_set_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("public source instances reconstruct");
    assert!(direct.contains("theorem axeyum_refutation : False"));

    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("public router reconstructs source instances");
    assert_eq!(fragment, ProofFragment::BvPositiveUniversalInstanceSet);
    assert_eq!(routed, direct);
}

#[test]
fn expired_search_never_returns_query_scoped_unsat() {
    let text = two_instance_formula(32, true);
    let mut script = parse_script(&text).unwrap();
    let assertions = script.assertions.clone();
    match produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::ZERO),
    ) {
        Ok(report) => assert!(!matches!(
            report.evidence,
            Evidence::UnsatBvPositiveUniversalInstanceSet(_)
        )),
        Err(SolverError::Unsupported(_)) => {}
        Err(error) => panic!("unexpected zero-deadline error: {error}"),
    }
}

#[test]
fn unsupported_quantified_sibling_declines_without_backend_error() {
    let text = "(set-logic BV)
                (declare-fun p () Bool)
                (assert (forall ((x (_ BitVec 32))) (=> (= x (_ bv0 32)) p)))
                (assert (exists ((y (_ BitVec 32))) (= y y)))
                (assert (not p))
                (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    match produce_evidence(&mut script.arena, &assertions, &config(5)) {
        Ok(report) => assert!(!matches!(
            report.evidence,
            Evidence::UnsatBvPositiveUniversalInstanceSet(_)
        )),
        Err(SolverError::Unsupported(_)) => {}
        Err(error) => panic!("unsupported sibling produced a hard error: {error}"),
    }
}

#[cfg(feature = "z3")]
#[test]
fn generated_query_scoped_instance_sets_match_direct_z3() {
    use z3::{Params, SatResult, Solver};

    for case in 0..32 {
        let contradictory = case % 2 == 0;
        let width = 2 + case / 2;
        let text = two_instance_formula(width, contradictory);
        let mut script = parse_script(&text).unwrap();
        let assertions = script.assertions.clone();
        let axeyum = produce_evidence(&mut script.arena, &assertions, &config(5));

        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 5_000);
        oracle.set_params(&params);
        oracle.from_string(text.as_str());
        let z3 = oracle.check();
        let expected = if contradictory {
            SatResult::Unsat
        } else {
            SatResult::Sat
        };
        assert_eq!(z3, expected, "unexpected Z3 result: {text}");

        match (contradictory, axeyum, z3) {
            (true, Ok(report), SatResult::Unsat) => {
                assert!(matches!(
                    report.evidence,
                    Evidence::UnsatBvPositiveUniversalInstanceSet(_)
                ));
                assert!(report.evidence.check(&script.arena, &assertions).unwrap());
                assert!(report.trusted_steps.is_empty());
            }
            (false, Ok(report), SatResult::Sat) => {
                assert!(matches!(report.evidence, Evidence::Sat(_)));
                assert!(report.evidence.check(&script.arena, &assertions).unwrap());
            }
            (mode, result, oracle) => panic!(
                "query-scoped case {case} (contradictory={mode}) disagreed: axeyum={result:?}, z3={oracle:?}"
            ),
        }
    }
}
