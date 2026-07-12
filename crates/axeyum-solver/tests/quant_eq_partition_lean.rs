//! ADR-0106: genuine Bool/Int quantifier reconstruction for single-pivot
//! equality partitions.

use axeyum_smtlib::{Script, parse_script};
use axeyum_solver::{
    EqualityPartitionRefutationCertificate, Evidence, ProofFragment, SolverConfig,
    produce_evidence, prove_unsat_to_lean_module,
    reconstruct_single_pivot_equality_partition_to_lean_module, scan_proof_fragment,
};

const SDLX: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress1__quantifiers__cbqi-sdlx-fixpoint-3-dd.smt2"
));

fn checked_certificate(text: &str) -> (Script, EqualityPartitionRefutationCertificate) {
    let mut script = parse_script(text).expect("partition formula parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("partition formula has evidence");
    let Evidence::UnsatEqualityPartition(certificate) = report.evidence else {
        panic!("expected equality-partition evidence")
    };
    assert!(
        Evidence::UnsatEqualityPartition(certificate.clone())
            .check(&script.arena, &assertions)
            .expect("certificate check runs")
    );
    (script, certificate)
}

#[test]
fn sdlx_reconstructs_genuine_nested_quantifiers_and_routes() {
    let (mut script, certificate) = checked_certificate(SDLX);
    let assertions = script.assertions.clone();
    let source = reconstruct_single_pivot_equality_partition_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("sdlx reconstructs");
    assert!(source.contains("theorem axeyum_refutation : False"));
    assert!(source.contains("eq_em"));
    assert!(!source.contains("sorryAx"));

    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("generic router reconstructs sdlx");
    assert_eq!(fragment, ProofFragment::SinglePivotEqualityPartition);
    assert!(routed.contains("theorem axeyum_refutation : False"));
}

#[test]
fn arbitrary_int_and_bool_universals_reconstruct() {
    for text in [
        r"(set-logic LIA)
           (assert (not (forall ((x Int)) (or (= x 3) (not (= x 3))))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (not (forall ((b Bool)) (or b (not b)))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (exists ((x Int)) (and (= x (- 5)) (not (= x (- 5))))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (exists ((b Bool)) (and b (not b))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (not (exists ((x Int)) (or (= x 11) (not (= x 11))))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (not (forall ((x Int) (b Bool))
             (= (ite (=> b (= x (- 2))) 4 5)
                (ite (ite b (= x (- 2)) true) 4 5)))))
           (check-sat)",
        r"(set-logic LIA)
           (assert (not (forall ((x Int)) (= (xor (= x 7) (= x 7)) false))))
           (check-sat)",
    ] {
        let (script, certificate) = checked_certificate(text);
        reconstruct_single_pivot_equality_partition_to_lean_module(
            &script.arena,
            &script.assertions,
            &certificate,
        )
        .unwrap_or_else(|error| panic!("control reconstructs: {error}\n{text}"));
    }
}

#[test]
fn tampered_case_count_is_rejected_before_proof_building() {
    let (script, mut certificate) = checked_certificate(SDLX);
    certificate.representative_cases += 1;
    assert!(
        reconstruct_single_pivot_equality_partition_to_lean_module(
            &script.arena,
            &script.assertions,
            &certificate,
        )
        .is_err()
    );
}

#[test]
fn oversized_partition_pivot_declines_before_proof_building() {
    let text = r"(set-logic LIA)
        (assert (not (forall ((x Int)) (or (= x 5000) (not (= x 5000))))))
        (check-sat)";
    let (script, certificate) = checked_certificate(text);
    assert!(
        reconstruct_single_pivot_equality_partition_to_lean_module(
            &script.arena,
            &script.assertions,
            &certificate,
        )
        .is_err()
    );
}

#[test]
fn broader_multi_pivot_evidence_is_not_silently_credited() {
    let text = r"
        (set-logic LIA)
        (assert (or false (forall ((x Int)) (or (= x (- 2)) (= x 7)))))
        (check-sat)
    ";
    let (mut script, certificate) = checked_certificate(text);
    let assertions = script.assertions.clone();
    assert!(
        reconstruct_single_pivot_equality_partition_to_lean_module(
            &script.arena,
            &assertions,
            &certificate,
        )
        .is_err()
    );
    assert_ne!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::SinglePivotEqualityPartition
    );
    assert!(prove_unsat_to_lean_module(&mut script.arena, &assertions).is_err());
}

#[test]
fn free_and_direct_arithmetic_forms_do_not_route() {
    for text in [
        r"(set-logic LIA) (declare-fun p () Int)
           (assert (forall ((x Int)) (= (= x 0) (= p 0)))) (check-sat)",
        r"(set-logic LIA)
           (assert (forall ((x Int)) (= (+ x 1) x))) (check-sat)",
    ] {
        let script = parse_script(text).expect("near miss parses");
        assert_ne!(
            scan_proof_fragment(&script.arena, &script.assertions),
            ProofFragment::SinglePivotEqualityPartition
        );
    }
}
