//! ADR-0129 source-bound paired-existential witness transfer.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    BV_PAIRED_EXISTS_BINDER_CAP, BV_PAIRED_EXISTS_NODE_CAP, BvPairedExistentialTransferCertificate,
    BvPairedExistentialTransferJustification, CheckResult, Evidence, SolverConfig, SolverError,
    check_bv_paired_existential_transfer, produce_evidence, solve,
};

const TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__nested9_true-unreach-call.i_575.smt2"
);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

fn target_certificate() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    BvPairedExistentialTransferCertificate,
) {
    let mut script = parse_script(TARGET).expect("target parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("target produces evidence");
    let Evidence::UnsatBvPairedExistentialTransfer(certificate) = report.evidence else {
        panic!(
            "expected ADR-0129 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(report.trusted_steps.is_empty());
    assert!(
        check_bv_paired_existential_transfer(&script.arena, &assertions, &certificate)
            .expect("target certificate rechecks")
    );
    (script, assertions, certificate)
}

#[test]
fn public_nested_unreachable_call_row_has_checked_transfer_evidence() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(assertions.len(), 2);
    assert_eq!(certificate.positive_assertion, assertions[0]);
    assert_eq!(certificate.negative_assertion, assertions[1]);
    assert_eq!(certificate.obligations.len(), 1);
    assert!(matches!(
        certificate.obligations[0].justification,
        BvPairedExistentialTransferJustification::SignedAddMonotonicity { .. }
    ));

    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert_eq!(
        report.evidence.kind_label(),
        "unsat-bv-paired-existential-transfer"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn public_pair_is_found_independently_of_assertion_order() {
    let mut script = parse_script(TARGET).expect("target parses");
    let mut assertions = script.assertions.clone();
    assertions.reverse();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvPairedExistentialTransfer(certificate) = &report.evidence else {
        panic!("reversed target should still use ADR-0129")
    };
    assert_eq!(certificate.positive_assertion, assertions[1]);
    assert_eq!(certificate.negative_assertion, assertions[0]);
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
}

#[test]
fn source_and_signed_monotonicity_mutations_fail_closed() {
    let (mut script, assertions, certificate) = target_certificate();

    let mut swapped_assertions = certificate.clone();
    std::mem::swap(
        &mut swapped_assertions.positive_assertion,
        &mut swapped_assertions.negative_assertion,
    );
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &swapped_assertions)
            .unwrap_or(false)
    );

    let mut stale_positive = certificate.clone();
    stale_positive.positive_assertion = script.arena.bool_const(true);
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &stale_positive)
            .unwrap_or(false)
    );

    let mut stale_existential = certificate.clone();
    stale_existential.positive_existential = script.arena.bool_const(true);
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &stale_existential)
            .unwrap_or(false)
    );

    let mut missing = certificate.clone();
    missing.obligations.clear();
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &missing)
            .unwrap_or(false)
    );

    let mut duplicate = certificate.clone();
    duplicate.obligations.push(duplicate.obligations[0].clone());
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &duplicate)
            .unwrap_or(false)
    );

    let mut wrong_consequent = certificate.clone();
    wrong_consequent.obligations[0].consequent = certificate.positive_existential;
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &wrong_consequent)
            .unwrap_or(false)
    );

    let mut swapped_reason = certificate;
    let BvPairedExistentialTransferJustification::SignedAddMonotonicity { strong, bound } =
        &mut swapped_reason.obligations[0].justification
    else {
        panic!("target uses signed monotonicity")
    };
    std::mem::swap(strong, bound);
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &swapped_reason)
            .unwrap_or(false)
    );
}

#[test]
fn alpha_identity_and_generic_qf_transfer_are_independently_checked() {
    let identical = "(set-logic BV) \
        (assert (exists ((x (_ BitVec 4))) (= x (_ bv0 4)))) \
        (assert (not (exists ((y (_ BitVec 4))) (= y (_ bv0 4))))) \
        (check-sat)";
    let mut script = parse_script(identical).expect("identity pair parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvPairedExistentialTransfer(certificate) = &report.evidence else {
        panic!("identity pair should use ADR-0129")
    };
    assert!(certificate.obligations.is_empty());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());

    let generic = "(set-logic BV) \
        (assert (exists ((x (_ BitVec 4))) (= x (_ bv0 4)))) \
        (assert (not (exists ((y (_ BitVec 4))) (bvule y (_ bv0 4))))) \
        (check-sat)";
    let mut script = parse_script(generic).expect("generic pair parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvPairedExistentialTransfer(certificate) = report.evidence else {
        panic!("generic pair should use ADR-0129")
    };
    assert_eq!(certificate.obligations.len(), 1);
    let BvPairedExistentialTransferJustification::QfProof { assumptions, .. } =
        &certificate.obligations[0].justification
    else {
        panic!("generic pair should carry a QF proof")
    };
    assert_eq!(assumptions.len(), 1);
    assert!(
        check_bv_paired_existential_transfer(&script.arena, &assertions, &certificate).unwrap()
    );

    let mut tampered = certificate.clone();
    let BvPairedExistentialTransferJustification::QfProof { proof, .. } =
        &mut tampered.obligations[0].justification
    else {
        unreachable!()
    };
    proof.dimacs = "p cnf 1 0\n".to_owned();
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &tampered)
            .unwrap_or(false)
    );

    let mut missing_assumption = certificate;
    let BvPairedExistentialTransferJustification::QfProof { assumptions, .. } =
        &mut missing_assumption.obligations[0].justification
    else {
        unreachable!()
    };
    assumptions.clear();
    assert!(
        !check_bv_paired_existential_transfer(&script.arena, &assertions, &missing_assumption)
            .unwrap_or(false)
    );
}

#[test]
fn malformed_premises_prefixes_contexts_and_sorts_decline() {
    for text in [
        "(set-logic BV) (declare-fun p () Bool) (declare-fun q () Bool) \
         (assert (and p (exists ((x (_ BitVec 4))) (= x x)))) \
         (assert (not (and q (exists ((y (_ BitVec 4))) (= y y))))) (check-sat)",
        "(set-logic BV) \
         (assert (or false (exists ((x (_ BitVec 4))) (= x x)))) \
         (assert (not (exists ((y (_ BitVec 4))) (= y y)))) (check-sat)",
        "(set-logic BV) \
         (assert (and (exists ((x (_ BitVec 4))) (= x x)) \
                      (exists ((z (_ BitVec 4))) (= z z)))) \
         (assert (not (exists ((y (_ BitVec 4))) (= y y)))) (check-sat)",
        "(set-logic BV) \
         (assert (exists ((x (_ BitVec 4))) (forall ((z (_ BitVec 4))) (= x z)))) \
         (assert (not (exists ((y (_ BitVec 4))) (= y y)))) (check-sat)",
        "(set-logic UFBV) (declare-fun f ((_ BitVec 4)) (_ BitVec 4)) \
         (assert (exists ((x (_ BitVec 4))) (= (f x) x))) \
         (assert (not (exists ((y (_ BitVec 4))) (= (f y) y)))) (check-sat)",
        "(set-logic BV) \
         (assert (exists ((x (_ BitVec 4))) (= x x))) \
         (assert (not (exists ((y (_ BitVec 5))) (= y y)))) (check-sat)",
        "(set-logic LIA) (assert (exists ((x Int)) (= x x))) \
         (assert (not (exists ((y Int)) (= y y)))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("declined pair parses");
        let assertions = script.assertions.clone();
        match produce_evidence(&mut script.arena, &assertions, &config()) {
            Ok(report) => assert!(
                !matches!(
                    report.evidence,
                    Evidence::UnsatBvPairedExistentialTransfer(_)
                ),
                "out-of-contract source received ADR-0129 evidence: {text}"
            ),
            Err(SolverError::Unsupported(_)) => {}
            Err(error) => panic!("unexpected decline error for {text}: {error}"),
        }
    }
}

#[test]
fn overflow_unsafe_neighbors_are_never_refuted() {
    for text in [
        "(set-logic BV) (declare-fun k () (_ BitVec 2)) \
         (assert (and (= k (_ bv2 2)) (exists ((x (_ BitVec 2))) \
           (and (bvsle (bvadd x (_ bv3 2)) k) (bvsle x (_ bv3 2)))))) \
         (assert (not (and (= k (_ bv2 2)) (exists ((y (_ BitVec 2))) \
           (and (bvsle (bvadd y (_ bv1 2)) k) (bvsle y (_ bv3 2))))))) (check-sat)",
        "(set-logic BV) (declare-fun k () (_ BitVec 3)) \
         (assert (and (= k (_ bv4 3)) (exists ((x (_ BitVec 3))) \
           (and (bvsle (bvadd x (_ bv3 3)) k) (bvsle x (_ bv1 3)))))) \
         (assert (not (and (= k (_ bv4 3)) (exists ((y (_ BitVec 3))) \
           (and (bvsle (bvadd y (_ bv1 3)) k) (bvsle y (_ bv1 3))))))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("overflow neighbor parses");
        let assertions = script.assertions.clone();
        match produce_evidence(&mut script.arena, &assertions, &config()) {
            Ok(report) => assert!(
                !matches!(
                    report.evidence,
                    Evidence::UnsatBvPairedExistentialTransfer(_)
                ),
                "overflow-unsafe source received ADR-0129 evidence: {text}"
            ),
            Err(SolverError::Unsupported(_)) => {}
            Err(error) => panic!("unexpected overflow-neighbor error: {error}"),
        }
        match solve(&mut script.arena, &assertions, &config()) {
            Ok(result) => assert!(!matches!(result, CheckResult::Unsat), "wrong UNSAT: {text}"),
            Err(SolverError::Unsupported(_)) => {}
            Err(error) => panic!("unexpected solve error: {error}"),
        }
    }
}

#[test]
fn binder_and_source_node_caps_fail_closed() {
    let mut arena = TermArena::new();
    let mut positive_body = arena.bool_const(true);
    let mut negative_body = positive_body;
    for index in 0..BV_PAIRED_EXISTS_BINDER_CAP / 2 {
        let positive = arena
            .declare(&format!("exact_positive_{index}"), Sort::Bool)
            .unwrap();
        let negative = arena
            .declare(&format!("exact_negative_{index}"), Sort::Bool)
            .unwrap();
        positive_body = arena.exists(positive, positive_body).unwrap();
        negative_body = arena.exists(negative, negative_body).unwrap();
    }
    let positive_assertion = positive_body;
    let negative_assertion = arena.not(negative_body).unwrap();
    let exact = BvPairedExistentialTransferCertificate {
        positive_assertion,
        negative_assertion,
        positive_existential: positive_body,
        negative_existential: negative_body,
        obligations: Vec::new(),
    };
    assert!(
        check_bv_paired_existential_transfer(
            &arena,
            &[positive_assertion, negative_assertion],
            &exact
        )
        .unwrap()
    );

    let positive = arena.declare("over_positive", Sort::Bool).unwrap();
    let negative = arena.declare("over_negative", Sort::Bool).unwrap();
    positive_body = arena.exists(positive, positive_body).unwrap();
    negative_body = arena.exists(negative, negative_body).unwrap();
    let positive_assertion = positive_body;
    let negative_assertion = arena.not(negative_body).unwrap();
    let over_binders = BvPairedExistentialTransferCertificate {
        positive_assertion,
        negative_assertion,
        positive_existential: positive_body,
        negative_existential: negative_body,
        obligations: Vec::new(),
    };
    assert!(
        !check_bv_paired_existential_transfer(
            &arena,
            &[positive_assertion, negative_assertion],
            &over_binders
        )
        .unwrap_or(false)
    );

    let mut arena = TermArena::new();
    let mut premises = arena.bool_const(true);
    for index in 0..=BV_PAIRED_EXISTS_NODE_CAP {
        let symbol = arena
            .declare(&format!("node_cap_{index}"), Sort::Bool)
            .unwrap();
        let symbol = arena.var(symbol);
        premises = arena.and(premises, symbol).unwrap();
    }
    let positive = arena.declare("node_positive", Sort::Bool).unwrap();
    let negative = arena.declare("node_negative", Sort::Bool).unwrap();
    let true_term = arena.bool_const(true);
    let positive_existential = arena.exists(positive, true_term).unwrap();
    let negative_existential = arena.exists(negative, true_term).unwrap();
    let positive_assertion = arena.and(premises, positive_existential).unwrap();
    let negative_inner = arena.and(premises, negative_existential).unwrap();
    let negative_assertion = arena.not(negative_inner).unwrap();
    let over_nodes = BvPairedExistentialTransferCertificate {
        positive_assertion,
        negative_assertion,
        positive_existential,
        negative_existential,
        obligations: Vec::new(),
    };
    assert!(
        !check_bv_paired_existential_transfer(
            &arena,
            &[positive_assertion, negative_assertion],
            &over_nodes
        )
        .unwrap_or(false)
    );
}

#[cfg(feature = "z3")]
#[test]
fn generated_safe_transfers_and_nontransfer_controls_agree_with_z3() {
    use z3::{Params, SatResult, Solver};

    for seed in 0u32..64 {
        let width = seed % 8 + 4;
        let strong = u128::from(seed % 3 + 1);
        let weak = u128::from(seed % (u32::try_from(strong).unwrap() + 1));
        let max_signed = (1u128 << (width - 1)) - 1;
        let bound = max_signed - strong;
        let unsat = format!(
            "(set-logic BV) (declare-fun k () (_ BitVec {width})) \
             (declare-fun p () Bool) \
             (assert (and p (exists ((x (_ BitVec {width}))) \
               (and (bvsle (bvadd x (_ bv{strong} {width})) k) \
                    (bvsle x (_ bv{bound} {width})))))) \
             (assert (not (and p (exists ((y (_ BitVec {width}))) \
               (and (bvsle (bvadd y (_ bv{weak} {width})) k) \
                    (bvsle y (_ bv{bound} {width}))))))) (check-sat)"
        );
        let overflow_bound = max_signed - 2;
        let min_signed = 1u128 << (width - 1);
        let sat = format!(
            "(set-logic BV) (declare-fun k () (_ BitVec {width})) \
             (declare-fun p () Bool) \
             (assert (and (= k (_ bv{min_signed} {width})) p \
               (exists ((x (_ BitVec {width}))) \
                 (and (bvsle (bvadd x (_ bv3 {width})) k) \
                      (bvsle x (_ bv{overflow_bound} {width})))))) \
             (assert (not (and (= k (_ bv{min_signed} {width})) p \
               (exists ((y (_ BitVec {width}))) \
                 (and (bvsle (bvadd y (_ bv1 {width})) k) \
                      (bvsle y (_ bv{overflow_bound} {width}))))))) (check-sat)"
        );

        for (text, expected) in [(unsat, SatResult::Unsat), (sat, SatResult::Sat)] {
            let mut script = parse_script(&text).expect("generated pair parses");
            let assertions = script.assertions.clone();
            match produce_evidence(&mut script.arena, &assertions, &config()) {
                Ok(report) if expected == SatResult::Unsat => {
                    assert!(matches!(
                        report.evidence,
                        Evidence::UnsatBvPairedExistentialTransfer(_)
                    ));
                    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
                }
                Ok(report) => assert!(
                    !matches!(
                        report.evidence,
                        Evidence::UnsatBvPairedExistentialTransfer(_)
                    ),
                    "SAT control received transfer evidence: {text}"
                ),
                Err(SolverError::Unsupported(_)) if expected == SatResult::Sat => {}
                Err(error) => panic!("unexpected generated result: {error}"),
            }
            let mut params = Params::new();
            params.set_u32("timeout", 2_000);
            let oracle = Solver::new();
            oracle.set_params(&params);
            oracle.from_string(text.as_str());
            assert_eq!(oracle.check(), expected, "unexpected Z3 result: {text}");
        }
    }
}
