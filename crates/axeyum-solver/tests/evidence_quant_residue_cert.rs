//! Checked evidence for the Euclidean quotient/remainder quantified-LIA slice.
#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{Evidence, SolverConfig, produce_evidence};

fn clock(modulus: i128) -> String {
    format!(
        "(set-logic LIA)\n\
         (declare-fun t () Int)\n\
         (assert (forall ((s Int) (m Int))\n\
           (or (not (= (+ (* {modulus} m) s) t)) (< s 0) (>= s {modulus}))))\n\
         (check-sat)\n"
    )
}

#[test]
fn clock_rows_carry_checked_euclidean_residue_evidence() {
    for modulus in [3, 10] {
        let mut script = parse_script(&clock(modulus)).unwrap();
        let assertions = script.assertions.clone();
        let report =
            produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
        let Evidence::UnsatIntEuclideanResidue(cert) = &report.evidence else {
            panic!(
                "expected Euclidean-residue evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.modulus, modulus);
        assert_eq!(report.evidence.kind_label(), "unsat-int-euclidean-residue");
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(report.trusted_steps.is_empty());
    }
}

#[test]
fn tampered_modulus_is_rejected() {
    let mut script = parse_script(&clock(3)).unwrap();
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    let Evidence::UnsatIntEuclideanResidue(mut cert) = report.evidence else {
        panic!("expected Euclidean-residue evidence");
    };
    cert.modulus = 2;
    let tampered = Evidence::UnsatIntEuclideanResidue(cert);
    assert!(!tampered.check(&script.arena, &assertions).unwrap());
}

#[test]
fn weakened_upper_bound_is_not_certified() {
    let text = "(set-logic LIA) (declare-fun t () Int) \
         (assert (forall ((s Int) (m Int)) \
           (or (not (= (+ (* 3 m) s) t)) (< s 0) (>= s 2)))) (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(report.evidence, Evidence::UnsatIntEuclideanResidue(_)),
        "a satisfiable weakened partition must not receive the certificate"
    );
}
