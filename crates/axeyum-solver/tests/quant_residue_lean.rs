//! ADR-0104: Euclidean-residue universals reconstructed from the general
//! integer-prelude decomposition theorem.
#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, int_euclidean_residue_refutation, prove_unsat_to_lean_module,
    reconstruct_int_euclidean_residue_to_lean_module, scan_proof_fragment,
};

const CLOCK_3: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress0__quantifiers__clock-3.smt2"
));

const CLOCK_10: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress0__quantifiers__clock-10.smt2"
));

#[test]
fn committed_clock_rows_reconstruct_and_route() {
    for (tag, text) in [("clock-3", CLOCK_3), ("clock-10", CLOCK_10)] {
        let mut script = parse_script(text).unwrap_or_else(|error| panic!("parse {tag}: {error}"));
        let assertions = script.assertions.clone();
        let certificate = int_euclidean_residue_refutation(&script.arena, &assertions)
            .unwrap_or_else(|| panic!("{tag} has ADR-0095 evidence"));
        let source = reconstruct_int_euclidean_residue_to_lean_module(
            &script.arena,
            &assertions,
            &certificate,
        )
        .unwrap_or_else(|error| panic!("{tag} reconstructs: {error}"));
        if tag == "clock-3" {
            let fnv1a = source
                .bytes()
                .fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
                    (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
                });
            assert_eq!((source.len(), fnv1a), (16_025, 0x4e97_fa30_7a29_d1d0));
        }
        assert!(source.contains("theorem axeyum_refutation : False"));
        assert!(source.contains("euclidean_decomposition"));
        assert!(!source.contains("sorryAx"));

        let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag} router reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::IntEuclideanResidue);
        assert!(routed.contains("theorem axeyum_refutation : False"));
    }
}

#[test]
fn tampered_modulus_is_rejected_before_proof_building() {
    let script = parse_script(CLOCK_3).expect("parse clock-3");
    let assertions = script.assertions.clone();
    let mut certificate = int_euclidean_residue_refutation(&script.arena, &assertions)
        .expect("clock-3 has ADR-0095 evidence");
    certificate.modulus = 4;
    assert!(
        reconstruct_int_euclidean_residue_to_lean_module(&script.arena, &assertions, &certificate,)
            .is_err()
    );
}

#[test]
fn weakened_satisfiable_near_miss_does_not_route() {
    let text = r"
        (set-logic LIA)
        (declare-fun t () Int)
        (assert (forall ((s Int) (m Int))
          (or (not (= (+ (* 3 m) s) t)) (< s 0) (>= s 2))))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("parse weakened near miss");
    let assertions = script.assertions.clone();
    assert!(int_euclidean_residue_refutation(&script.arena, &assertions).is_none());
    assert_ne!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::IntEuclideanResidue
    );
    assert!(prove_unsat_to_lean_module(&mut script.arena, &assertions).is_err());
}
