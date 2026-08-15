//! ADR-0105: checked affine-growth universals reconstructed through Euclidean
//! decomposition and guarded exact `ite` semantics.
#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, int_affine_growth_refutation, prove_unsat_to_lean_module,
    reconstruct_int_affine_growth_to_lean_module, scan_proof_fragment,
};

const REPAIR_CONST_NTERM: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress1__quantifiers__repair-const-nterm.smt2"
));

#[test]
fn repair_const_nterm_reconstructs_and_routes() {
    let mut script = parse_script(REPAIR_CONST_NTERM).expect("parse repair-const-nterm");
    let assertions = script.assertions.clone();
    let certificate = int_affine_growth_refutation(&script.arena, &assertions)
        .expect("target has ADR-0097 evidence");
    let source =
        reconstruct_int_affine_growth_to_lean_module(&script.arena, &assertions, &certificate)
            .expect("target reconstructs");
    let fnv1a = source
        .bytes()
        .fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
        });
    // Re-pinned 2026-08-15 (was `(79_801, 0x0e88_e1a5_ecbf_6a7a)`): `0fc7cc357`
    // discharged five of the six remaining integer axioms (`integer: axiom=6 → 1`),
    // so `Int.add_assoc`, `Int.mul_assoc`, `Int.left_distrib`, `Int.add_le_add` and
    // `Int.add_lt_add_of_le_of_lt` are theorems whose proof terms are now reachable
    // from this refutation and therefore emitted. Fewer axioms, more bytes. That
    // commit re-pinned `diophantine_lean_reconstruct` — which is in the Lean gate —
    // and did not re-pin this suite, which is in no gate; the pin shipped red.
    //
    // These bytes are CHECKED, not merely re-typed. `lean_crosscheck`'s
    // `quantified_lia_affine_growth_checks_in_real_lean` family, added in the same
    // commit as this re-pin, hands exactly this module to Lean 4.30.0 under
    // `scripts/check-lean-gate.sh`: accepted, `#print axioms axeyum_refutation`
    // reports `[Int.euclidean_decomposition, axeyum.reconstruct.dio.hyp._14,
    // axeyum.reconstruct.dio.x._0 … x._3]` — one ledger axiom plus the query's own
    // parameters — and no `sorryAx`. Before that family existed, "Lean accepts this"
    // was a comment nothing ran.
    assert_eq!((source.len(), fnv1a), (174_524, 0x298c_fdc2_b3fe_d3d5));
    assert!(source.contains("theorem axeyum_refutation : False"));
    assert!(source.contains("euclidean_decomposition"));
    assert!(!source.contains("sorryAx"));

    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("generic router reconstructs target");
    assert_eq!(fragment, ProofFragment::IntAffineGrowth);
    assert!(routed.contains("theorem axeyum_refutation : False"));
}

#[test]
fn signed_swapped_multibinder_checked_class_reconstructs() {
    let text = r"
        (set-logic LIA)
        (assert (forall ((unused0 Int) (x Int) (unused1 Int))
          (not (>=
            (+ (* (- 1) (ite (= (- 4) x) (- 2) 5)) (* 2 x))
            (- 3)))))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("parse signed/swapped class member");
    let assertions = script.assertions.clone();
    let certificate = int_affine_growth_refutation(&script.arena, &assertions)
        .expect("orientation variant is in ADR-0097 class");
    reconstruct_int_affine_growth_to_lean_module(&script.arena, &assertions, &certificate)
        .expect("orientation variant reconstructs");
    let (fragment, _) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("orientation variant routes");
    assert_eq!(fragment, ProofFragment::IntAffineGrowth);
}

#[test]
fn tampered_affine_certificate_is_rejected_before_proof_building() {
    let script = parse_script(REPAIR_CONST_NTERM).expect("parse repair-const-nterm");
    let assertions = script.assertions.clone();
    let mut certificate = int_affine_growth_refutation(&script.arena, &assertions)
        .expect("target has ADR-0097 evidence");
    certificate.coefficient = 4;
    assert!(
        reconstruct_int_affine_growth_to_lean_module(&script.arena, &assertions, &certificate,)
            .is_err()
    );
}

#[test]
fn binder_dependent_near_miss_does_not_route() {
    let text = r"
        (set-logic LIA)
        (declare-fun p () Int)
        (declare-fun a () Int)
        (assert (forall ((x Int))
          (not (>= (- (* 3 x) (ite (= x p) a x)) 1))))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("parse binder-dependent near miss");
    let assertions = script.assertions.clone();
    assert!(int_affine_growth_refutation(&script.arena, &assertions).is_none());
    assert_ne!(
        scan_proof_fragment(&script.arena, &assertions),
        ProofFragment::IntAffineGrowth
    );
    assert!(prove_unsat_to_lean_module(&mut script.arena, &assertions).is_err());
}
