//! Genuine Lean reconstruction for the checked ADR-0099 nested-XOR theorem.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, int_nested_xor_refutation, prove_unsat_to_lean_module,
    reconstruct_int_nested_xor_to_lean_module,
};

const ISSUE_4433: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress1__quantifiers__issue4433-nqe.smt2"
));

#[test]
fn issue4433_reconstructs_through_three_universal_instances() {
    let mut script = parse_script(ISSUE_4433).expect("parse issue4433");
    let assertions = script.assertions.clone();
    let certificate = int_nested_xor_refutation(&script.arena, &assertions)
        .expect("issue4433 has an ADR-0099 certificate");
    let source =
        reconstruct_int_nested_xor_to_lean_module(&script.arena, &assertions, &certificate)
            .expect("certificate reconstructs");
    assert!(source.contains("theorem axeyum_refutation : False"));
    assert!(!source.contains("sorryAx"));

    let (fragment, routed) =
        prove_unsat_to_lean_module(&mut script.arena, &assertions).expect("router reconstructs");
    assert_eq!(fragment, ProofFragment::IntNestedXor);
    assert!(routed.contains("theorem axeyum_refutation : False"));
}

#[test]
fn signed_pivots_and_swapped_children_reconstruct() {
    let text = r"
        (set-logic LIA)
        (assert (forall ((a Int) (b Int))
          (xor
            (forall ((c Int))
              (= (ite (= 3 c) 7 (- 2))
                 (ite (= 5 a) 7 (- 2))))
            (xor (= (- 4) b) (= 5 a)))))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("parse swapped nested-XOR theorem");
    let assertions = script.assertions.clone();
    let certificate = int_nested_xor_refutation(&script.arena, &assertions)
        .expect("swapped theorem has a certificate");
    reconstruct_int_nested_xor_to_lean_module(&script.arena, &assertions, &certificate)
        .expect("signed/swapped theorem reconstructs");
    let (fragment, _) =
        prove_unsat_to_lean_module(&mut script.arena, &assertions).expect("router reconstructs");
    assert_eq!(fragment, ProofFragment::IntNestedXor);
}

#[test]
fn tampered_nested_xor_certificate_is_rejected_before_proof_building() {
    let script = parse_script(ISSUE_4433).expect("parse issue4433");
    let assertions = script.assertions.clone();
    let mut certificate = int_nested_xor_refutation(&script.arena, &assertions)
        .expect("issue4433 has an ADR-0099 certificate");
    certificate.then_value = certificate.else_value;
    assert!(
        reconstruct_int_nested_xor_to_lean_module(&script.arena, &assertions, &certificate,)
            .is_err()
    );
}

#[test]
fn oversized_outer_pivot_declines_before_proof_building() {
    let text = r"
        (set-logic LIA)
        (assert (forall ((a Int) (b Int))
          (xor (xor (= a 5000) (= b 0))
               (forall ((c Int))
                 (= (ite (= a 5000) 1 2) (ite (= c 0) 1 2))))))
        (check-sat)
    ";
    let script = parse_script(text).expect("oversized nested-XOR theorem parses");
    let certificate = int_nested_xor_refutation(&script.arena, &script.assertions)
        .expect("oversized theorem still has a logical certificate");
    assert!(
        reconstruct_int_nested_xor_to_lean_module(&script.arena, &script.assertions, &certificate,)
            .is_err()
    );
}
