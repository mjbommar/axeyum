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
            // Re-pinned 2026-08-15 (was `(33_339, 0x682a_a2a2_d64f_6caf)`):
            // `0fc7cc357` discharged five of the six remaining integer axioms
            // (`integer: axiom=6 → 1`), so the additive/multiplicative laws this
            // refutation reaches are theorems whose proof terms are now emitted.
            // Fewer axioms, more bytes. That commit re-pinned
            // `diophantine_lean_reconstruct` — which is in the Lean gate — and not
            // this suite, which is in no gate; the pin shipped red.
            //
            // CHECKED, not merely re-typed: `lean_crosscheck`'s
            // `quantified_lia_euclidean_residue_checks_in_real_lean` family, added
            // in the same commit as this re-pin, hands this module to Lean 4.30.0
            // under `scripts/check-lean-gate.sh`. Accepted, and no `sorryAx`.
            //
            // RE-PINNED 2026-08-16: the module GREW 83,060 -> 124,121 bytes
            // because `Int.euclidean_decomposition` became a THEOREM, so the
            // export carries its proof rather than an assumption. MEASURED
            // 2026-08-16 through `lean_crosscheck`: `#print axioms
            // axeyum_refutation` now reports `[axeyum.reconstruct.dio.hyp._3,
            // axeyum.reconstruct.dio.x._0]` — the query's own parameters and
            // nothing else. `Int.euclidean_decomposition` is gone, and
            // `check_one_lean` fails any module that reintroduces an `Int.`
            // axiom.
            // RE-PINNED 2026-08-18, +1_640 bytes, and the delta is HEADER TEXT ONLY --
            // no proof byte changed, which is why the same +1_640 lands on four
            // unrelated modules. Two commits moved it, neither of them wrongly:
            //   +863  `b760fd6ae` declares Lean's codegen constants
            //         (`unsafe axiom lcErased/lcAny/lcVoid`); without them 21 of 77
            //         crosscheck families died under Lean 4.34.0-rc1.
            //   +777  `46724faec` adds `set_option maxRecDepth 65536`; a scope-shared
            //         `let` chain is nested syntax and 2,897 bindings in one lemma blow
            //         Lean 4.30.0's default of 512.
            // Each re-pinned only the golden module that sits in a gate (the
            // diophantine/Farkas ones) and not this suite, which sits in none -- the
            // third time that exact pattern has shipped a red pin (see `6389e0194`,
            // 2026-08-15). Caught by the FIRST completed run of `scripts/local-ci.sh`:
            // `artifacts/local-ci-runs/a6ee37c6a-s4.json`.
            assert_eq!((source.len(), fnv1a), (125_761, 0x1a11_6c08_58c3_d8fc));
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
