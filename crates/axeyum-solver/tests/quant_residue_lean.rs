//! ADR-0104: Euclidean-residue universals reconstructed from the general
//! integer-prelude decomposition theorem.
#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, int_euclidean_residue_refutation, prove_unsat_to_lean_module,
    reconstruct_int_euclidean_residue_to_lean_module, scan_proof_fragment,
};

// The golden pin covers the module BODY; the shared banner is pinned once, in
// `axeyum-lean-kernel --test module_banner_pin`. Header text under many pins is
// what made this suite red three times -- see the helper's module note.
#[path = "../../axeyum-lean-kernel/tests/support/lean_golden.rs"]
mod lean_golden;

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
            // The +1_640 of HEADER text that made this pin red on 2026-08-18 --
            // `b760fd6ae` (+863, Lean's codegen constants) and `46724faec` (+777,
            // `maxRecDepth`), the third recurrence of one mechanism -- can no longer
            // reach it: the pin below covers the module BODY, and the banner is pinned
            // once in `axeyum-lean-kernel --test module_banner_pin`. If this moves,
            // PROOF text moved.
            // RE-PINNED 2026-08-30 -- a PERMUTATION, not an edit. Every one of the five
            // golden modules moved by +0 bytes with a different hash on the same day,
            // and the cause is shared: `a70e2dc4d` (four Int order-coercion mirrors)
            // and `07c9c9f09` (the sign-of-a-product family) added declarations that
            // reference `Int.le`/`Int.lt`, pulling both definitions earlier in the
            // dependency-ordered emission -- to directly after `inductive Int`.
            // Emitting a `def` earlier is always safe in Lean; a definition must
            // precede its uses, never follow them. Verified by dumping each module at
            // the previous pin commit and at HEAD: `LC_ALL=C sort | cmp` is IDENTICAL
            // for all five, so no character changed anywhere.
            //
            // `LC_ALL=C` is load-bearing in that check. Under this host's en_US.UTF-8,
            // GNU `sort` compares `--` and a blank line as EQUAL and breaks the tie by
            // input order, so a plain `sort | cmp` called two of these five "content
            // changed" when they are permutations like the rest.
            //
            // For the next mover: a `+0 bytes` delta on a golden body is the signature
            // of a reordering. `LC_ALL=C sort | cmp` on two dumps answers
            // "permutation or not" in one command, far cheaper than the bisect the
            // delta invites -- and three runs first, since a same-length hash change
            // is also what a nondeterministic render would produce.
            lean_golden::assert_golden_module(
                "euclidean-residue",
                &source,
                (123_639, 0xbaa1_9475_52ff_e45b),
            );
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
