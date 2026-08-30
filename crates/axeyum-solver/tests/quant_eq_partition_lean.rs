//! ADR-0106: genuine Bool/Int quantifier reconstruction for single-pivot
//! equality partitions.
#![cfg(feature = "full")]

use axeyum_smtlib::{Script, parse_script};
use axeyum_solver::{
    EqualityPartitionRefutationCertificate, Evidence, ProofFragment, SolverConfig,
    produce_evidence, prove_unsat_to_lean_module,
    reconstruct_single_pivot_equality_partition_to_lean_module, scan_proof_fragment,
};

// The golden pin covers the module BODY; the shared banner is pinned once, in
// `axeyum-lean-kernel --test module_banner_pin`. Header text under many pins is
// what made this suite red three times -- see the helper's module note.
#[path = "../../axeyum-lean-kernel/tests/support/lean_golden.rs"]
mod lean_golden;

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
    // Re-pinned 2026-08-15 (was `(51_989, 0x33c9_7d4b_0b70_5040)`): `0fc7cc357`
    // discharged five of the six remaining integer axioms (`integer: axiom=6 → 1`),
    // so the integer laws this refutation reaches are theorems whose proof terms are
    // now emitted. Fewer axioms, more bytes. That commit re-pinned
    // `diophantine_lean_reconstruct` — which is in the Lean gate — and not this
    // suite, which is in no gate; the pin shipped red.
    //
    // CHECKED, not merely re-typed: `lean_crosscheck`'s
    // `quantified_lia_equality_partition_checks_in_real_lean` family, added in the
    // same commit as this re-pin, hands this module to Lean 4.30.0 under
    // `scripts/check-lean-gate.sh`. Accepted; `#print axioms axeyum_refutation`
    // reports `[axeyum.reconstruct.dio.hyp._97]` — the query hypothesis alone, no
    // ledger axiom — and there is no `sorryAx`.
    // The +1_640 of HEADER text that made this pin red on 2026-08-18 -- `b760fd6ae`
    // (+863, Lean's codegen constants) and `46724faec` (+777, `maxRecDepth`), the
    // third recurrence of one mechanism -- can no longer reach it: the pin below
    // covers the module BODY, and the banner is pinned once in
    // `axeyum-lean-kernel --test module_banner_pin`. If this moves, PROOF text
    // moved. See `crates/axeyum-lean-kernel/tests/support/lean_golden.rs`.
    // Re-pinned 2026-08-20 at the same 111_821-byte length: the native Bool
    // package now follows official Lean order `[false, true]`, and the checked
    // partition eliminator therefore writes the false cell before the true cell.
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
        "equality-partition",
        &source,
        (111_821, 0x9f0e_95b5_fa74_c6ab),
    );
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
