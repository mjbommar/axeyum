//! ADR-0105: checked affine-growth universals reconstructed through Euclidean
//! decomposition and guarded exact `ite` semantics.
#![cfg(feature = "full")]

use std::process::Command;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, int_affine_growth_refutation, prove_unsat_to_lean_module,
    reconstruct_int_affine_growth_to_lean_module, scan_proof_fragment,
};

// The golden pin covers the module BODY; the shared banner is pinned once, in
// `axeyum-lean-kernel --test module_banner_pin`. Header text under many pins is
// what made this suite red three times -- see the helper's module note.
#[path = "../../axeyum-lean-kernel/tests/support/lean_golden.rs"]
mod lean_golden;

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
    // `scripts/check-lean-gate.sh`: accepted, and no `sorryAx`. Before that family
    // existed, "Lean accepts this" was a comment nothing ran.
    //
    // RE-PINNED 2026-08-16, and the module GREW 174,524 -> 206,580 bytes for a
    // good reason: `Int.euclidean_decomposition` stopped being an axiom and
    // became a theorem, so the export now carries its proof instead of an
    // assumption. The reference below is therefore to a derived law, not a
    // ledger axiom. MEASURED 2026-08-16 through `lean_crosscheck`:
    // `#print axioms axeyum_refutation` now reports
    // `[axeyum.reconstruct.dio.hyp._14, axeyum.reconstruct.dio.x._0 … x._3]` —
    // the query's own parameters and NOTHING ELSE. `Int.euclidean_decomposition`
    // is gone from the list, so this refutation depends on no library axiom at
    // all. `check_one_lean` now fails any module whose axiom list contains an
    // `Int.` entry, so the shrink is a gate rather than a comment.
    // The +1_640 of HEADER text that made this pin red on 2026-08-18 -- `b760fd6ae`
    // (+863, Lean's codegen constants) and `46724faec` (+777, `maxRecDepth`), the
    // third recurrence of one mechanism -- can no longer reach it: the pin below
    // covers the module BODY, and the banner is pinned once in
    // `axeyum-lean-kernel --test module_banner_pin`. If this moves, PROOF text
    // moved. See `crates/axeyum-lean-kernel/tests/support/lean_golden.rs`.
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
    lean_golden::assert_golden_module("affine-growth", &source, (279_531, 0x191f_62fa_207f_ea53));
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

// Real-Lean toolchain discovery and skip accounting, shared with the other
// Lean-gated suites. Until this test existed, the golden pin above only
// asserted the rendered bytes matched a blessed hash -- never that a real Lean
// binary still accepts them. See `lean_probe.rs`'s module doc for the
// resolution policy (elan's toolchain directories are not on `PATH`).
#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

/// **Real-Lean crosscheck**: the rendered affine-growth module must be
/// accepted by a genuine `lean` binary (skips gracefully if none is
/// installed), and `#print axioms axeyum_refutation` must not depend on
/// `sorryAx`. This is the end-to-end kernel-checked payoff of ADR-0105 that
/// the byte pin alone cannot demonstrate.
#[test]
fn affine_growth_module_checks_in_real_lean() {
    let script = parse_script(REPAIR_CONST_NTERM).expect("parse repair-const-nterm");
    let assertions = script.assertions.clone();
    let certificate = int_affine_growth_refutation(&script.arena, &assertions)
        .expect("target has ADR-0097 evidence");
    let source =
        reconstruct_int_affine_growth_to_lean_module(&script.arena, &assertions, &certificate)
            .expect("target reconstructs");

    let Some(bin) = lean_probe::lean_bin_or_skip("affine-growth", 1) else {
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_affine_growth");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("affine_growth.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the affine-growth module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "affine-growth proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] affine-growth: {}",
        stdout.trim().replace('\n', " | ")
    );
    lean_probe::report_checked("affine-growth", 1);
}
