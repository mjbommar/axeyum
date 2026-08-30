//! Integration tests for integer-infeasibility (Diophantine) Lean reconstruction
//! (ADR-0042): the canonical `x + y = 0 ∧ x − y = 1 ⇒ 2x = 1` integer-infeasible
//! system reconstructs to a kernel-checked Lean `False`, while an
//! integer-FEASIBLE system is declined (never fabricated).
#![cfg(feature = "full")]

use std::process::Command;

use axeyum_ir::TermArena;
use axeyum_solver::{
    ProofFragment, prove_unsat_to_lean_module, reconstruct_diophantine_proof, scan_proof_fragment,
};

// The golden pin covers the module BODY; the shared banner is pinned once, in
// `axeyum-lean-kernel --test module_banner_pin`. Header text under many pins is
// what made this suite red three times -- see the helper's module note.
#[path = "../../axeyum-lean-kernel/tests/support/lean_golden.rs"]
mod lean_golden;

/// `x + y = 0 ∧ x − y = 1` over `Int`: rational-feasible (`x = ½`) yet
/// integer-infeasible (`2x = 1`). It reconstructs to a kernel-checked Lean `False`
/// through the Diophantine fragment, with the exported module naming the
/// `axeyum_refutation` theorem.
#[test]
fn two_x_eq_one_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();

    // The low-level reconstruction yields a kernel-checked `False` proof term.
    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "x+y=0 ∧ x−y=1 should reconstruct to False, got {:?}",
        proof.err()
    );

    // The unified entry routes it through the Diophantine fragment and renders a
    // self-contained Lean module that names the exported refutation.
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("Diophantine system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(
        source.contains("axeyum_refutation"),
        "rendered module should name the axeyum_refutation theorem"
    );
    // Moved 2026-08-17 by +863 bytes: the module header now declares Lean's
    // compiler-internal `lcErased`/`lcAny`/`lcVoid`. `prelude` mode omits
    // `Init.Prelude`, and Lean 4.34 runs codegen over Prop-valued inductives
    // carrying data, so without them 21 of 77 crosscheck families died on
    // `Unknown constant lcErased` under 4.34.0-rc1 while passing under 4.30.0.
    // The delta is exactly the header text; no proof bytes changed, and the
    // constants stay out of every axiom footprint (asserted separately in
    // `farkas_over_the_integers::codegen_constants_are_declared_but_never_in_the_footprint`).
    // Moved 2026-08-18 by +777 bytes: the header now carries
    // `set_option maxRecDepth 65536` and the paragraph explaining it. Scope-aware
    // `let` sharing binds repeated subterms, a `let` chain is nested syntax, and
    // the constructed-carrier module reached 2,897 levels in one declaration --
    // past Lean 4.30.0's default of 512. Again exactly the header text; no proof
    // bytes changed, and real Lean accepted this module on the same run
    // (`[lean ok] diophantine`, footprint = the four query axioms).
    // Moved 2026-08-29 by -909,862 bytes (1,142,012 -> 232,150, -79.7%): the
    // renderer switched from `render_lean_module` to `render_lean_module_compact`.
    // These are documented as semantically equivalent -- compact hoists repeated
    // CLOSED nodes and never touches anything with loose de Bruijn or free
    // variables -- so this is the SAME proof term, printed with sharing instead
    // of expanded as a tree. Nothing about the argument changed, and
    // `diophantine_module_checks_in_real_lean` (below) re-checks the compact
    // module with the pinned Lean binary and asserts the same axiom footprint.
    //
    // The pin's own reason for existing is why it moved so far. The renderer was
    // printing a hash-consed DAG as a tree with no sharing at all, so its output
    // tracked the tree expansion rather than the argument. Measured the same day
    // on `artifacts/examples/math/number-theory-v0/smt2/`
    // `diophantine-gcd-obstruction-conflict.smt2` (`14x + 21y = 5`, refuted
    // because `gcd(14,21) = 7` does not divide 5): 18,018 distinct DAG nodes,
    // one subterm repeated 169,184 times, and 96,297,506 printed bytes -- over
    // the 64 MB safety cap in `scripts/check-lra-hypothesis-binding.py`, which
    // that gate was crashing on deterministically. Compact renders it at
    // 2,268,010 bytes.
    // RE-PINNED 2026-08-30, SAME LENGTH, DIFFERENT HASH: +0 bytes, and the
    // reason is a pure PERMUTATION rather than any change to proof text.
    // Dumping the rendered module at the previous pin commit (`a7d555e59`) and
    // at HEAD and diffing showed exactly eight differing lines -- `def Int.le`
    // and `def Int.lt`, byte-identical, moved from ~line 171 up to ~line 127,
    // directly after `inductive Int`. Sorting both files gives IDENTICAL
    // output, so nothing else moved and no character changed.
    //
    // Cause: `a70e2dc4d` (four Int order-coercion mirrors) and `07c9c9f09`
    // (the sign-of-a-product family) added declarations that reference
    // `Int.le`/`Int.lt`, which pulls both earlier in the dependency-ordered
    // emission. Emitting a `def` EARLIER is always safe in Lean -- a
    // definition must precede its uses, never follow them -- and the real-Lean
    // check below re-verifies the module rather than taking that on argument.
    //
    // Worth knowing for the next mover: a `+0 bytes` delta on this pin is the
    // signature of a reordering, not an edit. Diff two dumps before assuming a
    // proof changed; `sort | cmp` answers "permutation or not" in one command.
    lean_golden::assert_golden_module("diophantine", &source, (232_150, 0xa19c_c777_e9d8_eddb));
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::Diophantine
    );
}

/// An integer-FEASIBLE system `x + y = 2 ∧ x − y = 0` (sat at `x = y = 1`) has no
/// Diophantine refutation and must be declined — never fabricated.
#[test]
fn feasible_system_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let two = arena.int_const(2);
    let e1 = arena.eq(xpy, two).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let zero = arena.int_const(0);
    let e2 = arena.eq(xmy, zero).unwrap();

    assert!(
        reconstruct_diophantine_proof(&arena, &[e1, e2]).is_err(),
        "a feasible integer system must not produce a Diophantine refutation"
    );
    // It is not classified as the Diophantine fragment either.
    assert_ne!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::Diophantine,
        "feasible system should not route to the Diophantine fragment"
    );
}

/// A cancelling system whose Diophantine refutation has the **degenerate `g = 0`
/// row**: `x + y = 0 ∧ y + z = 0 ∧ x − z = 1`. The integer combination
/// `−E₁ + E₂ + E₃` cancels every variable, leaving `0 = 1` (`combined = []`,
/// `constant = 1`). This reconstructs to a kernel-checked `False` through the
/// Diophantine fragment via the sign-based `Not (Eq Z zero 1)` close — no
/// discreteness needed.
#[test]
fn cancelling_system_zero_eq_const_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let ypz = arena.int_add(y, z).unwrap();
    let e2 = arena.eq(ypz, zero).unwrap();
    let xmz = arena.int_sub(x, z).unwrap();
    let one = arena.int_const(1);
    let e3 = arena.eq(xmz, one).unwrap();

    // Low-level reconstruction yields a kernel-checked `False` proof term.
    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2, e3]);
    assert!(
        proof.is_ok(),
        "cancelling 0 = 1 system should reconstruct to False, got {:?}",
        proof.err()
    );

    // The unified entry routes it through the Diophantine fragment and renders a
    // self-contained Lean module naming the exported refutation.
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
        .expect("cancelling system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(
        source.contains("axeyum_refutation"),
        "rendered module should name the axeyum_refutation theorem"
    );
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2, e3]),
        ProofFragment::Diophantine
    );
}

/// A 2-equality cancelling system `x = 1 ∧ x = 2` whose combination `−E₁ + E₂`
/// cancels `x`, leaving the degenerate `0 = 1` row (`combined = []`, `constant = 1`).
/// Like the 3-equality case, it reconstructs to a kernel-checked `False`.
#[test]
fn x_eq_one_and_x_eq_two_zero_eq_const_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let e1 = arena.eq(x, one).unwrap();
    let e2 = arena.eq(x, two).unwrap();

    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "x=1 ∧ x=2 (0 = 1 row) should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("x=1 ∧ x=2 should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(source.contains("axeyum_refutation"));
}

// Real-Lean toolchain discovery and skip accounting, shared with the other
// Lean-gated suites. The replaced local copy looked at `~/.elan/bin/lean`
// (elan's SHIM directory, absent unless elan has been sourced) and `which lean`,
// so an installed `~/.elan/toolchains/*/bin/lean` was invisible and this check
// skipped while the suite printed `ok`.
#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

/// **Real-Lean crosscheck**: the rendered Diophantine module must be accepted by a
/// genuine `lean` binary (skips gracefully if none is installed), and `#print
/// axioms axeyum_refutation` must not depend on `sorryAx`. This is the end-to-end
/// kernel-checked integer-proof payoff of ADR-0042.
#[test]
fn diophantine_module_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("Diophantine system reconstructs to a Lean module");
    assert_eq!(frag, ProofFragment::Diophantine);

    let Some(bin) = lean_probe::lean_bin_or_skip("diophantine", 1) else {
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_diophantine");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("diophantine.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the diophantine module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{source}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "diophantine proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] diophantine: {}",
        stdout.trim().replace('\n', " | ")
    );
    lean_probe::report_checked("diophantine", 1);
}
