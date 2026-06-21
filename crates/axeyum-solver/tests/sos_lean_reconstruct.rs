//! Slice-1 sum-of-squares (SOS) → Lean reconstruction (ADR-0040).
//!
//! The simplest SOS refutation: the one-variable real query `x*x < 0` is UNSAT
//! (a real square is never negative). This needs **no** ring normalizer — the SOS
//! identity `x² = 1·x²` is trivial — so the reconstructed proof is just
//! square-nonnegativity (`sq_nonneg`) composed with one order step
//! (`lt_of_le_of_lt`) and closed with `lt_irrefl`.
//!
//! These tests exercise the kernel-gated path end to end: success means the
//! trusted [`axeyum_solver::reconstruct`]'s `Kernel` *type-checked* the assembled
//! term to `False`. A buggy reconstruction would fail the `infer`/`def_eq` gate and
//! be rejected, never accepted as an unsound proof — so a passing test is a genuine
//! machine-checked refutation.

use axeyum_ir::{Rational, TermArena};
use axeyum_solver::{
    LraReconstructCtx, ProofFragment, prove_unsat_to_lean_module, reconstruct_sos_proof,
};

/// The trivial single-square query `x*x < 0` reconstructs to a kernel-checked
/// `False`: the dispatch routes it to [`ProofFragment::Sos`] and emits a
/// non-empty Lean module.
#[test]
fn x_squared_lt_zero_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(xx, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("trivial single-square SOS query `x*x < 0` reconstructs to a kernel-checked False");

    // The decisive fact: reconstruction SUCCEEDED, i.e. the trusted kernel accepted
    // the assembled term as a proof of `False`.
    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "the trivial single-square shape must route to the SOS fragment"
    );
    assert!(
        !source.is_empty(),
        "a successful SOS reconstruction must emit a non-empty Lean module"
    );
    // The rendered module proves `False` via the `axeyum_refutation` theorem.
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// General SOS (a multi-variable square like `(x − y)² < 0`) is **out of scope**
/// for this slice — it needs the degree-2 ring normalizer (a later slice). The
/// dedicated SOS reconstructor must *decline* (error) rather than fabricate a
/// proof: it never claims success without a kernel-checked term.
#[test]
fn general_sos_two_variable_square_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let diff = arena.real_sub(x, y).unwrap();
    let sq = arena.real_mul(diff, diff).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(sq, zero).unwrap();

    // The slice-1 SOS reconstructor must decline this shape outright.
    let mut ctx = LraReconstructCtx::new();
    let result = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]);
    assert!(
        result.is_err(),
        "general SOS `(x - y)^2 < 0` (two variables, non-square-of-a-variable lhs) \
         must be declined by the slice-1 reconstructor, not proven"
    );
}
