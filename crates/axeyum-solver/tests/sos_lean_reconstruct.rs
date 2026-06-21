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

/// A single square of a ±1-coefficient LINEAR form — `(x − y)² < 0` — reconstructs
/// to a kernel-checked `False` (slice 2a): the repeated factor `x − y` maps to a
/// kernel term via the LRA encoding and `sq_nonneg (x−y)` discharges `0 ≤ (x−y)²`.
/// Still no ring normalizer (the lhs is literally `ℓ·ℓ`).
#[test]
fn x_minus_y_squared_lt_zero_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let diff = arena.real_sub(x, y).unwrap();
    let sq = arena.real_mul(diff, diff).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(sq, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("(x−y)² < 0 reconstructs to a kernel-checked False");
    assert_eq!(fragment, ProofFragment::Sos);
    assert!(source.contains("axeyum_refutation"));
}

/// Out of scope for this slice: a square whose linear form has a coefficient
/// outside ±1 — `(x + x)² < 0` (`x + x` collects to `2·x`). `lin_to_r`'s slice does
/// not model the coefficient `2`, so the reconstructor must *decline* (error)
/// rather than fabricate a proof. (A sum-of-monomials SOS likewise needs the ring
/// normalizer — a later slice.)
#[test]
fn square_with_coefficient_outside_pm_one_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two_x = arena.real_add(x, x).unwrap(); // x + x = 2x (coefficient 2)
    let sq = arena.real_mul(two_x, two_x).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(sq, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let result = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]);
    assert!(
        result.is_err(),
        "(x+x)² < 0 (a square with coefficient 2) is outside lin_to_r's ±1 slice \
         and must be declined, not proven"
    );
}

/// Slice 2b — the degree-2 two-variable AM-GM sum form
/// `x*x + y*y − (x*y + x*y) < 0` (i.e. `x² + y² − 2xy < 0`). Unlike the earlier
/// slices, the asserted lhs is a **sum of monomials**, not a literal `ℓ·ℓ`, so the
/// reconstruction must PROVE the ring identity `Eq R p ((x−y)·(x−y))` in the kernel
/// and rewrite square-nonnegativity across it. Success means the trusted kernel
/// accepted that ring-identity proof and the closing order chain.
#[test]
fn am_gm_two_var_sum_form_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap(); // x² + y²
    let two_xy = arena.real_add(xy, xy).unwrap(); // x·y + x·y
    let lhs = arena.real_sub(sum_sq, two_xy).unwrap(); // x² + y² − 2xy
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion]).expect(
        "AM-GM sum form `x²+y²−2xy < 0` reconstructs to a kernel-checked False via the ring \
         identity p = (x−y)·(x−y)",
    );
    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "the AM-GM sum form must route to the SOS fragment"
    );
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// Out of scope for this slice: `x*x + y*y < 0` (i.e. `x² + y² < 0`). It is UNSAT,
/// but it is **not** a single perfect square — it is a *sum* of two independent
/// squares (`x²` and `y²`), which this AM-GM slice does not cover. The
/// reconstructor must *decline* (error) rather than fabricate a proof.
#[test]
fn sum_of_two_squares_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let lhs = arena.real_add(xx, yy).unwrap(); // x² + y²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let result = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]);
    assert!(
        result.is_err(),
        "x² + y² < 0 is a sum of two independent squares, not a single perfect square; \
         it is outside this AM-GM slice and must be declined, not proven"
    );
}
