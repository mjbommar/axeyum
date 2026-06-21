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

/// A square whose linear form has a coefficient outside ±1 — `(x + 2y)² < 0`
/// (= `x² + 4xy + 4y²`). The SOS certificate is the single square `x + 2y` with
/// `d = 1`; its `y`-coefficient is `2`, outside the ±1-form slice, but the
/// integer-coefficient form encoder (`2y = y + y`) now handles it via the
/// denominator-clearing rational-weight path (here `M = 1`, the integer form is
/// `x + 2y`). Genuinely UNSAT, so it now reconstructs to a kernel-checked `False`
/// rather than declining — the kernel gate guarantees the proof is sound.
#[test]
fn square_with_non_unit_form_coefficient_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let two_y = arena.real_mul(two, y).unwrap();
    let x_plus_2y = arena.real_add(x, two_y).unwrap(); // x + 2y (form coefficient 2)
    let sq = arena.real_mul(x_plus_2y, x_plus_2y).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(sq, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]).expect(
        "(x+2y)² < 0 is UNSAT; the integer-coefficient form encoder (2y = y+y) reconstructs it \
         to a kernel-checked False",
    );
    // The kernel `infer`+`def_eq False` gate inside `reconstruct_sos_proof` already
    // accepted `proof`; a non-error result is the machine-checked refutation.
    let _ = proof;
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

/// General SOS-certificate path: `x*x + y*y + (x*y + x*y) < 0` (i.e. `(x+y)² < 0`).
/// The certificate is a single perfect square of the ±1-linear form `x + y`, so the
/// generalized reconstructor (driven by the SOS certificate + degree-2 ring
/// normalizer, NOT the hard-coded `(x−y)²` matcher) must prove
/// `Eq R (x²+y²+2xy) ((x+y)·(x+y))` and refute. The `+2xy` distinguishes it from the
/// AM-GM `−2xy` shape.
#[test]
fn x_plus_y_squared_sum_form_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap(); // x² + y²
    let two_xy = arena.real_add(xy, xy).unwrap(); // x·y + x·y
    let lhs = arena.real_add(sum_sq, two_xy).unwrap(); // x² + y² + 2xy
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion]).expect(
        "(x+y)² < 0 sum form reconstructs to a kernel-checked False via the general SOS \
         certificate path",
    );
    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "the (x+y)² sum form must route to the SOS fragment"
    );
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// General SOS-certificate path on a DIFFERENT variable pair than the old hard-code:
/// `x*x + z*z − (x*z + x*z) < 0` (i.e. `(x−z)² < 0`). Exercises that the generalized
/// path is genuinely certificate-driven, not specialized to the `(x,y)` symbols.
#[test]
fn x_minus_z_squared_sum_form_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let z = arena.real_var("z").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let zz = arena.real_mul(z, z).unwrap();
    let xz = arena.real_mul(x, z).unwrap();
    let sum_sq = arena.real_add(xx, zz).unwrap(); // x² + z²
    let two_xz = arena.real_add(xz, xz).unwrap(); // x·z + x·z
    let lhs = arena.real_sub(sum_sq, two_xz).unwrap(); // x² + z² − 2xz
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("(x−z)² < 0 sum form reconstructs to a kernel-checked False");
    assert_eq!(fragment, ProofFragment::Sos);
    assert!(source.contains("axeyum_refutation"));
}

/// Multi-square slice: `x*x + y*y < 0` (i.e. `x² + y² < 0`) is UNSAT — a *sum* of
/// two independent ±1-unit squares (`x²` and `y²`, certificate `D = [1, 1]`). The
/// reconstructor folds `sq_nonneg x` and `sq_nonneg y` to `0 ≤ x² + y²` and closes
/// the order chain to a kernel-checked `False`. (Previously declined; now handled.)
#[test]
fn sum_of_two_squares_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let lhs = arena.real_add(xx, yy).unwrap(); // x² + y²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("x² + y² < 0 reconstructs to a kernel-checked False");
    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "the sum-of-squares shape must route to the SOS fragment"
    );
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// Multi-square slice with three squares: `x*x + y*y + z*z < 0` (`D = [1, 1, 1]`).
/// Exercises the fold over more than two squares — the right-nested `sosK` and the
/// matching `add_le_add` / `add_zero` rewrites must compose to a kernel-checked
/// `False`.
#[test]
fn sum_of_three_squares_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let zz = arena.real_mul(z, z).unwrap();
    let xy = arena.real_add(xx, yy).unwrap();
    let lhs = arena.real_add(xy, zz).unwrap(); // x² + y² + z²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("x² + y² + z² < 0 reconstructs to a kernel-checked False");
    assert_eq!(fragment, ProofFragment::Sos);
    assert!(source.contains("axeyum_refutation"));
}

/// Integer-weighted sum of squares `2*x*x + 2*y*y < 0` (certificate weights
/// `D = [2, 2]`): each square is expanded into two copies (`x²+x²+y²+y²`), so the
/// nonnegativity fold + ring normalizer discharge it. Kernel-checked `False`.
#[test]
fn integer_weighted_sum_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let two_xx = arena.real_mul(two, xx).unwrap();
    let two_yy = arena.real_mul(two, yy).unwrap();
    let lhs = arena.real_add(two_xx, two_yy).unwrap(); // 2x² + 2y²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("2x²+2y² < 0 reconstructs (integer weights 2 → two copies of each square)");
    assert_eq!(fragment, ProofFragment::Sos);
    assert!(source.contains("axeyum_refutation"));
}

/// HEADLINE — 3-variable AM-GM: `a*a + b*b + c*c − (a*b + b*c + c*a) < 0` is UNSAT
/// (`= ½[(a−b)²+(b−c)²+(c−a)²]`). Its `LDLᵀ` SOS certificate carries a RATIONAL weight
/// (`¾`) and a `±½` linear form, so it is the first query needing denominator
/// clearing. The reconstructor clears denominators (`4·p = (2a−b−c)² + 3·(b−c)²`) and
/// folds entirely in the existing integer machinery — no scaling lemma, no new kernel
/// axiom. Success means the trusted kernel accepted the cleared identity, the
/// nonnegativity fold, and the M-fold negativity chain as a proof of `False`.
#[test]
fn three_var_am_gm_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let a = arena.real_var("a").unwrap();
    let b = arena.real_var("b").unwrap();
    let c = arena.real_var("c").unwrap();
    let aa = arena.real_mul(a, a).unwrap();
    let bb = arena.real_mul(b, b).unwrap();
    let cc = arena.real_mul(c, c).unwrap();
    let ab = arena.real_mul(a, b).unwrap();
    let bc = arena.real_mul(b, c).unwrap();
    let ca = arena.real_mul(c, a).unwrap();
    let sum_sq = {
        let t = arena.real_add(aa, bb).unwrap();
        arena.real_add(t, cc).unwrap() // a² + b² + c²
    };
    let sum_cross = {
        let t = arena.real_add(ab, bc).unwrap();
        arena.real_add(t, ca).unwrap() // ab + bc + ca
    };
    let lhs = arena.real_sub(sum_sq, sum_cross).unwrap(); // a²+b²+c² − (ab+bc+ca)
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion]).expect(
        "3-var AM-GM `a²+b²+c² − (ab+bc+ca) < 0` reconstructs to a kernel-checked False via the \
         denominator-cleared rational-weight SOS path",
    );
    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "the 3-var AM-GM shape must route to the SOS fragment"
    );
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// Out of scope: an OVERSIZED integer weight `17*x*x < 0` (`D = [17]` > the
/// `SOS_MAX_SQUARE_WEIGHT = 16` repetition bound). Expanding it would make the proof
/// 17 squares long; the classifier declines (a denominator/scaling slice handles
/// large and rational weights later). The reconstructor must *decline*, not prove.
#[test]
fn oversized_weight_square_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let seventeen = arena.real_const(Rational::integer(17));
    let lhs = arena.real_mul(seventeen, xx).unwrap(); // 17·x²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let result = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]);
    assert!(
        result.is_err(),
        "17x² < 0 has weight 17 > SOS_MAX_SQUARE_WEIGHT; it must decline, not prove"
    );
}

/// Out of scope: a rational-weight SOS certificate whose cleared denominator exceeds
/// the slice bound (`SOS_RATIONAL_MAX = 64`). `65x² + 64xy + 16y² < 0` is UNSAT
/// (PSD Gram `[[65,32],[32,16]]`), and its `LDLᵀ` certificate's first square is the
/// form `x + (32/65)y` — clearing its denominator needs `C = 65 > 64`. The
/// denominator-clearing reconstructor declines (`Ok(None)`) rather than building a
/// 65-wide kernel term; `reconstruct_sos_proof` then surfaces the decline as an
/// error. A correct decline — never a fabricated proof.
#[test]
fn oversized_cleared_denominator_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let c65 = arena.real_const(Rational::integer(65));
    let c64 = arena.real_const(Rational::integer(64));
    let c16 = arena.real_const(Rational::integer(16));
    let t65 = arena.real_mul(c65, xx).unwrap(); // 65x²
    let t64 = arena.real_mul(c64, xy).unwrap(); // 64xy
    let t16 = arena.real_mul(c16, yy).unwrap(); // 16y²
    let s = arena.real_add(t65, t64).unwrap();
    let lhs = arena.real_add(s, t16).unwrap(); // 65x² + 64xy + 16y²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_lt(lhs, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let result = reconstruct_sos_proof(&mut ctx, &arena, &[assertion]);
    assert!(
        result.is_err(),
        "65x²+64xy+16y² < 0 needs a cleared denominator 65 > SOS_RATIONAL_MAX; it must decline"
    );
}

/// The `p > 0` strict-inequality DUAL: `−x² > 0` is UNSAT (a real square's
/// negation is never positive). The self-checked SOS certificate refutes the
/// `strict_lt == false` atom by certifying `−M ⪰ 0`, so its single square `x`
/// decomposes `−p = x²`. Reconstruction folds `0 ≤ x²` and `0 < −x²` into
/// `0 < x² + (−x²)`, then cancels exactly to `0 < 0`, refuted by `lt_irrefl`.
/// Routes to [`ProofFragment::Sos`] and emits `axeyum_refutation`.
#[test]
fn neg_square_gt_zero_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let neg = arena.real_neg(xx).unwrap(); // −x²
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_gt(neg, zero).unwrap(); // −x² > 0

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("the strict-dual SOS query `−x² > 0` reconstructs to a kernel-checked False");

    assert_eq!(
        fragment,
        ProofFragment::Sos,
        "a `p > 0` SOS certificate must route to the SOS fragment"
    );
    assert!(
        source.contains("axeyum_refutation"),
        "the Lean module must contain the refutation theorem"
    );
}

/// The multi-square `p > 0` dual: `−x² − y² > 0` is UNSAT. The certificate's two
/// squares `x`, `y` decompose `−p = x² + y²`; the reconstructor folds both
/// `sq_nonneg`s into `0 ≤ x² + y²` and combines with `0 < −x²−y²`, cancelling to
/// `0 < 0`.
#[test]
fn neg_sum_of_squares_gt_zero_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let neg = arena.real_neg(sum).unwrap(); // −(x² + y²)
    let zero = arena.real_const(Rational::integer(0));
    let assertion = arena.real_gt(neg, zero).unwrap(); // −x² − y² > 0

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
        .expect("the strict-dual SOS query `−x² − y² > 0` reconstructs to a kernel-checked False");

    assert_eq!(fragment, ProofFragment::Sos);
    assert!(source.contains("axeyum_refutation"));
}
