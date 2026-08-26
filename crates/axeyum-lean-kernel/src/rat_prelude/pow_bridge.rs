//! `Rat.pow_natDivSucc_two` — the bridge between `Rat.pow`'s
//! repeated-multiplication form and the `Rat.normalize`d, `2ⁿ`-denominator
//! form of the same rational, for the base `Rat.natDivSucc 1 1` (i.e. `1/2`).
//!
//! ## Why this exists
//!
//! `creal/exponential.rs` names the missing piece precisely: building a
//! Cauchy witness for the geometric bound `g n := ofRat (2/2ⁿ)` along
//! `CReal.pow`-based machinery (`geometric.rs`'s `geom_pair_within`/
//! `pow_half_le_natDivSucc`) needs `Rat.pow (natDivSucc 1 1) n` and
//! `Rat.normalize 1 (2ⁿ) _` identified — the same value, two representations,
//! with nothing bridging them. This file is exactly that bridge, "a clean,
//! bounded induction via `normalize_mul_normalize`", as anticipated there.
//!
//! ## The statement
//!
//! `Rat.pow_natDivSucc_two : ∀ (n : Nat),
//! pow (natDivSucc 1 1) n = normalize (ofNat 1) (Nat.pow 2 n) w`,
//! where `w : 1 ≤ Nat.pow 2 n` is built from `Nat.pow_pos`.
//!
//! ## The proof, by induction on `n`
//!
//! - **Base** (`n = 0`): `pow g 0 = one` by `Rat.pow_zero`, and
//!   `Rat.self_normalize` applied at `Rat.one` gives `normalize (num one)
//!   (den one) (den_pos one) = one`. Its LHS is definitionally the target —
//!   `num one`/`den one` project out of `Rat.one`'s `mk` fields by ι-reduction,
//!   `Nat.pow 2 0` ι-reduces to `1` (`Nat.pow` is *structural* recursion on
//!   the exponent, `nat_prelude/defs.rs`, not `Nat.gcd`'s well-founded one —
//!   the reduction this step needs never touches well-founded recursion),
//!   and the positivity witnesses agree by `Prop` proof irrelevance. So this
//!   theorem, reversed, closes the base case directly; no separate lemma
//!   needed for `0 ≤` normalize's internal `gcd` bookkeeping.
//! - **Step**: `pow g (succ j) = mul (pow g j) g` by `Rat.pow_succ`; rewrite
//!   `pow g j` to `normalize 1 (2ʲ) w_j` by the induction hypothesis; then
//!   `Rat.normalize_mul_normalize` at `(1, 2ʲ, w_j, 1, 2, h₂)` gives `mul
//!   (normalize 1 (2ʲ) w_j) (normalize 1 2 h₂) = normalize (1·1) (2ʲ·2) _`.
//!   `g` is definitionally `normalize 1 2 (one_le_succ 1)`
//!   (`Rat.natDivSucc`'s own definition, `rat_prelude/archimedean.rs`) —
//!   again by proof irrelevance the *specific* positivity witness supplied
//!   here does not have to match — and `1·1 ≡ 1`, `2ʲ·2 ≡ 2^(j+1)` both hold
//!   definitionally (`Int.mul` on an `ofNat` pair, and `Nat.pow`'s own
//!   `succ`-case ι-reduction respectively — again no well-founded recursion
//!   anywhere in this chain). So the conclusion of `normalize_mul_normalize`
//!   is definitionally the goal, and the whole step is three lemma
//!   applications chained by `Eq Rat` transitivity.

use super::RatPrelude;
use super::ops::{normalize, rchain, rcongr, req, rmul, rone, rpow, rsymm, rtrans};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `Rat.natDivSucc 1 1` — the constant base `g = 1/2` this bridge is about.
fn g_expr(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let one_nat = d.num(1);
    d.const_app(p.nat_div_succ, &[one_nat, one_nat])
}

/// `w(n) : 1 ≤ Nat.pow 2 n`, via `Nat.pow_pos 2 n two_pos` — `two_pos : Lt
/// zero 2` is `Nat.le_succ 1 : Le 1 2`, definitionally the same proposition.
fn witness(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
    let nat = p.int.nat;
    let one_nat = d.num(1);
    let two = d.num(2);
    let two_pos = d.lemma(nat.le_succ, &[one_nat]);
    let pow_pos_fn = d.lemma(nat.pow_pos, &[two, n]);
    d.apply(pow_pos_fn, &[two_pos])
}

/// `Rat.normalize (ofNat 1) (Nat.pow 2 n) (witness n)` — the right-hand side
/// of the bridge, at a given exponent `n`.
fn target(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
    let two = d.num(2);
    let pow2n = d.pow(two, n);
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let w = witness(d, p, n);
    normalize(d, one_int, pow2n, w)
}

/// `Eq Rat (pow g n) (target n)` — the motive, instantiated at `n`.
fn motive(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
    let g = g_expr(d, p);
    let lhs = rpow(d, p, g, n);
    let rhs = target(d, p, n);
    req(d, lhs, rhs)
}

/// The base case (`n = 0`): `pow g 0 = one = target 0`, by `pow_zero` then
/// `self_normalize` (reversed) — see the module doc for why the second step
/// needs no `gcd`-reduction.
fn base_case(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let g = g_expr(d, p);
    let zero = d.zero();
    let pow_g_zero = rpow(d, p, g, zero);
    let one = rone(d, p);
    let target_zero = target(d, p, zero);

    let pow_zero_step = d.lemma(p.pow_zero, &[g]);
    let self_step = d.lemma(p.self_normalize, &[one]);
    let flipped = rsymm(d, target_zero, one, self_step);
    rtrans(d, pow_g_zero, one, target_zero, pow_zero_step, flipped)
}

/// The step case: from `ih : pow g j = target j`, prove `pow g (succ j) =
/// target (succ j)` — see the module doc for the three-lemma chain.
fn succ_case(d: &mut IntDev<'_>, p: RatPrelude, j: ExprId, ih: ExprId) -> ExprId {
    let nat = p.int.nat;
    let g = g_expr(d, p);
    let sj = d.succ(j);

    let pow_g_sj = rpow(d, p, g, sj);
    let pow_g_j = rpow(d, p, g, j);
    let mul_powgj_g = rmul(d, pow_g_j, g);
    let target_j = target(d, p, j);
    let mul_targetj_g = rmul(d, target_j, g);
    let target_sj = target(d, p, sj);

    // pow g (succ j) = mul (pow g j) g.
    let step1 = d.lemma(p.pow_succ, &[g, j]);

    // mul (pow g j) g = mul (target j) g, rewriting by the induction
    // hypothesis.
    let step_ih = rcongr(d, pow_g_j, target_j, ih, &|d, x| rmul(d, x, g));

    // mul (target j) g = target (succ j): `normalize_mul_normalize` at
    // (1, 2^j, w_j, 1, 2, two_positive), whose conclusion is definitionally
    // this goal (`g` unfolds to `normalize 1 2 _`, `1*1 ≡ 1`,
    // `2^j * 2 ≡ 2^(succ j)`; see the module doc).
    let two = d.num(2);
    let pow2j = d.pow(two, j);
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let wj = witness(d, p, j);
    let two_positive = d.lemma(nat.le_succ, &[one_nat]);
    let step2 = d.lemma(
        p.normalize_mul_normalize,
        &[one_int, pow2j, wj, one_int, two, two_positive],
    );

    let (_, proof) = rchain(
        d,
        pow_g_sj,
        &[
            (mul_powgj_g, step1),
            (mul_targetj_g, step_ih),
            (target_sj, step2),
        ],
    );
    proof
}

/// Admit `Rat.pow_natDivSucc_two`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** the proof, not that a script gave up.
pub(super) fn declare_pow_bridge(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    d.theorem(p.pow_nat_div_succ_two, 1, &|d, v| {
        let n = v[0];
        let stmt = motive(d, p, n);
        let proof = d.induct(
            &|d, x| motive(d, p, x),
            &|d| base_case(d, p),
            &|d, j, ih| succ_case(d, p, j, ih),
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}
