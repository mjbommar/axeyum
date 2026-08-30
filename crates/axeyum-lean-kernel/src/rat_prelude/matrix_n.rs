//! **`Rat.matMul`** — matrix multiplication over ℚ at *symbolic* dimension,
//! the first matrix content in this kernel that is not fixed at 2×2 or 3×3.
//!
//! ## The encoding, and why no container type is needed
//!
//! [`super::vector`] represents an `n`-vector as a coefficient function
//! `Nat → Rat` plus an explicit bound, and gets Cauchy–Schwarz at arbitrary
//! `n` out of it. A matrix is the same idea one index up: an `m × n` matrix is
//! a function `Nat → Nat → Rat` together with explicit bounds. No `List`, no
//! `Finset`, no product type — none of which this kernel has in any prelude —
//! and `Rat.sumRange` already accepts exactly this shape (63 declarations in
//! this prelude take a `Nat → Nat → Rat`).
//!
//! `Rat.matMul A B k` has type `Nat → Nat → Rat`, i.e. **it is itself a
//! matrix**, so `matMul (matMul A B k) C m` is well-typed with no coercion and
//! associativity can be stated directly.
//!
//! ## Every statement here is POINTWISE, and that is forced
//!
//! `funext` is **absent** from this kernel (positive control of the same kind,
//! present: `congrFun'`). So two pointwise-equal functions are not
//! propositionally equal, and a matrix identity **cannot** be stated as an
//! `Eq` between two `Nat → Nat → Rat` values. Every theorem below therefore
//! concludes at a scalar:
//!
//! > `∀ … i j, matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j`
//!
//! This is not a workaround invented here — [`super::RatPrelude::sum_range_congr`]
//! already takes pointwise equality as its hypothesis for the same reason.
//!
//! ## Associativity is assembly, not new mathematics
//!
//! `(AB)C` and `A(BC)` differ by an interchange of summation order, and
//! [`super::RatPrelude::sum_range_swap`] (Fubini over a ℚ-valued double sum)
//! is exactly that interchange. The proof is four rewrites around it:
//!
//! 1. pull `C s j` inside the inner sum ([`sum_mul_const_right`], itself
//!    `mul_comm` + [`super::RatPrelude::mul_sum_range`] + `mul_comm`);
//! 2. `sum_range_swap`;
//! 3. `mul_assoc` under two nested [`super::RatPrelude::sum_range_congr`]s;
//! 4. pull `A i t` back out of the inner sum (`mul_sum_range`, symm).
//!
//! No induction on any dimension is performed in this file; every induction it
//! rests on was already done in [`super::sum`].

use super::RatPrelude;
use super::ops::{
    radd, rat_ty, rchain, req, rmul, rrefl, rsum_range, rsymm, rtrans, rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matMul`: above `Rat.sumRange`
/// ([`super::sum::SUM_HEIGHT`] = 34), above `Rat.mul`, and above every other
/// height declared in this prelude (the highest so far is 44), following the
/// "outranks everything it unfolds to" convention [`super::defs`] sets.
const MAT_MUL_HEIGHT: u16 = 46;

/// Admit `Rat.matMul` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_n(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mat_mul(d, p)?;
    declare_mat_mul_zero(d, p)?;
    declare_mat_mul_succ(d, p)?;
    declare_mat_mul_assoc(d, p)?;
    declare_mat_mul_add_left(d, p)?;
    declare_mat_mul_add_right(d, p)?;
    declare_mat_mul_smul_left(d, p)
}

/// `Nat → Nat → Rat`, the matrix type.
fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `fun t => A i t * B t j` — the `(i, j)` summand of `A · B`.
fn mat_summand(d: &mut IntDev<'_>, a: ExprId, b: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let ait = d.apply(a, &[i, t]);
    let btj = d.apply(b, &[t, j]);
    let body = rmul(d, ait, btj);
    let nat = d.nat_ty();
    d.lam_fv(t_fv, nat, body)
}

/// `Rat.matMul A B k i j`.
pub(super) fn rmat_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    k: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    d.const_app(p.mat_mul, &[a, b, k, i, j])
}

/// Admit `Rat.matMul : (Nat → Nat → Rat) → (Nat → Nat → Rat) → Nat → Nat →
/// Nat → Rat := fun A B k i j => sumRange (fun t => A i t * B t j) k`.
fn declare_mat_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let summand = mat_summand(d, a, b, i, j);
    let body = rsum_range(d, p, summand, k);
    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_k = d.lam_fv(k_fv, nat, with_i);
        let with_b = d.lam_fv(b_fv, mty, with_k);
        d.lam_fv(a_fv, mty, with_b)
    };
    let ty = {
        let over_j = d.arrow(nat, carrier);
        let over_i = d.arrow(nat, over_j);
        let over_k = d.arrow(nat, over_i);
        let over_b = d.arrow(mty, over_k);
        d.arrow(mty, over_b)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_MUL_HEIGHT),
    })
}

/// `Rat.matMul_zero : ∀ A B i j, matMul A B zero i j = zero` — `Eq.refl`,
/// mirroring [`super::sum`]'s `sumRange_zero`.
fn declare_mat_mul_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_n = d.zero();
    let lhs = rmat_mul(d, p, a, b, zero_n, i, j);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);
    let proof = rrefl(d, zero_r);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_succ : ∀ A B k i j, matMul A B (succ k) i j = matMul A B k i j
/// + A i k * B k j` — `Eq.refl`, mirroring [`super::sum`]'s `sumRange_succ`.
fn declare_mat_mul_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let sk = d.succ(k);
    let lhs = rmat_mul(d, p, a, b, sk, i, j);
    let prior = rmat_mul(d, p, a, b, k, i, j);
    let aik = d.apply(a, &[i, k]);
    let bkj = d.apply(b, &[k, j]);
    let term = rmul(d, aik, bkj);
    let rhs = radd(d, prior, term);
    let stmt = req(d, lhs, rhs);
    let proof = rrefl(d, rhs);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_succ,
        uparams: vec![],
        ty,
        value,
    })
}
