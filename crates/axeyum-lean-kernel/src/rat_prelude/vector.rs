//! **`Rat.dotN`** — the n-dimensional dot product over ℚ, the first
//! inner product in this kernel that is not fixed at a specific dimension.
//!
//! ## Why a coefficient function, not a `Matrix`/`Vector` type
//!
//! `matrix.rs`'s own note on `Rat.adj2` applies here verbatim: a container
//! type needs a product/tuple (or a `List`/`Fin n`), and this kernel has
//! none of those in any prelude. So a "vector" is not reified as its own
//! carrier — it is represented exactly the way [`super::RatPrelude::sum_range`]
//! already represents a summand: a coefficient **function** `Nat → Rat`
//! together with an explicit dimension bound `n`. `Rat.dotN u v n` is then
//! nothing but `sumRange (fun i => u i * v i) n`, and every algebraic law
//! below is proved by composing [`super::sum`]'s own `sumRange` algebra
//! rather than by a fresh induction on `n` — the same two-step
//! congr-then-split/pull shape [`super::probability`]'s `expectation_add`/
//! `expectation_smul` already use for a structurally identical two-function
//! definition.
//!
//! ## What ℚ already had for step 2
//!
//! [`super::RatPrelude::sq_nonneg`] (`∀ a, 0 ≤ a*a`) already exists in
//! `laws.rs`, proved from `Int.sq_nonneg` through the numerator — nothing
//! new to land there. [`declare_dot_n_self_nonneg`] is exactly that fact
//! carried pointwise through [`super::sum::declare_sum`]'s
//! `sumRange_nonneg`.

use super::RatPrelude;
use super::ops::{
    radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rlt, rmul, rneg, rone, rrefl,
    rsum_range, rsymm, rtrans, rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.dotN`: above every constant it calls directly
/// (`Rat.sumRange` at [`super::sum::SUM_HEIGHT`] = 34, `Rat.mul`) and above
/// every other height declared in this prelude so far (`probability.rs`'s
/// `PAIRWISE_UNCORRELATED_HEIGHT` = 41, the highest so far).
const DOT_N_HEIGHT: u16 = 42;

/// Admit `Rat.dotN` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_vector(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_dot_n(d, p)?;
    declare_dot_n_zero(d, p)?;
    declare_dot_n_succ(d, p)?;
    declare_dot_n_comm(d, p)?;
    declare_dot_n_add_left(d, p)?;
    declare_dot_n_smul_left(d, p)?;
    declare_dot_n_self_nonneg(d, p)?;
    declare_dot_n_two(d, p)?;
    declare_dot_n_cauchy_schwarz(d, p)
}

/// `fun i => Rat.mul (u i) (v i)` — the dot-product summand.
fn dot_summand(d: &mut IntDev<'_>, u: ExprId, v: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let vi = d.apply(v, &[i]);
    let body = rmul(d, ui, vi);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => Rat.add (u1 i) (u2 i)`.
fn combined_fn(d: &mut IntDev<'_>, u1: ExprId, u2: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let u1i = d.apply(u1, &[i]);
    let u2i = d.apply(u2, &[i]);
    let body = radd(d, u1i, u2i);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => Rat.add (Rat.mul (u1 i) (v i)) (Rat.mul (u2 i) (v i))`.
fn split_dot_summand(d: &mut IntDev<'_>, u1: ExprId, u2: ExprId, v: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let u1i = d.apply(u1, &[i]);
    let u2i = d.apply(u2, &[i]);
    let vi = d.apply(v, &[i]);
    let u1v = rmul(d, u1i, vi);
    let u2v = rmul(d, u2i, vi);
    let body = radd(d, u1v, u2v);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => Rat.mul a (u i)`.
fn scale_fn(d: &mut IntDev<'_>, a: ExprId, u: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let body = rmul(d, a, ui);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => Rat.mul a (Rat.mul (u i) (v i))`.
fn scale_dot_summand(d: &mut IntDev<'_>, a: ExprId, u: ExprId, v: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ui = d.apply(u, &[i]);
    let vi = d.apply(v, &[i]);
    let uv = rmul(d, ui, vi);
    let body = rmul(d, a, uv);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `Rat.dotN u v n`.
pub(super) fn rdot_n(d: &mut IntDev<'_>, p: RatPrelude, u: ExprId, v: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.dot_n, &[u, v, n])
}

/// Admit `Rat.dotN : (Nat → Rat) → (Nat → Rat) → Nat → Rat := fun u v n =>
/// sumRange (fun i => u i * v i) n`.
fn declare_dot_n(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = dot_summand(d, u, v);
    let body = rsum_range(d, p, summand, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_v = d.lam_fv(v_fv, fn_ty, with_n);
        d.lam_fv(u_fv, fn_ty, with_v)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        let over_v = d.arrow(fn_ty, inner);
        d.arrow(fn_ty, over_v)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dot_n,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DOT_N_HEIGHT),
    })
}

/// `Rat.dotN_zero : ∀ u v, dotN u v zero = zero` — `Eq.refl`, mirroring
/// [`super::sum`]'s own `sumRange_zero`.
fn declare_dot_n_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let zero_n = d.zero();
    let lhs = rdot_n(d, p, u, v, zero_n);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);
    let proof = rrefl(d, zero_r);

    let value = {
        let with_v = d.lam_fv(v_fv, fn_ty, proof);
        d.lam_fv(u_fv, fn_ty, with_v)
    };
    let ty = {
        let with_v = d.pi_fv(v_fv, fn_ty, stmt);
        d.pi_fv(u_fv, fn_ty, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_succ : ∀ u v n, dotN u v (succ n) = dotN u v n + u n * v n` —
/// `Eq.refl`, mirroring [`super::sum`]'s own `sumRange_succ`.
fn declare_dot_n_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let lhs = rdot_n(d, p, u, v, sn);
    let prior = rdot_n(d, p, u, v, n);
    let un = d.apply(u, &[n]);
    let vn = d.apply(v, &[n]);
    let unvn = rmul(d, un, vn);
    let rhs = radd(d, prior, unvn);
    let stmt_inner = req(d, lhs, rhs);
    let proof_inner = rrefl(d, rhs);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let over_v = d.pi_fv(v_fv, fn_ty, inner);
        d.pi_fv(u_fv, fn_ty, over_v)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let over_v = d.lam_fv(v_fv, fn_ty, inner);
        d.lam_fv(u_fv, fn_ty, over_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_succ,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_comm : ∀ u v n, dotN u v n = dotN v u n`.
///
/// `dotN u v n` and `dotN v u n` are each defeq to a `sumRange` over the
/// pointwise-commuted summand, so a single [`super::RatPrelude::sum_range_congr`]
/// application at the pointwise proof `mul_comm` closes the goal directly —
/// no induction, mirroring how [`super::matrix`]'s row-vector algebra reuses
/// an existing law rather than re-deriving it.
fn declare_dot_n_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let lhs = rdot_n(d, p, u, v, n);
    let rhs = rdot_n(d, p, v, u, n);
    let stmt = req(d, lhs, rhs);

    let f = dot_summand(d, u, v);
    let g = dot_summand(d, v, u);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let body = d.lemma(p.mul_comm, &[ui, vi]); // u i * v i = v i * u i
        d.lam_fv(i_fv, nat, body)
    };
    let proof = d.lemma(p.sum_range_congr, &[f, g, n, pointwise]);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_v = d.pi_fv(v_fv, fn_ty, with_n);
        d.pi_fv(u_fv, fn_ty, with_v)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_v = d.lam_fv(v_fv, fn_ty, with_n);
        d.lam_fv(u_fv, fn_ty, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_comm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_add_left : ∀ u1 u2 v n,`
/// `dotN (fun i => u1 i + u2 i) v n = dotN u1 v n + dotN u2 v n`.
///
/// [`super::RatPrelude::right_distrib`] distributes the summand pointwise
/// (via `sumRange_congr`), then [`super::RatPrelude::sum_range_add`] splits
/// the sum — the same two-step shape `probability.rs`'s
/// `declare_expectation_add` uses for its own two-function definition.
fn declare_dot_n_add_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u1_fv = d.fresh_fvar();
    let u1 = d.kernel().fvar(u1_fv);
    let u2_fv = d.fresh_fvar();
    let u2 = d.kernel().fvar(u2_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined = combined_fn(d, u1, u2);
    let lhs = rdot_n(d, p, combined, v, n);
    let d1 = rdot_n(d, p, u1, v, n);
    let d2 = rdot_n(d, p, u2, v, n);
    let rhs = radd(d, d1, d2);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun i => (u1 i+u2 i)*v i) n = sumRange (fun i => u1 i*v i + u2 i*v i) n
    let combined_summand = dot_summand(d, combined, v);
    let target_summand = split_dot_summand(d, u1, u2, v);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let u1i = d.apply(u1, &[i]);
        let u2i = d.apply(u2, &[i]);
        let vi = d.apply(v, &[i]);
        let body = d.lemma(p.right_distrib, &[u1i, u2i, vi]); // (u1 i+u2 i)*v i = u1 i*v i+u2 i*v i
        d.lam_fv(i_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, target_summand, n, pointwise],
    );

    // sumRange (fun i => u1 i*v i + u2 i*v i) n = sumRange f1 n + sumRange f2 n
    let f1 = dot_summand(d, u1, v);
    let f2 = dot_summand(d, u2, v);
    let add_step = d.lemma(p.sum_range_add, &[f1, f2, n]);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let sum_target = rsum_range(d, p, target_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_target, congr_step), (rhs, add_step)],
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_v = d.pi_fv(v_fv, fn_ty, with_n);
        let with_u2 = d.pi_fv(u2_fv, fn_ty, with_v);
        d.pi_fv(u1_fv, fn_ty, with_u2)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_v = d.lam_fv(v_fv, fn_ty, with_n);
        let with_u2 = d.lam_fv(u2_fv, fn_ty, with_v);
        d.lam_fv(u1_fv, fn_ty, with_u2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_add_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_smul_left : ∀ a u v n,`
/// `dotN (fun i => a * u i) v n = a * dotN u v n`.
///
/// [`super::RatPrelude::mul_assoc`] regroups the summand pointwise, then
/// [`super::RatPrelude::mul_sum_range`] pulls the constant back out of the
/// sum — the same two-step shape `probability.rs`'s
/// `declare_expectation_smul` uses.
fn declare_dot_n_smul_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_u = scale_fn(d, a, u);
    let lhs = rdot_n(d, p, scaled_u, v, n);
    let du = rdot_n(d, p, u, v, n);
    let rhs = rmul(d, a, du);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun i => (a*u i)*v i) n = sumRange (fun i => a*(u i*v i)) n
    let combined_summand = dot_summand(d, scaled_u, v);
    let regrouped_summand = scale_dot_summand(d, a, u, v);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ui = d.apply(u, &[i]);
        let vi = d.apply(v, &[i]);
        let body = d.lemma(p.mul_assoc, &[a, ui, vi]); // (a*u i)*v i = a*(u i*v i)
        d.lam_fv(i_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, regrouped_summand, n, pointwise],
    );

    // sumRange (fun i => a*(u i*v i)) n = a * sumRange (fun i => u i*v i) n
    let f = dot_summand(d, u, v);
    let mul_step = d.lemma(p.mul_sum_range, &[a, f, n]); // a*sumRange f n = sumRange regrouped n
    let sum_f = rsum_range(d, p, f, n);
    let a_sum_f = rmul(d, a, sum_f);
    let sum_regrouped = rsum_range(d, p, regrouped_summand, n);
    let mul_step_rev = super::ops::rsymm(d, a_sum_f, sum_regrouped, mul_step);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_regrouped, congr_step), (a_sum_f, mul_step_rev)],
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_v = d.pi_fv(v_fv, fn_ty, with_n);
        let with_u = d.pi_fv(u_fv, fn_ty, with_v);
        d.pi_fv(a_fv, carrier, with_u)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_v = d.lam_fv(v_fv, fn_ty, with_n);
        let with_u = d.lam_fv(u_fv, fn_ty, with_v);
        d.lam_fv(a_fv, carrier, with_u)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_smul_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_self_nonneg : ∀ v n, le zero (dotN v v n)`.
///
/// Every summand `v i * v i` is a square, nonnegative by
/// [`super::RatPrelude::sq_nonneg`] (already proved in `laws.rs`, nothing
/// new to land there); [`super::RatPrelude::sum_range_nonneg`] carries that
/// pointwise fact through the sum.
fn declare_dot_n_self_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dvv = rdot_n(d, p, v, v, n);
    let zero_r = rzero(d, p);
    let stmt = rle(d, p, zero_r, dvv);

    let f = dot_summand(d, v, v);
    let hyp = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, n);
        let h_fv = d.fresh_fvar();
        let vi = d.apply(v, &[i]);
        let body = d.lemma(p.sq_nonneg, &[vi]); // 0 ≤ v i * v i
        let with_h = d.lam_fv(h_fv, hi_ty, body);
        d.lam_fv(i_fv, nat, with_h)
    };
    let proof = d.lemma(p.sum_range_nonneg, &[f, n, hyp]);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(v_fv, fn_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(v_fv, fn_ty, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_self_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.dotN_two : ∀ u v,`
/// `dotN u v (succ (succ zero)) = u zero * v zero + u (succ zero) * v (succ zero)`
/// — the n = 2 cross-check named in [`RatPrelude::dot_n_two`]'s own doc
/// comment. Two [`RatPrelude::dot_n_succ`] unfoldings, one
/// [`RatPrelude::dot_n_zero`], one [`RatPrelude::zero_add`]: `dotN`'s
/// general recursion, run down to a concrete dimension, produces exactly
/// the two-term sum `matrix.rs`'s own row/column products are built from by
/// hand (`row1a := a*e + b*g` in `det2_mul`'s proof), with no new algebra.
fn declare_dot_n_two(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    let u0 = d.apply(u, &[zero_n]);
    let v0 = d.apply(v, &[zero_n]);
    let u0v0 = rmul(d, u0, v0);
    let u1 = d.apply(u, &[one_n]);
    let v1 = d.apply(v, &[one_n]);
    let u1v1 = rmul(d, u1, v1);

    let lhs = rdot_n(d, p, u, v, two_n);
    let rhs = radd(d, u0v0, u1v1);
    let stmt = req(d, lhs, rhs);

    // dotN u v two = dotN u v one + u1*v1
    let dot_uv_one = rdot_n(d, p, u, v, one_n);
    let mid1 = radd(d, dot_uv_one, u1v1);
    let step1 = d.lemma(p.dot_n_succ, &[u, v, one_n]);

    // dotN u v one = dotN u v zero + u0*v0
    let dot_uv_zero = rdot_n(d, p, u, v, zero_n);
    let inner2 = radd(d, dot_uv_zero, u0v0);
    let mid2 = radd(d, inner2, u1v1);
    let succ_at_zero = d.lemma(p.dot_n_succ, &[u, v, zero_n]);
    let step2 = rcongr(d, dot_uv_one, inner2, succ_at_zero, &|d, t| {
        radd(d, t, u1v1)
    });

    // dotN u v zero = zero
    let zero_r = rzero(d, p);
    let inner3 = radd(d, zero_r, u0v0);
    let mid3 = radd(d, inner3, u1v1);
    let zero_step = d.lemma(p.dot_n_zero, &[u, v]);
    let step3 = rcongr(d, dot_uv_zero, zero_r, zero_step, &|d, t| {
        let inner = radd(d, t, u0v0);
        radd(d, inner, u1v1)
    });

    // zero + u0*v0 = u0*v0
    let za = d.lemma(p.zero_add, &[u0v0]);
    let step4 = rcongr(d, inner3, u0v0, za, &|d, t| radd(d, t, u1v1));

    let (_e, proof) = rchain(
        d,
        lhs,
        &[(mid1, step1), (mid2, step2), (mid3, step3), (rhs, step4)],
    );

    let ty = {
        let with_v = d.pi_fv(v_fv, fn_ty, stmt);
        d.pi_fv(u_fv, fn_ty, with_v)
    };
    let value = {
        let with_v = d.lam_fv(v_fv, fn_ty, proof);
        d.lam_fv(u_fv, fn_ty, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_two,
        uparams: vec![],
        ty,
        value,
    })
}

// === Cauchy–Schwarz (squared): (dotN u v n)^2 ≤ dotN u u n * dotN v v n ===
//
// The discriminant argument: for any concrete `t`, `0 ≤ dotN (t*u+v) (t*u+v)
// n` (`dotN_self_nonneg`), and bilinearity expands the left side into `((t*t)*A
// + t*B) + (t*B + C)` where `A := dotN u u n`, `B := dotN u v n`, `C := dotN v
// v n` — [`discriminant_at`] is exactly that fact, reusable at any `t`. `A ≥ 0`
// always ([`RatPrelude::dot_n_self_nonneg`]), so [`nonneg_trichotomy`] on `A`
// leaves two cases: `A > 0` ([`pos_case`], at the minimizer `t := -(B·A⁻¹)`)
// and `A = 0` (a second trichotomy on `C`: `C > 0` reduces to `pos_case` with
// `u`/`v` swapped, `C = 0` is [`zero_zero_case`] at `t := 1` and `t := -1`).
// The same three-case shape `probability.rs`'s own
// `covariance_sq_le_variance_mul` uses, unweighted — no `IsDistribution`.

/// `dotN (scale_fn t u) (scale_fn t u) n = (t*t) * (dotN u u n)`.
fn smul_diag(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    u: ExprId,
    n: ExprId,
    t: ExprId,
) -> (ExprId, ExprId) {
    let u1 = scale_fn(d, t, u);
    let start = rdot_n(d, p, u1, u1, n);
    let a_expr = rdot_n(d, p, u, u, n);

    let smul1 = d.lemma(p.dot_n_smul_left, &[t, u, u1, n]);
    let dot_u_u1 = rdot_n(d, p, u, u1, n);
    let mid1 = rmul(d, t, dot_u_u1);

    let comm = d.lemma(p.dot_n_comm, &[u, u1, n]);
    let dot_u1_u = rdot_n(d, p, u1, u, n);
    let mid2 = rmul(d, t, dot_u1_u);
    let step2 = rcongr(d, dot_u_u1, dot_u1_u, comm, &|d, x| rmul(d, t, x));

    let smul2 = d.lemma(p.dot_n_smul_left, &[t, u, u, n]);
    let t_a = rmul(d, t, a_expr);
    let mid3 = rmul(d, t, t_a);
    let step3 = rcongr(d, dot_u1_u, t_a, smul2, &|d, x| rmul(d, t, x));

    let tt = rmul(d, t, t);
    let target = rmul(d, tt, a_expr);
    let assoc_fwd = d.lemma(p.mul_assoc, &[t, t, a_expr]); // (t*t)*A = t*(t*A)
    let step4 = rsymm(d, target, mid3, assoc_fwd);

    let (_e, proof) = rchain(
        d,
        start,
        &[(mid1, smul1), (mid2, step2), (mid3, step3), (target, step4)],
    );
    (target, proof)
}

/// For any concrete `t`, `0 ≤ ((t*t)*A + t*B) + (t*B + C)`, where `A := dotN u
/// u n`, `B := dotN u v n`, `C := dotN v v n`. From `dotN_self_nonneg` at `w
/// := fun i => t*u i + v i` plus [`RatPrelude::dot_n_add_left`] /
/// [`RatPrelude::dot_n_comm`] / [`RatPrelude::dot_n_smul_left`] — no
/// induction, the same congr-then-split shape [`declare_dot_n_add_left`]
/// itself uses. Returns `(a_expr, b_expr, c_expr, q_expr, proof)`.
fn discriminant_at(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    u: ExprId,
    v: ExprId,
    n: ExprId,
    t: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let u1 = scale_fn(d, t, u);
    let w = combined_fn(d, u1, v);

    let nonneg = d.lemma(p.dot_n_self_nonneg, &[w, n]);
    let dot_w_w = rdot_n(d, p, w, w, n);

    // dotN w w n = dotN u1 w n + dotN v w n
    let eq1 = d.lemma(p.dot_n_add_left, &[u1, v, w, n]);
    let dot_u1_w = rdot_n(d, p, u1, w, n);
    let dot_v_w = rdot_n(d, p, v, w, n);
    let after1 = radd(d, dot_u1_w, dot_v_w);

    // dot_u1_w -> dotN u1 u1 n + dotN u1 v n
    let comm1 = d.lemma(p.dot_n_comm, &[u1, w, n]);
    let dot_w_u1 = rdot_n(d, p, w, u1, n);
    let eq2 = d.lemma(p.dot_n_add_left, &[u1, v, u1, n]);
    let dot_u1_u1 = rdot_n(d, p, u1, u1, n);
    let dot_v_u1 = rdot_n(d, p, v, u1, n);
    let mid_a = radd(d, dot_u1_u1, dot_v_u1);
    let comm2 = d.lemma(p.dot_n_comm, &[v, u1, n]);
    let dot_u1_v = rdot_n(d, p, u1, v, n);
    let final_a = radd(d, dot_u1_u1, dot_u1_v);
    let step_a = rcongr(d, dot_v_u1, dot_u1_v, comm2, &|d, x| radd(d, dot_u1_u1, x));
    let (_ea, dot_u1_w_expanded) = rchain(
        d,
        dot_u1_w,
        &[(dot_w_u1, comm1), (mid_a, eq2), (final_a, step_a)],
    );

    // dot_v_w -> dotN u1 v n + dotN v v n
    let comm3 = d.lemma(p.dot_n_comm, &[v, w, n]);
    let dot_w_v = rdot_n(d, p, w, v, n);
    let eq3 = d.lemma(p.dot_n_add_left, &[u1, v, v, n]);
    let cc = rdot_n(d, p, v, v, n);
    let final_b = radd(d, dot_u1_v, cc);
    let (_eb, dot_v_w_expanded) = rchain(d, dot_v_w, &[(dot_w_v, comm3), (final_b, eq3)]);

    let combine1 = rcongr(d, dot_u1_w, final_a, dot_u1_w_expanded, &|d, x| {
        radd(d, x, dot_v_w)
    });
    let mid_combine = radd(d, final_a, dot_v_w);
    let combine2 = rcongr(d, dot_v_w, final_b, dot_v_w_expanded, &|d, x| {
        radd(d, final_a, x)
    });
    let rhs_target = radd(d, final_a, final_b);

    let a_expr = rdot_n(d, p, u, u, n);
    let b_expr = rdot_n(d, p, u, v, n);
    let (x_target, x_proof) = smul_diag(d, p, u, n, t);
    let y_proof = d.lemma(p.dot_n_smul_left, &[t, u, v, n]); // dotN u1 v n = t*B
    let y_target = rmul(d, t, b_expr);

    let step_x = rcongr(d, dot_u1_u1, x_target, x_proof, &|d, w2| {
        let inner1 = radd(d, w2, dot_u1_v);
        let inner2 = radd(d, dot_u1_v, cc);
        radd(d, inner1, inner2)
    });
    let mid_simplify = {
        let inner1 = radd(d, x_target, dot_u1_v);
        let inner2 = radd(d, dot_u1_v, cc);
        radd(d, inner1, inner2)
    };
    let step_y = rcongr(d, dot_u1_v, y_target, y_proof, &|d, w2| {
        let inner1 = radd(d, x_target, w2);
        let inner2 = radd(d, w2, cc);
        radd(d, inner1, inner2)
    });
    let q_expr = {
        let inner1 = radd(d, x_target, y_target);
        let inner2 = radd(d, y_target, cc);
        radd(d, inner1, inner2)
    };

    let (_ec, full_proof) = rchain(
        d,
        dot_w_w,
        &[
            (after1, eq1),
            (mid_combine, combine1),
            (rhs_target, combine2),
            (mid_simplify, step_x),
            (q_expr, step_y),
        ],
    );

    let zero_r = rzero(d, p);
    let nonneg_q = rat_eq_rewrite(d, dot_w_w, q_expr, full_proof, nonneg, &|d, x| {
        rle(d, p, zero_r, x)
    });

    (a_expr, b_expr, cc, q_expr, nonneg_q)
}

/// From `h : 0 ≤ Rat.neg x`, derive `x ≤ 0`.
fn nonpos_of_nonneg_neg(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, h: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let neg_x = rneg(d, x);
    let le_refl_x = d.lemma(p.le_refl, &[x]);
    let raw = d.lemma(p.add_le_add, &[zero_r, neg_x, x, x, h, le_refl_x]);
    // raw : le (zero+x) (neg_x+x)
    let lhs0 = radd(d, zero_r, x);
    let rhs0 = radd(d, neg_x, x);
    let za = d.lemma(p.zero_add, &[x]);
    let step1 = rat_eq_rewrite(d, lhs0, x, za, raw, &|d, w| rle(d, p, w, rhs0));
    let nac = d.lemma(p.neg_add_cancel, &[x]); // neg_x+x = zero
    rat_eq_rewrite(d, rhs0, zero_r, nac, step1, &|d, w| rle(d, p, x, w))
}

/// From `hsum : x + x = 0` and `hnn : 0 ≤ x`, derive `x ≤ 0`.
fn nonpos_of_double_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    hsum: ExprId,
    hnn: ExprId,
) -> ExprId {
    let zero_r = rzero(d, p);
    let le_refl_x = d.lemma(p.le_refl, &[x]);
    let raw = d.lemma(p.add_le_add, &[zero_r, x, x, x, hnn, le_refl_x]);
    // raw : le (zero+x) (x+x)
    let lhs0 = radd(d, zero_r, x);
    let rhs0 = radd(d, x, x);
    let za = d.lemma(p.zero_add, &[x]);
    let step1 = rat_eq_rewrite(d, lhs0, x, za, raw, &|d, w| rle(d, p, w, rhs0));
    rat_eq_rewrite(d, rhs0, zero_r, hsum, step1, &|d, w| rle(d, p, x, w))
}

/// `Or (Eq Rat val zero) (Lt zero val)`, from `le zero val` — a local copy of
/// `probability.rs`'s own private `nonneg_trichotomy` (module-private there,
/// so not reusable across `rat_prelude` submodules).
fn nonneg_trichotomy(d: &mut IntDev<'_>, p: RatPrelude, val: ExprId, h_nonneg: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lt_val_zero = rlt(d, p, val, zero_r);
    let eq_val_zero = req(d, val, zero_r);
    let lt_zero_val = rlt(d, p, zero_r, val);
    let right_or = d.or(eq_val_zero, lt_zero_val);
    let trichotomy = d.lemma(p.lt_trichotomy, &[val, zero_r]);
    d.or_elim(
        lt_val_zero,
        right_or,
        right_or,
        trichotomy,
        &|d, h_neg| {
            let zero_lt_zero = d.lemma(p.lt_of_le_of_lt, &[zero_r, val, zero_r, h_nonneg, h_neg]);
            let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
            let false_proof = d.apply(irrefl, &[zero_lt_zero]);
            d.absurd(right_or, false_proof)
        },
        &|_d, h_rest| h_rest,
    )
}

/// `Rat.one * x = x`.
fn one_mul_eq(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let start = rmul(d, one_r, x);
    let comm = d.lemma(p.mul_comm, &[one_r, x]); // one*x = x*one
    let mid = rmul(d, x, one_r);
    let mo = d.lemma(p.mul_one, &[x]); // x*one = x
    let (_e, proof) = rchain(d, start, &[(mid, comm), (x, mo)]);
    proof
}

/// `(Rat.neg Rat.one) * x = Rat.neg x`.
fn neg_one_mul_eq(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let neg_one = rneg(d, one_r);
    let start = rmul(d, neg_one, x);
    let nm = d.lemma(p.neg_mul, &[one_r, x]); // (-one)*x = -(one*x)
    let one_x = rmul(d, one_r, x);
    let mid1 = rneg(d, one_x);
    let inner = one_mul_eq(d, p, x); // one*x = x
    let step2 = rcongr(d, one_x, x, inner, &|d, w| rneg(d, w));
    let target = rneg(d, x);
    let (_e, proof) = rchain(d, start, &[(mid1, nm), (target, step2)]);
    proof
}

/// Cauchy–Schwarz when `A := dotN u u n` is POSITIVE:
/// `(dotN u v n)*(dotN u v n) ≤ A * (dotN v v n)`. The discriminant argument
/// at `t := neg (mul (dotN u v n) (inv A))`, the minimizer: `t*A = -B`
/// ([`RatPrelude::mul_inv_cancel`] cancels `A * inv A`), which collapses
/// `discriminant_at`'s `(t*t)*A` term to `neg (t*B)` and its `q_expr` to
/// `t*B + C`; multiplying the resulting `0 ≤ t*B + C` by `A` (nonneg) and
/// simplifying `A*(t*B)` the same way gives `0 ≤ -(B*B) + A*C`.
fn pos_case(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    u: ExprId,
    v: ExprId,
    n: ExprId,
    ha_pos: ExprId,
) -> ExprId {
    let a_expr = rdot_n(d, p, u, u, n);
    let b_expr = rdot_n(d, p, u, v, n);
    let c_expr = rdot_n(d, p, v, v, n);
    let inv_a = d.const_app(p.inv, &[a_expr]);
    let ba = rmul(d, b_expr, inv_a);
    let t = rneg(d, ba);
    let zero_r = rzero(d, p);
    let one_r = rone(d, p);
    let neg_b = rneg(d, b_expr);

    // t*A = -B
    let ta_eq_negb = {
        let start = rmul(d, t, a_expr);
        let step1 = d.lemma(p.neg_mul, &[ba, a_expr]); // (-ba)*A = -(ba*A)
        let ba_a = rmul(d, ba, a_expr);
        let mid1 = rneg(d, ba_a);
        let assoc1 = d.lemma(p.mul_assoc, &[b_expr, inv_a, a_expr]); // (B*invA)*A = B*(invA*A)
        let inv_a_a = rmul(d, inv_a, a_expr);
        let b_inv_a_a = rmul(d, b_expr, inv_a_a);
        let mid2 = rneg(d, b_inv_a_a);
        let step2 = rcongr(d, ba_a, b_inv_a_a, assoc1, &|d, x| rneg(d, x));
        let comm1 = d.lemma(p.mul_comm, &[inv_a, a_expr]); // invA*A = A*invA
        let a_inv_a = rmul(d, a_expr, inv_a);
        let b_a_inv_a = rmul(d, b_expr, a_inv_a);
        let mid3 = rneg(d, b_a_inv_a);
        let step3 = rcongr(d, inv_a_a, a_inv_a, comm1, &|d, x| {
            let bx = rmul(d, b_expr, x);
            rneg(d, bx)
        });
        let cancel = d.lemma(p.mul_inv_cancel, &[a_expr, ha_pos]); // A*invA = 1
        let b_one = rmul(d, b_expr, one_r);
        let mid4 = rneg(d, b_one);
        let step4 = rcongr(d, a_inv_a, one_r, cancel, &|d, x| {
            let bx = rmul(d, b_expr, x);
            rneg(d, bx)
        });
        let mul_one_b = d.lemma(p.mul_one, &[b_expr]); // B*1 = B
        let target = rneg(d, b_expr);
        let step5 = rcongr(d, b_one, b_expr, mul_one_b, &|d, x| rneg(d, x));
        let (_e, proof) = rchain(
            d,
            start,
            &[
                (mid1, step1),
                (mid2, step2),
                (mid3, step3),
                (mid4, step4),
                (target, step5),
            ],
        );
        proof
    };

    // A*t = -B
    let at_eq_negb = {
        let comm = d.lemma(p.mul_comm, &[a_expr, t]); // A*t = t*A
        let at = rmul(d, a_expr, t);
        let ta = rmul(d, t, a_expr);
        rtrans(d, at, ta, neg_b, comm, ta_eq_negb)
    };

    let (_a2, _b2, _c2, q_expr, nonneg_q) = discriminant_at(d, p, u, v, n, t);

    let tt = rmul(d, t, t);
    let x_target = rmul(d, tt, a_expr);
    let y_target = rmul(d, t, b_expr);

    // x_target = neg(y_target)
    let x_eq_negy = {
        let assoc = d.lemma(p.mul_assoc, &[t, t, a_expr]); // (t*t)*A = t*(t*A)
        let t_a = rmul(d, t, a_expr);
        let mid1 = rmul(d, t, t_a);
        let step2 = rcongr(d, t_a, neg_b, ta_eq_negb, &|d, x| rmul(d, t, x));
        let t_negb = rmul(d, t, neg_b);
        let mul_neg_step = d.lemma(p.mul_neg, &[t, b_expr]); // t*(-B) = -(t*B)
        let target = rneg(d, y_target);
        let (_e, proof) = rchain(
            d,
            x_target,
            &[(mid1, assoc), (t_negb, step2), (target, mul_neg_step)],
        );
        proof
    };

    // q_expr -> y_target + c_expr
    let y_plus_c = radd(d, y_target, c_expr);
    let (final_q, q_eq_yc) = {
        let neg_y = rneg(d, y_target);
        let step_a = rcongr(d, x_target, neg_y, x_eq_negy, &|d, x| {
            let inner1 = radd(d, x, y_target);
            radd(d, inner1, y_plus_c)
        });
        let neg_y_plus_y = radd(d, neg_y, y_target);
        let mid1 = radd(d, neg_y_plus_y, y_plus_c);
        let nac = d.lemma(p.neg_add_cancel, &[y_target]); // -y+y = 0
        let step_b = rcongr(d, neg_y_plus_y, zero_r, nac, &|d, x| radd(d, x, y_plus_c));
        let mid2 = radd(d, zero_r, y_plus_c);
        let za = d.lemma(p.zero_add, &[y_plus_c]);
        let (_e, proof) = rchain(d, q_expr, &[(mid1, step_a), (mid2, step_b), (y_plus_c, za)]);
        (y_plus_c, proof)
    };

    // A*Y = -(B*B)
    let bb = rmul(d, b_expr, b_expr);
    let neg_bb = rneg(d, bb);
    let ay_eq_negbb = {
        let forward = d.lemma(p.mul_assoc, &[a_expr, t, b_expr]); // (A*t)*B = A*(t*B)
        let start = rmul(d, a_expr, y_target);
        let at = rmul(d, a_expr, t);
        let mid1 = rmul(d, at, b_expr);
        let assoc_rev = rsymm(d, mid1, start, forward);
        let step2 = rcongr(d, at, neg_b, at_eq_negb, &|d, x| rmul(d, x, b_expr));
        let mid2 = rmul(d, neg_b, b_expr);
        let neg_mul_step = d.lemma(p.neg_mul, &[b_expr, b_expr]); // (-B)*B = -(B*B)
        let (_e, proof) = rchain(
            d,
            start,
            &[(mid1, assoc_rev), (mid2, step2), (neg_bb, neg_mul_step)],
        );
        proof
    };

    // A*final_q = -(B*B) + A*C
    let ac = rmul(d, a_expr, c_expr);
    let a_finalq_eq_target = radd(d, neg_bb, ac);
    let a_finalq_eq = {
        let start = rmul(d, a_expr, final_q);
        let distrib = d.lemma(p.left_distrib, &[a_expr, y_target, c_expr]); // A*(Y+C)=A*Y+A*C
        let ay = rmul(d, a_expr, y_target);
        let mid1 = radd(d, ay, ac);
        let step2 = rcongr(d, ay, neg_bb, ay_eq_negbb, &|d, x| radd(d, x, ac));
        let (_e, proof) = rchain(d, start, &[(mid1, distrib), (a_finalq_eq_target, step2)]);
        proof
    };

    let aq = rmul(d, a_expr, q_expr);
    let a_finalq = rmul(d, a_expr, final_q);
    let aq_eq_afinalq = rcongr(d, q_expr, final_q, q_eq_yc, &|d, x| rmul(d, a_expr, x));
    let aq_eq_final = rtrans(
        d,
        aq,
        a_finalq,
        a_finalq_eq_target,
        aq_eq_afinalq,
        a_finalq_eq,
    );

    let ha_le = d.lemma(p.le_of_lt, &[zero_r, a_expr, ha_pos]);
    let raw_le = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[a_expr, zero_r, q_expr, ha_le, nonneg_q],
    ); // le (A*0) (A*q_expr)
    let mz = d.lemma(p.mul_zero, &[a_expr]); // A*0 = 0
    let a_zero = rmul(d, a_expr, zero_r);
    let le0_aq = rat_eq_rewrite(d, a_zero, zero_r, mz, raw_le, &|d, x| rle(d, p, x, aq));

    let h_final = rat_eq_rewrite(d, aq, a_finalq_eq_target, aq_eq_final, le0_aq, &|d, x| {
        rle(d, p, zero_r, x)
    });

    // B*B ≤ A*C
    let neg_bb_plus_ac = radd(d, neg_bb, ac);
    let le_refl_bb = d.lemma(p.le_refl, &[bb]);
    let raw2 = d.lemma(
        p.add_le_add,
        &[zero_r, neg_bb_plus_ac, bb, bb, h_final, le_refl_bb],
    ); // le (0+bb) ((-bb+ac)+bb)
    let lhs0 = radd(d, zero_r, bb);
    let rhs0 = radd(d, neg_bb_plus_ac, bb);
    let za = d.lemma(p.zero_add, &[bb]);
    let step1 = rat_eq_rewrite(d, lhs0, bb, za, raw2, &|d, x| rle(d, p, x, rhs0));

    let rhs_eq_ac = {
        let comm1 = d.lemma(p.add_comm, &[neg_bb, ac]); // -bb+ac = ac+-bb
        let ac_neg_bb = radd(d, ac, neg_bb);
        let mid1 = radd(d, ac_neg_bb, bb);
        let step_a = rcongr(d, neg_bb_plus_ac, ac_neg_bb, comm1, &|d, x| radd(d, x, bb));
        let assoc = d.lemma(p.add_assoc, &[ac, neg_bb, bb]); // (ac+-bb)+bb = ac+(-bb+bb)
        let neg_bb_plus_bb = radd(d, neg_bb, bb);
        let mid2 = radd(d, ac, neg_bb_plus_bb);
        let nac = d.lemma(p.neg_add_cancel, &[bb]); // -bb+bb=0
        let mid3 = radd(d, ac, zero_r);
        let step_c = rcongr(d, neg_bb_plus_bb, zero_r, nac, &|d, x| radd(d, ac, x));
        let az = d.lemma(p.add_zero, &[ac]);
        let (_e, proof) = rchain(
            d,
            rhs0,
            &[(mid1, step_a), (mid2, assoc), (mid3, step_c), (ac, az)],
        );
        proof
    };

    rat_eq_rewrite(d, rhs0, ac, rhs_eq_ac, step1, &|d, x| rle(d, p, bb, x))
}

/// Cauchy–Schwarz when `A := dotN u u n` and `C := dotN v v n` are both
/// ZERO. `discriminant_at` at `t := one` and `t := neg one` gives `0 ≤ B+B`
/// and `0 ≤ neg(B)+neg(B)`; [`RatPrelude::neg_add`] plus
/// [`nonpos_of_nonneg_neg`] turns the second into `B+B ≤ 0`, and
/// [`RatPrelude::le_antisymm`] against the first gives `B+B = 0` — no case
/// split on the sign of `B` itself. Multiplying `B+B=0` by `B` gives
/// `B*B+B*B = 0`, and [`nonpos_of_double_zero`] (with
/// [`RatPrelude::sq_nonneg`]) closes `B*B ≤ 0 = A*C`.
fn zero_zero_case(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    u: ExprId,
    v: ExprId,
    n: ExprId,
    ha0: ExprId,
    hc0: ExprId,
) -> ExprId {
    let a_expr = rdot_n(d, p, u, u, n);
    let b_expr = rdot_n(d, p, u, v, n);
    let c_expr = rdot_n(d, p, v, v, n);
    let zero_r = rzero(d, p);
    let one_r = rone(d, p);
    let neg_one = rneg(d, one_r);

    // Reduce discriminant_at(t)'s q_expr to `y_val + y_val` given
    // `tt_eq_one : t*t = one` and `ty_eq : t*B = y_val`, `A = 0`, `C = 0`.
    let reduce = |d: &mut IntDev<'_>,
                  t: ExprId,
                  tt_eq_one: ExprId,
                  y_val: ExprId,
                  ty_eq: ExprId|
     -> ExprId {
        let (_a, _b, _c, q_expr, nonneg_q) = discriminant_at(d, p, u, v, n, t);
        let tt = rmul(d, t, t);
        let x_target = rmul(d, tt, a_expr);
        let y_target = rmul(d, t, b_expr);

        // x_target -> zero : (t*t)*A -> one*A -> A -> zero
        let x_eq_zero = {
            let step1 = rcongr(d, tt, one_r, tt_eq_one, &|d, x| rmul(d, x, a_expr));
            let mid1 = rmul(d, one_r, a_expr);
            let step2 = one_mul_eq(d, p, a_expr); // one*A = A
            let (_e, proof) = rchain(
                d,
                x_target,
                &[(mid1, step1), (a_expr, step2), (zero_r, ha0)],
            );
            proof
        };

        let y_plus_c = radd(d, y_target, c_expr);
        let step_x = rcongr(d, x_target, zero_r, x_eq_zero, &|d, w| {
            let inner1 = radd(d, w, y_target);
            radd(d, inner1, y_plus_c)
        });
        let mid_s1 = {
            let inner1 = radd(d, zero_r, y_target);
            radd(d, inner1, y_plus_c)
        };
        let y_val_plus_c = radd(d, y_val, c_expr);
        let step_y = rcongr(d, y_target, y_val, ty_eq, &|d, w| {
            let inner1 = radd(d, zero_r, w);
            let inner2 = radd(d, w, c_expr);
            radd(d, inner1, inner2)
        });
        let mid_s2 = {
            let inner1 = radd(d, zero_r, y_val);
            radd(d, inner1, y_val_plus_c)
        };
        let za = d.lemma(p.zero_add, &[y_val]);
        let zero_plus_yval = radd(d, zero_r, y_val);
        let step_za = rcongr(d, zero_plus_yval, y_val, za, &|d, w| {
            radd(d, w, y_val_plus_c)
        });
        let mid_s3 = radd(d, y_val, y_val_plus_c);
        let step_c = rcongr(d, c_expr, zero_r, hc0, &|d, w| {
            let inner = radd(d, y_val, w);
            radd(d, y_val, inner)
        });
        let y_val_plus_zero = radd(d, y_val, zero_r);
        let mid_s4 = radd(d, y_val, y_val_plus_zero);
        let az = d.lemma(p.add_zero, &[y_val]);
        let step_az = rcongr(d, y_val_plus_zero, y_val, az, &|d, w| radd(d, y_val, w));
        let target = radd(d, y_val, y_val);

        let (_e, full) = rchain(
            d,
            q_expr,
            &[
                (mid_s1, step_x),
                (mid_s2, step_y),
                (mid_s3, step_za),
                (mid_s4, step_c),
                (target, step_az),
            ],
        );
        rat_eq_rewrite(d, q_expr, target, full, nonneg_q, &|d, x| {
            rle(d, p, zero_r, x)
        })
    };

    // t := one : 0 ≤ B+B
    let one_sq = d.lemma(p.mul_one, &[one_r]); // one*one = one
    let one_b_eq = one_mul_eq(d, p, b_expr); // one*B = B
    let h_pos1 = reduce(d, one_r, one_sq, b_expr, one_b_eq);

    // t := neg one : 0 ≤ neg(B)+neg(B)
    let neg_one_sq = {
        let nme = neg_one_mul_eq(d, p, neg_one); // neg_one*neg_one = neg(neg_one)
        let nn = d.lemma(p.neg_neg, &[one_r]); // neg(neg(one)) = one
        let non = rmul(d, neg_one, neg_one);
        let neg_neg_one = rneg(d, neg_one);
        rtrans(d, non, neg_neg_one, one_r, nme, nn)
    };
    let neg_b = rneg(d, b_expr);
    let neg_one_b_eq = neg_one_mul_eq(d, p, b_expr); // neg_one*B = neg(B)
    let h_pos2 = reduce(d, neg_one, neg_one_sq, neg_b, neg_one_b_eq);

    // B+B = 0
    let bb_sum = radd(d, b_expr, b_expr);
    let neg_bb_sum = rneg(d, bb_sum);
    let neg_b_plus_neg_b = radd(d, neg_b, neg_b);
    let neg_add_symm = {
        let forward = d.lemma(p.neg_add, &[b_expr, b_expr]); // neg(B+B) = neg(B)+neg(B)
        rsymm(d, neg_bb_sum, neg_b_plus_neg_b, forward)
    };
    let h_pos2_rewritten = rat_eq_rewrite(
        d,
        neg_b_plus_neg_b,
        neg_bb_sum,
        neg_add_symm,
        h_pos2,
        &|d, x| rle(d, p, zero_r, x),
    );
    let bb_sum_le0 = nonpos_of_nonneg_neg(d, p, bb_sum, h_pos2_rewritten);
    let bb_sum_zero = d.lemma(p.le_antisymm, &[bb_sum, zero_r, bb_sum_le0, h_pos1]);

    // B*B + B*B = 0
    let bb = rmul(d, b_expr, b_expr);
    let bb_double = {
        let start = radd(d, bb, bb);
        let ld = d.lemma(p.left_distrib, &[b_expr, b_expr, b_expr]); // B*(B+B) = B*B+B*B
        let mid1 = rmul(d, b_expr, bb_sum);
        let ld_rev = rsymm(d, mid1, start, ld);
        let congr_step = rcongr(d, bb_sum, zero_r, bb_sum_zero, &|d, x| rmul(d, b_expr, x));
        let mid2 = rmul(d, b_expr, zero_r);
        let mz = d.lemma(p.mul_zero, &[b_expr]);
        let (_e, proof) = rchain(
            d,
            start,
            &[(mid1, ld_rev), (mid2, congr_step), (zero_r, mz)],
        );
        proof
    };

    let hnn = d.lemma(p.sq_nonneg, &[b_expr]);
    let bb_le0 = nonpos_of_double_zero(d, p, bb, bb_double, hnn);

    // A*C = 0
    let ac = rmul(d, a_expr, c_expr);
    let ac_eq_zero = {
        let step1 = rcongr(d, a_expr, zero_r, ha0, &|d, x| rmul(d, x, c_expr));
        let mid1 = rmul(d, zero_r, c_expr);
        let step2 = rcongr(d, c_expr, zero_r, hc0, &|d, x| rmul(d, zero_r, x));
        let mid2 = rmul(d, zero_r, zero_r);
        let mz = d.lemma(p.mul_zero, &[zero_r]); // zero*zero = zero
        let (_e, proof) = rchain(d, ac, &[(mid1, step1), (mid2, step2), (zero_r, mz)]);
        proof
    };
    let ac_eq_zero_symm = rsymm(d, ac, zero_r, ac_eq_zero);

    rat_eq_rewrite(d, zero_r, ac, ac_eq_zero_symm, bb_le0, &|d, x| {
        rle(d, p, bb, x)
    })
}

/// `Rat.dotN_cauchy_schwarz : ∀ u v n,`
/// `(dotN u v n)*(dotN u v n) ≤ (dotN u u n)*(dotN v v n)` — see
/// [`RatPrelude::dot_n_cauchy_schwarz`] for the full case breakdown.
fn declare_dot_n_cauchy_schwarz(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a_expr = rdot_n(d, p, u, u, n);
    let b_expr = rdot_n(d, p, u, v, n);
    let c_expr = rdot_n(d, p, v, v, n);
    let bb = rmul(d, b_expr, b_expr);
    let ac = rmul(d, a_expr, c_expr);
    let stmt = rle(d, p, bb, ac);

    let ha_nonneg = d.lemma(p.dot_n_self_nonneg, &[u, n]);
    let hc_nonneg = d.lemma(p.dot_n_self_nonneg, &[v, n]);
    let a_choice = nonneg_trichotomy(d, p, a_expr, ha_nonneg);

    let zero_r = rzero(d, p);
    let eq_a_zero = req(d, a_expr, zero_r);
    let lt_zero_a = rlt(d, p, zero_r, a_expr);

    let proof = d.or_elim(
        eq_a_zero,
        lt_zero_a,
        stmt,
        a_choice,
        &|d, ha0| {
            let c_choice = nonneg_trichotomy(d, p, c_expr, hc_nonneg);
            let eq_c_zero = req(d, c_expr, zero_r);
            let lt_zero_c = rlt(d, p, zero_r, c_expr);
            d.or_elim(
                eq_c_zero,
                lt_zero_c,
                stmt,
                c_choice,
                &|d, hc0| zero_zero_case(d, p, u, v, n, ha0, hc0),
                &|d, hc_pos| {
                    let swapped = pos_case(d, p, v, u, n, hc_pos); // le (B'*B') (C*A)
                    let b_prime = rdot_n(d, p, v, u, n);
                    let comm_b = d.lemma(p.dot_n_comm, &[u, v, n]); // B = B'
                    let b_prime_eq_b = rsymm(d, b_expr, b_prime, comm_b); // B' = B
                    let ca = rmul(d, c_expr, a_expr);
                    let step1 =
                        rat_eq_rewrite(d, b_prime, b_expr, b_prime_eq_b, swapped, &|d, x| {
                            let xx = rmul(d, x, x);
                            rle(d, p, xx, ca)
                        });
                    let comm_ac = d.lemma(p.mul_comm, &[c_expr, a_expr]); // C*A = A*C
                    rat_eq_rewrite(d, ca, ac, comm_ac, step1, &|d, x| rle(d, p, bb, x))
                },
            )
        },
        &|d, ha_pos| pos_case(d, p, u, v, n, ha_pos),
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_v = d.pi_fv(v_fv, fn_ty, with_n);
        d.pi_fv(u_fv, fn_ty, with_v)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_v = d.lam_fv(v_fv, fn_ty, with_n);
        d.lam_fv(u_fv, fn_ty, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_n_cauchy_schwarz,
        uparams: vec![],
        ty,
        value,
    })
}
