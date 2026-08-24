//! `Rat.sumRange` — finite sums over `ℚ` — and the algebra a probability
//! statement needs from it.
//!
//! Mirrors [`NatPrelude::sum_range`](crate::nat_prelude::NatPrelude::sum_range)'s
//! own convention exactly (`nat_prelude/defs.rs::declare_finite_ranges`, and
//! its algebra in `nat_prelude/algebra.rs` /
//! `nat_prelude/binomial.rs::declare_sum_range_congr_lt`), the way
//! [`crate::complex`]'s `Complex.sumRange` already does for a carrier that,
//! like `Rat`, has no definitional ring laws: exclusive bound, `sumRange f
//! zero ≡ zero`, `sumRange f (succ n) ≡ add (sumRange f n) (f n)` — the new
//! term folded on the RIGHT of the prior sum.
//!
//! `sumRange_congr` and `sumRange_add`/`mul_sumRange` are the unrestricted
//! (`∀ i, …`) forms, exactly `Nat`'s own `sum_range_congr` /
//! `sum_range_add` / `mul_sumRange`. `sumRange_le` is the **bounded**
//! (`∀ i, Lt i n → …`) form, mirroring `Nat.sumRange_congr_lt`'s own proof
//! shape with the two `Eq` congruences on the successor step replaced by one
//! `Rat.add_le_add`. `sumRange_nonneg` is proved directly by the same
//! induction rather than derived from `sumRange_le` against the zero
//! function, since the direct route needs one lemma (`Rat.add_nonneg`)
//! instead of two.

use super::RatPrelude;
use super::ops::{radd, rat_ty, rchain, rcongr, req, rle, rrefl, rsum_range, rzero};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.sumRange`: above every constant it calls
/// (`Rat.add` at `int_prelude`'s `DERIVED_HEIGHT` = 21, `Rat.zero` at
/// `rat_prelude::defs::LEAF_HEIGHT` = 30) and above every other height
/// declared in this prelude so far (`Rat.abs`/`Rat.ble`/`natDivSucc_*` at 33).
const SUM_HEIGHT: u16 = 34;

/// Declare `Rat.sumRange` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sum(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_sum_range(d, p)?;
    declare_sum_range_equations(d, p)?;
    declare_sum_range_congr(d, p)?;
    declare_sum_range_add(d, p)?;
    declare_mul_sum_range(d, p)?;
    declare_sum_range_le(d, p)?;
    declare_sum_range_nonneg(d, p)?;
    declare_sum_range_congr_lt(d, p)?;
    declare_sum_range_eq_zero_of_lt(d, p)?;
    Ok(())
}

/// `Rat.sumRange : (Nat → Rat) → Nat → Rat`, structural `Nat.rec` on the
/// bound: `sumRange f zero ≡ Rat.zero`, `sumRange f (succ j) ≡ Rat.add
/// (sumRange f j) (f j)`.
fn declare_sum_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rzero(d, p);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = radd(d, ih, fj);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_HEIGHT),
    })
}

/// `Rat.sumRange_zero`/`Rat.sumRange_succ`: the defining equations, each
/// closed by `Eq.refl` alone since `sumRange`'s `Nat.rec` application
/// ι-reduces on both minor premises.
fn declare_sum_range_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_zero : ∀ f, Eq Rat (sumRange f zero) zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = rsum_range(d, p, f, zero_n);
        let zero_r = rzero(d, p);
        let stmt = req(d, lhs, zero_r);
        let proof = rrefl(d, zero_r);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_succ : ∀ f (n : Nat),
    //   Eq Rat (sumRange f (succ n)) (add (sumRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = rsum_range(d, p, f, sn);
        let prior = rsum_range(d, p, f, n);
        let fj = d.apply(f, &[n]);
        let rhs = radd(d, prior, fj);
        let stmt_inner = req(d, lhs, rhs);
        let proof_inner = rrefl(d, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt_inner);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof_inner);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Rat.sumRange_congr : ∀ f g n, (∀ i, Eq Rat (f i) (g i)) → Eq Rat
/// (sumRange f n) (sumRange g n)` — pointwise equality gives equality of the
/// sums. `funext` is not available (and would not help even if it were: the
/// two `sumRange` VALUES need to be shown equal, not the two functions), so
/// this is a genuine induction on `n`, mirroring `Nat.sumRange_congr`
/// (`nat_prelude/algebra.rs::declare_finite_sum_theorems`) exactly.
fn declare_sum_range_congr(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let eq = req(d, fi, gi);
        d.pi_fv(i_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rsum_range(d, p, f, x);
        let rhs = rsum_range(d, p, g, x);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = rzero(d, p);
            rrefl(d, zero)
        },
        &|d, j, ih| {
            let f_prior = rsum_range(d, p, f, j);
            let g_prior = rsum_range(d, p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = radd(d, f_prior, fj);
            let mid = radd(d, g_prior, fj);
            let h1 = rcongr(d, f_prior, g_prior, ih, &|d, t| radd(d, t, fj));
            let end = radd(d, g_prior, gj);
            let pointwise_j = d.apply(h, &[j]);
            let h2 = rcongr(d, fj, gj, pointwise_j, &|d, t| radd(d, g_prior, t));
            let (_e, proof) = rchain(d, start, &[(mid, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_congr, ty, value)
}

/// `(A+B)+(C+D) = (A+C)+(B+D)` over `Rat`, returned as a `(target, proof)`
/// chain step. A local copy of `Nat`'s own `add_add_add_comm`
/// (`nat_prelude/binomial.rs`) with `Rat.add_assoc`/`Rat.add_comm` in place of
/// the `Nat` laws — kept private since only [`declare_sum_range_add`] needs
/// it.
fn radd_add_add_comm(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let cd = radd(d, c, dd);
    let bd = radd(d, b, dd);
    let ab = radd(d, a, b);
    let start = radd(d, ab, cd);

    // start = a + (b + (c+d))
    let bcd = radd(d, b, cd);
    let s1 = radd(d, a, bcd);
    let h1 = d.lemma(p.add_assoc, &[a, b, cd]);

    // b+(c+d) -> (b+c)+d
    let bc = radd(d, b, c);
    let bc_d = radd(d, bc, dd);
    let s2 = radd(d, a, bc_d);
    let h_bcd = d.lemma(p.add_assoc, &[b, c, dd]); // (b+c)+d = b+(c+d)
    let h2_inner = rsymm_local(d, bc_d, bcd, h_bcd);
    let h2 = rcongr(d, bcd, bc_d, h2_inner, &|d, t| radd(d, a, t));

    // (b+c) -> (c+b)
    let cb = radd(d, c, b);
    let cb_d = radd(d, cb, dd);
    let s3 = radd(d, a, cb_d);
    let h_comm = d.lemma(p.add_comm, &[b, c]);
    let h3 = rcongr(d, bc, cb, h_comm, &|d, t| {
        let td = radd(d, t, dd);
        radd(d, a, td)
    });

    // (c+b)+d -> c+(b+d)
    let c_bd = radd(d, c, bd);
    let s4 = radd(d, a, c_bd);
    let h_assoc2 = d.lemma(p.add_assoc, &[c, b, dd]);
    let h4 = rcongr(d, cb_d, c_bd, h_assoc2, &|d, t| radd(d, a, t));

    // a+(c+(b+d)) -> (a+c)+(b+d)
    let ac = radd(d, a, c);
    let target = radd(d, ac, bd);
    let a_c_bd = radd(d, a, c_bd);
    let h_assoc3 = d.lemma(p.add_assoc, &[a, c, bd]); // (a+c)+(b+d) = a+(c+(b+d))
    let h5 = rsymm_local(d, target, a_c_bd, h_assoc3);

    let (_e, proof) = rchain(
        d,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (target, h5)],
    );
    (target, proof)
}

/// `super::ops::rsymm`, spelled out under a local name so this file reads the
/// same as its `Nat` template (`d.symm`) at every call site.
fn rsymm_local(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    super::ops::rsymm(d, a, b, h)
}

/// `Rat.sumRange_add : ∀ f g n, Eq Rat (sumRange (fun i => f i + g i) n)
/// (sumRange f n + sumRange g n)`.
///
/// Mirrors `Nat.sumRange_add`'s own proof shape
/// (`nat_prelude/binomial.rs::declare_sum_range_add`): the successor case
/// needs [`radd_add_add_comm`] since the induction hypothesis rewrites the
/// *inner* pair while `sumRange_succ` produces the *outer* one.
fn declare_sum_range_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut IntDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = radd(d, fi, gi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = rsum_range(d, p, combined, x);
        let sf = rsum_range(d, p, f, x);
        let sg = rsum_range(d, p, g, x);
        let rhs = radd(d, sf, sg);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = rzero(d, p);
            rrefl(d, zero)
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let combined_j = d.apply(combined, &[j]);
            let prior_combined = rsum_range(d, p, combined, j);
            let start = radd(d, prior_combined, combined_j);

            let sf_j = rsum_range(d, p, f, j);
            let sg_j = rsum_range(d, p, g, j);
            let sfg = radd(d, sf_j, sg_j);
            let h1 = rcongr(d, prior_combined, sfg, ih, &|d, t| radd(d, t, combined_j));
            let after_ih = radd(d, sfg, combined_j);

            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fg_j = radd(d, fj, gj);
            let h_bridge = rrefl(d, fg_j); // combined_j ≡ fg_j by beta
            let after_bridge = radd(d, sfg, fg_j);
            let h2 = rcongr(d, combined_j, fg_j, h_bridge, &|d, t| radd(d, sfg, t));

            let end = radd_add_add_comm(d, p, sf_j, sg_j, fj, gj);
            let (_e, proof) = rchain(d, start, &[(after_ih, h1), (after_bridge, h2), end]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_add, ty, value)
}

/// `Rat.mul_sumRange : ∀ c f n, Eq Rat (c * sumRange f n) (sumRange (fun i =>
/// c * f i) n)` — a constant distributes through a finite sum.
///
/// Mirrors `Nat.mul_sumRange` (`nat_prelude/algebra.rs`), with `Rat.mul_zero`
/// standing in for `Nat`'s definitional `mul a zero ≡ zero` in the base case:
/// `Rat.mul` renormalises, so that step is a **law**, not `Eq.refl` — exactly
/// [`crate::complex`]'s own `Complex.mul_sumRange`.
fn declare_mul_sum_range(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = super::ops::rmul(d, c, fi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs_sum = rsum_range(d, p, f, x);
        let lhs = super::ops::rmul(d, c, lhs_sum);
        let scaled = scaled_fn(d);
        let rhs = rsum_range(d, p, scaled, x);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| d.lemma(p.mul_zero, &[c]),
        &|d, j, ih| {
            let prior = rsum_range(d, p, f, j);
            let fj = d.apply(f, &[j]);
            let extended = radd(d, prior, fj);
            let start = super::ops::rmul(d, c, extended);

            let c_prior = super::ops::rmul(d, c, prior);
            let c_fj = super::ops::rmul(d, c, fj);
            let distributed = radd(d, c_prior, c_fj);
            let h1 = d.lemma(p.left_distrib, &[c, prior, fj]);

            let scaled = scaled_fn(d);
            let scaled_prior = rsum_range(d, p, scaled, j);
            let end = radd(d, scaled_prior, c_fj);
            let h2 = rcongr(d, c_prior, scaled_prior, ih, &|d, t| radd(d, t, c_fj));

            let (_e, proof) = rchain(d, start, &[(distributed, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(c_fv, carrier, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(c_fv, carrier, over_f)
    };
    d.declare_theorem(p.mul_sum_range, ty, value)
}

/// `∀ i, Lt i bound → Rat.le (f i) (g i)`.
pub(crate) fn bounded_pointwise_le(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    g: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let le = rle(d, p, fi, gi);
    let body = d.arrow(hyp, le);
    d.pi_fv(i_fv, nat, body)
}

/// `∀ i, Lt i bound → Rat.le Rat.zero (f i)`.
pub(crate) fn bounded_nonneg(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let zero_r = rzero(d, p);
    let nonneg = rle(d, p, zero_r, fi);
    let body = d.arrow(hyp, nonneg);
    d.pi_fv(i_fv, nat, body)
}

/// `Rat.sumRange_le : ∀ f g n, (∀ i, Lt i n → Rat.le (f i) (g i)) → Rat.le
/// (sumRange f n) (sumRange g n)` — **monotonicity**, the fact every
/// probability bound in this file is built from.
///
/// Mirrors `Nat.sumRange_congr_lt`'s bounded-hypothesis induction
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`) with the two `Eq`
/// congruences on the successor step replaced by one `Rat.add_le_add`.
fn declare_sum_range_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise_le(d, p, f, g, x);
        let lhs = rsum_range(d, p, f, x);
        let rhs = rsum_range(d, p, g, x);
        let concl = rle(d, p, lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_pointwise_le(d, p, f, g, zero_n);
            let h_fv = d.fresh_fvar();
            let zero_r = rzero(d, p);
            let body = d.lemma(p.le_refl, &[zero_r]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise_le(d, p, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = rsum_range(d, p, f, j);
            let g_prior = rsum_range(d, p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = d.lemma(p.add_le_add, &[f_prior, g_prior, fj, gj, sub1, sub2]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_le, ty, value)
}

/// `Rat.sumRange_nonneg : ∀ f n, (∀ i, Lt i n → Rat.le Rat.zero (f i)) →
/// Rat.le Rat.zero (sumRange f n)`.
///
/// Direct induction on `n`, the same shape as [`declare_sum_range_le`] with
/// `Rat.add_nonneg` in place of `Rat.add_le_add` — proved directly rather
/// than derived from `sumRange_le` against the zero function, since the
/// direct route needs one law instead of two.
fn declare_sum_range_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_nonneg(d, p, f, x);
        let sum = rsum_range(d, p, f, x);
        let zero_r = rzero(d, p);
        let concl = rle(d, p, zero_r, sum);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_nonneg(d, p, f, zero_n);
            let h_fv = d.fresh_fvar();
            let zero_r = rzero(d, p);
            let body = d.lemma(p.le_refl, &[zero_r]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_nonneg(d, p, f, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = rsum_range(d, p, f, j);
            let fj = d.apply(f, &[j]);
            let body = d.lemma(p.add_nonneg, &[f_prior, fj, sub1, sub2]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.sum_range_nonneg, ty, value)
}

/// `fun i => Lt i bound -> Eq Rat (f i) (g i)`.
fn bounded_pointwise_eq(d: &mut IntDev<'_>, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqn = req(d, fi, gi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `Rat.sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → Eq Rat (f i) (g i)) → Eq
/// Rat (sumRange f n) (sumRange g n)` — [`declare_sum_range_congr`]'s
/// UNRESTRICTED pointwise congruence, weakened to indices below the bound —
/// what a sum whose summand identity holds only on a bounded range (e.g. a
/// zero fact a `PairwiseUncorrelated`-style hypothesis supplies only for `i ≠
/// j`, never universally) can actually provide. Missing from ℚ's own sum
/// development even though `Nat`/`Complex` both have it
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`,
/// `complex::declare_sum_range_congr_lt`) — this repairs that gap, a
/// general-purpose one, not a single call site's one-off.
///
/// Mirrors [`declare_sum_range_le`]'s bounded-hypothesis induction shape with
/// the closing `Rat.add_le_add` step replaced by two `Eq` congruences
/// (`rcongr`/`rchain`), exactly [`declare_sum_range_congr`]'s own successor
/// step.
fn declare_sum_range_congr_lt(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise_eq(d, f, g, x);
        let lhs = rsum_range(d, p, f, x);
        let rhs = rsum_range(d, p, g, x);
        let concl = req(d, lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_pointwise_eq(d, f, g, zero_n);
            let h_fv = d.fresh_fvar();
            let zero_r = rzero(d, p);
            let body = rrefl(d, zero_r);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise_eq(d, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = rsum_range(d, p, f, j);
            let g_prior = rsum_range(d, p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = radd(d, f_prior, fj);
            let mid = radd(d, g_prior, fj);
            let h1 = rcongr(d, f_prior, g_prior, sub1, &|d, t| radd(d, t, fj));
            let end = radd(d, g_prior, gj);
            let h2 = rcongr(d, fj, gj, sub2, &|d, t| radd(d, g_prior, t));
            let (_e, chain) = rchain(d, start, &[(mid, h1), (end, h2)]);
            d.lam_fv(h_fv, hyp_ty, chain)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_congr_lt, ty, value)
}

/// `fun i => Lt i bound -> Eq Rat (f i) Rat.zero`.
fn bounded_eq_zero(d: &mut IntDev<'_>, p: RatPrelude, f: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let zero_r = rzero(d, p);
    let eqn = req(d, fi, zero_r);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `Rat.sumRange_eq_zero_of_lt : ∀ f n, (∀ i, Lt i n → Eq Rat (f i) Rat.zero)
/// → Eq Rat (sumRange f n) Rat.zero` — "a sum of pointwise, bounded-below-`n`
/// zeros is zero". The bounded fact
/// [`super::probability::declare_covariance_sum_vars_left`]'s own successor
/// step (via [`super::probability`]'s `variance_sumVars` route) needs and
/// [`RatPrelude::sum_range_congr`] alone cannot give: that one wants an
/// UNRESTRICTED `∀i, f i = g i`, while `PairwiseUncorrelated` only ever
/// supplies zero facts bounded by the range, never universally.
///
/// Same bounded-hypothesis induction shape as [`declare_sum_range_congr_lt`],
/// nested directly here rather than derived from it (so this needs no
/// auxiliary "sum of the literal-zero function is zero" side lemma): the
/// successor step's two `Eq` congruences collapse `sumRange f j` via the
/// inductive hypothesis and `f j` via the hypothesis applied at `j`, then
/// [`RatPrelude::zero_add`] closes `zero + zero = zero`.
fn declare_sum_range_eq_zero_of_lt(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_eq_zero(d, p, f, x);
        let lhs = rsum_range(d, p, f, x);
        let zero_r = rzero(d, p);
        let concl = req(d, lhs, zero_r);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_eq_zero(d, p, f, zero_n);
            let h_fv = d.fresh_fvar();
            let zero_r = rzero(d, p);
            let body = rrefl(d, zero_r);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_eq_zero(d, p, f, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = rsum_range(d, p, f, j);
            let fj = d.apply(f, &[j]);
            let zero_r = rzero(d, p);
            let start = radd(d, f_prior, fj);
            let mid = radd(d, zero_r, fj);
            let h1 = rcongr(d, f_prior, zero_r, sub1, &|d, t| radd(d, t, fj));
            let after_h2 = radd(d, zero_r, zero_r);
            let h2 = rcongr(d, fj, zero_r, sub2, &|d, t| radd(d, zero_r, t));
            let z_add = d.lemma(p.zero_add, &[zero_r]);
            let (_e, chain) = rchain(d, start, &[(mid, h1), (after_h2, h2), (zero_r, z_add)]);
            d.lam_fv(h_fv, hyp_ty, chain)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.sum_range_eq_zero_of_lt, ty, value)
}
