//! **The symbolic-length telescope-with-uniform-bound lemmas.**
//!
//! `CReal.sumRange_telescope` (`series.rs`) already turns a sum of `k`
//! *consecutive differences* `f(i+1) − f i` into the single difference
//! `f k − f 0`, for an arbitrary `Nat` `k`. What a subdivision argument (a
//! Riemann sum, a mean-value-style estimate) needs on top of that is: if
//! *every one* of those `k` differences is bounded by a single constant —
//! the piece count `k` is **data**, not a fixed small numeral the way the
//! existing sum/product convenience rules use — then so is the telescoped
//! difference, against the constant summed `k` times.
//!
//! `CReal.sumRange_le` (`series.rs`) is already exactly that "promote a
//! pointwise bound to a bound on the finite sum" step, for an arbitrary `n`.
//! So both halves this file needs already exist; nothing here is new
//! mathematics, only the composition: apply `sumRange_le` to the
//! *difference* function against the *constant* function, then rewrite
//! whichever side is the difference-sum through `sumRange_telescope`. The
//! rewrite is `CReal.le_congr` (`Equiv` on each side of a `le`, not `Eq`,
//! since `CReal.Equiv` is the defined relation and nothing rewrites under it
//! for free).
//!
//! `CReal.sumRange (fun _ => bound) k` is left unevaluated — it is not
//! folded into `mul (ofNat k) bound` (no `CReal.sumRange_const` lemma exists
//! or is needed here). That expression, symbolic in `k`, **is** "a bound
//! comparable at an arbitrary target index": a caller who has chosen `k`
//! pieces each individually bounded by `bound` gets a bound on the whole
//! telescoped difference, without this file ever knowing what determined
//! `k`. Two directions are landed, since a subdivision argument's error
//! terms are two-sided and both compose identically:
//!
//! - [`declare_sum_range_telescope_le`]: an UPPER bound on each difference
//!   telescopes to an upper bound on the total (`f k − f 0 ≤ Σ_{i<k}
//!   bound`).
//! - [`declare_sum_range_telescope_ge`]: a LOWER bound on each difference
//!   telescopes to a lower bound on the total (`Σ_{i<k} bound ≤ f k − f 0`).
//!
//! The intended first consumer is `CReal.monotone_of_nonneg_deriv` (not yet
//! landed): each piece's difference is bounded below by `−(1/(e+1))·step`
//! (`HasDerivativeOn`'s spec plus the nonnegative-derivative hypothesis), so
//! [`declare_sum_range_telescope_ge`] with `bound := neg ((1/(e+1))·step)`
//! gives a lower bound on `F y − F x` for every accuracy `e`, and
//! `CReal.le_of_forall_le_add_small` (`archimedean_squeeze.rs`) closes that
//! down to `CReal.le` outright. That composition is not built here — it
//! needs `HasDerivativeOn` (`derivative.rs`) and a choice of piece count from
//! `CReal.bound` (`product.rs`) instantiated at each piece, both a
//! substantial further slice — but every piece landed in this file is
//! already independently reusable: the same shape is what a Riemann-sum
//! upper/lower bound and the Fundamental Theorem of Calculus need.

use super::{CRealPrelude, cadd, cle, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit `CReal.sumRange_telescope_ge` and `CReal.sumRange_telescope_le`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_monotone(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sum_range_telescope_ge(d, p)?;
    declare_sum_range_telescope_le(d, p)
}

// --- small local term builders ----------------------------------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// The step function `fun k => add (f (Nat.succ k)) (neg (f k))`, built
/// **identically** in shape to `series::declare_sum_range_telescope`'s own
/// (private) `step_fn`, so that `p.sum_range_le` and `p.sum_range_telescope`
/// below are applied to literally the same term (the single `ExprId` this
/// function returns is reused for both, rather than rebuilt twice).
fn diffs_fn(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let f_sk = d.apply(f, &[sk]);
    let f_k = d.apply(f, &[k]);
    let neg_fk = cneg(d, p, f_k);
    let body = cadd(d, p, f_sk, neg_fk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun _ : Nat => bound` — the constant function over `Nat`.
fn const_fn(d: &mut IntDev<'_>, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let fv = d.fresh_fvar();
    d.lam_fv(fv, nat, bound)
}

/// `∀ i, Nat.lt i n → le (f i) (g i)` — the pointwise hypothesis
/// `CReal.sumRange_le` takes, built identically to
/// `series::bounded_le_pointwise` (private to that module, so re-built here
/// rather than shared).
fn bounded_pointwise(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, n);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let leq = cle(d, p, fi, gi);
    let body = d.arrow(hyp, leq);
    d.pi_fv(i_fv, nat, body)
}

/// `CReal.sumRange_telescope_ge : ∀ f bound k,
/// (∀ i, Nat.lt i k → le bound (add (f (Nat.succ i)) (neg (f i)))) →
/// le (sumRange (fun _ => bound) k) (add (f k) (neg (f Nat.zero)))`.
///
/// Every piece's difference bounded *below* by a constant telescopes to a
/// lower bound on the total difference. `sumRange_le` applied to
/// `(const bound, diffs)` gives `le (sumRange (const bound) k) (sumRange
/// diffs k)`; `sumRange_telescope` rewrites the right side to `f k − f 0`
/// via `le_congr` (`Equiv` refl on the left, the telescope `Equiv` on the
/// right).
fn declare_sum_range_telescope_ge(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let bound_fv = d.fresh_fvar();
    let bound = d.kernel().fvar(bound_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let g = diffs_fn(d, p, f);
    let cbound = const_fn(d, bound);

    let hyp_ty = bounded_pointwise(d, p, cbound, g, k);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    // step1 : le (sumRange cbound k) (sumRange g k)
    let step1 = d.lemma(p.sum_range_le, &[cbound, g, k, hyp]);
    // step2 : Equiv (sumRange g k) (add (f k) (neg (f 0)))
    let step2 = d.lemma(p.sum_range_telescope, &[f, k]);

    let sum_cbound = d.const_app(p.sum_range, &[cbound, k]);
    let sum_g = d.const_app(p.sum_range, &[g, k]);
    let refl_lhs = d.lemma(p.equiv_refl, &[sum_cbound]);

    let zero_n = d.zero();
    let f0 = d.apply(f, &[zero_n]);
    let neg_f0 = cneg(d, p, f0);
    let fk = d.apply(f, &[k]);
    let target = cadd(d, p, fk, neg_f0);

    // le_congr : ∀ a b c e, Equiv a b → Equiv c e → le a c → le b e.
    // a = b = sum_cbound (refl), c = sum_g, e = target: le sum_cbound target.
    let value_body = d.lemma(
        p.le_congr,
        &[
            sum_cbound, sum_cbound, sum_g, target, refl_lhs, step2, step1,
        ],
    );

    let concl = cle(d, p, sum_cbound, target);
    let stmt = d.arrow(hyp_ty, concl);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, stmt);
        let over_bound = d.pi_fv(bound_fv, carrier, over_k);
        d.pi_fv(f_fv, fn_ty, over_bound)
    };
    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, value_body);
        let over_k = d.lam_fv(k_fv, nat, over_hyp);
        let over_bound = d.lam_fv(bound_fv, carrier, over_k);
        d.lam_fv(f_fv, fn_ty, over_bound)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_telescope_ge,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_telescope_le : ∀ f bound k,
/// (∀ i, Nat.lt i k → le (add (f (Nat.succ i)) (neg (f i))) bound) →
/// le (add (f k) (neg (f Nat.zero))) (sumRange (fun _ => bound) k)`.
///
/// The mirror of [`declare_sum_range_telescope_ge`]: every piece's
/// difference bounded *above* by a constant telescopes to an upper bound on
/// the total difference. `sumRange_le` applied to `(diffs, const bound)`
/// gives `le (sumRange diffs k) (sumRange (const bound) k)`; `le_congr`
/// rewrites the left side via `sumRange_telescope` instead of the right.
fn declare_sum_range_telescope_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let bound_fv = d.fresh_fvar();
    let bound = d.kernel().fvar(bound_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let g = diffs_fn(d, p, f);
    let cbound = const_fn(d, bound);

    let hyp_ty = bounded_pointwise(d, p, g, cbound, k);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    // step1 : le (sumRange g k) (sumRange cbound k)
    let step1 = d.lemma(p.sum_range_le, &[g, cbound, k, hyp]);
    // step2 : Equiv (sumRange g k) (add (f k) (neg (f 0)))
    let step2 = d.lemma(p.sum_range_telescope, &[f, k]);

    let sum_cbound = d.const_app(p.sum_range, &[cbound, k]);
    let sum_g = d.const_app(p.sum_range, &[g, k]);
    let refl_rhs = d.lemma(p.equiv_refl, &[sum_cbound]);

    let zero_n = d.zero();
    let f0 = d.apply(f, &[zero_n]);
    let neg_f0 = cneg(d, p, f0);
    let fk = d.apply(f, &[k]);
    let target = cadd(d, p, fk, neg_f0);

    // le_congr : ∀ a b c e, Equiv a b → Equiv c e → le a c → le b e.
    // a = sum_g, b = target, c = e = sum_cbound (refl): le target sum_cbound.
    let value_body = d.lemma(
        p.le_congr,
        &[
            sum_g, target, sum_cbound, sum_cbound, step2, refl_rhs, step1,
        ],
    );

    let concl = cle(d, p, target, sum_cbound);
    let stmt = d.arrow(hyp_ty, concl);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, stmt);
        let over_bound = d.pi_fv(bound_fv, carrier, over_k);
        d.pi_fv(f_fv, fn_ty, over_bound)
    };
    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, value_body);
        let over_k = d.lam_fv(k_fv, nat, over_hyp);
        let over_bound = d.lam_fv(bound_fv, carrier, over_k);
        d.lam_fv(f_fv, fn_ty, over_bound)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_telescope_le,
        uparams: vec![],
        ty,
        value,
    })
}
