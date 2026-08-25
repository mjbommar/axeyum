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

use super::{CRealPrelude, cadd, cle, creal_ty, div_succ, equiv};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::rzero;

/// Admit `CReal.sumRange_telescope_ge`, `CReal.sumRange_telescope_le`, and
/// `CReal.hasDerivative_closeOfEquiv`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_monotone(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sum_range_telescope_ge(d, p)?;
    declare_sum_range_telescope_le(d, p)?;
    declare_has_derivative_close_of_equiv(d, p)
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

// =============================================================================
// `CReal.hasDerivative_closeOfEquiv`
// =============================================================================
//
// The missing piece the two-lane handoff plan for `monotone_of_nonneg_deriv`
// did not name. That plan's step 1 builds interpolation points `x_i := x +
// ofNat i · step` between `x` and `y`, choosing the piece count `K` so the
// LAST point `x_K` lands on `y` — but `ofNat K · step ~ (y − x)` is a PROVED
// `Rat` identity (`Rat.natDivSucc_scale`), not a reduction, so `x_K` is only
// ever `Equiv` to `y`, never syntactically equal to it. Closing the
// telescoped derivative bound down to `F x ≤ F y` needs `F` to respect that
// `Equiv` on the two endpoints, and that is NOT free for an arbitrary
// `F : CReal → CReal` — only proven congruences (`mul_congr`, `neg_congr`, …)
// carry across `Equiv`, and `HasDerivativeOn`'s own hypothesis is stated for
// the SPECIFIC `x`, `y` a caller supplies, not up to `Equiv` on them.
//
// `hasDerivative_closeOfEquiv` supplies exactly that bridge, for any `F` that
// has a derivative on an interval containing both points: instantiate
// `HasDerivativeOn`'s spec at ANY fixed accuracy (`e := 0` suffices) with its
// own `x := u`, `y := v`. Since `u ~ v`, the piece width `v − u` is `Equiv`
// to `zero` OUTRIGHT (not merely small — no accuracy needs to be chosen to
// make it small), so the hypothesis `within_real (v−u) (ofRat (natDivSucc 1
// (modulus 0)))` is available from `close_zero_error` alone (`0 ≤ ofRat
// (…)` closes both sides against the FIXED bound `zero`), and the
// conclusion's own bound `(1/(0+1)) · |v−u|` collapses to `~ zero` the same
// way (`mul_le_mul_of_nonneg_left` against `zero`, then `mul_zero`). The
// error term `(F v − F u) − F'(u)·(v−u)` is therefore itself `Equiv zero`;
// `F'(u)·(v−u) ~ F'(u)·zero ~ zero` separately; and `F v − F u ~ zero` falls
// out of the two by `equiv_of_sub_equiv_zero`. No Archimedean closing is
// needed anywhere in this file, because the bound is already exactly `zero`
// regardless of which accuracy is chosen — unlike `monotone_of_nonneg_deriv`
// itself, whose OTHER telescoped pieces do not collapse this way and still
// need the full construction `archimedean_squeeze.rs`'s
// `le_of_forall_le_add_small` closes.
//
// This lemma is also independently useful: it is exactly "differentiable
// implies continuous", restricted to `Equiv`-related points inside the
// domain, and `derivative.rs`'s own module documentation names uniqueness of
// the derivative as a motivating future consumer of results in this shape.

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

/// `add x (neg y)` — `x - y`.
fn cdiff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    cadd(d, p, x, ny)
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development; rebuilt here rather than imported since
/// `derivative.rs`'s own copy is private to that module (a sibling of this
/// one, not an ancestor).
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (neg zero) zero` — the group identity `-0 = 0`. Duplicated from
/// `derivative.rs`'s private helper of the same shape.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = esymm(d, p, padded, nz, h1);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h : Equiv (add a (neg b)) zero`, derive `Equiv a b` — the general
/// "a difference `Equiv` to zero means the two sides are `Equiv`" bridge,
/// read off `(a + (−b)) + b` two ways: it is `Equiv a` (`add_assoc` +
/// `neg_add_self` + `add_zero`) and it is `Equiv b` (`add_congr` against `h`
/// + `add_comm` + `add_zero`).
fn equiv_of_sub_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let nb = cneg(d, p, b);
    let diff = cadd(d, p, a, nb);
    let lhs = cadd(d, p, diff, b);
    let zero_c = czero(d, p);

    let a_from_lhs = {
        let assoc = d.lemma(p.add_assoc, &[a, nb, b]);
        let nb_b = cadd(d, p, nb, b);
        let a_nbb = cadd(d, p, a, nb_b);
        let nas = neg_add_self(d, p, b);
        let refl_a = erefl(d, p, a);
        let cong = d.lemma(p.add_congr, &[a, a, nb_b, zero_c, refl_a, nas]);
        let a_zero = cadd(d, p, a, zero_c);
        let trim = d.lemma(p.add_zero, &[a]);
        echain(d, p, lhs, &[(a_nbb, assoc), (a_zero, cong), (a, trim)])
    };
    let b_from_lhs = {
        let refl_b = erefl(d, p, b);
        let cong = d.lemma(p.add_congr, &[diff, zero_c, b, b, h, refl_b]);
        let zero_b = cadd(d, p, zero_c, b);
        let comm = d.lemma(p.add_comm, &[zero_c, b]);
        let b_zero = cadd(d, p, b, zero_c);
        let trim = d.lemma(p.add_zero, &[b]);
        echain(d, p, lhs, &[(zero_b, cong), (b_zero, comm), (b, trim)])
    };
    let a_from_lhs_symm = esymm(d, p, lhs, a, a_from_lhs);
    d.lemma(p.equiv_trans, &[a, lhs, b, a_from_lhs_symm, b_from_lhs])
}

/// `Equiv (neg (neg x)) x`.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let nx_nnx = cadd(d, p, nx, nnx);
    let nnx_nx = cadd(d, p, nnx, nx);
    let comm = d.lemma(p.add_comm, &[nx, nnx]);
    let comm_symm = esymm(d, p, nx_nnx, nnx_nx, comm);
    let an = d.lemma(p.add_neg, &[nx]);
    let zero_c = czero(d, p);
    let h = echain(d, p, nnx_nx, &[(nx_nnx, comm_symm), (zero_c, an)]);
    equiv_of_sub_equiv_zero(d, p, nnx, x, h)
}

/// From `v_equiv_zero : Equiv v zero` and `zero_le_bound : le zero bound`,
/// derive `le (abs v) bound`. Duplicated from `derivative.rs`'s private
/// helper of the same shape (private to that module, so a sibling module
/// cannot reach it).
fn close_zero_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_equiv_zero: ExprId,
    zero_le_bound: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let v_le_zero = d.lemma(p.le_of_equiv, &[v, zero_c, v_equiv_zero]);
    let h_upper = d.lemma(p.le_trans, &[v, zero_c, bound, v_le_zero, zero_le_bound]);
    let nv = cneg(d, p, v);
    let neg_zero_c = cneg(d, p, zero_c);
    let nv_eq_negzero = d.lemma(p.neg_congr, &[v, zero_c, v_equiv_zero]);
    let nz_eq = neg_zero_equiv(d, p);
    let nv_equiv_zero = echain(d, p, nv, &[(neg_zero_c, nv_eq_negzero), (zero_c, nz_eq)]);
    let nv_le_zero = d.lemma(p.le_of_equiv, &[nv, zero_c, nv_equiv_zero]);
    let h_lower = d.lemma(p.le_trans, &[nv, zero_c, bound, nv_le_zero, zero_le_bound]);
    d.lemma(p.abs_le, &[v, bound, h_upper, h_lower])
}

/// From `h : Equiv (abs v) zero`, derive `Equiv v zero` — the converse
/// direction `close_zero_error` does not give: `v ≤ |v| ≤ 0` and
/// `−v ≤ |v| ≤ 0` (the second via `neg_le_neg` + `double_neg`) sandwich `v`
/// between `0` and itself.
fn equiv_zero_of_abs_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let abs_v = cabs(d, p, v);

    let v_le_absv = d.lemma(p.le_abs_self, &[v]);
    let refl_v = erefl(d, p, v);
    let v_le_zero = d.lemma(p.le_congr, &[v, v, abs_v, zero_c, refl_v, h, v_le_absv]);

    let nv = cneg(d, p, v);
    let negv_le_absv = d.lemma(p.neg_le_abs, &[v]);
    let refl_nv = erefl(d, p, nv);
    let negv_le_zero = d.lemma(
        p.le_congr,
        &[nv, nv, abs_v, zero_c, refl_nv, h, negv_le_absv],
    );

    let step = d.lemma(p.neg_le_neg, &[nv, zero_c, negv_le_zero]);
    // step : le (neg zero) (neg nv)
    let neg_zero_c = cneg(d, p, zero_c);
    let nnv = cneg(d, p, nv);
    let nz_eq = neg_zero_equiv(d, p);
    let dn = double_neg(d, p, v); // Equiv nnv v
    let zero_le_v = d.lemma(p.le_congr, &[neg_zero_c, zero_c, nnv, v, nz_eq, dn, step]);

    d.lemma(p.equiv_of_le_le, &[v, zero_c, v_le_zero, zero_le_v])
}

/// `CReal.hasDerivative_closeOfEquiv : ∀ F F' a b, HasDerivativeOn F F' a b →
/// ∀ u v, le a u → le u b → le a v → le v b → Equiv u v → Equiv (F u) (F v)`.
/// See the block comment above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_has_derivative_close_of_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = d.const_app(p.has_derivative_on, &[f, fp, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let hau_ty = cle(d, p, a, u);
    let hau_fv = d.fresh_fvar();
    let hau = d.kernel().fvar(hau_fv);
    let hub_ty = cle(d, p, u, b);
    let hub_fv = d.fresh_fvar();
    let hub = d.kernel().fvar(hub_fv);
    let hav_ty = cle(d, p, a, v);
    let hav_fv = d.fresh_fvar();
    let hav = d.kernel().fvar(hav_fv);
    let hvb_ty = cle(d, p, v, b);
    let hvb_fv = d.fresh_fvar();
    let hvb = d.kernel().fvar(hvb_fv);

    let huv_ty = equiv(d, p, u, v);
    let huv_fv = d.fresh_fvar();
    let huv = d.kernel().fvar(huv_fv);

    let zero_c = czero(d, p);
    let w = cdiff(d, p, v, u); // add v (neg u)

    // w_equiv_zero : Equiv w zero, from Equiv u v.
    let w_equiv_zero = {
        let nc = d.lemma(p.neg_congr, &[u, v, huv]); // Equiv (neg u) (neg v)
        let refl_v = erefl(d, p, v);
        let nu = cneg(d, p, u);
        let nv0 = cneg(d, p, v);
        let step1 = d.lemma(p.add_congr, &[v, v, nu, nv0, refl_v, nc]);
        // step1 : Equiv (add v (neg u)) (add v (neg v))
        let an = d.lemma(p.add_neg, &[v]); // Equiv (add v (neg v)) zero
        let v_nv = cadd(d, p, v, nv0);
        echain(d, p, w, &[(v_nv, step1), (zero_c, an)])
    };

    let zero_le_zero = d.lemma(p.le_refl, &[zero_c]);
    let abs_w_le_zero = close_zero_error(d, p, w, zero_c, w_equiv_zero, zero_le_zero);

    let e2 = d.num(0);
    let mod_fn = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
    let mod_val = d.apply(mod_fn, &[e2]);
    let in_bound = div_succ(d, p, 1, mod_val);
    let ofr_in = d.const_app(p.of_rat, &[in_bound]);
    let zero_le_ofr_in = {
        let one_nat = d.num(1);
        let rzero_expr = rzero(d, p.rat);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, mod_val]);
        d.lemma(p.of_rat_le, &[rzero_expr, in_bound, rle])
    };
    let abs_w_for_hyp = cabs(d, p, w);
    let hyp = d.lemma(
        p.le_trans,
        &[abs_w_for_hyp, zero_c, ofr_in, abs_w_le_zero, zero_le_ofr_in],
    );

    let error_bound = d.lemma(
        p.hd_spec,
        &[f, fp, a, b, hf, e2, u, v, hau, hub, hav, hvb, hyp],
    );
    // error_bound : le (abs error) (mul (ofRat (natDivSucc 1 e2)) (abs w))
    // where error = add (add (F v) (neg (F u))) (neg (mul (F' u) w)).

    let fu = d.apply(f, &[u]);
    let fv = d.apply(f, &[v]);
    let fpu = d.apply(fp, &[u]);
    let deriv_term = cmul(d, p, fpu, w);
    let fy_fx = cdiff(d, p, fv, fu);
    let error = cdiff(d, p, fy_fx, deriv_term);

    let ofr_e2 = {
        let r = div_succ(d, p, 1, e2);
        d.const_app(p.of_rat, &[r])
    };
    let ofr_e2_nonneg = {
        let one_nat = d.num(1);
        let rzero_expr = rzero(d, p.rat);
        let r = div_succ(d, p, 1, e2);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, e2]);
        d.lemma(p.of_rat_le, &[rzero_expr, r, rle])
    };
    let abs_w = cabs(d, p, w);
    let out_bound = cmul(d, p, ofr_e2, abs_w);
    let out_bound_le_zero = {
        let step_a = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[ofr_e2, abs_w, zero_c, ofr_e2_nonneg, abs_w_le_zero],
        );
        // step_a : le (mul ofr_e2 abs_w) (mul ofr_e2 zero_c)
        let mz = d.lemma(p.mul_zero, &[ofr_e2]); // Equiv (mul ofr_e2 zero_c) zero_c
        let ofr_e2_zero = cmul(d, p, ofr_e2, zero_c);
        let refl_lhs = erefl(d, p, out_bound);
        d.lemma(
            p.le_congr,
            &[
                out_bound,
                out_bound,
                ofr_e2_zero,
                zero_c,
                refl_lhs,
                mz,
                step_a,
            ],
        )
    };

    let abs_error = cabs(d, p, error);
    let error_le_zero = d.lemma(
        p.le_trans,
        &[abs_error, out_bound, zero_c, error_bound, out_bound_le_zero],
    );
    let abs_error_nonneg = d.lemma(p.abs_nonneg, &[error]);
    let abs_error_eq_zero = d.lemma(
        p.equiv_of_le_le,
        &[abs_error, zero_c, error_le_zero, abs_error_nonneg],
    );
    let error_equiv_zero = equiv_zero_of_abs_equiv_zero(d, p, error, abs_error_eq_zero);

    let deriv_term_equiv_zero = {
        let refl_fpu = erefl(d, p, fpu);
        let mc = d.lemma(p.mul_congr, &[fpu, fpu, w, zero_c, refl_fpu, w_equiv_zero]);
        // mc : Equiv (mul fpu w) (mul fpu zero_c)
        let mz = d.lemma(p.mul_zero, &[fpu]); // Equiv (mul fpu zero_c) zero_c
        let fpu_zero = cmul(d, p, fpu, zero_c);
        echain(d, p, deriv_term, &[(fpu_zero, mc), (zero_c, mz)])
    };

    let fy_fx_equiv_deriv_term = equiv_of_sub_equiv_zero(d, p, fy_fx, deriv_term, error_equiv_zero);
    let fy_fx_equiv_zero = d.lemma(
        p.equiv_trans,
        &[
            fy_fx,
            deriv_term,
            zero_c,
            fy_fx_equiv_deriv_term,
            deriv_term_equiv_zero,
        ],
    );
    let fv_equiv_fu = equiv_of_sub_equiv_zero(d, p, fv, fu, fy_fx_equiv_zero);
    let conclusion = esymm(d, p, fv, fu, fv_equiv_fu); // Equiv fu fv

    let value = {
        let with_huv = d.lam_fv(huv_fv, huv_ty, conclusion);
        let with_hvb = d.lam_fv(hvb_fv, hvb_ty, with_huv);
        let with_hav = d.lam_fv(hav_fv, hav_ty, with_hvb);
        let with_hub = d.lam_fv(hub_fv, hub_ty, with_hav);
        let with_hau = d.lam_fv(hau_fv, hau_ty, with_hub);
        let with_v = d.lam_fv(v_fv, carrier, with_hau);
        let with_u = d.lam_fv(u_fv, carrier, with_v);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_u);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let concl = equiv(d, p, fu, fv);
        let after_huv = d.arrow(huv_ty, concl);
        let after_hvb = d.arrow(hvb_ty, after_huv);
        let after_hav = d.arrow(hav_ty, after_hvb);
        let after_hub = d.arrow(hub_ty, after_hav);
        let after_hau = d.arrow(hau_ty, after_hub);
        let over_v = d.pi_fv(v_fv, carrier, after_hau);
        let over_u = d.pi_fv(u_fv, carrier, over_v);
        let after_hf = d.arrow(hf_ty, over_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_close_of_equiv,
        uparams: vec![],
        ty,
        value,
    })
}
