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
//! The first consumer is `CReal.monotone_of_nonneg_deriv`, landed further
//! down this file: each piece's difference is bounded below by
//! `−(1/(e_acc+1))·step` (`HasDerivativeOn`'s spec plus the
//! nonnegative-derivative hypothesis), so [`declare_sum_range_telescope_ge`]
//! with `bound := neg ((1/(e_acc+1))·step)` gives a lower bound on `F y − F
//! x` for every outer accuracy, and `CReal.le_of_forall_le_add_small`
//! (`archimedean_squeeze.rs`) closes that down to `CReal.le` outright. That
//! composition needed a piece count chosen from an Archimedean bound on
//! `abs (y − x)` (not `CReal.bound` itself — see
//! `declare_monotone_of_nonneg_deriv`'s own documentation), plus — contrary
//! to what this paragraph used to say — `CReal.sumRange (fun _ => bound) k`
//! DOES eventually need folding into `mul (ofNat k) bound`
//! ([`declare_sum_range_const`]) once a concrete numeric bound has to be
//! extracted from the telescoped sum. The telescope lemmas above still leave
//! it unevaluated, and still do not need it themselves.

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, and_intro, cadd, cle, creal_ty, div_succ, embed, equiv};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, req, rmul, rone, rzero,
};

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

// =============================================================================
// `CReal.monotone_of_nonneg_deriv`
// =============================================================================
//
// The recipe: with `c` an Archimedean witness for `abs (y - x)` and
// `magnitude := succ c`, per outer accuracy `e_outer`,
//
//   e_acc   := magnitude * e_outer + c        (exact, `Rat.natDivSucc_scale`)
//   mod_val := HasDerivativeOn.modulus _ e_acc
//   m0      := magnitude * mod_val + c
//   K       := succ m0
//   step    := (y - x) * ofRat (natDivSucc 1 m0)
//   x_i     := x + ofNat i * step
//
// Each piece's `HasDerivativeOn` estimate, plus the nonnegative-derivative
// hypothesis and `step >= 0`, bounds `F(x_{i+1}) - F(x_i)` below by a FIXED
// (i-independent) constant; [`declare_sum_range_telescope_ge`] sums the `K`
// pieces, [`declare_sum_range_const`] evaluates that sum as a single
// product, and the same `Rat.natDivSucc_scale` identity that built `e_acc`
// collapses the product to exactly `1/(e_outer+1)`, closed by
// `CReal.le_of_forall_le_add_small`.
//
// **A second gap beyond the one the two-lane handoff plan named.** That plan
// flagged `x_K ~ y` (never `=`) as the reason `hasDerivative_closeOfEquiv`
// exists. The SAME issue holds at the OTHER end: `x_0 := x + ofNat
// Nat.zero * step` is only ever `Equiv x`, never syntactically `x` (`ofNat
// Nat.zero` is not definitionally `CReal.zero` — no more than `ofNat
// (Nat.succ Nat.zero)` is definitionally `CReal.one`, which is exactly why
// `of_nat_one_equiv_local` above needs a proof at all). So
// `hasDerivative_closeOfEquiv` is applied TWICE below, once per endpoint —
// nothing new is needed for it, but a proof built only for the `x_K` end
// would still be missing the `x_0` end.

// --- `ofNat 0`/`ofNat 1`/`ofNat (succ m)`, restated locally --------------

/// `Eq Rat (Rat.natDivSucc Nat.zero Nat.zero) Rat.zero` — `Rat.self_normalize`
/// applied to `Rat.zero` itself, the same shortcut
/// [`CRealPrelude::rat_unit_eq_one`] uses for `Rat.one`: `num`/`den` are
/// structure projections of `Rat.zero`'s own direct `Rat.mk`, so they reduce
/// to exactly `natDivSucc`'s inputs and no gcd/cross-multiplication reasoning
/// is needed.
fn rat_zero_eq_nat_div_succ(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let zero_val = rzero(d, rat);
    d.lemma(rat.self_normalize, &[zero_val])
    // : Eq Rat (natDivSucc Nat.zero Nat.zero) zero_val
}

/// `Equiv (ofNat Nat.zero) zero` — the numeral-`0` sibling of
/// [`of_nat_one_equiv_local`]: `ofNat Nat.zero` unfolds one delta step to
/// `embed (natDivSucc 0 0)`, `CReal.zero` unfolds one delta step to `embed
/// Rat.zero`, and [`rat_zero_eq_nat_div_succ`] bridges them.
fn of_nat_zero_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[zero_nat, zero_nat]);
    let zero_rat = rzero(d, rat);
    let unit_eq_zero = rat_zero_eq_nat_div_succ(d, p);
    let unit_embed = embed(d, p, unit); // defeq (ofNat Nat.zero)
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, zero_rat, unit_eq_zero, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, unit_embed, embedded)
    })
    // : Equiv unit_embed (ofRat zero_rat) -- defeq Equiv (ofNat Nat.zero) zero.
}

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` — duplicated from `integral.rs`'s
/// private `of_nat_one_equiv_local` (that module is out of scope for this
/// slice, so it cannot be called from here; see its doc comment for the
/// route: `ofNat 1` and `one` each unfold one delta step to an `embed`, and
/// [`CRealPrelude::rat_unit_eq_one`] bridges the two `Rat`s).
fn of_nat_one_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` — duplicated from
/// `integral.rs`'s private `of_nat_succ_equiv_local`, for the same
/// out-of-scope-file reason.
fn of_nat_succ_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, add_of_nat_m_1, embedded)
    });
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    let one_eq = of_nat_one_equiv_local(d, p);
    let refl_m = d.lemma(p.equiv_refl, &[of_nat_m]);
    let congr_step = d.lemma(
        p.add_congr,
        &[of_nat_m, of_nat_m, of_nat_1, one_c, refl_m, one_eq],
    );
    let add_of_nat_m_one = cadd(d, p, of_nat_m, one_c);
    d.lemma(
        p.equiv_trans,
        &[
            of_nat_succ_m,
            add_of_nat_m_1,
            add_of_nat_m_one,
            flipped,
            congr_step,
        ],
    )
}

// --- `sumRange` over a constant -------------------------------------------

/// `Equiv (sumRange (fun _ => w) (Nat.succ m)) (mul (ofNat (Nat.succ m)) w)`
/// — duplicated from `integral.rs`'s private `riemann_sum_const_core`
/// (out of scope for this slice): induction on `m`, `w` fixed. The base case
/// needs `ofNat 1 ~ one` ([`of_nat_one_equiv_local`]); the step needs `ofNat
/// (succ k) ~ add (ofNat k) one` ([`of_nat_succ_equiv_local`]) plus
/// [`right_distrib`].
fn sum_range_const_core(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, m: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f = const_fn(d, w);
        let sx = d.succ(x);
        let lhs = d.const_app(p.sum_range, &[f, sx]);
        let ox = d.const_app(p.of_nat, &[sx]);
        let rhs = cmul(d, p, ox, w);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let one_c = d.kernel().const_(p.one, vec![]);
            let one_nat = d.num(1);
            let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);

            let start = cadd(d, p, zero_c, w);
            let m1w = cmul(d, p, one_c, w);
            let target_mw = cmul(d, p, of_nat_1, w);

            let step1 = {
                let comm = d.lemma(p.add_comm, &[zero_c, w]);
                let wz = cadd(d, p, w, zero_c);
                let vanish = d.lemma(p.add_zero, &[w]);
                d.lemma(p.equiv_trans, &[start, wz, w, comm, vanish])
            };
            let step2 = {
                let mw1 = cmul(d, p, w, one_c);
                let mul_one_w = d.lemma(p.mul_one, &[w]);
                let back = d.lemma(p.equiv_symm, &[mw1, w, mul_one_w]);
                let comm = d.lemma(p.mul_comm, &[w, one_c]);
                d.lemma(p.equiv_trans, &[w, mw1, m1w, back, comm])
            };
            let step3 = {
                let one_eq = of_nat_one_equiv_local(d, p);
                let back = d.lemma(p.equiv_symm, &[of_nat_1, one_c, one_eq]);
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.mul_congr, &[one_c, of_nat_1, w, w, back, refl_w])
            };
            let s01 = d.lemma(p.equiv_trans, &[start, w, m1w, step1, step2]);
            d.lemma(p.equiv_trans, &[start, m1w, target_mw, s01, step3])
        },
        &|d, j, ih| {
            let f = const_fn(d, w);
            let sj = d.succ(j);
            let prior = d.const_app(p.sum_range, &[f, sj]);
            let start = cadd(d, p, prior, w);

            let of_nat_sj = d.const_app(p.of_nat, &[sj]);
            let ih_target = cmul(d, p, of_nat_sj, w);

            let step_ih = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.add_congr, &[prior, ih_target, w, w, ih, refl_w])
            };
            let after_ih = cadd(d, p, ih_target, w);

            let ssj = d.succ(sj);
            let of_nat_ssj = d.const_app(p.of_nat, &[ssj]);
            let final_target = cmul(d, p, of_nat_ssj, w);

            let one_c = d.kernel().const_(p.one, vec![]);
            let succ_eq = of_nat_succ_equiv_local(d, p, sj);
            let sum_of_nat = cadd(d, p, of_nat_sj, one_c);
            let expanded = cmul(d, p, sum_of_nat, w);

            let h_a = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(
                    p.mul_congr,
                    &[of_nat_ssj, sum_of_nat, w, w, succ_eq, refl_w],
                )
            };
            let h_b = right_distrib(d, p, of_nat_sj, one_c, w);
            let one_w = cmul(d, p, one_c, w);
            let distributed = cadd(d, p, ih_target, one_w);
            let h_c = {
                let refl_left = d.lemma(p.equiv_refl, &[ih_target]);
                let one_mul_w = {
                    let mw1 = cmul(d, p, w, one_c);
                    let mul_one_w = d.lemma(p.mul_one, &[w]);
                    let comm = d.lemma(p.mul_comm, &[one_c, w]);
                    d.lemma(p.equiv_trans, &[one_w, mw1, w, comm, mul_one_w])
                };
                d.lemma(
                    p.add_congr,
                    &[ih_target, ih_target, one_w, w, refl_left, one_mul_w],
                )
            };

            let rev = {
                let s1 = d.lemma(
                    p.equiv_trans,
                    &[final_target, expanded, distributed, h_a, h_b],
                );
                d.lemma(
                    p.equiv_trans,
                    &[final_target, distributed, after_ih, s1, h_c],
                )
            };
            let rev_flipped = d.lemma(p.equiv_symm, &[final_target, after_ih, rev]);
            d.lemma(
                p.equiv_trans,
                &[start, after_ih, final_target, step_ih, rev_flipped],
            )
        },
        m,
    )
}

/// Admit `CReal.sumRange_const`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_range_const(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let body = sum_range_const_core(d, p, w, m);

    let sm = d.succ(m);
    let cf = const_fn(d, w);
    let lhs = d.const_app(p.sum_range, &[cf, sm]);
    let on = d.const_app(p.of_nat, &[sm]);
    let rhs = cmul(d, p, on, w);
    let concl = equiv(d, p, lhs, rhs);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(w_fv, carrier, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, body);
        d.lam_fv(w_fv, carrier, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the mesh identity -----------------------------------------------------

/// `Eq Rat (Rat.mul (Rat.natDivSucc (Nat.succ m) 0) (Rat.natDivSucc 1 m))
/// Rat.one` — duplicated from `integral.rs`'s private
/// `nat_div_succ_inverse_pair_eq_one` (out of scope for this slice): `(m+1)/1
/// · 1/(m+1) = 1`.
fn nat_div_succ_inverse_pair_eq_one(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);
    let one_val = rone(d, rat);

    let product = rmul(d, whole, modulus);
    let fused = {
        let scaled = NatOps::mul(d, successor, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, m])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[successor, one_nat, m]);
    let collapsed = d.const_app(rat.nat_div_succ, &[successor, m]);
    let collapse = {
        let scaled = NatOps::mul(d, successor, one_nat);
        let identity = d.lemma(nat.mul_one, &[successor]);
        nat_eq_to_rat(d, scaled, successor, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, m])
        })
    };
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let scale = {
        let deep = NatOps::mul(d, successor, zero_nat);
        let index = NatOps::add(d, deep, m);
        let law = d.lemma(rat.nat_div_succ_scale, &[m, zero_nat]);
        let flatten = d.lemma(nat.zero_add, &[m]);
        nat_rewrite_prop(d, index, m, flatten, law, &|d, t| {
            let left = d.const_app(rat.nat_div_succ, &[successor, t]);
            req(d, left, unit)
        })
    };
    let unit_is_one = d.lemma(p.rat_unit_eq_one, &[]);
    let (_, cancel) = rchain(
        d,
        product,
        &[
            (fused, fuse),
            (collapsed, collapse),
            (unit, scale),
            (one_val, unit_is_one),
        ],
    );
    cancel
}

/// `Equiv (mul (ofNat (Nat.succ m)) (ofRat (Rat.natDivSucc 1 m))) one` —
/// duplicated from `integral.rs`'s private `mesh_inverse_identity`.
fn mesh_inverse_identity(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);

    let embed_whole = embed(d, p, whole);
    let embed_modulus = embed(d, p, modulus);
    let product_real = cmul(d, p, embed_whole, embed_modulus);

    let rat_eq = nat_div_succ_inverse_pair_eq_one(d, p, m);
    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[whole, modulus]);

    let product_rat = rmul(d, whole, modulus);
    let one_rat = rone(d, rat);
    rat_eq_rewrite(d, product_rat, one_rat, rat_eq, of_rat_mul_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, product_real, embedded)
    })
}

/// `Equiv (mul (ofNat (Nat.succ m)) (mul width frac)) width`, where `frac :=
/// embed (Rat.natDivSucc 1 m)` — duplicated verbatim from `integral.rs`'s
/// private `mesh_times_count_eq_width` (already general in `width`, not tied
/// to a Riemann sum's own `a`/`b`).
fn mesh_times_count_eq_width(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    frac: ExprId,
    m: ExprId,
) -> ExprId {
    let on = {
        let successor = d.succ(m);
        d.const_app(p.of_nat, &[successor])
    };
    let delta = cmul(d, p, width, frac);
    let a_start = cmul(d, p, on, delta);

    let on_width = cmul(d, p, on, width);
    let width_on = cmul(d, p, width, on);
    let on_frac = cmul(d, p, on, frac);

    let b1 = cmul(d, p, on_width, frac);
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[on, width, frac]);
        d.lemma(p.equiv_symm, &[b1, a_start, assoc])
    };

    let b2 = cmul(d, p, width_on, frac);
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[on, width]);
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        d.lemma(
            p.mul_congr,
            &[on_width, width_on, frac, frac, comm, refl_frac],
        )
    };

    let b3 = cmul(d, p, width, on_frac);
    let h3 = d.lemma(p.mul_assoc, &[width, on, frac]);

    let one_c = d.kernel().const_(p.one, vec![]);
    let b4 = cmul(d, p, width, one_c);
    let h4 = {
        let cancel = mesh_inverse_identity(d, p, m);
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        d.lemma(
            p.mul_congr,
            &[width, width, on_frac, one_c, refl_width, cancel],
        )
    };

    let h5 = d.lemma(p.mul_one, &[width]);

    echain(
        d,
        p,
        a_start,
        &[(b1, h1), (b2, h2), (b3, h3), (b4, h4), (width, h5)],
    )
}

/// Admit `CReal.mesh_count_width`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_count_width(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let width_fv = d.fresh_fvar();
    let width = d.kernel().fvar(width_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);

    let body = mesh_times_count_eq_width(d, p, width, frac_real, m);

    let sm = d.succ(m);
    let on = d.const_app(p.of_nat, &[sm]);
    let delta = cmul(d, p, width, frac_real);
    let lhs = cmul(d, p, on, delta);
    let concl = equiv(d, p, lhs, width);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(width_fv, carrier, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, body);
        d.lam_fv(width_fv, carrier, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_count_width,
        uparams: vec![],
        ty,
        value,
    })
}

// --- subdivision points lie in `[a, b]` -------------------------------------

/// `add b (neg a)` — the interval width `b − a`. Duplicated from
/// `integral.rs`'s private `width_of`.
fn width_of(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    cadd(d, p, b, na)
}

/// `Equiv (add a (add b (neg a))) b` — `a + (b − a) ~ b`. Duplicated from
/// `integral.rs`'s private `add_sub_cancel`.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let start = cadd(d, p, a, width);

    let nab = cadd(d, p, na, b);
    let s1 = cadd(d, p, a, nab);
    let h1 = {
        let comm = d.lemma(p.add_comm, &[b, na]);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, width, nab, refl_a, comm])
    };

    let ana = cadd(d, p, a, na);
    let s2 = cadd(d, p, ana, b);
    let h2 = {
        let assoc = d.lemma(p.add_assoc, &[a, na, b]);
        d.lemma(p.equiv_symm, &[s2, s1, assoc])
    };

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, zero_c, b);
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        d.lemma(p.add_congr, &[ana, zero_c, b, b, hn, refl_b])
    };

    let s4 = cadd(d, p, b, zero_c);
    let h4 = d.lemma(p.add_comm, &[zero_c, b]);

    let h5 = d.lemma(p.add_zero, &[b]);

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (b, h5)],
    )
}

/// `Equiv (add (add a step) (neg a)) step` — `(a + step) − a ~ step`, the
/// LEFT-cancellation [`add_sub_cancel`] does not give (that one cancels on
/// the right: `a + (b − a) ~ b`).
fn add_sub_cancel_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, step: ExprId) -> ExprId {
    let a_step = cadd(d, p, a, step);
    let na = cneg(d, p, a);
    let start = cadd(d, p, a_step, na);

    let step_a = cadd(d, p, step, a);
    let s1 = cadd(d, p, step_a, na);
    let h1 = {
        let comm = d.lemma(p.add_comm, &[a, step]);
        let refl_na = d.lemma(p.equiv_refl, &[na]);
        d.lemma(p.add_congr, &[a_step, step_a, na, na, comm, refl_na])
    };

    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, step, a_na);
    let h2 = d.lemma(p.add_assoc, &[step, a, na]);

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, step, zero_c);
    let h3 = {
        let an = d.lemma(p.add_neg, &[a]);
        let refl_step = d.lemma(p.equiv_refl, &[step]);
        d.lemma(p.add_congr, &[step, step, a_na, zero_c, refl_step, an])
    };

    let h4 = d.lemma(p.add_zero, &[step]);

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (step, h4)])
}

/// `add x0 (mul (ofNat i) step)` — the canonical `i`-th subdivision point.
/// Built as its own helper so every occurrence below is the SAME term,
/// matching [`declare_subdivision_point_in_bounds`]'s own `sp`.
fn sample_pt(d: &mut IntDev<'_>, p: CRealPrelude, x0: ExprId, step: ExprId, i: ExprId) -> ExprId {
    let oi = d.const_app(p.of_nat, &[i]);
    let term = cmul(d, p, oi, step);
    cadd(d, p, x0, term)
}

/// `Equiv (add (sample_pt x0 step (Nat.succ i)) (neg (sample_pt x0 step i)))
/// step` — `x_{i+1} − x_i ~ step`, needed so the per-piece `HasDerivativeOn`
/// spec (stated about the LITERAL difference of two consecutive points) can
/// be read as a statement about the (i-independent) `step`.
fn consecutive_diff_eq_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x0: ExprId,
    step: ExprId,
    i: ExprId,
) -> ExprId {
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let u = cmul(d, p, of_nat_i, step);
    let x_i = cadd(d, p, x0, u);
    let si = d.succ(i);

    let v_eq_u_plus_step = {
        let of_nat_si = d.const_app(p.of_nat, &[si]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let succ_eq = of_nat_succ_equiv_local(d, p, i);
        let sum_of_nat = cadd(d, p, of_nat_i, one_c);
        let v = cmul(d, p, of_nat_si, step);
        let expanded = cmul(d, p, sum_of_nat, step);
        let h_a = {
            let refl_step = d.lemma(p.equiv_refl, &[step]);
            d.lemma(
                p.mul_congr,
                &[of_nat_si, sum_of_nat, step, step, succ_eq, refl_step],
            )
        };
        let h_b = right_distrib(d, p, of_nat_i, one_c, step);
        let one_step = cmul(d, p, one_c, step);
        let distributed = cadd(d, p, u, one_step);
        let h_c = {
            let refl_u = d.lemma(p.equiv_refl, &[u]);
            let one_mul_step = {
                let step_one = cmul(d, p, step, one_c);
                let mul_one_step = d.lemma(p.mul_one, &[step]);
                let comm = d.lemma(p.mul_comm, &[one_c, step]);
                d.lemma(
                    p.equiv_trans,
                    &[one_step, step_one, step, comm, mul_one_step],
                )
            };
            d.lemma(p.add_congr, &[u, u, one_step, step, refl_u, one_mul_step])
        };
        let u_plus_step = cadd(d, p, u, step);
        let s1 = d.lemma(p.equiv_trans, &[v, expanded, distributed, h_a, h_b]);
        d.lemma(p.equiv_trans, &[v, distributed, u_plus_step, s1, h_c])
    };

    let of_nat_si = d.const_app(p.of_nat, &[si]);
    let v = cmul(d, p, of_nat_si, step);
    let x_si = cadd(d, p, x0, v);
    let nx_i = cneg(d, p, x_i);
    let start = cadd(d, p, x_si, nx_i);

    let u_plus_step = cadd(d, p, u, step);
    let x0_u_step = cadd(d, p, x0, u_plus_step);
    let h_v = {
        let refl_x0 = d.lemma(p.equiv_refl, &[x0]);
        d.lemma(
            p.add_congr,
            &[x0, x0, v, u_plus_step, refl_x0, v_eq_u_plus_step],
        )
    };
    let s1 = cadd(d, p, x0_u_step, nx_i);
    let h1 = {
        let refl_nxi = d.lemma(p.equiv_refl, &[nx_i]);
        d.lemma(p.add_congr, &[x_si, x0_u_step, nx_i, nx_i, h_v, refl_nxi])
    };

    let xi_plus_step = cadd(d, p, x_i, step);
    let assoc = d.lemma(p.add_assoc, &[x0, u, step]); // Equiv xi_plus_step x0_u_step
    let h2_base = d.lemma(p.equiv_symm, &[xi_plus_step, x0_u_step, assoc]);
    let refl_nxi2 = d.lemma(p.equiv_refl, &[nx_i]);
    let s2 = cadd(d, p, xi_plus_step, nx_i);
    let h2 = d.lemma(
        p.add_congr,
        &[x0_u_step, xi_plus_step, nx_i, nx_i, h2_base, refl_nxi2],
    );

    let cancel = add_sub_cancel_left(d, p, x_i, step);

    echain(d, p, start, &[(s1, h1), (s2, h2), (step, cancel)])
}

/// `CReal.le zero (CReal.ofNat n)`. Duplicated from `integral.rs`'s private
/// `zero_le_of_nat`.
fn zero_le_of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let rat_n = d.const_app(p.rat.nat_div_succ, &[n, zero_nat]);
    let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
    let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[n, zero_nat]);
    d.lemma(p.of_rat_le, &[rzero_expr, rat_n, rle])
}

/// `CReal.le x (add x w)`, given `hw : CReal.le zero w`. Duplicated from
/// `integral.rs`'s private `shift_le_of_nonneg`.
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
}

/// `(step, hstep_nonneg)`, `step := mul (add b (neg a)) (ofRat (natDivSucc 1
/// m))`, given `hab : le a b`. Duplicated from `integral.rs`'s private
/// `delta_nonneg_of`.
fn step_nonneg_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    hab: ExprId,
) -> (ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    let step = cmul(d, p, width, frac_real);
    let zero_c = czero(d, p);

    let width_nonneg = {
        let na = cneg(d, p, a);
        let refl_na = d.lemma(p.le_refl, &[na]);
        let a_na = cadd(d, p, a, na);
        let b_na = cadd(d, p, b, na);
        let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_bna = d.lemma(p.equiv_refl, &[b_na]);
        d.lemma(
            p.le_congr,
            &[a_na, zero_c, b_na, b_na, hn, refl_bna, shifted],
        )
    };

    let frac_nonneg = {
        let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, m]);
        d.lemma(p.of_rat_le, &[rzero_expr, frac, rle])
    };

    let step_nonneg = d.lemma(p.mul_nonneg, &[width, frac_real, width_nonneg, frac_nonneg]);
    (step, step_nonneg)
}

/// `Nat.le i n`, from `hlt : Nat.lt i n` (defeq `Nat.le (succ i) n`).
/// Duplicated from `integral.rs`'s private `nat_le_of_lt`.
fn nat_le_of_lt(d: &mut IntDev<'_>, i: ExprId, n: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let succ_i = d.succ(i);
    let step = d.const_app(np.le_succ, &[i]);
    d.const_app(np.le_trans, &[i, succ_i, n, step, hlt])
}

/// `CReal.subdivisionPoint_in_bounds : ∀ a b m i, le a b → Nat.le i (Nat.succ
/// m) → And (le a sp) (le sp b)`, `sp := sample_pt a step i`, `step := mul
/// (add b (neg a)) (ofRat (natDivSucc 1 m))` — a trivial generalization of
/// `integral.rs`'s `riemannSum_sample_in_bounds` from `Nat.lt` to `Nat.le`
/// (see that name's own doc comment). The upper-bound half is actually
/// SIMPLER than that theorem's own: `hle` is already `Nat.le i (Nat.succ
/// m)`, so `CReal.ofNat_le` applies with no `Nat.lt → Nat.le` conversion.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_subdivision_point_in_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let n = d.succ(m);
    let hle_ty = d.le(i, n);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let (step, step_nonneg) = step_nonneg_of(d, p, a, b, m, hab);
    let sp = sample_pt(d, p, a, step, i);
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let term = cmul(d, p, of_nat_i, step);

    let lower = {
        let i_nonneg = zero_le_of_nat(d, p, i);
        let term_nonneg = d.lemma(p.mul_nonneg, &[of_nat_i, step, i_nonneg, step_nonneg]);
        shift_le_of_nonneg(d, p, a, term, term_nonneg)
    };

    let upper = {
        let of_nat_ile = d.lemma(p.of_nat_le, &[i, n, hle]);
        let of_nat_n = d.const_app(p.of_nat, &[n]);

        let step_mul = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[step, of_nat_i, of_nat_n, step_nonneg, of_nat_ile],
        );
        let comm_i = d.lemma(p.mul_comm, &[step, of_nat_i]);
        let comm_n = d.lemma(p.mul_comm, &[step, of_nat_n]);
        let di = cmul(d, p, step, of_nat_i);
        let dn = cmul(d, p, step, of_nat_n);
        let nd = cmul(d, p, of_nat_n, step);
        let commuted = d.lemma(p.le_congr, &[di, term, dn, nd, comm_i, comm_n, step_mul]);

        let width = width_of(d, p, a, b);
        let one_nat = d.num(1);
        let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_real = embed(d, p, frac);
        let n_step_eq_width = mesh_times_count_eq_width(d, p, width, frac_real, m);

        let refl_term = d.lemma(p.equiv_refl, &[term]);
        let term_le_width = d.lemma(
            p.le_congr,
            &[term, term, nd, width, refl_term, n_step_eq_width, commuted],
        );

        let refl_a = d.lemma(p.le_refl, &[a]);
        let shifted = d.lemma(p.add_le_add, &[a, a, term, width, refl_a, term_le_width]);

        let cancel = add_sub_cancel(d, p, a, b);
        let a_width = cadd(d, p, a, width);
        let refl_sp = d.lemma(p.equiv_refl, &[sp]);
        d.lemma(p.le_congr, &[sp, sp, a_width, b, refl_sp, cancel, shifted])
    };

    let a_le_sp = cle(d, p, a, sp);
    let sp_le_b = cle(d, p, sp, b);
    let and_ty = d.const_app(p.rat.int.logic.and, &[a_le_sp, sp_le_b]);
    let proof_body = and_intro(d, p, a_le_sp, sp_le_b, lower, upper);

    let ty = {
        let after_hle = d.arrow(hle_ty, and_ty);
        let after_hab = d.arrow(hab_ty, after_hle);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_m = d.pi_fv(m_fv, nat, over_i);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hle);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_m = d.lam_fv(m_fv, nat, over_i);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.subdivision_point_in_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

// --- small algebraic utilities for the main theorem -------------------------

/// `Equiv (add zero x) x`.
fn zero_add_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let zx = cadd(d, p, zero_c, x);
    let xz = cadd(d, p, x, zero_c);
    let comm = d.lemma(p.add_comm, &[zero_c, x]);
    let az = d.lemma(p.add_zero, &[x]);
    d.lemma(p.equiv_trans, &[zx, xz, x, comm, az])
}

/// From `h : Equiv (add val ww) zero`, derive `Equiv val (neg ww)` —
/// `val` solves `_ + ww ~ zero`, so it equals `neg ww`. The shared step
/// [`cancel_to_same`] applies once per side.
fn reduce_to_negw(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    val: ExprId,
    ww: ExprId,
    neg_w: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let val_zero = cadd(d, p, val, zero_c);
    let w_negw = cadd(d, p, ww, neg_w);
    let val_w_negw = cadd(d, p, val, w_negw);
    let val_w = cadd(d, p, val, ww);
    let valw_negw = cadd(d, p, val_w, neg_w);
    let zero_negw = cadd(d, p, zero_c, neg_w);
    let negw_zero = cadd(d, p, neg_w, zero_c);

    let s1 = {
        let az = d.lemma(p.add_zero, &[val]);
        d.lemma(p.equiv_symm, &[val_zero, val, az])
    };
    let s2 = {
        let an = d.lemma(p.add_neg, &[ww]);
        let an_symm = d.lemma(p.equiv_symm, &[w_negw, zero_c, an]);
        let refl_val = d.lemma(p.equiv_refl, &[val]);
        d.lemma(p.add_congr, &[val, val, zero_c, w_negw, refl_val, an_symm])
    };
    let s3 = {
        // add_assoc(val, ww, neg_w) : Equiv (add (add val ww) neg_w)
        //   (add val (add ww neg_w)) = Equiv valw_negw val_w_negw.
        let assoc = d.lemma(p.add_assoc, &[val, ww, neg_w]);
        d.lemma(p.equiv_symm, &[valw_negw, val_w_negw, assoc])
    };
    let s4 = {
        let refl_negw = d.lemma(p.equiv_refl, &[neg_w]);
        d.lemma(p.add_congr, &[val_w, zero_c, neg_w, neg_w, h, refl_negw])
    };
    let s5 = d.lemma(p.add_comm, &[zero_c, neg_w]);
    let s6 = d.lemma(p.add_zero, &[neg_w]);

    echain(
        d,
        p,
        val,
        &[
            (val_zero, s1),
            (val_w_negw, s2),
            (valw_negw, s3),
            (zero_negw, s4),
            (negw_zero, s5),
            (neg_w, s6),
        ],
    )
}

/// From `hx : Equiv (add xx ww) zero` and `hy : Equiv (add yy ww) zero`,
/// derive `Equiv xx yy` — both solve `_ + ww ~ zero`, so both equal `neg ww`.
fn cancel_to_same(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    xx: ExprId,
    yy: ExprId,
    ww: ExprId,
    hx: ExprId,
    hy: ExprId,
) -> ExprId {
    let neg_w = cneg(d, p, ww);
    let x_eq_negw = reduce_to_negw(d, p, xx, ww, neg_w, hx);
    let y_eq_negw = reduce_to_negw(d, p, yy, ww, neg_w, hy);
    let negw_eq_y = d.lemma(p.equiv_symm, &[yy, neg_w, y_eq_negw]);
    d.lemma(p.equiv_trans, &[xx, neg_w, yy, x_eq_negw, negw_eq_y])
}

/// `Equiv (mul a (neg b)) (neg (mul a b))` — `CReal` has no standalone
/// `mul_neg` law (mirroring the missing `neg_add`), so this is derived
/// inline: both sides solve `_ + mul a b ~ zero` (the first via
/// `left_distrib` against `neg_add_self`/`mul_zero`, the second via
/// `add_neg` commuted), and [`cancel_to_same`] identifies the two solutions.
fn mul_neg_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let ab = cmul(d, p, a, b);
    let anb = cmul(d, p, a, nb);

    let hx = {
        let nb_b = cadd(d, p, nb, b);
        let dist = d.lemma(p.left_distrib, &[a, nb, b]); // Equiv (mul a nb_b)(add anb ab)
        let nas = neg_add_self(d, p, b);
        let a_nbb = cmul(d, p, a, nb_b);
        let zero_c = czero(d, p);
        let a_zero = cmul(d, p, a, zero_c);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let congr1 = d.lemma(p.mul_congr, &[a, a, nb_b, zero_c, refl_a, nas]);
        let mz = d.lemma(p.mul_zero, &[a]);
        let anb_ab = cadd(d, p, anb, ab);
        let chain = echain(d, p, a_nbb, &[(a_zero, congr1), (zero_c, mz)]);
        let dist_symm = d.lemma(p.equiv_symm, &[a_nbb, anb_ab, dist]);
        d.lemma(p.equiv_trans, &[anb_ab, a_nbb, zero_c, dist_symm, chain])
    };
    let hy = neg_add_self(d, p, ab);
    let neg_ab = cneg(d, p, ab);
    cancel_to_same(d, p, anb, neg_ab, ab, hx, hy)
}

/// `Equiv (add pp (add dd (neg pp))) dd` — `P + (D − P) ~ D`, the
/// decomposition a bound on `D − P` needs to become a bound on `D`.
fn add_cancel_middle(d: &mut IntDev<'_>, p: CRealPrelude, dd: ExprId, pp: ExprId) -> ExprId {
    let neg_p = cneg(d, p, pp);
    let err = cadd(d, p, dd, neg_p);
    let start = cadd(d, p, pp, err);

    let p_d = cadd(d, p, pp, dd);
    let s1 = cadd(d, p, p_d, neg_p);
    let h1 = {
        let assoc = d.lemma(p.add_assoc, &[pp, dd, neg_p]);
        d.lemma(p.equiv_symm, &[s1, start, assoc])
    };

    let d_p = cadd(d, p, dd, pp);
    let s2 = cadd(d, p, d_p, neg_p);
    let h2 = {
        let comm = d.lemma(p.add_comm, &[pp, dd]);
        let refl_np = d.lemma(p.equiv_refl, &[neg_p]);
        d.lemma(p.add_congr, &[p_d, d_p, neg_p, neg_p, comm, refl_np])
    };

    let p_np = cadd(d, p, pp, neg_p);
    let s3 = cadd(d, p, dd, p_np);
    let h3 = d.lemma(p.add_assoc, &[dd, pp, neg_p]);

    let zero_c = czero(d, p);
    let s4 = cadd(d, p, dd, zero_c);
    let h4 = {
        let an = d.lemma(p.add_neg, &[pp]);
        let refl_d = d.lemma(p.equiv_refl, &[dd]);
        d.lemma(p.add_congr, &[dd, dd, p_np, zero_c, refl_d, an])
    };

    let h5 = d.lemma(p.add_zero, &[dd]);

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (dd, h5)],
    )
}

/// From `h : le (abs v) bound`, derive `le (neg bound) v` — the lower half
/// of the two-sided bound `within_real` packages.
fn lower_of_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let neg_v = cneg(d, p, v);
    let abs_v = cabs(d, p, v);
    let neg_le = d.lemma(p.neg_le_abs, &[v]);
    let step1 = d.lemma(p.le_trans, &[neg_v, abs_v, bound, neg_le, h]);
    let step2 = d.lemma(p.neg_le_neg, &[neg_v, bound, step1]);
    let nb = cneg(d, p, bound);
    let nnv = cneg(d, p, neg_v);
    let dn = double_neg(d, p, v);
    let refl_nb = d.lemma(p.equiv_refl, &[nb]);
    d.lemma(p.le_congr, &[nb, nb, nnv, v, refl_nb, dn, step2])
}

/// From `hv_nonneg : le zero v`, derive `Equiv (abs v) v`.
fn abs_eq_self_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    hv_nonneg: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_v = d.lemma(p.le_refl, &[v]);
    let neg_v = cneg(d, p, v);

    let neg_v_le_zero = {
        let step = d.lemma(p.neg_le_neg, &[zero_c, v, hv_nonneg]);
        let nz_eq = neg_zero_equiv(d, p);
        let neg_zero_c = cneg(d, p, zero_c);
        let refl_negv = d.lemma(p.equiv_refl, &[neg_v]);
        d.lemma(
            p.le_congr,
            &[neg_v, neg_v, neg_zero_c, zero_c, refl_negv, nz_eq, step],
        )
    };
    let neg_v_le_v = d.lemma(p.le_trans, &[neg_v, zero_c, v, neg_v_le_zero, hv_nonneg]);
    let abs_v_le_v = d.lemma(p.abs_le, &[v, v, refl_v, neg_v_le_v]);
    let v_le_abs_v = d.lemma(p.le_abs_self, &[v]);
    let abs_v = cabs(d, p, v);
    d.lemma(p.equiv_of_le_le, &[abs_v, v, abs_v_le_v, v_le_abs_v])
}

/// From `hv_nonneg : le zero v`, `h_bound_nonneg : le zero bound`, and
/// `h_le : le v bound`, derive `le (abs v) bound`.
fn abs_le_of_nonneg_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    hv_nonneg: ExprId,
    h_bound_nonneg: ExprId,
    h_le: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let nv = cneg(d, p, v);
    let neg_zero_c = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, v, hv_nonneg]);
    let nz_eq = neg_zero_equiv(d, p);
    let refl_nv = d.lemma(p.equiv_refl, &[nv]);
    let nv_le_zero = d.lemma(
        p.le_congr,
        &[nv, nv, neg_zero_c, zero_c, refl_nv, nz_eq, step1],
    );
    let nv_le_bound = d.lemma(p.le_trans, &[nv, zero_c, bound, nv_le_zero, h_bound_nonneg]);
    d.lemma(p.abs_le, &[v, bound, h_le, nv_le_bound])
}

/// `Equiv (mul (ofNat magnitude) (ofRat (natDivSucc 1 deep))) (ofRat
/// (natDivSucc 1 outer))`, given `magnitude = Nat.succ c` and `deep =
/// magnitude*outer + c` (built exactly that way — this is a syntactic
/// requirement, not just a numeric fact, since `Rat.natDivSucc_scale` is
/// applied at `(c, outer)` and its conclusion must match `deep` on the
/// nose). The exact rational collapse, lifted from `Rat` to `CReal` via
/// `nat_div_succ_mul`/`Nat.mul_one` and `CReal.ofRat_mul`.
fn magnitude_times_frac_eq_outer(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let mag_rat = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);
    let frac_rat = d.const_app(rat.nat_div_succ, &[one_nat, deep]);
    let mag_real = embed(d, p, mag_rat);
    let frac_real = embed(d, p, frac_rat);
    let product_real = cmul(d, p, mag_real, frac_real);

    let product_rat = rmul(d, mag_rat, frac_rat);
    let fused = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, deep])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[magnitude, one_nat, deep]);
    let collapsed = d.const_app(rat.nat_div_succ, &[magnitude, deep]);
    let collapse = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        let identity = d.lemma(nat.mul_one, &[magnitude]);
        nat_eq_to_rat(d, scaled, magnitude, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, deep])
        })
    };
    let outer_rat = d.const_app(rat.nat_div_succ, &[one_nat, outer]);
    let scale = d.lemma(rat.nat_div_succ_scale, &[c, outer]);
    // scale : Eq Rat (natDivSucc magnitude deep) (natDivSucc 1 outer),
    // PROVIDED `deep` is exactly `mul(magnitude, outer) + c`.

    let (_, chain) = rchain(
        d,
        product_rat,
        &[(fused, fuse), (collapsed, collapse), (outer_rat, scale)],
    );

    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[mag_rat, frac_rat]);
    rat_eq_rewrite(
        d,
        product_rat,
        outer_rat,
        chain,
        of_rat_mul_step,
        &|d, t| {
            let embedded = embed(d, p, t);
            equiv(d, p, product_real, embedded)
        },
    )
}

/// `le (mul diff (ofRat (natDivSucc 1 deep))) (ofRat (natDivSucc 1 outer))`,
/// given `diff_le_mag : le diff (ofNat magnitude)`, `magnitude = Nat.succ
/// c`, `deep = magnitude*outer + c`. The numeric heart of both the
/// per-piece step bound (`outer := mod_val`, `deep := m0`) and the final
/// Archimedean closing bound (`outer := e_outer`, `deep := e_acc`).
#[allow(clippy::too_many_arguments)]
fn step_le_outer_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    diff: ExprId,
    diff_le_mag: ExprId,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let frac_deep_rat = div_succ(d, p, 1, deep);
    let frac_deep = embed(d, p, frac_deep_rat);
    let frac_nonneg = {
        let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, deep]);
        d.lemma(p.of_rat_le, &[rzero_expr, frac_deep_rat, rle])
    };

    let step = cmul(d, p, diff, frac_deep);
    let diff_frac = cmul(d, p, frac_deep, diff);
    let comm1 = d.lemma(p.mul_comm, &[diff, frac_deep]);

    let om = d.const_app(p.of_nat, &[magnitude]);
    let mag_frac = cmul(d, p, frac_deep, om);
    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[frac_deep, diff, om, frac_nonneg, diff_le_mag],
    );

    let refl_mag_frac = d.lemma(p.equiv_refl, &[mag_frac]);
    // `scaled : le diff_frac mag_frac`; `le_congr`'s `hab : Equiv a b` needs
    // `a` to match `scaled`'s own LHS (`diff_frac`), so `comm1` (which runs
    // `step ~ diff_frac`) has to be flipped.
    let comm1_symm = d.lemma(p.equiv_symm, &[step, diff_frac, comm1]);
    let step_le_mag_frac = d.lemma(
        p.le_congr,
        &[
            diff_frac,
            step,
            mag_frac,
            mag_frac,
            comm1_symm,
            refl_mag_frac,
            scaled,
        ],
    );

    let frac_mag = cmul(d, p, om, frac_deep);
    let comm2 = d.lemma(p.mul_comm, &[frac_deep, om]);
    let collapse = magnitude_times_frac_eq_outer(d, p, c, magnitude, outer, deep);
    let out_bound_rat = div_succ(d, p, 1, outer);
    let out_bound = embed(d, p, out_bound_rat);
    let mag_frac_eq_out = d.lemma(
        p.equiv_trans,
        &[mag_frac, frac_mag, out_bound, comm2, collapse],
    );

    let refl_step = d.lemma(p.equiv_refl, &[step]);
    d.lemma(
        p.le_congr,
        &[
            step,
            step,
            mag_frac,
            out_bound,
            refl_step,
            mag_frac_eq_out,
            step_le_mag_frac,
        ],
    )
}

/// From `h : le (add aa (neg bb)) cc`, derive `le aa (add cc bb)` — shifting
/// a subtracted term across an inequality.
fn le_shift_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    aa: ExprId,
    bb: ExprId,
    cc: ExprId,
    h: ExprId,
) -> ExprId {
    let nb = cneg(d, p, bb);
    let a_nb = cadd(d, p, aa, nb);
    let a_nb_b = cadd(d, p, a_nb, bb);
    let c_b = cadd(d, p, cc, bb);

    let identity = {
        let nb_b = cadd(d, p, nb, bb);
        let assoc = d.lemma(p.add_assoc, &[aa, nb, bb]);
        let nas = neg_add_self(d, p, bb);
        let a_nbb = cadd(d, p, aa, nb_b);
        let zero_c = czero(d, p);
        let a_zero = cadd(d, p, aa, zero_c);
        let refl_a = d.lemma(p.equiv_refl, &[aa]);
        let congr1 = d.lemma(p.add_congr, &[aa, aa, nb_b, zero_c, refl_a, nas]);
        let az = d.lemma(p.add_zero, &[aa]);
        echain(d, p, a_nb_b, &[(a_nbb, assoc), (a_zero, congr1), (aa, az)])
    };

    let refl_b = d.lemma(p.le_refl, &[bb]);
    let grown = d.lemma(p.add_le_add, &[a_nb, cc, bb, bb, h, refl_b]);

    let refl_cb = d.lemma(p.equiv_refl, &[c_b]);
    d.lemma(
        p.le_congr,
        &[a_nb_b, aa, c_b, c_b, identity, refl_cb, grown],
    )
}

/// `CReal.monotone_of_nonneg_deriv : ∀ F F' a b, HasDerivativeOn F F' a b →
/// (∀ z, le a z → le z b → le zero (F' z)) → ∀ x y, le a x → le x y → le y b
/// → le (F x) (F y)`. See the module documentation for the subdivision
/// construction.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_monotone_of_nonneg_deriv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

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

    // hderiv : ∀ z, le a z → le z b → le zero (F' z).
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let zero_c = czero(d, p);
        let concl = cle(d, p, zero_c, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxy_ty = cle(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);

    // target : ∀ e_outer, le fx (add fy (ofRat (natDivSucc 1 e_outer))).
    let target = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ(d, p, 1, e);
        let qe = embed(d, p, qe_rat);
        let sum = cadd(d, p, fy, qe);
        let body = cle(d, p, fx, sum);
        d.pi_fv(e_fv, nat, body)
    };

    let diff = cdiff(d, p, y, x);
    let abs_diff = cabs(d, p, diff);
    let harch = d.lemma(p.archimedean, &[abs_diff]);

    let pred = {
        let n_fv = d.fresh_fvar();
        let nn = d.kernel().fvar(n_fv);
        let on = d.const_app(p.of_nat, &[nn]);
        let body = cle(d, p, abs_diff, on);
        d.lam_fv(n_fv, nat, body)
    };

    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hc_ty = {
            let oc = d.const_app(p.of_nat, &[c]);
            cle(d, p, abs_diff, oc)
        };
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);

        let magnitude = d.succ(c);
        let hc2 = {
            let oc = d.const_app(p.of_nat, &[c]);
            let om = d.const_app(p.of_nat, &[magnitude]);
            let le_succ_name = d.prelude().le_succ;
            let le_succ_c = d.const_app(le_succ_name, &[c]);
            let mono = d.lemma(p.of_nat_le, &[c, magnitude, le_succ_c]);
            d.lemma(p.le_trans, &[abs_diff, oc, om, hc, mono])
        };
        let diff_le_mag = {
            let om = d.const_app(p.of_nat, &[magnitude]);
            let le_abs = d.lemma(p.le_abs_self, &[diff]);
            d.lemma(p.le_trans, &[diff, abs_diff, om, le_abs, hc2])
        };

        let body = {
            let e_fv = d.fresh_fvar();
            let e_outer = d.kernel().fvar(e_fv);

            let me = NatOps::mul(d, magnitude, e_outer);
            let e_acc = NatOps::add(d, me, c);

            let mod_fn = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
            let mod_val = d.apply(mod_fn, &[e_acc]);

            let mm = NatOps::mul(d, magnitude, mod_val);
            let m0 = NatOps::add(d, mm, c);
            let big_k = d.succ(m0);

            let (step, step_nonneg) = step_nonneg_of(d, p, x, y, m0, hxy);

            // step_bound_le : le step (ofRat (natDivSucc 1 mod_val)).
            let step_bound_le =
                step_le_outer_bound(d, p, diff, diff_le_mag, c, magnitude, mod_val, m0);
            let in_bound_rat = div_succ(d, p, 1, mod_val);
            let in_bound = embed(d, p, in_bound_rat);
            let in_bound_nonneg = {
                let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
                let one_nat = d.num(1);
                let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, mod_val]);
                d.lemma(p.of_rat_le, &[rzero_expr, in_bound_rat, rle])
            };
            let within_step = abs_le_of_nonneg_le(
                d,
                p,
                step,
                in_bound,
                step_nonneg,
                in_bound_nonneg,
                step_bound_le,
            );

            let frac_e_acc_rat = div_succ(d, p, 1, e_acc);
            let frac_e_acc_real = embed(d, p, frac_e_acc_rat);
            let bound_val = cmul(d, p, frac_e_acc_real, step);
            let neg_bound_val = cneg(d, p, bound_val);

            // per-piece hypothesis : ∀ i, Nat.lt i K →
            //   le neg_bound_val (add (F(x_(succ i))) (neg (F x_i))).
            let per_piece = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hlt_ty = d.lt(i, big_k);
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);

                let x_i = sample_pt(d, p, x, step, i);
                let si = d.succ(i);
                let x_si = sample_pt(d, p, x, step, si);

                let hle_i_k = nat_le_of_lt(d, i, big_k, hlt);
                let bounds_i =
                    d.const_app(p.subdivision_point_in_bounds, &[x, y, m0, i, hxy, hle_i_k]);
                let x_le_xi = cle(d, p, x, x_i);
                let xi_le_y = cle(d, p, x_i, y);
                let x_le_xi_p = d.and_left(x_le_xi, xi_le_y, bounds_i);
                let xi_le_y_p = d.and_right(x_le_xi, xi_le_y, bounds_i);
                let a_le_xi = d.lemma(p.le_trans, &[a, x, x_i, hax, x_le_xi_p]);
                let xi_le_b = d.lemma(p.le_trans, &[x_i, y, b, xi_le_y_p, hyb]);

                // `hlt` is already `Nat.le (succ i) K` (defeq `Nat.lt i K`),
                // so it serves directly as the `hle` argument at `succ i`.
                let bounds_si =
                    d.const_app(p.subdivision_point_in_bounds, &[x, y, m0, si, hxy, hlt]);
                let x_le_xsi = cle(d, p, x, x_si);
                let xsi_le_y = cle(d, p, x_si, y);
                let x_le_xsi_p = d.and_left(x_le_xsi, xsi_le_y, bounds_si);
                let xsi_le_y_p = d.and_right(x_le_xsi, xsi_le_y, bounds_si);
                let a_le_xsi = d.lemma(p.le_trans, &[a, x, x_si, hax, x_le_xsi_p]);
                let xsi_le_b = d.lemma(p.le_trans, &[x_si, y, b, xsi_le_y_p, hyb]);

                let diff_i_eq_step = consecutive_diff_eq_step(d, p, x, step, i);
                let diff_i = {
                    let nxi = cneg(d, p, x_i);
                    cadd(d, p, x_si, nxi)
                };

                let within_diff_i = {
                    let abs_diff_i = cabs(d, p, diff_i);
                    let abs_step = cabs(d, p, step);
                    let abs_congr_step = d.lemma(p.abs_congr, &[diff_i, step, diff_i_eq_step]);
                    // abs_congr_step : Equiv abs_diff_i abs_step; le_congr's `hab`
                    // needs the other direction.
                    let abs_congr_step_symm =
                        d.lemma(p.equiv_symm, &[abs_diff_i, abs_step, abs_congr_step]);
                    let refl_in_bound = d.lemma(p.equiv_refl, &[in_bound]);
                    d.lemma(
                        p.le_congr,
                        &[
                            abs_step,
                            abs_diff_i,
                            in_bound,
                            in_bound,
                            abs_congr_step_symm,
                            refl_in_bound,
                            within_step,
                        ],
                    )
                };

                let error_bound = d.lemma(
                    p.hd_spec,
                    &[
                        f,
                        fp,
                        a,
                        b,
                        hf,
                        e_acc,
                        x_i,
                        x_si,
                        a_le_xi,
                        xi_le_b,
                        a_le_xsi,
                        xsi_le_b,
                        within_diff_i,
                    ],
                );
                // error_bound : le (abs error_diff) (mul frac_e_acc_real (abs diff_i))
                // error_diff = add (add (F x_si) (neg (F x_i))) (neg (mul (F' x_i) diff_i))

                let fpi = d.apply(fp, &[x_i]);
                let f_xi = d.apply(f, &[x_i]);
                let f_xsi = d.apply(f, &[x_si]);
                let dd = cdiff(d, p, f_xsi, f_xi); // D := F(x_si) - F(x_i)

                let p_diff = cmul(d, p, fpi, diff_i);
                let p_step = cmul(d, p, fpi, step);
                let error_diff = cdiff(d, p, dd, p_diff);
                let error_step = cdiff(d, p, dd, p_step);

                let error_eq = {
                    let refl_dd = d.lemma(p.equiv_refl, &[dd]);
                    let p_eq = {
                        let refl_fpi = d.lemma(p.equiv_refl, &[fpi]);
                        d.lemma(
                            p.mul_congr,
                            &[fpi, fpi, diff_i, step, refl_fpi, diff_i_eq_step],
                        )
                    };
                    let neg_p_eq = d.lemma(p.neg_congr, &[p_diff, p_step, p_eq]);
                    let neg_p_diff = cneg(d, p, p_diff);
                    let neg_p_step = cneg(d, p, p_step);
                    d.lemma(
                        p.add_congr,
                        &[dd, dd, neg_p_diff, neg_p_step, refl_dd, neg_p_eq],
                    )
                };

                let bound_eq = {
                    let abs_diff_i = cabs(d, p, diff_i);
                    let abs_step = cabs(d, p, step);
                    let abs_congr_step = d.lemma(p.abs_congr, &[diff_i, step, diff_i_eq_step]);
                    let mid = cmul(d, p, frac_e_acc_real, abs_step);
                    let step1 = {
                        let refl_frac = d.lemma(p.equiv_refl, &[frac_e_acc_real]);
                        d.lemma(
                            p.mul_congr,
                            &[
                                frac_e_acc_real,
                                frac_e_acc_real,
                                abs_diff_i,
                                abs_step,
                                refl_frac,
                                abs_congr_step,
                            ],
                        )
                    };
                    let abs_eq_step = abs_eq_self_of_nonneg(d, p, step, step_nonneg);
                    let step2 = {
                        let refl_frac = d.lemma(p.equiv_refl, &[frac_e_acc_real]);
                        d.lemma(
                            p.mul_congr,
                            &[
                                frac_e_acc_real,
                                frac_e_acc_real,
                                abs_step,
                                step,
                                refl_frac,
                                abs_eq_step,
                            ],
                        )
                    };
                    let bound_diff = cmul(d, p, frac_e_acc_real, abs_diff_i);
                    d.lemma(p.equiv_trans, &[bound_diff, mid, bound_val, step1, step2])
                };

                let error_bound2 = {
                    let abs_error_diff = cabs(d, p, error_diff);
                    let abs_error_step = cabs(d, p, error_step);
                    let abs_congr_err = d.lemma(p.abs_congr, &[error_diff, error_step, error_eq]);
                    let abs_diff_i_for_bound = cabs(d, p, diff_i);
                    let bound_diff = cmul(d, p, frac_e_acc_real, abs_diff_i_for_bound);
                    d.lemma(
                        p.le_congr,
                        &[
                            abs_error_diff,
                            abs_error_step,
                            bound_diff,
                            bound_val,
                            abs_congr_err,
                            bound_eq,
                            error_bound,
                        ],
                    )
                };
                // error_bound2 : le (abs error_step) bound_val

                let lower_error = lower_of_within(d, p, error_step, bound_val, error_bound2);
                // lower_error : le neg_bound_val error_step

                let refl_p_step = d.lemma(p.le_refl, &[p_step]);
                let grown = d.lemma(
                    p.add_le_add,
                    &[
                        p_step,
                        p_step,
                        neg_bound_val,
                        error_step,
                        refl_p_step,
                        lower_error,
                    ],
                );
                // grown : le (add p_step neg_bound_val) (add p_step error_step)

                let decompose = add_cancel_middle(d, p, dd, p_step);
                // decompose : Equiv (add p_step error_step) dd
                let lhs_expr = {
                    let np = cneg(d, p, bound_val);
                    cadd(d, p, p_step, np)
                };
                let p_step_error_step = cadd(d, p, p_step, error_step);
                let refl_lhs = d.lemma(p.equiv_refl, &[lhs_expr]);
                let transported = d.lemma(
                    p.le_congr,
                    &[
                        lhs_expr,
                        lhs_expr,
                        p_step_error_step,
                        dd,
                        refl_lhs,
                        decompose,
                        grown,
                    ],
                );
                // transported : le lhs_expr dd

                let fpi_nonneg = d.apply(hderiv, &[x_i, a_le_xi, xi_le_b]);
                let p_step_nonneg = d.lemma(p.mul_nonneg, &[fpi, step, fpi_nonneg, step_nonneg]);

                let zero_c = czero(d, p);
                let neg_bv = cneg(d, p, bound_val);
                let padded = cadd(d, p, zero_c, neg_bv);
                let refl_negbv = d.lemma(p.le_refl, &[neg_bv]);
                let grown0 = d.lemma(
                    p.add_le_add,
                    &[zero_c, p_step, neg_bv, neg_bv, p_step_nonneg, refl_negbv],
                );
                let za = zero_add_equiv(d, p, neg_bv);
                let refl_lhs2 = d.lemma(p.equiv_refl, &[lhs_expr]);
                let negbv_le_lhs = d.lemma(
                    p.le_congr,
                    &[padded, neg_bv, lhs_expr, lhs_expr, za, refl_lhs2, grown0],
                );

                let final_bound = d.lemma(
                    p.le_trans,
                    &[neg_bound_val, lhs_expr, dd, negbv_le_lhs, transported],
                );
                // final_bound : le neg_bound_val dd = le neg_bound_val (add (F x_si)(neg (F x_i)))

                let with_hlt = d.lam_fv(hlt_fv, hlt_ty, final_bound);
                d.lam_fv(i_fv, nat, with_hlt)
            };

            // f_pts := fun i => F (sample_pt x step i).
            let f_pts = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let x_i = sample_pt(d, p, x, step, i);
                let body = d.apply(f, &[x_i]);
                d.lam_fv(i_fv, nat, body)
            };

            let telescope = d.lemma(
                p.sum_range_telescope_ge,
                &[f_pts, neg_bound_val, big_k, per_piece],
            );
            // telescope : le (sumRange (const neg_bound_val) K)
            //   (add (f_pts K) (neg (f_pts Nat.zero)))

            let sum_eq = d.lemma(p.sum_range_const, &[neg_bound_val, m0]);
            // sum_eq : Equiv (sumRange (const neg_bound_val) K)
            //   (mul (ofNat K) neg_bound_val)
            let k_real = d.const_app(p.of_nat, &[big_k]);
            let k_times_negbv = cmul(d, p, k_real, neg_bound_val);
            let f_pts_k = {
                let x_k = sample_pt(d, p, x, step, big_k);
                d.apply(f, &[x_k])
            };
            let zero_n = d.zero();
            let f_pts_0 = {
                let x_0 = sample_pt(d, p, x, step, zero_n);
                d.apply(f, &[x_0])
            };
            let rhs0 = {
                let nf0 = cneg(d, p, f_pts_0);
                cadd(d, p, f_pts_k, nf0)
            };
            let telescope2 = {
                let refl_rhs = d.lemma(p.equiv_refl, &[rhs0]);
                let cf = const_fn(d, neg_bound_val);
                let sum_range_const_lhs = d.const_app(p.sum_range, &[cf, big_k]);
                d.lemma(
                    p.le_congr,
                    &[
                        sum_range_const_lhs,
                        k_times_negbv,
                        rhs0,
                        rhs0,
                        sum_eq,
                        refl_rhs,
                        telescope,
                    ],
                )
            };
            // telescope2 : le k_times_negbv rhs0

            let neg_step2 = mul_neg_right(d, p, k_real, bound_val);
            // neg_step2 : Equiv (mul k_real neg_bound_val) (neg (mul k_real bound_val))
            let k_times_bv = cmul(d, p, k_real, bound_val);
            let neg_ktbv = cneg(d, p, k_times_bv);
            let telescope3 = {
                let refl_rhs = d.lemma(p.equiv_refl, &[rhs0]);
                d.lemma(
                    p.le_congr,
                    &[
                        k_times_negbv,
                        neg_ktbv,
                        rhs0,
                        rhs0,
                        neg_step2,
                        refl_rhs,
                        telescope2,
                    ],
                )
            };
            // telescope3 : le neg_ktbv rhs0

            // KB_le : le k_times_bv (ofRat (natDivSucc 1 e_outer)).
            let kb_le = {
                // k_times_bv = mul k_real (mul frac_e_acc_real step)
                //   ~ mul frac_e_acc_real (mul k_real step)   [assoc/comm]
                //   ~ mul frac_e_acc_real diff                [mesh_count_width]
                //   ~ mul diff frac_e_acc_real                [comm]
                //   <= ofRat (natDivSucc 1 e_outer)            [step_le_outer_bound]
                let k_frac = cmul(d, p, k_real, frac_e_acc_real);
                let s1 = cmul(d, p, k_frac, step);
                let h1 = d.lemma(p.mul_assoc, &[k_real, frac_e_acc_real, step]);
                // h1 : Equiv s1 k_times_bv

                let frac_k = cmul(d, p, frac_e_acc_real, k_real);
                let s2 = cmul(d, p, frac_k, step);
                let h2 = {
                    let comm = d.lemma(p.mul_comm, &[k_real, frac_e_acc_real]);
                    let refl_step = d.lemma(p.equiv_refl, &[step]);
                    d.lemma(p.mul_congr, &[k_frac, frac_k, step, step, comm, refl_step])
                };
                // h2 : Equiv s1 s2

                let k_step = cmul(d, p, k_real, step);
                let s3 = cmul(d, p, frac_e_acc_real, k_step);
                let h3 = d.lemma(p.mul_assoc, &[frac_e_acc_real, k_real, step]);
                // h3 : Equiv s2 s3

                let mesh = d.lemma(p.mesh_count_width, &[diff, m0]);
                // mesh : Equiv k_step diff  (k_real = ofNat (succ m0) = ofNat K)
                let s4 = cmul(d, p, frac_e_acc_real, diff);
                let h4 = {
                    let refl_frac = d.lemma(p.equiv_refl, &[frac_e_acc_real]);
                    d.lemma(
                        p.mul_congr,
                        &[
                            frac_e_acc_real,
                            frac_e_acc_real,
                            k_step,
                            diff,
                            refl_frac,
                            mesh,
                        ],
                    )
                };
                // h4 : Equiv s3 s4

                let s5 = cmul(d, p, diff, frac_e_acc_real);
                let h5 = d.lemma(p.mul_comm, &[frac_e_acc_real, diff]);
                // h5 : Equiv s4 s5

                let k_times_bv_eq_s5 = {
                    // Equiv k_times_bv s5 by chaining s1..s5 and flipping h1.
                    let chain_s1_to_s5 =
                        echain(d, p, s1, &[(s2, h2), (s3, h3), (s4, h4), (s5, h5)]);
                    let h1_symm = d.lemma(p.equiv_symm, &[s1, k_times_bv, h1]);
                    d.lemma(
                        p.equiv_trans,
                        &[k_times_bv, s1, s5, h1_symm, chain_s1_to_s5],
                    )
                };

                let outer_bound =
                    step_le_outer_bound(d, p, diff, diff_le_mag, c, magnitude, e_outer, e_acc);
                // outer_bound : le s5 (ofRat (natDivSucc 1 e_outer))

                let out_bound_rat = div_succ(d, p, 1, e_outer);
                let out_bound = embed(d, p, out_bound_rat);
                let refl_out = d.lemma(p.equiv_refl, &[out_bound]);
                // outer_bound : le s5 out_bound. `le_congr`'s `hab : Equiv a
                // b` needs `a` to match `outer_bound`'s own LHS (`s5`), and
                // the RESULT's `b` slot is what becomes the new left side.
                let k_times_bv_eq_s5_symm =
                    d.lemma(p.equiv_symm, &[k_times_bv, s5, k_times_bv_eq_s5]);
                d.lemma(
                    p.le_congr,
                    &[
                        s5,
                        k_times_bv,
                        out_bound,
                        out_bound,
                        k_times_bv_eq_s5_symm,
                        refl_out,
                        outer_bound,
                    ],
                )
            };
            // kb_le : le k_times_bv (ofRat (natDivSucc 1 e_outer))

            let out_bound_rat = div_succ(d, p, 1, e_outer);
            let out_bound = embed(d, p, out_bound_rat);
            let neg_out_bound = cneg(d, p, out_bound);

            let neg_kb = d.lemma(p.neg_le_neg, &[k_times_bv, out_bound, kb_le]);
            // neg_kb : le (neg out_bound) (neg k_times_bv) = le neg_out_bound neg_ktbv

            let chained = d.lemma(
                p.le_trans,
                &[neg_out_bound, neg_ktbv, rhs0, neg_kb, telescope3],
            );
            // chained : le neg_out_bound rhs0

            // Transport rhs0 = add f_pts_k (neg f_pts_0) into add fy (neg fx)
            // via hasDerivative_closeOfEquiv at BOTH ends.
            let x_0 = sample_pt(d, p, x, step, zero_n);
            let x_0_eq_x = {
                let of_nat_0_eq_zero = of_nat_zero_equiv_local(d, p);
                let of_nat_0 = d.const_app(p.of_nat, &[zero_n]);
                let u0 = cmul(d, p, of_nat_0, step);
                let zero_c = czero(d, p);
                let u0_eq_zero = {
                    let step_zero = cmul(d, p, step, zero_c);
                    let refl_step = d.lemma(p.equiv_refl, &[step]);
                    let comm = d.lemma(p.mul_comm, &[of_nat_0, step]);
                    let congr1 = d.lemma(
                        p.mul_congr,
                        &[step, step, of_nat_0, zero_c, refl_step, of_nat_0_eq_zero],
                    );
                    let mz = d.lemma(p.mul_zero, &[step]);
                    let u0_step0 = cmul(d, p, step, of_nat_0);
                    echain(
                        d,
                        p,
                        u0,
                        &[(u0_step0, comm), (step_zero, congr1), (zero_c, mz)],
                    )
                };
                let x_u0 = cadd(d, p, x, u0);
                let x_zero = cadd(d, p, x, zero_c);
                let congr2 = {
                    let refl_x = d.lemma(p.equiv_refl, &[x]);
                    d.lemma(p.add_congr, &[x, x, u0, zero_c, refl_x, u0_eq_zero])
                };
                let az = d.lemma(p.add_zero, &[x]);
                echain(d, p, x_u0, &[(x_zero, congr2), (x, az)])
            };

            let x_k = sample_pt(d, p, x, step, big_k);
            let x_k_eq_y = {
                let mesh = d.lemma(p.mesh_count_width, &[diff, m0]);
                // mesh : Equiv (mul k_real step) diff
                let k_step = cmul(d, p, k_real, step);
                let x_kstep = cadd(d, p, x, k_step);
                let x_diff = cadd(d, p, x, diff);
                let congr3 = {
                    let refl_x = d.lemma(p.equiv_refl, &[x]);
                    d.lemma(p.add_congr, &[x, x, k_step, diff, refl_x, mesh])
                };
                let cancel = add_sub_cancel(d, p, x, y);
                echain(d, p, x_kstep, &[(x_diff, congr3), (y, cancel)])
            };

            // bounds for x_0 and x_k, needed by hasDerivative_closeOfEquiv.
            let zero_le_k = {
                let np = d.prelude();
                d.const_app(np.zero_le, &[big_k])
            };
            let bounds_0 = d.const_app(
                p.subdivision_point_in_bounds,
                &[x, y, m0, zero_n, hxy, zero_le_k],
            );
            let x_le_x0 = cle(d, p, x, x_0);
            let x0_le_y = cle(d, p, x_0, y);
            let x_le_x0_p = d.and_left(x_le_x0, x0_le_y, bounds_0);
            let x0_le_y_p = d.and_right(x_le_x0, x0_le_y, bounds_0);
            let a_le_x0 = d.lemma(p.le_trans, &[a, x, x_0, hax, x_le_x0_p]);
            let x0_le_b = d.lemma(p.le_trans, &[x_0, y, b, x0_le_y_p, hyb]);

            let le_k_refl = {
                let np = d.prelude();
                d.const_app(np.le_refl, &[big_k])
            };
            let bounds_k = d.const_app(
                p.subdivision_point_in_bounds,
                &[x, y, m0, big_k, hxy, le_k_refl],
            );
            let x_le_xk = cle(d, p, x, x_k);
            let xk_le_y = cle(d, p, x_k, y);
            let x_le_xk_p = d.and_left(x_le_xk, xk_le_y, bounds_k);
            let xk_le_y_p = d.and_right(x_le_xk, xk_le_y, bounds_k);
            let a_le_xk = d.lemma(p.le_trans, &[a, x, x_k, hax, x_le_xk_p]);
            let xk_le_b = d.lemma(p.le_trans, &[x_k, y, b, xk_le_y_p, hyb]);

            let a_le_x = hax;
            let x_le_b = d.lemma(p.le_trans, &[x, y, b, hxy, hyb]);

            let f_x0_eq_fx = d.lemma(
                p.has_derivative_close_of_equiv,
                &[
                    f, fp, a, b, hf, x_0, x, a_le_x0, x0_le_b, a_le_x, x_le_b, x_0_eq_x,
                ],
            );
            let a_le_y = d.lemma(p.le_trans, &[a, x, y, hax, hxy]);
            let f_xk_eq_fy = d.lemma(
                p.has_derivative_close_of_equiv,
                &[
                    f, fp, a, b, hf, x_k, y, a_le_xk, xk_le_b, a_le_y, hyb, x_k_eq_y,
                ],
            );

            let rhs_eq = {
                let nf_x0 = cneg(d, p, f_pts_0);
                let nfx = cneg(d, p, fx);
                let neg_congr_step = d.lemma(p.neg_congr, &[f_pts_0, fx, f_x0_eq_fx]);
                d.lemma(
                    p.add_congr,
                    &[f_pts_k, fy, nf_x0, nfx, f_xk_eq_fy, neg_congr_step],
                )
            };
            // rhs_eq : Equiv rhs0 (add fy (neg fx))

            let rhs_target = cdiff(d, p, fy, fx);
            let chained2 = {
                let refl_neg_out = d.lemma(p.equiv_refl, &[neg_out_bound]);
                d.lemma(
                    p.le_congr,
                    &[
                        neg_out_bound,
                        neg_out_bound,
                        rhs0,
                        rhs_target,
                        refl_neg_out,
                        rhs_eq,
                        chained,
                    ],
                )
            };
            // chained2 : le neg_out_bound (add fy (neg fx))

            // Shift `fx` across: le (add neg_out_bound fx) (add rhs_target fx),
            // then simplify (add rhs_target fx) ~ fy and commute the LHS into
            // the `le (add A (neg B)) C` shape `le_shift_add` expects.
            let shifted_by_fx = {
                let refl_fx = d.lemma(p.le_refl, &[fx]);
                d.lemma(
                    p.add_le_add,
                    &[neg_out_bound, rhs_target, fx, fx, chained2, refl_fx],
                )
            };
            // shifted_by_fx : le (add neg_out_bound fx) (add rhs_target fx)

            let rhs_target_fx_eq_fy = {
                let nfx = cneg(d, p, fx);
                let nfx_fx = cadd(d, p, nfx, fx);
                let fy_nfxfx = cadd(d, p, fy, nfx_fx);
                let rhs_target_fx = cadd(d, p, rhs_target, fx);
                // add_assoc(fy, nfx, fx) : Equiv (add (add fy nfx) fx)
                //   (add fy (add nfx fx)) = Equiv rhs_target_fx fy_nfxfx.
                let assoc_r = d.lemma(p.add_assoc, &[fy, nfx, fx]);
                let nas_fx = neg_add_self(d, p, fx);
                let zero_c2 = czero(d, p);
                let fy_zero = cadd(d, p, fy, zero_c2);
                let congr_r = {
                    let refl_fy = d.lemma(p.equiv_refl, &[fy]);
                    d.lemma(p.add_congr, &[fy, fy, nfx_fx, zero_c2, refl_fy, nas_fx])
                };
                let az_fy = d.lemma(p.add_zero, &[fy]);
                echain(
                    d,
                    p,
                    rhs_target_fx,
                    &[(fy_nfxfx, assoc_r), (fy_zero, congr_r), (fy, az_fy)],
                )
            };
            // rhs_target_fx_eq_fy : Equiv (add rhs_target fx) fy

            let comm_lhs = d.lemma(p.add_comm, &[neg_out_bound, fx]);
            // comm_lhs : Equiv (add neg_out_bound fx) (add fx neg_out_bound)

            let negoutbound_fx = cadd(d, p, neg_out_bound, fx);
            let fx_negoutbound = cadd(d, p, fx, neg_out_bound);
            let rhs_target_fx = cadd(d, p, rhs_target, fx);
            let final_hyp = d.lemma(
                p.le_congr,
                &[
                    negoutbound_fx,
                    fx_negoutbound,
                    rhs_target_fx,
                    fy,
                    comm_lhs,
                    rhs_target_fx_eq_fy,
                    shifted_by_fx,
                ],
            );
            // final_hyp : le (add fx (neg out_bound)) fy

            let final_step = le_shift_add(d, p, fx, out_bound, fy, final_hyp);
            // final_step : le fx (add fy out_bound) = target's body at e_outer

            d.lam_fv(e_fv, nat, final_step)
        };

        let with_hc = d.lam_fv(hc_fv, hc_ty, body);
        d.lam_fv(c_fv, nat, with_hc)
    };

    let inner_proof = exists_elim(d, pred, target, harch, minor);
    let value_body = d.lemma(p.le_of_forall_le_add_small, &[fx, fy, inner_proof]);

    let value = {
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, value_body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hyb);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        let with_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, with_x);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hderiv);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let concl = cle(d, p, fx, fy);
        let after_hyb = d.arrow(hyb_ty, concl);
        let after_hxy = d.arrow(hxy_ty, after_hyb);
        let after_hax = d.arrow(hax_ty, after_hxy);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let after_hderiv = d.arrow(hderiv_ty, over_x);
        let after_hf = d.arrow(hf_ty, after_hderiv);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.monotone_of_nonneg_deriv,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`declare_sum_range_const`], [`declare_mesh_count_width`],
/// [`declare_subdivision_point_in_bounds`],
/// `CReal.monotone_of_nonneg_deriv` itself, and its two Spivak-ch.-11
/// corollaries [`declare_constant_of_zero_deriv`] and
/// [`declare_antitone_of_nonpos_deriv`] (both need
/// `CReal.monotone_of_nonneg_deriv`, so they cannot land any earlier).
/// Called from `creal.rs`'s pipeline AFTER `integral::declare_integral`
/// (for `CReal.ofNat_le`) — separately from [`declare_monotone`], which
/// runs earlier and has no such dependency.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_monotone_of_nonneg_deriv_all(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_const(d, p)?;
    declare_mesh_count_width(d, p)?;
    declare_subdivision_point_in_bounds(d, p)?;
    declare_monotone_of_nonneg_deriv(d, p)?;
    declare_constant_of_zero_deriv(d, p)?;
    declare_antitone_of_nonpos_deriv(d, p)
}

// =============================================================================
// `CReal.constant_of_zero_deriv` and `CReal.antitone_of_nonpos_deriv`
// =============================================================================
//
// Spivak ch. 11's other two corollaries of "the significance of the
// derivative", both without the Mean Value Theorem (unavailable here — it
// rests on the extreme value theorem, not constructively provable) and
// without ever case-splitting on `CReal.le` (undecidable):
//
// - `constant_of_zero_deriv` applies `monotone_of_nonneg_deriv` TWICE: once
//   to `F` directly (`le (F x) (F y)`), once to `neg ∘ F` via
//   `hasDerivative_neg` (`le (neg (F x)) (neg (F y))`, flipped by
//   `neg_le_neg` + double negation to `le (F y) (F x)`) — then
//   `equiv_of_le_le` closes the pair into `Equiv (F x) (F y)`. Each
//   application's nonnegative-derivative hypothesis comes from the SAME
//   `Equiv (F' z) zero` hypothesis, read as `le zero (F' z)` directly
//   (`equiv_symm` + `le_of_equiv`) and, for the negated copy, as
//   `le zero (neg (F' z))` (`neg_congr` against `neg_zero_equiv`, then the
//   same `equiv_symm` + `le_of_equiv`).
// - `antitone_of_nonpos_deriv` is exactly the SECOND half of that trick
//   generalized to an arbitrary (not merely zero) sign hypothesis: a
//   nonpositive derivative for `F` (`le (F' z) zero`) is a nonnegative
//   derivative for `neg ∘ F` (`neg_le_neg` against `neg_zero_equiv`, via
//   `le_congr` rather than an `Equiv` chain since the hypothesis is only an
//   inequality), so `monotone_of_nonneg_deriv` applied to `neg ∘ F` gives
//   `le (neg (F x)) (neg (F y))`, flipped the same way to `le (F y) (F x)`.

/// `CReal.constant_of_zero_deriv : ∀ F F' a b, HasDerivativeOn F F' a b →
/// (∀ z, le a z → le z b → Equiv (F' z) zero) → ∀ x y, le a x → le x y →
/// le y b → Equiv (F x) (F y)`. See the block comment above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_constant_of_zero_deriv(
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

    // hderiv : ∀ z, le a z → le z b → Equiv (F' z) zero.
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let zero_c = czero(d, p);
        let concl = equiv(d, p, fpz, zero_c);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxy_ty = cle(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);

    // Direction 1: le fx fy, from `monotone_of_nonneg_deriv` applied to F
    // directly.
    let le_fx_fy = {
        let hderiv_pos = {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let haz_fv = d.fresh_fvar();
            let haz = d.kernel().fvar(haz_fv);
            let hzb_fv = d.fresh_fvar();
            let hzb = d.kernel().fvar(hzb_fv);
            let hz_equiv = d.apply(hderiv, &[z, haz, hzb]); // Equiv (F' z) zero
            let zero_c = czero(d, p);
            let fpz = d.apply(fp, &[z]);
            let hz_equiv_symm = esymm(d, p, fpz, zero_c, hz_equiv); // Equiv zero (F' z)
            let body = d.lemma(p.le_of_equiv, &[zero_c, fpz, hz_equiv_symm]); // le zero (F' z)
            let a_le_z = cle(d, p, a, z);
            let z_le_b = cle(d, p, z, b);
            let with_hzb = d.lam_fv(hzb_fv, z_le_b, body);
            let with_haz = d.lam_fv(haz_fv, a_le_z, with_hzb);
            d.lam_fv(z_fv, carrier, with_haz)
        };
        d.lemma(
            p.monotone_of_nonneg_deriv,
            &[f, fp, a, b, hf, hderiv_pos, x, y, hax, hxy, hyb],
        )
    };

    // Direction 2: le fy fx, from `monotone_of_nonneg_deriv` applied to
    // `neg ∘ F` (via `hasDerivative_neg`), then flipped back by `neg_le_neg`
    // + double negation.
    let le_fy_fx = {
        let neg_f = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let fr = d.apply(f, &[r]);
            let nfr = cneg(d, p, fr);
            d.lam_fv(r_fv, carrier, nfr)
        };
        let neg_fp = {
            let x2_fv = d.fresh_fvar();
            let x2 = d.kernel().fvar(x2_fv);
            let fpx2 = d.apply(fp, &[x2]);
            let nfpx2 = cneg(d, p, fpx2);
            d.lam_fv(x2_fv, carrier, nfpx2)
        };
        let hf_neg = d.lemma(p.has_derivative_neg, &[f, fp, a, b, hf]);

        let hderiv_neg_pos = {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let haz_fv = d.fresh_fvar();
            let haz = d.kernel().fvar(haz_fv);
            let hzb_fv = d.fresh_fvar();
            let hzb = d.kernel().fvar(hzb_fv);
            let hz_equiv = d.apply(hderiv, &[z, haz, hzb]); // Equiv (F' z) zero
            let fpz = d.apply(fp, &[z]);
            let zero_c = czero(d, p);
            let neg_fpz = cneg(d, p, fpz);
            let neg_zero_c = cneg(d, p, zero_c);
            let nc = d.lemma(p.neg_congr, &[fpz, zero_c, hz_equiv]); // Equiv (neg fpz) (neg zero)
            let nz_eq = neg_zero_equiv(d, p); // Equiv (neg zero) zero
            let neg_fpz_equiv_zero = echain(d, p, neg_fpz, &[(neg_zero_c, nc), (zero_c, nz_eq)]);
            let neg_fpz_equiv_zero_symm = esymm(d, p, neg_fpz, zero_c, neg_fpz_equiv_zero);
            let body = d.lemma(p.le_of_equiv, &[zero_c, neg_fpz, neg_fpz_equiv_zero_symm]); // le zero (neg (F' z))
            let a_le_z = cle(d, p, a, z);
            let z_le_b = cle(d, p, z, b);
            let with_hzb = d.lam_fv(hzb_fv, z_le_b, body);
            let with_haz = d.lam_fv(haz_fv, a_le_z, with_hzb);
            d.lam_fv(z_fv, carrier, with_haz)
        };

        let le_neg_fx_neg_fy = d.lemma(
            p.monotone_of_nonneg_deriv,
            &[
                neg_f,
                neg_fp,
                a,
                b,
                hf_neg,
                hderiv_neg_pos,
                x,
                y,
                hax,
                hxy,
                hyb,
            ],
        );
        // le_neg_fx_neg_fy : le (neg_f x) (neg_f y), beta-equal to
        // le (neg fx) (neg fy).
        let neg_fx = cneg(d, p, fx);
        let neg_fy = cneg(d, p, fy);
        let flipped = d.lemma(p.neg_le_neg, &[neg_fx, neg_fy, le_neg_fx_neg_fy]);
        // flipped : le (neg (neg fy)) (neg (neg fx))
        let nn_fy = cneg(d, p, neg_fy);
        let nn_fx = cneg(d, p, neg_fx);
        let dn_fy = double_neg(d, p, fy); // Equiv (neg (neg fy)) fy
        let dn_fx = double_neg(d, p, fx); // Equiv (neg (neg fx)) fx
        d.lemma(p.le_congr, &[nn_fy, fy, nn_fx, fx, dn_fy, dn_fx, flipped])
    };

    let value_body = d.lemma(p.equiv_of_le_le, &[fx, fy, le_fx_fy, le_fy_fx]);

    let value = {
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, value_body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hyb);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        let with_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, with_x);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hderiv);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let concl = equiv(d, p, fx, fy);
        let after_hyb = d.arrow(hyb_ty, concl);
        let after_hxy = d.arrow(hxy_ty, after_hyb);
        let after_hax = d.arrow(hax_ty, after_hxy);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let after_hderiv = d.arrow(hderiv_ty, over_x);
        let after_hf = d.arrow(hf_ty, after_hderiv);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.constant_of_zero_deriv,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.antitone_of_nonpos_deriv : ∀ F F' a b, HasDerivativeOn F F' a b →
/// (∀ z, le a z → le z b → le (F' z) zero) → ∀ x y, le a x → le x y → le y b
/// → le (F y) (F x)`. See the block comment above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_antitone_of_nonpos_deriv(
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

    // hderiv : ∀ z, le a z → le z b → le (F' z) zero.
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let zero_c = czero(d, p);
        let concl = cle(d, p, fpz, zero_c);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxy_ty = cle(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);

    let neg_f = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let nfr = cneg(d, p, fr);
        d.lam_fv(r_fv, carrier, nfr)
    };
    let neg_fp = {
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let fpx2 = d.apply(fp, &[x2]);
        let nfpx2 = cneg(d, p, fpx2);
        d.lam_fv(x2_fv, carrier, nfpx2)
    };
    let hf_neg = d.lemma(p.has_derivative_neg, &[f, fp, a, b, hf]);

    // hderiv_pos : ∀ z, le a z → le z b → le zero (neg (F' z)), from the
    // nonpositive hypothesis via `neg_le_neg` against `neg_zero_equiv`.
    let hderiv_pos = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_fv = d.fresh_fvar();
        let haz = d.kernel().fvar(haz_fv);
        let hzb_fv = d.fresh_fvar();
        let hzb = d.kernel().fvar(hzb_fv);
        let h_nonpos = d.apply(hderiv, &[z, haz, hzb]); // le (F' z) zero
        let fpz = d.apply(fp, &[z]);
        let zero_c = czero(d, p);
        let neg_fpz = cneg(d, p, fpz);
        let neg_zero_c = cneg(d, p, zero_c);
        let step = d.lemma(p.neg_le_neg, &[fpz, zero_c, h_nonpos]); // le (neg zero) (neg fpz)
        let nz_eq = neg_zero_equiv(d, p); // Equiv (neg zero) zero
        let refl_neg_fpz = erefl(d, p, neg_fpz);
        let body = d.lemma(
            p.le_congr,
            &[
                neg_zero_c,
                zero_c,
                neg_fpz,
                neg_fpz,
                nz_eq,
                refl_neg_fpz,
                step,
            ],
        ); // le zero (neg (F' z))
        let a_le_z = cle(d, p, a, z);
        let z_le_b = cle(d, p, z, b);
        let with_hzb = d.lam_fv(hzb_fv, z_le_b, body);
        let with_haz = d.lam_fv(haz_fv, a_le_z, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let le_neg_fx_neg_fy = d.lemma(
        p.monotone_of_nonneg_deriv,
        &[neg_f, neg_fp, a, b, hf_neg, hderiv_pos, x, y, hax, hxy, hyb],
    );
    let neg_fx = cneg(d, p, fx);
    let neg_fy = cneg(d, p, fy);
    let flipped = d.lemma(p.neg_le_neg, &[neg_fx, neg_fy, le_neg_fx_neg_fy]);
    let nn_fy = cneg(d, p, neg_fy);
    let nn_fx = cneg(d, p, neg_fx);
    let dn_fy = double_neg(d, p, fy);
    let dn_fx = double_neg(d, p, fx);
    let value_body = d.lemma(p.le_congr, &[nn_fy, fy, nn_fx, fx, dn_fy, dn_fx, flipped]);

    let value = {
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, value_body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hyb);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        let with_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, with_x);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hderiv);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let concl = cle(d, p, fy, fx);
        let after_hyb = d.arrow(hyb_ty, concl);
        let after_hxy = d.arrow(hxy_ty, after_hyb);
        let after_hax = d.arrow(hax_ty, after_hxy);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let after_hderiv = d.arrow(hderiv_ty, over_x);
        let after_hf = d.arrow(hf_ty, after_hderiv);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.antitone_of_nonpos_deriv,
        uparams: vec![],
        ty,
        value,
    })
}
