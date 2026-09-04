//! **Detachable subsets, counting measure, and the Dirac space** — the
//! predicative base case, following Petrakis and Zeuner (*Pre-measure spaces
//! and pre-integration spaces in predicative Bishop–Cheng measure theory*,
//! arXiv:2207.08684) rather than Bishop–Cheng directly.
//!
//! ## Why this file exists
//!
//! The objection this shelf is supposed to answer is that *membership in a
//! measurable set is undecidable, so an indicator is not `Bool`-valued*. The
//! answer is not to weaken the indicator to a `[0,1]`-valued function and
//! live with it (which is what
//! [`IntSpace.Indicator`](super::IntSpacePrelude::indicator) alone does); it
//! is to make the SET the positive object. A **complemented** subset is a
//! pair of predicates carried with a witness that they are apart, and its
//! indicator is then a genuine function — the difference of two indicator
//! functions — with no decision anywhere.
//!
//! The base case, and the one this file builds, is the **detachable** subset:
//! membership IS decidable, so the subset is literally a `Nat → Bool` and its
//! indicator is `boolIndicator ∘ A`. Everything about it computes.
//!
//! ## What lands here
//!
//! - [`declare_bool_indicator`] and its two bounds, by `Bool.rec` — the two
//!   cases are `0 ≤ 0` and `0 ≤ 1`, and `0 ≤ 1` and `1 ≤ 1`.
//! - `IntSpace.detachable_is_indicator`: **every detachable subset of a
//!   finite index set is an integrable set of `IntSpace.crealFinite`**, with
//!   the integrability datum `IntSpace.Triv.mk`. Positive, first-class, and
//!   no side condition is discharged by hand at the use site.
//! - `IntSpace.countingMeasure`, with nonnegativity and the bound by the
//!   index count, both as instances of the generic measure theorems.
//! - `IntSpace.crealDirac k` — the **Dirac integration space**: `∫f = f k`,
//!   `total = 1`. A probability space, sixteen fields, and every law field is
//!   `Equiv.refl` or one existing lemma. It is the cheapest possible witness
//!   that the record is not secretly about intervals.
//!
//! ## What this file does NOT do
//!
//! It does not build complemented subsets of ℝ. A complemented subset of an
//! interval whose indicator is *integrable in `crealInterval`'s sense* must
//! have a uniformly continuous indicator, and a uniformly continuous
//! `{0,1}`-valued function on a connected interval is constant — so the only
//! integrable sets of `crealInterval` in the current design are the trivial
//! ones. That is not a defect of complemented subsets; it is the reason
//! Petrakis–Zeuner take L¹ to be the **completion** of the pre-integration
//! space rather than the pre-integration space itself. See ADR-1612 for the
//! measurement of what that completion would reuse.

use super::{
    FCONST, FLE, INTEGRABLE, INTEGRAL, IntSpacePrelude, TOTAL, definition, radd, req, rle, rmul,
    rone, rrefl, rsymm, rty, rzero, theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_bool_indicator(d, p)?;
    declare_bool_indicator_nonneg(d, p)?;
    declare_bool_indicator_le_one(d, p)?;
    declare_detachable_indicator(d, p)?;
    declare_detachable_is_indicator(d, p)?;
    declare_counting_measure(d, p)?;
    declare_counting_measure_nonneg(d, p)?;
    declare_counting_measure_le_total(d, p)?;
    declare_creal_dirac(d, p)?;
    declare_creal_dirac_integral(d, p)?;
    declare_creal_dirac_total(d, p)?;
    declare_dirac_measure_detachable(d, p)?;
    Ok(())
}

/// `Bool.rec.{1} (fun _ => CReal) on_false on_true condition`.
fn bool_select_creal(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    use crate::BinderInfo;
    let bool_ty = d.bool_ty();
    let r = rty(d, p.creal);
    let anon = d.kernel().anon();
    let motive = d.kernel().lam(anon, bool_ty, r, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = p.creal.rat.int.logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `IntSpace.boolIndicator : Bool → CReal := fun b => if b then 1 else 0`.
fn declare_bool_indicator(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let bool_ty = d.bool_ty();
    let r = rty(d, c);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let one = rone(d, c);
    let zero = rzero(d, c);
    let body = bool_select_creal(d, p, b, one, zero);
    let value = d.lam_fv(b_fv, bool_ty, body);
    let ty = d.arrow(bool_ty, r);
    definition(d, p.bool_indicator, ty, value)
}

/// `Bool.rec.{0}` at a `Prop` motive, with `on_true` and `on_false` given.
fn bool_cases_prop(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    motive: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    condition: ExprId,
) -> ExprId {
    let zero = d.kernel().level_zero();
    let bool_rec = p.creal.rat.int.logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![zero]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `IntSpace.boolIndicator_nonneg : ∀ b, CReal.le CReal.zero
/// (IntSpace.boolIndicator b)`.
fn declare_bool_indicator_nonneg(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let bool_ty = d.bool_ty();
    let zero = rzero(d, c);
    let one = rone(d, c);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ind_b = d.const_app(p.bool_indicator, &[b]);
    let concl = rle(d, c, zero, ind_b);

    let motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let ind = d.const_app(p.bool_indicator, &[m]);
        let body = rle(d, c, zero, ind);
        d.lam_fv(m_fv, bool_ty, body)
    };
    let on_true = {
        let lt = d.kernel().const_(c.zero_lt_one, vec![]);
        d.lemma(c.le_of_lt, &[zero, one, lt])
    };
    let on_false = d.lemma(c.le_refl, &[zero]);
    let body = bool_cases_prop(d, p, motive, on_true, on_false, b);

    let value = d.lam_fv(b_fv, bool_ty, body);
    let ty = d.pi_fv(b_fv, bool_ty, concl);
    theorem(d, p.bool_indicator_nonneg, ty, value)
}

/// `IntSpace.boolIndicator_le_one : ∀ b,
/// CReal.le (IntSpace.boolIndicator b) CReal.one`.
fn declare_bool_indicator_le_one(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let bool_ty = d.bool_ty();
    let zero = rzero(d, c);
    let one = rone(d, c);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ind_b = d.const_app(p.bool_indicator, &[b]);
    let concl = rle(d, c, ind_b, one);

    let motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let ind = d.const_app(p.bool_indicator, &[m]);
        let body = rle(d, c, ind, one);
        d.lam_fv(m_fv, bool_ty, body)
    };
    let on_true = d.lemma(c.le_refl, &[one]);
    let on_false = {
        let lt = d.kernel().const_(c.zero_lt_one, vec![]);
        d.lemma(c.le_of_lt, &[zero, one, lt])
    };
    let body = bool_cases_prop(d, p, motive, on_true, on_false, b);

    let value = d.lam_fv(b_fv, bool_ty, body);
    let ty = d.pi_fv(b_fv, bool_ty, concl);
    theorem(d, p.bool_indicator_le_one, ty, value)
}

/// The type `Nat → Bool`, and the term `fun i => boolIndicator (A i)`.
fn subset_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `IntSpace.detachableIndicator : (Nat → Bool) → Nat → CReal
/// := fun A i => IntSpace.boolIndicator (A i)`.
fn declare_detachable_indicator(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let r = rty(d, c);
    let sub = subset_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ai = d.apply(a, &[i]);
    let body = d.const_app(p.bool_indicator, &[ai]);

    let value = {
        let t = d.lam_fv(i_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let inner = d.arrow(nat, r);
        d.arrow(sub, inner)
    };
    definition(d, p.detachable_indicator, ty, value)
}

/// `IntSpace.detachable_is_indicator : ∀ A m,
/// IntSpace.Indicator (IntSpace.crealFinite m)
///   (IntSpace.detachableIndicator A)`.
///
/// **Every detachable subset of a finite index set is an integrable set.**
/// The integrability datum is `IntSpace.Triv.mk`; nothing is decided, and
/// nothing is discharged at the use site.
fn declare_detachable_is_indicator(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let sub = subset_ty(d);
    let natp = d.prelude();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);

    let space = d.const_app(p.creal_finite, &[m]);
    let chi = d.const_app(p.detachable_indicator, &[a]);

    // `fle (fconst 0) chi` and `fle chi (fconst 1)`, spelled out so the two
    // `And` sides have the exact types `IntSpace.Indicator` unfolds to.
    let zero = rzero(d, c);
    let one = rone(d, c);
    let fconst = {
        let sel = d.kernel().const_(p.record.sel(FCONST), vec![]);
        d.apply(sel, &[space])
    };
    let c0 = d.apply(fconst, &[zero]);
    let c1 = d.apply(fconst, &[one]);
    let fle = {
        let sel = d.kernel().const_(p.record.sel(FLE), vec![]);
        d.apply(sel, &[space])
    };
    let lo = d.apply(fle, &[c0, chi]);
    let hi = d.apply(fle, &[chi, c1]);

    let lo_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let ai = d.apply(a, &[i]);
        let body = d.lemma(p.bool_indicator_nonneg, &[ai]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, lt, body);
        d.lam_fv(i_fv, nat, body)
    };
    let hi_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let ai = d.apply(a, &[i]);
        let body = d.lemma(p.bool_indicator_le_one, &[ai]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, lt, body);
        d.lam_fv(i_fv, nat, body)
    };

    let intro = c.rat.int.logic.and_intro;
    let value = {
        let body = d.const_app(intro, &[lo, hi, lo_proof, hi_proof]);
        let t = d.lam_fv(m_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let concl = d.const_app(p.indicator, &[space, chi]);
        let t = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(a_fv, sub, t)
    };
    theorem(d, p.detachable_is_indicator, ty, value)
}

/// `IntSpace.countingMeasure : (Nat → Bool) → Nat → CReal
/// := fun A m => IntSpace.measure (IntSpace.crealFinite m)
///      (IntSpace.detachableIndicator A) IntSpace.Triv.mk` — the number of
/// indices below `succ m` that `A` accepts, obtained as an INTEGRAL and not
/// as a cardinality function.
fn declare_counting_measure(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let r = rty(d, c);
    let sub = subset_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let space = d.const_app(p.creal_finite, &[m]);
    let chi = d.const_app(p.detachable_indicator, &[a]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let body = d.const_app(p.measure, &[space, chi, triv_mk]);

    let value = {
        let t = d.lam_fv(m_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let inner = d.arrow(nat, r);
        d.arrow(sub, inner)
    };
    definition(d, p.counting_measure, ty, value)
}

/// `IntSpace.countingMeasure_nonneg : ∀ A m,
/// CReal.le CReal.zero (IntSpace.countingMeasure A m)`.
fn declare_counting_measure_nonneg(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let sub = subset_ty(d);
    let zero = rzero(d, c);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let space = d.const_app(p.creal_finite, &[m]);
    let chi = d.const_app(p.detachable_indicator, &[a]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let hind = d.lemma(p.detachable_is_indicator, &[a, m]);

    let value = {
        let body = d.lemma(p.measure_nonneg, &[space, chi, triv_mk, hind]);
        let t = d.lam_fv(m_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let cm = d.const_app(p.counting_measure, &[a, m]);
        let concl = rle(d, c, zero, cm);
        let t = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(a_fv, sub, t)
    };
    theorem(d, p.counting_measure_nonneg, ty, value)
}

/// `IntSpace.countingMeasure_le_total : ∀ A m,
/// CReal.le (IntSpace.countingMeasure A m) (CReal.ofNat (Nat.succ m))` — a
/// subset of `succ m` indices has at most `succ m` elements, obtained from
/// the GENERIC `measure_le_total` and the finite instance's `total`.
fn declare_counting_measure_le_total(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let sub = subset_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);

    let space = d.const_app(p.creal_finite, &[m]);
    let chi = d.const_app(p.detachable_indicator, &[a]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let hind = d.lemma(p.detachable_is_indicator, &[a, m]);

    let value = {
        let body = d.lemma(p.measure_le_total, &[space, chi, triv_mk, hind]);
        let t = d.lam_fv(m_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let cm = d.const_app(p.counting_measure, &[a, m]);
        let total = d.const_app(c.of_nat, &[n]);
        let concl = rle(d, c, cm, total);
        let t = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(a_fv, sub, t)
    };
    theorem(d, p.counting_measure_le_total, ty, value)
}

// ---------------------------------------------------------------------------
// The Dirac integration space.
// ---------------------------------------------------------------------------

/// `IntSpace.crealDirac : Nat → IntSpace` — evaluation at `k`, with
/// `total = 1`. A **probability** integration space, and the cheapest witness
/// that `IntSpace` is not the interval integral in disguise: every law field
/// is `CReal.Equiv.refl` or one existing lemma.
fn declare_creal_dirac(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let carrier = d.arrow(nat, r);
    let triv_ty = d.kernel().const_(p.triv, vec![]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);

    let fle = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = rle(d, c, fi, gi);
        let body = d.pi_fv(i_fv, nat, body);
        let inner = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, inner)
    };
    let fle_refl = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.lemma(c.le_refl, &[fi]);
        let body = d.lam_fv(i_fv, nat, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let fle_trans = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hh_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(hh_fv);
        let fg_ty = d.apply(fle, &[f, g]);
        let gh_ty = d.apply(fle, &[g, hh]);
        let hfg_fv = d.fresh_fvar();
        let hfg = d.kernel().fvar(hfg_fv);
        let hgh_fv = d.fresh_fvar();
        let hgh = d.kernel().fvar(hgh_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let hi = d.apply(hh, &[i]);
        let p1 = d.apply(hfg, &[i]);
        let p2 = d.apply(hgh, &[i]);
        let body = d.lemma(c.le_trans, &[fi, gi, hi, p1, p2]);
        let body = d.lam_fv(i_fv, nat, body);
        let body = d.lam_fv(hgh_fv, gh_ty, body);
        let body = d.lam_fv(hfg_fv, fg_ty, body);
        let body = d.lam_fv(hh_fv, carrier, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let fadd = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = radd(d, c, fi, gi);
        let body = d.lam_fv(i_fv, nat, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let fscale = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = rmul(d, c, w, fi);
        let body = d.lam_fv(i_fv, nat, body);
        let body = d.lam_fv(f_fv, carrier, body);
        d.lam_fv(w_fv, r, body)
    };
    let fconst = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let i_fv = d.fresh_fvar();
        let body = d.lam_fv(i_fv, nat, w);
        d.lam_fv(w_fv, r, body)
    };
    let const_mono = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hxy_ty = rle(d, c, x, y);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let i_fv = d.fresh_fvar();
        let body = d.lam_fv(i_fv, nat, hxy);
        let body = d.lam_fv(hxy_fv, hxy_ty, body);
        let body = d.lam_fv(y_fv, r, body);
        d.lam_fv(x_fv, r, body)
    };
    let integrable = {
        let f_fv = d.fresh_fvar();
        d.lam_fv(f_fv, carrier, triv_ty)
    };
    let const_integrable = {
        let w_fv = d.fresh_fvar();
        d.lam_fv(w_fv, r, triv_mk)
    };
    let integral = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let body = d.apply(f, &[k]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, triv_ty, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let total = rone(d, c);
    let integral_const = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let wo = rmul(d, c, w, total);
        let h = d.lemma(c.mul_one, &[w]);
        let body = rsymm(d, c, wo, w, h);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, triv_ty, body);
        d.lam_fv(w_fv, r, body)
    };
    let integral_le = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hle_ty = d.apply(fle, &[f, g]);
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);
        let body = d.apply(hle, &[k]);
        let body = d.lam_fv(hle_fv, hle_ty, body);
        let hg_fv = d.fresh_fvar();
        let body = d.lam_fv(hg_fv, triv_ty, body);
        let hf_fv = d.fresh_fvar();
        let body = d.lam_fv(hf_fv, triv_ty, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let integral_add = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let sum = radd(d, c, fk, gk);
        let body = rrefl(d, c, sum);
        let hfg_fv = d.fresh_fvar();
        let body = d.lam_fv(hfg_fv, triv_ty, body);
        let hg_fv = d.fresh_fvar();
        let body = d.lam_fv(hg_fv, triv_ty, body);
        let hf_fv = d.fresh_fvar();
        let body = d.lam_fv(hf_fv, triv_ty, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };
    let integral_scale = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fk = d.apply(f, &[k]);
        let scaled = rmul(d, c, w, fk);
        let body = rrefl(d, c, scaled);
        let hcf_fv = d.fresh_fvar();
        let body = d.lam_fv(hcf_fv, triv_ty, body);
        let hf_fv = d.fresh_fvar();
        let body = d.lam_fv(hf_fv, triv_ty, body);
        let body = d.lam_fv(f_fv, carrier, body);
        d.lam_fv(w_fv, r, body)
    };

    let args = [
        carrier,
        fle,
        fle_refl,
        fle_trans,
        fadd,
        fscale,
        fconst,
        const_mono,
        integrable,
        const_integrable,
        integral,
        total,
        integral_const,
        integral_le,
        integral_add,
        integral_scale,
    ];
    debug_assert_eq!(args.len(), super::FIELD_COUNT);
    let inst = mk_instance(d.kernel(), &p.record, &args);

    let value = d.lam_fv(k_fv, nat, inst);
    let ty = {
        let space = d.kernel().const_(p.record.ind, vec![]);
        d.arrow(nat, space)
    };
    definition(d, p.creal_dirac, ty, value)
}

/// `IntSpace.crealDirac_integral : ∀ f k t,
/// CReal.Equiv ((IntSpace.crealDirac k).integral f t) (f k)` — the reduction
/// probe, by `CReal.Equiv.refl`.
fn declare_creal_dirac_integral(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let carrier = d.arrow(nat, r);
    let triv_ty = d.kernel().const_(p.triv, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let direct = d.apply(f, &[k]);
    let via = {
        let s = d.const_app(p.creal_dirac, &[k]);
        let sel = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
        let head = d.apply(sel, &[s]);
        d.apply(head, &[f, t])
    };

    let value = {
        let body = rrefl(d, c, direct);
        let x = d.lam_fv(t_fv, triv_ty, body);
        let x = d.lam_fv(k_fv, nat, x);
        d.lam_fv(f_fv, carrier, x)
    };
    let ty = {
        let concl = req(d, c, via, direct);
        let x = d.pi_fv(t_fv, triv_ty, concl);
        let x = d.pi_fv(k_fv, nat, x);
        d.pi_fv(f_fv, carrier, x)
    };
    theorem(d, p.creal_dirac_integral, ty, value)
}

/// `IntSpace.crealDirac_total : ∀ k,
/// CReal.Equiv (IntSpace.crealDirac k).total CReal.one` — **the Dirac space
/// is a probability space**, which is what makes the counting-measure bound
/// above read as `μ(A) ≤ 1` rather than as a cardinality.
fn declare_creal_dirac_total(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let one = rone(d, c);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let via = {
        let s = d.const_app(p.creal_dirac, &[k]);
        let sel = d.kernel().const_(p.record.sel(TOTAL), vec![]);
        d.apply(sel, &[s])
    };

    let value = {
        let body = rrefl(d, c, one);
        d.lam_fv(k_fv, nat, body)
    };
    let ty = {
        let concl = req(d, c, via, one);
        d.pi_fv(k_fv, nat, concl)
    };
    theorem(d, p.creal_dirac_total, ty, value)
}

/// `IntSpace.dirac_measure_detachable : ∀ A k,
/// CReal.Equiv (IntSpace.measure (IntSpace.crealDirac k)
///   (IntSpace.detachableIndicator A) IntSpace.Triv.mk)
///   (IntSpace.boolIndicator (A k))`.
///
/// **The Dirac measure of a detachable set is 1 if `k` is in it and 0 if it
/// is not** — and the proof is `CReal.Equiv.refl`, because on a detachable
/// subset every step of that sentence COMPUTES. This is the base case
/// Petrakis–Zeuner start from, and the answer to "indicators are not
/// `Bool`-valued": here they are, and nothing was decided to get them.
fn declare_dirac_measure_detachable(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let sub = subset_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let space = d.const_app(p.creal_dirac, &[k]);
    let chi = d.const_app(p.detachable_indicator, &[a]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let lhs = d.const_app(p.measure, &[space, chi, triv_mk]);
    let ak = d.apply(a, &[k]);
    let rhs = d.const_app(p.bool_indicator, &[ak]);

    let value = {
        let body = rrefl(d, c, rhs);
        let t = d.lam_fv(k_fv, nat, body);
        d.lam_fv(a_fv, sub, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(k_fv, nat, concl);
        d.pi_fv(a_fv, sub, t)
    };
    theorem(d, p.dirac_measure_detachable, ty, value)
}

// Keep the field-index imports honest: this module reaches for these through
// `p.record.sel`, and a rename upstream must break the build here too.
const _: [usize; 4] = [FCONST, FLE, INTEGRABLE, INTEGRAL];
