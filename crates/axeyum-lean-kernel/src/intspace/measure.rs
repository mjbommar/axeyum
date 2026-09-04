//! **Measure, derived from the integral.**
//!
//! The thesis W3-1 was opened to test, in five declarations: the measure of a
//! set is the integral of its indicator *when that indicator is integrable*.
//!
//! ## "Integrable set" is a positive notion, and it is not one object
//!
//! An integrable set here is a **pair of arguments**, always carried
//! together: a `chi : S.carrier` with
//!
//! - a `Sort 1` integrability datum `h : S.Integrable chi` — the positive
//!   content, the thing a classical development would replace by
//!   "measurable", and
//! - a `Prop`-valued [`Indicator`](IntSpacePrelude::indicator) side
//!   condition `0 ≤ chi ≤ 1`.
//!
//! It is not bundled into a single object, and that is forced rather than
//! chosen. Bundling needs `Sigma` or `Subtype` (both absent from this kernel,
//! ADR-1595's own finding) or a record at `Sort 3`
//! (`structures::declare_record` is fixed at `Sort 2`, and its own
//! universe control asserts that). Carrying the two arguments separately
//! costs one extra binder per theorem and nothing else, which is the same
//! answer ADR-1601 got for classical hypotheses.
//!
//! ## What the indicator condition is, and what it is NOT
//!
//! `0 ≤ chi ≤ 1` is the *located* condition, and it is weaker than "`chi` is
//! two-valued". The sharper characterisation — `chi · chi ~ chi`, idempotence
//! — is not usable constructively: over ℝ, `x·(x−1) ~ 0` does **not** give
//! `x ~ 0 ∨ x ~ 1`, because a product of reals vanishing does not decide
//! which factor did. So an integrable set's indicator is genuinely a
//! `[0,1]`-valued function here, which is exactly the reviewer's objection
//! ("membership is undecidable, so indicators are not `Bool`-valued")
//! confirmed rather than worked around. `measure_nonneg` and
//! `measure_le_total` are the two facts that survive it, and both are proved
//! below.

use super::{
    FCONST, FLE, FLE_REFL, INTEGRABLE, INTEGRAL, INTEGRAL_CONST, IntSpacePrelude, TOTAL,
    definition, field, generic_space, req, rle, rmul, rone, rtrans, rty, rzero, theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_indicator(d, p)?;
    declare_measure(d, p)?;
    declare_measure_nonneg(d, p)?;
    declare_measure_le_total(d, p)?;
    declare_measure_witness_independent(d, p)?;
    declare_measure_const(d, p)?;
    declare_indicator_univ(d, p)?;
    declare_measure_univ(d, p)?;
    Ok(())
}

fn indicator_ty(d: &mut IntDev<'_>, p: IntSpacePrelude, s: ExprId, chi: ExprId) -> ExprId {
    d.const_app(p.indicator, &[s, chi])
}

fn measure_term(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    s: ExprId,
    chi: ExprId,
    h: ExprId,
) -> ExprId {
    d.const_app(p.measure, &[s, chi, h])
}

/// The two halves of `Indicator S chi`, as bare propositions.
fn indicator_sides(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    s: ExprId,
    chi: ExprId,
) -> (ExprId, ExprId) {
    let c = p.creal;
    let zero = rzero(d, c);
    let one = rone(d, c);
    let fconst = field(d, p, s, FCONST);
    let c0 = d.apply(fconst, &[zero]);
    let fconst2 = field(d, p, s, FCONST);
    let c1 = d.apply(fconst2, &[one]);
    let fle = field(d, p, s, FLE);
    let lo = d.apply(fle, &[c0, chi]);
    let fle2 = field(d, p, s, FLE);
    let hi = d.apply(fle2, &[chi, c1]);
    (lo, hi)
}

/// `IntSpace.Indicator : ∀ (S : IntSpace), S.carrier → Prop
/// := fun S chi => And (S.fle (S.fconst 0) chi) (S.fle chi (S.fconst 1))`.
fn declare_indicator(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let chi_fv = d.fresh_fvar();
    let chi = d.kernel().fvar(chi_fv);

    let (lo, hi) = indicator_sides(d, p, g.s, chi);
    let body = d.and(lo, hi);

    let value = {
        let t = d.lam_fv(chi_fv, g.carrier, body);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.carrier, prop);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    definition(d, p.indicator, ty, value)
}

/// `IntSpace.measure : ∀ (S : IntSpace) (chi : S.carrier),
/// S.Integrable chi → CReal := fun S chi h => S.integral chi h`.
///
/// The whole inversion, in one definition: measure is *defined from* the
/// integral, and only where the integrability datum exists.
fn declare_measure(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let r = rty(d, c);

    let chi_fv = d.fresh_fvar();
    let chi = d.kernel().fvar(chi_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[chi]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let body = d.apply(integral, &[chi, h]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(chi_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let inner = d.arrow(h_ty, r);
        let t = d.pi_fv(chi_fv, g.carrier, inner);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    definition(d, p.measure, ty, value)
}

/// `IntSpace.measure_nonneg : ∀ S chi h, Indicator S chi →
/// CReal.le CReal.zero (measure S chi h)`.
fn declare_measure_nonneg(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let chi_fv = d.fresh_fvar();
    let chi = d.kernel().fvar(chi_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[chi]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hi_ty = indicator_ty(d, p, g.s, chi);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let value = {
        let (lo, up) = indicator_sides(d, p, g.s, chi);
        let left = d.and_left(lo, up, hi);
        let body = d.lemma(p.integral_nonneg, &[g.s, chi, h, left]);
        let t = d.lam_fv(hi_fv, hi_ty, body);
        let t = d.lam_fv(h_fv, h_ty, t);
        let t = d.lam_fv(chi_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let zero = rzero(d, c);
        let m = measure_term(d, p, g.s, chi, h);
        let concl = rle(d, c, zero, m);
        let t = d.arrow(hi_ty, concl);
        let t = d.pi_fv(h_fv, h_ty, t);
        let t = d.pi_fv(chi_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.measure_nonneg, ty, value)
}

/// `IntSpace.measure_le_total : ∀ S chi h, Indicator S chi →
/// CReal.le (measure S chi h) S.total`.
fn declare_measure_le_total(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let chi_fv = d.fresh_fvar();
    let chi = d.kernel().fvar(chi_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[chi]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hi_ty = indicator_ty(d, p, g.s, chi);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let value = {
        let (lo, up) = indicator_sides(d, p, g.s, chi);
        let right = d.and_right(lo, up, hi);
        let body = d.lemma(p.integral_le_total, &[g.s, chi, h, right]);
        let t = d.lam_fv(hi_fv, hi_ty, body);
        let t = d.lam_fv(h_fv, h_ty, t);
        let t = d.lam_fv(chi_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let m = measure_term(d, p, g.s, chi, h);
        let total = field(d, p, g.s, TOTAL);
        let concl = rle(d, c, m, total);
        let t = d.arrow(hi_ty, concl);
        let t = d.pi_fv(h_fv, h_ty, t);
        let t = d.pi_fv(chi_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.measure_le_total, ty, value)
}

/// `IntSpace.measure_witness_independent : ∀ S chi h1 h2,
/// CReal.Equiv (measure S chi h1) (measure S chi h2)`.
///
/// The measure of a set does not depend on WHICH integrability datum
/// witnesses it. On a classical development this is not even a statement;
/// here it is the theorem that makes "the measure of the set" well defined.
fn declare_measure_witness_independent(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let chi_fv = d.fresh_fvar();
    let chi = d.kernel().fvar(chi_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[chi]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let value = {
        let body = d.lemma(p.integral_witness_independent, &[g.s, chi, h1, h2]);
        let t = d.lam_fv(h2_fv, h_ty, body);
        let t = d.lam_fv(h1_fv, h_ty, t);
        let t = d.lam_fv(chi_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let m1 = measure_term(d, p, g.s, chi, h1);
        let m2 = measure_term(d, p, g.s, chi, h2);
        let concl = req(d, c, m1, m2);
        let t = d.pi_fv(h2_fv, h_ty, concl);
        let t = d.pi_fv(h1_fv, h_ty, t);
        let t = d.pi_fv(chi_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.measure_witness_independent, ty, value)
}

/// `IntSpace.measure_const : ∀ S c h,
/// CReal.Equiv (measure S (S.fconst c) h) (CReal.mul c S.total)`.
fn declare_measure_const(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let r = rty(d, c);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let fconst = field(d, p, g.s, FCONST);
    let cv = d.apply(fconst, &[v]);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[cv]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let value = {
        let ic = field(d, p, g.s, INTEGRAL_CONST);
        let body = d.apply(ic, &[v, h]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(v_fv, r, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let m = measure_term(d, p, g.s, cv, h);
        let total = field(d, p, g.s, TOTAL);
        let rhs = rmul(d, c, v, total);
        let concl = req(d, c, m, rhs);
        let t = d.pi_fv(h_fv, h_ty, concl);
        let t = d.pi_fv(v_fv, r, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.measure_const, ty, value)
}

/// `IntSpace.indicator_univ : ∀ S, Indicator S (S.fconst CReal.one)` — the
/// whole space is an integrable set, and its integrability datum is
/// `S.constIntegrable CReal.one`, which every space has by construction.
fn declare_indicator_univ(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let one = rone(d, c);
    let fconst = field(d, p, g.s, FCONST);
    let c1 = d.apply(fconst, &[one]);

    let value = {
        let zero = rzero(d, c);
        let zlt = d.kernel().const_(c.zero_lt_one, vec![]);
        let zle = d.lemma(c.le_of_lt, &[zero, one, zlt]);
        let cm = field(d, p, g.s, CONST_MONO_IDX);
        let lo_proof = d.apply(cm, &[zero, one, zle]);
        let refl = field(d, p, g.s, FLE_REFL);
        let hi_proof = d.apply(refl, &[c1]);
        let (lo, hi) = indicator_sides(d, p, g.s, c1);
        let intro = c.rat.int.logic.and_intro;
        let body = d.const_app(intro, &[lo, hi, lo_proof, hi_proof]);
        d.lam_fv(g.s_fv, g.space_ty, body)
    };
    let ty = {
        let concl = indicator_ty(d, p, g.s, c1);
        d.pi_fv(g.s_fv, g.space_ty, concl)
    };
    theorem(d, p.indicator_univ, ty, value)
}

/// `IntSpace.measure_univ : ∀ S h,
/// CReal.Equiv (measure S (S.fconst CReal.one) h) S.total`.
fn declare_measure_univ(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let one = rone(d, c);
    let fconst = field(d, p, g.s, FCONST);
    let c1 = d.apply(fconst, &[one]);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[c1]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let total = field(d, p, g.s, TOTAL);
    let m = measure_term(d, p, g.s, c1, h);
    let mid = rmul(d, c, one, total);

    let value = {
        let step1 = d.lemma(p.measure_const, &[g.s, one, h]);
        let t1 = rmul(d, c, total, one);
        let comm = d.lemma(c.mul_comm, &[one, total]);
        let mo = d.lemma(c.mul_one, &[total]);
        let step2 = rtrans(d, c, mid, t1, total, comm, mo);
        let body = rtrans(d, c, m, mid, total, step1, step2);
        let t = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = req(d, c, m, total);
        let t = d.pi_fv(h_fv, h_ty, concl);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.measure_univ, ty, value)
}

/// Local alias so the `constMono` field index reads at the use site.
const CONST_MONO_IDX: usize = super::CONST_MONO;
