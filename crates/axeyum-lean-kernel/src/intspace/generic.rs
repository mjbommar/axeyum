//! The theorems that hold of **every** integration space.
//!
//! This is the yield side of ADR-1612's measurement. Nothing here mentions an
//! interval, a Riemann sum, or a modulus of continuity; each is proved once
//! from the record's fields and then holds of `crealInterval`, of
//! `crealFinite`, and of every integration space anyone builds later.
//!
//! Two of them are worth naming individually:
//!
//! - [`declare_integral_congr`] is the **integrand congruence**
//!   `CReal.integral` never had. It is derived from monotonicity alone, by
//!   antisymmetry of `CReal.le`: if `f ≤ g` and `g ≤ f` pointwise then the
//!   two integrals bound each other, so `CReal.equiv_of_le_le` closes it. The
//!   library had `CReal.integral_le` for eight days and nobody took this
//!   step.
//! - [`declare_integral_witness_independent`] is
//!   `CReal.integral_witness_independent` **derived rather than assumed**.
//!   That theorem cost a whole `converges_unique` argument on ℝ; here it is
//!   one line off the congruence, because the record makes the integral a
//!   monotone functional and monotonicity already knows the value does not
//!   depend on the witness.

use super::{
    CONST_INTEGRABLE, FCONST, FLE, FLE_REFL, FLE_TRANS, INTEGRABLE, INTEGRAL, INTEGRAL_CONST,
    INTEGRAL_LE, IntSpacePrelude, TOTAL, definition, field, generic_space, req, rle, rmul, rone,
    rsymm, rtrans, rty, rzero, theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_integral_congr(d, p)?;
    declare_integral_witness_independent(d, p)?;
    declare_integral_le_const(d, p)?;
    declare_const_le_integral(d, p)?;
    declare_integral_nonneg(d, p)?;
    declare_integral_le_total(d, p)?;
    declare_fequiv(d, p)?;
    declare_fequiv_refl(d, p)?;
    declare_fequiv_symm(d, p)?;
    declare_fequiv_trans(d, p)?;
    declare_integral_fequiv_congr(d, p)?;
    Ok(())
}

/// `IntSpace.integral_congr : ∀ S f g hf hg, S.fle f g → S.fle g f →
/// CReal.Equiv (S.integral f hf) (S.integral g hg)`.
fn declare_integral_congr(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hg_ty = d.apply(integrable, &[gg]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let fle = field(d, p, g.s, FLE);
    let h1_ty = d.apply(fle, &[f, gg]);
    let h2_ty = d.apply(fle, &[gg, f]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[f, hf]);
    let rhs = d.apply(integral, &[gg, hg]);

    let value = {
        let ile = field(d, p, g.s, INTEGRAL_LE);
        let up = d.apply(ile, &[f, gg, hf, hg, h1]);
        let down = d.apply(ile, &[gg, f, hg, hf, h2]);
        let body = d.lemma(c.equiv_of_le_le, &[lhs, rhs, up, down]);
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(hg_fv, hg_ty, t);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(gg_fv, g.carrier, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(h2_fv, h2_ty, concl);
        let t = d.pi_fv(h1_fv, h1_ty, t);
        let t = d.pi_fv(hg_fv, hg_ty, t);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(gg_fv, g.carrier, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_congr, ty, value)
}

/// `IntSpace.integral_witness_independent : ∀ S f h1 h2,
/// CReal.Equiv (S.integral f h1) (S.integral f h2)`.
fn declare_integral_witness_independent(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let h_ty = d.apply(integrable, &[f]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[f, h1]);
    let rhs = d.apply(integral, &[f, h2]);

    let value = {
        let refl = field(d, p, g.s, FLE_REFL);
        let hr = d.apply(refl, &[f]);
        let body = d.lemma(p.integral_congr, &[g.s, f, f, h1, h2, hr, hr]);
        let t = d.lam_fv(h2_fv, h_ty, body);
        let t = d.lam_fv(h1_fv, h_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(h2_fv, h_ty, concl);
        let t = d.pi_fv(h1_fv, h_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_witness_independent, ty, value)
}

/// `IntSpace.integral_le_const : ∀ S M f hf, S.fle f (S.fconst M) →
/// CReal.le (S.integral f hf) (CReal.mul M S.total)`.
fn declare_integral_le_const(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let r = rty(d, c);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let fconst = field(d, p, g.s, FCONST);
    let cm = d.apply(fconst, &[m]);
    let fle = field(d, p, g.s, FLE);
    let h_ty = d.apply(fle, &[f, cm]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[f, hf]);
    let total = field(d, p, g.s, TOTAL);
    let rhs = rmul(d, c, m, total);

    let value = {
        let ci = field(d, p, g.s, CONST_INTEGRABLE);
        let hc = d.apply(ci, &[m]);
        let mid = d.apply(integral, &[cm, hc]);
        let ile = field(d, p, g.s, INTEGRAL_LE);
        let step1 = d.apply(ile, &[f, cm, hf, hc, h]);
        let ic = field(d, p, g.s, INTEGRAL_CONST);
        let eqc = d.apply(ic, &[m, hc]);
        let step2 = d.lemma(c.le_of_equiv, &[mid, rhs, eqc]);
        let body = d.lemma(c.le_trans, &[lhs, mid, rhs, step1, step2]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        let t = d.lam_fv(m_fv, r, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, lhs, rhs);
        let t = d.pi_fv(h_fv, h_ty, concl);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        let t = d.pi_fv(m_fv, r, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_le_const, ty, value)
}

/// `IntSpace.const_le_integral : ∀ S M f hf, S.fle (S.fconst M) f →
/// CReal.le (CReal.mul M S.total) (S.integral f hf)`.
fn declare_const_le_integral(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let r = rty(d, c);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let fconst = field(d, p, g.s, FCONST);
    let cm = d.apply(fconst, &[m]);
    let fle = field(d, p, g.s, FLE);
    let h_ty = d.apply(fle, &[cm, f]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let rhs = d.apply(integral, &[f, hf]);
    let total = field(d, p, g.s, TOTAL);
    let lhs = rmul(d, c, m, total);

    let value = {
        let ci = field(d, p, g.s, CONST_INTEGRABLE);
        let hc = d.apply(ci, &[m]);
        let mid = d.apply(integral, &[cm, hc]);
        let ic = field(d, p, g.s, INTEGRAL_CONST);
        let eqc = d.apply(ic, &[m, hc]);
        let flipped = rsymm(d, c, mid, lhs, eqc);
        let step1 = d.lemma(c.le_of_equiv, &[lhs, mid, flipped]);
        let ile = field(d, p, g.s, INTEGRAL_LE);
        let step2 = d.apply(ile, &[cm, f, hc, hf, h]);
        let body = d.lemma(c.le_trans, &[lhs, mid, rhs, step1, step2]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        let t = d.lam_fv(m_fv, r, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, lhs, rhs);
        let t = d.pi_fv(h_fv, h_ty, concl);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        let t = d.pi_fv(m_fv, r, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.const_le_integral, ty, value)
}

/// `IntSpace.integral_nonneg : ∀ S f hf, S.fle (S.fconst CReal.zero) f →
/// CReal.le CReal.zero (S.integral f hf)`.
///
/// The one algebraic step is `0 · total ~ 0`, which needs `mul_comm` because
/// the ℝ prelude has `mul_zero` and no `zero_mul`.
fn declare_integral_nonneg(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let zero = rzero(d, c);
    let fconst = field(d, p, g.s, FCONST);
    let c0 = d.apply(fconst, &[zero]);
    let fle = field(d, p, g.s, FLE);
    let h_ty = d.apply(fle, &[c0, f]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let rhs = d.apply(integral, &[f, hf]);
    let total = field(d, p, g.s, TOTAL);
    let mid = rmul(d, c, zero, total);

    let value = {
        // `0 · T ~ T · 0 ~ 0`, then flipped to `0 ~ 0 · T`.
        let tz = rmul(d, c, total, zero);
        let comm = d.lemma(c.mul_comm, &[zero, total]);
        let mz = d.lemma(c.mul_zero, &[total]);
        let mid_eq_zero = rtrans(d, c, mid, tz, zero, comm, mz);
        let zero_eq_mid = rsymm(d, c, mid, zero, mid_eq_zero);
        let step1 = d.lemma(c.le_of_equiv, &[zero, mid, zero_eq_mid]);
        let step2 = d.lemma(p.const_le_integral, &[g.s, zero, f, hf, h]);
        let body = d.lemma(c.le_trans, &[zero, mid, rhs, step1, step2]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, zero, rhs);
        let t = d.pi_fv(h_fv, h_ty, concl);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_nonneg, ty, value)
}

/// `IntSpace.integral_le_total : ∀ S f hf, S.fle f (S.fconst CReal.one) →
/// CReal.le (S.integral f hf) S.total`.
fn declare_integral_le_total(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let one = rone(d, c);
    let fconst = field(d, p, g.s, FCONST);
    let c1 = d.apply(fconst, &[one]);
    let fle = field(d, p, g.s, FLE);
    let h_ty = d.apply(fle, &[f, c1]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[f, hf]);
    let total = field(d, p, g.s, TOTAL);
    let mid = rmul(d, c, one, total);

    let value = {
        let t1 = rmul(d, c, total, one);
        let comm = d.lemma(c.mul_comm, &[one, total]);
        let mo = d.lemma(c.mul_one, &[total]);
        let mid_eq_total = rtrans(d, c, mid, t1, total, comm, mo);
        let step1 = d.lemma(p.integral_le_const, &[g.s, one, f, hf, h]);
        let step2 = d.lemma(c.le_of_equiv, &[mid, total, mid_eq_total]);
        let body = d.lemma(c.le_trans, &[lhs, mid, total, step1, step2]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, lhs, total);
        let t = d.pi_fv(h_fv, h_ty, concl);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_le_total, ty, value)
}

// ---------------------------------------------------------------------------
// The setoid the order induces. `fle` is a preorder by fields 2 and 3, so the
// symmetric part is an equivalence -- and the record needs no `feq` field.
// ---------------------------------------------------------------------------

/// `IntSpace.FEquiv : ∀ (S : IntSpace), S.carrier → S.carrier → Prop
/// := fun S f g => And (S.fle f g) (S.fle g f)`.
fn declare_fequiv(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);

    let fle = field(d, p, g.s, FLE);
    let l = d.apply(fle, &[f, gg]);
    let r = d.apply(fle, &[gg, f]);
    let body = d.and(l, r);

    let value = {
        let t = d.lam_fv(gg_fv, g.carrier, body);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let inner = d.arrow(g.carrier, prop);
        let t = d.arrow(g.carrier, inner);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    definition(d, p.fequiv, ty, value)
}

fn fequiv_ty(d: &mut IntDev<'_>, p: IntSpacePrelude, s: ExprId, f: ExprId, g: ExprId) -> ExprId {
    d.const_app(p.fequiv, &[s, f, g])
}

/// `IntSpace.fequiv_refl : ∀ S f, IntSpace.FEquiv S f f`.
fn declare_fequiv_refl(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let fle = field(d, p, g.s, FLE);
    let side = d.apply(fle, &[f, f]);

    let value = {
        let refl = field(d, p, g.s, FLE_REFL);
        let hr = d.apply(refl, &[f]);
        let intro = p.creal.rat.int.logic.and_intro;
        let body = d.const_app(intro, &[side, side, hr, hr]);
        let t = d.lam_fv(f_fv, g.carrier, body);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = fequiv_ty(d, p, g.s, f, f);
        let t = d.pi_fv(f_fv, g.carrier, concl);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.fequiv_refl, ty, value)
}

/// `IntSpace.fequiv_symm : ∀ S f g, FEquiv S f g → FEquiv S g f`.
fn declare_fequiv_symm(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);

    let h_ty = fequiv_ty(d, p, g.s, f, gg);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let fle = field(d, p, g.s, FLE);
    let fg = d.apply(fle, &[f, gg]);
    let gf = d.apply(fle, &[gg, f]);

    let value = {
        let left = d.and_left(fg, gf, h);
        let right = d.and_right(fg, gf, h);
        let intro = p.creal.rat.int.logic.and_intro;
        let body = d.const_app(intro, &[gf, fg, right, left]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(gg_fv, g.carrier, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = fequiv_ty(d, p, g.s, gg, f);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(gg_fv, g.carrier, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.fequiv_symm, ty, value)
}

/// `IntSpace.fequiv_trans : ∀ S f g h, FEquiv S f g → FEquiv S g h →
/// FEquiv S f h`.
fn declare_fequiv_trans(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);
    let hh_fv = d.fresh_fvar();
    let hh = d.kernel().fvar(hh_fv);

    let h1_ty = fequiv_ty(d, p, g.s, f, gg);
    let h2_ty = fequiv_ty(d, p, g.s, gg, hh);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let fle = field(d, p, g.s, FLE);
    let fg = d.apply(fle, &[f, gg]);
    let gf = d.apply(fle, &[gg, f]);
    let gh = d.apply(fle, &[gg, hh]);
    let hg = d.apply(fle, &[hh, gg]);
    let fh = d.apply(fle, &[f, hh]);
    let hf = d.apply(fle, &[hh, f]);

    let value = {
        let tr = field(d, p, g.s, FLE_TRANS);
        let a = d.and_left(fg, gf, h1);
        let b = d.and_left(gh, hg, h2);
        let up = d.apply(tr, &[f, gg, hh, a, b]);
        let c2 = d.and_right(gh, hg, h2);
        let d2 = d.and_right(fg, gf, h1);
        let down = d.apply(tr, &[hh, gg, f, c2, d2]);
        let intro = p.creal.rat.int.logic.and_intro;
        let body = d.const_app(intro, &[fh, hf, up, down]);
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(hh_fv, g.carrier, t);
        let t = d.lam_fv(gg_fv, g.carrier, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = fequiv_ty(d, p, g.s, f, hh);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(hh_fv, g.carrier, t);
        let t = d.pi_fv(gg_fv, g.carrier, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.fequiv_trans, ty, value)
}

/// `IntSpace.integral_fequiv_congr : ∀ S f g hf hg, FEquiv S f g →
/// CReal.Equiv (S.integral f hf) (S.integral g hg)`.
fn declare_integral_fequiv_congr(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hg_ty = d.apply(integrable, &[gg]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let h_ty = fequiv_ty(d, p, g.s, f, gg);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[f, hf]);
    let rhs = d.apply(integral, &[gg, hg]);

    let value = {
        let fle = field(d, p, g.s, FLE);
        let fg = d.apply(fle, &[f, gg]);
        let gf = d.apply(fle, &[gg, f]);
        let left = d.and_left(fg, gf, h);
        let right = d.and_right(fg, gf, h);
        let body = d.lemma(p.integral_congr, &[g.s, f, gg, hf, hg, left, right]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(hg_fv, hg_ty, t);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(gg_fv, g.carrier, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(hg_fv, hg_ty, t);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(gg_fv, g.carrier, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_fequiv_congr, ty, value)
}
