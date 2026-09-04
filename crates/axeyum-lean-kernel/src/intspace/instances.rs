//! The two instances, their reduction probes, and what the generic layer
//! buys back on ℝ.
//!
//! ## `crealInterval` — the Riemann integral, as an integration space
//!
//! Twelve of the sixteen fields are filled by an **existing** `CReal`
//! declaration applied to `a`, `b` and `hab` with no new estimate:
//! `integral_const`, `integral_le`, `integral_add`, `integral_scale`,
//! `uniformly_continuous_const`, `le_refl`, `le_trans`, and `CReal.integral`
//! itself. The other four are the pointwise definitions (`fle`, `fadd`,
//! `fscale`, `fconst`) and one three-line proof (`constMono`).
//!
//! ## `crealFinite` — the finite index set, as an integration space
//!
//! `CReal.sumRange` over `Nat.succ m` indices, with `sumRange_le`,
//! `sumRange_add`, `mul_sumRange` and `sumRange_const` filling the same four
//! law fields. **This is the bridge reviewer 08 needs**: expectation over a
//! finite index set is an integral, `total` is the index count (so the
//! derived measure is COUNTING measure), and everything the generic layer
//! proves — congruence, nonnegativity, the constant law, monotone
//! convergence — lands on `CReal.sumRange` for free.
//!
//! It also settles a question the record's design raises: is `IntSpace`
//! secretly the interval integral wearing a hat? No. The two instances share
//! no machinery at all — one is built from Riemann sums with a modulus, the
//! other from a `Nat.rec` — and every field of both is filled.

use super::{
    INTEGRAL, IntSpacePrelude, TOTAL, definition, radd, req, rle, rmul, rneg, rrefl, rsymm, rtrans,
    rty, rzero, theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_creal_interval(d, p)?;
    declare_creal_interval_integral(d, p)?;
    declare_creal_interval_total(d, p)?;
    declare_creal_finite(d, p)?;
    declare_creal_finite_integral(d, p)?;
    declare_creal_witness_independent(d, p)?;
    declare_creal_integral_congr(d, p)?;
    declare_creal_integral_nonneg(d, p)?;
    declare_creal_sum_range_congr(d, p)?;
    declare_creal_sum_range_nonneg(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The interval instance.
// ---------------------------------------------------------------------------

/// The sixteen constructor arguments of `IntSpace.crealInterval a b hab`, as
/// a vector, so the test module can rebuild the instance with ONE slot
/// replaced and require the kernel to refuse. Every field of this record is
/// load-bearing only if that refusal actually happens.
pub(crate) fn interval_args(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
) -> Vec<ExprId> {
    let c = p.creal;
    let r = rty(d, c);
    let carrier = d.arrow(r, r);

    // `fun f g => ∀ t, le a t → le t b → le (f t) (g t)`.
    let fle = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let concl = rle(d, c, ft, gt);
        let body = d.arrow(hi, concl);
        let body = d.arrow(lo, body);
        let body = d.pi_fv(t_fv, r, body);
        let inner = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, inner)
    };

    // `fun f t _ _ => CReal.le_refl (f t)`.
    let fle_refl = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let ft = d.apply(f, &[t]);
        let body = d.lemma(c.le_refl, &[ft]);
        let h2_fv = d.fresh_fvar();
        let body = d.lam_fv(h2_fv, hi, body);
        let h1_fv = d.fresh_fvar();
        let body = d.lam_fv(h1_fv, lo, body);
        let body = d.lam_fv(t_fv, r, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun f g h hfg hgh t h1 h2 =>
    //    CReal.le_trans (f t) (g t) (h t) (hfg t h1 h2) (hgh t h1 h2)`.
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
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let ht = d.apply(hh, &[t]);
        let p1 = d.apply(hfg, &[t, h1, h2]);
        let p2 = d.apply(hgh, &[t, h1, h2]);
        let body = d.lemma(c.le_trans, &[ft, gt, ht, p1, p2]);
        let body = d.lam_fv(h2_fv, hi, body);
        let body = d.lam_fv(h1_fv, lo, body);
        let body = d.lam_fv(t_fv, r, body);
        let body = d.lam_fv(hgh_fv, gh_ty, body);
        let body = d.lam_fv(hfg_fv, fg_ty, body);
        let body = d.lam_fv(hh_fv, carrier, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun f g t => add (f t) (g t)`.
    let fadd = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let body = radd(d, c, ft, gt);
        let body = d.lam_fv(t_fv, r, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun w f t => mul w (f t)`.
    let fscale = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let body = rmul(d, c, w, ft);
        let body = d.lam_fv(t_fv, r, body);
        let body = d.lam_fv(f_fv, carrier, body);
        d.lam_fv(w_fv, r, body)
    };

    // `fun w _ => w`.
    let fconst = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let t_fv = d.fresh_fvar();
        let body = d.lam_fv(t_fv, r, w);
        d.lam_fv(w_fv, r, body)
    };

    // `fun x y hxy t _ _ => hxy`.
    let const_mono = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hxy_ty = rle(d, c, x, y);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let h2_fv = d.fresh_fvar();
        let body = d.lam_fv(h2_fv, hi, hxy);
        let h1_fv = d.fresh_fvar();
        let body = d.lam_fv(h1_fv, lo, body);
        let body = d.lam_fv(t_fv, r, body);
        let body = d.lam_fv(hxy_fv, hxy_ty, body);
        let body = d.lam_fv(y_fv, r, body);
        d.lam_fv(x_fv, r, body)
    };

    // `fun f => CReal.UniformlyContinuousOn f a b`.
    let integrable = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let body = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun w => CReal.uniformly_continuous_const w a b`.
    let const_integrable = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let body = d.lemma(c.uniformly_continuous_const, &[w, a, b]);
        d.lam_fv(w_fv, r, body)
    };

    // `fun f h => CReal.integral f a b hab h`.
    let integral = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let h_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.const_app(c.integral, &[f, a, b, hab, h]);
        let body = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `b + -a`.
    let total = {
        let na = rneg(d, c, a);
        radd(d, c, b, na)
    };

    // `fun w h => CReal.integral_const w a b hab h`.
    let integral_const = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let cw = d.apply(fconst, &[w]);
        let h_ty = d.apply(integrable, &[cw]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(c.integral_const, &[w, a, b, hab, h]);
        let body = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(w_fv, r, body)
    };

    // `fun f g hf hg hle => CReal.integral_le f g a b hab hf hg hle`.
    let integral_le = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hf_ty = d.apply(integrable, &[f]);
        let hg_ty = d.apply(integrable, &[g]);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);
        let hle_ty = d.apply(fle, &[f, g]);
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);
        let body = d.lemma(c.integral_le, &[f, g, a, b, hab, hf, hg, hle]);
        let body = d.lam_fv(hle_fv, hle_ty, body);
        let body = d.lam_fv(hg_fv, hg_ty, body);
        let body = d.lam_fv(hf_fv, hf_ty, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun f g hf hg hfg => CReal.integral_add f g a b hab hfg hf hg`.
    let integral_add = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let sum = d.apply(fadd, &[f, g]);
        let hf_ty = d.apply(integrable, &[f]);
        let hg_ty = d.apply(integrable, &[g]);
        let hfg_ty = d.apply(integrable, &[sum]);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);
        let hfg_fv = d.fresh_fvar();
        let hfg = d.kernel().fvar(hfg_fv);
        let body = d.lemma(c.integral_add, &[f, g, a, b, hab, hfg, hf, hg]);
        let body = d.lam_fv(hfg_fv, hfg_ty, body);
        let body = d.lam_fv(hg_fv, hg_ty, body);
        let body = d.lam_fv(hf_fv, hf_ty, body);
        let body = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, body)
    };

    // `fun w f hf hcf => CReal.integral_scale w f a b hab hf hcf`.
    let integral_scale = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let scaled = d.apply(fscale, &[w, f]);
        let hf_ty = d.apply(integrable, &[f]);
        let hcf_ty = d.apply(integrable, &[scaled]);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hcf_fv = d.fresh_fvar();
        let hcf = d.kernel().fvar(hcf_fv);
        let body = d.lemma(c.integral_scale, &[w, f, a, b, hab, hf, hcf]);
        let body = d.lam_fv(hcf_fv, hcf_ty, body);
        let body = d.lam_fv(hf_fv, hf_ty, body);
        let body = d.lam_fv(f_fv, carrier, body);
        d.lam_fv(w_fv, r, body)
    };

    let args = vec![
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
    args
}

/// `IntSpace.crealInterval : ∀ (a b : CReal), CReal.le a b → IntSpace`.
fn declare_creal_interval(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let args = interval_args(d, p, a, b, hab);
    let inst = mk_instance(d.kernel(), &p.record, &args);

    let value = {
        let t = d.lam_fv(hab_fv, hab_ty, inst);
        let t = d.lam_fv(b_fv, r, t);
        d.lam_fv(a_fv, r, t)
    };
    let ty = {
        let space = d.kernel().const_(p.record.ind, vec![]);
        let t = d.arrow(hab_ty, space);
        let t = d.pi_fv(b_fv, r, t);
        d.pi_fv(a_fv, r, t)
    };
    definition(d, p.creal_interval, ty, value)
}

/// `IntSpace.crealInterval a b hab` as a term.
fn interval(d: &mut IntDev<'_>, p: IntSpacePrelude, a: ExprId, b: ExprId, hab: ExprId) -> ExprId {
    d.const_app(p.creal_interval, &[a, b, hab])
}

/// `IntSpace.crealInterval_integral : ∀ F a b hab u,
/// CReal.Equiv ((IntSpace.crealInterval a b hab).integral F u)
///   (CReal.integral F a b hab u)`.
///
/// Proved by `CReal.Equiv.refl`, so its ADMISSION is the statement that the
/// `integral` selector reduces definitionally on this instance.
fn declare_creal_interval_integral(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let carrier = d.arrow(r, r);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let direct = d.const_app(c.integral, &[f, a, b, hab, u]);
    let via = {
        let s = interval(d, p, a, b, hab);
        let sel = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
        let head = d.apply(sel, &[s]);
        d.apply(head, &[f, u])
    };

    let value = {
        let body = rrefl(d, c, direct);
        let t = d.lam_fv(u_fv, u_ty, body);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, r, t);
        let t = d.lam_fv(a_fv, r, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, via, direct);
        let t = d.pi_fv(u_fv, u_ty, concl);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(b_fv, r, t);
        let t = d.pi_fv(a_fv, r, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_interval_integral, ty, value)
}

/// `IntSpace.crealInterval_total : ∀ a b hab,
/// CReal.Equiv (IntSpace.crealInterval a b hab).total (CReal.add b (CReal.neg a))`
/// — the second reduction probe, on a different field, so the first one
/// passing cannot be an accident of that one selector.
fn declare_creal_interval_total(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let na = rneg(d, c, a);
    let direct = radd(d, c, b, na);
    let via = {
        let s = interval(d, p, a, b, hab);
        let sel = d.kernel().const_(p.record.sel(TOTAL), vec![]);
        d.apply(sel, &[s])
    };

    let value = {
        let body = rrefl(d, c, direct);
        let t = d.lam_fv(hab_fv, hab_ty, body);
        let t = d.lam_fv(b_fv, r, t);
        d.lam_fv(a_fv, r, t)
    };
    let ty = {
        let concl = req(d, c, via, direct);
        let t = d.pi_fv(hab_fv, hab_ty, concl);
        let t = d.pi_fv(b_fv, r, t);
        d.pi_fv(a_fv, r, t)
    };
    theorem(d, p.creal_interval_total, ty, value)
}

// ---------------------------------------------------------------------------
// The finite instance.
// ---------------------------------------------------------------------------

/// `IntSpace.crealFinite : Nat → IntSpace` — `CReal.sumRange` over the
/// `Nat.succ m` indices below the bound.
fn declare_creal_finite(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let natp = d.prelude();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);

    let carrier = d.arrow(nat, r);

    // `fun f g => ∀ i, Nat.lt i n → le (f i) (g i)`.
    let fle = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let concl = rle(d, c, fi, gi);
        let body = d.arrow(lt, concl);
        let body = d.pi_fv(i_fv, nat, body);
        let inner = d.lam_fv(g_fv, carrier, body);
        d.lam_fv(f_fv, carrier, inner)
    };

    let fle_refl = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let fi = d.apply(f, &[i]);
        let body = d.lemma(c.le_refl, &[fi]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, lt, body);
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
        let lt = d.const_app(natp.lt, &[i, n]);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let hi2 = d.apply(hh, &[i]);
        let p1 = d.apply(hfg, &[i, hi]);
        let p2 = d.apply(hgh, &[i, hi]);
        let body = d.lemma(c.le_trans, &[fi, gi, hi2, p1, p2]);
        let body = d.lam_fv(hi_fv, lt, body);
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
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, lt, hxy);
        let body = d.lam_fv(i_fv, nat, body);
        let body = d.lam_fv(hxy_fv, hxy_ty, body);
        let body = d.lam_fv(y_fv, r, body);
        d.lam_fv(x_fv, r, body)
    };

    // `fun _ => IntSpace.Triv` — everything on a finite index set is
    // integrable, and the datum carries no information.
    let triv_ty = d.kernel().const_(p.triv, vec![]);
    let integrable = {
        let f_fv = d.fresh_fvar();
        d.lam_fv(f_fv, carrier, triv_ty)
    };
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let const_integrable = {
        let w_fv = d.fresh_fvar();
        d.lam_fv(w_fv, r, triv_mk)
    };

    // `fun f _ => CReal.sumRange f n`.
    let integral = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let body = d.const_app(c.sum_range, &[f, n]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, triv_ty, body);
        d.lam_fv(f_fv, carrier, body)
    };

    let total = d.const_app(c.of_nat, &[n]);

    // `fun w _ => Equiv.trans (sumRange_const w m) (mul_comm (ofNat n) w)`.
    let integral_const = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let cw = d.apply(fconst, &[w]);
        let lhs = d.const_app(c.sum_range, &[cw, n]);
        let mid = rmul(d, c, total, w);
        let rhs = rmul(d, c, w, total);
        let s1 = d.lemma(c.sum_range_const, &[w, m]);
        let s2 = d.lemma(c.mul_comm, &[total, w]);
        let body = rtrans(d, c, lhs, mid, rhs, s1, s2);
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
        let body = d.lemma(c.sum_range_le, &[f, g, n, hle]);
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
        let body = d.lemma(c.sum_range_add, &[f, g, n]);
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
        let scaled = d.apply(fscale, &[w, f]);
        let sum_f = d.const_app(c.sum_range, &[f, n]);
        let lhs = rmul(d, c, w, sum_f);
        let rhs = d.const_app(c.sum_range, &[scaled, n]);
        let h = d.lemma(c.mul_sum_range, &[w, f, n]);
        let body = rsymm(d, c, lhs, rhs, h);
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

    let value = d.lam_fv(m_fv, nat, inst);
    let ty = {
        let space = d.kernel().const_(p.record.ind, vec![]);
        d.arrow(nat, space)
    };
    definition(d, p.creal_finite, ty, value)
}

/// `IntSpace.crealFinite_integral : ∀ f m t,
/// CReal.Equiv ((IntSpace.crealFinite m).integral f t)
///   (CReal.sumRange f (Nat.succ m))` — the finite instance's reduction
/// probe, again by `CReal.Equiv.refl`.
fn declare_creal_finite_integral(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let carrier = d.arrow(nat, r);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);
    let triv_ty = d.kernel().const_(p.triv, vec![]);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let direct = d.const_app(c.sum_range, &[f, n]);
    let via = {
        let s = d.const_app(p.creal_finite, &[m]);
        let sel = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
        let head = d.apply(sel, &[s]);
        d.apply(head, &[f, t])
    };

    let value = {
        let body = rrefl(d, c, direct);
        let t2 = d.lam_fv(t_fv, triv_ty, body);
        let t2 = d.lam_fv(m_fv, nat, t2);
        d.lam_fv(f_fv, carrier, t2)
    };
    let ty = {
        let concl = req(d, c, via, direct);
        let t2 = d.pi_fv(t_fv, triv_ty, concl);
        let t2 = d.pi_fv(m_fv, nat, t2);
        d.pi_fv(f_fv, carrier, t2)
    };
    theorem(d, p.creal_finite_integral, ty, value)
}

// ---------------------------------------------------------------------------
// What the generic layer buys back. THIS is ADR-1612's measurement: each of
// these states a fact about `CReal.integral` or `CReal.sumRange` and proves
// it by ONE application of a generic `IntSpace` theorem to an instance.
// ---------------------------------------------------------------------------

/// `IntSpace.CReal.integral_witness_independent : ∀ F a b hab u1 u2,
/// CReal.Equiv (CReal.integral F a b hab u1) (CReal.integral F a b hab u2)`
/// — **the same statement as `CReal.integral_witness_independent`**, proved
/// here by `IntSpace.integral_witness_independent` at the interval instance
/// and nothing else. Its admission is what makes the "became an instance"
/// claim checkable rather than rhetorical.
fn declare_creal_witness_independent(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let carrier = d.arrow(r, r);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let u1_fv = d.fresh_fvar();
    let u1 = d.kernel().fvar(u1_fv);
    let u2_fv = d.fresh_fvar();
    let u2 = d.kernel().fvar(u2_fv);

    let lhs = d.const_app(c.integral, &[f, a, b, hab, u1]);
    let rhs = d.const_app(c.integral, &[f, a, b, hab, u2]);

    let value = {
        let s = interval(d, p, a, b, hab);
        let body = d.lemma(p.integral_witness_independent, &[s, f, u1, u2]);
        let t = d.lam_fv(u2_fv, u_ty, body);
        let t = d.lam_fv(u1_fv, u_ty, t);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, r, t);
        let t = d.lam_fv(a_fv, r, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(u2_fv, u_ty, concl);
        let t = d.pi_fv(u1_fv, u_ty, t);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(b_fv, r, t);
        let t = d.pi_fv(a_fv, r, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_witness_independent, ty, value)
}

/// `IntSpace.CReal.integral_congr : ∀ F G a b hab uF uG,
/// (∀ t, le a t → le t b → le (F t) (G t)) →
/// (∀ t, le a t → le t b → le (G t) (F t)) →
/// CReal.Equiv (CReal.integral F a b hab uF) (CReal.integral G a b hab uG)`
/// — **new content on ℝ**: the library had `integral_le` and no way to turn
/// a two-sided pointwise bound into an `Equiv` of integrals.
fn declare_creal_integral_congr(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let carrier = d.arrow(r, r);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let uf_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let ug_ty = d.const_app(c.uniformly_continuous_on, &[g, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);
    let ug_fv = d.fresh_fvar();
    let ug = d.kernel().fvar(ug_fv);

    let pointwise = |d: &mut IntDev<'_>, lo_f: ExprId, hi_f: ExprId| {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let l = d.apply(lo_f, &[t]);
        let rr = d.apply(hi_f, &[t]);
        let concl = rle(d, c, l, rr);
        let body = d.arrow(hi, concl);
        let body = d.arrow(lo, body);
        d.pi_fv(t_fv, r, body)
    };
    let h1_ty = pointwise(d, f, g);
    let h2_ty = pointwise(d, g, f);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let lhs = d.const_app(c.integral, &[f, a, b, hab, uf]);
    let rhs = d.const_app(c.integral, &[g, a, b, hab, ug]);

    let value = {
        let s = interval(d, p, a, b, hab);
        let body = d.lemma(p.integral_congr, &[s, f, g, uf, ug, h1, h2]);
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(ug_fv, ug_ty, t);
        let t = d.lam_fv(uf_fv, uf_ty, t);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, r, t);
        let t = d.lam_fv(a_fv, r, t);
        let t = d.lam_fv(g_fv, carrier, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(ug_fv, ug_ty, t);
        let t = d.pi_fv(uf_fv, uf_ty, t);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(b_fv, r, t);
        let t = d.pi_fv(a_fv, r, t);
        let t = d.pi_fv(g_fv, carrier, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_integral_congr, ty, value)
}

/// `IntSpace.CReal.integral_nonneg : ∀ F a b hab uF,
/// (∀ t, le a t → le t b → le CReal.zero (F t)) →
/// CReal.le CReal.zero (CReal.integral F a b hab uF)` — new content on ℝ.
fn declare_creal_integral_nonneg(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let carrier = d.arrow(r, r);
    let zero = rzero(d, c);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let uf_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);

    let h_ty = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let ft = d.apply(f, &[t]);
        let concl = rle(d, c, zero, ft);
        let body = d.arrow(hi, concl);
        let body = d.arrow(lo, body);
        d.pi_fv(t_fv, r, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let integral = d.const_app(c.integral, &[f, a, b, hab, uf]);

    let value = {
        let s = interval(d, p, a, b, hab);
        let body = d.lemma(p.integral_nonneg, &[s, f, uf, h]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(uf_fv, uf_ty, t);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, r, t);
        let t = d.lam_fv(a_fv, r, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = rle(d, c, zero, integral);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(uf_fv, uf_ty, t);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(b_fv, r, t);
        let t = d.pi_fv(a_fv, r, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_integral_nonneg, ty, value)
}

/// `IntSpace.CReal.sumRange_congr : ∀ f g m,
/// (∀ i, Nat.lt i (Nat.succ m) → CReal.le (f i) (g i)) →
/// (∀ i, Nat.lt i (Nat.succ m) → CReal.le (g i) (f i)) →
/// CReal.Equiv (CReal.sumRange f (Nat.succ m)) (CReal.sumRange g (Nat.succ m))`
/// — **the same generic theorem, on the finite instance.** One proof, two
/// carriers, and neither is the other's special case.
fn declare_creal_sum_range_congr(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let natp = d.prelude();
    let carrier = d.arrow(nat, r);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);

    let pointwise = |d: &mut IntDev<'_>, lo_f: ExprId, hi_f: ExprId| {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let l = d.apply(lo_f, &[i]);
        let rr = d.apply(hi_f, &[i]);
        let concl = rle(d, c, l, rr);
        let body = d.arrow(lt, concl);
        d.pi_fv(i_fv, nat, body)
    };
    let h1_ty = pointwise(d, f, g);
    let h2_ty = pointwise(d, g, f);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let lhs = d.const_app(c.sum_range, &[f, n]);
    let rhs = d.const_app(c.sum_range, &[g, n]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);

    let value = {
        let s = d.const_app(p.creal_finite, &[m]);
        let body = d.lemma(p.integral_congr, &[s, f, g, triv_mk, triv_mk, h1, h2]);
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(m_fv, nat, t);
        let t = d.lam_fv(g_fv, carrier, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.pi_fv(g_fv, carrier, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_sum_range_congr, ty, value)
}

/// `IntSpace.CReal.sumRange_nonneg : ∀ f m,
/// (∀ i, Nat.lt i (Nat.succ m) → CReal.le CReal.zero (f i)) →
/// CReal.le CReal.zero (CReal.sumRange f (Nat.succ m))`.
fn declare_creal_sum_range_nonneg(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let natp = d.prelude();
    let carrier = d.arrow(nat, r);
    let zero = rzero(d, c);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);

    let h_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.const_app(natp.lt, &[i, n]);
        let fi = d.apply(f, &[i]);
        let concl = rle(d, c, zero, fi);
        let body = d.arrow(lt, concl);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sum = d.const_app(c.sum_range, &[f, n]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);

    let value = {
        let s = d.const_app(p.creal_finite, &[m]);
        let body = d.lemma(p.integral_nonneg, &[s, f, triv_mk, h]);
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(m_fv, nat, t);
        d.lam_fv(f_fv, carrier, t)
    };
    let ty = {
        let concl = rle(d, c, zero, sum);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(m_fv, nat, t);
        d.pi_fv(f_fv, carrier, t)
    };
    theorem(d, p.creal_sum_range_nonneg, ty, value)
}
