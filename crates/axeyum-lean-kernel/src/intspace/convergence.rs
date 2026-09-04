//! Monotone convergence, as an ADR-0603 **graded statement family**.
//!
//! | grade | declaration | status |
//! |---|---|---|
//! | general constructive form | [`IntSpacePrelude::integral_mono_step`], [`IntSpacePrelude::integral_seq_le`] | **proved**, footprint empty |
//! | classical form, on a hypothesis | [`IntSpacePrelude::monotone_convergence_of_real`] | **proved**, footprint empty, cost **one binder** |
//! | the classical principle itself | [`IntSpacePrelude::real_monotone_convergence`] | a `Prop`, never asserted |
//! | boundary refutation | see below | **NOT LANDED**, and the obstruction is named |
//!
//! ## What is constructive here, and what is not
//!
//! The constructive content of monotone convergence is entirely in the
//! integral: if `u₀ ≤ u₁ ≤ … ≤ f` pointwise then `∫u₀ ≤ ∫u₁ ≤ … ≤ ∫f`, and
//! both halves of that are one application of the record's `integralLe`
//! field. Nothing about an interval, a mesh or a modulus enters.
//!
//! What is *not* constructive is the last step, and it is not about
//! integration at all: **a bounded monotone sequence of reals need not
//! converge**. That is a statement about ℝ, it is of LPO strength, and it is
//! the whole gap between the two rows above. So the classical theorem is
//! stated the way ADR-1601 decided classical statements are stated — with the
//! principle as an explicit hypothesis
//! ([`IntSpacePrelude::real_monotone_convergence`]), never as an axiom — and
//! the measured cost of carrying it is **one binder and one argument
//! position**, matching ADR-1601's own ten-theorem measurement exactly.
//!
//! ## The boundary refutation that did NOT land, and why
//!
//! The converse — *unrestricted monotone convergence on any space with
//! `total ~ 1` implies `RealMonotoneConvergence`* — is the ADR-0603 boundary
//! member, and it is true: feed the space the constant sequence
//! `u n := S.fconst (s n)`, whose integrals are `s n · total ~ s n` by
//! `integralConst`. It is **not proved here**, and the obstruction is
//! specific and worth recording rather than hiding: transporting
//! `CReal.Converges` along a POINTWISE `Equiv` between two sequences needs a
//! congruence lemma the ℝ prelude does not have. It has
//! `CReal.converges_of_equiv` (a sequence exactly `Equiv` to a fixed
//! *target*), `CReal.converges_of_close` (a `Within` bound on the raw
//! samples) and `CReal.converges_unique`, and none of the three is
//! `∀ n, Equiv (f n) (g n) → Converges f L → Converges g L`. Adding that
//! lemma is the next declaration in this direction, it belongs in
//! `creal/convergence.rs` rather than here, and it is a `creal/` file this
//! lane was told not to expand into.

use super::{
    FLE, INTEGRABLE, INTEGRAL, IntSpacePrelude, definition, field, generic_space, rle, rty, theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_monotone_seq(d, p)?;
    declare_integral_mono_step(d, p)?;
    declare_integral_seq_le(d, p)?;
    declare_real_monotone_convergence(d, p)?;
    declare_monotone_convergence(d, p)?;
    declare_monotone_convergence_of_real(d, p)?;
    Ok(())
}

/// `Exists.{1} elem_ty predicate`.
fn exists_ty(d: &mut IntDev<'_>, p: IntSpacePrelude, elem_ty: ExprId, predicate: ExprId) -> ExprId {
    let one = d.level_one();
    let name = p.creal.rat.int.logic.exists_;
    let head = d.kernel().const_(name, vec![one]);
    d.apply(head, &[elem_ty, predicate])
}

/// `IntSpace.MonotoneSeq : ∀ (S : IntSpace), (Nat → S.carrier) → Prop
/// := fun S u => ∀ n, S.fle (u n) (u (Nat.succ n))`.
fn declare_monotone_seq(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let g = generic_space(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, g.carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let un = d.apply(u, &[n]);
    let sn = d.succ(n);
    let usn = d.apply(u, &[sn]);
    let fle = field(d, p, g.s, FLE);
    let step = d.apply(fle, &[un, usn]);
    let body = d.pi_fv(n_fv, nat, step);

    let value = {
        let t = d.lam_fv(u_fv, seq_ty, body);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(seq_ty, prop);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    definition(d, p.monotone_seq, ty, value)
}

/// `IntSpace.integral_mono_step : ∀ S u hu, MonotoneSeq S u → ∀ n,
/// CReal.le (S.integral (u n) (hu n)) (S.integral (u (succ n)) (hu (succ n)))`.
fn declare_integral_mono_step(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, g.carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // `hu : ∀ n, S.Integrable (u n)`.
    let hu_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let integrable = field(d, p, g.s, INTEGRABLE);
        let body = d.apply(integrable, &[um]);
        d.pi_fv(m_fv, nat, body)
    };
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let hm_ty = d.const_app(p.monotone_seq, &[g.s, u]);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let un = d.apply(u, &[n]);
    let sn = d.succ(n);
    let usn = d.apply(u, &[sn]);
    let hun = d.apply(hu, &[n]);
    let husn = d.apply(hu, &[sn]);
    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[un, hun]);
    let integral2 = field(d, p, g.s, INTEGRAL);
    let rhs = d.apply(integral2, &[usn, husn]);

    let value = {
        let ile = field(d, p, g.s, super::INTEGRAL_LE);
        let step = d.apply(hm, &[n]);
        let body = d.apply(ile, &[un, usn, hun, husn, step]);
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(hm_fv, hm_ty, t);
        let t = d.lam_fv(hu_fv, hu_ty, t);
        let t = d.lam_fv(u_fv, seq_ty, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, lhs, rhs);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.arrow(hm_ty, t);
        let t = d.pi_fv(hu_fv, hu_ty, t);
        let t = d.pi_fv(u_fv, seq_ty, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_mono_step, ty, value)
}

/// `IntSpace.integral_seq_le : ∀ S u hu f hf, (∀ n, S.fle (u n) f) → ∀ n,
/// CReal.le (S.integral (u n) (hu n)) (S.integral f hf)`.
fn declare_integral_seq_le(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, g.carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hu_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let integrable = field(d, p, g.s, INTEGRABLE);
        let body = d.apply(integrable, &[um]);
        d.pi_fv(m_fv, nat, body)
    };
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let hb_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let fle = field(d, p, g.s, FLE);
        let body = d.apply(fle, &[um, f]);
        d.pi_fv(m_fv, nat, body)
    };
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let un = d.apply(u, &[n]);
    let hun = d.apply(hu, &[n]);
    let integral = field(d, p, g.s, INTEGRAL);
    let lhs = d.apply(integral, &[un, hun]);
    let integral2 = field(d, p, g.s, INTEGRAL);
    let rhs = d.apply(integral2, &[f, hf]);

    let value = {
        let ile = field(d, p, g.s, super::INTEGRAL_LE);
        let step = d.apply(hb, &[n]);
        let body = d.apply(ile, &[un, f, hun, hf, step]);
        let t = d.lam_fv(n_fv, nat, body);
        let t = d.lam_fv(hb_fv, hb_ty, t);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        let t = d.lam_fv(hu_fv, hu_ty, t);
        let t = d.lam_fv(u_fv, seq_ty, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = rle(d, c, lhs, rhs);
        let t = d.pi_fv(n_fv, nat, concl);
        let t = d.arrow(hb_ty, t);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        let t = d.pi_fv(hu_fv, hu_ty, t);
        let t = d.pi_fv(u_fv, seq_ty, t);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    theorem(d, p.integral_seq_le, ty, value)
}

/// `IntSpace.RealMonotoneConvergence : Prop :=
/// ∀ (s : Nat → CReal) (B : CReal),
///   (∀ n, CReal.le (s n) (s (Nat.succ n))) → (∀ n, CReal.le (s n) B) →
///   ∃ L, CReal.Converges s L`.
///
/// **Never asserted.** This is the classical principle, of LPO strength, and
/// it exists here only to be a hypothesis (ADR-1601).
fn declare_real_monotone_convergence(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let nat = d.nat_ty();
    let r = rty(d, c);
    let seq_ty = d.arrow(nat, r);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let mono = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(s, &[n]);
        let succ_n = d.succ(n);
        let ssn = d.apply(s, &[succ_n]);
        let body = rle(d, c, sn, ssn);
        d.pi_fv(n_fv, nat, body)
    };
    let bounded = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(s, &[n]);
        let body = rle(d, c, sn, b);
        d.pi_fv(n_fv, nat, body)
    };
    let concl = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let conv = d.const_app(c.converges, &[s, l]);
        let pred = d.lam_fv(l_fv, r, conv);
        exists_ty(d, p, r, pred)
    };

    let value = {
        let t = d.arrow(bounded, concl);
        let t = d.arrow(mono, t);
        let t = d.pi_fv(b_fv, r, t);
        d.pi_fv(s_fv, seq_ty, t)
    };
    let ty = d.kernel().sort_zero();
    definition(d, p.real_monotone_convergence, ty, value)
}

/// `IntSpace.MonotoneConvergence : IntSpace → Prop`.
fn declare_monotone_convergence(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let nat = d.nat_ty();
    let r = rty(d, c);
    let seq_ty = d.arrow(nat, g.carrier);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hu_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let integrable = field(d, p, g.s, INTEGRABLE);
        let body = d.apply(integrable, &[um]);
        d.pi_fv(m_fv, nat, body)
    };
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let _hf = d.kernel().fvar(hf_fv);

    let hm_ty = d.const_app(p.monotone_seq, &[g.s, u]);
    let hb_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let fle = field(d, p, g.s, FLE);
        let body = d.apply(fle, &[um, f]);
        d.pi_fv(m_fv, nat, body)
    };

    // `fun n => S.integral (u n) (hu n)`.
    let int_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let un = d.apply(u, &[n]);
        let hun = d.apply(hu, &[n]);
        let integral = field(d, p, g.s, INTEGRAL);
        let body = d.apply(integral, &[un, hun]);
        d.lam_fv(n_fv, nat, body)
    };
    let concl = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let conv = d.const_app(c.converges, &[int_seq, l]);
        let pred = d.lam_fv(l_fv, r, conv);
        exists_ty(d, p, r, pred)
    };

    let value = {
        let t = d.arrow(hb_ty, concl);
        let t = d.arrow(hm_ty, t);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(f_fv, g.carrier, t);
        let t = d.pi_fv(hu_fv, hu_ty, t);
        let t = d.pi_fv(u_fv, seq_ty, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        d.arrow(g.space_ty, prop)
    };
    definition(d, p.monotone_convergence, ty, value)
}

/// `IntSpace.monotone_convergence_of_real : ∀ S,
/// RealMonotoneConvergence → MonotoneConvergence S`.
///
/// **The measurement ADR-1601 predicts and this file confirms:** the whole
/// cost of the classical theorem is one binder (`hR`) and one argument
/// position. The two constructive facts are fed to it unchanged; no new
/// obligation appears, and the footprint stays empty.
fn declare_monotone_convergence_of_real(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, g.carrier);

    let hr_ty = d.kernel().const_(p.real_monotone_convergence, vec![]);
    let hr_fv = d.fresh_fvar();
    let hr = d.kernel().fvar(hr_fv);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hu_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let integrable = field(d, p, g.s, INTEGRABLE);
        let body = d.apply(integrable, &[um]);
        d.pi_fv(m_fv, nat, body)
    };
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let integrable = field(d, p, g.s, INTEGRABLE);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let hm_ty = d.const_app(p.monotone_seq, &[g.s, u]);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);
    let hb_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let um = d.apply(u, &[m]);
        let fle = field(d, p, g.s, FLE);
        let body = d.apply(fle, &[um, f]);
        d.pi_fv(m_fv, nat, body)
    };
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let int_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let un = d.apply(u, &[n]);
        let hun = d.apply(hu, &[n]);
        let integral = field(d, p, g.s, INTEGRAL);
        let body = d.apply(integral, &[un, hun]);
        d.lam_fv(n_fv, nat, body)
    };
    let bound = {
        let integral = field(d, p, g.s, INTEGRAL);
        d.apply(integral, &[f, hf])
    };

    let value = {
        let mono = d.lemma(p.integral_mono_step, &[g.s, u, hu, hm]);
        let bounded = d.lemma(p.integral_seq_le, &[g.s, u, hu, f, hf, hb]);
        let body = d.apply(hr, &[int_seq, bound, mono, bounded]);
        let t = d.lam_fv(hb_fv, hb_ty, body);
        let t = d.lam_fv(hm_fv, hm_ty, t);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(f_fv, g.carrier, t);
        let t = d.lam_fv(hu_fv, hu_ty, t);
        let t = d.lam_fv(u_fv, seq_ty, t);
        let t = d.lam_fv(hr_fv, hr_ty, t);
        d.lam_fv(g.s_fv, g.space_ty, t)
    };
    let ty = {
        let concl = d.const_app(p.monotone_convergence, &[g.s]);
        let t = d.arrow(hr_ty, concl);
        d.pi_fv(g.s_fv, g.space_ty, t)
    };
    let _ = c;
    theorem(d, p.monotone_convergence_of_real, ty, value)
}
