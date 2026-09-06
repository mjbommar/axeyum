//! **The disc-membership bridge** — turning the interval hypotheses a real
//! `CReal.HasDerivativeOn` supplies into the `Complex.InDisc` memberships a
//! `Complex.HasDerivativeOn` demands, along a horizontal or vertical segment
//! through the centre.
//!
//! # The gap this closes, stated precisely
//!
//! `Complex.HasDerivativeOn.spec` guards its conclusion behind
//! `InDisc c r x → InDisc c r y → …`. `CReal.HasDerivativeOn.spec` guards its
//! own behind `le a x → le x b → le a y → le y b → …`. A Cauchy–Riemann
//! argument walks a real parameter along a segment through `c` and must, at
//! every point, hand the complex spec a membership built out of the real
//! interval facts it holds. Nothing in `complex/deriv.rs` does that: `InDisc`
//! is a statement about `Complex.abs`, and no lemma related `Complex.abs` of a
//! point on a segment to `CReal.abs` of its real offset.
//!
//! # What it costs: one ring identity and one isometry
//!
//! Parametrise the horizontal segment through `c` by its real offset `u`, so
//! the point is `c + ofReal u`. Then
//!
//! ```text
//! (c + ofReal u) − c  ~  ofReal u
//! ```
//!
//! is a two-atom ring identity — one [`super::ring_law_proof`] call, `c` and
//! `ofReal u` both opaque — and
//! [`super::components::ComponentNames::abs_of_real`] (`Complex.abs (ofReal t)
//! ~ CReal.abs t`, the statement that ℝ ↪ ℂ is an isometry) converts the
//! modulus. `CReal.le_congr` then carries the caller's real bound across both
//! steps. That is the whole of [`CauchyRiemannNames::in_disc_ofReal_offset`]:
//! **two rewriting steps, no estimate, no modulus arithmetic.**
//!
//! The vertical segment costs one lemma more, because
//! `Complex.abs (I · ofReal v)` has to lose its `I`:
//! [`CauchyRiemannNames::abs_I`] (`Complex.abs I ~ CReal.one`, by the same
//! `normSq`-then-`sqrt` route `Complex.abs_one` and `Complex.abs_zero` take)
//! feeds [`ComplexPrelude::abs_mul`], and `CReal.one_mul` collapses the
//! product.
//!
//! # The hypothesis shape is `le u r` and `le (neg u) r`, deliberately
//!
//! [`CauchyRiemannNames::in_disc_of_two_sided`] takes the two ONE-SIDED bounds
//! rather than `le (abs u) r`, because that is the form the interval facts
//! arrive in: `le a t` and `le t b` on a segment centred at `c` re-centre to
//! exactly `le (neg u) s` and `le u s`. `CReal.abs_le` (which is `max_le`
//! verbatim) closes the two into the modulus bound with no order algebra at
//! the call site.
//!
//! # What is NOT here
//!
//! The Cauchy–Riemann equations themselves. They are not blocked on this
//! bridge any more; they are blocked on a *component-extraction* lemma with no
//! analogue yet on either shelf: from `Complex.HasDerivativeOn F F' c r` one
//! must produce `CReal.HasDerivativeOn (fun t => re (F (c + ofReal t))) (fun t
//! => re (F' (c + ofReal t))) a b`, i.e. push the complex error bound down to
//! its real part. `Complex.abs_re_le` gives the inequality direction needed,
//! but the modulus must also be transported (the complex modulus is stated
//! against `Complex.abs (y − x)`, the real one against `CReal.abs (y − x)`,
//! and on a horizontal segment those agree only through
//! [`CauchyRiemannNames::in_disc_ofReal_offset`]'s own identity), and the real
//! spec's error term `(u(y) − u(x)) − u'(x)(y − x)` must be recognised as the
//! real part of the complex one — a `re`-congruence over `add`/`neg`/`mul`
//! that `complex.rs` has for `Equiv` but not as a distribution law over the
//! product. ADR-1656 sizes that as the next slice.

// Proof scripts are straight-line term constructions with short mathematical
// names, exactly as in `complex/deriv.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::deriv::{in_disc_ty, rchain, zabs, zadd, zmul, zsub};
use super::ring::{RExpr, render as rrender, ring_proof};
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The names [`declare_cauchy_riemann`] declares, owned by this module rather
/// than by [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs` arrangement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CauchyRiemannNames {
    /// `Complex.abs_I : CReal.Equiv (Complex.abs Complex.I) CReal.one`.
    pub abs_i: NameId,
    /// `Complex.inDisc_ofReal_offset : ∀ c r u, CReal.le (CReal.abs u) r →
    /// Complex.InDisc c r (Complex.add c (Complex.ofReal u))`.
    pub in_disc_of_real_offset: NameId,
    /// `Complex.inDisc_I_offset : ∀ c r v, CReal.le (CReal.abs v) r →
    /// Complex.InDisc c r (Complex.add c (Complex.mul Complex.I
    /// (Complex.ofReal v)))`.
    pub in_disc_i_offset: NameId,
    /// `Complex.inDisc_of_two_sided : ∀ c r u, CReal.le u r →
    /// CReal.le (CReal.neg u) r →
    /// Complex.InDisc c r (Complex.add c (Complex.ofReal u))`.
    pub in_disc_of_two_sided: NameId,
    /// `Complex.inDisc_I_of_two_sided : ∀ c r v, CReal.le v r →
    /// CReal.le (CReal.neg v) r → Complex.InDisc c r (Complex.add c
    /// (Complex.mul Complex.I (Complex.ofReal v)))`.
    pub in_disc_i_of_two_sided: NameId,
}

/// Interns this module's names under `complex`. Called once from
/// `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> CauchyRiemannNames {
    CauchyRiemannNames {
        abs_i: kernel.name_str(complex, "abs_I"),
        in_disc_of_real_offset: kernel.name_str(complex, "inDisc_ofReal_offset"),
        in_disc_i_offset: kernel.name_str(complex, "inDisc_I_offset"),
        in_disc_of_two_sided: kernel.name_str(complex, "inDisc_of_two_sided"),
        in_disc_i_of_two_sided: kernel.name_str(complex, "inDisc_I_of_two_sided"),
    }
}

/// Declare the disc-membership bridge.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cauchy_riemann(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    declare_abs_i(d, p)?;
    declare_in_disc_of_real_offset(d, p)?;
    declare_in_disc_i_offset(d, p)?;
    declare_in_disc_of_two_sided(d, p)?;
    declare_in_disc_i_of_two_sided(d, p)
}

/// `Complex.abs_I : CReal.Equiv (Complex.abs Complex.I) CReal.one`.
///
/// `Complex.I` is `mk zero one`, so `normSq I` δι-unfolds to
/// `add (mul zero zero) (mul one one)`, which [`ring_proof`] equates with
/// `CReal.one`; `CReal.sqrt_congr` carries that under the root and
/// `CReal.sqrt_one` finishes. Exactly the route `Complex.abs_one` and
/// `Complex.abs_zero` take.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_i(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let rone = d.kernel().const_(creal.one, vec![]);

    let lit = RExpr::add(
        RExpr::mul(RExpr::Zero, RExpr::Zero),
        RExpr::mul(RExpr::One, RExpr::One),
    );
    let lit_term = rrender(d, creal, &lit);
    let lit_one = ring_proof(d, creal, &lit, &RExpr::One);

    let sqrt_lit = d.const_app(creal.sqrt, &[lit_term]);
    let sqrt_one_term = d.const_app(creal.sqrt, &[rone]);
    let step1 = d.lemma(creal.sqrt_congr, &[lit_term, rone, lit_one]);
    let step2 = d.kernel().const_(creal.sqrt_one, vec![]);
    let value = rchain(d, creal, sqrt_lit, &[(sqrt_one_term, step1), (rone, step2)]);

    let ty = {
        let i_z = d.kernel().const_(p.i, vec![]);
        let abs_i_z = zabs(d, p, i_z);
        d.const_app(creal.equiv, &[abs_i_z, rone])
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_riemann.abs_i,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `offset_equiv : Complex.Equiv (Complex.add (add c w) (neg c)) w` and
/// `abs_equiv : CReal.Equiv (Complex.abs w) m`, plus `h : CReal.le m r`,
/// derive `CReal.le (Complex.abs (add (add c w) (neg c))) r` — i.e.
/// `Complex.InDisc c r (add c w)` after `InDisc`'s own delta step.
///
/// The shared tail of both offset lemmas; only `w` and the modulus rewrite
/// differ between the horizontal and the vertical case.
fn disc_from_modulus(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    r: ExprId,
    w: ExprId,
    m: ExprId,
    offset_equiv: ExprId,
    abs_equiv: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let point = zadd(d, p, c, w);
    let diff = zsub(d, p, point, c);
    let abs_diff = zabs(d, p, diff);
    let abs_w = zabs(d, p, w);

    // abs_diff ~ abs_w ~ m
    let lift = d.lemma(p.abs_congr, &[diff, w, offset_equiv]);
    let chain = rchain(d, creal, abs_diff, &[(abs_w, lift), (m, abs_equiv)]);
    // chain : Equiv abs_diff m
    let back = d.lemma(creal.equiv_symm, &[abs_diff, m, chain]);
    // back : Equiv m abs_diff
    let refl_r = d.lemma(creal.equiv_refl, &[r]);
    d.lemma(creal.le_congr, &[m, abs_diff, r, r, back, refl_r, h])
}

/// `Complex.inDisc_ofReal_offset : ∀ c r u, CReal.le (CReal.abs u) r →
/// Complex.InDisc c r (Complex.add c (Complex.ofReal u))` — a point on the
/// horizontal segment through `c` lies in the disc as soon as its real offset
/// does.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_in_disc_of_real_offset(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let w = d.const_app(p.of_real, &[u]);
    let abs_u = d.const_app(creal.abs, &[u]);
    let hyp_ty = d.const_app(creal.le, &[abs_u, r]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `(c + w) − c ~ w`, two opaque atoms.
    let offset_equiv = {
        let c_sym = CExpr::var(d, p, c);
        let w_sym = CExpr::var(d, p, w);
        let lhs = CExpr::add(CExpr::add(c_sym.clone(), w_sym.clone()), CExpr::neg(c_sym));
        ring_law_proof(d, p, &lhs, &w_sym)
    };
    // `Complex.abs (ofReal u) ~ CReal.abs u`.
    let abs_equiv = d.lemma(p.components.abs_of_real, &[u]);

    let body = disc_from_modulus(d, p, c, r, w, abs_u, offset_equiv, abs_equiv, h);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, body);
        let with_u = d.lam_fv(u_fv, real, with_h);
        let with_r = d.lam_fv(r_fv, real, with_u);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let point = zadd(d, p, c, w);
        let concl = in_disc_ty(d, p, c, r, point);
        let with_h = d.arrow(hyp_ty, concl);
        let with_u = d.pi_fv(u_fv, real, with_h);
        let with_r = d.pi_fv(r_fv, real, with_u);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_riemann.in_disc_of_real_offset,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.inDisc_I_offset : ∀ c r v, CReal.le (CReal.abs v) r →
/// Complex.InDisc c r (Complex.add c (Complex.mul Complex.I
/// (Complex.ofReal v)))` — the vertical segment, one lemma dearer than the
/// horizontal one because the `I` has to be removed from the modulus.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_in_disc_i_offset(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let i_z = d.kernel().const_(p.i, vec![]);
    let ofr_v = d.const_app(p.of_real, &[v]);
    let w = zmul(d, p, i_z, ofr_v);
    let abs_v = d.const_app(creal.abs, &[v]);
    let hyp_ty = d.const_app(creal.le, &[abs_v, r]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let offset_equiv = {
        let c_sym = CExpr::var(d, p, c);
        let w_sym = CExpr::var(d, p, w);
        let lhs = CExpr::add(CExpr::add(c_sym.clone(), w_sym.clone()), CExpr::neg(c_sym));
        ring_law_proof(d, p, &lhs, &w_sym)
    };

    // `abs (I · ofReal v) ~ abs I · abs (ofReal v) ~ one · abs v ~ abs v`.
    let abs_equiv = {
        let abs_w = zabs(d, p, w);
        let abs_i = zabs(d, p, i_z);
        let abs_ofr = zabs(d, p, ofr_v);
        let rone = d.kernel().const_(creal.one, vec![]);

        let split = d.lemma(p.abs_mul, &[i_z, ofr_v]);
        // split : Equiv (abs w) (mul (abs I) (abs (ofReal v)))
        let prod = d.const_app(creal.mul, &[abs_i, abs_ofr]);

        let i_one = d.kernel().const_(p.cauchy_riemann.abs_i, vec![]);
        let ofr_eq = d.lemma(p.components.abs_of_real, &[v]);
        let collapse = d.lemma(
            creal.mul_congr,
            &[abs_i, rone, abs_ofr, abs_v, i_one, ofr_eq],
        );
        // collapse : Equiv prod (mul one (abs v))
        let one_absv = d.const_app(creal.mul, &[rone, abs_v]);

        // `mul one (abs v) ~ abs v`, by `mul_comm` then `mul_one`.
        let absv_one = d.const_app(creal.mul, &[abs_v, rone]);
        let comm = d.lemma(creal.mul_comm, &[rone, abs_v]);
        let mo = d.lemma(creal.mul_one, &[abs_v]);
        let unit = rchain(d, creal, one_absv, &[(absv_one, comm), (abs_v, mo)]);

        rchain(
            d,
            creal,
            abs_w,
            &[(prod, split), (one_absv, collapse), (abs_v, unit)],
        )
    };

    let body = disc_from_modulus(d, p, c, r, w, abs_v, offset_equiv, abs_equiv, h);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, body);
        let with_v = d.lam_fv(v_fv, real, with_h);
        let with_r = d.lam_fv(r_fv, real, with_v);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let point = zadd(d, p, c, w);
        let concl = in_disc_ty(d, p, c, r, point);
        let with_h = d.arrow(hyp_ty, concl);
        let with_v = d.pi_fv(v_fv, real, with_h);
        let with_r = d.pi_fv(r_fv, real, with_v);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_riemann.in_disc_i_offset,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.inDisc_of_two_sided : ∀ c r u, CReal.le u r → CReal.le (neg u) r →
/// Complex.InDisc c r (Complex.add c (Complex.ofReal u))` — the form the
/// interval hypotheses arrive in.
///
/// `CReal.abs_le` (which is `max_le` verbatim) folds the two one-sided bounds
/// into the modulus bound [`declare_in_disc_of_real_offset`] takes.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_in_disc_of_two_sided(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let neg_u = d.const_app(creal.neg, &[u]);
    let hi_ty = d.const_app(creal.le, &[u, r]);
    let lo_ty = d.const_app(creal.le, &[neg_u, r]);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let lo_fv = d.fresh_fvar();
    let lo = d.kernel().fvar(lo_fv);

    let abs_bound = d.lemma(creal.abs_le, &[u, r, hi, lo]);
    let body = d.lemma(
        p.cauchy_riemann.in_disc_of_real_offset,
        &[c, r, u, abs_bound],
    );

    let value = {
        let with_lo = d.lam_fv(lo_fv, lo_ty, body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_lo);
        let with_u = d.lam_fv(u_fv, real, with_hi);
        let with_r = d.lam_fv(r_fv, real, with_u);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let w = d.const_app(p.of_real, &[u]);
        let point = zadd(d, p, c, w);
        let concl = in_disc_ty(d, p, c, r, point);
        let with_lo = d.arrow(lo_ty, concl);
        let with_hi = d.arrow(hi_ty, with_lo);
        let with_u = d.pi_fv(u_fv, real, with_hi);
        let with_r = d.pi_fv(r_fv, real, with_u);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_riemann.in_disc_of_two_sided,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.inDisc_I_of_two_sided` — [`declare_in_disc_of_two_sided`] on the
/// vertical segment.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_in_disc_i_of_two_sided(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let neg_v = d.const_app(creal.neg, &[v]);
    let hi_ty = d.const_app(creal.le, &[v, r]);
    let lo_ty = d.const_app(creal.le, &[neg_v, r]);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let lo_fv = d.fresh_fvar();
    let lo = d.kernel().fvar(lo_fv);

    let abs_bound = d.lemma(creal.abs_le, &[v, r, hi, lo]);
    let body = d.lemma(p.cauchy_riemann.in_disc_i_offset, &[c, r, v, abs_bound]);

    let value = {
        let with_lo = d.lam_fv(lo_fv, lo_ty, body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_lo);
        let with_v = d.lam_fv(v_fv, real, with_hi);
        let with_r = d.lam_fv(r_fv, real, with_v);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let i_z = d.kernel().const_(p.i, vec![]);
        let ofr_v = d.const_app(p.of_real, &[v]);
        let w = zmul(d, p, i_z, ofr_v);
        let point = zadd(d, p, c, w);
        let concl = in_disc_ty(d, p, c, r, point);
        let with_lo = d.arrow(lo_ty, concl);
        let with_hi = d.arrow(hi_ty, with_lo);
        let with_v = d.pi_fv(v_fv, real, with_hi);
        let with_r = d.pi_fv(r_fv, real, with_v);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_riemann.in_disc_i_of_two_sided,
        uparams: vec![],
        ty,
        value,
    })
}
