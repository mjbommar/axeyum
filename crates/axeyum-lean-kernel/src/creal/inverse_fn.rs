//! Spivak ch. 12, inverse functions — the ORDER-REFLECTING direction.
//!
//! `creal/monotone.rs` already gives the forward half of "F is an order
//! embedding on `[a,b]`": `CReal.strict_mono_of_pos_deriv` (`x<y → Fx<Fy`)
//! and its apartness corollary `CReal.strict_injective_of_pos_deriv`
//! (`Apart x y → Apart (F x) (F y)`). The classical inverse function theorem
//! also needs the CONVERSE — order-reflection, `F x < F y → x < y` — to say
//! `F` has a genuine (order-preserving) inverse on its range.
//!
//! ## What is NOT provable here, and why
//!
//! **Unconditional order-reflection is out of reach with this development's
//! current machinery, and the obstruction is structural, not a missing
//! lemma.** Producing `x < y` from nothing but `F x < F y` requires DECIDING
//! which of `x < y` or `y < x` holds — `CReal.lt` is not decidable (see
//! `creal/monotone.rs`: "you cannot case-split on the ordering of two
//! reals"), and no algebraic manipulation manufactures that decision out of
//! a codomain inequality alone. Every attempt along that road (bounding
//! `y − x` below by a rescaled `F y − F x` via the derivative bound,
//! bisecting the domain to localise a preimage, …) either silently assumes
//! an order between `x` and `y` to even get started, or needs an EXACT
//! bisection/localisation step. The only bisection this development has is
//! `creal/ivt.rs`'s `ivt_step`/`ivt_iter`, which is approximate; the exact
//! `ivt_approx` is still open (blocked on a `pow`-vs-`natDivSucc` decay
//! bound). So exact order-reflection is exactly as hard as an exact
//! preimage — both convert a codomain fact into domain POSITION
//! information, which is IVT territory, not algebra.
//!
//! ## What IS provable, and why it is exactly the fact Chapter 12 needs
//!
//! [`declare_order_reflect_of_pos_deriv`] proves order-reflection
//! CONDITIONAL on already knowing `Apart x y`: given that disjunction as
//! DATA (not derived — it is a hypothesis, never manufactured by
//! excluded middle), case-splitting on it is completely valid. One branch
//! IS the goal; the other branch is refuted by combining
//! `strict_mono_of_pos_deriv` with transitivity and irreflexivity of `lt`.
//! This is precisely the fact Chapter 12 needs to compose with
//! `strict_injective_of_pos_deriv`: on any pair already known apart, `F` is
//! an order isomorphism onto its image (`Apart x y ↔ Apart (F x) (F y)`,
//! and within that, the SIGN of the apartness — which one is bigger —
//! matches up in both directions), even though the disjunction itself is
//! never manufactured from nothing.
//!
//! ## Continuity of the inverse, also conditional on `Apart`
//!
//! `creal/monotone.rs`'s `CReal.inverse_lipschitz_of_pos_deriv` is the
//! CONTINUITY half of the same story, built by the same case-split-on-given-
//! `Apart` idiom: `Apart x y → abs (x − y) ≤ (2k+2)·abs (F x − F y)`, with NO
//! codomain hypothesis at all. This is not the "bounding `y − x` below by a
//! rescaled `F y − F x`" route the section above rules out for UNCONDITIONAL
//! order-reflection — it never tries to derive `Apart x y` from a codomain
//! fact, only to bound a gap once `Apart x y` is already given, exactly the
//! same legitimate case split `order_reflect_of_pos_deriv` performs above.
//! It composes `CReal.strict_mono_magnitude` (the exact per-side rate
//! `strict_mono_of_pos_deriv` proves internally) with `CReal.scale_cancel_le`
//! and `CReal.abs_le`. See its own doc comment
//! (`CRealPrelude::inverse_lipschitz_of_pos_deriv`) for the full statement.

use super::{CRealPrelude, cle, clt, creal_ty, div_succ, embed};
use crate::KernelError;
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `CReal.order_reflect_of_pos_deriv : ∀ F F' a b, HasDerivativeOn F F' a b →
/// ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
/// ∀ x y, le a x → le x b → le a y → le y b → Apart x y →
/// lt (F x) (F y) → lt x y`.
///
/// See the module documentation for why `Apart x y` is a HYPOTHESIS here,
/// never derived.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_order_reflect_of_pos_deriv(
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

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // hderiv_ty : ∀ z, le a z → le z b → le a_k (F' z).
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let a_k_rat = div_succ(d, p, 1, k);
        let a_k = embed(d, p, a_k_rat);
        let concl = cle(d, p, a_k, fpz);
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

    // `hax`/`hyb` are only needed to shape the statement (`F` is total on
    // `[a,b]`, so `x`/`y` are constrained at both ends); the proof itself
    // only ever needs `hay`/`hxb` (the "other" endpoint bounds), to feed
    // `strict_mono_of_pos_deriv` in the `lt y x` branch.
    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hxb_ty = cle(d, p, x, b);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hay_ty = cle(d, p, a, y);
    let hay_fv = d.fresh_fvar();
    let hay = d.kernel().fvar(hay_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();

    let hap_ty = d.const_app(p.apart, &[x, y]);
    let hap_fv = d.fresh_fvar();
    let hap = d.kernel().fvar(hap_fv);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let hcodom_ty = clt(d, p, fx, fy);
    let hcodom_fv = d.fresh_fvar();
    let hcodom = d.kernel().fvar(hcodom_fv);

    let target = clt(d, p, x, y);
    let lt_xy_ty = target;
    let lt_yx_ty = clt(d, p, y, x);

    // Case on the GIVEN `Apart x y` — valid, since it is data, not an
    // excluded-middle split on the undecidable `CReal.lt`.
    let value_body = d.or_elim(
        lt_xy_ty,
        lt_yx_ty,
        target,
        hap,
        &|_d, hlt_xy| hlt_xy,
        &|d, hlt_yx| {
            // `lt y x` → `lt (F y) (F x)` via `strict_mono_of_pos_deriv`.
            let step = d.lemma(
                p.strict_mono_of_pos_deriv,
                &[f, fp, a, b, hf, k, hderiv, y, x, hay, hlt_yx, hxb],
            );
            // step : lt (F y) (F x). Together with `hcodom : lt (F x) (F y)`,
            // transitivity gives `lt (F x) (F x)`, refuted by irreflexivity.
            let combined = d.lemma(p.lt_trans, &[fx, fy, fx, hcodom, step]);
            let refuted = d.lemma(p.lt_irrefl, &[fx]);
            let false_proof = d.apply(refuted, &[combined]);
            d.absurd(target, false_proof)
        },
    );

    let value = {
        let with_hcodom = d.lam_fv(hcodom_fv, hcodom_ty, value_body);
        let with_hap = d.lam_fv(hap_fv, hap_ty, with_hcodom);
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, with_hap);
        let with_hay = d.lam_fv(hay_fv, hay_ty, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_hay);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        let with_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, with_x);
        let with_k = d.lam_fv(k_fv, nat, with_hderiv);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_k);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let after_hcodom = d.arrow(hcodom_ty, target);
        let after_hap = d.arrow(hap_ty, after_hcodom);
        let after_hyb = d.arrow(hyb_ty, after_hap);
        let after_hay = d.arrow(hay_ty, after_hyb);
        let after_hxb = d.arrow(hxb_ty, after_hay);
        let after_hax = d.arrow(hax_ty, after_hxb);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let after_hderiv = d.arrow(hderiv_ty, over_x);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hf = d.arrow(hf_ty, over_k);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.order_reflect_of_pos_deriv,
        uparams: vec![],
        ty,
        value,
    })
}
