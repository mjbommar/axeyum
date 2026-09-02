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

use super::monotone::{cneg, czero, echain, equiv_of_sub_equiv_zero, erefl, esymm, neg_zero_equiv};
use super::{CRealPrelude, and_intro, cadd, cle, clt, creal_ty, div_succ, embed, equiv};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
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
        name: p.inverse_fn.order_reflect_of_pos_deriv,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_exact_root_at` -- existence of the inverse, as a function: given
// a uniformly-positive-derivative `F` on `[a,b]` and ANY target `y` between
// `F a` and `F b`, there is an exact preimage `c` with `Equiv (F c) y`.
//
// `creal/ivt.rs`'s `ivt_exact_root` already proves exactly this at `y := 0`.
// This is not a re-derivation of that argument -- it is a wrapper applying
// `ivt_exact_root` to the SHIFTED function `G := fun z => F z - y`, whose
// zero set is `F`'s `y`-preimage set. `G`'s derivative is `F'` itself (a
// constant shift changes neither continuity nor the derivative bound), so
// the shift costs nothing on the hypotheses side: `hasDerivative_sub` and
// `uniformly_continuous_sub` compose `F`'s own data with
// `hasDerivative_const`/`uniformly_continuous_const` at `y`, and the
// derivative-bound hypothesis (`F' z` bounded below) transports to `G' z`
// through the ring identity `F' z ~ F' z - 0` (`add_zero` + `neg_zero`,
// `monotone.rs::neg_zero_equiv`) via `le_congr` -- no new estimate, purely
// algebraic. `G a <= 0 <= G b` is `add_le_add`/`add_neg` applied to the
// hypotheses `F a <= y <= F b`, the same shift on the other two endpoints.
// Once `ivt_exact_root` returns `Equiv (G c) zero`, `monotone.rs`'s own
// `equiv_of_sub_equiv_zero` (already built there for an unrelated purpose)
// reads it back as `Equiv (F c) y` directly.
// =============================================================================

/// `Exists CReal predicate` -- copied from `ivt.rs`'s private helper of the
/// same shape (that module is out of scope here; see its own doc comment for
/// why the universe is `level_one`, matching `Nat`'s).
fn cexists_ty(d: &mut IntDev<'_>, p: CRealPrelude, elem_ty: ExprId, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_const, &[elem_ty, pred])
}

fn cexists_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    pred: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let intro_name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[elem_ty, pred, witness, proof])
}

fn cexists_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists_const, &[elem_ty, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = p.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[elem_ty, predicate, motive, minor, witness])
}

/// `CReal.ivt_exact_root_at : ∀ F F' a b, HasDerivativeOn F F' a b →
/// UniformlyContinuousOn F a b → le a b → ∀ y, le (F a) y → le y (F b) →
/// ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
/// ∃ c, le a c ∧ (le c b ∧ Equiv (F c) y)`.
///
/// See the module documentation for the shift-by-`y` argument. Every
/// hypothesis this needs beyond `ivt_exact_root`'s own is exactly the same
/// shape at `y` that `ivt_exact_root` already takes at `0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_ivt_exact_root_at(
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

    let uc_ty_ab = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let fa = d.apply(f, &[a]);
    let hya_ty = cle(d, p, fa, y);
    let hya_fv = d.fresh_fvar();
    let hya = d.kernel().fvar(hya_fv);
    let fb = d.apply(f, &[b]);
    let hyb_ty = cle(d, p, y, fb);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let a_k_rat = div_succ(d, p, 1, k);
    let a_k = embed(d, p, a_k_rat);
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let concl = cle(d, p, a_k, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let zero_c = czero(d, p);

    // `const_y_fn := fun _ => y`, `const_zero_fn := fun _ => zero` -- the
    // exact shapes `hasDerivative_const`/`uniformly_continuous_const`
    // themselves produce, built by hand so `G`/`G'` below are literally the
    // terms `hasDerivative_sub`/`uniformly_continuous_sub` substitute in.
    let const_y_fn = {
        let ig_fv = d.fresh_fvar();
        d.lam_fv(ig_fv, carrier, y)
    };
    let const_zero_fn = {
        let ig_fv = d.fresh_fvar();
        d.lam_fv(ig_fv, carrier, zero_c)
    };

    // `g_expr := fun r => add (F r) (neg (const_y_fn r))` -- `G := F - y`.
    let g_expr = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let cyr = d.apply(const_y_fn, &[r]);
        let neg_cyr = cneg(d, p, cyr);
        let diff = cadd(d, p, fr, neg_cyr);
        d.lam_fv(r_fv, carrier, diff)
    };
    // `gp_expr := fun x => add (F' x) (neg (const_zero_fn x))` -- `G' := F'`,
    // up to the ring identity `F' x - 0 ~ F' x` transported below.
    let gp_expr = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let czx = d.apply(const_zero_fn, &[x]);
        let neg_czx = cneg(d, p, czx);
        let diff = cadd(d, p, fpx, neg_czx);
        d.lam_fv(x_fv, carrier, diff)
    };

    let hd_const_y = d.const_app(p.has_derivative_const, &[y, a, b]);
    let hd_g = d.const_app(
        p.has_derivative_sub,
        &[f, fp, const_y_fn, const_zero_fn, a, b, hf, hd_const_y],
    );

    let huc_const_y = d.const_app(p.uniformly_continuous_const, &[y, a, b]);
    let huc_g = d.const_app(
        p.uniformly_continuous_sub,
        &[f, const_y_fn, a, b, huc, huc_const_y],
    );

    // `hga : le (G a) zero` from `le (F a) y` -- shift both sides by `neg y`,
    // then rewrite `y + neg y` down to `zero` via `add_neg`.
    let hga = {
        let neg_y = cneg(d, p, y);
        let refl_neg_y = d.lemma(p.le_refl, &[neg_y]);
        let step = d.lemma(p.add_le_add, &[fa, y, neg_y, neg_y, hya, refl_neg_y]);
        let y_plus_negy = cadd(d, p, y, neg_y);
        let cancel = d.lemma(p.add_neg, &[y]);
        let lhs = cadd(d, p, fa, neg_y);
        let refl_lhs = erefl(d, p, lhs);
        d.lemma(
            p.le_congr,
            &[lhs, lhs, y_plus_negy, zero_c, refl_lhs, cancel, step],
        )
    };

    // `hgb : le zero (G b)` from `le y (F b)` -- the mirror shift.
    let hgb = {
        let neg_y = cneg(d, p, y);
        let refl_neg_y = d.lemma(p.le_refl, &[neg_y]);
        let step = d.lemma(p.add_le_add, &[y, fb, neg_y, neg_y, hyb, refl_neg_y]);
        let y_plus_negy = cadd(d, p, y, neg_y);
        let cancel = d.lemma(p.add_neg, &[y]);
        let rhs = cadd(d, p, fb, neg_y);
        let refl_rhs = erefl(d, p, rhs);
        d.lemma(
            p.le_congr,
            &[y_plus_negy, zero_c, rhs, rhs, cancel, refl_rhs, step],
        )
    };

    // `hderiv_g : ∀ z, le a z → le z b → le a_k (G' z)` -- transport
    // `hderiv`'s bound on `F' z` across `Equiv (F' z) (add (F' z) (neg
    // zero))` (`add_zero` + `neg_zero_equiv`, chained), which is exactly
    // `G' z` up to the `const_zero_fn z` beta reduction.
    let hderiv_g = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let hz1_fv = d.fresh_fvar();
        let hz1 = d.kernel().fvar(hz1_fv);
        let hz2_fv = d.fresh_fvar();
        let hz2 = d.kernel().fvar(hz2_fv);

        let orig = d.apply(hderiv, &[z, hz1, hz2]);
        let fpz = d.apply(fp, &[z]);

        let fpz_plus_zero = cadd(d, p, fpz, zero_c);
        let add_zero_fpz = d.lemma(p.add_zero, &[fpz]);
        let symm1 = esymm(d, p, fpz_plus_zero, fpz, add_zero_fpz);

        let neg_zero_c = cneg(d, p, zero_c);
        let nz_eq = neg_zero_equiv(d, p);
        let nz_eq_symm = esymm(d, p, neg_zero_c, zero_c, nz_eq);

        let refl_fpz = erefl(d, p, fpz);
        let fpz_plus_negzero = cadd(d, p, fpz, neg_zero_c);
        let cong = d.lemma(
            p.add_congr,
            &[fpz, fpz, zero_c, neg_zero_c, refl_fpz, nz_eq_symm],
        );
        let target_equiv = echain(
            d,
            p,
            fpz,
            &[(fpz_plus_zero, symm1), (fpz_plus_negzero, cong)],
        );

        let refl_ak = erefl(d, p, a_k);
        let transported = d.lemma(
            p.le_congr,
            &[a_k, a_k, fpz, fpz_plus_negzero, refl_ak, target_equiv, orig],
        );

        let hz2_ty = cle(d, p, z, b);
        let hz1_ty = cle(d, p, a, z);
        let with_hz2 = d.lam_fv(hz2_fv, hz2_ty, transported);
        let with_hz1 = d.lam_fv(hz1_fv, hz1_ty, with_hz2);
        d.lam_fv(z_fv, carrier, with_hz1)
    };

    let hex = d.const_app(
        p.ivt_exact_root,
        &[
            g_expr, gp_expr, a, b, hd_g, huc_g, hab, hga, hgb, k, hderiv_g,
        ],
    );

    // `g_root_pred := fun c => le a c ∧ (le c b ∧ Equiv (G c) zero)` -- the
    // predicate `hex`'s existential ranges over.
    let g_root_pred = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let le1 = cle(d, p, a, c);
        let le2 = cle(d, p, c, b);
        let gc = d.apply(g_expr, &[c]);
        let eq0 = equiv(d, p, gc, zero_c);
        let inner = d.and(le2, eq0);
        let body = d.and(le1, inner);
        d.lam_fv(c_fv, carrier, body)
    };

    // `root_pred := fun c => le a c ∧ (le c b ∧ Equiv (F c) y)` -- the
    // target's own predicate.
    let root_pred = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let le1 = cle(d, p, a, c);
        let le2 = cle(d, p, c, b);
        let fc = d.apply(f, &[c]);
        let eqy = equiv(d, p, fc, y);
        let inner = d.and(le2, eqy);
        let body = d.and(le1, inner);
        d.lam_fv(c_fv, carrier, body)
    };
    let target_ty = cexists_ty(d, p, carrier, root_pred);

    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        let le1 = cle(d, p, a, c);
        let le2 = cle(d, p, c, b);
        let gc = d.apply(g_expr, &[c]);
        let eq0 = equiv(d, p, gc, zero_c);
        let inner_ty = d.and(le2, eq0);
        let conj_ty_here = d.and(le1, inner_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let hac = d.and_left(le1, inner_ty, h);
        let rest = d.and_right(le1, inner_ty, h);
        let hcb = d.and_left(le2, eq0, rest);
        let heq0 = d.and_right(le2, eq0, rest);

        let fc = d.apply(f, &[c]);
        let heqy = equiv_of_sub_equiv_zero(d, p, fc, y, heq0);
        let eqy_ty = equiv(d, p, fc, y);

        let inner2_ty = d.and(le2, eqy_ty);
        let inner2 = and_intro(d, p, le2, eqy_ty, hcb, heqy);
        let conj2 = and_intro(d, p, le1, inner2_ty, hac, inner2);

        let body = cexists_intro(d, p, carrier, root_pred, c, conj2);
        let with_h = d.lam_fv(h_fv, conj_ty_here, body);
        d.lam_fv(c_fv, carrier, with_h)
    };

    let proof = cexists_elim(d, p, carrier, g_root_pred, target_ty, hex, minor);

    let value = {
        let over_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, proof);
        let over_k = d.lam_fv(k_fv, nat, over_hderiv);
        let over_hyb = d.lam_fv(hyb_fv, hyb_ty, over_k);
        let over_hya = d.lam_fv(hya_fv, hya_ty, over_hyb);
        let over_y = d.lam_fv(y_fv, carrier, over_hya);
        let over_hab = d.lam_fv(hab_fv, hab_ty, over_y);
        let over_huc = d.lam_fv(huc_fv, uc_ty_ab, over_hab);
        let over_hf = d.lam_fv(hf_fv, hf_ty, over_huc);
        let over_b = d.lam_fv(b_fv, carrier, over_hf);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_fp = d.lam_fv(fp_fv, func_ty, over_a);
        d.lam_fv(f_fv, func_ty, over_fp)
    };
    let ty = {
        let after_hderiv = d.arrow(hderiv_ty, target_ty);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hyb = d.arrow(hyb_ty, over_k);
        let after_hya = d.arrow(hya_ty, after_hyb);
        let over_y = d.pi_fv(y_fv, carrier, after_hya);
        let after_hab = d.arrow(hab_ty, over_y);
        let after_huc = d.arrow(uc_ty_ab, after_hab);
        let after_hf = d.arrow(hf_ty, after_huc);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inverse_fn.ivt_exact_root_at,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/inverse_fn.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InverseFnNames {
    /// `CReal.order_reflect_of_pos_deriv : ∀ F F' a b, HasDerivativeOn F F' a
    /// b → ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∀ x y, le a x → le x b → le a y → le y b → Apart x y → lt (F x) (F y)
    /// → lt x y` (`creal/inverse_fn.rs`) — the CONVERSE half of
    /// [`super::CRealPrelude::strict_mono_of_pos_deriv`], and the reason it is stated with
    /// `Apart x y` as a HYPOTHESIS rather than derived: producing `lt x y`
    /// from nothing but a codomain inequality would require deciding which
    /// of `lt x y`/`lt y x` holds, and `CReal.lt` is not decidable. Given
    /// `Apart x y` as DATA (not derived via excluded middle), the proof
    /// cases on it: the `lt x y` branch is the goal already; the `lt y x`
    /// branch applies [`super::CRealPrelude::strict_mono_of_pos_deriv`] to get
    /// `lt (F y) (F x)`, which together with the hypothesis `lt (F x) (F y)`
    /// gives `lt (F x) (F x)` via `lt_trans`, refuted by `lt_irrefl`.
    ///
    /// Unconditional order-reflection (no `Apart x y` hypothesis) is NOT
    /// proved here and is not reachable with this development's current
    /// machinery: it is exactly as hard as finding an exact preimage
    /// (`creal/ivt.rs`'s `ivt_approx`, still open), since both require
    /// turning a codomain inequality into domain POSITION information, which
    /// needs some form of bisection/localisation this file does not have in
    /// exact form.
    pub order_reflect_of_pos_deriv: NameId,
    /// `CReal.ivt_exact_root_at : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// UniformlyContinuousOn F a b → le a b → ∀ y, le (F a) y → le y (F b) →
    /// ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∃ c, le a c ∧ (le c b ∧ Equiv (F c) y)` (`creal/inverse_fn.rs`) —
    /// Chapter 12's EXISTENCE half: `F` has a genuine preimage for every
    /// target `y` between `F a` and `F b`, not just for `y = zero`.
    ///
    /// Not a re-derivation of [`super::CRealPrelude::ivt_exact_root`] — a wrapper applying
    /// it to the SHIFTED function `G := fun z => add (F z) (neg y)`, whose
    /// root is `F`'s `y`-preimage. `G`'s derivative and continuity come from
    /// [`super::CRealPrelude::has_derivative_sub`]/[`super::CRealPrelude::uniformly_continuous_sub`]
    /// composed with [`super::CRealPrelude::has_derivative_const`]/
    /// [`super::CRealPrelude::uniformly_continuous_const`] at `y` — a constant shift changes
    /// neither — and the derivative-bound hypothesis on `F'` transports to
    /// `G'` through the ring identity `F' z ~ F' z − 0`
    /// ([`super::CRealPrelude::add_zero`] plus `monotone.rs`'s private `neg_zero_equiv`,
    /// via [`super::CRealPrelude::le_congr`]). `G a ≤ 0 ≤ G b` is
    /// [`super::CRealPrelude::add_le_add`]/[`super::CRealPrelude::add_neg`] applied to `F a ≤ y ≤ F b`,
    /// the same shift at the other two endpoints. `ivt_exact_root`'s result
    /// `Equiv (G c) zero` reads back as `Equiv (F c) y` via `monotone.rs`'s
    /// `equiv_of_sub_equiv_zero`, built there for an unrelated purpose and
    /// reused here unchanged.
    pub ivt_exact_root_at: NameId,
}

impl InverseFnNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            order_reflect_of_pos_deriv: kernel.name_str(creal, "order_reflect_of_pos_deriv"),
            ivt_exact_root_at: kernel.name_str(creal, "ivt_exact_root_at"),
        }
    }
}
