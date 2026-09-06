//! **`Complex.hasDerivative_mul`** — the product rule on ℂ, and the one place
//! this shelf's ring calculus pays for itself outright.
//!
//! # The decomposition, and why it needs four hypotheses
//!
//! ```text
//! F(y)G(y) − F(x)G(x) − (F'(x)G(x) + F(x)G'(x))(y−x)
//!   = F(y)·[G(y) − G(x) − G'(x)(y−x)]        -- term 1
//!   + G(x)·[F(y) − F(x) − F'(x)(y−x)]        -- term 2
//!   + (F(y) − F(x))·G'(x)·(y−x)              -- term 3
//! ```
//!
//! Term 1 needs `|F(y)|` bounded, term 2 needs `|G(x)|` bounded, and term 3
//! needs BOTH `|G'(x)|` bounded and a modulus of continuity for **`F`** — not
//! for `G`. `creal/derivative.rs`'s module documentation records that its own
//! prose put the continuity requirement on the wrong function for a while and
//! had to be re-verified numerically; the formula above is the corrected one,
//! transcribed with `F` and `G` in the positions that make term 3's factor
//! `F(y) − F(x)`.
//!
//! So the statement carries four hypotheses that are **not** derived here:
//! `Complex.UniformlyContinuousOn F c r` and three `Complex.BoundedOn` facts
//! (on `F`, `G`, `G'`), exactly as `CReal.hasDerivative_mul` does. ADR-1642
//! sized the alternative (deriving them) and this file follows its
//! recommendation.
//!
//! # What ℂ gets for free: the six-leaf shuffle is one call
//!
//! `creal/derivative.rs` spends roughly five hundred lines showing that the
//! three terms above sum to the error term — `expand_bound_term` twice,
//! `expand_term3`, `cancel_middle`, and a hand-built eight-step associativity
//! and commutativity shuffle (`8a`…`8f`) that brings `−F(y)G(x)` and
//! `+G(x)F(y)` adjacent so they cancel. Here that is **one**
//! [`super::ring_law_proof`] call: `complex/ring.rs` normalises both sides to
//! a sorted multiset of signed monomials in the two real components and emits
//! the `Complex.Equiv` proof.
//!
//! What ℂ does **not** get for free is the accuracy budget. Three terms, each
//! rescaled by its own magnitude bound, have to fuse to one `1/(e+1)`; that is
//! `Rat.natDivSucc` arithmetic with no complex number in it, and it is reused
//! verbatim from `creal/derivative.rs` (`mul_modulus_components`,
//! `weaken_to_addend`, `fold_index0_first`/`_second`,
//! `fuse_three_equal_bounds`) rather than re-derived — see
//! `complex/estimates.rs`'s module documentation for why that reuse is exact
//! and not an approximation.
//!
//! # What is NOT here
//!
//! `Complex.hasDerivative_polyEval`. It is not blocked on the product rule any
//! more; it is blocked on the same thing the real shelf's general
//! `hasDerivative_pow` was blocked on, and for the same reason. An induction
//! over the degree applies this theorem at every step, and every step needs
//! THREE fresh `BoundedOn` facts (about the partial polynomial, about its
//! derivative, and about the next monomial) plus uniform continuity of the
//! accumulator — i.e. closure of `BoundedOn` and `UniformlyContinuousOn` under
//! `mul` and `add` on the disc.
//!
//! Two of the four are now landed:
//! [`super::estimates::EstimateNames::bounded_on_add`] and
//! [`super::estimates::EstimateNames::bounded_on_mul`], both cheap for the
//! reason `abs_mul_le_of_bounds` is cheap. What remains is
//! `Complex.uniformlyContinuous_mul` — whose real analogue
//! (`CReal.uniformly_continuous_mul`, `creal/uniform_continuity.rs`'s SECOND
//! entry point) needed the same product-of-bounds composition and is a slice
//! on the order of this file — and then the induction itself, which must also
//! carry `Complex.pow`'s own derivative. So the remaining work is bounded and
//! sized, not a new obstruction.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `complex/deriv.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::deriv::{
    abs_le_of_equiv, error_sym, fn_ty, hd_ty, in_disc_ty, of_div_succ, zabs, zadd, zmul, zsub,
};
use super::estimates::{bounded_on_ty, uc_ty};
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::Kernel;
use crate::KernelError;
use crate::creal::derivative::{
    fold_index0_first, fold_index0_second, fuse_three_equal_bounds, mag_bound,
    mul_modulus_components, weaken_to_addend,
};
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The names [`declare_leibniz`] declares, owned by this module rather than by
/// [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs`/`estimates.rs`
/// arrangement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeibnizNames {
    /// `Complex.hasDerivative_mul` — the product rule.
    pub has_derivative_mul: NameId,
}

/// Interns this module's names under `complex`. Called once from
/// `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> LeibnizNames {
    LeibnizNames {
        has_derivative_mul: kernel.name_str(complex, "hasDerivative_mul"),
    }
}

/// Declare the product rule.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_leibniz(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_has_derivative_mul(d, p)
}

/// `CReal.add a b`.
fn radd_c(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.add, &[a, b])
}

/// `CReal.mul a b`.
fn rmul(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.mul, &[a, b])
}

/// `CReal.Equiv.refl a`.
fn rrefl(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_refl, &[a])
}

/// `CReal.Equiv.symm` at `(a, b)` from a proof of `CReal.Equiv a b`.
fn rsymm_at(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_symm, &[a, b, h])
}

/// One of the product rule's first two terms, bounded.
///
/// From `outer_bound : le (abs p_val) (mag_bound k)` and
/// `error_bound : le (abs err) (mul (ofRat (1/(e'+1))) abs_diff)` (an
/// `HasDerivativeOn.spec` conclusion), derive
/// `le (abs (mul p_val err)) (mul (ofRat (1/(three_e+1))) abs_diff)`.
///
/// The two bounds multiply by [`super::estimates::EstimateNames::abs_mul_le_of_bounds`],
/// `CReal.mul_assoc` regroups `B·(s·|y−x|)` into `(B·s)·|y−x|`, and
/// [`fold_index0_first`] reads `B·s` back down to the term's equal share
/// `1/(three_e+1)`. This is `creal/derivative.rs`'s term1/term2 block, which
/// is identical for both terms there and is factored out here.
///
/// Returns `(out_bound, proof)`.
fn bound_scaled_error(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    p_val: ExprId,
    err: ExprId,
    k: ExprId,
    three_e: ExprId,
    e_prime: ExprId,
    abs_diff: ExprId,
    outer_bound: ExprId,
    error_bound: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let big = mag_bound(d, creal, k);
    let small = of_div_succ(d, p, 1, e_prime);
    let small_times_absdiff = rmul(d, p, small, abs_diff);

    let term = zmul(d, p, p_val, err);
    let abs_term = zabs(d, p, term);
    let upper = d.lemma(
        p.estimates.abs_mul_le_of_bounds,
        &[
            p_val,
            err,
            big,
            small_times_absdiff,
            outer_bound,
            error_bound,
        ],
    );
    // le (abs term) (mul big (mul small abs_diff))

    let assoc = d.lemma(creal.mul_assoc, &[big, small, abs_diff]);
    // Equiv (mul (mul big small) abs_diff) (mul big (mul small abs_diff))
    let mul_big_small = rmul(d, p, big, small);
    let regrouped = rmul(d, p, mul_big_small, abs_diff);
    let nested = rmul(d, p, big, small_times_absdiff);
    let assoc_symm = rsymm_at(d, p, regrouped, nested, assoc);

    let (_, _, ofr_out, fold) = fold_index0_first(d, creal, k, three_e, e_prime);
    let refl_absdiff = rrefl(d, p, abs_diff);
    let lift = d.lemma(
        creal.mul_congr,
        &[
            mul_big_small,
            ofr_out,
            abs_diff,
            abs_diff,
            fold,
            refl_absdiff,
        ],
    );
    let out_bound = rmul(d, p, ofr_out, abs_diff);
    // nested ~ regrouped ~ out_bound
    let refl_nested = rrefl(d, p, nested);
    let chain1 = d.lemma(
        creal.equiv_trans,
        &[nested, nested, regrouped, refl_nested, assoc_symm],
    );
    let bound_equiv = d.lemma(
        creal.equiv_trans,
        &[nested, regrouped, out_bound, chain1, lift],
    );

    let refl_abs_term = rrefl(d, p, abs_term);
    let bounded = d.lemma(
        creal.le_congr,
        &[
            abs_term,
            abs_term,
            nested,
            out_bound,
            refl_abs_term,
            bound_equiv,
            upper,
        ],
    );
    (out_bound, bounded)
}

/// `Complex.hasDerivative_mul : ∀ F F' G G' c r, HasDerivativeOn F F' c r →
/// HasDerivativeOn G G' c r → UniformlyContinuousOn F c r → ∀ k1 k2 k3,
/// BoundedOn F c r k1 → BoundedOn G c r k2 → BoundedOn G' c r k3 →
/// HasDerivativeOn (fun z => mul (F z) (G z))
///   (fun x => add (mul (F' x) (G x)) (mul (F x) (G' x))) c r`.
///
/// See the module documentation for the decomposition, which of its three
/// terms needs which hypothesis, and why the six-leaf algebraic shuffle the
/// real proof performs by hand is one [`super::ring_law_proof`] call here.
///
/// The three `BoundedOn` hypotheses take the raw inline shape rather than the
/// named `Complex.BoundedOn` constant, exactly as `CReal.hasDerivative_mul`'s
/// do: the two are definitionally equal (`Complex.bounded_on_unfold` is the
/// isolated confirmation), and the inline form is directly applicable at a
/// point without an intervening unfold.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_has_derivative_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let hf_ty = hd_ty(d, p, f, fp, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, c, r);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);
    let huc_ty = uc_ty(d, p, f, c, r);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);
    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);

    let hbf_ty = bounded_on_ty(d, p, f, c, r, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_ty(d, p, g, c, r, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);
    let hbgp_ty = bounded_on_ty(d, p, gp, c, r, k3);
    let hbgp_fv = d.fresh_fvar();
    let hbgp = d.kernel().fvar(hbgp_fv);

    let fmul = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let prod = zmul(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, prod)
    };
    let fmul_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let gx = d.apply(g, &[x]);
        let fx = d.apply(f, &[x]);
        let gpx = d.apply(gp, &[x]);
        let t1 = zmul(d, p, fpx, gx);
        let t2 = zmul(d, p, fx, gpx);
        let sum = zadd(d, p, t1, t2);
        d.lam_fv(x_fv, carrier, sum)
    };

    let mf = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);
    let mg = d.const_app(p.deriv.hd_modulus, &[g, gp, c, r, hg]);
    let mu = d.const_app(p.estimates.uc_modulus, &[f, c, r, huc]);

    let modulus_mul = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let (_, _, _, _, _, _, _, _, combined) =
            mul_modulus_components(d, mg, mf, mu, k1, k2, k3, e);
        d.lam_fv(e_fv, nat, combined)
    };

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdx = d.kernel().fvar(hdx_fv);
        let hdy_fv = d.fresh_fvar();
        let hdy = d.kernel().fvar(hdy_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let diff_yx = zsub(d, p, y, x);
        let abs_diff = zabs(d, p, diff_yx);

        let (three_e, e1p, e2p, e3, mg_val, mf_val, mu_val, mgf, combined) =
            mul_modulus_components(d, mg, mf, mu, k1, k2, k3, e);

        let mod_e = d.apply(modulus_mul, &[e]);
        let in_bound = of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        let (h_g, h_f, h_c) =
            weaken_to_addend(d, creal, abs_diff, combined, mgf, mg_val, mf_val, mu_val, h);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let fpx = d.apply(fp, &[x]);
        let gpx = d.apply(gp, &[x]);

        // --- term 1 = F(y) · [G's error at e1p] ---------------------------
        let g_error = {
            let gyx = zsub(d, p, gy, gx);
            let gderiv = zmul(d, p, gpx, diff_yx);
            zsub(d, p, gyx, gderiv)
        };
        let g_error_bound = d.lemma(
            p.deriv.hd_spec,
            &[g, gp, c, r, hg, e1p, x, y, hdx, hdy, h_g],
        );
        let hbf_y = d.apply(hbf, &[y, hdy]);
        let (out_bound1, term1_bound) = bound_scaled_error(
            d,
            p,
            fy,
            g_error,
            k1,
            three_e,
            e1p,
            abs_diff,
            hbf_y,
            g_error_bound,
        );
        let term1 = zmul(d, p, fy, g_error);
        let abs_term1 = zabs(d, p, term1);

        // --- term 2 = G(x) · [F's error at e2p] ---------------------------
        let f_error = {
            let fyx = zsub(d, p, fy, fx);
            let fderiv = zmul(d, p, fpx, diff_yx);
            zsub(d, p, fyx, fderiv)
        };
        let f_error_bound = d.lemma(
            p.deriv.hd_spec,
            &[f, fp, c, r, hf, e2p, x, y, hdx, hdy, h_f],
        );
        let hbg_x = d.apply(hbg, &[x, hdx]);
        let (out_bound2, term2_bound) = bound_scaled_error(
            d,
            p,
            gx,
            f_error,
            k2,
            three_e,
            e2p,
            abs_diff,
            hbg_x,
            f_error_bound,
        );
        let term2 = zmul(d, p, gx, f_error);
        let abs_term2 = zabs(d, p, term2);

        // --- term 3 = (F(y) − F(x)) · G'(x) · (y − x) ----------------------
        // Uniform continuity bounds `|F y − F x|` with NO `|y−x|` factor on
        // the right, so this term is closed by TWO product steps rather than
        // by one `hd_spec` call.
        let fy_fx = zsub(d, p, fy, fx);
        let uc_bound = d.lemma(
            p.estimates.uc_spec,
            &[f, c, r, huc, e3, y, x, hdy, hdx, h_c],
        );
        // le (abs fy_fx) (ofRat (natDivSucc 1 e3))
        let hbgp_x = d.apply(hbgp, &[x, hdx]);
        let big_b3 = mag_bound(d, creal, k3);
        let small3 = of_div_succ(d, p, 1, e3);
        let step3a = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[fy_fx, gpx, small3, big_b3, uc_bound, hbgp_x],
        );
        // le (abs (mul fy_fx gpx)) (mul small3 big_b3)
        let (_, _, ofr_out3, fold3) = fold_index0_second(d, creal, k3, three_e, e3);
        let mul_fyfx_gpx = zmul(d, p, fy_fx, gpx);
        let abs_mul_fyfx_gpx = zabs(d, p, mul_fyfx_gpx);
        let mul_small3_big3 = rmul(d, p, small3, big_b3);
        let refl_abs_mfg = rrefl(d, p, abs_mul_fyfx_gpx);
        let step3b = d.lemma(
            creal.le_congr,
            &[
                abs_mul_fyfx_gpx,
                abs_mul_fyfx_gpx,
                mul_small3_big3,
                ofr_out3,
                refl_abs_mfg,
                fold3,
                step3a,
            ],
        );
        let le_refl_absdiff = d.lemma(creal.le_refl, &[abs_diff]);
        let term3 = zmul(d, p, mul_fyfx_gpx, diff_yx);
        let abs_term3 = zabs(d, p, term3);
        let term3_bound = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[
                mul_fyfx_gpx,
                diff_yx,
                ofr_out3,
                abs_diff,
                step3b,
                le_refl_absdiff,
            ],
        );
        let out_bound3 = rmul(d, p, ofr_out3, abs_diff);

        // --- combine the three bounds through the triangle inequality -----
        let term1_plus_term2 = zadd(d, p, term1, term2);
        let combined_terms = zadd(d, p, term1_plus_term2, term3);

        let triangle_12 = d.lemma(p.abs_add_le, &[term1, term2]);
        let sum12_le = d.lemma(
            creal.add_le_add,
            &[
                abs_term1,
                out_bound1,
                abs_term2,
                out_bound2,
                term1_bound,
                term2_bound,
            ],
        );
        let abs_t1_plus_abs_t2 = radd_c(d, p, abs_term1, abs_term2);
        let ob1_plus_ob2 = radd_c(d, p, out_bound1, out_bound2);
        let abs_t1t2 = zabs(d, p, term1_plus_term2);
        let sum_ab_le = d.lemma(
            creal.le_trans,
            &[
                abs_t1t2,
                abs_t1_plus_abs_t2,
                ob1_plus_ob2,
                triangle_12,
                sum12_le,
            ],
        );

        let triangle_123 = d.lemma(p.abs_add_le, &[term1_plus_term2, term3]);
        let sum123_le = d.lemma(
            creal.add_le_add,
            &[
                abs_t1t2,
                ob1_plus_ob2,
                abs_term3,
                out_bound3,
                sum_ab_le,
                term3_bound,
            ],
        );
        let abs_t1t2_plus_abs_t3 = radd_c(d, p, abs_t1t2, abs_term3);
        let ob12_plus_ob3 = radd_c(d, p, ob1_plus_ob2, out_bound3);
        let abs_combined = zabs(d, p, combined_terms);
        let combined_le = d.lemma(
            creal.le_trans,
            &[
                abs_combined,
                abs_t1t2_plus_abs_t3,
                ob12_plus_ob3,
                triangle_123,
                sum123_le,
            ],
        );

        // --- fuse the three equal `1/(3e+3)` shares down to `1/(e+1)` -----
        let one_nat = d.num(1);
        let r1 = d.const_app(creal.rat.nat_div_succ, &[one_nat, three_e]);
        let r2 = d.const_app(creal.rat.nat_div_succ, &[one_nat, three_e]);
        let r3 = d.const_app(creal.rat.nat_div_succ, &[one_nat, three_e]);
        let ofr_out1 = of_div_succ(d, p, 1, three_e);
        let ofr_out2 = of_div_succ(d, p, 1, three_e);
        let (final_out_bound, fuse_proof) = fuse_three_equal_bounds(
            d, creal, e, three_e, ofr_out1, ofr_out2, ofr_out3, r1, r2, r3, abs_diff,
        );
        let refl_abs_combined = rrefl(d, p, abs_combined);
        let final_error_bound = d.lemma(
            creal.le_congr,
            &[
                abs_combined,
                abs_combined,
                ob12_plus_ob3,
                final_out_bound,
                refl_abs_combined,
                fuse_proof,
                combined_le,
            ],
        );

        // --- the ring identity, in ONE call -------------------------------
        let fmul_y = d.apply(fmul, &[y]);
        let fmul_x = d.apply(fmul, &[x]);
        let fmul_p_x = d.apply(fmul_p, &[x]);
        let deriv_term_mul = zmul(d, p, fmul_p_x, diff_yx);
        let fy_fx_mul = zsub(d, p, fmul_y, fmul_x);
        let actual_error = zsub(d, p, fy_fx_mul, deriv_term_mul);

        let fy_sym = CExpr::var(d, p, fy);
        let fx_sym = CExpr::var(d, p, fx);
        let gy_sym = CExpr::var(d, p, gy);
        let gx_sym = CExpr::var(d, p, gx);
        let fpx_sym = CExpr::var(d, p, fpx);
        let gpx_sym = CExpr::var(d, p, gpx);
        let x_sym = CExpr::var(d, p, x);
        let y_sym = CExpr::var(d, p, y);
        let diff_sym = CExpr::add(y_sym, CExpr::neg(x_sym));

        let actual_sym = error_sym(
            CExpr::mul(fy_sym.clone(), gy_sym.clone()),
            CExpr::mul(fx_sym.clone(), gx_sym.clone()),
            CExpr::add(
                CExpr::mul(fpx_sym.clone(), gx_sym.clone()),
                CExpr::mul(fx_sym.clone(), gpx_sym.clone()),
            ),
            diff_sym.clone(),
        );
        let term1_sym = CExpr::mul(
            fy_sym.clone(),
            error_sym(gy_sym, gx_sym.clone(), gpx_sym.clone(), diff_sym.clone()),
        );
        let term2_sym = CExpr::mul(
            gx_sym,
            error_sym(fy_sym.clone(), fx_sym.clone(), fpx_sym, diff_sym.clone()),
        );
        let term3_sym = CExpr::mul(
            CExpr::mul(CExpr::add(fy_sym, CExpr::neg(fx_sym)), gpx_sym),
            diff_sym,
        );
        let ring = ring_law_proof(
            d,
            p,
            &actual_sym,
            &CExpr::add(CExpr::add(term1_sym, term2_sym), term3_sym),
        );

        let conclusion = abs_le_of_equiv(
            d,
            p,
            actual_error,
            combined_terms,
            final_out_bound,
            ring,
            final_error_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[fmul, fmul_p, c, r, modulus_mul, spec]);
    let value = {
        let with_hbgp = d.lam_fv(hbgp_fv, hbgp_ty, mk_applied);
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, with_hbgp);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.lam_fv(k2_fv, nat, with_k3);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_huc = d.lam_fv(huc_fv, huc_ty, with_k1);
        let with_hg = d.lam_fv(hg_fv, hg_ty, with_huc);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_c);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fmul, fmul_p, c, r);
        let with_hbgp = d.arrow(hbgp_ty, applied);
        let with_hbg = d.arrow(hbg_ty, with_hbgp);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.pi_fv(k2_fv, nat, with_k3);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_huc = d.arrow(huc_ty, with_k1);
        let with_hg = d.arrow(hg_ty, with_huc);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_c);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.leibniz.has_derivative_mul,
        uparams: vec![],
        ty,
        value,
    })
}
