//! **Closure of `Complex.UniformlyContinuousOn` under `+` and `·`** — the two
//! facts `complex/leibniz.rs`'s module documentation names as the last
//! obstruction between `Complex.hasDerivative_mul` and a derivative for a
//! polynomial.
//!
//! # Why this file exists
//!
//! `Complex.hasDerivative_mul` takes four hypotheses it does not derive: a
//! modulus of continuity for `F`, and `Complex.BoundedOn` for `F`, `G` and
//! `G'`. An induction over a polynomial's degree applies it at every step, so
//! every step must *rebuild* those four for the accumulated partial
//! polynomial. Two of the four were already closed —
//! [`super::estimates::EstimateNames::bounded_on_add`] and
//! [`super::estimates::EstimateNames::bounded_on_mul`]. The other two are here.
//!
//! # The two proofs are `creal/uniform_continuity.rs`'s, position for position
//!
//! | real (`creal/uniform_continuity.rs`) | complex (this file) |
//! | --- | --- |
//! | `CReal.uniformly_continuous_add` | `Complex.uniformlyContinuous_add` |
//! | `CReal.uniformly_continuous_mul` | `Complex.uniformlyContinuous_mul` |
//! | four interval hypotheses `le a x`, `le x b`, … | two disc memberships `InDisc c r x`, `InDisc c r y` |
//! | `CReal.abs` | [`ComplexPrelude::abs`] |
//! | a hand-built `add4_comm`/`neg_add` shuffle | one [`super::ring_law_proof`] call |
//! | `product_diff_identity`, ~60 lines of `left_distrib`/`mul_comm`/`neg_congr` | one [`super::ring_law_proof`] call |
//!
//! Everything **after** the modulus is taken lives in `CReal`, because
//! `Complex.UniformlyContinuousOn`'s bound is `CReal.le (Complex.abs …)
//! (CReal.ofRat …)`. So the whole accuracy budget — `Rat.natDivSucc_antitone`
//! to weaken the combined modulus down to each factor's own,
//! `Rat.natDivSucc_scale` (through [`fold_index0_first`]) to absorb a magnitude
//! weight, and `Rat.natDivSucc_add`/`_halve` to fuse two `1/(2n+2)` shares into
//! `1/(n+1)` — is reused **verbatim** from the real shelf rather than
//! re-derived. That reuse is exact, not an approximation: none of those lemmas
//! mentions a carrier at all.
//!
//! What ℂ genuinely buys is the algebra. The real `mul` proof spends
//! `product_diff_identity` — a private ~60-line construction — showing
//! `F(x)G(x) − F(y)G(y) = F(x)(G(x) − G(y)) + G(y)(F(x) − F(y))`. Here that
//! identity, and the `add` proof's own four-leaf regrouping, are single
//! [`super::ring_law_proof`] calls: `complex/ring.rs` normalises both sides to
//! a sorted multiset of signed monomials in the two real components.
//!
//! # The estimate, worked on paper first
//!
//! For `add`, target accuracy `n` splits two ways at `m := 2n+1`
//! (`Rat.natDivSucc_halve`), each factor consulted at `m` and the combined
//! modulus `mF(m) + mG(m)`.
//!
//! For `mul`, each of the two shares must additionally absorb its own
//! magnitude weight: `(k₁+1)·X ≤ 1/(2n+2)` needs `X ≤ 1/((k₁+1)(2n+2))`, which
//! is `G`'s own spec read at `e_g := rescale_index(k₁, m) = (k₁+1)·m + k₁` —
//! `Rat.natDivSucc_scale`'s own index shape, and the reason `e_g` may not be
//! spelled any other way. Symmetrically `e_f := rescale_index(k₂, m)` weights
//! `F`'s error by `G`'s bound, since term two is `G(y)·(F(x) − F(y))`. The
//! combined modulus is `mG(e_g) + mF(e_f)`.
//!
//! Concretely, with `k₁ = 0` and `n = 1` (so `m = 3`): `e_g = 1·3 + 0 = 3`,
//! and `(0+1)/(3+1) = 1/4 = natDivSucc 1 3`, matching `m = 3` on the nose.
//!
//! # What the two mutants say
//!
//! ADR-1656 records both. Ignoring one of the two moduli in `modulus_mul`
//! (taking `mG(e_g)` alone) is rejected by the kernel, because the weakening
//! step `Rat.natDivSucc_antitone` then has no `Nat.le` to run on — the
//! combined-modulus hypothesis is *load-bearing in the proof term*, not a
//! comment about it.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `complex/leibniz.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::deriv::{fn_ty, in_disc_ty, of_div_succ, zabs, zadd, zmul, zsub};
use super::estimates::{bounded_on_ty, uc_ty};
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::Kernel;
use crate::KernelError;
use crate::creal::derivative::{fold_index0_first, rescale_index};
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite};

/// The names [`declare_uc_closure`] declares, owned by this module rather than
/// by [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs`/`estimates.rs`
/// arrangement, so a new declaration inside this file never touches
/// `complex.rs`'s struct, `STEPS` table, or `intern_names`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UcClosureNames {
    /// `Complex.uniformlyContinuous_add : ∀ F G c r, UniformlyContinuousOn F c r →
    /// UniformlyContinuousOn G c r →
    /// UniformlyContinuousOn (fun z => add (F z) (G z)) c r`.
    pub uniformly_continuous_add: NameId,
    /// `Complex.uniformlyContinuous_mul : ∀ F G c r, UniformlyContinuousOn F c r →
    /// UniformlyContinuousOn G c r → ∀ k1 k2, BoundedOn F c r k1 →
    /// BoundedOn G c r k2 →
    /// UniformlyContinuousOn (fun z => mul (F z) (G z)) c r`.
    pub uniformly_continuous_mul: NameId,
}

/// Interns this module's names under `complex`. Called once from
/// `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> UcClosureNames {
    UcClosureNames {
        uniformly_continuous_add: kernel.name_str(complex, "uniformlyContinuous_add"),
        uniformly_continuous_mul: kernel.name_str(complex, "uniformlyContinuous_mul"),
    }
}

/// Declare closure of uniform continuity under `+` and `·`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_uc_closure(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_uniformly_continuous_add(d, p)?;
    declare_uniformly_continuous_mul(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

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

/// `Rat.natDivSucc k j` with a literal numerator.
fn div_succ(d: &mut IntDev<'_>, p: ComplexPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.creal.rat.nat_div_succ, &[numerator, j])
}

/// `CReal.le CReal.zero (mag_bound k)`, via `Rat.zero_le_natDivSucc` lifted by
/// `CReal.ofRat_le` — `CReal.zero` is defeq to `ofRat Rat.zero`. The ℂ-side
/// copy of `creal/uniform_continuity.rs::mag_bound_nonneg`, which is private
/// there; identical body, and it mentions no complex number at all.
fn mag_bound_nonneg(d: &mut IntDev<'_>, p: ComplexPrelude, k: ExprId) -> ExprId {
    let creal = p.creal;
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = d.const_app(creal.rat.nat_div_succ, &[succ_k, zero_idx]);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, creal.rat);
    let rat_nonneg = d.lemma(creal.rat.zero_le_nat_div_succ, &[succ_k, zero_idx]);
    d.lemma(creal.of_rat_le, &[rzero_expr, bound_rat, rat_nonneg])
}

/// `m := 2n + 1` — the two-way accuracy split `Rat.natDivSucc_halve` inverts,
/// shared by both proofs below.
fn split_index(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    let two_n = d.mul(two, n);
    d.succ(two_n)
}

/// From `h : CReal.le (Complex.abs (x − y)) (ofRat (natDivSucc 1 combined))`
/// and `h_le : Nat.le part combined`, derive
/// `CReal.le (Complex.abs (x − y)) (ofRat (natDivSucc 1 part))`.
///
/// `Rat.natDivSucc_antitone` then `CReal.ofRat_le` then `CReal.le_trans`: a
/// bigger denominator is a smaller bound, so a hypothesis stated at the SUM of
/// two moduli implies each summand's own. This is the step the "one of the two
/// moduli ignored" mutant destroys — with a single-summand modulus there is no
/// `Nat.le` for `natDivSucc_antitone` to consume.
fn weaken_modulus(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    abs_diff: ExprId,
    part: ExprId,
    combined: ExprId,
    h_le: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let r_part = div_succ(d, p, 1, part);
    let r_combined = div_succ(d, p, 1, combined);
    let rat_le = d.lemma(creal.rat.nat_div_succ_antitone, &[part, combined, h_le]);
    let ofr_part = d.const_app(creal.of_rat, &[r_part]);
    let ofr_combined = d.const_app(creal.of_rat, &[r_combined]);
    let creal_le = d.lemma(creal.of_rat_le, &[r_combined, r_part, rat_le]);
    d.lemma(
        creal.le_trans,
        &[abs_diff, ofr_combined, ofr_part, h, creal_le],
    )
}

/// The pair `(Nat.le first combined, Nat.le second combined)` for
/// `combined := first + second`. The second needs `Nat.add_comm` to reorient
/// `Nat.le_add_right`'s output, exactly as
/// `creal/uniform_continuity.rs::declare_uniformly_continuous_add` does.
fn le_both_addends(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    first: ExprId,
    second: ExprId,
) -> (ExprId, ExprId) {
    let nat_p = p.creal.rat.int.nat;
    let combined = d.add(first, second);
    let h_first = d.lemma(nat_p.le_add_right, &[first, second]);
    let swapped = d.add(second, first);
    let raw_second = d.lemma(nat_p.le_add_right, &[second, first]);
    let comm_eq = d.lemma(nat_p.add_comm, &[second, first]);
    let h_second = nat_rewrite_prop(d, swapped, combined, comm_eq, raw_second, &|d, t| {
        NatOps::le(d, second, t)
    });
    (h_first, h_second)
}

/// From two bounds of `ofRat (natDivSucc 1 m)` each, with `m := 2n + 1`,
/// derive `CReal.Equiv (add ofr_m ofr_m) (ofRat (natDivSucc 1 n))` —
/// `1/(m+1) + 1/(m+1) = 2/(2n+2) = 1/(n+1)`, by `CReal.ofRat_add`,
/// `Rat.natDivSucc_add` and `Rat.natDivSucc_halve`. The tail both proofs
/// share, and `creal/uniform_continuity.rs`'s verbatim.
fn fuse_two_halves(d: &mut IntDev<'_>, p: ComplexPrelude, n: ExprId, m: ExprId) -> ExprId {
    let creal = p.creal;
    let one_nat = d.num(1);
    let r_half = div_succ(d, p, 1, m);
    let ofr_half = d.const_app(creal.of_rat, &[r_half]);
    let sum_of_halves = radd_c(d, p, ofr_half, ofr_half);

    let of_rat_add_proof = d.lemma(creal.of_rat_add, &[r_half, r_half]);
    let eq1 = d.lemma(creal.rat.nat_div_succ_add, &[one_nat, one_nat, m]);
    let two_m = div_succ(d, p, 2, m);
    let radd_halves = radd(d, r_half, r_half);
    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(creal.of_rat, &[t]);
        d.const_app(creal.equiv, &[sum_of_halves, oft])
    };
    let step_a = rat_eq_rewrite(d, radd_halves, two_m, eq1, of_rat_add_proof, &motive);
    let eq2 = d.lemma(creal.rat.nat_div_succ_halve, &[n]);
    let out_bound_rat = div_succ(d, p, 1, n);
    rat_eq_rewrite(d, two_m, out_bound_rat, eq2, step_a, &motive)
}

// ---------------------------------------------------------------------------
// `add`
// ---------------------------------------------------------------------------

/// `Complex.uniformlyContinuous_add : ∀ F G c r, UniformlyContinuousOn F c r →
/// UniformlyContinuousOn G c r →
/// UniformlyContinuousOn (fun z => add (F z) (G z)) c r`.
///
/// Modulus `n ↦ mF(2n+1) + mG(2n+1)`; each factor's error is `1/(2n+2)` and
/// the triangle inequality ([`ComplexPrelude::abs_add_le`]) sums them.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_add(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let huc_f_ty = uc_ty(d, p, f, c, r);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, c, r);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let sum_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let sum = zadd(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, sum)
    };

    let mf = d.const_app(p.estimates.uc_modulus, &[f, c, r, huc_f]);
    let mg = d.const_app(p.estimates.uc_modulus, &[g, c, r, huc_g]);

    let modulus_add = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = split_index(d, n);
        let mf_m = d.apply(mf, &[m]);
        let mg_m = d.apply(mg, &[m]);
        let sum = d.add(mf_m, mg_m);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
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

        let m = split_index(d, n);
        let mf_m = d.apply(mf, &[m]);
        let mg_m = d.apply(mg, &[m]);
        let combined = d.add(mf_m, mg_m);

        let mod_n = d.apply(modulus_add, &[n]);
        let in_bound = of_div_succ(d, p, 1, mod_n);
        let diff_xy = zsub(d, p, x, y);
        let abs_diff = zabs(d, p, diff_xy);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        // --- weaken the combined-modulus hypothesis to each factor's own ---
        let (h_le_f, h_le_g) = le_both_addends(d, p, mf_m, mg_m);
        let hyp_f = weaken_modulus(d, p, abs_diff, mf_m, combined, h_le_f, h);
        let hyp_g = weaken_modulus(d, p, abs_diff, mg_m, combined, h_le_g, h);

        // --- each factor's own error at accuracy `m` ------------------------
        let spec_f = d.const_app(p.estimates.uc_spec, &[f, c, r, huc_f]);
        let spec_g = d.const_app(p.estimates.uc_spec, &[g, c, r, huc_g]);
        let close_f = d.apply(spec_f, &[m, x, y, hdx, hdy, hyp_f]);
        let close_g = d.apply(spec_g, &[m, x, y, hdx, hdy, hyp_g]);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let error_f = zsub(d, p, fx, fy);
        let error_g = zsub(d, p, gx, gy);
        let abs_error_f = zabs(d, p, error_f);
        let abs_error_g = zabs(d, p, error_g);

        let r_half = div_succ(d, p, 1, m);
        let ofr_half = d.const_app(creal.of_rat, &[r_half]);
        // close_f : le abs_error_f ofr_half ; close_g : le abs_error_g ofr_half

        // --- triangle inequality on the SPLIT difference --------------------
        let sum_errors = zadd(d, p, error_f, error_g);
        let abs_sum_errors = zabs(d, p, sum_errors);
        let triangle = d.lemma(p.abs_add_le, &[error_f, error_g]);
        let sum_of_abs = radd_c(d, p, abs_error_f, abs_error_g);
        let sum_bounds = d.lemma(
            creal.add_le_add,
            &[
                abs_error_f,
                ofr_half,
                abs_error_g,
                ofr_half,
                close_f,
                close_g,
            ],
        );
        let sum_of_halves = radd_c(d, p, ofr_half, ofr_half);
        let combined_le = d.lemma(
            creal.le_trans,
            &[
                abs_sum_errors,
                sum_of_abs,
                sum_of_halves,
                triangle,
                sum_bounds,
            ],
        );

        // --- the algebra, in ONE call ---------------------------------------
        // (F x + G x) − (F y + G y)  ~  (F x − F y) + (G x − G y)
        let sum_x = zadd(d, p, fx, gx);
        let sum_y = zadd(d, p, fy, gy);
        let actual_diff = zsub(d, p, sum_x, sum_y);
        let abs_actual = zabs(d, p, actual_diff);
        let ring = {
            let fx_sym = CExpr::var(d, p, fx);
            let fy_sym = CExpr::var(d, p, fy);
            let gx_sym = CExpr::var(d, p, gx);
            let gy_sym = CExpr::var(d, p, gy);
            let lhs = CExpr::add(
                CExpr::add(fx_sym.clone(), gx_sym.clone()),
                CExpr::neg(CExpr::add(fy_sym.clone(), gy_sym.clone())),
            );
            let rhs = CExpr::add(
                CExpr::add(fx_sym, CExpr::neg(fy_sym)),
                CExpr::add(gx_sym, CExpr::neg(gy_sym)),
            );
            ring_law_proof(d, p, &lhs, &rhs)
        };
        // ring : Complex.Equiv actual_diff sum_errors
        let abs_equiv = d.lemma(p.abs_congr, &[actual_diff, sum_errors, ring]);
        // abs_equiv : CReal.Equiv abs_actual abs_sum_errors

        // --- fuse the two halves down to `1/(n+1)` --------------------------
        let fuse = fuse_two_halves(d, p, n, m);
        let out_bound_rat = div_succ(d, p, 1, n);
        let ofr_out = d.const_app(creal.of_rat, &[out_bound_rat]);
        let abs_equiv_back = d.lemma(creal.equiv_symm, &[abs_actual, abs_sum_errors, abs_equiv]);
        let result = d.lemma(
            creal.le_congr,
            &[
                abs_sum_errors,
                abs_actual,
                sum_of_halves,
                ofr_out,
                abs_equiv_back,
                fuse,
                combined_le,
            ],
        );

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hdy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_hdx = d.lam_fv(hdx_fv, disc_x, with_hdy);
        let with_y = d.lam_fv(y_fv, carrier, with_hdx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.estimates.uc_mk, &[sum_fn, c, r, modulus_add, spec]);
    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, mk_applied);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_r = d.lam_fv(r_fv, real, with_huc_f);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_g = d.lam_fv(g_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, sum_fn, c, r);
        let with_huc_g = d.arrow(huc_g_ty, applied);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_r = d.pi_fv(r_fv, real, with_huc_f);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_g = d.pi_fv(g_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uc_closure.uniformly_continuous_add,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `mul`
// ---------------------------------------------------------------------------

/// `Complex.uniformlyContinuous_mul : ∀ F G c r, UniformlyContinuousOn F c r →
/// UniformlyContinuousOn G c r → ∀ k1 k2, BoundedOn F c r k1 →
/// BoundedOn G c r k2 → UniformlyContinuousOn (fun z => mul (F z) (G z)) c r`.
///
/// See this module's documentation for the estimate and for why `e_g` must be
/// spelled `rescale_index(k1, m)` and not any equal-valued alternative.
///
/// The two `BoundedOn` hypotheses take the raw inline shape
/// ([`super::estimates::bounded_on_ty`]) rather than the named
/// `Complex.BoundedOn` constant, exactly as `Complex.hasDerivative_mul`'s
/// three do: the two are definitionally equal (`Complex.bounded_on_unfold` is
/// the isolated confirmation) and the inline form is directly applicable at a
/// point without an intervening unfold.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_mul(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let huc_f_ty = uc_ty(d, p, f, c, r);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, c, r);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hbf_ty = bounded_on_ty(d, p, f, c, r, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_ty(d, p, g, c, r, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);

    let mul_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let prod = zmul(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, prod)
    };

    let mf = d.const_app(p.estimates.uc_modulus, &[f, c, r, huc_f]);
    let mg = d.const_app(p.estimates.uc_modulus, &[g, c, r, huc_g]);

    let modulus_mul = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = split_index(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let sum = d.add(mg_eg, mf_ef);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
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

        let m = split_index(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let combined = d.add(mg_eg, mf_ef);

        let mod_n = d.apply(modulus_mul, &[n]);
        let in_bound = of_div_succ(d, p, 1, mod_n);
        let diff_xy = zsub(d, p, x, y);
        let abs_diff = zabs(d, p, diff_xy);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        let (h_le_g, h_le_f) = le_both_addends(d, p, mg_eg, mf_ef);
        let hyp_g = weaken_modulus(d, p, abs_diff, mg_eg, combined, h_le_g, h);
        let hyp_f = weaken_modulus(d, p, abs_diff, mf_ef, combined, h_le_f, h);

        let spec_g = d.const_app(p.estimates.uc_spec, &[g, c, r, huc_g]);
        let spec_f = d.const_app(p.estimates.uc_spec, &[f, c, r, huc_f]);
        let close_g = d.apply(spec_g, &[e_g, x, y, hdx, hdy, hyp_g]);
        let close_f = d.apply(spec_f, &[e_f, x, y, hdx, hdy, hyp_f]);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        // `BoundedOn` at the two points it is needed: `|F x|` for term one and
        // `|G y|` for term two.
        let hbf_x = d.apply(hbf, &[x, hdx]);
        let hbg_y = d.apply(hbg, &[y, hdy]);

        // --- term one: `F x · (G x − G y)` --------------------------------
        let diff_g = zsub(d, p, gx, gy);
        let abs_diff_g = zabs(d, p, diff_g);
        let term1 = zmul(d, p, fx, diff_g);
        let abs_term1 = zabs(d, p, term1);
        let (big1, small1, fold1_out, fold1_proof) = fold_index0_first(d, creal, k1, m, e_g);
        let refl_abs_diff_g = d.lemma(creal.le_refl, &[abs_diff_g]);
        let t1_le_prod = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[fx, diff_g, big1, abs_diff_g, hbf_x, refl_abs_diff_g],
        );
        let k1_nonneg = mag_bound_nonneg(d, p, k1);
        let scaled_g = d.lemma(
            creal.mul_le_mul_of_nonneg_left,
            &[big1, abs_diff_g, small1, k1_nonneg, close_g],
        );
        let mul_big1_diffg = rmul(d, p, big1, abs_diff_g);
        let mul_big1_small1 = rmul(d, p, big1, small1);
        let t1_unfused = d.lemma(
            creal.le_trans,
            &[
                abs_term1,
                mul_big1_diffg,
                mul_big1_small1,
                t1_le_prod,
                scaled_g,
            ],
        );
        let refl_abs_term1 = rrefl(d, p, abs_term1);
        let final1 = d.lemma(
            creal.le_congr,
            &[
                abs_term1,
                abs_term1,
                mul_big1_small1,
                fold1_out,
                refl_abs_term1,
                fold1_proof,
                t1_unfused,
            ],
        );
        // final1 : le abs_term1 (ofRat (natDivSucc 1 m))

        // --- term two: `G y · (F x − F y)`, symmetric ----------------------
        let diff_f = zsub(d, p, fx, fy);
        let abs_diff_f = zabs(d, p, diff_f);
        let term2 = zmul(d, p, gy, diff_f);
        let abs_term2 = zabs(d, p, term2);
        let (big2, small2, fold2_out, fold2_proof) = fold_index0_first(d, creal, k2, m, e_f);
        let refl_abs_diff_f = d.lemma(creal.le_refl, &[abs_diff_f]);
        let t2_le_prod = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[gy, diff_f, big2, abs_diff_f, hbg_y, refl_abs_diff_f],
        );
        let k2_nonneg = mag_bound_nonneg(d, p, k2);
        let scaled_f = d.lemma(
            creal.mul_le_mul_of_nonneg_left,
            &[big2, abs_diff_f, small2, k2_nonneg, close_f],
        );
        let mul_big2_difff = rmul(d, p, big2, abs_diff_f);
        let mul_big2_small2 = rmul(d, p, big2, small2);
        let t2_unfused = d.lemma(
            creal.le_trans,
            &[
                abs_term2,
                mul_big2_difff,
                mul_big2_small2,
                t2_le_prod,
                scaled_f,
            ],
        );
        let refl_abs_term2 = rrefl(d, p, abs_term2);
        let final2 = d.lemma(
            creal.le_congr,
            &[
                abs_term2,
                abs_term2,
                mul_big2_small2,
                fold2_out,
                refl_abs_term2,
                fold2_proof,
                t2_unfused,
            ],
        );

        // --- triangle inequality + fuse -------------------------------------
        let sum_terms = zadd(d, p, term1, term2);
        let abs_sum_terms = zabs(d, p, sum_terms);
        let triangle = d.lemma(p.abs_add_le, &[term1, term2]);
        let sum_of_abs = radd_c(d, p, abs_term1, abs_term2);
        let sum_bounds = d.lemma(
            creal.add_le_add,
            &[abs_term1, fold1_out, abs_term2, fold2_out, final1, final2],
        );
        let sum_of_halves = radd_c(d, p, fold1_out, fold2_out);
        let combined_le = d.lemma(
            creal.le_trans,
            &[
                abs_sum_terms,
                sum_of_abs,
                sum_of_halves,
                triangle,
                sum_bounds,
            ],
        );

        // --- the product-difference identity, in ONE call --------------------
        // F(x)G(x) − F(y)G(y)  ~  F(x)(G(x) − G(y)) + G(y)(F(x) − F(y))
        let prod_x = zmul(d, p, fx, gx);
        let prod_y = zmul(d, p, fy, gy);
        let actual_diff = zsub(d, p, prod_x, prod_y);
        let abs_actual = zabs(d, p, actual_diff);
        let ring = {
            let fx_sym = CExpr::var(d, p, fx);
            let fy_sym = CExpr::var(d, p, fy);
            let gx_sym = CExpr::var(d, p, gx);
            let gy_sym = CExpr::var(d, p, gy);
            let lhs = CExpr::add(
                CExpr::mul(fx_sym.clone(), gx_sym.clone()),
                CExpr::neg(CExpr::mul(fy_sym.clone(), gy_sym.clone())),
            );
            let rhs = CExpr::add(
                CExpr::mul(
                    fx_sym.clone(),
                    CExpr::add(gx_sym, CExpr::neg(gy_sym.clone())),
                ),
                CExpr::mul(gy_sym, CExpr::add(fx_sym, CExpr::neg(fy_sym))),
            );
            ring_law_proof(d, p, &lhs, &rhs)
        };
        // ring : Complex.Equiv actual_diff sum_terms
        let abs_equiv = d.lemma(p.abs_congr, &[actual_diff, sum_terms, ring]);
        let abs_equiv_back = d.lemma(creal.equiv_symm, &[abs_actual, abs_sum_terms, abs_equiv]);

        let fuse = fuse_two_halves(d, p, n, m);
        let out_bound_rat = div_succ(d, p, 1, n);
        let ofr_out = d.const_app(creal.of_rat, &[out_bound_rat]);
        let result = d.lemma(
            creal.le_congr,
            &[
                abs_sum_terms,
                abs_actual,
                sum_of_halves,
                ofr_out,
                abs_equiv_back,
                fuse,
                combined_le,
            ],
        );

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hdy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_hdx = d.lam_fv(hdx_fv, disc_x, with_hdy);
        let with_y = d.lam_fv(y_fv, carrier, with_hdx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.estimates.uc_mk, &[mul_fn, c, r, modulus_mul, spec]);
    let value = {
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, mk_applied);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k2 = d.lam_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, with_k1);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_r = d.lam_fv(r_fv, real, with_huc_f);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_g = d.lam_fv(g_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, mul_fn, c, r);
        let with_hbg = d.arrow(hbg_ty, applied);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k2 = d.pi_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.arrow(huc_g_ty, with_k1);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_r = d.pi_fv(r_fv, real, with_huc_f);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_g = d.pi_fv(g_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uc_closure.uniformly_continuous_mul,
        uparams: vec![],
        ty,
        value,
    })
}
