//! **Transport and the power rule on ℂ** — `Complex.hasDerivative_congr` and
//! `Complex.hasDerivative_pow`, the two steps between the product rule and a
//! derivative for a polynomial.
//!
//! # Why transport is needed at all, and why it is not `Eq`
//!
//! A constructive derivative is **not unique as a function**, only up to
//! pointwise `Complex.Equiv` on the disc. Two developments producing "the
//! same" derivative in different syntactic forms therefore cannot be connected
//! without a transport lemma, and `Eq Complex` is not the equality of complex
//! numbers here (`complex.rs`'s module doc). So
//! [`PolyDerivNames::has_derivative_congr`] moves a `HasDerivativeOn` along
//! two pointwise `Complex.Equiv` agreements, and it demands them **only on the
//! disc** — `HasDerivativeOn.spec`'s conclusion mentions `F x`, `F y`, `F' x`
//! solely inside a body reached through `InDisc c r x → InDisc c r y → …`, the
//! same memberships a caller must already hold to reach that body. Agreement
//! off the disc is neither needed nor assumed. The modulus is reused
//! **verbatim**: this is a relabelling, not an estimate.
//!
//! # The power rule states its exponent as `succ n`, and must
//!
//! `Complex.pow`'s own recursion is `pow z (Nat.succ j) ≡ mul (pow z j) z` —
//! the fresh factor on the RIGHT. Stating the power rule at exponent `n`
//! directly forces `pow x (n − 1)` in the derivative, and `Nat.sub` is
//! truncated. At `succ n` (derivative `(n+1)·pow x n`) no subtraction appears
//! anywhere: the base case is exponent `1`, the step goes `succ j → succ (succ
//! j)`, and every lower exponent in the derivative is the induction variable
//! itself.
//!
//! # Why the induction commutes the product first
//!
//! `Complex.hasDerivative_mul` needs `UniformlyContinuousOn` on its **first**
//! factor only. `pow`'s defining equation would put the already-built
//! `pow (·, j)` in that slot — precisely the function whose own continuity
//! this induction cannot supply at an arbitrary `j`. So the step instead
//! builds `HasDerivativeOn (fun z => mul z (pow z (succ j))) …` with `F := id`
//! (continuity from `Complex.uniformlyContinuous_id`, available at every step)
//! and `G := pow (·, succ j)`, then transports across `Complex.mul_comm`.
//!
//! Landing [`super::uc_closure`] does **not** remove this: closure of
//! continuity under products answers a different question (continuity of a
//! product given continuity of its factors), and the missing fact here is
//! continuity of `pow (·, j)` itself.
//!
//! # Boundedness is a hypothesis, not a derived fact
//!
//! `hasDerivative_mul` needs three `Nat` magnitude bounds at *every* step.
//! Deriving `BoundedOn (pow · n) c r _` for every `n` from scratch is separate
//! Nat-indexed machinery, so this theorem takes two Skolem functions
//! `kb`, `kd : Nat → Nat` and proofs that they work for **every** `n` — the
//! shape `CReal.hasDerivative_pow` already uses, and the reason the statement
//! is long.
//!
//! # What ℂ buys over the real shelf
//!
//! `creal/derivative.rs`'s step case spends roughly sixty lines of
//! `mul_comm`/`mul_assoc`/`right_distrib`/`add_comm`/`of_nat_succ` to show the
//! built derivative equals the stated one. Here it is one
//! [`super::ring_law_proof`] call, because `Complex.ofNat_succ` and
//! `Complex.pow_succ` both close by `Eq.refl` — `ofNat (succ (succ j))` IS
//! `add (ofNat (succ j)) one` and `pow x (succ j)` IS `mul (pow x j) x` to the
//! kernel, so the whole obligation is a polynomial identity in the three
//! opaque atoms `ofNat (succ j)`, `pow x j` and `x`.
//!
//! ADR-1656 records this file.

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

use super::deriv::{abs_le_of_equiv, fn_ty, hd_ty, in_disc_ty, zadd, zmul, zsub};
use super::estimates::bounded_on_ty;
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The names [`declare_polyderiv`] declares, owned by this module rather than
/// by [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs`/`estimates.rs`
/// arrangement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyDerivNames {
    /// `Complex.hasDerivative_congr : ∀ F F' c r, HasDerivativeOn F F' c r →
    /// ∀ G G', (∀ z, InDisc c r z → Equiv (G z) (F z)) →
    /// (∀ z, InDisc c r z → Equiv (G' z) (F' z)) → HasDerivativeOn G G' c r`.
    pub has_derivative_congr: NameId,
    /// `Complex.hasDerivative_pow` — the power rule at exponent `Nat.succ n`,
    /// gated on Skolem magnitude bounds for `pow (·, n)` and its derivative.
    pub has_derivative_pow: NameId,
}

/// Interns this module's names under `complex`. Called once from
/// `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> PolyDerivNames {
    PolyDerivNames {
        has_derivative_congr: kernel.name_str(complex, "hasDerivative_congr"),
        has_derivative_pow: kernel.name_str(complex, "hasDerivative_pow"),
    }
}

/// Declare transport and the power rule.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_polyderiv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_has_derivative_congr(d, p)?;
    declare_has_derivative_pow(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

/// `∀ z, InDisc c r z → Complex.Equiv (lhs z) (rhs z)` — agreement of two
/// functions **on the disc only**, the hypothesis shape
/// [`declare_has_derivative_congr`] takes and the ℂ analogue of
/// `creal/derivative.rs::agree_on_interval_ty` with the two interval
/// hypotheses collapsed to one membership.
pub(super) fn agree_on_disc_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    r: ExprId,
    lhs_fn: ExprId,
    rhs_fn: ExprId,
) -> ExprId {
    let carrier = complex_ty(d, p);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let disc = in_disc_ty(d, p, c, r, z);
    let lz = d.apply(lhs_fn, &[z]);
    let rz = d.apply(rhs_fn, &[z]);
    let eq = d.const_app(p.equiv, &[lz, rz]);
    let with_disc = d.arrow(disc, eq);
    d.pi_fv(z_fv, carrier, with_disc)
}

/// `fun z => Complex.pow z (Nat.succ v)`.
fn pow_succ_fn(d: &mut IntDev<'_>, p: ComplexPrelude, carrier: ExprId, v: ExprId) -> ExprId {
    let succ_v = d.succ(v);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let pz = d.const_app(p.pow, &[z, succ_v]);
    d.lam_fv(z_fv, carrier, pz)
}

/// `fun x => Complex.mul (Complex.ofNat (Nat.succ v)) (Complex.pow x v)` — the
/// claimed derivative of [`pow_succ_fn`] at `v`.
fn pow_deriv_fn(d: &mut IntDev<'_>, p: ComplexPrelude, carrier: ExprId, v: ExprId) -> ExprId {
    let succ_v = d.succ(v);
    let coeff = d.const_app(p.of_nat, &[succ_v]);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let px = d.const_app(p.pow, &[x, v]);
    let body = zmul(d, p, coeff, px);
    d.lam_fv(x_fv, carrier, body)
}

// ---------------------------------------------------------------------------
// transport
// ---------------------------------------------------------------------------

/// `Complex.hasDerivative_congr` — move a derivative along pointwise
/// `Complex.Equiv` agreement **on the disc**.
///
/// See this module's documentation for why the hypotheses are disc-local and
/// why the modulus is reused verbatim.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_has_derivative_congr(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hf_ty = hd_ty(d, p, f, fp, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);

    let agree_g_ty = agree_on_disc_ty(d, p, c, r, g, f);
    let agree_gp_ty = agree_on_disc_ty(d, p, c, r, gp, fp);
    let agree_g_fv = d.fresh_fvar();
    let agree_g = d.kernel().fvar(agree_g_fv);
    let agree_gp_fv = d.fresh_fvar();
    let agree_gp = d.kernel().fvar(agree_gp_fv);

    // Reuse `F`'s own modulus verbatim — a relabelling, not an estimate.
    let modulus = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);

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
        let abs_diff = d.const_app(p.abs, &[diff_yx]);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = super::deriv::of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term_f = zmul(d, p, fpx, diff_yx);
        let fy_fx = zsub(d, p, fy, fx);
        let error_f = zsub(d, p, fy_fx, deriv_term_f);

        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let gpx = d.apply(gp, &[x]);
        let deriv_term_g = zmul(d, p, gpx, diff_yx);
        let gy_gx = zsub(d, p, gy, gx);
        let error_g = zsub(d, p, gy_gx, deriv_term_g);

        let ofr_out = super::deriv::of_div_succ(d, p, 1, e);
        let out_bound = d.const_app(creal.mul, &[ofr_out, abs_diff]);

        // The two agreements, instantiated at `y` and at `x` with their own
        // disc memberships — the SAME memberships `spec` already demands.
        let gy_eq_fy = d.apply(agree_g, &[y, hdy]);
        let gx_eq_fx = d.apply(agree_g, &[x, hdx]);
        let gpx_eq_fpx = d.apply(agree_gp, &[x, hdx]);

        let neg_gx = d.const_app(p.neg, &[gx]);
        let neg_fx = d.const_app(p.neg, &[fx]);
        let neg_gx_eq = d.lemma(p.neg_congr, &[gx, fx, gx_eq_fx]);
        let gy_gx_eq = d.lemma(p.add_congr, &[gy, fy, neg_gx, neg_fx, gy_eq_fy, neg_gx_eq]);

        let refl_diff = d.lemma(p.equiv_refl, &[diff_yx]);
        let deriv_term_eq = d.lemma(
            p.mul_congr,
            &[gpx, fpx, diff_yx, diff_yx, gpx_eq_fpx, refl_diff],
        );
        let neg_deriv_g = d.const_app(p.neg, &[deriv_term_g]);
        let neg_deriv_f = d.const_app(p.neg, &[deriv_term_f]);
        let neg_deriv_eq = d.lemma(p.neg_congr, &[deriv_term_g, deriv_term_f, deriv_term_eq]);

        let error_eq = d.lemma(
            p.add_congr,
            &[
                gy_gx,
                fy_fx,
                neg_deriv_g,
                neg_deriv_f,
                gy_gx_eq,
                neg_deriv_eq,
            ],
        );

        let error_f_bound = d.lemma(p.deriv.hd_spec, &[f, fp, c, r, hf, e, x, y, hdx, hdy, h]);
        let conclusion =
            abs_le_of_equiv(d, p, error_g, error_f, out_bound, error_eq, error_f_bound);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hdy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_hdx = d.lam_fv(hdx_fv, disc_x, with_hdy);
        let with_y = d.lam_fv(y_fv, carrier, with_hdx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[g, gp, c, r, modulus, spec]);
    let value = {
        let with_agree_gp = d.lam_fv(agree_gp_fv, agree_gp_ty, mk_applied);
        let with_agree_g = d.lam_fv(agree_g_fv, agree_g_ty, with_agree_gp);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_agree_g);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_g);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, g, gp, c, r);
        let with_agree_gp = d.arrow(agree_gp_ty, applied);
        let with_agree_g = d.arrow(agree_g_ty, with_agree_gp);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_agree_g);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_hf = d.arrow(hf_ty, with_g);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polyderiv.has_derivative_congr,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// the power rule
// ---------------------------------------------------------------------------

/// `Complex.hasDerivative_pow : ∀ c r k1, BoundedOn (fun z => z) c r k1 →
/// ∀ (kb kd : Nat → Nat),
///   (∀ n, BoundedOn (fun z => pow z n) c r (kb n)) →
///   (∀ n, BoundedOn (fun x => mul (ofNat (Nat.succ n)) (pow x n)) c r (kd n)) →
///   ∀ n, HasDerivativeOn (fun z => pow z (Nat.succ n))
///          (fun x => mul (ofNat (Nat.succ n)) (pow x n)) c r`.
///
/// See this module's documentation for the exponent convention, the commuting
/// step, and why the two magnitude Skolems are hypotheses.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_has_derivative_pow(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let nat = d.nat_ty();
    let one_level = d.level_one();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);

    let id_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        d.lam_fv(z_fv, carrier, z)
    };
    let one_z = d.kernel().const_(p.one, vec![]);
    let const_one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_z)
    };

    let hb_id_ty = bounded_on_ty(d, p, id_fn, c, r, k1);
    let hb_id_fv = d.fresh_fvar();
    let hb_id = d.kernel().fvar(hb_id_fv);

    let nat_to_nat = d.arrow(nat, nat);
    let kb_fv = d.fresh_fvar();
    let kb = d.kernel().fvar(kb_fv);
    let kd_fv = d.fresh_fvar();
    let kd = d.kernel().fvar(kd_fv);

    let hb_body_ty = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let pz = d.const_app(p.pow, &[z, v]);
        let pf = d.lam_fv(z_fv, carrier, pz);
        let kbv = d.apply(kb, &[v]);
        let bt = bounded_on_ty(d, p, pf, c, r, kbv);
        d.pi_fv(v_fv, nat, bt)
    };
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let hd_body_ty = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let df = pow_deriv_fn(d, p, carrier, v);
        let kdv = d.apply(kd, &[v]);
        let bt = bounded_on_ty(d, p, df, c, r, kdv);
        d.pi_fv(v_fv, nat, bt)
    };
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    // motive(v) := HasDerivativeOn (pow_succ_fn v) (pow_deriv_fn v) c r.
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let pf = pow_succ_fn(d, p, carrier, v);
        let df = pow_deriv_fn(d, p, carrier, v);
        hd_ty(d, p, pf, df, c, r)
    };

    // --- base case: v = 0, i.e. exponent 1 ------------------------------
    let base = {
        let zero_v = d.zero();
        let hf = d.const_app(p.deriv.has_derivative_id, &[c, r]);

        // `pow x 1` ≡ `mul (pow x 0) x` ≡ `mul one x`, and the claimed
        // derivative `mul (ofNat 1) (pow x 0)` ≡ `mul (add zero one) one`.
        // Both obligations are closed ring identities; the atoms are `x`
        // alone and nothing at all.
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hdx_fv = d.fresh_fvar();
        let disc_x = in_disc_ty(d, p, c, r, x);
        let agree_g_body = {
            let x_sym = CExpr::var(d, p, x);
            let lhs = CExpr::mul(CExpr::One, x_sym.clone());
            ring_law_proof(d, p, &lhs, &x_sym)
        };
        let agree_g = {
            let with_hdx = d.lam_fv(hdx_fv, disc_x, agree_g_body);
            d.lam_fv(x_fv, carrier, with_hdx)
        };

        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let hdx2_fv = d.fresh_fvar();
        let disc_x2 = in_disc_ty(d, p, c, r, x2);
        let agree_gp_body = {
            let lhs = CExpr::mul(CExpr::add(CExpr::Zero, CExpr::One), CExpr::One);
            ring_law_proof(d, p, &lhs, &CExpr::One)
        };
        let agree_gp = {
            let with_hdx = d.lam_fv(hdx2_fv, disc_x2, agree_gp_body);
            d.lam_fv(x2_fv, carrier, with_hdx)
        };

        let pow_1_fn = pow_succ_fn(d, p, carrier, zero_v);
        let deriv_0_fn = pow_deriv_fn(d, p, carrier, zero_v);

        d.const_app(
            p.polyderiv.has_derivative_congr,
            &[
                id_fn,
                const_one_fn,
                c,
                r,
                hf,
                pow_1_fn,
                deriv_0_fn,
                agree_g,
                agree_gp,
            ],
        )
    };

    // --- step case: j -> succ j ----------------------------------------
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let succ_j = d.succ(j);
        let g_fn = pow_succ_fn(d, p, carrier, j); // fun z => pow z (succ j)
        let gp_fn = pow_deriv_fn(d, p, carrier, j); // fun x => mul (ofNat (succ j)) (pow x j)

        let hf = d.const_app(p.deriv.has_derivative_id, &[c, r]);
        let huc = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
        let k2 = d.apply(kb, &[succ_j]);
        let k3 = d.apply(kd, &[j]);
        let hbg = d.apply(hb, &[succ_j]);
        let hbgp = d.apply(hd, &[j]);

        let mk_applied = d.const_app(
            p.leibniz.has_derivative_mul,
            &[
                id_fn,
                const_one_fn,
                g_fn,
                gp_fn,
                c,
                r,
                hf,
                ih,
                huc,
                k1,
                k2,
                k3,
                hb_id,
                hbg,
                hbgp,
            ],
        );
        // `mk_applied` proves, up to beta:
        //   HasDerivativeOn (fun z => mul z (pow z (succ j)))
        //     (fun x => add (mul one (pow x (succ j))) (mul x (gp_fn x))) c r.

        // agree_g: `pow x (succ (succ j))` ≡ `mul (pow x (succ j)) x`, and the
        // built subject is `mul x (pow x (succ j))`. With `A := pow x (succ
        // j)` opaque, that is `mul A x ~ mul x A` — `Complex.mul_comm`.
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hdx_fv = d.fresh_fvar();
        let disc_x = in_disc_ty(d, p, c, r, x);
        let pow_x_succ_j = d.const_app(p.pow, &[x, succ_j]);
        let agree_g_body = d.lemma(p.mul_comm, &[pow_x_succ_j, x]);
        let agree_g = {
            let with_hdx = d.lam_fv(hdx_fv, disc_x, agree_g_body);
            d.lam_fv(x_fv, carrier, with_hdx)
        };

        // agree_gp: the stated derivative at `succ j` is
        //   `mul (ofNat (succ (succ j))) (pow x (succ j))`
        // ≡ `mul (add C one) (mul P x)`   (ofNat_succ and pow_succ are Eq.refl)
        // and the built one is
        //   `add (mul one (mul P x)) (mul x (mul C P))`,
        // with `C := ofNat (succ j)` and `P := pow x j` opaque atoms. That is
        // the polynomial identity `(C+1)·P·x = 1·(P·x) + x·(C·P)` — ONE call.
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let hdx2_fv = d.fresh_fvar();
        let disc_x2 = in_disc_ty(d, p, c, r, x2);
        let agree_gp_body = {
            let coeff = d.const_app(p.of_nat, &[succ_j]);
            let pow_x2_j = d.const_app(p.pow, &[x2, j]);
            let c_sym = CExpr::var(d, p, coeff);
            let pp_sym = CExpr::var(d, p, pow_x2_j);
            let x_sym = CExpr::var(d, p, x2);
            let a_sym = CExpr::mul(pp_sym.clone(), x_sym.clone()); // pow x (succ j)
            let lhs = CExpr::mul(CExpr::add(c_sym.clone(), CExpr::One), a_sym.clone());
            let rhs = CExpr::add(
                CExpr::mul(CExpr::One, a_sym),
                CExpr::mul(x_sym, CExpr::mul(c_sym, pp_sym)),
            );
            ring_law_proof(d, p, &lhs, &rhs)
        };
        let agree_gp = {
            let with_hdx = d.lam_fv(hdx2_fv, disc_x2, agree_gp_body);
            d.lam_fv(x2_fv, carrier, with_hdx)
        };

        let subject_fn = {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let pz = d.const_app(p.pow, &[z, succ_j]);
            let mzp = zmul(d, p, z, pz);
            d.lam_fv(z_fv, carrier, mzp)
        };
        let deriv_of_subject_fn = {
            let x3_fv = d.fresh_fvar();
            let x3 = d.kernel().fvar(x3_fv);
            let pow_x3_succ_j = d.const_app(p.pow, &[x3, succ_j]);
            let mul_one_a = zmul(d, p, one_z, pow_x3_succ_j);
            let coeff3 = d.const_app(p.of_nat, &[succ_j]);
            let pow_x3_j = d.const_app(p.pow, &[x3, j]);
            let mul_c_p = zmul(d, p, coeff3, pow_x3_j);
            let mul_x_cp = zmul(d, p, x3, mul_c_p);
            let sum = zadd(d, p, mul_one_a, mul_x_cp);
            d.lam_fv(x3_fv, carrier, sum)
        };

        let pow_succ_succ_fn = pow_succ_fn(d, p, carrier, succ_j);
        let deriv_succ_fn = pow_deriv_fn(d, p, carrier, succ_j);

        d.const_app(
            p.polyderiv.has_derivative_congr,
            &[
                subject_fn,
                deriv_of_subject_fn,
                c,
                r,
                mk_applied,
                pow_succ_succ_fn,
                deriv_succ_fn,
                agree_g,
                agree_gp,
            ],
        )
    };

    let motive_lam = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let body = motive(d, v);
        d.lam_fv(v_fv, nat, body)
    };
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let ih_ty = motive(d, j);
        let body = step(d, j, ih);
        let inner = d.lam_fv(ih_fv, ih_ty, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof_body = d.apply(rec, &[motive_lam, base, minor_succ, n]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof_body);
        let with_hd = d.lam_fv(hd_fv, hd_body_ty, with_n);
        let with_hb = d.lam_fv(hb_fv, hb_body_ty, with_hd);
        let with_kd = d.lam_fv(kd_fv, nat_to_nat, with_hb);
        let with_kb = d.lam_fv(kb_fv, nat_to_nat, with_kd);
        let with_hbid = d.lam_fv(hb_id_fv, hb_id_ty, with_kb);
        let with_k1 = d.lam_fv(k1_fv, nat, with_hbid);
        let with_r = d.lam_fv(r_fv, real, with_k1);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let target = motive(d, n);
        let with_n = d.pi_fv(n_fv, nat, target);
        let with_hd = d.arrow(hd_body_ty, with_n);
        let with_hb = d.arrow(hb_body_ty, with_hd);
        let with_kd = d.pi_fv(kd_fv, nat_to_nat, with_hb);
        let with_kb = d.pi_fv(kb_fv, nat_to_nat, with_kd);
        let with_hbid = d.arrow(hb_id_ty, with_kb);
        let with_k1 = d.pi_fv(k1_fv, nat, with_hbid);
        let with_r = d.pi_fv(r_fv, real, with_k1);
        d.pi_fv(c_fv, carrier, with_r)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polyderiv.has_derivative_pow,
        uparams: vec![],
        ty,
        value,
    })
}
