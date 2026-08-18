//! The **structural core**: what makes `Eq Rat` usable.
//!
//! `Rat` is a normalised structure, so two rationals are equal exactly when
//! their projections are — but the projections are only reachable through
//! `Rat.rec`, and the two proof fields are dependently typed. Everything in
//! this module exists to turn that into three usable facts:
//!
//! - [`declare_structural`] — `mk_congr`, `eta`, `ext`. Equal numerator and
//!   equal denominator give equal rationals, *whatever* the proof fields hold,
//!   because the kernel has definitional **proof irrelevance**.
//! - [`declare_uniqueness`] — `eq_of_cross`: a reduced representative is
//!   unique, so cross-multiplication decides equality. This is the keystone,
//!   and the only genuinely number-theoretic step: it needs Gauss's lemma over
//!   `ℕ` (coprime cancellation, from Bézout) and cancellation over `ℤ`.
//! - [`declare_normalize_laws`] — `normalize` preserves the value it is given
//!   (`normalize_cross`) and therefore respects cross-equality
//!   (`normalize_congr`) and is the identity on an already-reduced pair
//!   (`self_normalize`).
//!
//! With those, a ring law over `ℚ` becomes a cross-multiplication identity over
//! the constructed `ℤ`, which is ordinary algebra.

use super::RatPrelude;
use super::ops::{
    bezout_elim, den, den_z, mk, normalize, num, positive_ty, rat_eq_rewrite, rat_theorem, rat_ty,
    rchain, reduced_ty, req, req_motive, rrefl, rsymm, rtrans, rtransport,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, Shape, case_split};
use crate::nat_prelude::NatOps;

/// Admit `Rat.mk_congr`, `Rat.eta` and `Rat.ext`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_structural(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    // --- mk_congr ----------------------------------------------------------
    // ∀ n1 n2 d1 d2, n1 = n2 → d1 = d2 →
    //   ∀ p1 r1 p2 r2, mk n1 d1 p1 r1 = mk n2 d2 p2 r2
    //
    // The two proof fields are never inspected: at `n1 = n1`, `d1 = d1` the two
    // sides differ only in them, and definitional proof irrelevance makes
    // `Eq.refl` check against the stated type.
    {
        let n1_fv = d.fresh_fvar();
        let n1 = d.kernel().fvar(n1_fv);
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        let d1_fv = d.fresh_fvar();
        let d1 = d.kernel().fvar(d1_fv);
        let d2_fv = d.fresh_fvar();
        let d2 = d.kernel().fvar(d2_fv);
        let hn_ty = d.ieq(n1, n2);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hd_ty = d.eq(d1, d2);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);
        let p1_ty = positive_ty(d, d1);
        let p1_fv = d.fresh_fvar();
        let p1 = d.kernel().fvar(p1_fv);
        let r1_ty = reduced_ty(d, n1, d1);
        let r1_fv = d.fresh_fvar();
        let r1 = d.kernel().fvar(r1_fv);
        let source = mk(d, n1, d1, p1, r1);

        // `∀ p2 r2, source = mk numerator denominator p2 r2`, the shape both
        // transports move through.
        let goal = |d: &mut IntDev<'_>, numerator: ExprId, denominator: ExprId| -> ExprId {
            let p2_ty = positive_ty(d, denominator);
            let p2_fv = d.fresh_fvar();
            let p2 = d.kernel().fvar(p2_fv);
            let r2_ty = reduced_ty(d, numerator, denominator);
            let r2_fv = d.fresh_fvar();
            let r2 = d.kernel().fvar(r2_fv);
            let target = mk(d, numerator, denominator, p2, r2);
            let equation = req(d, source, target);
            let with_r2 = d.pi_fv(r2_fv, r2_ty, equation);
            d.pi_fv(p2_fv, p2_ty, with_r2)
        };

        // Base: numerator `n1`, denominator `d1` — reflexivity, up to proof
        // irrelevance in `p2`/`r2`.
        let base = {
            let p2_ty = positive_ty(d, d1);
            let p2_fv = d.fresh_fvar();
            let r2_ty = reduced_ty(d, n1, d1);
            let r2_fv = d.fresh_fvar();
            let body = rrefl(d, source);
            let with_r2 = d.lam_fv(r2_fv, r2_ty, body);
            d.lam_fv(p2_fv, p2_ty, with_r2)
        };
        // Move the numerator n1 ↦ n2 at fixed denominator d1.
        let at_n2 = {
            let motive = d.ieq_motive(n1, &|d, y| goal(d, y, d1));
            d.itransport(n1, motive, base, n2, hn)
        };
        // Then the denominator d1 ↦ d2.
        let body = {
            let motive = d.eq_motive(d1, &|d, x| goal(d, n2, x));
            d.transport(d1, motive, at_n2, d2, hd)
        };

        let ty = {
            let inner = goal(d, n2, d2);
            let with_r1 = d.pi_fv(r1_fv, r1_ty, inner);
            let with_p1 = d.pi_fv(p1_fv, p1_ty, with_r1);
            let with_hd = d.pi_fv(hd_fv, hd_ty, with_p1);
            let with_hn = d.pi_fv(hn_fv, hn_ty, with_hd);
            let with_d2 = d.pi_fv(d2_fv, nat_ty, with_hn);
            let with_d1 = d.pi_fv(d1_fv, nat_ty, with_d2);
            let with_n2 = d.pi_fv(n2_fv, int_ty, with_d1);
            d.pi_fv(n1_fv, int_ty, with_n2)
        };
        let value = {
            let with_r1 = d.lam_fv(r1_fv, r1_ty, body);
            let with_p1 = d.lam_fv(p1_fv, p1_ty, with_r1);
            let with_hd = d.lam_fv(hd_fv, hd_ty, with_p1);
            let with_hn = d.lam_fv(hn_fv, hn_ty, with_hd);
            let with_d2 = d.lam_fv(d2_fv, nat_ty, with_hn);
            let with_d1 = d.lam_fv(d1_fv, nat_ty, with_d2);
            let with_n2 = d.lam_fv(n2_fv, int_ty, with_d1);
            d.lam_fv(n1_fv, int_ty, with_n2)
        };
        d.declare_theorem(p.mk_congr, ty, value)?;
    }

    // --- eta ---------------------------------------------------------------
    // ∀ q, q = mk (num q) (den q) (den_pos q) (reduced q).
    // By `Rat.rec`: on `mk n dn pp rr` the right-hand side ι-reduces to itself.
    rat_theorem(d, p.eta, 1, &|d, v| {
        let q = v[0];
        let claim = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let rebuilt = {
                let numerator = num(d, x);
                let denominator = den(d, x);
                let positive = super::ops::den_pos(d, x);
                let reduced = super::ops::reduced(d, x);
                mk(d, numerator, denominator, positive, reduced)
            };
            req(d, x, rebuilt)
        };
        let stmt = claim(d, q);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = claim(d, x);
            d.lam_fv(x_fv, carrier, body)
        };
        let minor = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let dn_fv = d.fresh_fvar();
            let dn = d.kernel().fvar(dn_fv);
            let pp_ty = positive_ty(d, dn);
            let pp_fv = d.fresh_fvar();
            let pp = d.kernel().fvar(pp_fv);
            let rr_ty = reduced_ty(d, n, dn);
            let rr_fv = d.fresh_fvar();
            let rr = d.kernel().fvar(rr_fv);
            let built = mk(d, n, dn, pp, rr);
            let body = rrefl(d, built);
            let with_rr = d.lam_fv(rr_fv, rr_ty, body);
            let with_pp = d.lam_fv(pp_fv, pp_ty, with_rr);
            let with_dn = d.lam_fv(dn_fv, nat_ty, with_pp);
            d.lam_fv(n_fv, int_ty, with_dn)
        };
        let level_zero = d.kernel().level_zero();
        let rec = d.kernel().const_(p.int.rat_rec, vec![level_zero]);
        let proof = d.apply(rec, &[motive, minor, q]);
        (stmt, proof)
    })?;

    // --- ext ---------------------------------------------------------------
    // ∀ q r, num q = num r → den q = den r → q = r.
    rat_theorem(d, p.ext, 2, &|d, v| {
        let (q, r) = (v[0], v[1]);
        let hn_ty = {
            let left = num(d, q);
            let right = num(d, r);
            d.ieq(left, right)
        };
        let hd_ty = {
            let left = den(d, q);
            let right = den(d, r);
            d.eq(left, right)
        };
        let conclusion = req(d, q, r);
        let stmt = {
            let inner = d.arrow(hd_ty, conclusion);
            d.arrow(hn_ty, inner)
        };
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let expand = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let numerator = num(d, x);
            let denominator = den(d, x);
            let positive = super::ops::den_pos(d, x);
            let reduced = super::ops::reduced(d, x);
            mk(d, numerator, denominator, positive, reduced)
        };
        let left_expanded = expand(d, q);
        let right_expanded = expand(d, r);
        let step_left = d.const_app(p.eta, &[q]);
        let step_middle = {
            let nq = num(d, q);
            let nr = num(d, r);
            let dq = den(d, q);
            let dr = den(d, r);
            let pq = super::ops::den_pos(d, q);
            let rq = super::ops::reduced(d, q);
            let pr = super::ops::den_pos(d, r);
            let rr = super::ops::reduced(d, r);
            d.const_app(p.mk_congr, &[nq, nr, dq, dr, hn, hd, pq, rq, pr, rr])
        };
        let step_right = {
            let forward = d.const_app(p.eta, &[r]);
            rsymm(d, r, right_expanded, forward)
        };
        let (_, chained) = rchain(
            d,
            q,
            &[
                (left_expanded, step_left),
                (right_expanded, step_middle),
                (r, step_right),
            ],
        );
        let proof = {
            let with_hd = d.lam_fv(hd_fv, hd_ty, chained);
            d.lam_fv(hn_fv, hn_ty, with_hd)
        };
        (stmt, proof)
    })
}

/// Placeholder for the arithmetic support lemmas (Gauss, cancellation).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_arithmetic_support(
    _d: &mut IntDev<'_>,
    _p: RatPrelude,
) -> Result<(), KernelError> {
    Ok(())
}

/// Placeholder for `eq_of_cross`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniqueness(_d: &mut IntDev<'_>, _p: RatPrelude) -> Result<(), KernelError> {
    Ok(())
}

/// Placeholder for the `normalize` laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_normalize_laws(
    _d: &mut IntDev<'_>,
    _p: RatPrelude,
) -> Result<(), KernelError> {
    Ok(())
}
