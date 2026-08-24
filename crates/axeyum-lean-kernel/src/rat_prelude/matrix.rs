//! **Linear algebra over ℚ, 2×2** — the first matrix content in this kernel.
//!
//! No `Matrix` inductive, no `List`, no `Fin`: the kernel has none of those in
//! any prelude, and a 2×2 matrix is exactly four `Rat` entries, passed as four
//! explicit arguments. [`Rat.det2`](super::RatPrelude::det2) is the one new
//! *definition* — `det2 a b c d := a·d − b·c` — and everything else is a
//! theorem about it.
//!
//! ## Why `det2_mul` decomposes instead of expanding
//!
//! The naive route is to FOIL both sides of `det2 (ae+bg) (af+bh) (ce+dg)
//! (cf+dh) = det2 a b c d · det2 e f g h` into eight monomials each and match
//! them pairwise. That is what the identity *is*, but building it that way
//! needs an ℤ-style "product as a factor multiset" reorderer for `Rat.mul` — a
//! second copy of `ops::iprod_perm`, just for this one proof.
//!
//! Instead this file proves `det2` is **linear in each row** —
//! [`lin_row1`]/[`lin_row2`] below, each a four-term identity, no factor
//! reordering beyond a single "swap the outer factor with the inner-left one"
//! step ([`middle_swap`]) — and gets multiplicativity from linearity plus
//! [`det2_repeat`] (a repeated row is zero) and `det2_swap_rows` (already
//! required as one of the four basic laws). That is the textbook proof of
//! Cauchy's determinant-product formula for `n = 2`, and it keeps every
//! intermediate identity to four terms instead of eight.
//!
//! ## The defeq this all leans on
//!
//! `Rat.det2 x y z w` is declared as a plain `Definition` (`Rat.sub (Rat.mul x
//! w) (Rat.mul y z)`), exactly the way `Rat.sub`/`Rat.div` are in
//! [`super::defs`]. So a proof built entirely in the *unfolded* `add`/`neg`/
//! `mul` form type-checks against a **stated** goal that mentions `Rat.det2`
//! — the kernel's conversion unfolds the `Definition` (repeatedly, through
//! `Rat.sub`'s own unfolding to `add _ (neg _)`) the same way
//! [`super::group::declare_subtraction`]'s `sub_self` proof (an `add_neg`
//! proof, accepted for a `sub a a = 0` goal) already relies on. Every helper
//! below builds the unfolded form and lets that defeq bridge it back to
//! `Rat.det2`/`Rat.sub` in the declared statement, so `Rat.det2` never needs
//! an equation lemma of its own.

use super::RatPrelude;
use super::group::rsub;
use super::ops::{
    radd, rat_theorem, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rsymm, rtrans, rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.det2`: above every `Rat` definition it unfolds
/// through (`Rat.sub`, `Rat.mul`), matching the "outranks everything it
/// unfolds to" convention [`super::defs`] sets for `Rat.zero`/`Rat.one`.
const DET2_HEIGHT: u16 = 40;

/// Admit `Rat.det2`, its four basic laws, and multiplicativity.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det2_def(d, p)?;
    declare_det2_swap_rows(d, p)?;
    declare_det2_id(d, p)?;
    declare_det2_scale_row(d, p)?;
    declare_det2_row_add(d, p)?;
    declare_det2_mul(d, p)?;
    declare_adjugate(d, p)
}

/// `Rat.det2 a b c d := Rat.sub (Rat.mul a d) (Rat.mul b c)`.
fn declare_det2_def(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);

    let ad = rmul(d, a, dd);
    let bc = rmul(d, b, c);
    let body = rsub(d, p, ad, bc);

    let value = {
        let with_d = d.lam_fv(dd_fv, carrier, body);
        let with_c = d.lam_fv(c_fv, carrier, with_d);
        let with_b = d.lam_fv(b_fv, carrier, with_c);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let inner3 = d.arrow(carrier, carrier);
        let inner2 = d.arrow(carrier, inner3);
        let inner1 = d.arrow(carrier, inner2);
        d.arrow(carrier, inner1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.det2,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DET2_HEIGHT),
    })
}

/// `Rat.det2 x y z w` — the folded application, for building statements.
fn rdet2(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId, z: ExprId, w: ExprId) -> ExprId {
    let _ = p;
    d.const_app(p.det2, &[x, y, z, w])
}

/// `x - y`, unfolded to `add x (neg y)` — defeq to `Rat.sub x y`, built without
/// going through the `Rat.sub` constant so callers never nest a `d`-taking
/// call inside another.
fn diff(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let ny = rneg(d, y);
    radd(d, x, ny)
}

// --- small algebraic helpers, private to this module -----------------------

/// `w*(x*y) = x*(w*y)` — swap the outer-left factor with the inner-left one.
fn middle_swap(d: &mut IntDev<'_>, p: RatPrelude, w: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let xy = rmul(d, x, y);
    let start = rmul(d, w, xy);
    let wx = rmul(d, w, x);
    let flat = rmul(d, wx, y);
    let step1 = {
        let forward = d.lemma(p.mul_assoc, &[w, x, y]); // (w*x)*y = w*(x*y)
        rsymm(d, flat, start, forward)
    };
    let xw = rmul(d, x, w);
    let commuted = rmul(d, xw, y);
    let step2 = {
        let swap = d.lemma(p.mul_comm, &[w, x]); // w*x = x*w
        rcongr(d, wx, xw, swap, &|d, t| rmul(d, t, y))
    };
    let wy = rmul(d, w, y);
    let target = rmul(d, x, wy);
    let step3 = d.lemma(p.mul_assoc, &[x, w, y]); // (x*w)*y = x*(w*y)
    let (_, proof) = rchain(
        d,
        start,
        &[(flat, step1), (commuted, step2), (target, step3)],
    );
    proof
}

/// `(k*x) - (k*y) = k*(x - y)`.
fn mul_sub_right_rev(d: &mut IntDev<'_>, p: RatPrelude, k: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let neg_y = rneg(d, y);
    let folded_diff = radd(d, x, neg_y); // = x - y (defeq)
    let lhs_forward = rmul(d, k, folded_diff); // k*(x-y)
    let distrib = d.lemma(p.left_distrib, &[k, x, neg_y]); // k*(x+(-y)) = k*x + k*(-y)
    let kx = rmul(d, k, x);
    let k_neg_y = rmul(d, k, neg_y);
    let expanded = radd(d, kx, k_neg_y);
    let ky = rmul(d, k, y);
    let mul_neg_pf = d.lemma(p.mul_neg, &[k, y]); // k*(-y) = -(k*y)
    let neg_ky = rneg(d, ky);
    let step2 = rcongr(d, k_neg_y, neg_ky, mul_neg_pf, &|d, t| radd(d, kx, t));
    let target = radd(d, kx, neg_ky); // = k*x - k*y (defeq)
    let (_, proof_fwd) = rchain(d, lhs_forward, &[(expanded, distrib), (target, step2)]);
    rsymm(d, lhs_forward, target, proof_fwd)
}

/// `det2 x y x y = 0` — a repeated row makes the determinant vanish.
fn det2_repeat(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId) -> ExprId {
    let xy = rmul(d, x, y);
    let yx = rmul(d, y, x);
    let neg_yx = rneg(d, yx);
    let start = radd(d, xy, neg_yx); // = det2 x y x y (defeq)
    let commute = d.lemma(p.mul_comm, &[y, x]); // y*x = x*y
    let step = rcongr(d, yx, xy, commute, &|d, t| {
        let nt = rneg(d, t);
        radd(d, xy, nt)
    });
    let neg_xy = rneg(d, xy);
    let mid = radd(d, xy, neg_xy);
    let zero = rzero(d, p);
    let vanish = d.lemma(p.add_neg, &[xy]); // xy + (-xy) = 0
    let (_, proof) = rchain(d, start, &[(mid, step), (zero, vanish)]);
    proof
}

/// `det2 (p*e+q*g) (p*f+q*h) x y = p*(det2 e f x y) + q*(det2 g h x y)`.
///
/// Linearity of `det2` in its **first row**, for arbitrary second row `x y`.
#[allow(clippy::too_many_arguments)]
fn lin_row1(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pp: ExprId,
    qq: ExprId,
    ee: ExprId,
    ff: ExprId,
    gg: ExprId,
    hh: ExprId,
    xx: ExprId,
    yy: ExprId,
) -> ExprId {
    let pe = rmul(d, pp, ee);
    let qg = rmul(d, qq, gg);
    let row1a = radd(d, pe, qg);
    let pf = rmul(d, pp, ff);
    let qh = rmul(d, qq, hh);
    let row1b = radd(d, pf, qh);
    let lhs_a = rmul(d, row1a, yy);
    let lhs_b = rmul(d, row1b, xx);
    let neg_lhs_b = rneg(d, lhs_b);
    let start = radd(d, lhs_a, neg_lhs_b); // = det2 row1a row1b x y (defeq)

    let pey = rmul(d, pe, yy);
    let qgy = rmul(d, qg, yy);
    let lhs_a_expanded = radd(d, pey, qgy);
    let expand_a = d.lemma(p.right_distrib, &[pe, qg, yy]);
    let pfx = rmul(d, pf, xx);
    let qhx = rmul(d, qh, xx);
    let lhs_b_expanded = radd(d, pfx, qhx);
    let expand_b = d.lemma(p.right_distrib, &[pf, qh, xx]);

    let step1 = rcongr(d, lhs_a, lhs_a_expanded, expand_a, &|d, t| {
        let n = rneg(d, lhs_b);
        radd(d, t, n)
    });
    let mid1 = radd(d, lhs_a_expanded, neg_lhs_b);
    let step2 = rcongr(d, lhs_b, lhs_b_expanded, expand_b, &|d, t| {
        let n = rneg(d, t);
        radd(d, lhs_a_expanded, n)
    });
    let neg_lhs_b_expanded = rneg(d, lhs_b_expanded);
    let mid2 = radd(d, lhs_a_expanded, neg_lhs_b_expanded);

    let ey0 = rmul(d, ee, yy);
    let p_ey = rmul(d, pp, ey0);
    let assoc_pey = d.lemma(p.mul_assoc, &[pp, ee, yy]); // (p*e)*y = p*(e*y)
    let gy0 = rmul(d, gg, yy);
    let q_gy = rmul(d, qq, gy0);
    let assoc_qgy = d.lemma(p.mul_assoc, &[qq, gg, yy]);
    let fx0 = rmul(d, ff, xx);
    let p_fx = rmul(d, pp, fx0);
    let assoc_pfx = d.lemma(p.mul_assoc, &[pp, ff, xx]);
    let hx0 = rmul(d, hh, xx);
    let q_hx = rmul(d, qq, hx0);
    let assoc_qhx = d.lemma(p.mul_assoc, &[qq, hh, xx]);

    let lhs_a_regrouped = radd(d, p_ey, q_gy);
    let regroup_a = {
        let s1 = rcongr(d, pey, p_ey, assoc_pey, &|d, t| radd(d, t, qgy));
        let m = radd(d, p_ey, qgy);
        let s2 = rcongr(d, qgy, q_gy, assoc_qgy, &|d, t| radd(d, p_ey, t));
        let (_, pr) = rchain(d, lhs_a_expanded, &[(m, s1), (lhs_a_regrouped, s2)]);
        pr
    };
    let lhs_b_regrouped = radd(d, p_fx, q_hx);
    let regroup_b = {
        let s1 = rcongr(d, pfx, p_fx, assoc_pfx, &|d, t| radd(d, t, qhx));
        let m = radd(d, p_fx, qhx);
        let s2 = rcongr(d, qhx, q_hx, assoc_qhx, &|d, t| radd(d, p_fx, t));
        let (_, pr) = rchain(d, lhs_b_expanded, &[(m, s1), (lhs_b_regrouped, s2)]);
        pr
    };
    let step3 = rcongr(d, lhs_a_expanded, lhs_a_regrouped, regroup_a, &|d, t| {
        let n = rneg(d, lhs_b_expanded);
        radd(d, t, n)
    });
    let mid3 = radd(d, lhs_a_regrouped, neg_lhs_b_expanded);
    let step4 = rcongr(d, lhs_b_expanded, lhs_b_regrouped, regroup_b, &|d, t| {
        let n = rneg(d, t);
        radd(d, lhs_a_regrouped, n)
    });
    let neg_lhs_b_regrouped = rneg(d, lhs_b_regrouped);
    let mid4 = radd(d, lhs_a_regrouped, neg_lhs_b_regrouped);

    let split = d.lemma(p.sub_add_add, &[p_ey, q_gy, p_fx, q_hx]);
    let neg_p_fx = rneg(d, p_fx);
    let a_minus_c = radd(d, p_ey, neg_p_fx);
    let neg_q_hx = rneg(d, q_hx);
    let b_minus_e = radd(d, q_gy, neg_q_hx);
    let split_target = radd(d, a_minus_c, b_minus_e);

    let ey = rmul(d, ee, yy);
    let fx = rmul(d, ff, xx);
    let ey_minus_fx = diff(d, ey, fx); // = det2 e f x y (defeq)
    let p_scaled = rmul(d, pp, ey_minus_fx);
    let fix_p = mul_sub_right_rev(d, p, pp, ey, fx);
    let gy = rmul(d, gg, yy);
    let hx = rmul(d, hh, xx);
    let gy_minus_hx = diff(d, gy, hx); // = det2 g h x y (defeq)
    let q_scaled = rmul(d, qq, gy_minus_hx);
    let fix_q = mul_sub_right_rev(d, p, qq, gy, hx);

    let step5 = rcongr(d, a_minus_c, p_scaled, fix_p, &|d, t| radd(d, t, b_minus_e));
    let mid5 = radd(d, p_scaled, b_minus_e);
    let step6 = rcongr(d, b_minus_e, q_scaled, fix_q, &|d, t| radd(d, p_scaled, t));
    let final_val = radd(d, p_scaled, q_scaled);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (split_target, split),
            (mid5, step5),
            (final_val, step6),
        ],
    );
    proof
}

/// `det2 x y (p*e+q*g) (p*f+q*h) = p*(det2 x y e f) + q*(det2 x y g h)`.
///
/// Linearity of `det2` in its **second row**, for arbitrary first row `x y`.
#[allow(clippy::too_many_arguments)]
fn lin_row2(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    xx: ExprId,
    yy: ExprId,
    pp: ExprId,
    qq: ExprId,
    ee: ExprId,
    ff: ExprId,
    gg: ExprId,
    hh: ExprId,
) -> ExprId {
    let pe = rmul(d, pp, ee);
    let qg = rmul(d, qq, gg);
    let row2a = radd(d, pe, qg);
    let pf = rmul(d, pp, ff);
    let qh = rmul(d, qq, hh);
    let row2b = radd(d, pf, qh);
    let lhs_a = rmul(d, xx, row2b);
    let lhs_b = rmul(d, yy, row2a);
    let neg_lhs_b = rneg(d, lhs_b);
    let start = radd(d, lhs_a, neg_lhs_b); // = det2 x y row2a row2b (defeq)

    let xpf = rmul(d, xx, pf);
    let xqh = rmul(d, xx, qh);
    let lhs_a_expanded = radd(d, xpf, xqh);
    let expand_a = d.lemma(p.left_distrib, &[xx, pf, qh]);
    let ype = rmul(d, yy, pe);
    let yqg = rmul(d, yy, qg);
    let lhs_b_expanded = radd(d, ype, yqg);
    let expand_b = d.lemma(p.left_distrib, &[yy, pe, qg]);

    let step1 = rcongr(d, lhs_a, lhs_a_expanded, expand_a, &|d, t| {
        let n = rneg(d, lhs_b);
        radd(d, t, n)
    });
    let mid1 = radd(d, lhs_a_expanded, neg_lhs_b);
    let step2 = rcongr(d, lhs_b, lhs_b_expanded, expand_b, &|d, t| {
        let n = rneg(d, t);
        radd(d, lhs_a_expanded, n)
    });
    let neg_lhs_b_expanded = rneg(d, lhs_b_expanded);
    let mid2 = radd(d, lhs_a_expanded, neg_lhs_b_expanded);

    let xf0 = rmul(d, xx, ff);
    let p_xf = rmul(d, pp, xf0);
    let ms_xpf = middle_swap(d, p, xx, pp, ff); // x*(p*f) = p*(x*f)
    let xh0 = rmul(d, xx, hh);
    let q_xh = rmul(d, qq, xh0);
    let ms_xqh = middle_swap(d, p, xx, qq, hh);
    let ye0 = rmul(d, yy, ee);
    let p_ye = rmul(d, pp, ye0);
    let ms_ype = middle_swap(d, p, yy, pp, ee);
    let yg0 = rmul(d, yy, gg);
    let q_yg = rmul(d, qq, yg0);
    let ms_yqg = middle_swap(d, p, yy, qq, gg);

    let lhs_a_regrouped = radd(d, p_xf, q_xh);
    let regroup_a = {
        let s1 = rcongr(d, xpf, p_xf, ms_xpf, &|d, t| radd(d, t, xqh));
        let m = radd(d, p_xf, xqh);
        let s2 = rcongr(d, xqh, q_xh, ms_xqh, &|d, t| radd(d, p_xf, t));
        let (_, pr) = rchain(d, lhs_a_expanded, &[(m, s1), (lhs_a_regrouped, s2)]);
        pr
    };
    let lhs_b_regrouped = radd(d, p_ye, q_yg);
    let regroup_b = {
        let s1 = rcongr(d, ype, p_ye, ms_ype, &|d, t| radd(d, t, yqg));
        let m = radd(d, p_ye, yqg);
        let s2 = rcongr(d, yqg, q_yg, ms_yqg, &|d, t| radd(d, p_ye, t));
        let (_, pr) = rchain(d, lhs_b_expanded, &[(m, s1), (lhs_b_regrouped, s2)]);
        pr
    };
    let step3 = rcongr(d, lhs_a_expanded, lhs_a_regrouped, regroup_a, &|d, t| {
        let n = rneg(d, lhs_b_expanded);
        radd(d, t, n)
    });
    let mid3 = radd(d, lhs_a_regrouped, neg_lhs_b_expanded);
    let step4 = rcongr(d, lhs_b_expanded, lhs_b_regrouped, regroup_b, &|d, t| {
        let n = rneg(d, t);
        radd(d, lhs_a_regrouped, n)
    });
    let neg_lhs_b_regrouped = rneg(d, lhs_b_regrouped);
    let mid4 = radd(d, lhs_a_regrouped, neg_lhs_b_regrouped);

    let split = d.lemma(p.sub_add_add, &[p_xf, q_xh, p_ye, q_yg]);
    let neg_p_ye = rneg(d, p_ye);
    let a_minus_c = radd(d, p_xf, neg_p_ye);
    let neg_q_yg = rneg(d, q_yg);
    let b_minus_e = radd(d, q_xh, neg_q_yg);
    let split_target = radd(d, a_minus_c, b_minus_e);

    let xf = rmul(d, xx, ff);
    let ye = rmul(d, yy, ee);
    let xf_minus_ye = diff(d, xf, ye); // = det2 x y e f (defeq)
    let p_scaled = rmul(d, pp, xf_minus_ye);
    let fix_p = mul_sub_right_rev(d, p, pp, xf, ye);
    let xh = rmul(d, xx, hh);
    let yg = rmul(d, yy, gg);
    let xh_minus_yg = diff(d, xh, yg); // = det2 x y g h (defeq)
    let q_scaled = rmul(d, qq, xh_minus_yg);
    let fix_q = mul_sub_right_rev(d, p, qq, xh, yg);

    let step5 = rcongr(d, a_minus_c, p_scaled, fix_p, &|d, t| radd(d, t, b_minus_e));
    let mid5 = radd(d, p_scaled, b_minus_e);
    let step6 = rcongr(d, b_minus_e, q_scaled, fix_q, &|d, t| radd(d, p_scaled, t));
    let final_val = radd(d, p_scaled, q_scaled);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (split_target, split),
            (mid5, step5),
            (final_val, step6),
        ],
    );
    proof
}

// --- the four basic laws -----------------------------------------------------

/// `Rat.det2_swap_rows : ∀ a b c d, det2 c d a b = neg (det2 a b c d)`.
fn declare_det2_swap_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det2_swap_rows, 4, &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let lhs = rdet2(d, p, c, dd, a, b);
        let rhs_inner = rdet2(d, p, a, b, c, dd);
        let rhs = rneg(d, rhs_inner);
        let stmt = req(d, lhs, rhs);

        let ad = rmul(d, a, dd);
        let bc = rmul(d, b, c);
        let cb = rmul(d, c, b);
        let da = rmul(d, dd, a);
        let neg_da = rneg(d, da);
        let start = radd(d, cb, neg_da); // = lhs unfolded

        let cb_comm = d.lemma(p.mul_comm, &[c, b]); // c*b = b*c
        let step1 = rcongr(d, cb, bc, cb_comm, &|d, t| {
            let n = rneg(d, da);
            radd(d, t, n)
        });
        let mid1 = radd(d, bc, neg_da);

        let da_comm = d.lemma(p.mul_comm, &[dd, a]); // d*a = a*d
        let step2 = rcongr(d, da, ad, da_comm, &|d, t| {
            let n = rneg(d, t);
            radd(d, bc, n)
        });
        let neg_ad = rneg(d, ad);
        let bc_minus_ad = radd(d, bc, neg_ad);

        // rhs = neg(det2 a b c d) = neg(ad - bc) (defeq); neg_sub : neg(ad-bc) = bc-ad.
        let neg_sub_pf = d.lemma(p.neg_sub, &[ad, bc]);
        let final_step = rsymm(d, rhs, bc_minus_ad, neg_sub_pf);

        let (_, proof) = rchain(
            d,
            start,
            &[(mid1, step1), (bc_minus_ad, step2), (rhs, final_step)],
        );
        (stmt, proof)
    })
}

/// `Rat.det2_id : det2 1 0 0 1 = 1`.
fn declare_det2_id(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det2_id, 0, &|d, _v| {
        let one = rone(d, p);
        let zero = rzero(d, p);
        let lhs = rdet2(d, p, one, zero, zero, one);
        let stmt = req(d, lhs, one);

        let oo = rmul(d, one, one);
        let zz = rmul(d, zero, zero);
        let neg_zz = rneg(d, zz);
        let start = radd(d, oo, neg_zz);

        let mo = d.lemma(p.mul_one, &[one]); // 1*1 = 1
        let step1 = rcongr(d, oo, one, mo, &|d, t| {
            let n = rneg(d, zz);
            radd(d, t, n)
        });
        let mid1 = radd(d, one, neg_zz);

        let mz = d.lemma(p.mul_zero, &[zero]); // 0*0 = 0
        let step2 = rcongr(d, zz, zero, mz, &|d, t| {
            let n = rneg(d, t);
            radd(d, one, n)
        });
        let neg_zero = rneg(d, zero);
        let mid2 = radd(d, one, neg_zero);

        let nz = d.lemma(p.neg_zero, &[]); // -0 = 0
        let step3 = rcongr(d, neg_zero, zero, nz, &|d, t| radd(d, one, t));
        let mid3 = radd(d, one, zero);

        let az = d.lemma(p.add_zero, &[one]); // 1+0 = 1

        let (_, proof) = rchain(
            d,
            start,
            &[(mid1, step1), (mid2, step2), (mid3, step3), (one, az)],
        );
        (stmt, proof)
    })
}

/// `Rat.det2_scale_row : ∀ k a b c d, det2 (k*a) (k*b) c d = k * det2 a b c d`.
fn declare_det2_scale_row(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det2_scale_row, 5, &|d, v| {
        let (k, a, b, c, dd) = (v[0], v[1], v[2], v[3], v[4]);
        let ka = rmul(d, k, a);
        let kb = rmul(d, k, b);
        let lhs = rdet2(d, p, ka, kb, c, dd);
        let rhs_inner = rdet2(d, p, a, b, c, dd);
        let rhs = rmul(d, k, rhs_inner);
        let stmt = req(d, lhs, rhs);

        let ka_d = rmul(d, ka, dd);
        let kb_c = rmul(d, kb, c);
        let neg_kb_c = rneg(d, kb_c);
        let start = radd(d, ka_d, neg_kb_c);

        let a_dd = rmul(d, a, dd);
        let k_ad = rmul(d, k, a_dd);
        let assoc1 = d.lemma(p.mul_assoc, &[k, a, dd]); // (k*a)*d = k*(a*d)
        let step1 = rcongr(d, ka_d, k_ad, assoc1, &|d, t| {
            let n = rneg(d, kb_c);
            radd(d, t, n)
        });
        let mid1 = radd(d, k_ad, neg_kb_c);

        let b_c = rmul(d, b, c);
        let k_bc = rmul(d, k, b_c);
        let assoc2 = d.lemma(p.mul_assoc, &[k, b, c]); // (k*b)*c = k*(b*c)
        let step2 = rcongr(d, kb_c, k_bc, assoc2, &|d, t| {
            let n = rneg(d, t);
            radd(d, k_ad, n)
        });
        let neg_k_bc = rneg(d, k_bc);
        let mid2 = radd(d, k_ad, neg_k_bc);

        let ad_minus_bc = diff(d, a_dd, b_c); // = det2 a b c d (defeq)
        let k_scaled = rmul(d, k, ad_minus_bc); // = rhs (defeq)
        let fix = mul_sub_right_rev(d, p, k, a_dd, b_c);

        let (_, proof) = rchain(d, start, &[(mid1, step1), (mid2, step2), (k_scaled, fix)]);
        (stmt, proof)
    })
}

/// `Rat.det2_row_add : ∀ a b c d k, det2 (a + k*c) (b + k*d) c d = det2 a b c d`.
///
/// Adding a multiple of row 2 to row 1 leaves the determinant fixed — the
/// fact that makes Gaussian elimination sound.
fn declare_det2_row_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det2_row_add, 5, &|d, v| {
        let (a, b, c, dd, k) = (v[0], v[1], v[2], v[3], v[4]);
        let kc = rmul(d, k, c);
        let kd = rmul(d, k, dd);
        let row1a = radd(d, a, kc);
        let row1b = radd(d, b, kd);
        let lhs = rdet2(d, p, row1a, row1b, c, dd);
        let rhs = rdet2(d, p, a, b, c, dd);
        let stmt = req(d, lhs, rhs);

        let lhs_a = rmul(d, row1a, dd);
        let lhs_b = rmul(d, row1b, c);
        let neg_lhs_b = rneg(d, lhs_b);
        let start = radd(d, lhs_a, neg_lhs_b);

        let a_d = rmul(d, a, dd);
        let kc_d = rmul(d, kc, dd);
        let lhs_a_exp = radd(d, a_d, kc_d);
        let exp_a = d.lemma(p.right_distrib, &[a, kc, dd]);
        let step1 = rcongr(d, lhs_a, lhs_a_exp, exp_a, &|d, t| {
            let n = rneg(d, lhs_b);
            radd(d, t, n)
        });
        let mid1 = radd(d, lhs_a_exp, neg_lhs_b);

        let b_c = rmul(d, b, c);
        let kd_c = rmul(d, kd, c);
        let lhs_b_exp = radd(d, b_c, kd_c);
        let exp_b = d.lemma(p.right_distrib, &[b, kd, c]);
        let step2 = rcongr(d, lhs_b, lhs_b_exp, exp_b, &|d, t| {
            let n = rneg(d, t);
            radd(d, lhs_a_exp, n)
        });
        let neg_lhs_b_exp = rneg(d, lhs_b_exp);
        let mid2 = radd(d, lhs_a_exp, neg_lhs_b_exp);

        let split = d.lemma(p.sub_add_add, &[a_d, kc_d, b_c, kd_c]);
        let ad_minus_bc = diff(d, a_d, b_c); // = rhs (defeq)
        let kcd_minus_kdc = diff(d, kc_d, kd_c);
        let split_target = radd(d, ad_minus_bc, kcd_minus_kdc);

        // kc_d - kd_c = 0: both reduce to k*(c*d), read through mul_comm.
        let c_dd = rmul(d, c, dd);
        let k_cd = rmul(d, k, c_dd);
        let assoc_a = d.lemma(p.mul_assoc, &[k, c, dd]); // (k*c)*d = k*(c*d)
        let dd_c = rmul(d, dd, c);
        let k_dc = rmul(d, k, dd_c);
        let assoc_b = d.lemma(p.mul_assoc, &[k, dd, c]); // (k*d)*c = k*(d*c)
        let cd_comm = d.lemma(p.mul_comm, &[c, dd]); // c*d = d*c
        let k_cd_eq_k_dc = rcongr(d, c_dd, dd_c, cd_comm, &|d, t| rmul(d, k, t));

        let neg_kd_c = rneg(d, kd_c);
        let step_a = rcongr(d, kc_d, k_cd, assoc_a, &|d, t| {
            let n = rneg(d, kd_c);
            radd(d, t, n)
        });
        let mid_a = radd(d, k_cd, neg_kd_c);
        let step_b = rcongr(d, kd_c, k_dc, assoc_b, &|d, t| {
            let n = rneg(d, t);
            radd(d, k_cd, n)
        });
        let neg_k_dc = rneg(d, k_dc);
        let mid_b = radd(d, k_cd, neg_k_dc);
        let step_c = {
            let back = rsymm(d, k_cd, k_dc, k_cd_eq_k_dc);
            rcongr(d, k_dc, k_cd, back, &|d, t| {
                let n = rneg(d, t);
                radd(d, k_cd, n)
            })
        };
        let neg_k_cd = rneg(d, k_cd);
        let mid_c = radd(d, k_cd, neg_k_cd);
        let zero = rzero(d, p);
        let vanish = d.lemma(p.add_neg, &[k_cd]);

        let (_, kcd_zero) = rchain(
            d,
            kcd_minus_kdc,
            &[
                (mid_a, step_a),
                (mid_b, step_b),
                (mid_c, step_c),
                (zero, vanish),
            ],
        );

        let step5 = rcongr(d, kcd_minus_kdc, zero, kcd_zero, &|d, t| {
            radd(d, ad_minus_bc, t)
        });
        let mid5 = radd(d, ad_minus_bc, zero);
        let az = d.lemma(p.add_zero, &[ad_minus_bc]);

        let (_, proof) = rchain(
            d,
            start,
            &[
                (mid1, step1),
                (mid2, step2),
                (split_target, split),
                (mid5, step5),
                (ad_minus_bc, az),
            ],
        );
        (stmt, proof)
    })
}

/// `Rat.det2_mul : ∀ a b c d e f g h,`
/// `  det2 (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) = det2 a b c d * det2 e f g h`.
fn declare_det2_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det2_mul, 8, &|d, v| {
        let (a, b, c, dd, e, f, g, h) = (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);

        let ae = rmul(d, a, e);
        let bg = rmul(d, b, g);
        let row1a = radd(d, ae, bg);
        let af = rmul(d, a, f);
        let bh = rmul(d, b, h);
        let row1b = radd(d, af, bh);
        let ce = rmul(d, c, e);
        let dg = rmul(d, dd, g);
        let row2a = radd(d, ce, dg);
        let cf = rmul(d, c, f);
        let dh = rmul(d, dd, h);
        let row2b = radd(d, cf, dh);

        let lhs = rdet2(d, p, row1a, row1b, row2a, row2b);
        let big_x = rdet2(d, p, e, f, g, h);
        let det_abcd = rdet2(d, p, a, b, c, dd);
        let rhs = rmul(d, det_abcd, big_x);
        let stmt = req(d, lhs, rhs);

        // Step 1: det2 row1a row1b row2a row2b = a*(det2 e f row2a row2b) + b*(det2 g h row2a row2b).
        let proof1 = lin_row1(d, p, a, b, e, f, g, h, row2a, row2b);
        let det_ef_22 = rdet2(d, p, e, f, row2a, row2b);
        let det_gh_22 = rdet2(d, p, g, h, row2a, row2b);
        let a_ef22 = rmul(d, a, det_ef_22);
        let b_gh22 = rmul(d, b, det_gh_22);
        let after1 = radd(d, a_ef22, b_gh22);

        // Step 2: det2 e f row2a row2b = c*(det2 e f e f) + d*big_x = d*big_x.
        let proof2 = lin_row2(d, p, e, f, c, dd, e, f, g, h);
        let det_ef_ef = rdet2(d, p, e, f, e, f);
        let c_efef = rmul(d, c, det_ef_ef);
        let dx = rmul(d, dd, big_x);
        let after2 = radd(d, c_efef, dx);
        let rep_ef = det2_repeat(d, p, e, f);
        let zero = rzero(d, p);
        let c_zero = rmul(d, c, zero);
        let after2b = radd(d, c_zero, dx);
        let step2b = rcongr(d, det_ef_ef, zero, rep_ef, &|d, t| {
            let ct = rmul(d, c, t);
            radd(d, ct, dx)
        });
        let mz = d.lemma(p.mul_zero, &[c]); // c*0 = 0
        let after2c = radd(d, zero, dx);
        let step2c = rcongr(d, c_zero, zero, mz, &|d, t| radd(d, t, dx));
        let za = d.lemma(p.zero_add, &[dx]); // 0+d*X = d*X

        let (_, ef_reduced) = rchain(
            d,
            det_ef_22,
            &[
                (after2, proof2),
                (after2b, step2b),
                (after2c, step2c),
                (dx, za),
            ],
        );

        // Step 3: det2 g h row2a row2b = c*(det2 g h e f) + d*(det2 g h g h) = c*(-big_x).
        let proof3 = lin_row2(d, p, g, h, c, dd, e, f, g, h);
        let det_gh_ef = rdet2(d, p, g, h, e, f);
        let det_gh_gh = rdet2(d, p, g, h, g, h);
        let c_ghef = rmul(d, c, det_gh_ef);
        let dd_ghgh = rmul(d, dd, det_gh_gh);
        let after3 = radd(d, c_ghef, dd_ghgh);
        let swap_pf = d.lemma(p.det2_swap_rows, &[e, f, g, h]); // det2 g h e f = neg(det2 e f g h)
        let neg_x = rneg(d, big_x);
        let c_negx = rmul(d, c, neg_x);
        let after3b = radd(d, c_negx, dd_ghgh);
        let step3b = rcongr(d, det_gh_ef, neg_x, swap_pf, &|d, t| {
            let ct = rmul(d, c, t);
            radd(d, ct, dd_ghgh)
        });
        let rep_gh = det2_repeat(d, p, g, h);
        let dd_zero = rmul(d, dd, zero);
        let after3c = radd(d, c_negx, dd_zero);
        let step3c = rcongr(d, det_gh_gh, zero, rep_gh, &|d, t| {
            let ddt = rmul(d, dd, t);
            radd(d, c_negx, ddt)
        });
        let mz2 = d.lemma(p.mul_zero, &[dd]); // d*0 = 0
        let after3d = radd(d, c_negx, zero);
        let step3d = rcongr(d, dd_zero, zero, mz2, &|d, t| radd(d, c_negx, t));
        let az = d.lemma(p.add_zero, &[c_negx]); // c_negx + 0 = c_negx

        let (_, gh_reduced) = rchain(
            d,
            det_gh_22,
            &[
                (after3, proof3),
                (after3b, step3b),
                (after3c, step3c),
                (after3d, step3d),
                (c_negx, az),
            ],
        );

        // Combine: after1 = a*(d*X) + b*(c*(-X)).
        let a_ddx = rmul(d, a, dx);
        let b_cnegx = rmul(d, b, c_negx);
        let combine1 = rcongr(d, det_ef_22, dx, ef_reduced, &|d, t| {
            let at = rmul(d, a, t);
            radd(d, at, b_gh22)
        });
        let mid_c1 = radd(d, a_ddx, b_gh22);
        let combine2 = rcongr(d, det_gh_22, c_negx, gh_reduced, &|d, t| {
            let bt = rmul(d, b, t);
            radd(d, a_ddx, bt)
        });
        let mid_c2 = radd(d, a_ddx, b_cnegx);

        // a*(d*X) -> (a*d)*X.
        let a_d = rmul(d, a, dd);
        let ad_x = rmul(d, a_d, big_x);
        let assoc1 = d.lemma(p.mul_assoc, &[a, dd, big_x]); // (a*d)*X = a*(d*X)
        let un_assoc1 = rsymm(d, ad_x, a_ddx, assoc1);
        let step_u1 = rcongr(d, a_ddx, ad_x, un_assoc1, &|d, t| radd(d, t, b_cnegx));
        let mid_u1 = radd(d, ad_x, b_cnegx);

        // b*(c*(-X)) -> (b*c)*(-X) -> -((b*c)*X).
        let b_c = rmul(d, b, c);
        let bc_negx = rmul(d, b_c, neg_x);
        let assoc2 = d.lemma(p.mul_assoc, &[b, c, neg_x]); // (b*c)*(-X) = b*(c*(-X))
        let un_assoc2 = rsymm(d, bc_negx, b_cnegx, assoc2);
        let step_u2 = rcongr(d, b_cnegx, bc_negx, un_assoc2, &|d, t| radd(d, ad_x, t));
        let mid_u2 = radd(d, ad_x, bc_negx);

        let bc_x = rmul(d, b_c, big_x);
        let neg_bcx = rneg(d, bc_x);
        let mul_neg_pf = d.lemma(p.mul_neg, &[b_c, big_x]); // (b*c)*(-X) = -((b*c)*X)
        let step_u3 = rcongr(d, bc_negx, neg_bcx, mul_neg_pf, &|d, t| radd(d, ad_x, t));
        let mid_u3 = radd(d, ad_x, neg_bcx); // = (a*d)*X - (b*c)*X

        // sub_mul: (a*d)*X - (b*c)*X = ((a*d)-(b*c))*X = det2 a b c d * X = rhs.
        let sub_mul_pf = d.lemma(p.sub_mul, &[a_d, b_c, big_x]);

        let (_, proof) = rchain(
            d,
            after1,
            &[
                (mid_c1, combine1),
                (mid_c2, combine2),
                (mid_u1, step_u1),
                (mid_u2, step_u2),
                (mid_u3, step_u3),
                (rhs, sub_mul_pf),
            ],
        );

        let final_proof = rtrans(d, lhs, after1, rhs, proof1, proof);
        (stmt, final_proof)
    })
}

// --- the adjugate identity ---------------------------------------------------
//
// `A * adj(A) = det(A) * I`, entrywise. `adj2` is not reified as a kernel
// constant — a function returning four rationals needs a product/tuple type,
// and the kernel has none — so the four entries `d, -b, -c, a` are written out
// directly in each of the four theorems below, one per matrix entry of the
// product. No hypothesis: every one of the four is an identity.

/// Admit the four entries of `A · adj(A) = det(A) · I`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_adjugate(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mul_adj2_top_left(d, p)?;
    declare_mul_adj2_top_right(d, p)?;
    declare_mul_adj2_bottom_left(d, p)?;
    declare_mul_adj2_bottom_right(d, p)
}

/// `Rat.mul_adj2_top_left : ∀ a b c d, a*d + b*(-c) = det2 a b c d`.
fn declare_mul_adj2_top_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_adj2_top_left, 4, &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let neg_c = rneg(d, c);
        let b_negc = rmul(d, b, neg_c);
        let a_d = rmul(d, a, dd);
        let lhs = radd(d, a_d, b_negc);
        let rhs = rdet2(d, p, a, b, c, dd);
        let stmt = req(d, lhs, rhs);

        let mul_neg_pf = d.lemma(p.mul_neg, &[b, c]); // b*(-c) = -(b*c)
        let b_c = rmul(d, b, c);
        let neg_bc = rneg(d, b_c);
        let step = rcongr(d, b_negc, neg_bc, mul_neg_pf, &|d, t| radd(d, a_d, t));
        let target = radd(d, a_d, neg_bc); // = det2 a b c d (defeq)

        let (_, proof) = rchain(d, lhs, &[(target, step)]);
        (stmt, proof)
    })
}

/// `Rat.mul_adj2_top_right : ∀ a b c d, a*(-b) + b*a = 0`.
fn declare_mul_adj2_top_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_adj2_top_right, 4, &|d, v| {
        let (a, b, _c, _dd) = (v[0], v[1], v[2], v[3]);
        let neg_b = rneg(d, b);
        let a_negb = rmul(d, a, neg_b);
        let b_a = rmul(d, b, a);
        let lhs = radd(d, a_negb, b_a);
        let zero = rzero(d, p);
        let stmt = req(d, lhs, zero);

        let mul_neg_pf = d.lemma(p.mul_neg, &[a, b]); // a*(-b) = -(a*b)
        let a_b = rmul(d, a, b);
        let neg_ab = rneg(d, a_b);
        let step1 = rcongr(d, a_negb, neg_ab, mul_neg_pf, &|d, t| radd(d, t, b_a));
        let mid1 = radd(d, neg_ab, b_a);

        let comm_pf = d.lemma(p.mul_comm, &[b, a]); // b*a = a*b
        let step2 = rcongr(d, b_a, a_b, comm_pf, &|d, t| radd(d, neg_ab, t));
        let mid2 = radd(d, neg_ab, a_b);

        let cancel = d.lemma(p.neg_add_cancel, &[a_b]); // -(a*b) + a*b = 0

        let (_, proof) = rchain(d, lhs, &[(mid1, step1), (mid2, step2), (zero, cancel)]);
        (stmt, proof)
    })
}

/// `Rat.mul_adj2_bottom_left : ∀ a b c d, c*d + d*(-c) = 0`.
fn declare_mul_adj2_bottom_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_adj2_bottom_left, 4, &|d, v| {
        let (_a, _b, c, dd) = (v[0], v[1], v[2], v[3]);
        let neg_c = rneg(d, c);
        let d_negc = rmul(d, dd, neg_c);
        let c_d = rmul(d, c, dd);
        let lhs = radd(d, c_d, d_negc);
        let zero = rzero(d, p);
        let stmt = req(d, lhs, zero);

        let mul_neg_pf = d.lemma(p.mul_neg, &[dd, c]); // d*(-c) = -(d*c)
        let d_c = rmul(d, dd, c);
        let neg_dc = rneg(d, d_c);
        let step1 = rcongr(d, d_negc, neg_dc, mul_neg_pf, &|d, t| radd(d, c_d, t));
        let mid1 = radd(d, c_d, neg_dc);

        let comm_pf = d.lemma(p.mul_comm, &[dd, c]); // d*c = c*d
        let step2 = rcongr(d, d_c, c_d, comm_pf, &|d, t| {
            let n = rneg(d, t);
            radd(d, c_d, n)
        });
        let neg_c_d = rneg(d, c_d);
        let mid2 = radd(d, c_d, neg_c_d);

        let vanish = d.lemma(p.add_neg, &[c_d]); // c*d + -(c*d) = 0

        let (_, proof) = rchain(d, lhs, &[(mid1, step1), (mid2, step2), (zero, vanish)]);
        (stmt, proof)
    })
}

/// `Rat.mul_adj2_bottom_right : ∀ a b c d, c*(-b) + d*a = det2 a b c d`.
fn declare_mul_adj2_bottom_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_adj2_bottom_right, 4, &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let neg_b = rneg(d, b);
        let c_negb = rmul(d, c, neg_b);
        let d_a = rmul(d, dd, a);
        let lhs = radd(d, c_negb, d_a);
        let rhs = rdet2(d, p, a, b, c, dd);
        let stmt = req(d, lhs, rhs);

        let mul_neg_pf = d.lemma(p.mul_neg, &[c, b]); // c*(-b) = -(c*b)
        let c_b = rmul(d, c, b);
        let neg_cb = rneg(d, c_b);
        let step1 = rcongr(d, c_negb, neg_cb, mul_neg_pf, &|d, t| radd(d, t, d_a));
        let mid1 = radd(d, neg_cb, d_a);

        let comm1 = d.lemma(p.mul_comm, &[c, b]); // c*b = b*c
        let b_c = rmul(d, b, c);
        let step2 = rcongr(d, c_b, b_c, comm1, &|d, t| {
            let n = rneg(d, t);
            radd(d, n, d_a)
        });
        let neg_bc = rneg(d, b_c);
        let mid2 = radd(d, neg_bc, d_a);

        let comm2 = d.lemma(p.mul_comm, &[dd, a]); // d*a = a*d
        let a_d = rmul(d, a, dd);
        let step3 = rcongr(d, d_a, a_d, comm2, &|d, t| radd(d, neg_bc, t));
        let mid3 = radd(d, neg_bc, a_d); // = -(b*c) + a*d

        let add_comm_pf = d.lemma(p.add_comm, &[neg_bc, a_d]); // -(b*c)+a*d = a*d+-(b*c)
        let target = radd(d, a_d, neg_bc); // = det2 a b c d (defeq)

        let (_, proof) = rchain(
            d,
            lhs,
            &[
                (mid1, step1),
                (mid2, step2),
                (mid3, step3),
                (target, add_comm_pf),
            ],
        );
        (stmt, proof)
    })
}
