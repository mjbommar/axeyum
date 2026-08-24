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
use crate::name::NameId;
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
    declare_adjugate(d, p)?;
    declare_inverse(d, p)?;
    declare_cramer(d, p)
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

// --- the inverse: A⁻¹·A = I, entrywise --------------------------------------
//
// `A⁻¹ = adj(A) / det(A)`, so each entry of `A⁻¹` is `Rat.inv (det2 a b c d)`
// times the matching adjugate entry, written with the scalar `invD` as the
// LEFTMOST factor in every product (`invD * d`, not `d * invD`) so that
// pulling it back out of a two-factor product is a single `mul_assoc`, not a
// `mul_comm` followed by a `mul_assoc`. `adj2` is still not reified, for the
// same reason `mul_adj2_*` above does not reify it: no product/tuple type.

/// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Rat), hyp → concl`, given a
/// statement builder (returning `(hyp, concl)`) and a proof builder (given the
/// bound variables and the hypothesis witness, returning a proof of `concl`).
///
/// The hypothesis-carrying counterpart of [`rat_theorem`], which only covers
/// theorems with no hypothesis at all — every `inv2_*`/`cramer_two_*` theorem
/// needs `det2 a b c d ≠ 0`, which is not itself `Rat`-typed, so it cannot be
/// one more entry in `rat_theorem`'s uniform `Rat`-typed argument list.
fn rat_theorem_hyp(
    d: &mut IntDev<'_>,
    name: NameId,
    arity: usize,
    stmt: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
    proof: &dyn Fn(&mut IntDev<'_>, &[ExprId], ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (hyp_ty, concl_ty) = stmt(d, &vars);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let body = proof(d, &vars, h);

    let mut ty = d.arrow(hyp_ty, concl_ty);
    let mut value = d.lam_fv(h_fv, hyp_ty, body);
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, carrier, ty);
        value = d.lam_fv(fv, carrier, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Not (Eq Rat (det2 a b c d) Rat.zero)`.
fn det2_ne_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> ExprId {
    let det = rdet2(d, p, a, b, c, dd);
    let zero = rzero(d, p);
    let eq_zero = req(d, det, zero);
    d.not(eq_zero)
}

/// `Rat.inv (det2 a b c d)`.
fn inv_det2(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> ExprId {
    let det = rdet2(d, p, a, b, c, dd);
    d.const_app(p.inv, &[det])
}

/// `invD*D = 1`, given `h : D ≠ 0` — `mul_inv_cancel_of_ne_zero` read through
/// `mul_comm`, since that law is stated `D * invD = 1`.
fn inv_det2_cancel(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    det: ExprId,
    inv_det: ExprId,
    h: ExprId,
) -> ExprId {
    let start = rmul(d, inv_det, det);
    let comm = d.lemma(p.mul_comm, &[inv_det, det]); // invD*D = D*invD
    let flipped = rmul(d, det, inv_det);
    let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[det, h]); // D*invD = 1
    let one = rone(d, p);
    rtrans(d, start, flipped, one, comm, cancel)
}

/// Admit the four entries of `A⁻¹·A = I`, given `det2 a b c d ≠ 0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_inverse(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_inv2_top_left(d, p)?;
    declare_inv2_top_right(d, p)?;
    declare_inv2_bottom_left(d, p)?;
    declare_inv2_bottom_right(d, p)
}

/// `Rat.inv2_top_left : ∀ a b c d, det2 a b c d ≠ 0 →`
/// `  (invD*d)*a + (invD*(-b))*c = 1`, `invD := Rat.inv (det2 a b c d)`.
///
/// The (1,1) entry of `A⁻¹·A`. Factor `invD` out of both terms by
/// `mul_assoc` (one step each, since `invD` is already the leftmost factor),
/// combine with `left_distrib` run backward, match the resulting sum against
/// [`declare_mul_adj2_top_left`]'s `a*d + b*(-c) = det2 a b c d` (one
/// `mul_comm` for the first term, `neg_mul` then `mul_neg` for the second),
/// then cancel `invD*D` against `mul_inv_cancel_of_ne_zero`.
fn declare_inv2_top_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem_hyp(
        d,
        p.inv2_top_left,
        4,
        &|d, v| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let hyp = det2_ne_zero(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let inv11 = rmul(d, inv_det, dd);
            let neg_b = rneg(d, b);
            let inv12 = rmul(d, inv_det, neg_b);
            let term1 = rmul(d, inv11, a);
            let term2 = rmul(d, inv12, c);
            let lhs = radd(d, term1, term2);
            let one = rone(d, p);
            let concl = req(d, lhs, one);
            (hyp, concl)
        },
        &|d, v, h| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let det = rdet2(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_b = rneg(d, b);

            let inv11 = rmul(d, inv_det, dd);
            let inv12 = rmul(d, inv_det, neg_b);
            let term1 = rmul(d, inv11, a);
            let term2 = rmul(d, inv12, c);
            let start = radd(d, term1, term2);

            let da = rmul(d, dd, a);
            let negb_c = rmul(d, neg_b, c);
            let inv_det_da = rmul(d, inv_det, da);
            let inv_det_negbc = rmul(d, inv_det, negb_c);

            let f1 = d.lemma(p.mul_assoc, &[inv_det, dd, a]); // (invD*d)*a = invD*(d*a)
            let step1 = rcongr(d, term1, inv_det_da, f1, &|d, t| radd(d, t, term2));
            let mid1 = radd(d, inv_det_da, term2);

            let f2 = d.lemma(p.mul_assoc, &[inv_det, neg_b, c]); // (invD*(-b))*c = invD*((-b)*c)
            let step2 = rcongr(d, term2, inv_det_negbc, f2, &|d, t| radd(d, inv_det_da, t));
            let mid2 = radd(d, inv_det_da, inv_det_negbc);

            let combined_inner = radd(d, da, negb_c);
            let combined = rmul(d, inv_det, combined_inner);
            let distrib_fwd = d.lemma(p.left_distrib, &[inv_det, da, negb_c]); // invD*(da+(-b)c) = invD*da+invD*(-b)c
            let step3 = rsymm(d, combined, mid2, distrib_fwd);

            // rewrite (d*a) + ((-b)*c) to a*d + b*(-c), mul_adj2_top_left's LHS.
            let a_dd = rmul(d, a, dd);
            let comm1 = d.lemma(p.mul_comm, &[dd, a]); // d*a = a*d
            let inner_step1 = rcongr(d, da, a_dd, comm1, &|d, t| radd(d, t, negb_c));
            let inner_mid1 = radd(d, a_dd, negb_c);

            let bc = rmul(d, b, c);
            let neg_bc = rneg(d, bc);
            let neg_mul_pf = d.lemma(p.neg_mul, &[b, c]); // (-b)*c = -(b*c)
            let inner_step2 = rcongr(d, negb_c, neg_bc, neg_mul_pf, &|d, t| radd(d, a_dd, t));
            let inner_mid2 = radd(d, a_dd, neg_bc);

            let neg_c = rneg(d, c);
            let b_negc = rmul(d, b, neg_c);
            let mul_neg_pf = d.lemma(p.mul_neg, &[b, c]); // b*(-c) = -(b*c)
            let neg_bc_to_bnegc = rsymm(d, b_negc, neg_bc, mul_neg_pf); // -(b*c) = b*(-c)
            let inner_step3 = rcongr(d, neg_bc, b_negc, neg_bc_to_bnegc, &|d, t| radd(d, a_dd, t));
            let inner_target = radd(d, a_dd, b_negc);

            let (_, inner_proof) = rchain(
                d,
                combined_inner,
                &[
                    (inner_mid1, inner_step1),
                    (inner_mid2, inner_step2),
                    (inner_target, inner_step3),
                ],
            );

            let step4 = rcongr(d, combined_inner, inner_target, inner_proof, &|d, t| {
                rmul(d, inv_det, t)
            });
            let mid4 = rmul(d, inv_det, inner_target);

            let adj_pf = d.lemma(p.mul_adj2_top_left, &[a, b, c, dd]); // a*d + b*(-c) = det2 a b c d
            let step5 = rcongr(d, inner_target, det, adj_pf, &|d, t| rmul(d, inv_det, t));
            let mid5 = rmul(d, inv_det, det);

            let one = rone(d, p);
            let cancel = inv_det2_cancel(d, p, det, inv_det, h);

            let (_, proof) = rchain(
                d,
                start,
                &[
                    (mid1, step1),
                    (mid2, step2),
                    (combined, step3),
                    (mid4, step4),
                    (mid5, step5),
                    (one, cancel),
                ],
            );
            proof
        },
    )
}

/// `Rat.inv2_top_right : ∀ a b c d, det2 a b c d ≠ 0 →`
/// `  (invD*d)*b + (invD*(-b))*d = 0`, `invD := Rat.inv (det2 a b c d)`.
///
/// The (1,2) entry of `A⁻¹·A`. No determinant identity needed: after
/// factoring `invD` out, the inner sum is `d*b + (-b)*d`, which collapses to
/// `d*b + -(d*b)` by `neg_mul` and one `mul_comm`, then `add_neg`.
fn declare_inv2_top_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem_hyp(
        d,
        p.inv2_top_right,
        4,
        &|d, v| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let hyp = det2_ne_zero(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let inv11 = rmul(d, inv_det, dd);
            let neg_b = rneg(d, b);
            let inv12 = rmul(d, inv_det, neg_b);
            let term1 = rmul(d, inv11, b);
            let term2 = rmul(d, inv12, dd);
            let lhs = radd(d, term1, term2);
            let zero = rzero(d, p);
            let concl = req(d, lhs, zero);
            (hyp, concl)
        },
        &|d, v, _h| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_b = rneg(d, b);

            let inv11 = rmul(d, inv_det, dd);
            let inv12 = rmul(d, inv_det, neg_b);
            let term1 = rmul(d, inv11, b);
            let term2 = rmul(d, inv12, dd);
            let start = radd(d, term1, term2);

            let db = rmul(d, dd, b);
            let negb_d = rmul(d, neg_b, dd);
            let inv_det_db = rmul(d, inv_det, db);
            let inv_det_negbd = rmul(d, inv_det, negb_d);

            let f1 = d.lemma(p.mul_assoc, &[inv_det, dd, b]); // (invD*d)*b = invD*(d*b)
            let step1 = rcongr(d, term1, inv_det_db, f1, &|d, t| radd(d, t, term2));
            let mid1 = radd(d, inv_det_db, term2);

            let f2 = d.lemma(p.mul_assoc, &[inv_det, neg_b, dd]); // (invD*(-b))*d = invD*((-b)*d)
            let step2 = rcongr(d, term2, inv_det_negbd, f2, &|d, t| radd(d, inv_det_db, t));
            let mid2 = radd(d, inv_det_db, inv_det_negbd);

            let combined_inner = radd(d, db, negb_d);
            let combined = rmul(d, inv_det, combined_inner);
            let distrib_fwd = d.lemma(p.left_distrib, &[inv_det, db, negb_d]);
            let step3 = rsymm(d, combined, mid2, distrib_fwd);

            // (d*b) + ((-b)*d) -> (d*b) + -(b*d) -> (d*b) + -(d*b) -> 0.
            let bd = rmul(d, b, dd);
            let neg_bd = rneg(d, bd);
            let neg_mul_pf = d.lemma(p.neg_mul, &[b, dd]); // (-b)*d = -(b*d)
            let inner_step1 = rcongr(d, negb_d, neg_bd, neg_mul_pf, &|d, t| radd(d, db, t));
            let inner_mid1 = radd(d, db, neg_bd);

            let db_comm = d.lemma(p.mul_comm, &[b, dd]); // b*d = d*b
            let neg_db = rneg(d, db);
            let inner_step2 = rcongr(d, bd, db, db_comm, &|d, t| {
                let n = rneg(d, t);
                radd(d, db, n)
            });
            let inner_mid2 = radd(d, db, neg_db);

            let zero = rzero(d, p);
            let vanish = d.lemma(p.add_neg, &[db]); // d*b + -(d*b) = 0

            let (_, inner_proof) = rchain(
                d,
                combined_inner,
                &[
                    (inner_mid1, inner_step1),
                    (inner_mid2, inner_step2),
                    (zero, vanish),
                ],
            );

            let step4 = rcongr(d, combined_inner, zero, inner_proof, &|d, t| {
                rmul(d, inv_det, t)
            });
            let mid4 = rmul(d, inv_det, zero);

            let mz = d.lemma(p.mul_zero, &[inv_det]); // invD*0 = 0

            let (_, proof) = rchain(
                d,
                start,
                &[
                    (mid1, step1),
                    (mid2, step2),
                    (combined, step3),
                    (mid4, step4),
                    (zero, mz),
                ],
            );
            proof
        },
    )
}

/// `Rat.inv2_bottom_left : ∀ a b c d, det2 a b c d ≠ 0 →`
/// `  (invD*(-c))*a + (invD*a)*c = 0`, `invD := Rat.inv (det2 a b c d)`.
///
/// The (2,1) entry of `A⁻¹·A`. After factoring `invD` out, the inner sum is
/// `(-c)*a + a*c`, which collapses to `-(a*c) + a*c` by `neg_mul` and one
/// `mul_comm`, then `neg_add_cancel`.
fn declare_inv2_bottom_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem_hyp(
        d,
        p.inv2_bottom_left,
        4,
        &|d, v| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let hyp = det2_ne_zero(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_c = rneg(d, c);
            let inv21 = rmul(d, inv_det, neg_c);
            let inv22 = rmul(d, inv_det, a);
            let term1 = rmul(d, inv21, a);
            let term2 = rmul(d, inv22, c);
            let lhs = radd(d, term1, term2);
            let zero = rzero(d, p);
            let concl = req(d, lhs, zero);
            (hyp, concl)
        },
        &|d, v, _h| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_c = rneg(d, c);

            let inv21 = rmul(d, inv_det, neg_c);
            let inv22 = rmul(d, inv_det, a);
            let term1 = rmul(d, inv21, a);
            let term2 = rmul(d, inv22, c);
            let start = radd(d, term1, term2);

            let neg_ca = rmul(d, neg_c, a);
            let ac0 = rmul(d, a, c);
            let inv_det_negca = rmul(d, inv_det, neg_ca);
            let inv_det_ac = rmul(d, inv_det, ac0);

            let f1 = d.lemma(p.mul_assoc, &[inv_det, neg_c, a]); // (invD*(-c))*a = invD*((-c)*a)
            let step1 = rcongr(d, term1, inv_det_negca, f1, &|d, t| radd(d, t, term2));
            let mid1 = radd(d, inv_det_negca, term2);

            let f2 = d.lemma(p.mul_assoc, &[inv_det, a, c]); // (invD*a)*c = invD*(a*c)
            let step2 = rcongr(d, term2, inv_det_ac, f2, &|d, t| radd(d, inv_det_negca, t));
            let mid2 = radd(d, inv_det_negca, inv_det_ac);

            let combined_inner = radd(d, neg_ca, ac0);
            let combined = rmul(d, inv_det, combined_inner);
            let distrib_fwd = d.lemma(p.left_distrib, &[inv_det, neg_ca, ac0]);
            let step3 = rsymm(d, combined, mid2, distrib_fwd);

            // (-c)*a + a*c -> -(c*a) + a*c -> -(a*c) + a*c -> 0.
            let ca = rmul(d, c, a);
            let neg_caval = rneg(d, ca);
            let neg_mul_pf = d.lemma(p.neg_mul, &[c, a]); // (-c)*a = -(c*a)
            let inner_step1 = rcongr(d, neg_ca, neg_caval, neg_mul_pf, &|d, t| radd(d, t, ac0));
            let inner_mid1 = radd(d, neg_caval, ac0);

            let ca_comm = d.lemma(p.mul_comm, &[c, a]); // c*a = a*c
            let neg_ac = rneg(d, ac0);
            let inner_step2 = rcongr(d, ca, ac0, ca_comm, &|d, t| {
                let n = rneg(d, t);
                radd(d, n, ac0)
            });
            let inner_mid2 = radd(d, neg_ac, ac0);

            let zero = rzero(d, p);
            let vanish = d.lemma(p.neg_add_cancel, &[ac0]); // -(a*c) + a*c = 0

            let (_, inner_proof) = rchain(
                d,
                combined_inner,
                &[
                    (inner_mid1, inner_step1),
                    (inner_mid2, inner_step2),
                    (zero, vanish),
                ],
            );

            let step4 = rcongr(d, combined_inner, zero, inner_proof, &|d, t| {
                rmul(d, inv_det, t)
            });
            let mid4 = rmul(d, inv_det, zero);

            let mz = d.lemma(p.mul_zero, &[inv_det]); // invD*0 = 0

            let (_, proof) = rchain(
                d,
                start,
                &[
                    (mid1, step1),
                    (mid2, step2),
                    (combined, step3),
                    (mid4, step4),
                    (zero, mz),
                ],
            );
            proof
        },
    )
}

/// `Rat.inv2_bottom_right : ∀ a b c d, det2 a b c d ≠ 0 →`
/// `  (invD*(-c))*b + (invD*a)*d = 1`, `invD := Rat.inv (det2 a b c d)`.
///
/// The (2,2) entry of `A⁻¹·A`. Factor `invD` out of both terms, match the sum
/// against [`declare_mul_adj2_bottom_right`]'s `c*(-b) + d*a = det2 a b c d`
/// (`neg_mul` then `mul_neg` for the first term, `mul_comm` for the second),
/// then cancel `invD*D` against `mul_inv_cancel_of_ne_zero`.
fn declare_inv2_bottom_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem_hyp(
        d,
        p.inv2_bottom_right,
        4,
        &|d, v| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let hyp = det2_ne_zero(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_c = rneg(d, c);
            let inv21 = rmul(d, inv_det, neg_c);
            let inv22 = rmul(d, inv_det, a);
            let term1 = rmul(d, inv21, b);
            let term2 = rmul(d, inv22, dd);
            let lhs = radd(d, term1, term2);
            let one = rone(d, p);
            let concl = req(d, lhs, one);
            (hyp, concl)
        },
        &|d, v, h| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let det = rdet2(d, p, a, b, c, dd);
            let inv_det = inv_det2(d, p, a, b, c, dd);
            let neg_c = rneg(d, c);

            let inv21 = rmul(d, inv_det, neg_c);
            let inv22 = rmul(d, inv_det, a);
            let term1 = rmul(d, inv21, b);
            let term2 = rmul(d, inv22, dd);
            let start = radd(d, term1, term2);

            let negc_b = rmul(d, neg_c, b);
            let a_dd = rmul(d, a, dd);
            let inv_det_negcb = rmul(d, inv_det, negc_b);
            let inv_det_add = rmul(d, inv_det, a_dd);

            let f1 = d.lemma(p.mul_assoc, &[inv_det, neg_c, b]); // (invD*(-c))*b = invD*((-c)*b)
            let step1 = rcongr(d, term1, inv_det_negcb, f1, &|d, t| radd(d, t, term2));
            let mid1 = radd(d, inv_det_negcb, term2);

            let f2 = d.lemma(p.mul_assoc, &[inv_det, a, dd]); // (invD*a)*d = invD*(a*d)
            let step2 = rcongr(d, term2, inv_det_add, f2, &|d, t| radd(d, inv_det_negcb, t));
            let mid2 = radd(d, inv_det_negcb, inv_det_add);

            let combined_inner = radd(d, negc_b, a_dd);
            let combined = rmul(d, inv_det, combined_inner);
            let distrib_fwd = d.lemma(p.left_distrib, &[inv_det, negc_b, a_dd]);
            let step3 = rsymm(d, combined, mid2, distrib_fwd);

            // (-c)*b + a*d -> -(c*b) + a*d -> c*(-b) + a*d -> c*(-b) + d*a.
            let cb = rmul(d, c, b);
            let neg_cb = rneg(d, cb);
            let neg_mul_pf = d.lemma(p.neg_mul, &[c, b]); // (-c)*b = -(c*b)
            let inner_step1 = rcongr(d, negc_b, neg_cb, neg_mul_pf, &|d, t| radd(d, t, a_dd));
            let inner_mid1 = radd(d, neg_cb, a_dd);

            let neg_b = rneg(d, b);
            let c_negb = rmul(d, c, neg_b);
            let mul_neg_pf = d.lemma(p.mul_neg, &[c, b]); // c*(-b) = -(c*b)
            let neg_cb_to_cnegb = rsymm(d, c_negb, neg_cb, mul_neg_pf); // -(c*b) = c*(-b)
            let inner_step2 = rcongr(d, neg_cb, c_negb, neg_cb_to_cnegb, &|d, t| radd(d, t, a_dd));
            let inner_mid2 = radd(d, c_negb, a_dd);

            let ad_comm = d.lemma(p.mul_comm, &[a, dd]); // a*d = d*a
            let d_a = rmul(d, dd, a);
            let inner_step3 = rcongr(d, a_dd, d_a, ad_comm, &|d, t| radd(d, c_negb, t));
            let inner_target = radd(d, c_negb, d_a);

            let (_, inner_proof) = rchain(
                d,
                combined_inner,
                &[
                    (inner_mid1, inner_step1),
                    (inner_mid2, inner_step2),
                    (inner_target, inner_step3),
                ],
            );

            let step4 = rcongr(d, combined_inner, inner_target, inner_proof, &|d, t| {
                rmul(d, inv_det, t)
            });
            let mid4 = rmul(d, inv_det, inner_target);

            let adj_pf = d.lemma(p.mul_adj2_bottom_right, &[a, b, c, dd]); // c*(-b) + d*a = det2 a b c d
            let step5 = rcongr(d, inner_target, det, adj_pf, &|d, t| rmul(d, inv_det, t));
            let mid5 = rmul(d, inv_det, det);

            let one = rone(d, p);
            let cancel = inv_det2_cancel(d, p, det, inv_det, h);

            let (_, proof) = rchain(
                d,
                start,
                &[
                    (mid1, step1),
                    (mid2, step2),
                    (combined, step3),
                    (mid4, step4),
                    (mid5, step5),
                    (one, cancel),
                ],
            );
            proof
        },
    )
}

// --- Cramer's rule for a 2×2 system -----------------------------------------
//
// `a·x + b·y = u`, `c·x + d·y = v`, `det2 a b c d ≠ 0`. Only the FORWARD
// direction is proved — a solution must have this form — hence
// `cramer_two_unique_*`, never a bare `cramer_two_*`: existence (that the
// displayed `x` and `y` together actually solve the system) is a different,
// unattempted argument.
//
// Each unknown's proof factors through an unconditional algebraic identity
// (`cramer_col1_identity`/`cramer_col2_identity`, no hypothesis at all —
// substituting the system's LHS expressions for one column of `A` scales the
// determinant by that unknown) via the same `sub_add_add`-then-two-brackets
// route [`declare_det2_row_add`] uses: one bracket collapses to `0` by
// `mul_assoc`/`mul_comm`/`add_neg`, the other folds into `det2 a b c d *
// (unknown)` by `mul_assoc`/`mul_comm`/`sub_mul` (`sub_mul`'s right-scalar
// form, where [`declare_det2_scale_row`] needed the left-scalar
// `left_distrib` route instead).

/// `det2 (a*x+b*y) b (c*x+d*y) d = (det2 a b c d) * x` — unconditional, no
/// hypothesis. Substituting the system's LHS expressions for column 1 of `A`
/// scales the determinant by `x`.
#[allow(clippy::too_many_arguments)]
fn cramer_col1_identity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let ax = rmul(d, a, x);
    let by = rmul(d, b, y);
    let cx = rmul(d, c, x);
    let dy = rmul(d, dd, y);
    let u = radd(d, ax, by);
    let v = radd(d, cx, dy);

    let term_ud = rmul(d, u, dd);
    let term_bv = rmul(d, b, v);
    let start = diff(d, term_ud, term_bv); // = det2 u b v d (defeq)

    let ax_dd = rmul(d, ax, dd);
    let by_dd = rmul(d, by, dd);
    let u_expanded = radd(d, ax_dd, by_dd);
    let expand_u = d.lemma(p.right_distrib, &[ax, by, dd]); // (ax+by)*d = ax*d+by*d
    let step1 = rcongr(d, term_ud, u_expanded, expand_u, &|d, t| {
        diff(d, t, term_bv)
    });
    let mid1 = diff(d, u_expanded, term_bv);

    let b_cx = rmul(d, b, cx);
    let b_dy = rmul(d, b, dy);
    let v_expanded = radd(d, b_cx, b_dy);
    let expand_v = d.lemma(p.left_distrib, &[b, cx, dy]); // b*(cx+dy) = b*cx+b*dy
    let step2 = rcongr(d, term_bv, v_expanded, expand_v, &|d, t| {
        diff(d, u_expanded, t)
    });
    let mid2 = diff(d, u_expanded, v_expanded);

    let split = d.lemma(p.sub_add_add, &[ax_dd, by_dd, b_cx, b_dy]);
    let bracket1 = diff(d, ax_dd, b_cx);
    let bracket2 = diff(d, by_dd, b_dy);
    let split_target = radd(d, bracket1, bracket2);

    // bracket1: (a*x)*d - b*(c*x) -> (a*d)*x - (b*c)*x -> ((a*d)-(b*c))*x = D*x.
    let a_dd = rmul(d, a, dd);
    let b_c = rmul(d, b, c);
    let a_dd_x = rmul(d, a_dd, x);
    let b_c_x = rmul(d, b_c, x);

    let assoc1 = d.lemma(p.mul_assoc, &[a, x, dd]); // (a*x)*d = a*(x*d)
    let x_dd = rmul(d, x, dd);
    let a_xdd = rmul(d, a, x_dd);
    let comm1 = d.lemma(p.mul_comm, &[x, dd]); // x*d = d*x
    let dd_x = rmul(d, dd, x);
    let a_ddx = rmul(d, a, dd_x);
    let cg1 = rcongr(d, x_dd, dd_x, comm1, &|d, t| rmul(d, a, t));
    let (_, lhs_to_a_ddx) = rchain(d, ax_dd, &[(a_xdd, assoc1), (a_ddx, cg1)]);
    let assoc1b = d.lemma(p.mul_assoc, &[a, dd, x]); // (a*d)*x = a*(d*x)
    let a_ddx_to_a_dd_x = rsymm(d, a_dd_x, a_ddx, assoc1b); // a*(d*x) = (a*d)*x
    let bracket1_lhs = rtrans(d, ax_dd, a_ddx, a_dd_x, lhs_to_a_ddx, a_ddx_to_a_dd_x);

    let assoc2 = d.lemma(p.mul_assoc, &[b, c, x]); // (b*c)*x = b*(c*x)
    let bracket1_rhs = rsymm(d, b_c_x, b_cx, assoc2); // b*(c*x) = (b*c)*x

    let step_b1a = rcongr(d, ax_dd, a_dd_x, bracket1_lhs, &|d, t| {
        let n = rneg(d, b_cx);
        radd(d, t, n)
    });
    let mid_b1a = diff(d, a_dd_x, b_cx);
    let step_b1b = rcongr(d, b_cx, b_c_x, bracket1_rhs, &|d, t| {
        let n = rneg(d, t);
        radd(d, a_dd_x, n)
    });
    let mid_b1b = diff(d, a_dd_x, b_c_x);

    let sub_mul_pf = d.lemma(p.sub_mul, &[a_dd, b_c, x]); // (a_dd*x)-(b_c*x) = (a_dd-b_c)*x
    let det = rdet2(d, p, a, b, c, dd);
    let det_x = rmul(d, det, x); // = (a_dd-b_c)*x (defeq)

    let (_, bracket1_proof) = rchain(
        d,
        bracket1,
        &[
            (mid_b1a, step_b1a),
            (mid_b1b, step_b1b),
            (det_x, sub_mul_pf),
        ],
    );

    // bracket2: (b*y)*d - b*(d*y) -> b*(d*y) - b*(d*y) -> 0.
    let assoc3 = d.lemma(p.mul_assoc, &[b, y, dd]); // (b*y)*d = b*(y*d)
    let y_dd = rmul(d, y, dd);
    let b_ydd = rmul(d, b, y_dd);
    let comm2 = d.lemma(p.mul_comm, &[y, dd]); // y*d = d*y
    let cg2 = rcongr(d, y_dd, dy, comm2, &|d, t| rmul(d, b, t));
    let (_, bracket2_lhs) = rchain(d, by_dd, &[(b_ydd, assoc3), (b_dy, cg2)]);

    let step_b2 = rcongr(d, by_dd, b_dy, bracket2_lhs, &|d, t| {
        let n = rneg(d, b_dy);
        radd(d, t, n)
    });
    let mid_b2 = diff(d, b_dy, b_dy);
    let zero = rzero(d, p);
    let vanish2 = d.lemma(p.add_neg, &[b_dy]); // b*(d*y) + -(b*(d*y)) = 0

    let (_, bracket2_proof) = rchain(d, bracket2, &[(mid_b2, step_b2), (zero, vanish2)]);

    let step3 = rcongr(d, bracket1, det_x, bracket1_proof, &|d, t| {
        radd(d, t, bracket2)
    });
    let mid3 = radd(d, det_x, bracket2);
    let step4 = rcongr(d, bracket2, zero, bracket2_proof, &|d, t| radd(d, det_x, t));
    let mid4 = radd(d, det_x, zero);
    let az = d.lemma(p.add_zero, &[det_x]); // D*x + 0 = D*x

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (split_target, split),
            (mid3, step3),
            (mid4, step4),
            (det_x, az),
        ],
    );
    proof
}

/// `det2 a (a*x+b*y) c (c*x+d*y) = (det2 a b c d) * y` — unconditional, no
/// hypothesis. Substituting the system's LHS expressions for column 2 of `A`
/// scales the determinant by `y`.
#[allow(clippy::too_many_arguments)]
fn cramer_col2_identity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let ax = rmul(d, a, x);
    let by = rmul(d, b, y);
    let cx = rmul(d, c, x);
    let dy = rmul(d, dd, y);
    let u = radd(d, ax, by);
    let v = radd(d, cx, dy);

    let term_av = rmul(d, a, v);
    let term_uc = rmul(d, u, c);
    let start = diff(d, term_av, term_uc); // = det2 a u c v (defeq)

    let a_cx = rmul(d, a, cx);
    let a_dy = rmul(d, a, dy);
    let v_expanded = radd(d, a_cx, a_dy);
    let expand_v = d.lemma(p.left_distrib, &[a, cx, dy]); // a*(cx+dy) = a*cx+a*dy
    let step1 = rcongr(d, term_av, v_expanded, expand_v, &|d, t| {
        diff(d, t, term_uc)
    });
    let mid1 = diff(d, v_expanded, term_uc);

    let ax_c = rmul(d, ax, c);
    let by_c = rmul(d, by, c);
    let u_expanded = radd(d, ax_c, by_c);
    let expand_u = d.lemma(p.right_distrib, &[ax, by, c]); // (ax+by)*c = ax*c+by*c
    let step2 = rcongr(d, term_uc, u_expanded, expand_u, &|d, t| {
        diff(d, v_expanded, t)
    });
    let mid2 = diff(d, v_expanded, u_expanded);

    let split = d.lemma(p.sub_add_add, &[a_cx, a_dy, ax_c, by_c]);
    let bracket1 = diff(d, a_cx, ax_c);
    let bracket2 = diff(d, a_dy, by_c);
    let split_target = radd(d, bracket1, bracket2);

    // bracket1: a*(c*x) - (a*x)*c -> a*(c*x) - a*(c*x) -> 0.
    let assoc1 = d.lemma(p.mul_assoc, &[a, x, c]); // (a*x)*c = a*(x*c)
    let x_c = rmul(d, x, c);
    let a_xc = rmul(d, a, x_c);
    let comm1 = d.lemma(p.mul_comm, &[x, c]); // x*c = c*x
    let cg1 = rcongr(d, x_c, cx, comm1, &|d, t| rmul(d, a, t));
    let (_, bracket1_rhs) = rchain(d, ax_c, &[(a_xc, assoc1), (a_cx, cg1)]);

    let step_b1 = rcongr(d, ax_c, a_cx, bracket1_rhs, &|d, t| {
        let n = rneg(d, t);
        radd(d, a_cx, n)
    });
    let mid_b1 = diff(d, a_cx, a_cx);
    let zero = rzero(d, p);
    let vanish1 = d.lemma(p.add_neg, &[a_cx]); // a*(c*x) + -(a*(c*x)) = 0

    let (_, bracket1_proof) = rchain(d, bracket1, &[(mid_b1, step_b1), (zero, vanish1)]);

    // bracket2: a*(d*y) - (b*y)*c -> (a*d)*y - (b*c)*y -> ((a*d)-(b*c))*y = D*y.
    let a_dd = rmul(d, a, dd);
    let b_c = rmul(d, b, c);
    let a_dd_y = rmul(d, a_dd, y);
    let b_c_y = rmul(d, b_c, y);

    let assoc2 = d.lemma(p.mul_assoc, &[a, dd, y]); // (a*d)*y = a*(d*y)
    let a_dy_to_a_dd_y = rsymm(d, a_dd_y, a_dy, assoc2); // a*(d*y) = (a*d)*y

    let assoc3 = d.lemma(p.mul_assoc, &[b, y, c]); // (b*y)*c = b*(y*c)
    let y_c = rmul(d, y, c);
    let b_yc = rmul(d, b, y_c);
    let comm2 = d.lemma(p.mul_comm, &[y, c]); // y*c = c*y
    let c_y = rmul(d, c, y);
    let b_cy = rmul(d, b, c_y);
    let cg2 = rcongr(d, y_c, c_y, comm2, &|d, t| rmul(d, b, t));
    let (_, byc_to_b_cy) = rchain(d, by_c, &[(b_yc, assoc3), (b_cy, cg2)]);
    let assoc3b = d.lemma(p.mul_assoc, &[b, c, y]); // (b*c)*y = b*(c*y)
    let b_cy_to_b_c_y = rsymm(d, b_c_y, b_cy, assoc3b); // b*(c*y) = (b*c)*y
    let bracket2_rhs = rtrans(d, by_c, b_cy, b_c_y, byc_to_b_cy, b_cy_to_b_c_y);

    let step_b2a = rcongr(d, a_dy, a_dd_y, a_dy_to_a_dd_y, &|d, t| {
        let n = rneg(d, by_c);
        radd(d, t, n)
    });
    let mid_b2a = diff(d, a_dd_y, by_c);
    let step_b2b = rcongr(d, by_c, b_c_y, bracket2_rhs, &|d, t| {
        let n = rneg(d, t);
        radd(d, a_dd_y, n)
    });
    let mid_b2b = diff(d, a_dd_y, b_c_y);

    let sub_mul_pf = d.lemma(p.sub_mul, &[a_dd, b_c, y]); // (a_dd*y)-(b_c*y) = (a_dd-b_c)*y
    let det = rdet2(d, p, a, b, c, dd);
    let det_y = rmul(d, det, y); // = (a_dd-b_c)*y (defeq)

    let (_, bracket2_proof) = rchain(
        d,
        bracket2,
        &[
            (mid_b2a, step_b2a),
            (mid_b2b, step_b2b),
            (det_y, sub_mul_pf),
        ],
    );

    let step3 = rcongr(d, bracket1, zero, bracket1_proof, &|d, t| {
        radd(d, t, bracket2)
    });
    let mid3 = radd(d, zero, bracket2);
    let step4 = rcongr(d, bracket2, det_y, bracket2_proof, &|d, t| radd(d, zero, t));
    let mid4 = radd(d, zero, det_y);
    let za = d.lemma(p.zero_add, &[det_y]); // 0 + D*y = D*y

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (split_target, split),
            (mid3, step3),
            (mid4, step4),
            (det_y, za),
        ],
    );
    proof
}

/// Admit `Rat.cramer_two_unique_x` and `Rat.cramer_two_unique_y`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_cramer(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_cramer_two_unique_x(d, p)?;
    declare_cramer_two_unique_y(d, p)
}

/// Solve `M = D*w` for `w`, given `h3 : D ≠ 0`, producing a proof of
/// `Eq (Rat.mul m inv_det) w` — which is defeq to `Eq (Rat.div m det) w`, so
/// [`rsymm`]-ing the result closes a goal `w = Rat.div m det`.
///
/// `m_is_det_w : m = D*w`. Chain: `m*invD = (D*w)*invD = D*(w*invD) =
/// D*(invD*w) = (D*invD)*w = 1*w = w`.
#[allow(clippy::too_many_arguments)]
fn cramer_solve(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    det: ExprId,
    inv_det: ExprId,
    w: ExprId,
    m: ExprId,
    m_is_det_w: ExprId,
    h3: ExprId,
) -> ExprId {
    let det_w = rmul(d, det, w);
    let start = rmul(d, m, inv_det);
    let step1 = rcongr(d, m, det_w, m_is_det_w, &|d, t| rmul(d, t, inv_det));
    let mid1 = rmul(d, det_w, inv_det);

    let assoc1 = d.lemma(p.mul_assoc, &[det, w, inv_det]); // (D*w)*invD = D*(w*invD)
    let w_inv_det = rmul(d, w, inv_det);
    let mid2 = rmul(d, det, w_inv_det);

    let comm1 = d.lemma(p.mul_comm, &[w, inv_det]); // w*invD = invD*w
    let inv_det_w = rmul(d, inv_det, w);
    let step3 = rcongr(d, w_inv_det, inv_det_w, comm1, &|d, t| rmul(d, det, t));
    let mid3 = rmul(d, det, inv_det_w);

    let det_inv_det_w = rmul(d, det, inv_det); // = D*invD (the argument sub_mul'd against w below)
    let mid4 = rmul(d, det_inv_det_w, w); // (D*invD)*w
    let assoc2 = d.lemma(p.mul_assoc, &[det, inv_det, w]); // (D*invD)*w = D*(invD*w)
    let mid3_to_mid4 = rsymm(d, mid4, mid3, assoc2); // D*(invD*w) = (D*invD)*w

    let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[det, h3]); // D*invD = 1
    let one = rone(d, p);
    let step5 = rcongr(d, det_inv_det_w, one, cancel, &|d, t| rmul(d, t, w));
    let mid5 = rmul(d, one, w);

    let comm2 = d.lemma(p.mul_comm, &[one, w]); // 1*w = w*1
    let w1 = rmul(d, w, one);
    let step6 = comm2;
    let mul_one_pf = d.lemma(p.mul_one, &[w]); // w*1 = w

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, assoc1),
            (mid3, step3),
            (mid4, mid3_to_mid4),
            (mid5, step5),
            (w1, step6),
            (w, mul_one_pf),
        ],
    );
    proof
}

/// `Rat.cramer_two_unique_x : ∀ a b c d x y u v,`
/// `  a*x+b*y = u → c*x+d*y = v → det2 a b c d ≠ 0 →`
/// `  x = Rat.div (det2 u b v d) (det2 a b c d)`.
///
/// The **forward** direction only — a solution of the system must have this
/// form. Existence is a different, unattempted argument, hence
/// `cramer_two_unique_x` rather than a bare `cramer_two_x`.
fn declare_cramer_two_unique_x(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (a, b, c, dd, x, y, u, v) = (
        vars[0], vars[1], vars[2], vars[3], vars[4], vars[5], vars[6], vars[7],
    );

    let ax = rmul(d, a, x);
    let by = rmul(d, b, y);
    let axby = radd(d, ax, by);
    let h1_ty = req(d, axby, u);
    let cx = rmul(d, c, x);
    let dy = rmul(d, dd, y);
    let cxdy = radd(d, cx, dy);
    let h2_ty = req(d, cxdy, v);
    let h3_ty = det2_ne_zero(d, p, a, b, c, dd);

    let det = rdet2(d, p, a, b, c, dd);
    let m = rdet2(d, p, u, b, v, dd);
    let inv_det = d.const_app(p.inv, &[det]);
    let div_m_det = d.const_app(p.div, &[m, det]);
    let concl_ty = req(d, x, div_m_det);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let body = {
        let identity = cramer_col1_identity(d, p, a, b, c, dd, x, y); // det2 axby b cxdy d = D*x
        let det_x = rmul(d, det, x);
        let start = rdet2(d, p, axby, b, cxdy, dd);

        let m_partial = rdet2(d, p, u, b, cxdy, dd);
        let rewrite1 = rcongr(d, axby, u, h1, &|d, t| rdet2(d, p, t, b, cxdy, dd));
        let rewrite2 = rcongr(d, cxdy, v, h2, &|d, t| rdet2(d, p, u, b, t, dd));
        let (_, start_is_m) = rchain(d, start, &[(m_partial, rewrite1), (m, rewrite2)]);

        let m_is_start = rsymm(d, start, m, start_is_m);
        let m_is_det_x = rtrans(d, m, start, det_x, m_is_start, identity);

        cramer_solve(d, p, det, inv_det, x, m, m_is_det_x, h3)
    };
    let final_body = rsymm(d, div_m_det, x, body); // Eq div_m_det x -> Eq x div_m_det

    let with_h3 = d.lam_fv(h3_fv, h3_ty, final_body);
    let with_h2 = d.lam_fv(h2_fv, h2_ty, with_h3);
    let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);

    let inner_h3 = d.arrow(h3_ty, concl_ty);
    let inner_h2 = d.arrow(h2_ty, inner_h3);
    let mut ty = d.arrow(h1_ty, inner_h2);
    let mut value = with_h1;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, carrier, ty);
        value = d.lam_fv(fv, carrier, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cramer_two_unique_x,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.cramer_two_unique_y : ∀ a b c d x y u v,`
/// `  a*x+b*y = u → c*x+d*y = v → det2 a b c d ≠ 0 →`
/// `  y = Rat.div (det2 a u c v) (det2 a b c d)`.
///
/// The **forward** direction only — see [`declare_cramer_two_unique_x`].
fn declare_cramer_two_unique_y(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (a, b, c, dd, x, y, u, v) = (
        vars[0], vars[1], vars[2], vars[3], vars[4], vars[5], vars[6], vars[7],
    );

    let ax = rmul(d, a, x);
    let by = rmul(d, b, y);
    let axby = radd(d, ax, by);
    let h1_ty = req(d, axby, u);
    let cx = rmul(d, c, x);
    let dy = rmul(d, dd, y);
    let cxdy = radd(d, cx, dy);
    let h2_ty = req(d, cxdy, v);
    let h3_ty = det2_ne_zero(d, p, a, b, c, dd);

    let det = rdet2(d, p, a, b, c, dd);
    let m = rdet2(d, p, a, u, c, v);
    let inv_det = d.const_app(p.inv, &[det]);
    let div_m_det = d.const_app(p.div, &[m, det]);
    let concl_ty = req(d, y, div_m_det);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let body = {
        let identity = cramer_col2_identity(d, p, a, b, c, dd, x, y); // det2 a axby c cxdy = D*y
        let det_y = rmul(d, det, y);
        let start = rdet2(d, p, a, axby, c, cxdy);

        let m_partial = rdet2(d, p, a, u, c, cxdy);
        let rewrite1 = rcongr(d, axby, u, h1, &|d, t| rdet2(d, p, a, t, c, cxdy));
        let rewrite2 = rcongr(d, cxdy, v, h2, &|d, t| rdet2(d, p, a, u, c, t));
        let (_, start_is_m) = rchain(d, start, &[(m_partial, rewrite1), (m, rewrite2)]);

        let m_is_start = rsymm(d, start, m, start_is_m);
        let m_is_det_y = rtrans(d, m, start, det_y, m_is_start, identity);

        cramer_solve(d, p, det, inv_det, y, m, m_is_det_y, h3)
    };
    let final_body = rsymm(d, div_m_det, y, body);

    let with_h3 = d.lam_fv(h3_fv, h3_ty, final_body);
    let with_h2 = d.lam_fv(h2_fv, h2_ty, with_h3);
    let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);

    let inner_h3 = d.arrow(h3_ty, concl_ty);
    let inner_h2 = d.arrow(h2_ty, inner_h3);
    let mut ty = d.arrow(h1_ty, inner_h2);
    let mut value = with_h1;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, carrier, ty);
        value = d.lam_fv(fv, carrier, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cramer_two_unique_y,
        uparams: vec![],
        ty,
        value,
    })
}
