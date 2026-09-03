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
    den, mk, num, radd, rat_theorem, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rrefl, rsymm,
    rtrans, rzero,
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

/// Delta height for `Rat.det3`: one above [`DET2_HEIGHT`], following this
/// file's convention of a monotone bump per new definition (`CRAMER2_HEIGHT`,
/// `OF_INT_HEIGHT` below do the same). `Rat.det3` does not call `Rat.det2` in
/// its own value (see [`declare_det3_def`]'s doc comment for why), so it only
/// needs to sit above `Rat.sub`/`Rat.mul` the way [`DET2_HEIGHT`] does — this
/// keeps the numbering linear rather than because of a real dependency.
const DET3_HEIGHT: u16 = DET2_HEIGHT + 1;

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
    declare_det2_eq_zero_of_lin_dep(d, p)?;
    declare_adjugate(d, p)?;
    declare_inverse(d, p)?;
    declare_cramer(d, p)?;
    declare_cramer2(d, p)?;
    declare_of_int_def(d, p)?;
    declare_of_int_add(d, p)?;
    declare_of_int_mul(d, p)?;
    declare_of_int_neg(d, p)?;
    declare_det2_fib(d, p)?;
    declare_det3_def(d, p)?;
    declare_det3_id(d, p)?;
    declare_det3_cofactor_row1(d, p)?;
    declare_det3_scale_row(d, p)?;
    declare_det3_ofint(d, p)?;
    declare_det3_example_generic(d, p)?;
    declare_det3_example_diagonal(d, p)?;
    declare_det3_example_singular(d, p)
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
pub(super) fn rdet2(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    w: ExprId,
) -> ExprId {
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
/// `w*(x*y) = x*(w*y)`, by `ring::rat::prove_eq_at` (ring-tactic-2,
/// ADR-1582) rather than the hand `mul_assoc`/`mul_comm` chain this file
/// used to carry — this identity in particular needs the ring producer's
/// intra-monomial factor sorting (`sort_factors`): both sides normalize to
/// the same three-factor monomial only once its factor list is sorted.
fn middle_swap(d: &mut IntDev<'_>, p: RatPrelude, w: ExprId, x: ExprId, y: ExprId) -> ExprId {
    crate::ring::rat::prove_eq_at(d, &p, &[w, x, y], &|d, v| {
        let (w, x, y) = (v[0], v[1], v[2]);
        let xy = rmul(d, x, y);
        let lhs = rmul(d, w, xy);
        let wy = rmul(d, w, y);
        let rhs = rmul(d, x, wy);
        (lhs, rhs)
    })
    .expect("middle_swap: w*(x*y) = x*(w*y) is a ring identity")
}

/// `(k*x) - (k*y) = k*(x - y)`, by `ring::rat::prove_eq_at` (ring-tactic-2,
/// ADR-1582) rather than the hand `left_distrib`/`mul_neg` chain this file
/// used to carry.
fn mul_sub_right_rev(d: &mut IntDev<'_>, p: RatPrelude, k: ExprId, x: ExprId, y: ExprId) -> ExprId {
    crate::ring::rat::prove_eq_at(d, &p, &[k, x, y], &|d, v| {
        let (k, x, y) = (v[0], v[1], v[2]);
        let kx = rmul(d, k, x);
        let ky = rmul(d, k, y);
        let neg_ky = rneg(d, ky);
        let lhs = radd(d, kx, neg_ky);
        let neg_y = rneg(d, y);
        let xy = radd(d, x, neg_y);
        let rhs = rmul(d, k, xy);
        (lhs, rhs)
    })
    .expect("mul_sub_right_rev: (k*x)-(k*y) = k*(x-y) is a ring identity")
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

// --- linear dependence: the singular case of a 2x2 system ------------------
//
// `Rat.det2_eq_zero_of_lin_dep` is the first statement in this kernel about
// linear DEPENDENCE rather than about solving. With no `List`/`Finset`/
// product type, "the rows are proportional" cannot be an existential over a
// vector or a pair — it is stated the way linear dependence is actually
// defined: a nontrivial scalar combination of the rows that vanishes.
//
// The naive `∃ t, c = t·a ∧ d = t·b` is FALSE at `a = b = 0` with `(c,d)`
// nonzero — no `t` scales `(0,0)` to a nonzero `(c,d)` — even though `det2`
// is then always `0`. So the statement here is the symmetric one, with no
// degenerate case:
//
//   `∃ s t, (s ≠ 0 ∨ t ≠ 0) ∧ s·a + t·c = 0 ∧ s·b + t·d = 0`
//
// encoded as three explicit hypotheses (`Or`/`Eq`/`Eq`) rather than a bundled
// `∃`, matching every other `_of_ne_zero`-style theorem in this file.

/// `s·a = neg (t·c)`, given `h : s·a + t·c = 0` — `add_comm` to read the sum
/// the other way round, then `neg_eq_of_add_eq_zero`.
fn cross_solve(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    s: ExprId,
    a: ExprId,
    t: ExprId,
    c: ExprId,
    h: ExprId, // s*a + t*c = 0
) -> ExprId {
    let sa = rmul(d, s, a);
    let tc = rmul(d, t, c);
    let zero = rzero(d, p);
    let sa_tc = radd(d, sa, tc);
    let tc_sa = radd(d, tc, sa);

    let comm = d.lemma(p.add_comm, &[sa, tc]); // sa+tc = tc+sa
    let comm_rev = rsymm(d, sa_tc, tc_sa, comm); // tc+sa = sa+tc
    let tc_sa_zero = rtrans(d, tc_sa, sa_tc, zero, comm_rev, h); // tc+sa=0

    let neg_tc_eq_sa = d.lemma(p.neg_eq_of_add_eq_zero, &[tc, sa, tc_sa_zero]); // neg(tc)=sa
    let neg_tc = rneg(d, tc);
    rsymm(d, neg_tc, sa, neg_tc_eq_sa) // sa = neg(tc)
}

/// `(s·a)·m = neg (t·(c·m))`, given `h_a : s·a = neg (t·c)`.
///
/// The one algebraic step [`declare_det2_eq_zero_of_lin_dep`] repeats at four
/// different `m`: substitute the negated cross term (`neg_mul`), then pull
/// `t` back out of `(t·c)·m` by `mul_assoc`.
fn cross_scaled(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    s: ExprId,
    a: ExprId,
    t: ExprId,
    c: ExprId,
    h_a: ExprId, // s*a = neg(t*c)
    m: ExprId,
) -> ExprId {
    let sa = rmul(d, s, a);
    let tc = rmul(d, t, c);
    let neg_tc = rneg(d, tc);
    let sam = rmul(d, sa, m);

    let step1 = rcongr(d, sa, neg_tc, h_a, &|d, w| rmul(d, w, m)); // sa*m = neg(tc)*m
    let neg_tc_m = rmul(d, neg_tc, m);

    let step2 = d.lemma(p.neg_mul, &[tc, m]); // neg(tc)*m = neg(tc*m)
    let tcm = rmul(d, tc, m);
    let neg_tcm = rneg(d, tcm);

    let assoc = d.lemma(p.mul_assoc, &[t, c, m]); // (t*c)*m = t*(c*m)
    let cm = rmul(d, c, m);
    let t_cm = rmul(d, t, cm);
    let step3 = rcongr(d, tcm, t_cm, assoc, &|d, w| rneg(d, w)); // neg(tcm) = neg(t*(c*m))
    let neg_t_cm = rneg(d, t_cm);

    let (_, proof) = rchain(
        d,
        sam,
        &[(neg_tc_m, step1), (neg_tcm, step2), (neg_t_cm, step3)],
    );
    proof
}

/// `det2 a b c d = 0`, given `ad_eq_bc : a·d = b·c`.
pub(super) fn det2_zero_of_ad_eq_bc(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    ad_eq_bc: ExprId,
) -> ExprId {
    let ad = rmul(d, a, dd);
    let bc = rmul(d, b, c);
    let neg_bc = rneg(d, bc);
    let start = radd(d, ad, neg_bc); // = det2 a b c d (defeq)

    let step = rcongr(d, ad, bc, ad_eq_bc, &|d, w| {
        let n = rneg(d, bc);
        radd(d, w, n)
    });
    let mid = radd(d, bc, neg_bc);
    let zero = rzero(d, p);
    let vanish = d.lemma(p.add_neg, &[bc]); // bc + neg(bc) = 0

    let (_, proof) = rchain(d, start, &[(mid, step), (zero, vanish)]);
    proof
}

/// `Rat.det2_eq_zero_of_lin_dep : ∀ a b c d s t,`
/// `  Or (Not (s=0)) (Not (t=0)) → s·a+t·c=0 → s·b+t·d=0 → det2 a b c d = 0`.
///
/// The **easy direction** of "`det2 = 0` iff the rows are linearly
/// dependent": a nontrivial vanishing combination of the rows forces the
/// determinant to vanish. Pure algebra, plus one `Or`-elimination on the
/// nontriviality hypothesis itself (a value already in hand, not a decision
/// procedure run on `a,b,c,d,s,t`).
///
/// [`cross_solve`] turns the two hypotheses into `s·a = neg(t·c)` and
/// `s·b = neg(t·d)`. [`cross_scaled`] at `m := d` and `m := c` combines them
/// (through `t·(c·d) = t·(d·c)`) into `(s·a)·d = (s·b)·c`, hence
/// `s·(a·d) = s·(b·c)`; at `m := b` and `m := a` it combines them (through a
/// double-negation cancellation, since that route lands on `neg = neg`
/// rather than on the values directly) into `t·(a·d) = t·(b·c)`. Whichever of
/// `s,t` the hypothesis names nonzero cancels its equation
/// ([`RatPrelude::mul_left_cancel_of_ne_zero`]) down to `a·d = b·c`, and
/// [`det2_zero_of_ad_eq_bc`] finishes both branches identically.
fn declare_det2_eq_zero_of_lin_dep(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let zero = rzero(d, p);
    let s_eq_zero = req(d, s, zero);
    let s_ne_zero = d.not(s_eq_zero);
    let t_eq_zero = req(d, t, zero);
    let t_ne_zero = d.not(t_eq_zero);
    let nontrivial = d.or(s_ne_zero, t_ne_zero);
    let nt_fv = d.fresh_fvar();
    let nt = d.kernel().fvar(nt_fv);

    let sa = rmul(d, s, a);
    let tc = rmul(d, t, c);
    let sa_tc = radd(d, sa, tc);
    let eq1_ty = req(d, sa_tc, zero);
    let eq1_fv = d.fresh_fvar();
    let eq1 = d.kernel().fvar(eq1_fv);

    let sb = rmul(d, s, b);
    let td = rmul(d, t, dd);
    let sb_td = radd(d, sb, td);
    let eq2_ty = req(d, sb_td, zero);
    let eq2_fv = d.fresh_fvar();
    let eq2 = d.kernel().fvar(eq2_fv);

    let det = rdet2(d, p, a, b, c, dd);
    let concl = req(d, det, zero);

    let body = {
        let h_a = cross_solve(d, p, s, a, t, c, eq1); // s*a = neg(t*c)
        let h_b = cross_solve(d, p, s, b, t, dd, eq2); // s*b = neg(t*d)

        let a_dd = rmul(d, a, dd);
        let b_c = rmul(d, b, c);

        // --- s*(a*d) = s*(b*c) --------------------------------------------
        let l1 = cross_scaled(d, p, s, a, t, c, h_a, dd); // (s*a)*d = neg(t*(c*d))
        let l2 = cross_scaled(d, p, s, b, t, dd, h_b, c); // (s*b)*c = neg(t*(d*c))

        let cd = rmul(d, c, dd);
        let dc = rmul(d, dd, c);
        let t_cd = rmul(d, t, cd);
        let t_dc = rmul(d, t, dc);
        let comm_cd = d.lemma(p.mul_comm, &[c, dd]); // c*d = d*c
        let m_d = rcongr(d, cd, dc, comm_cd, &|d, w| rmul(d, t, w)); // t*(c*d)=t*(d*c)
        let neg_t_cd = rneg(d, t_cd);
        let neg_t_dc = rneg(d, t_dc);
        let neg_m_d = rcongr(d, t_cd, t_dc, m_d, &|d, w| rneg(d, w));

        let sa_dd = rmul(d, sa, dd);
        let sb_c = rmul(d, sb, c);
        let l2_rev = rsymm(d, sb_c, neg_t_dc, l2); // neg(t*(d*c)) = (s*b)*c
        let (_, k0) = rchain(
            d,
            sa_dd,
            &[(neg_t_cd, l1), (neg_t_dc, neg_m_d), (sb_c, l2_rev)],
        );
        // k0 : (s*a)*d = (s*b)*c

        let s_add = rmul(d, s, a_dd);
        let s_bc = rmul(d, s, b_c);
        let assoc_s1 = d.lemma(p.mul_assoc, &[s, a, dd]); // (s*a)*d = s*(a*d)
        let assoc_s2 = d.lemma(p.mul_assoc, &[s, b, c]); // (s*b)*c = s*(b*c)
        let un_assoc_s1 = rsymm(d, sa_dd, s_add, assoc_s1); // s*(a*d) = (s*a)*d
        let (_, k) = rchain(
            d,
            s_add,
            &[(sa_dd, un_assoc_s1), (sb_c, k0), (s_bc, assoc_s2)],
        );
        // k : s*(a*d) = s*(b*c)

        // --- t*(a*d) = t*(b*c) --------------------------------------------
        let n1 = cross_scaled(d, p, s, a, t, c, h_a, b); // (s*a)*b = neg(t*(c*b))
        let n2 = cross_scaled(d, p, s, b, t, dd, h_b, a); // (s*b)*a = neg(t*(d*a))

        let sa_b = rmul(d, sa, b);
        let sb_a = rmul(d, sb, a);
        let assoc_n1 = d.lemma(p.mul_assoc, &[s, a, b]); // (s*a)*b = s*(a*b)
        let assoc_n2 = d.lemma(p.mul_assoc, &[s, b, a]); // (s*b)*a = s*(b*a)
        let ab = rmul(d, a, b);
        let ba = rmul(d, b, a);
        let comm_ab = d.lemma(p.mul_comm, &[a, b]); // a*b = b*a
        let s_ab = rmul(d, s, ab);
        let s_ba = rmul(d, s, ba);
        let congr_ab = rcongr(d, ab, ba, comm_ab, &|d, w| rmul(d, s, w)); // s*(a*b)=s*(b*a)
        let un_assoc_n2 = rsymm(d, sb_a, s_ba, assoc_n2); // s*(b*a) = (s*b)*a
        let (_, n0) = rchain(
            d,
            sa_b,
            &[(s_ab, assoc_n1), (s_ba, congr_ab), (sb_a, un_assoc_n2)],
        );
        // n0 : (s*a)*b = (s*b)*a

        let cb = rmul(d, c, b);
        let da = rmul(d, dd, a);
        let t_cb = rmul(d, t, cb);
        let t_da = rmul(d, t, da);
        let neg_t_cb = rneg(d, t_cb);
        let neg_t_da = rneg(d, t_da);
        let n1_rev = rsymm(d, sa_b, neg_t_cb, n1); // neg(t*(c*b)) = (s*a)*b
        let (_, neg_eq2) = rchain(d, neg_t_cb, &[(sa_b, n1_rev), (sb_a, n0), (neg_t_da, n2)]);
        // neg_eq2 : neg(t*(c*b)) = neg(t*(d*a))

        // neg_t_cb = neg(t_cb), neg_t_da = neg(t_da).
        let neg_neg_tcb_expr = rneg(d, neg_t_cb); // = neg(neg(t_cb))
        let neg_neg_tda_expr = rneg(d, neg_t_da); // = neg(neg(t_da))
        let neg_neg_tcb = d.lemma(p.neg_neg, &[t_cb]); // neg(neg(t_cb))=t_cb
        let tcb_eq_negneg = rsymm(d, neg_neg_tcb_expr, t_cb, neg_neg_tcb); // t_cb = neg(neg(t_cb))
        let negneg_eq = rcongr(d, neg_t_cb, neg_t_da, neg_eq2, &|d, w| rneg(d, w));
        let neg_neg_tda = d.lemma(p.neg_neg, &[t_da]); // neg(neg(t_da))=t_da
        let (_, t0) = rchain(
            d,
            t_cb,
            &[
                (neg_neg_tcb_expr, tcb_eq_negneg),
                (neg_neg_tda_expr, negneg_eq),
                (t_da, neg_neg_tda),
            ],
        );
        // t0 : t*(c*b) = t*(d*a)

        let comm_cb = d.lemma(p.mul_comm, &[c, b]); // c*b = b*c
        let cm2 = rcongr(d, cb, b_c, comm_cb, &|d, w| rmul(d, t, w)); // t*(c*b)=t*(b*c) i.e. t_cb = t_bc
        let comm_da = d.lemma(p.mul_comm, &[dd, a]); // d*a = a*d
        let cm1 = rcongr(d, da, a_dd, comm_da, &|d, w| rmul(d, t, w)); // t*(d*a)=t*(a*d) i.e. t_da = t_ad

        let t_bc = rmul(d, t, b_c);
        let t_ad = rmul(d, t, a_dd);
        let cm2_rev = rsymm(d, t_cb, t_bc, cm2); // t_bc = t_cb
        let (_, t_bc_eq_ad) = rchain(d, t_bc, &[(t_cb, cm2_rev), (t_da, t0), (t_ad, cm1)]);
        // t_bc_eq_ad : t*(b*c) = t*(a*d)
        let big_t = rsymm(d, t_bc, t_ad, t_bc_eq_ad); // t*(a*d) = t*(b*c)

        // --- case split on the nontriviality hypothesis ---------------------
        d.or_elim(
            s_ne_zero,
            t_ne_zero,
            concl,
            nt,
            &|d, hs| {
                let ad_eq_bc = d.lemma(p.mul_left_cancel_of_ne_zero, &[s, a_dd, b_c, hs, k]);
                det2_zero_of_ad_eq_bc(d, p, a, b, c, dd, ad_eq_bc)
            },
            &|d, ht| {
                let ad_eq_bc = d.lemma(p.mul_left_cancel_of_ne_zero, &[t, a_dd, b_c, ht, big_t]);
                det2_zero_of_ad_eq_bc(d, p, a, b, c, dd, ad_eq_bc)
            },
        )
    };

    let mut ty = concl;
    ty = d.arrow(eq2_ty, ty);
    ty = d.arrow(eq1_ty, ty);
    ty = d.arrow(nontrivial, ty);
    let mut value = body;
    value = d.lam_fv(eq2_fv, eq2_ty, value);
    value = d.lam_fv(eq1_fv, eq1_ty, value);
    value = d.lam_fv(nt_fv, nontrivial, value);

    let binders = [
        (a_fv, carrier),
        (b_fv, carrier),
        (c_fv, carrier),
        (dd_fv, carrier),
        (s_fv, carrier),
        (t_fv, carrier),
    ];
    for &(fv, vty) in binders.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }

    d.declare_theorem(p.det2_eq_zero_of_lin_dep, ty, value)
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

// --- Cramer's rule for a 2×2 system: the solution formulas, and that they
// --- actually solve the system -----------------------------------------------
//
// `cramer_two_unique_x`/`cramer_two_unique_y` above are the FORWARD direction
// only: *if* `(x, y)` solves the system, it must equal these formulas. That
// says nothing about whether the formulas solve anything — uniqueness and
// existence are different theorems. This section adds the formulas as
// unconditional VALUES (`Rat.cramer2_x`/`Rat.cramer2_y`, total because
// `Rat.inv` is total) and the SUBSTITUTION direction (`Rat.cramer2_solves`):
// plugged back in, they satisfy both equations, given `D ≠ 0`.

/// Delta height for `Rat.cramer2_x`/`Rat.cramer2_y`: above both `Rat.div`
/// (`DERIVED_HEIGHT + 1` in `defs.rs`) and `Rat.det2` ([`DET2_HEIGHT`]),
/// since each definition's body applies both directly.
const CRAMER2_HEIGHT: u16 = DET2_HEIGHT + 1;

/// `Rat.cramer2_x a b c d u v := Rat.div (det2 u b v d) (det2 a b c d)` —
/// Cramer's formula for `x`, the solution of `a·x+b·y=u, c·x+d·y=v` when
/// `det2 a b c d ≠ 0`. Defined **unconditionally**: `Rat.inv` is total
/// (`inv 0 = 0`), so the value needs no `D ≠ 0` hypothesis — that belongs on
/// the *theorem* about it ([`declare_cramer2_solves`]), not on the
/// definition. Six separate `Rat` arguments, not a matrix or a pair: this
/// kernel has no tuple/product type, hence the `_x`/`_y` split already
/// established by [`declare_cramer_two_unique_x`]/
/// [`declare_cramer_two_unique_y`].
fn declare_cramer2_x(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (a, b, c, dd, u, v) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);

    let m = rdet2(d, p, u, b, v, dd);
    let det = rdet2(d, p, a, b, c, dd);
    let body = d.const_app(p.div, &[m, det]);

    let value = {
        let mut val = body;
        for &fv in fvs.iter().rev() {
            val = d.lam_fv(fv, carrier, val);
        }
        val
    };
    let ty = {
        let mut t = carrier;
        for _ in 0..6 {
            t = d.arrow(carrier, t);
        }
        t
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cramer2_x,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(CRAMER2_HEIGHT),
    })
}

/// `Rat.cramer2_y a b c d u v := Rat.div (det2 a u c v) (det2 a b c d)` — the
/// `y` companion of [`declare_cramer2_x`].
fn declare_cramer2_y(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (a, b, c, dd, u, v) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);

    let m = rdet2(d, p, a, u, c, v);
    let det = rdet2(d, p, a, b, c, dd);
    let body = d.const_app(p.div, &[m, det]);

    let value = {
        let mut val = body;
        for &fv in fvs.iter().rev() {
            val = d.lam_fv(fv, carrier, val);
        }
        val
    };
    let ty = {
        let mut t = carrier;
        for _ in 0..6 {
            t = d.arrow(carrier, t);
        }
        t
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cramer2_y,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(CRAMER2_HEIGHT),
    })
}

/// `a·(det2 u b v d) + b·(det2 a u c v) = (det2 a b c d)·u` — unconditional,
/// no hypothesis. Half of "the Cramer values satisfy the system": scaling
/// `det2 u b v d` (`x`'s Cramer numerator) by `a` and `det2 a u c v` (`y`'s
/// Cramer numerator) by `b` and summing collapses to `D·u`. The cross terms
/// `a·(b·v)` and `b·(a·v)` are equal (`mul_comm`+`mul_assoc`) and telescope
/// away via `sub_add_sub`, leaving `a·(u·d) − b·(u·c) = D·u` by `sub_mul`.
#[allow(clippy::too_many_arguments)]
fn cramer_solves_eq1_identity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    u: ExprId,
    v: ExprId,
) -> ExprId {
    let u_dd = rmul(d, u, dd);
    let b_v = rmul(d, b, v);
    let mx = diff(d, u_dd, b_v); // = det2 u b v d (defeq)
    let a_v = rmul(d, a, v);
    let u_c = rmul(d, u, c);
    let my = diff(d, a_v, u_c); // = det2 a u c v (defeq)

    let term_a = rmul(d, a, mx);
    let term_b = rmul(d, b, my);
    let start = radd(d, term_a, term_b);

    let a_udd = rmul(d, a, u_dd);
    let a_bv = rmul(d, a, b_v);
    let target_a = diff(d, a_udd, a_bv);
    let msrr_a = mul_sub_right_rev(d, p, a, u_dd, b_v); // target_a = term_a
    let step_a = rsymm(d, target_a, term_a, msrr_a); // term_a -> target_a
    let cstep_a = rcongr(d, term_a, target_a, step_a, &|d, t| radd(d, t, term_b));
    let mid1 = radd(d, target_a, term_b);

    let b_av = rmul(d, b, a_v);
    let b_uc = rmul(d, b, u_c);
    let target_b = diff(d, b_av, b_uc);
    let msrr_b = mul_sub_right_rev(d, p, b, a_v, u_c); // target_b = term_b
    let step_b = rsymm(d, target_b, term_b, msrr_b); // term_b -> target_b
    let cstep_b = rcongr(d, term_b, target_b, step_b, &|d, t| radd(d, target_a, t));
    let mid2 = radd(d, target_a, target_b); // (a_udd - a_bv) + (b_av - b_uc)

    // b_av = a_bv: b*(a*v) = (b*a)*v = (a*b)*v = a*(b*v).
    let ba = rmul(d, b, a);
    let ba_v = rmul(d, ba, v);
    let assoc_bav = d.lemma(p.mul_assoc, &[b, a, v]); // (b*a)*v = b*(a*v) = b_av
    let step_bav1 = rsymm(d, ba_v, b_av, assoc_bav); // b_av -> ba_v
    let ab = rmul(d, a, b);
    let ab_v = rmul(d, ab, v);
    let comm_ba = d.lemma(p.mul_comm, &[b, a]); // b*a = a*b
    let step_bav2 = rcongr(d, ba, ab, comm_ba, &|d, t| rmul(d, t, v)); // ba_v -> ab_v
    let assoc_abv = d.lemma(p.mul_assoc, &[a, b, v]); // (a*b)*v = a*(b*v) = a_bv
    let (_, hab) = rchain(
        d,
        b_av,
        &[(ba_v, step_bav1), (ab_v, step_bav2), (a_bv, assoc_abv)],
    ); // hab : b_av = a_bv

    let step_rewrite = rcongr(d, b_av, a_bv, hab, &|d, t| {
        let inner = diff(d, t, b_uc);
        radd(d, target_a, inner)
    });
    let a_bv_minus_buc = diff(d, a_bv, b_uc);
    let mid3 = radd(d, target_a, a_bv_minus_buc); // (a_udd-a_bv)+(a_bv-b_uc)

    let telescope = d.lemma(p.sub_add_sub, &[a_udd, a_bv, b_uc]); // mid3 = a_udd - b_uc
    let mid4 = diff(d, a_udd, b_uc);

    // a_udd -> (a*dd)*u
    let dd_u = rmul(d, dd, u);
    let a_ddu = rmul(d, a, dd_u);
    let comm_udd = d.lemma(p.mul_comm, &[u, dd]); // u*d = d*u
    let step_udd1 = rcongr(d, u_dd, dd_u, comm_udd, &|d, t| rmul(d, a, t)); // a_udd -> a_ddu
    let a_dd = rmul(d, a, dd);
    let a_dd_u = rmul(d, a_dd, u);
    let assoc_addu = d.lemma(p.mul_assoc, &[a, dd, u]); // (a*d)*u = a*(d*u) = a_ddu
    let step_udd2 = rsymm(d, a_dd_u, a_ddu, assoc_addu); // a_ddu -> a_dd_u
    let (_, a_udd_to_a_dd_u) = rchain(d, a_udd, &[(a_ddu, step_udd1), (a_dd_u, step_udd2)]);

    // b_uc -> (b*c)*u
    let c_u = rmul(d, c, u);
    let b_cu = rmul(d, b, c_u);
    let comm_uc = d.lemma(p.mul_comm, &[u, c]); // u*c = c*u
    let step_buc1 = rcongr(d, u_c, c_u, comm_uc, &|d, t| rmul(d, b, t)); // b_uc -> b_cu
    let b_c = rmul(d, b, c);
    let b_c_u = rmul(d, b_c, u);
    let assoc_bcu = d.lemma(p.mul_assoc, &[b, c, u]); // (b*c)*u = b*(c*u) = b_cu
    let step_buc2 = rsymm(d, b_c_u, b_cu, assoc_bcu); // b_cu -> b_c_u
    let (_, b_uc_to_b_c_u) = rchain(d, b_uc, &[(b_cu, step_buc1), (b_c_u, step_buc2)]);

    let step5 = rcongr(d, a_udd, a_dd_u, a_udd_to_a_dd_u, &|d, t| {
        let n = rneg(d, b_uc);
        radd(d, t, n)
    });
    let mid5 = diff(d, a_dd_u, b_uc);
    let step6 = rcongr(d, b_uc, b_c_u, b_uc_to_b_c_u, &|d, t| {
        let n = rneg(d, t);
        radd(d, a_dd_u, n)
    });
    let mid6 = diff(d, a_dd_u, b_c_u);

    let sub_mul_pf = d.lemma(p.sub_mul, &[a_dd, b_c, u]); // (a_dd*u)-(b_c*u)=(a_dd-b_c)*u
    let det = rdet2(d, p, a, b, c, dd);
    let det_u = rmul(d, det, u); // = (a_dd-b_c)*u (defeq)

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, cstep_a),
            (mid2, cstep_b),
            (mid3, step_rewrite),
            (mid4, telescope),
            (mid5, step5),
            (mid6, step6),
            (det_u, sub_mul_pf),
        ],
    );
    proof
}

/// `c·(det2 u b v d) + d·(det2 a u c v) = (det2 a b c d)·v` — unconditional,
/// no hypothesis. The other half of "the Cramer values satisfy the system"
/// ([`cramer_solves_eq1_identity`] is the `u`/first-equation half): here the
/// `u`-terms `c·(u·d)` and `d·(u·c)` are equal (a three-factor commute) and
/// cancel, leaving `d·(a·v) − c·(b·v) = D·v`.
#[allow(clippy::too_many_arguments)]
fn cramer_solves_eq2_identity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    u: ExprId,
    v: ExprId,
) -> ExprId {
    let u_dd = rmul(d, u, dd);
    let b_v = rmul(d, b, v);
    let mx = diff(d, u_dd, b_v); // = det2 u b v d (defeq)
    let a_v = rmul(d, a, v);
    let u_c = rmul(d, u, c);
    let my = diff(d, a_v, u_c); // = det2 a u c v (defeq)

    let term_c = rmul(d, c, mx);
    let term_dd = rmul(d, dd, my);
    let start = radd(d, term_c, term_dd);

    let c_udd = rmul(d, c, u_dd);
    let c_bv = rmul(d, c, b_v);
    let target_c = diff(d, c_udd, c_bv);
    let msrr_c = mul_sub_right_rev(d, p, c, u_dd, b_v); // target_c = term_c
    let step_c = rsymm(d, target_c, term_c, msrr_c); // term_c -> target_c
    let cstep_c = rcongr(d, term_c, target_c, step_c, &|d, t| radd(d, t, term_dd));
    let mid1 = radd(d, target_c, term_dd);

    let dd_av = rmul(d, dd, a_v);
    let dd_uc = rmul(d, dd, u_c);
    let target_dd = diff(d, dd_av, dd_uc);
    let msrr_dd = mul_sub_right_rev(d, p, dd, a_v, u_c); // target_dd = term_dd
    let step_dd = rsymm(d, target_dd, term_dd, msrr_dd); // term_dd -> target_dd
    let cstep_dd = rcongr(d, term_dd, target_dd, step_dd, &|d, t| radd(d, target_c, t));
    let mid2 = radd(d, target_c, target_dd); // (c_udd-c_bv)+(dd_av-dd_uc)

    // c_udd = dd_uc: c*(u*d) = (c*d)*u = (d*c)*u = d*(c*u) = d*(u*c).
    let dd_u = rmul(d, dd, u);
    let c_ddu = rmul(d, c, dd_u);
    let comm_h1 = d.lemma(p.mul_comm, &[u, dd]); // u*d = d*u
    let step_h1 = rcongr(d, u_dd, dd_u, comm_h1, &|d, t| rmul(d, c, t)); // c_udd -> c_ddu
    let c_dd = rmul(d, c, dd);
    let cdd_u = rmul(d, c_dd, u);
    let assoc_h2 = d.lemma(p.mul_assoc, &[c, dd, u]); // (c*d)*u = c*(d*u) = c_ddu
    let step_h2 = rsymm(d, cdd_u, c_ddu, assoc_h2); // c_ddu -> cdd_u
    let ddc = rmul(d, dd, c);
    let ddc_u = rmul(d, ddc, u);
    let comm_h3 = d.lemma(p.mul_comm, &[c, dd]); // c*d = d*c
    let step_h3 = rcongr(d, c_dd, ddc, comm_h3, &|d, t| rmul(d, t, u)); // cdd_u -> ddc_u
    let c_u = rmul(d, c, u);
    let dd_cu = rmul(d, dd, c_u);
    let assoc_h4 = d.lemma(p.mul_assoc, &[dd, c, u]); // (d*c)*u = d*(c*u) = dd_cu
    let comm_h5 = d.lemma(p.mul_comm, &[c, u]); // c*u = u*c
    let step_h5 = rcongr(d, c_u, u_c, comm_h5, &|d, t| rmul(d, dd, t)); // dd_cu -> dd_uc

    let (_, hcu) = rchain(
        d,
        c_udd,
        &[
            (c_ddu, step_h1),
            (cdd_u, step_h2),
            (ddc_u, step_h3),
            (dd_cu, assoc_h4),
            (dd_uc, step_h5),
        ],
    ); // hcu : c_udd = dd_uc

    let step_rewrite = rcongr(d, c_udd, dd_uc, hcu, &|d, t| {
        let inner = diff(d, t, c_bv);
        radd(d, inner, target_dd)
    });
    let dd_uc_minus_cbv = diff(d, dd_uc, c_bv);
    let mid2b = radd(d, dd_uc_minus_cbv, target_dd); // (dd_uc-c_bv)+(dd_av-dd_uc)

    let swap = d.lemma(p.add_comm, &[dd_uc_minus_cbv, target_dd]); // mid2b = swapped
    let swapped = radd(d, target_dd, dd_uc_minus_cbv); // (dd_av-dd_uc)+(dd_uc-c_bv)

    let telescope = d.lemma(p.sub_add_sub, &[dd_av, dd_uc, c_bv]); // swapped = dd_av - c_bv
    let mid4 = diff(d, dd_av, c_bv);

    // dd_av -> (a*dd)*v
    let dda = rmul(d, dd, a);
    let dda_v = rmul(d, dda, v);
    let assoc_ddav = d.lemma(p.mul_assoc, &[dd, a, v]); // (d*a)*v = d*(a*v) = dd_av
    let step_ddav1 = rsymm(d, dda_v, dd_av, assoc_ddav); // dd_av -> dda_v
    let a_dd = rmul(d, a, dd);
    let a_dd_v = rmul(d, a_dd, v);
    let comm_ddav = d.lemma(p.mul_comm, &[dd, a]); // d*a = a*d
    let step_ddav2 = rcongr(d, dda, a_dd, comm_ddav, &|d, t| rmul(d, t, v)); // dda_v -> a_dd_v
    let (_, dd_av_to_a_dd_v) = rchain(d, dd_av, &[(dda_v, step_ddav1), (a_dd_v, step_ddav2)]);

    // c_bv -> (b*c)*v
    let cb = rmul(d, c, b);
    let cb_v = rmul(d, cb, v);
    let assoc_cbv = d.lemma(p.mul_assoc, &[c, b, v]); // (c*b)*v = c*(b*v) = c_bv
    let step_cbv1 = rsymm(d, cb_v, c_bv, assoc_cbv); // c_bv -> cb_v
    let b_c = rmul(d, b, c);
    let b_c_v = rmul(d, b_c, v);
    let comm_cbv = d.lemma(p.mul_comm, &[c, b]); // c*b = b*c
    let step_cbv2 = rcongr(d, cb, b_c, comm_cbv, &|d, t| rmul(d, t, v)); // cb_v -> b_c_v
    let (_, c_bv_to_b_c_v) = rchain(d, c_bv, &[(cb_v, step_cbv1), (b_c_v, step_cbv2)]);

    let step5 = rcongr(d, dd_av, a_dd_v, dd_av_to_a_dd_v, &|d, t| {
        let n = rneg(d, c_bv);
        radd(d, t, n)
    });
    let mid5 = diff(d, a_dd_v, c_bv);
    let step6 = rcongr(d, c_bv, b_c_v, c_bv_to_b_c_v, &|d, t| {
        let n = rneg(d, t);
        radd(d, a_dd_v, n)
    });
    let mid6 = diff(d, a_dd_v, b_c_v);

    let sub_mul_pf = d.lemma(p.sub_mul, &[a_dd, b_c, v]); // (a_dd*v)-(b_c*v)=(a_dd-b_c)*v
    let det = rdet2(d, p, a, b, c, dd);
    let det_v = rmul(d, det, v); // = (a_dd-b_c)*v (defeq)

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, cstep_c),
            (mid2, cstep_dd),
            (mid2b, step_rewrite),
            (swapped, swap),
            (mid4, telescope),
            (mid5, step5),
            (mid6, step6),
            (det_v, sub_mul_pf),
        ],
    );
    proof
}

/// Solve `coef1·m1 + coef2·m2 = D·w` for `w`, given `h3 : D ≠ 0`, producing a
/// proof of `Eq (coef1·(m1·invD) + coef2·(m2·invD)) w` — the two-term
/// generalisation of [`cramer_solve`], needed for the SUBSTITUTION direction
/// ([`declare_cramer2_solves`]) where both `Rat.cramer2_x` and
/// `Rat.cramer2_y` appear together in the same equation, unlike the
/// uniqueness direction's single unknown.
#[allow(clippy::too_many_arguments)]
fn combo_cramer_solve(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    det: ExprId,
    inv_det: ExprId,
    coef1: ExprId,
    m1: ExprId,
    coef2: ExprId,
    m2: ExprId,
    w: ExprId,
    combo_is_det_w: ExprId,
    h3: ExprId,
) -> ExprId {
    let m1_invd = rmul(d, m1, inv_det);
    let m2_invd = rmul(d, m2, inv_det);
    let term1 = rmul(d, coef1, m1_invd);
    let term2 = rmul(d, coef2, m2_invd);
    let start = radd(d, term1, term2);

    let coef1_m1 = rmul(d, coef1, m1);
    let coef1_m1_invd = rmul(d, coef1_m1, inv_det);
    let assoc1 = d.lemma(p.mul_assoc, &[coef1, m1, inv_det]); // coef1_m1_invd = term1
    let step1 = rsymm(d, coef1_m1_invd, term1, assoc1); // term1 -> coef1_m1_invd
    let cstep1 = rcongr(d, term1, coef1_m1_invd, step1, &|d, t| radd(d, t, term2));
    let mid1 = radd(d, coef1_m1_invd, term2);

    let coef2_m2 = rmul(d, coef2, m2);
    let coef2_m2_invd = rmul(d, coef2_m2, inv_det);
    let assoc2 = d.lemma(p.mul_assoc, &[coef2, m2, inv_det]); // coef2_m2_invd = term2
    let step2 = rsymm(d, coef2_m2_invd, term2, assoc2); // term2 -> coef2_m2_invd
    let cstep2 = rcongr(d, term2, coef2_m2_invd, step2, &|d, t| {
        radd(d, coef1_m1_invd, t)
    });
    let mid2 = radd(d, coef1_m1_invd, coef2_m2_invd);

    let combined_inner = radd(d, coef1_m1, coef2_m2);
    let combined = rmul(d, combined_inner, inv_det);
    let distrib_fwd = d.lemma(p.right_distrib, &[coef1_m1, coef2_m2, inv_det]); // combined = mid2
    let step3 = rsymm(d, combined, mid2, distrib_fwd); // mid2 -> combined

    let det_w = rmul(d, det, w);
    let step4 = rcongr(d, combined_inner, det_w, combo_is_det_w, &|d, t| {
        rmul(d, t, inv_det)
    });
    let mid4 = rmul(d, det_w, inv_det);

    let assoc3 = d.lemma(p.mul_assoc, &[det, w, inv_det]); // mid4 = mid5
    let w_invd = rmul(d, w, inv_det);
    let mid5 = rmul(d, det, w_invd);

    let comm1 = d.lemma(p.mul_comm, &[w, inv_det]); // w*invD = invD*w
    let invd_w = rmul(d, inv_det, w);
    let step6 = rcongr(d, w_invd, invd_w, comm1, &|d, t| rmul(d, det, t));
    let mid6 = rmul(d, det, invd_w);

    let det_invd = rmul(d, det, inv_det);
    let det_invd_w = rmul(d, det_invd, w);
    let assoc4 = d.lemma(p.mul_assoc, &[det, inv_det, w]); // det_invd_w = mid6
    let step7 = rsymm(d, det_invd_w, mid6, assoc4); // mid6 -> det_invd_w

    let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[det, h3]); // det*invD = 1
    let one = rone(d, p);
    let step8 = rcongr(d, det_invd, one, cancel, &|d, t| rmul(d, t, w));
    let mid8 = rmul(d, one, w);

    let comm2 = d.lemma(p.mul_comm, &[one, w]); // 1*w = w*1
    let w1 = rmul(d, w, one);
    let mul_one_pf = d.lemma(p.mul_one, &[w]); // w*1 = w

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, cstep1),
            (mid2, cstep2),
            (combined, step3),
            (mid4, step4),
            (mid5, assoc3),
            (mid6, step6),
            (det_invd_w, step7),
            (mid8, step8),
            (w1, comm2),
            (w, mul_one_pf),
        ],
    );
    proof
}

/// `Rat.cramer2_solves : ∀ a b c d u v, Not (det2 a b c d = 0) →`
/// `  (a·(cramer2_x a b c d u v) + b·(cramer2_y a b c d u v) = u) ∧`
/// `  (c·(cramer2_x a b c d u v) + d·(cramer2_y a b c d u v) = v)`.
///
/// The **substitution** direction of Cramer's rule: the formulas actually
/// solve the system, not merely that a solution (if one exists) must equal
/// them ([`declare_cramer_two_unique_x`]/[`declare_cramer_two_unique_y`]).
/// Bundled with the kernel's `Prop`-level `And` — no tuple/product type
/// exists to return `(x, y)` together, but `And` needs no such type, only two
/// `Prop`s. Each half reduces to [`cramer_solves_eq1_identity`]/
/// [`cramer_solves_eq2_identity`] (unconditional algebraic identities) via
/// [`combo_cramer_solve`].
fn declare_cramer2_solves(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem_hyp(
        d,
        p.cramer2_solves,
        6,
        &|d, v| {
            let (a, b, c, dd, u, vv) = (v[0], v[1], v[2], v[3], v[4], v[5]);
            let hyp = det2_ne_zero(d, p, a, b, c, dd);

            let x = d.const_app(p.cramer2_x, &[a, b, c, dd, u, vv]);
            let y = d.const_app(p.cramer2_y, &[a, b, c, dd, u, vv]);

            let ax = rmul(d, a, x);
            let by = rmul(d, b, y);
            let ax_by = radd(d, ax, by);
            let eq1 = req(d, ax_by, u);

            let cx = rmul(d, c, x);
            let dy = rmul(d, dd, y);
            let cx_dy = radd(d, cx, dy);
            let eq2 = req(d, cx_dy, vv);

            let concl = d.and(eq1, eq2);
            (hyp, concl)
        },
        &|d, v, h| {
            let (a, b, c, dd, u, vv) = (v[0], v[1], v[2], v[3], v[4], v[5]);
            let det = rdet2(d, p, a, b, c, dd);
            let inv_det = d.const_app(p.inv, &[det]);
            let mx = rdet2(d, p, u, b, vv, dd);
            let my = rdet2(d, p, a, u, c, vv);

            let identity1 = cramer_solves_eq1_identity(d, p, a, b, c, dd, u, vv);
            let proof_eq1 = combo_cramer_solve(d, p, det, inv_det, a, mx, b, my, u, identity1, h);

            let identity2 = cramer_solves_eq2_identity(d, p, a, b, c, dd, u, vv);
            let proof_eq2 = combo_cramer_solve(d, p, det, inv_det, c, mx, dd, my, vv, identity2, h);

            let x = d.const_app(p.cramer2_x, &[a, b, c, dd, u, vv]);
            let y = d.const_app(p.cramer2_y, &[a, b, c, dd, u, vv]);
            let ax = rmul(d, a, x);
            let by = rmul(d, b, y);
            let ax_by = radd(d, ax, by);
            let eq1 = req(d, ax_by, u);
            let cx = rmul(d, c, x);
            let dy = rmul(d, dd, y);
            let cx_dy = radd(d, cx, dy);
            let eq2 = req(d, cx_dy, vv);

            let intro = p.int.logic.and_intro;
            d.const_app(intro, &[eq1, eq2, proof_eq1, proof_eq2])
        },
    )
}

/// Admit `Rat.cramer2_x`, `Rat.cramer2_y`, and `Rat.cramer2_solves`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_cramer2(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_cramer2_x(d, p)?;
    declare_cramer2_y(d, p)?;
    declare_cramer2_solves(d, p)
}

// ============================================================================
// The Fibonacci–determinant bridge: `Rat.ofInt` and `Rat.det2_fib`.
// ============================================================================
//
// `Int.fib_cassini` (`int_prelude/fibonacci.rs`) proves
// `fib(n+2)·fib(n) − fib(n+1)² = (−1)^(n+1)` over `ℤ`. That LEFT side is
// exactly `Rat.det2` applied to the four entries of `Mⁿ` for
// `M = [[1,1],[1,0]]` (`det2 x y z w := x·w − y·z`, so `det2 C B B A =
// C·A − B·B` with `C = fib(n+2), B = fib(n+1), A = fib n`) — Cassini's
// identity **is** `det (Mⁿ) = (−1)ⁿ` read through this file's `det2_mul`.
// This section makes that identification a derivation rather than a
// comment: `Rat.ofInt` casts `ℤ` into `ℚ`, three lemmas say it is a ring
// homomorphism for `+`, `·`, `neg`, and `Rat.det2_fib` transports
// `Int.fib_cassini` across the cast.
//
// No matrix type is reified here either, for the same reason `adj2` above
// is not: this kernel has no product/tuple type, so `Mⁿ` is never written
// down as a single value — only its four entries, which is all `det2_fib`'s
// statement needs.

/// Delta height for `Rat.ofInt`: it unfolds to one `Rat.mk` application (a
/// constructor, not a further `Definition`), so — like `Rat.det2` — it only
/// needs to sit above whatever it is compared against during unfolding, not
/// above the whole rational development.
const OF_INT_HEIGHT: u16 = 40;

/// `Rat.ofInt x := Rat.mk x 1 pos red`, where `pos : 1 ≤ 1` does not depend on
/// `x` and `red : gcd (natAbs x) 1 = 1` is `Rat.gcd_one_right` at `natAbs x` —
/// valid for **any** `x : Int`, so no case split on `x`'s constructor is
/// needed the way [`super::defs::inv_body`] or `Rat.normalize` need one.
///
/// `Rat.num (ofInt x)` and `Rat.den (ofInt x)` therefore reduce to `x` and `1`
/// by a single `ι`-step each — the fact every proof below leans on.
fn declare_of_int_def(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let int_ty = d.int_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let unit = d.num(1);
    let positive = {
        let nat = p.int.nat;
        d.lemma(nat.le_refl, &[unit])
    };
    let reduced = {
        let nat_abs = d.const_app(p.int.nat_abs, &[x]);
        d.lemma(p.gcd_one_right, &[nat_abs])
    };
    let body = mk(d, x, unit, positive, reduced);
    let value = d.lam_fv(x_fv, int_ty, body);
    let ty = d.arrow(int_ty, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_int,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(OF_INT_HEIGHT),
    })
}

/// `Rat.ofInt x` — the folded application, for building statements.
fn of_int(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.of_int, &[x])
}

/// From `h : Eq Int a b`, derive `Eq Rat (f a) (f b)` — the `Rat`-valued
/// congruence [`super::ops::int_eq_to_nat`] is the `Nat`-valued twin of.
/// [`Int.fib_cassini`](crate::int_prelude::IntPrelude::fib_cassini) is an `ℤ`
/// equation and `Rat.ofInt` casts into `ℚ`, so this is the one device that
/// transports it.
fn int_eq_to_rat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.ieq_motive(a, &|d, x| {
        let fx = f(d, x);
        req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    d.itransport(a, motive, refl_case, b, h)
}

/// `Rat.ofInt_add : ∀ x y : Int, Eq Rat (ofInt (x+y)) (ofInt x + ofInt y)`.
///
/// Both sides have denominator exactly `1`, so the identity boils down to
/// `Rat.add_cross` at `(ofInt x, ofInt y)` — with `den(ofInt x)`, `den(ofInt
/// y)` unfolding to the literal `1` — simplified by `Int.mul_one` (`z·1 = z`
/// is **not** definitional here for symbolic `z`, matching `laws.rs`'s
/// `unit_law` convention: this development always cites the lemma) and closed
/// by `Rat.eq_of_cross`.
fn declare_of_int_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    d.int_theorem(p.of_int_add, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let sum_int = d.iadd(x, y);
        let qxy = of_int(d, p, sum_int);
        let qx = of_int(d, p, x);
        let qy = of_int(d, p, y);
        let combined = radd(d, qx, qy);
        let stmt = req(d, qxy, combined);

        let one_i = d.ione();
        let num_combined = num(d, combined);
        let den_combined = den(d, combined);
        let den_combined_z = d.of_nat(den_combined);

        // lhs0 = num(combined) * ofNat(den(ofInt x)) ~ num(combined) * 1,
        // the marker `Rat.eq_of_cross`'s hypothesis states on its RHS.
        let lhs0 = d.imul(num_combined, one_i);

        // sum_expr = x*1 + y*1 ~ Rat.add_cross's naive-sum numerator, once
        // `den(ofInt x)`/`den(ofInt y)` unfold to `1`.
        let sum_x1 = d.imul(x, one_i);
        let sum_y1 = d.imul(y, one_i);
        let sum_expr = d.iadd(sum_x1, sum_y1);
        let rhs0 = d.imul(sum_expr, den_combined_z);

        // add_cross(qx, qy), read at this simplified shape by kernel defeq
        // (den(ofInt _) ~ 1, num(ofInt _) ~ its argument, both single
        // `ι`-steps; `1*1 ~ 1` is concrete-literal computation).
        let cross0 = d.lemma(p.add_cross, &[qx, qy]);

        // Simplify sum_expr down to x+y.
        let xy = d.iadd(x, y);
        let (_, simplify_sum) = {
            let mul_one_x = d.lemma(p.int.mul_one, &[x]);
            let mid_x = d.iadd(x, sum_y1);
            let step_x = d.icongr(sum_x1, x, mul_one_x, &|d, t| d.iadd(t, sum_y1));
            let mul_one_y = d.lemma(p.int.mul_one, &[y]);
            let step_y = d.icongr(sum_y1, y, mul_one_y, &|d, t| d.iadd(x, t));
            d.ichain(sum_expr, &[(mid_x, step_x), (xy, step_y)])
        };
        let rhs1 = d.imul(xy, den_combined_z);
        let step_rhs = d.icongr(sum_expr, xy, simplify_sum, &|d, t| {
            d.imul(t, den_combined_z)
        });

        let (_, lhs0_to_rhs1) = d.ichain(lhs0, &[(rhs0, cross0), (rhs1, step_rhs)]);
        let hyp = d.isymm(lhs0, rhs1, lhs0_to_rhs1);
        let proof = d.const_app(p.eq_of_cross, &[qxy, combined, hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Rat.ofInt_mul : ∀ x y : Int, Eq Rat (ofInt (x·y)) (ofInt x · ofInt y)`.
///
/// Same route as [`declare_of_int_add`] via `Rat.mul_cross`, but with no
/// `mul_one` cleanup needed on the product side: `mul_cross`'s naive-product
/// numerator is already `num(ofInt x) * num(ofInt y) ~ x·y`.
fn declare_of_int_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    d.int_theorem(p.of_int_mul, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let prod_int = d.imul(x, y);
        let qxy = of_int(d, p, prod_int);
        let qx = of_int(d, p, x);
        let qy = of_int(d, p, y);
        let combined = rmul(d, qx, qy);
        let stmt = req(d, qxy, combined);

        let one_i = d.ione();
        let num_combined = num(d, combined);
        let den_combined = den(d, combined);
        let den_combined_z = d.of_nat(den_combined);

        let lhs0 = d.imul(num_combined, one_i);
        let xy = d.imul(x, y);
        let rhs0 = d.imul(xy, den_combined_z);

        // mul_cross(qx, qy), read at this simplified shape by kernel defeq
        // (den(ofInt _) ~ 1, num(ofInt _) ~ its argument).
        let cross0 = d.lemma(p.mul_cross, &[qx, qy]);

        let hyp = d.isymm(lhs0, rhs0, cross0);
        let proof = d.const_app(p.eq_of_cross, &[qxy, combined, hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Rat.ofInt_neg : ∀ x : Int, Eq Rat (ofInt (neg x)) (neg (ofInt x))`.
///
/// **Free** — unlike `+`/`·`, `Rat.neg` does not renormalise (it rebuilds
/// `Rat.mk` directly, transporting the reducedness field along
/// `natAbs (neg x) = natAbs x`), so `neg (ofInt x)` and `ofInt (neg x)` both
/// `δ`/`ι`-reduce to `Rat.mk (neg x) 1 (le_refl 1) _`, differing only in the
/// fourth (`Prop`-typed) field — which the kernel's definitional proof
/// irrelevance (`tc.rs::proof_irrel_eq`) erases. `Eq.refl` is the whole proof.
fn declare_of_int_neg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    d.int_theorem(p.of_int_neg, 1, &|d, v| {
        let x = v[0];
        let neg_x = d.ineg(x);
        let qneg = of_int(d, p, neg_x);
        let qx = of_int(d, p, x);
        let negq = rneg(d, qx);
        let stmt = req(d, qneg, negq);
        let proof = rrefl(d, qneg);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Rat.det2_fib : ∀ n, Eq Rat`
/// `  (det2 (ofInt (ofNat (fib (n+2)))) (ofInt (ofNat (fib (n+1))))`
/// `        (ofInt (ofNat (fib (n+1)))) (ofInt (ofNat (fib n))))`
/// `  (ofInt (pow (neg one) (succ n)))`
///
/// Cassini's identity, read through `det2`: for `M = [[1,1],[1,0]]`, `Mⁿ =
/// [[fib(n+1), fib n], [fib n, fib(n-1)]]` and `det M = −1`, so
/// `det (Mⁿ) = (−1)ⁿ` expands to exactly this statement at the shifted index
/// `Int.fib_cassini` uses. **Derived from `Int.fib_cassini`** (not reproved
/// independently): [`int_eq_to_rat`] transports it across `Rat.ofInt`, and
/// [`declare_of_int_add`]/[`declare_of_int_mul`]/[`declare_of_int_neg`]
/// rewrite the cast of `D(n) := fib(n+2)·fib(n) − fib(n+1)²` into
/// `det2 (ofInt C) (ofInt B) (ofInt B) (ofInt A)` — the defining unfolding of
/// `det2 x y z w := x·w − y·z` at `x=C, y=B, z=B, w=A`.
fn declare_det2_fib(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let fib = p.int.nat.fib;
    let fib_n = d.const_app(fib, &[n]);
    let fib_sn = d.const_app(fib, &[sn]);
    let fib_ssn = d.const_app(fib, &[ssn]);
    let a_int = d.of_nat(fib_n);
    let b_int = d.of_nat(fib_sn);
    let c_int = d.of_nat(fib_ssn);

    let ca_int = d.imul(c_int, a_int);
    let bb_int = d.imul(b_int, b_int);
    let d_n = d.isub(ca_int, bb_int);
    let neg_bb_int = d.ineg(bb_int);

    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let rhs_int = d.ipow(neg_one, sn);

    // Int.fib_cassini n : Eq Int d_n rhs_int (exact same construction as
    // int_prelude/fibonacci.rs's `cassini_lhs`/`cassini_stmt`).
    let cassini_proof = d.lemma(p.int.fib_cassini, &[n]);

    let qa = of_int(d, p, a_int);
    let qb = of_int(d, p, b_int);
    let qc = of_int(d, p, c_int);

    let lhs = rdet2(d, p, qc, qb, qb, qa);
    let rhs = of_int(d, p, rhs_int);
    let stmt = req(d, lhs, rhs);

    // Step A: Eq Rat (ofInt d_n) (ofInt rhs_int), by transporting Cassini.
    let q_dn = int_eq_to_rat(d, d_n, rhs_int, cassini_proof, &|d, t| of_int(d, p, t));

    // Step B: Eq Rat (ofInt d_n) (det2 qc qb qb qa), by ofInt_add/mul/neg.
    let of_int_dn = of_int(d, p, d_n);
    let of_int_ca = of_int(d, p, ca_int);
    let of_int_neg_bb = of_int(d, p, neg_bb_int);
    let of_int_bb = of_int(d, p, bb_int);

    let qc_qa = rmul(d, qc, qa);
    let qb_qb = rmul(d, qb, qb);
    let neg_qb_qb = rneg(d, qb_qb);
    let neg_of_int_bb = rneg(d, of_int_bb);

    // ofInt(d_n) = ofInt(C*A) + ofInt(-(B*B))  [ofInt_add at (ca_int, neg_bb_int);
    // d_n ~ ca_int + neg_bb_int by unfolding Int.sub, a single delta step].
    let q_add_lemma = d.lemma(p.of_int_add, &[ca_int, neg_bb_int]);
    let combined_rhs = radd(d, of_int_ca, of_int_neg_bb);

    // ofInt(C*A) = qc*qa.
    let q_mul_ca = d.lemma(p.of_int_mul, &[c_int, a_int]);
    let mid_a = radd(d, qc_qa, of_int_neg_bb);
    let step_a = rcongr(d, of_int_ca, qc_qa, q_mul_ca, &|d, t| {
        radd(d, t, of_int_neg_bb)
    });

    // ofInt(-(B*B)) = -(ofInt(B*B)) = -(qb*qb).
    let q_neg_bb = d.lemma(p.of_int_neg, &[bb_int]);
    let q_mul_bb = d.lemma(p.of_int_mul, &[b_int, b_int]);
    let step_negbb = {
        let inner = rcongr(d, of_int_bb, qb_qb, q_mul_bb, &|d, t| rneg(d, t));
        rtrans(d, of_int_neg_bb, neg_of_int_bb, neg_qb_qb, q_neg_bb, inner)
    };
    let target = radd(d, qc_qa, neg_qb_qb); // = det2 qc qb qb qa, unfolded
    let step_b = rcongr(d, of_int_neg_bb, neg_qb_qb, step_negbb, &|d, t| {
        radd(d, qc_qa, t)
    });

    let (_, combine_proof) = rchain(d, combined_rhs, &[(mid_a, step_a), (target, step_b)]);
    let q_dn_to_target = rtrans(
        d,
        of_int_dn,
        combined_rhs,
        target,
        q_add_lemma,
        combine_proof,
    );
    let target_to_dn = rsymm(d, of_int_dn, target, q_dn_to_target);

    // Combine Step A and Step B: det2 qc qb qb qa = ofInt(d_n) = ofInt(rhs_int).
    let final_proof = rtrans(d, target, of_int_dn, rhs, target_to_dn, q_dn);

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, final_proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det2_fib,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The 3×3 determinant: `Rat.det3`, `Rat.det3_id`, cofactor expansion.
// ============================================================================
//
// Same idiom as `Rat.det2` above: no matrix carrier, nine explicit scalar
// arguments in row-major order — `det3 a b c d e f g h i` is
// `[[a,b,c],[d,e,f],[g,h,i]]`. `Rat.det3` is built directly as the
// cofactor-expanded-along-row-1 formula (`a*det2(e,f,h,i) − b*det2(d,f,g,i) +
// c*det2(d,e,g,h)`, written out in raw `sub`/`mul` form rather than by
// calling `Rat.det2`), so [`declare_det3_cofactor_row1`] — the theorem
// stating that expansion in terms of three `Rat.det2` applications — needs no
// ring-law rewriting at all: both sides δ-unfold to the identical raw term,
// and `Eq.refl` closes it.

/// `Rat.det3 a b c d e f g h i :=`
/// `  (a*(e*i − f*h) − b*(d*i − f*g)) + c*(d*h − e*g)`
///
/// The 3×3 determinant of `[[a,b,c],[d,e,f],[g,h,i]]`, cofactor-expanded
/// along the first row: `e*i−f*h`, `d*i−f*g`, `d*h−e*g` are exactly
/// `Rat.det2 e f h i`, `Rat.det2 d f g i`, `Rat.det2 d e g h` unfolded (`Rat.det2
/// x y z w := x*w − y*z`). Written directly in this expanded raw form — not
/// by applying `Rat.det2` three times — so [`declare_det3_cofactor_row1`]
/// needs no algebra: it is the same claim stated two ways, provable by
/// `Eq.refl`.
fn declare_det3_def(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..9).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
    let (a, b, c, dd, e, f, g, h, i) = (
        vars[0], vars[1], vars[2], vars[3], vars[4], vars[5], vars[6], vars[7], vars[8],
    );

    let ei = rmul(d, e, i);
    let fh = rmul(d, f, h);
    let x = rsub(d, p, ei, fh);
    let di = rmul(d, dd, i);
    let fg = rmul(d, f, g);
    let y = rsub(d, p, di, fg);
    let dh = rmul(d, dd, h);
    let eg = rmul(d, e, g);
    let z = rsub(d, p, dh, eg);

    let ax = rmul(d, a, x);
    let by = rmul(d, b, y);
    let cz = rmul(d, c, z);
    let ax_by = rsub(d, p, ax, by);
    let body = radd(d, ax_by, cz);

    let mut value = body;
    for &fv in fvs.iter().rev() {
        value = d.lam_fv(fv, carrier, value);
    }
    let mut ty = carrier;
    for _ in 0..9 {
        ty = d.arrow(carrier, ty);
    }
    d.kernel().add_declaration(Declaration::Definition {
        name: p.det3,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DET3_HEIGHT),
    })
}

/// `Rat.det3 a b c d e f g h i` — the folded application, for building
/// statements. Argument order matches [`declare_det3_def`]: row-major,
/// `[[a,b,c],[d,e,f],[g,h,i]]`.
#[allow(clippy::too_many_arguments)]
pub(super) fn rdet3(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
    e: ExprId,
    f: ExprId,
    g: ExprId,
    h: ExprId,
    i: ExprId,
) -> ExprId {
    d.const_app(p.det3, &[a, b, c, dd, e, f, g, h, i])
}

/// `zero * x = 0`, via `mul_comm` then `mul_zero` — this development has no
/// standalone `zero_mul` law (see `Rat.mul_zero`'s own doc comment), so every
/// left-zero product goes through commutation first.
/// `zero * x = zero`, by `ring::rat::prove_eq_at` (ring-tactic-2, ADR-1582)
/// rather than the hand `mul_comm`/`mul_zero` chain this file used to carry.
fn zero_mul(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    crate::ring::rat::prove_eq_at(d, &p, &[x], &|d, v| {
        let x = v[0];
        let zero = rzero(d, p);
        let lhs = rmul(d, zero, x);
        (lhs, zero)
    })
    .expect("zero_mul: zero*x = zero is a ring identity")
}

/// `Rat.det3_id : det3 1 0 0 0 1 0 0 0 1 = 1` — the 3×3 identity matrix has
/// determinant 1.
fn declare_det3_id(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det3_id, 0, &|d, _v| {
        let one = rone(d, p);
        let zero = rzero(d, p);
        // Row-major identity: a=1 b=0 c=0 / d=0 e=1 f=0 / g=0 h=0 i=1.
        let lhs = rdet3(d, p, one, zero, zero, zero, one, zero, zero, zero, one);
        let stmt = req(d, lhs, one);

        // --- X = e*i - f*h = 1*1 - 0*0 -> 1 ----------------------------------
        let ei = rmul(d, one, one);
        let fh = rmul(d, zero, zero);
        let neg_fh = rneg(d, fh);
        let x_raw = radd(d, ei, neg_fh);

        let mo_ei = d.lemma(p.mul_one, &[one]); // one*one = one
        let step_x1 = rcongr(d, ei, one, mo_ei, &|d, t| {
            let n = rneg(d, fh);
            radd(d, t, n)
        });
        let mid_x1 = radd(d, one, neg_fh);
        let mz_fh = d.lemma(p.mul_zero, &[zero]); // zero*zero = zero
        let step_x2 = rcongr(d, fh, zero, mz_fh, &|d, t| {
            let n = rneg(d, t);
            radd(d, one, n)
        });
        let neg_zero = rneg(d, zero);
        let mid_x2 = radd(d, one, neg_zero);
        let nz_x = d.lemma(p.neg_zero, &[]); // -0 = 0
        let step_x3 = rcongr(d, neg_zero, zero, nz_x, &|d, t| radd(d, one, t));
        let mid_x3 = radd(d, one, zero);
        let az_x = d.lemma(p.add_zero, &[one]); // 1+0 = 1
        let (_, x_proof) = rchain(
            d,
            x_raw,
            &[
                (mid_x1, step_x1),
                (mid_x2, step_x2),
                (mid_x3, step_x3),
                (one, az_x),
            ],
        );

        // --- Y = d*i - f*g = 0*1 - 0*0 -> 0 -----------------------------------
        let di = rmul(d, zero, one);
        let fg = rmul(d, zero, zero);
        let neg_fg = rneg(d, fg);
        let y_raw = radd(d, di, neg_fg);

        let zm_di = zero_mul(d, p, one); // zero*one = zero
        let step_y1 = rcongr(d, di, zero, zm_di, &|d, t| {
            let n = rneg(d, fg);
            radd(d, t, n)
        });
        let mid_y1 = radd(d, zero, neg_fg);
        let mz_fg = d.lemma(p.mul_zero, &[zero]); // zero*zero = zero
        let step_y2 = rcongr(d, fg, zero, mz_fg, &|d, t| {
            let n = rneg(d, t);
            radd(d, zero, n)
        });
        let mid_y2 = radd(d, zero, neg_zero);
        let nz_y = d.lemma(p.neg_zero, &[]);
        let step_y3 = rcongr(d, neg_zero, zero, nz_y, &|d, t| radd(d, zero, t));
        let mid_y3 = radd(d, zero, zero);
        let az_y = d.lemma(p.add_zero, &[zero]); // 0+0 = 0
        let (_, y_proof) = rchain(
            d,
            y_raw,
            &[
                (mid_y1, step_y1),
                (mid_y2, step_y2),
                (mid_y3, step_y3),
                (zero, az_y),
            ],
        );

        // --- Z = d*h - e*g = 0*0 - 1*0 -> 0 -----------------------------------
        let dh = rmul(d, zero, zero);
        let eg = rmul(d, one, zero);
        let neg_eg = rneg(d, eg);
        let z_raw = radd(d, dh, neg_eg);

        let mz_dh = d.lemma(p.mul_zero, &[zero]); // zero*zero = zero
        let step_z1 = rcongr(d, dh, zero, mz_dh, &|d, t| {
            let n = rneg(d, eg);
            radd(d, t, n)
        });
        let mid_z1 = radd(d, zero, neg_eg);
        let mz_eg = d.lemma(p.mul_zero, &[one]); // one*zero = zero
        let step_z2 = rcongr(d, eg, zero, mz_eg, &|d, t| {
            let n = rneg(d, t);
            radd(d, zero, n)
        });
        let mid_z2 = radd(d, zero, neg_zero);
        let nz_z = d.lemma(p.neg_zero, &[]);
        let step_z3 = rcongr(d, neg_zero, zero, nz_z, &|d, t| radd(d, zero, t));
        let mid_z3 = radd(d, zero, zero);
        let az_z = d.lemma(p.add_zero, &[zero]);
        let (_, z_proof) = rchain(
            d,
            z_raw,
            &[
                (mid_z1, step_z1),
                (mid_z2, step_z2),
                (mid_z3, step_z3),
                (zero, az_z),
            ],
        );

        // --- combine: (a*X - b*Y) + c*Z, a=1, b=0, c=0 ------------------------
        let ax = rmul(d, one, x_raw);
        let by = rmul(d, zero, y_raw);
        let neg_by = rneg(d, by);
        let ax_by = radd(d, ax, neg_by);
        let cz = rmul(d, zero, z_raw);
        let top = radd(d, ax_by, cz); // = lhs, raw unfolded

        let ax_mid = rmul(d, one, one);
        let step_ax1 = rcongr(d, x_raw, one, x_proof, &|d, t| rmul(d, one, t));
        let mo_ax = d.lemma(p.mul_one, &[one]);
        let (_, ax_proof) = rchain(d, ax, &[(ax_mid, step_ax1), (one, mo_ax)]);

        let by_mid = rmul(d, zero, zero);
        let step_by1 = rcongr(d, y_raw, zero, y_proof, &|d, t| rmul(d, zero, t));
        let mz_by = d.lemma(p.mul_zero, &[zero]);
        let (_, by_proof) = rchain(d, by, &[(by_mid, step_by1), (zero, mz_by)]);

        let cz_mid = rmul(d, zero, zero);
        let step_cz1 = rcongr(d, z_raw, zero, z_proof, &|d, t| rmul(d, zero, t));
        let mz_cz = d.lemma(p.mul_zero, &[zero]);
        let (_, cz_proof) = rchain(d, cz, &[(cz_mid, step_cz1), (zero, mz_cz)]);

        // top = add(add(ax, neg(by)), cz)
        let step1 = rcongr(d, ax, one, ax_proof, &|d, t| {
            let n = rneg(d, by);
            let inner = radd(d, t, n);
            radd(d, inner, cz)
        });
        let mid1 = {
            let neg_by = rneg(d, by);
            let inner = radd(d, one, neg_by);
            radd(d, inner, cz)
        };
        let step2 = rcongr(d, by, zero, by_proof, &|d, t| {
            let n = rneg(d, t);
            let inner = radd(d, one, n);
            radd(d, inner, cz)
        });
        let mid2 = {
            let neg_zero2 = rneg(d, zero);
            let inner = radd(d, one, neg_zero2);
            radd(d, inner, cz)
        };
        let neg_zero_mid = rneg(d, zero);
        let step3 = rcongr(d, neg_zero_mid, zero, nz_x, &|d, t| {
            let inner = radd(d, one, t);
            radd(d, inner, cz)
        });
        let mid3 = {
            let inner = radd(d, one, zero);
            radd(d, inner, cz)
        };
        let az1 = d.lemma(p.add_zero, &[one]); // one+zero = one
        let one_plus_zero = radd(d, one, zero);
        let step4 = rcongr(d, one_plus_zero, one, az1, &|d, t| radd(d, t, cz));
        let mid4 = radd(d, one, cz);
        let step5 = rcongr(d, cz, zero, cz_proof, &|d, t| radd(d, one, t));
        let mid5 = radd(d, one, zero);
        let step6 = d.lemma(p.add_zero, &[one]); // one+zero = one

        let (_, proof) = rchain(
            d,
            top,
            &[
                (mid1, step1),
                (mid2, step2),
                (mid3, step3),
                (mid4, step4),
                (mid5, step5),
                (one, step6),
            ],
        );
        (stmt, proof)
    })
}

/// `Rat.det3_cofactor_row1 : ∀ a b c d e f g h i,`
/// `det3 a b c d e f g h i = (a * det2 e f h i - b * det2 d f g i) + c * det2 d e g h`
///
/// Cofactor expansion along the first row. `Rat.det3` was *defined* as
/// exactly this expanded raw arithmetic ([`declare_det3_def`]), and each
/// `Rat.det2 p q r s` δ-unfolds to `p*s - q*r`, so both sides of this
/// statement δ/β-reduce to the identical term — `Eq.refl` closes it, no
/// ring-law rewriting needed.
fn declare_det3_cofactor_row1(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det3_cofactor_row1, 9, &|d, v| {
        let (a, b, c, dd, e, f, g, h, i) = (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]);
        let lhs = rdet3(d, p, a, b, c, dd, e, f, g, h, i);

        let det_efhi = rdet2(d, p, e, f, h, i);
        let det_dfgi = rdet2(d, p, dd, f, g, i);
        let det_degh = rdet2(d, p, dd, e, g, h);

        let a_ef = rmul(d, a, det_efhi);
        let b_df = rmul(d, b, det_dfgi);
        let ab = rsub(d, p, a_ef, b_df);
        let c_dg = rmul(d, c, det_degh);
        let rhs = radd(d, ab, c_dg);

        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, lhs);
        (stmt, proof)
    })
}

/// `(k*x - k*y) + k*z = k*((x - y) + z)` — the three-term generalization of
/// [`mul_sub_right_rev`]'s two-term factoring, needed because `Rat.det3`'s raw
/// body is a THREE-term combination (`(a*X - b*Y) + c*Z`), not the two-term
/// `det2` shape `mul_sub_right_rev` was built for. Proved by reusing
/// `mul_sub_right_rev` for the leading two terms, then one more
/// `left_distrib` (reversed) to fold in the third.
/// `(k*x-k*y)+k*z = k*((x-y)+z)`, by `ring::rat::prove_eq_at`
/// (ring-tactic-2, ADR-1582) rather than the hand chain (through
/// [`mul_sub_right_rev`] plus one more `left_distrib`) this file used to
/// carry.
fn factor_k_out_of_three(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    k: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    crate::ring::rat::prove_eq_at(d, &p, &[k, x, y, z], &|d, v| {
        let (k, x, y, z) = (v[0], v[1], v[2], v[3]);
        let kx = rmul(d, k, x);
        let ky = rmul(d, k, y);
        let neg_ky = rneg(d, ky);
        let kx_minus_ky = radd(d, kx, neg_ky);
        let kz = rmul(d, k, z);
        let lhs = radd(d, kx_minus_ky, kz);
        let neg_y = rneg(d, y);
        let xy = radd(d, x, neg_y);
        let xy_z = radd(d, xy, z);
        let rhs = rmul(d, k, xy_z);
        (lhs, rhs)
    })
    .expect("factor_k_out_of_three: (k*x-k*y)+k*z = k*((x-y)+z) is a ring identity")
}

/// `Rat.det3_scale_row : ∀ k a b c d e f g h i,`
/// `det3 (k*a) (k*b) (k*c) d e f g h i = k * det3 a b c d e f g h i`.
///
/// Scaling **row 1** by `k`. Rows 2 and 3 (`d e f g h i`) are untouched by
/// this substitution, so the three 2×2 minors that make up `Rat.det3`'s raw
/// body — `X = e*i-f*h`, `Y = d*i-f*g`, `Z = d*h-e*g` (matching
/// [`declare_det3_cofactor_row1`]'s cofactor form) — are **byte-identical**
/// on both sides: no `det2` law is needed at all, only `mul_assoc` to pull
/// `k` back out of each `(k*row1_entry)*minor` product, and
/// [`factor_k_out_of_three`] to re-fold the resulting three-term
/// `k*X' - k*Y' + k*Z'` into `k*(X'-Y'+Z')`.
///
/// Rows 2 and 3 are deliberately **not** stated here, for the same reason
/// [`declare_det2_scale_row`] only states row 1 for `det2`: scaling row 2
/// (`d e f`) or row 3 (`g h i`) puts the scale factor **inside** each minor
/// instead of outside all three uniformly (row 2's `e,f` are entries of `X`
/// *and* `Z`; row 3's `h,i` are entries of `X` *and* `Y`), so each of the
/// three minors needs its own one- or two-argument scale identity first
/// (`det2_scale_row` directly for the minor where the scaled pair is that
/// minor's own first row; `middle_swap` plus `mul_assoc`, mirroring this
/// file's `X = e*i-f*h -> (k*e)*i - f*(k*h)`-style rewrite, for the minor
/// where the scaled entries are split across both factors) before the same
/// three-term factor-out closes it. That is three more `mul_assoc`/`middle_swap`
/// derivations nested one level deeper than this one, not a different proof
/// technique — sized but not attempted here, in favor of `det3_swap_rows` and
/// `det3_row_add`.
fn declare_det3_scale_row(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det3_scale_row, 10, &|d, v| {
        let (k, a, b, c, dd, e, f, g, h, i) =
            (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9]);
        let ka = rmul(d, k, a);
        let kb = rmul(d, k, b);
        let kc = rmul(d, k, c);
        let lhs = rdet3(d, p, ka, kb, kc, dd, e, f, g, h, i);
        let rhs_inner = rdet3(d, p, a, b, c, dd, e, f, g, h, i);
        let rhs = rmul(d, k, rhs_inner);
        let stmt = req(d, lhs, rhs);

        // The three minors, raw -- identical on both sides (row 1 untouched).
        let ei = rmul(d, e, i);
        let fh = rmul(d, f, h);
        let x_minor = diff(d, ei, fh);
        let di = rmul(d, dd, i);
        let fg = rmul(d, f, g);
        let y_minor = diff(d, di, fg);
        let dh = rmul(d, dd, h);
        let eg = rmul(d, e, g);
        let z_minor = diff(d, dh, eg);

        // start = (ka*X - kb*Y) + kc*Z, the raw unfolding of `lhs`.
        let ka_x = rmul(d, ka, x_minor);
        let kb_y = rmul(d, kb, y_minor);
        let neg_kb_y = rneg(d, kb_y);
        let ka_x_minus_kb_y = radd(d, ka_x, neg_kb_y);
        let kc_z = rmul(d, kc, z_minor);
        let start = radd(d, ka_x_minus_kb_y, kc_z);

        // Step 1: ka*X = k*(a*X).
        let a_x = rmul(d, a, x_minor);
        let k_ax = rmul(d, k, a_x);
        let assoc1 = d.lemma(p.mul_assoc, &[k, a, x_minor]); // (k*a)*X = k*(a*X)
        let step1 = rcongr(d, ka_x, k_ax, assoc1, &|d, t| {
            let n = rneg(d, kb_y);
            let inner = radd(d, t, n);
            radd(d, inner, kc_z)
        });
        let neg_kb_y_1 = rneg(d, kb_y);
        let k_ax_minus_kb_y = radd(d, k_ax, neg_kb_y_1);
        let mid1 = radd(d, k_ax_minus_kb_y, kc_z);

        // Step 2: kb*Y = k*(b*Y).
        let b_y = rmul(d, b, y_minor);
        let k_by = rmul(d, k, b_y);
        let assoc2 = d.lemma(p.mul_assoc, &[k, b, y_minor]); // (k*b)*Y = k*(b*Y)
        let step2 = rcongr(d, kb_y, k_by, assoc2, &|d, t| {
            let n = rneg(d, t);
            let inner = radd(d, k_ax, n);
            radd(d, inner, kc_z)
        });
        let neg_k_by = rneg(d, k_by);
        let k_ax_minus_k_by = radd(d, k_ax, neg_k_by);
        let mid2 = radd(d, k_ax_minus_k_by, kc_z);

        // Step 3: kc*Z = k*(c*Z).
        let c_z = rmul(d, c, z_minor);
        let k_cz = rmul(d, k, c_z);
        let assoc3 = d.lemma(p.mul_assoc, &[k, c, z_minor]); // (k*c)*Z = k*(c*Z)
        let step3 = rcongr(d, kc_z, k_cz, assoc3, &|d, t| {
            let n = rneg(d, k_by);
            let inner = radd(d, k_ax, n);
            radd(d, inner, t)
        });
        let mid3 = radd(d, k_ax_minus_k_by, k_cz);

        // Step 4: (k*(a*X) - k*(b*Y)) + k*(c*Z) = k*((a*X - b*Y) + c*Z).
        let step4 = factor_k_out_of_three(d, p, k, a_x, b_y, c_z);
        let a_x_minus_b_y = diff(d, a_x, b_y);
        let target_inner = radd(d, a_x_minus_b_y, c_z);
        let target = rmul(d, k, target_inner); // = rhs (defeq)

        let (_, proof) = rchain(
            d,
            start,
            &[(mid1, step1), (mid2, step2), (mid3, step3), (target, step4)],
        );
        (stmt, proof)
    })
}

// ============================================================================
// `Rat.det3_ofInt` — the `ofInt` bridge, and concrete determinant examples.
// ============================================================================
//
// Same route as `declare_det2_fib`'s Step B, extracted as a reusable helper
// and applied three times (once per 2×2 minor) instead of once: `Rat.mul`
// and `Rat.add` do not compute for symbolic — or even concrete-literal —
// `Rat` arguments (`Rat.det2_id` above needs eight ring-law steps just for
// `det2 1 0 0 1`), but `Int.add`/`Int.mul` on **concrete** numerals compute
// by β/δ/ι alone (`int_prelude_tests.rs::the_operations_compute_their_normal_forms`).
// So a concrete `Rat.det3` example is proved by casting every entry through
// `Rat.ofInt`, pushing the `Rat` arithmetic down to `Int` arithmetic via the
// ring-homomorphism lemmas, and letting the kernel compute the `Int` side for
// free.

/// Proof that `Rat.det2 (ofInt pi) (ofInt qi) (ofInt ri) (ofInt si)` equals
/// `ofInt minor`, where `minor := isub(imul(pi,si), imul(qi,ri))` — the
/// `Rat.det2` analogue of `declare_det2_fib`'s Step B, generalized from the
/// Fibonacci instance (`pi=si`-independent, `qi=ri`) to arbitrary `Int`
/// arguments. [`declare_det3_ofint`] applies this three times, once per 2×2
/// minor, instead of re-deriving the `ofInt_add`/`ofInt_mul`/`ofInt_neg`
/// bookkeeping each time. Returns `(minor, proof)`; the proof's type is
/// stated at the raw `add`/`neg` unfolding of `Rat.det2`, bridged to the
/// folded `Rat.det2` application by the kernel's own conversion, the same
/// way every proof in this file relies on `Rat.det2`/`Rat.sub` unfolding.
fn det2_ofint_bridge(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pi: ExprId,
    qi: ExprId,
    ri: ExprId,
    si: ExprId,
) -> (ExprId, ExprId) {
    let ps = d.imul(pi, si);
    let qr = d.imul(qi, ri);
    let neg_qr = d.ineg(qr);
    let minor = d.isub(ps, qr);

    let qp = of_int(d, p, pi);
    let qq = of_int(d, p, qi);
    let qri = of_int(d, p, ri);
    let qs = of_int(d, p, si);

    let of_int_minor = of_int(d, p, minor);
    let of_int_ps = of_int(d, p, ps);
    let of_int_neg_qr = of_int(d, p, neg_qr);
    let of_int_qr = of_int(d, p, qr);

    let qp_qs = rmul(d, qp, qs);
    let qq_qr = rmul(d, qq, qri);
    let neg_qq_qr = rneg(d, qq_qr);
    let neg_of_int_qr = rneg(d, of_int_qr);

    let combined = radd(d, of_int_ps, of_int_neg_qr);

    // ofInt(ps + neg_qr) = ofInt(ps) + ofInt(neg_qr) ~ combined (ps+neg_qr is
    // defeq to `minor`'s own isub unfolding, a single delta step).
    let add_lemma = d.lemma(p.of_int_add, &[ps, neg_qr]);

    // ofInt(ps) = qp*qs.
    let mul_ps = d.lemma(p.of_int_mul, &[pi, si]);
    let mid_a = radd(d, qp_qs, of_int_neg_qr);
    let step_a = rcongr(d, of_int_ps, qp_qs, mul_ps, &|d, t| {
        radd(d, t, of_int_neg_qr)
    });

    // ofInt(neg_qr) = neg(ofInt(qr)) = neg(qq*qri).
    let neg_lemma = d.lemma(p.of_int_neg, &[qr]);
    let mul_qr = d.lemma(p.of_int_mul, &[qi, ri]);
    let inner = rcongr(d, of_int_qr, qq_qr, mul_qr, &|d, t| rneg(d, t));
    let step_negqr = rtrans(d, of_int_neg_qr, neg_of_int_qr, neg_qq_qr, neg_lemma, inner);
    let target = radd(d, qp_qs, neg_qq_qr); // = det2 qp qq qri qs, unfolded
    let step_b = rcongr(d, of_int_neg_qr, neg_qq_qr, step_negqr, &|d, t| {
        radd(d, qp_qs, t)
    });

    let (_, combine_proof) = rchain(d, combined, &[(mid_a, step_a), (target, step_b)]);
    let minor_to_target = rtrans(d, of_int_minor, combined, target, add_lemma, combine_proof);
    let target_to_minor = rsymm(d, of_int_minor, target, minor_to_target);

    (minor, target_to_minor)
}

/// `Rat.det3_ofInt : ∀ a b c d e f g h i : Int,`
/// `det3 (ofInt a) (ofInt b) (ofInt c) (ofInt d) (ofInt e) (ofInt f) (ofInt g) (ofInt h) (ofInt i)`
/// `= ofInt ((a*(e*i-f*h) - b*(d*i-f*g)) + c*(d*h-e*g))`
///
/// The bridge a *concrete* `Rat.det3` example needs: cast every entry through
/// `Rat.ofInt`, then this rewrites the whole determinant down to a single
/// `ofInt` of a pure `Int` expression, which the kernel computes for free at
/// concrete literals (unlike `Rat.mul`/`Rat.add`, which never compute — see
/// [`declare_det3_id`]'s eight-step proof even at 0/1 literals). Proved via
/// [`declare_det3_cofactor_row1`] plus three applications of
/// [`det2_ofint_bridge`] (one per 2×2 minor) plus the outer `ofInt_add`.
fn declare_det3_ofint(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    d.int_theorem(p.det3_ofint, 9, &|d, v| {
        let (a, b, c, dd, e, f, g, h, i) = (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]);

        let qa = of_int(d, p, a);
        let qb = of_int(d, p, b);
        let qc = of_int(d, p, c);
        let qd = of_int(d, p, dd);
        let qe = of_int(d, p, e);
        let qf = of_int(d, p, f);
        let qg = of_int(d, p, g);
        let qh = of_int(d, p, h);
        let qi = of_int(d, p, i);

        let lhs = rdet3(d, p, qa, qb, qc, qd, qe, qf, qg, qh, qi);

        // The cofactor form `top`, matching `det3_cofactor_row1`'s RHS exactly.
        let det_efhi = rdet2(d, p, qe, qf, qh, qi);
        let det_dfgi = rdet2(d, p, qd, qf, qg, qi);
        let det_degh = rdet2(d, p, qd, qe, qg, qh);
        let a_ef = rmul(d, qa, det_efhi);
        let b_df = rmul(d, qb, det_dfgi);
        let ab = rsub(d, p, a_ef, b_df);
        let c_dg = rmul(d, qc, det_degh);
        let top = radd(d, ab, c_dg);
        let cofactor_proof = d.lemma(p.det3_cofactor_row1, &[qa, qb, qc, qd, qe, qf, qg, qh, qi]);

        // Bridge each 2x2 minor to an Int value.
        let (x_minor, x_bridge) = det2_ofint_bridge(d, p, e, f, h, i);
        let (y_minor, y_bridge) = det2_ofint_bridge(d, p, dd, f, g, i);
        let (z_minor, z_bridge) = det2_ofint_bridge(d, p, dd, e, g, h);
        let of_x = of_int(d, p, x_minor);
        let of_y = of_int(d, p, y_minor);
        let of_z = of_int(d, p, z_minor);

        // Rewrite the three det2 minors down to ofInt form, one at a time.
        let step_x = rcongr(d, det_efhi, of_x, x_bridge, &|d, t| {
            let am = rmul(d, qa, t);
            let s = rsub(d, p, am, b_df);
            radd(d, s, c_dg)
        });
        let mid_x = {
            let am = rmul(d, qa, of_x);
            let s = rsub(d, p, am, b_df);
            radd(d, s, c_dg)
        };
        let step_y = rcongr(d, det_dfgi, of_y, y_bridge, &|d, t| {
            let am = rmul(d, qa, of_x);
            let bm = rmul(d, qb, t);
            let s = rsub(d, p, am, bm);
            radd(d, s, c_dg)
        });
        let mid_y = {
            let am = rmul(d, qa, of_x);
            let bm = rmul(d, qb, of_y);
            let s = rsub(d, p, am, bm);
            radd(d, s, c_dg)
        };
        let step_z = rcongr(d, det_degh, of_z, z_bridge, &|d, t| {
            let am = rmul(d, qa, of_x);
            let bm = rmul(d, qb, of_y);
            let s = rsub(d, p, am, bm);
            let cm = rmul(d, qc, t);
            radd(d, s, cm)
        });
        let mid_z = {
            let am = rmul(d, qa, of_x);
            let bm = rmul(d, qb, of_y);
            let s = rsub(d, p, am, bm);
            let cm = rmul(d, qc, of_z);
            radd(d, s, cm)
        };

        // Rewrite each qa*ofInt(x_minor) etc. down to ofInt(a*x_minor) etc.
        let ax_int = d.imul(a, x_minor);
        let by_int = d.imul(b, y_minor);
        let cz_int = d.imul(c, z_minor);
        let of_ax = of_int(d, p, ax_int);
        let of_by = of_int(d, p, by_int);
        let of_cz = of_int(d, p, cz_int);

        let mul_a = d.lemma(p.of_int_mul, &[a, x_minor]); // ofInt(ax) = qa*ofX
        let am = rmul(d, qa, of_x);
        let mul_a_rev = rsymm(d, of_ax, am, mul_a);
        let mul_b = d.lemma(p.of_int_mul, &[b, y_minor]); // ofInt(by) = qb*ofY
        let bm = rmul(d, qb, of_y);
        let mul_b_rev = rsymm(d, of_by, bm, mul_b);
        let mul_c = d.lemma(p.of_int_mul, &[c, z_minor]); // ofInt(cz) = qc*ofZ
        let cm = rmul(d, qc, of_z);
        let mul_c_rev = rsymm(d, of_cz, cm, mul_c);

        let step_ax = rcongr(d, am, of_ax, mul_a_rev, &|d, t| {
            let s = rsub(d, p, t, bm);
            radd(d, s, cm)
        });
        let mid_ax = {
            let s = rsub(d, p, of_ax, bm);
            radd(d, s, cm)
        };
        let step_by = rcongr(d, bm, of_by, mul_b_rev, &|d, t| {
            let s = rsub(d, p, of_ax, t);
            radd(d, s, cm)
        });
        let mid_by = {
            let s = rsub(d, p, of_ax, of_by);
            radd(d, s, cm)
        };
        let step_cz = rcongr(d, cm, of_cz, mul_c_rev, &|d, t| {
            let s = rsub(d, p, of_ax, of_by);
            radd(d, s, t)
        });
        let mid_cz = {
            let s = rsub(d, p, of_ax, of_by);
            radd(d, s, of_cz)
        };

        // Final combine: (ofInt(ax) - ofInt(by)) + ofInt(cz) = ofInt(rhs_int).
        let ax_by_int = d.isub(ax_int, by_int);
        let neg_by_int = d.ineg(by_int);
        let ax_by_int_raw = d.iadd(ax_int, neg_by_int); // defeq to ax_by_int
        let rhs_int = d.iadd(ax_by_int, cz_int);
        let rhs_int_raw = d.iadd(ax_by_int_raw, cz_int); // defeq to rhs_int

        let of_ax_by_raw = of_int(d, p, ax_by_int_raw);
        // ofInt(ax + neg(by)) = ofInt(ax) + ofInt(neg(by)) — this proof's
        // *declared* type names the additive-unfolded shape, but `Rat.sub`
        // folded (`sub_ax_by` below) is defeq to that same shape (`Rat.sub`
        // unfolds to `add _ (neg _)`, and `ofInt(neg by) ~ neg(ofInt by)` via
        // `ofInt_neg`), so the kernel accepts this same term at either shape
        // — exactly the reuse `declare_det2_fib` relies on throughout.
        let add1 = d.lemma(p.of_int_add, &[ax_int, neg_by_int]);
        let sub_ax_by = rsub(d, p, of_ax, of_by);
        let of_by_to_sub = rsymm(d, of_ax_by_raw, sub_ax_by, add1);

        let step_final1 = rcongr(d, sub_ax_by, of_ax_by_raw, of_by_to_sub, &|d, t| {
            radd(d, t, of_cz)
        });
        let mid_final1 = radd(d, of_ax_by_raw, of_cz);

        let add2 = d.lemma(p.of_int_add, &[ax_by_int_raw, cz_int]); // ofInt(rhs_raw) = ofInt(ax_by_raw)+ofInt(cz)
        let of_rhs_raw = of_int(d, p, rhs_int_raw);
        let final_to_rhs = rsymm(d, of_rhs_raw, mid_final1, add2);

        let (_, chain_proof) = rchain(
            d,
            top,
            &[
                (mid_x, step_x),
                (mid_y, step_y),
                (mid_z, step_z),
                (mid_ax, step_ax),
                (mid_by, step_by),
                (mid_cz, step_cz),
                (mid_final1, step_final1),
                (of_rhs_raw, final_to_rhs),
            ],
        );

        let lhs_to_top = cofactor_proof;
        let full_proof = rtrans(d, lhs, top, of_rhs_raw, lhs_to_top, chain_proof);

        let of_rhs = of_int(d, p, rhs_int);
        let stmt = req(d, lhs, of_rhs);
        (stmt, full_proof)
    })?;
    Ok(())
}

/// The `Int` numeral `n` (`Int.ofNat`/`Int.negSucc` normal form) — built the
/// same way `int_prelude_tests.rs`'s private `numeral` helper does, needed
/// here for the concrete `det3` examples below (this file's only integer
/// literals besides `Rat.zero`/`Rat.one`).
fn int_numeral(d: &mut IntDev<'_>, n: i64) -> ExprId {
    if n >= 0 {
        let nat = d.num(u32::try_from(n).expect("non-negative"));
        d.of_nat(nat)
    } else {
        let nat = d.num(u32::try_from(-n - 1).expect("negative"));
        d.neg_succ(nat)
    }
}

/// Declare a concrete `det3` example: `Rat.det3` at nine `Int` literals
/// equals `ofInt expected`, proved by `Rat.det3_ofInt` alone — the `Int`
/// side is a pure computation at concrete literals (see
/// [`declare_det3_ofint`]'s doc comment), so no further ring-law rewriting
/// is needed; the kernel's own conversion check does the arithmetic.
#[allow(clippy::too_many_arguments)]
fn declare_det3_example(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    name: NameId,
    entries: [i64; 9],
    expected: i64,
) -> Result<(), KernelError> {
    rat_theorem(d, name, 0, &|d, _v| {
        let ints: Vec<ExprId> = entries.iter().map(|&n| int_numeral(d, n)).collect();
        let qs: Vec<ExprId> = ints.iter().map(|&n| of_int(d, p, n)).collect();
        let lhs = rdet3(
            d, p, qs[0], qs[1], qs[2], qs[3], qs[4], qs[5], qs[6], qs[7], qs[8],
        );
        let expected_int = int_numeral(d, expected);
        let expected_q = of_int(d, p, expected_int);
        let stmt = req(d, lhs, expected_q);

        // `Rat.det3_ofInt` applied at these nine literals has declared type
        // `Eq Rat lhs (ofInt (Sarrus-formula-at-these-literals))`; that
        // Sarrus formula is a closed `Int` expression built from `imul`/
        // `isub`/`iadd` at concrete numerals, which computes to `expected_int`
        // by β/δ/ι alone, so `ofInt(Sarrus…)` is defeq to `expected_q` and
        // this same proof term closes the stated goal too.
        let proof = d.lemma(
            p.det3_ofint,
            &[
                ints[0], ints[1], ints[2], ints[3], ints[4], ints[5], ints[6], ints[7], ints[8],
            ],
        );
        (stmt, proof)
    })
}

/// `Rat.det3_example_generic : det3 (ofInt 1) (ofInt 2) (ofInt 3) (ofInt 4)`
/// `(ofInt 5) (ofInt 6) (ofInt 7) (ofInt 8) (ofInt 10) = ofInt (-3)` — the
/// determinant of `[[1,2,3],[4,5,6],[7,8,10]]`, an odd-permutation instance
/// (so a single sign error in the expansion would NOT still land on `0`,
/// unlike the singular example below).
fn declare_det3_example_generic(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det3_example(
        d,
        p,
        p.det3_example_generic,
        [1, 2, 3, 4, 5, 6, 7, 8, 10],
        -3,
    )
}

/// `Rat.det3_example_diagonal : det3 (ofInt 2) (ofInt 0) (ofInt 0) (ofInt 0)`
/// `(ofInt 3) (ofInt 0) (ofInt 0) (ofInt 0) (ofInt 4) = ofInt 24` — the
/// determinant of `diag(2,3,4)`.
fn declare_det3_example_diagonal(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det3_example(
        d,
        p,
        p.det3_example_diagonal,
        [2, 0, 0, 0, 3, 0, 0, 0, 4],
        24,
    )
}

/// `Rat.det3_example_singular : det3 (ofInt 1) (ofInt 2) (ofInt 3) (ofInt 4)`
/// `(ofInt 5) (ofInt 6) (ofInt 7) (ofInt 8) (ofInt 9) = ofInt 0` — the
/// determinant of `[[1,2,3],[4,5,6],[7,8,9]]` (rows in arithmetic
/// progression, so singular).
fn declare_det3_example_singular(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det3_example(
        d,
        p,
        p.det3_example_singular,
        [1, 2, 3, 4, 5, 6, 7, 8, 9],
        0,
    )
}
