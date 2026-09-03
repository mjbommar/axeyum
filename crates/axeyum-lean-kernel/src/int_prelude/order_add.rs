//! The `Int` order/addition family that follows directly from
//! [`super::order::declare_additive_order`]'s `Int.add_le_add` plus the
//! additive-cancellation identities already proved in `algebra.rs`
//! (`add_neg_cancel_right`) and `modeq.rs` (`cancel_neg_add`,
//! `cancel_neg_add_left`).
//!
//! Nothing here splits on `Int.rec`. Every proof is generic algebra:
//! `add_le_add` instantiated with a `le_refl` on one side gives the
//! left/right monotonicity corollaries, and every cancellation (the `Iff`s,
//! the `sub`-transpositions, and `add_le_of_le_neg_add`) is `add_le_add`
//! applied to shift both sides by a common term, followed by an equality
//! rewrite that collapses the shifted term back down.
//!
//! `Int.sub a b` is `add a (neg b)` (`ReducibilityHint::Regular`,
//! `sub.rs`), so exactly as that module's doc says: state the `c - b`/`c - a`
//! forms **folded** (matching the Mathlib statement being mirrored) and prove
//! against the **unfolded** `add c (neg b)` throughout — `add_declaration`'s
//! defeq check bridges the two at the boundary.

use super::modeq::{cancel_neg_add, cancel_neg_add_left};
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::linarith::int as linarith;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// Shared algebraic cores
// ---------------------------------------------------------------------------

/// `Eq Int (add a (add (neg a) x)) x` — "a + (-a + x) = x", the mirror image
/// of `modeq.rs`'s private `cancel_neg_add_left` (`-a + (a + x) = x`) with `a`
/// and `-a` swapped. Needed because `add_le_of_le_neg_add` and
/// `add_le_of_le_sub_left` both shift on the *left* by `a` itself, not by
/// `-a`.
fn add_cancel_neg_left(d: &mut IntDev<'_>, a: ExprId, x: ExprId) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let neg_a_x = d.iadd(neg_a, x);
    let start = d.iadd(a, neg_a_x);

    let a_neg_a = d.iadd(a, neg_a);
    let mid = d.iadd(a_neg_a, x);
    let assoc = d.const_app(p.add_assoc, &[a, neg_a, x]); // Eq(mid, start)
    let step1 = d.isymm(mid, start, assoc); // Eq(start, mid)

    let zero = d.izero();
    let an = d.const_app(p.add_neg, &[a]); // Eq(a+(-a), 0)
    let zero_x = d.iadd(zero, x);
    let step2 = d.icongr(a_neg_a, zero, an, &|d, t| d.iadd(t, x)); // Eq(mid, zero_x)

    let x_zero = d.iadd(x, zero);
    let comm = d.const_app(p.add_comm, &[zero, x]); // Eq(zero_x, x_zero)
    let az = d.const_app(p.add_zero, &[x]); // Eq(x_zero, x)
    let step3 = d.itrans(zero_x, x_zero, x, comm, az); // Eq(zero_x, x)

    let (_, proof) = d.ichain(start, &[(mid, step1), (zero_x, step2), (x, step3)]);
    proof
}

/// From `h : le b (add (neg a) c)`, derive `le (add a b) c`.
fn le_of_le_neg_add_core(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let refl_a = d.const_app(p.le_refl, &[a]);
    let neg_a = d.ineg(a);
    let neg_a_c = d.iadd(neg_a, c);
    let raw = d.const_app(p.add_le_add, &[a, a, b, neg_a_c, refl_a, h]);
    // raw : a+b <= a+((-a)+c)
    let eq_c = add_cancel_neg_left(d, a, c); // Eq(a+((-a)+c), c)
    let ab = d.iadd(a, b);
    let a_neg_a_c = d.iadd(a, neg_a_c);
    d.int_eq_rewrite(a_neg_a_c, c, eq_c, raw, &|d, x| d.ile(ab, x))
}

/// From `h : le a (add c (neg b))`, derive `le (add a b) c`.
fn le_of_le_sub_right_core(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let refl_b = d.const_app(p.le_refl, &[b]);
    let neg_b = d.ineg(b);
    let c_sub_b = d.iadd(c, neg_b);
    let raw = d.const_app(p.add_le_add, &[a, c_sub_b, b, b, h, refl_b]);
    // raw : a+b <= (c+(-b))+b
    let eq_c = cancel_neg_add(d, c, b); // Eq((c+(-b))+b, c)
    let ab = d.iadd(a, b);
    let c_sub_b_b = d.iadd(c_sub_b, b);
    d.int_eq_rewrite(c_sub_b_b, c, eq_c, raw, &|d, x| d.ile(ab, x))
}

/// From `h : le (add a b) c`, derive `le a (add c (neg b))`.
fn le_sub_of_add_le_core(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let neg_b = d.ineg(b);
    let refl_neg_b = d.const_app(p.le_refl, &[neg_b]);
    let ab = d.iadd(a, b);
    let raw = d.const_app(p.add_le_add, &[ab, c, neg_b, neg_b, h, refl_neg_b]);
    // raw : (a+b)+(-b) <= c+(-b)
    let eq_a = d.const_app(p.add_neg_cancel_right, &[a, b]); // Eq((a+b)+(-b), a)
    let ab_negb = d.iadd(ab, neg_b);
    let c_negb = d.iadd(c, neg_b);
    d.int_eq_rewrite(ab_negb, a, eq_a, raw, &|d, x| d.ile(x, c_negb))
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// `Int.add_le_add_left : a <= b -> forall c, c+a <= c+b` and
/// `Int.add_le_add_right : a <= b -> forall c, a+c <= b+c` — each `add_le_add`
/// with a `le_refl` on the fixed side.
pub(super) fn declare_add_le_add_left_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.add_le_add_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hyp = d.ile(a, b);
        let ca = d.iadd(c, a);
        let cb = d.iadd(c, b);
        let concl = d.ile(ca, cb);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let refl_c = d.const_app(p.le_refl, &[c]);
        let body = d.const_app(p.add_le_add, &[c, c, a, b, refl_c, h]);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    d.int_theorem(p.add_le_add_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hyp = d.ile(a, b);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let concl = d.ile(ac, bc);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let refl_c = d.const_app(p.le_refl, &[c]);
        let body = d.const_app(p.add_le_add, &[a, b, c, c, h, refl_c]);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Int.add_le_add_iff_left : Iff (a+b <= a+c) (b <= c)` and
/// `Int.add_le_add_iff_right : Iff (a+c <= b+c) (a <= b)`.
///
/// `mpr` in each is the left/right monotonicity corollary above; `mp` shifts
/// the hypothesis by the common term's negation on the same side and
/// collapses the result with `cancel_neg_add_left`/`add_neg_cancel_right`.
pub(super) fn declare_add_le_add_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // add_le_add_iff_left : forall b c a, Iff (a+b <= a+c) (b <= c).
    d.int_theorem(p.add_le_add_iff_left, 3, &|d, v| {
        let (b, c, a) = (v[0], v[1], v[2]);
        let ab = d.iadd(a, b);
        let ac = d.iadd(a, c);
        let left_ty = d.ile(ab, ac);
        let right_ty = d.ile(b, c);

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let refl_a = d.const_app(p.le_refl, &[a]);
            let body = d.const_app(p.add_le_add, &[a, a, b, c, refl_a, h]);
            d.lam_fv(h_fv, right_ty, body)
        };

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let neg_a = d.ineg(a);
            let refl_neg_a = d.const_app(p.le_refl, &[neg_a]);
            let raw = d.const_app(p.add_le_add, &[neg_a, neg_a, ab, ac, refl_neg_a, h]);
            // raw : (-a)+(a+b) <= (-a)+(a+c)
            let eq_b = cancel_neg_add_left(d, a, b); // Eq((-a)+(a+b), b)
            let eq_c = cancel_neg_add_left(d, a, c); // Eq((-a)+(a+c), c)
            let neg_a_ab = d.iadd(neg_a, ab);
            let neg_a_ac = d.iadd(neg_a, ac);
            let step1 = d.int_eq_rewrite(neg_a_ab, b, eq_b, raw, &|d, x| d.ile(x, neg_a_ac));
            let step2 = d.int_eq_rewrite(neg_a_ac, c, eq_c, step1, &|d, x| d.ile(b, x));
            d.lam_fv(h_fv, left_ty, step2)
        };

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // add_le_add_iff_right : forall a b c, Iff (a+c <= b+c) (a <= b).
    d.int_theorem(p.add_le_add_iff_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let left_ty = d.ile(ac, bc);
        let right_ty = d.ile(a, b);

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let refl_c = d.const_app(p.le_refl, &[c]);
            let body = d.const_app(p.add_le_add, &[a, b, c, c, h, refl_c]);
            d.lam_fv(h_fv, right_ty, body)
        };

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let neg_c = d.ineg(c);
            let refl_neg_c = d.const_app(p.le_refl, &[neg_c]);
            let raw = d.const_app(p.add_le_add, &[ac, bc, neg_c, neg_c, h, refl_neg_c]);
            // raw : (a+c)+(-c) <= (b+c)+(-c)
            let eq_a = d.const_app(p.add_neg_cancel_right, &[a, c]); // Eq((a+c)+(-c), a)
            let eq_b = d.const_app(p.add_neg_cancel_right, &[b, c]); // Eq((b+c)+(-c), b)
            let ac_negc = d.iadd(ac, neg_c);
            let bc_negc = d.iadd(bc, neg_c);
            let step1 = d.int_eq_rewrite(ac_negc, a, eq_a, raw, &|d, x| d.ile(x, bc_negc));
            let step2 = d.int_eq_rewrite(bc_negc, b, eq_b, step1, &|d, x| d.ile(a, x));
            d.lam_fv(h_fv, left_ty, step2)
        };

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Int.add_le_add_three : a<=d -> b<=e -> c<=f -> (a+b)+c <= (d+e)+f` — two
/// applications of `add_le_add`.
pub(super) fn declare_add_le_add_three(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    linarith::declare(d, &p, p.add_le_add_three, 6, &|d, v| {
        let (a, b, c, dd, e, f) = (v[0], v[1], v[2], v[3], v[4], v[5]);
        let h1_ty = d.ile(a, dd);
        let h2_ty = d.ile(b, e);
        let h3_ty = d.ile(c, f);
        let ab = d.iadd(a, b);
        let de = d.iadd(dd, e);
        let abc = d.iadd(ab, c);
        let def = d.iadd(de, f);
        (vec![h1_ty, h2_ty, h3_ty], d.ile(abc, def))
    })?;
    Ok(())
}

/// `Int.add_le_iff_le_sub : Iff (a+b <= c) (a <= c-b)`.
pub(super) fn declare_add_le_iff_le_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_le_iff_le_sub, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.iadd(a, b);
        let left_ty = d.ile(ab, c);
        let c_sub_b = d.isub(c, b);
        let right_ty = d.ile(a, c_sub_b);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = le_sub_of_add_le_core(d, a, b, c, h);
            d.lam_fv(h_fv, left_ty, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = le_of_le_sub_right_core(d, a, b, c, h);
            d.lam_fv(h_fv, right_ty, body)
        };

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// The three `sub`/`neg`-transposition one-way laws:
/// `Int.add_le_of_le_neg_add`, `Int.add_le_of_le_sub_left`,
/// `Int.add_le_of_le_sub_right` — each `a+b<=c` from a hypothesis putting the
/// gap on the other side, via the matching core above.
pub(super) fn declare_add_le_of_le_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.add_le_of_le_neg_add, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let neg_a = d.ineg(a);
        let neg_a_c = d.iadd(neg_a, c);
        let hyp = d.ile(b, neg_a_c);
        let ab = d.iadd(a, b);
        let concl = d.ile(ab, c);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = le_of_le_neg_add_core(d, a, b, c, h);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    linarith::declare(d, &p, p.add_le_of_le_sub_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let c_sub_a = d.isub(c, a);
        let hyp = d.ile(b, c_sub_a);
        let ab = d.iadd(a, b);
        (vec![hyp], d.ile(ab, c))
    })?;

    d.int_theorem(p.add_le_of_le_sub_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let c_sub_b = d.isub(c, b);
        let hyp = d.ile(a, c_sub_b);
        let ab = d.iadd(a, b);
        let concl = d.ile(ab, c);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = le_of_le_sub_right_core(d, a, b, c, h);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    Ok(())
}
