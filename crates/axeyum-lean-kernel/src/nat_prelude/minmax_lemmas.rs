//! The order theory of [`minmax`](super::minmax)'s `Max.max`/`Min.min` — the
//! twelve `Init.Data.Nat.MinMax` / `Init.Data.Nat.Lemmas` mirrors that
//! ADR-1060 opened the vocabulary for but deliberately declared nothing about.
//!
//! # Why these mirrors flip honestly
//!
//! `minmax.rs`'s module doc says any mirror "stated against Mathlib's REAL,
//! typeclass-elaborated `Max.max`/`Min.min` stays `open`". Read as a claim
//! about *typeclass machinery* that is right; read as a claim about the
//! *propositions*, it is too strong, and applying it as a blanket would rule
//! out every already-flipped mirror mentioning `+` (`HAdd.hAdd`/`instAddNat`
//! are exactly as elaborated as `Max.max`/`Nat.instMax`).
//!
//! The criterion is whether Mathlib's `def` is the same FUNCTION. Read at the
//! pinned toolchain (`lean4` v4.30.0, `d024af09`, the source `elan` ships
//! beside the pinned Mathlib `c5ea0035…`) rather than from a paraphrase:
//!
//! - `Init/Prelude.lean:1311` `maxOfLe … where max x y := ite (LE.le x y) y x`
//! - `Init/Prelude.lean:1328` `minOfLe … where min x y := ite (LE.le x y) x y`
//! - `Init/Data/Nat/Basic.lean:873` `instance : Max Nat := maxOfLe`
//! - `Init/Prelude.lean:2088` `instance : Min Nat := minOfLe`
//! - `Init/Data/Nat/Basic.lean:871`
//!   `Nat.min_def : min n m = if n ≤ m then n else m := rfl`
//!
//! So Lean's `max`/`min` at `Nat` ARE `if a ≤ b then b else a` and
//! `if a ≤ b then a else b`, decided by `Nat.decLe` (i.e. `Nat.ble`) — which
//! is [`super::minmax`]'s definition verbatim. Same function, same value at
//! every pair; only the delivery (a class projection at an instance) differs,
//! and that is elaboration, not content.
//!
//! # The two branch cuts, and why `Nat.ble` is the hinge
//!
//! `Max.max a b` is `bool_select_nat (ble a b) b a`, a `Bool.rec` that is
//! STUCK at a symbolic `ble a b`. Nothing about `max` reduces until the
//! boolean is known, so every proof here begins by learning it:
//!
//! | in hand | bridge | rewrite gives |
//! |---|---|---|
//! | `Le a b` | [`NatPrelude::ble_eq_true_of_le`] | `max a b = b`, `min a b = a` |
//! | `Eq Bool (ble a b) false` | — | `max a b = a`, `min a b = b` |
//!
//! The rewrite is an `Eq.rec` at `Bool` in the SYMM direction (`true = ble a b`,
//! not `ble a b = true`): transporting forward would need the goal as its own
//! `refl` case. `Eq (bool_select_nat true b a) b` closes by `Eq.refl b`,
//! because a `Bool.rec` at a LITERAL scrutinee iota-reduces.
//!
//! `Nat.max_eq_left`/`Nat.min_eq_right` take `Le b a`, which does NOT decide
//! `ble a b` — at `a = b` the boolean is `true` and the OTHER branch is
//! selected. They therefore split on
//! [`bool_true_or_false`](super::ops::bool_true_or_false) and close the `true`
//! branch through `le_antisymm`, rather than assuming a false boolean.
//!
//! Above those four, everything is `Nat.le_total` plus one rewrite, so no
//! declaration here performs an induction and none forms a numeral larger
//! than `0`.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Non-dependent `Or.rec` into `goal`.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `h : Eq Nat from_ to_` and `pf : body from_` give `body to_`.
fn subst_nat(
    d: &mut NatDev<'_>,
    from_: ExprId,
    to_: ExprId,
    h: ExprId,
    pf: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let motive = d.eq_motive(from_, body);
    d.transport(from_, motive, pf, to_, h)
}

/// `Max.max a b`.
fn max_of(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let name = p.max_max;
    d.const_app(name, &[a, b])
}

/// `Min.min a b`.
fn min_of(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let name = p.min_min;
    d.const_app(name, &[a, b])
}

/// Rewrite a `bool_select_nat (ble a b) on_true on_false` under a known
/// boolean value. `hb : Eq Bool (ble a b) known`, and `result` is whichever of
/// `on_true`/`on_false` the literal `known` selects — so the `refl` case
/// iota-reduces and the transport lands on the stuck form.
fn select_eq_under(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    known: ExprId,
    result: ExprId,
    hb: ExprId,
) -> ExprId {
    let test = d.ble(a, b);
    let hb_sym = d.bool_symm(test, known, hb);
    let motive = d.bool_eq_motive(known, &|d, x| {
        let sel = d.bool_select_nat(x, on_true, on_false);
        d.eq(sel, result)
    });
    let refl_case = d.refl(result);
    d.bool_transport(known, motive, refl_case, test, hb_sym)
}

/// `hb : Eq Bool (ble a b) true` gives `Eq Nat (Max.max a b) b`.
fn max_of_ble_true(d: &mut NatDev<'_>, a: ExprId, b: ExprId, hb: ExprId) -> ExprId {
    let known = d.bool_true();
    select_eq_under(d, a, b, b, a, known, b, hb)
}

/// `hb : Eq Bool (ble a b) false` gives `Eq Nat (Max.max a b) a`.
fn max_of_ble_false(d: &mut NatDev<'_>, a: ExprId, b: ExprId, hb: ExprId) -> ExprId {
    let known = d.bool_false();
    select_eq_under(d, a, b, b, a, known, a, hb)
}

/// `hb : Eq Bool (ble a b) true` gives `Eq Nat (Min.min a b) a`.
fn min_of_ble_true(d: &mut NatDev<'_>, a: ExprId, b: ExprId, hb: ExprId) -> ExprId {
    let known = d.bool_true();
    select_eq_under(d, a, b, a, b, known, a, hb)
}

/// `hb : Eq Bool (ble a b) false` gives `Eq Nat (Min.min a b) b`.
fn min_of_ble_false(d: &mut NatDev<'_>, a: ExprId, b: ExprId, hb: ExprId) -> ExprId {
    let known = d.bool_false();
    select_eq_under(d, a, b, a, b, known, b, hb)
}

/// Declare the `Nat` min/max order theory.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_minmax_lemmas_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // --- the four rewrite cuts ---------------------------------------------

    // max_eq_right : Le a b -> max a b = b
    d.theorem(p.max_eq_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hb = d.lemma(p.ble_eq_true_of_le, &[a, b, h]);
        let body = max_of_ble_true(d, a, b, hb);
        let lhs = max_of(d, &p, a, b);
        let concl = d.eq(lhs, b);
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    // min_eq_left : Le a b -> min a b = a
    d.theorem(p.min_eq_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hb = d.lemma(p.ble_eq_true_of_le, &[a, b, h]);
        let body = min_of_ble_true(d, a, b, hb);
        let lhs = min_of(d, &p, a, b);
        let concl = d.eq(lhs, a);
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    // max_eq_left : Le b a -> max a b = a. `Le b a` does NOT decide `ble a b`
    // (at `a = b` it is `true`), so split and close the true branch by
    // antisymmetry rather than by a false boolean.
    d.theorem(p.max_eq_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp = d.le(b, a);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lhs = max_of(d, &p, a, b);
        let concl = d.eq(lhs, a);

        let test = d.ble(a, b);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let is_true = d.bool_eq(test, true_);
        let is_false = d.bool_eq(test, false_);
        let split = bool_true_or_false(d, &p, test);

        let true_case = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let a_le_b = d.lemma(p.le_of_ble_eq_true, &[a, b, e]);
            let a_eq_b = d.lemma(p.le_antisymm, &[a, b, a_le_b, h]);
            let max_eq_b = max_of_ble_true(d, a, b, e);
            let b_eq_a = d.symm(a, b, a_eq_b);
            let inner = d.trans(lhs, b, a, max_eq_b, b_eq_a);
            d.lam_fv(e_fv, is_true, inner)
        };
        let false_case = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let inner = max_of_ble_false(d, a, b, e);
            d.lam_fv(e_fv, is_false, inner)
        };
        let body = or_elim(
            d, &p, is_true, is_false, concl, true_case, false_case, split,
        );
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    // min_eq_right : Le b a -> min a b = b. Same split, same reason.
    d.theorem(p.min_eq_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp = d.le(b, a);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lhs = min_of(d, &p, a, b);
        let concl = d.eq(lhs, b);

        let test = d.ble(a, b);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let is_true = d.bool_eq(test, true_);
        let is_false = d.bool_eq(test, false_);
        let split = bool_true_or_false(d, &p, test);

        let true_case = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let a_le_b = d.lemma(p.le_of_ble_eq_true, &[a, b, e]);
            let a_eq_b = d.lemma(p.le_antisymm, &[a, b, a_le_b, h]);
            let min_eq_a = min_of_ble_true(d, a, b, e);
            let inner = d.trans(lhs, a, b, min_eq_a, a_eq_b);
            d.lam_fv(e_fv, is_true, inner)
        };
        let false_case = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let inner = min_of_ble_false(d, a, b, e);
            d.lam_fv(e_fv, is_false, inner)
        };
        let body = or_elim(
            d, &p, is_true, is_false, concl, true_case, false_case, split,
        );
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    // --- the order mirrors --------------------------------------------------

    // le_max_left : Le a (max a b)
    d.theorem(p.le_max_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let m = max_of(d, &p, a, b);
        let goal = d.le(a, m);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.max_eq_right, &[a, b, h]);
            let e_sym = d.symm(m, b, e);
            let inner = subst_nat(d, b, m, e_sym, h, &|d, x| d.le(a, x));
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.max_eq_left, &[a, b, h]);
            let e_sym = d.symm(m, a, e);
            let refl_le = d.lemma(p.le_refl_thm, &[a]);
            let inner = subst_nat(d, a, m, e_sym, refl_le, &|d, x| d.le(a, x));
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // le_max_right : Le b (max a b)
    d.theorem(p.le_max_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let m = max_of(d, &p, a, b);
        let goal = d.le(b, m);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.max_eq_right, &[a, b, h]);
            let e_sym = d.symm(m, b, e);
            let refl_le = d.lemma(p.le_refl_thm, &[b]);
            let inner = subst_nat(d, b, m, e_sym, refl_le, &|d, x| d.le(b, x));
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.max_eq_left, &[a, b, h]);
            let e_sym = d.symm(m, a, e);
            let inner = subst_nat(d, a, m, e_sym, h, &|d, x| d.le(b, x));
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // min_le_left : Le (min a b) a
    d.theorem(p.min_le_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let m = min_of(d, &p, a, b);
        let goal = d.le(m, a);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_left, &[a, b, h]);
            let e_sym = d.symm(m, a, e);
            let refl_le = d.lemma(p.le_refl_thm, &[a]);
            let inner = subst_nat(d, a, m, e_sym, refl_le, &|d, x| d.le(x, a));
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_right, &[a, b, h]);
            let e_sym = d.symm(m, b, e);
            let inner = subst_nat(d, b, m, e_sym, h, &|d, x| d.le(x, a));
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // min_le_right : Le (min a b) b
    d.theorem(p.min_le_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let m = min_of(d, &p, a, b);
        let goal = d.le(m, b);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_left, &[a, b, h]);
            let e_sym = d.symm(m, a, e);
            let inner = subst_nat(d, a, m, e_sym, h, &|d, x| d.le(x, b));
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_right, &[a, b, h]);
            let e_sym = d.symm(m, b, e);
            let refl_le = d.lemma(p.le_refl_thm, &[b]);
            let inner = subst_nat(d, b, m, e_sym, refl_le, &|d, x| d.le(x, b));
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // max_comm : max a b = max b a
    d.theorem(p.max_comm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let lhs = max_of(d, &p, a, b);
        let rhs = max_of(d, &p, b, a);
        let goal = d.eq(lhs, rhs);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e1 = d.lemma(p.max_eq_right, &[a, b, h]);
            let e2 = d.lemma(p.max_eq_left, &[b, a, h]);
            let e2_sym = d.symm(rhs, b, e2);
            let inner = d.trans(lhs, b, rhs, e1, e2_sym);
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e1 = d.lemma(p.max_eq_left, &[a, b, h]);
            let e2 = d.lemma(p.max_eq_right, &[b, a, h]);
            let e2_sym = d.symm(rhs, a, e2);
            let inner = d.trans(lhs, a, rhs, e1, e2_sym);
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // le_min_of_le_of_le : Le a b -> Le a c -> Le a (min b c)
    d.theorem(p.le_min_of_le_of_le, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hyp1 = d.le(a, b);
        let hyp2 = d.le(a, c);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let m = min_of(d, &p, b, c);
        let goal = d.le(a, m);
        let left_ty = d.le(b, c);
        let right_ty = d.le(c, b);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_left, &[b, c, h]);
            let e_sym = d.symm(m, b, e);
            let inner = subst_nat(d, b, m, e_sym, h1, &|d, x| d.le(a, x));
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let e = d.lemma(p.min_eq_right, &[b, c, h]);
            let e_sym = d.symm(m, c, e);
            let inner = subst_nat(d, c, m, e_sym, h2, &|d, x| d.le(a, x));
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[b, c]);
        let body = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        let inner_stmt = d.arrow(hyp2, goal);
        let stmt = d.arrow(hyp1, inner_stmt);
        let inner_proof = d.lam_fv(h2_fv, hyp2, body);
        let proof = d.lam_fv(h1_fv, hyp1, inner_proof);
        (stmt, proof)
    })?;

    // le_min : Le a (min b c) <-> Le a b /\ Le a c
    d.theorem(p.le_min, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let m = min_of(d, &p, b, c);
        let lhs_ty = d.le(a, m);
        let le_ab = d.le(a, b);
        let le_ac = d.le(a, c);
        let rhs_ty = d.const_app(p.logic.and, &[le_ab, le_ac]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let mle_b = d.lemma(p.min_le_left, &[b, c]);
            let mle_c = d.lemma(p.min_le_right, &[b, c]);
            let left = d.lemma(p.le_trans, &[a, m, b, h, mle_b]);
            let right = d.lemma(p.le_trans, &[a, m, c, h, mle_c]);
            let pair = d.const_app(p.logic.and_intro, &[le_ab, le_ac, left, right]);
            d.lam_fv(h_fv, lhs_ty, pair)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let left = and_left(d, le_ab, le_ac, h);
            let right = and_right(d, le_ab, le_ac, h);
            let body = d.lemma(p.le_min_of_le_of_le, &[a, b, c, left, right]);
            d.lam_fv(h_fv, rhs_ty, body)
        };
        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // lt_min : Lt a (min b c) <-> Lt a b /\ Lt a c. `Nat.lt n m` is a
    // Definition unfolding to `Le (succ n) m`, so this IS `le_min` at
    // `succ a` -- exactly as Lean core states it (`Nat.lt_min := Nat.le_min`).
    d.theorem(p.lt_min, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let m = min_of(d, &p, b, c);
        let lhs_ty = d.lt(a, m);
        let lt_ab = d.lt(a, b);
        let lt_ac = d.lt(a, c);
        let rhs_ty = d.const_app(p.logic.and, &[lt_ab, lt_ac]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
        let sa = d.succ(a);
        let proof = d.lemma(p.le_min, &[sa, b, c]);
        (stmt, proof)
    })?;

    // --- translation-invariance --------------------------------------------

    // add_max_add_left : max (a+b) (a+c) = a + max b c
    d.theorem(p.add_max_add_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.add(a, b);
        let ac = d.add(a, c);
        let lhs = max_of(d, &p, ab, ac);
        let m = max_of(d, &p, b, c);
        let rhs = d.add(a, m);
        let goal = d.eq(lhs, rhs);
        let left_ty = d.le(b, c);
        let right_ty = d.le(c, b);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_left, &[a, b, c, h]);
            let e1 = d.lemma(p.max_eq_right, &[ab, ac, hab]);
            let e2 = d.lemma(p.max_eq_right, &[b, c, h]);
            let e2c = d.congr(m, c, e2, &|d, t| d.add(a, t));
            let e2c_sym = d.symm(rhs, ac, e2c);
            let inner = d.trans(lhs, ac, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_left, &[a, c, b, h]);
            let e1 = d.lemma(p.max_eq_left, &[ab, ac, hab]);
            let e2 = d.lemma(p.max_eq_left, &[b, c, h]);
            let e2c = d.congr(m, b, e2, &|d, t| d.add(a, t));
            let e2c_sym = d.symm(rhs, ab, e2c);
            let inner = d.trans(lhs, ab, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[b, c]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // add_min_add_left : min (a+b) (a+c) = a + min b c
    d.theorem(p.add_min_add_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.add(a, b);
        let ac = d.add(a, c);
        let lhs = min_of(d, &p, ab, ac);
        let m = min_of(d, &p, b, c);
        let rhs = d.add(a, m);
        let goal = d.eq(lhs, rhs);
        let left_ty = d.le(b, c);
        let right_ty = d.le(c, b);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_left, &[a, b, c, h]);
            let e1 = d.lemma(p.min_eq_left, &[ab, ac, hab]);
            let e2 = d.lemma(p.min_eq_left, &[b, c, h]);
            let e2c = d.congr(m, b, e2, &|d, t| d.add(a, t));
            let e2c_sym = d.symm(rhs, ab, e2c);
            let inner = d.trans(lhs, ab, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_left, &[a, c, b, h]);
            let e1 = d.lemma(p.min_eq_right, &[ab, ac, hab]);
            let e2 = d.lemma(p.min_eq_right, &[b, c, h]);
            let e2c = d.congr(m, c, e2, &|d, t| d.add(a, t));
            let e2c_sym = d.symm(rhs, ac, e2c);
            let inner = d.trans(lhs, ac, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[b, c]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // add_max_add_right : max (a+c) (b+c) = max a b + c
    d.theorem(p.add_max_add_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let lhs = max_of(d, &p, ac, bc);
        let m = max_of(d, &p, a, b);
        let rhs = d.add(m, c);
        let goal = d.eq(lhs, rhs);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_right, &[c, a, b, h]);
            let e1 = d.lemma(p.max_eq_right, &[ac, bc, hab]);
            let e2 = d.lemma(p.max_eq_right, &[a, b, h]);
            let e2c = d.congr(m, b, e2, &|d, t| d.add(t, c));
            let e2c_sym = d.symm(rhs, bc, e2c);
            let inner = d.trans(lhs, bc, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_right, &[c, b, a, h]);
            let e1 = d.lemma(p.max_eq_left, &[ac, bc, hab]);
            let e2 = d.lemma(p.max_eq_left, &[a, b, h]);
            let e2c = d.congr(m, a, e2, &|d, t| d.add(t, c));
            let e2c_sym = d.symm(rhs, ac, e2c);
            let inner = d.trans(lhs, ac, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // add_min_add_right : min (a+c) (b+c) = min a b + c
    d.theorem(p.add_min_add_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let lhs = min_of(d, &p, ac, bc);
        let m = min_of(d, &p, a, b);
        let rhs = d.add(m, c);
        let goal = d.eq(lhs, rhs);
        let left_ty = d.le(a, b);
        let right_ty = d.le(b, a);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_right, &[c, a, b, h]);
            let e1 = d.lemma(p.min_eq_left, &[ac, bc, hab]);
            let e2 = d.lemma(p.min_eq_left, &[a, b, h]);
            let e2c = d.congr(m, a, e2, &|d, t| d.add(t, c));
            let e2c_sym = d.symm(rhs, ac, e2c);
            let inner = d.trans(lhs, ac, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, left_ty, inner)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.add_le_add_right, &[c, b, a, h]);
            let e1 = d.lemma(p.min_eq_right, &[ac, bc, hab]);
            let e2 = d.lemma(p.min_eq_right, &[a, b, h]);
            let e2c = d.congr(m, b, e2, &|d, t| d.add(t, c));
            let e2c_sym = d.symm(rhs, bc, e2c);
            let inner = d.trans(lhs, bc, rhs, e1, e2c_sym);
            d.lam_fv(h_fv, right_ty, inner)
        };
        let total = d.lemma(p.le_total, &[a, b]);
        let proof = or_elim(d, &p, left_ty, right_ty, goal, left_case, right_case, total);
        (goal, proof)
    })?;

    // --- the two degeneracy characterisations -------------------------------

    // add_eq_max_iff : m + n = max m n <-> m = 0 \/ n = 0
    d.theorem(p.add_eq_max_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let zero = d.zero();
        let sum = d.add(m, n);
        let mx = max_of(d, &p, m, n);
        let lhs_ty = d.eq(sum, mx);
        let m_zero = d.eq(m, zero);
        let n_zero = d.eq(n, zero);
        let rhs_ty = d.const_app(p.logic.or, &[m_zero, n_zero]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let left_ty = d.le(m, n);
            let right_ty = d.le(n, m);
            let left_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let e = d.lemma(p.max_eq_right, &[m, n, g]);
                let sum_eq_n = d.trans(sum, mx, n, h, e);
                let iff_ty = d.lemma(p.add_eq_right, &[m, n]);
                let sum_eq_n_ty = d.eq(sum, n);
                let fwd = iff_forward(d, sum_eq_n_ty, m_zero, iff_ty);
                let got = d.apply(fwd, &[sum_eq_n]);
                let inner = d.const_app(p.logic.or_inl, &[m_zero, n_zero, got]);
                d.lam_fv(g_fv, left_ty, inner)
            };
            let right_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let e = d.lemma(p.max_eq_left, &[m, n, g]);
                let sum_eq_m = d.trans(sum, mx, m, h, e);
                let iff_ty = d.lemma(p.add_eq_left, &[m, n]);
                let sum_eq_m_ty = d.eq(sum, m);
                let fwd = iff_forward(d, sum_eq_m_ty, n_zero, iff_ty);
                let got = d.apply(fwd, &[sum_eq_m]);
                let inner = d.const_app(p.logic.or_inr, &[m_zero, n_zero, got]);
                d.lam_fv(g_fv, right_ty, inner)
            };
            let total = d.lemma(p.le_total, &[m, n]);
            let body = or_elim(
                d, &p, left_ty, right_ty, rhs_ty, left_case, right_case, total,
            );
            d.lam_fv(h_fv, lhs_ty, body)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // m = 0: `0 + n = n = max 0 n`, then transport `0 -> m`.
            let left_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let zn = d.add(zero, n);
                let max_zn = max_of(d, &p, zero, n);
                let zero_add_n = d.lemma(p.zero_add, &[n]);
                let zero_le_n = d.lemma(p.zero_le, &[n]);
                let max_eq = d.lemma(p.max_eq_right, &[zero, n, zero_le_n]);
                let max_sym = d.symm(max_zn, n, max_eq);
                let base = d.trans(zn, n, max_zn, zero_add_n, max_sym);
                let g_sym = d.symm(m, zero, g);
                let inner = subst_nat(d, zero, m, g_sym, base, &|d, x| {
                    let s = d.add(x, n);
                    let mm = max_of(d, &p, x, n);
                    d.eq(s, mm)
                });
                d.lam_fv(g_fv, m_zero, inner)
            };
            // n = 0: `m + 0 = m = max m 0`, then transport `0 -> n`.
            let right_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let mz = d.add(m, zero);
                let max_mz = max_of(d, &p, m, zero);
                let add_zero_m = d.lemma(p.add_zero, &[m]);
                let zero_le_m = d.lemma(p.zero_le, &[m]);
                let max_eq = d.lemma(p.max_eq_left, &[m, zero, zero_le_m]);
                let max_sym = d.symm(max_mz, m, max_eq);
                let base = d.trans(mz, m, max_mz, add_zero_m, max_sym);
                let g_sym = d.symm(n, zero, g);
                let inner = subst_nat(d, zero, n, g_sym, base, &|d, x| {
                    let s = d.add(m, x);
                    let mm = max_of(d, &p, m, x);
                    d.eq(s, mm)
                });
                d.lam_fv(g_fv, n_zero, inner)
            };
            let body = or_elim(d, &p, m_zero, n_zero, lhs_ty, left_case, right_case, h);
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // add_eq_min_iff : m + n = min m n <-> m = 0 /\ n = 0
    d.theorem(p.add_eq_min_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let zero = d.zero();
        let sum = d.add(m, n);
        let mn = min_of(d, &p, m, n);
        let lhs_ty = d.eq(sum, mn);
        let m_zero = d.eq(m, zero);
        let n_zero = d.eq(n, zero);
        let rhs_ty = d.const_app(p.logic.and, &[m_zero, n_zero]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let left_ty = d.le(m, n);
            let right_ty = d.le(n, m);
            // m <= n: min m n = m, so m+n = m gives n = 0; then m <= 0.
            let left_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let e = d.lemma(p.min_eq_left, &[m, n, g]);
                let sum_eq_m = d.trans(sum, mn, m, h, e);
                let iff_ty = d.lemma(p.add_eq_left, &[m, n]);
                let sum_eq_m_ty = d.eq(sum, m);
                let fwd = iff_forward(d, sum_eq_m_ty, n_zero, iff_ty);
                let n_is_zero = d.apply(fwd, &[sum_eq_m]);
                let m_le_zero = subst_nat(d, n, zero, n_is_zero, g, &|d, x| d.le(m, x));
                let zero_le_m = d.lemma(p.zero_le, &[m]);
                let m_is_zero = d.lemma(p.le_antisymm, &[m, zero, m_le_zero, zero_le_m]);
                let inner = d.const_app(p.logic.and_intro, &[m_zero, n_zero, m_is_zero, n_is_zero]);
                d.lam_fv(g_fv, left_ty, inner)
            };
            // n <= m: min m n = n, so m+n = n gives m = 0; then n <= 0.
            let right_case = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let e = d.lemma(p.min_eq_right, &[m, n, g]);
                let sum_eq_n = d.trans(sum, mn, n, h, e);
                let iff_ty = d.lemma(p.add_eq_right, &[m, n]);
                let sum_eq_n_ty = d.eq(sum, n);
                let fwd = iff_forward(d, sum_eq_n_ty, m_zero, iff_ty);
                let m_is_zero = d.apply(fwd, &[sum_eq_n]);
                let n_le_zero = subst_nat(d, m, zero, m_is_zero, g, &|d, x| d.le(n, x));
                let zero_le_n = d.lemma(p.zero_le, &[n]);
                let n_is_zero = d.lemma(p.le_antisymm, &[n, zero, n_le_zero, zero_le_n]);
                let inner = d.const_app(p.logic.and_intro, &[m_zero, n_zero, m_is_zero, n_is_zero]);
                d.lam_fv(g_fv, right_ty, inner)
            };
            let total = d.lemma(p.le_total, &[m, n]);
            let body = or_elim(
                d, &p, left_ty, right_ty, rhs_ty, left_case, right_case, total,
            );
            d.lam_fv(h_fv, lhs_ty, body)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hm = and_left(d, m_zero, n_zero, h);
            let hn = and_right(d, m_zero, n_zero, h);
            // `0 + 0` and `min 0 0` both reduce to `0`: `ble 0 0` is a literal
            // `true`, so the `Bool.rec` iota-reduces and `refl 0` closes it.
            let base = d.refl(zero);
            let hn_sym = d.symm(n, zero, hn);
            let with_n = subst_nat(d, zero, n, hn_sym, base, &|d, x| {
                let s = d.add(zero, x);
                let mm = min_of(d, &p, zero, x);
                d.eq(s, mm)
            });
            let hm_sym = d.symm(m, zero, hm);
            let body = subst_nat(d, zero, m, hm_sym, with_n, &|d, x| {
                let s = d.add(x, n);
                let mm = min_of(d, &p, x, n);
                d.eq(s, mm)
            });
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;

    Ok(())
}
