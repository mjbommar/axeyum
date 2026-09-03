//! The sign-of-a-product family: five `Mathlib v4.30` mirrors that all reduce
//! to one case analysis on the signs of the two factors.
//!
//! `Int.mul_nonneg_of_nonneg_or_nonpos`, `Int.mul_nonneg_iff`,
//! `Int.mul_pos_iff`, `Int.mul_neg_iff` and `Int.mul_nonpos_iff` are the four
//! sign quadrants plus one direct implication. Rather than the shape
//! case-split (`Int.ofNat`/`Int.negSucc`) the rest of `int_prelude` uses for
//! ring identities, these go through the *abstract* sign split
//! `Int.le_total zero a` / `Int.le_total zero b`, because the statements are
//! about arbitrary `a b : Int` and the quadrant a value falls into is what the
//! disjunction is actually about.
//!
//! Six "quadrant" facts feed every one of the five: `Int.mul_nonneg` and
//! `Int.mul_pos` already exist; the other two same-sign facts
//! (`mul_nonneg_of_nonpos_of_nonpos`, `mul_pos_of_neg_of_neg`) go through a
//! sign flip (`x ≤ 0 → 0 ≤ -x`, built from `add_le_add_left` +
//! `add_left_neg` + `add_zero`, no case split) and `(-a)*(-b) = a*b`
//! (`neg_mul_neg`, from `gcd.rs`'s already-derived `neg_mul`/`neg_neg`); the
//! two mixed-sign nonstrict facts fall out of `mul_le_mul_of_nonneg_left`
//! applied at `c := 0` with no neg reasoning at all; the two mixed-sign
//! strict facts route through the nonstrict fact's argument shifted by
//! `mul_pos`/`mul_neg`.
//!
//! The "hard" (`→`) direction of each `Iff` case-splits into the two
//! same-sign and two mixed-sign quadrants. A same-sign quadrant always
//! satisfies the OTHER `Iff`'s nonstrict conclusion unconditionally, so when
//! the hypothesis being decided is the *opposite* strictness from what the
//! quadrant guarantees, the two combine via `Int.le_antisymm` to force the
//! product to be exactly zero, and `Int.mul_eq_zero` decides which factor
//! vanishes; when it is the *same* direction but the hypothesis is *strict*
//! and the quadrant fact is only nonstrict, `Int.eq_em` decides whether the
//! relevant factor is itself zero (which forces the product to zero,
//! contradicting the strict hypothesis) or not (which upgrades the nonstrict
//! sign to strict via `Int.lt_of_le_of_ne`). A mixed-sign quadrant either
//! matches the target disjunct directly or contradicts the hypothesis
//! outright, depending on which of the five theorems is being proved.

use super::gcd::{neg_mul, neg_neg};
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// Generic proof plumbing
// ---------------------------------------------------------------------------

/// `And.intro left right lp rp : And left right`.
fn and_intro(d: &mut IntDev<'_>, left: ExprId, right: ExprId, lp: ExprId, rp: ExprId) -> ExprId {
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// `fun (h : ty) => body(h)`.
fn with_hyp(
    d: &mut IntDev<'_>,
    ty: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fv = d.fresh_fvar();
    let h = d.kernel().fvar(fv);
    let result = body(d, h);
    d.lam_fv(fv, ty, result)
}

/// From `heq : Eq Int x zero`, derive both `le zero x` and `le x zero` — `x`
/// being exactly zero satisfies either half of a sign disjunct.
fn from_eq_zero(d: &mut IntDev<'_>, x: ExprId, heq: ExprId) -> (ExprId, ExprId) {
    let p = d.int();
    let zero = d.izero();
    let flip = d.isymm(x, zero, heq); // Eq zero x
    let refl0 = d.const_app(p.le_refl, &[zero]); // le zero zero
    let nonneg = d.int_eq_rewrite(zero, x, flip, refl0, &|d, t| d.ile(zero, t));
    let nonpos = d.int_eq_rewrite(zero, x, flip, refl0, &|d, t| d.ile(t, zero));
    (nonneg, nonpos)
}

/// `Eq Int (mul zero x) zero`.
///
/// Retired to the `simp` rewrite-chain producer (ADR-1586): `mul_comm`
/// (extra) then `mul_zero` (default). There is no `zero_mul` law in
/// `IntPrelude`.
fn zero_mul_eq_zero(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let p = d.int();
    let defaults = crate::simp::int::default_rules(&p);
    let extra = [crate::simp::int::rule_mul_comm(&p)];
    let rules = crate::simp::int::with_extra(&defaults, &extra);
    let zero = d.izero();
    let zx = d.imul(zero, x);
    crate::simp::int::prove_eq(d, &rules, zx, zero)
        .unwrap_or_else(|e| panic!("zero_mul_eq_zero: simp declined: {e:?}"))
}

/// From `heq : Eq Int zero a`, derive `Eq Int (mul a b) zero`.
fn product_zero_of_left_zero(d: &mut IntDev<'_>, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let zero = d.izero();
    let ab = d.imul(a, b);
    let zero_b = d.imul(zero, b);
    let congr = d.icongr(zero, a, heq, &|d, t| d.imul(t, b)); // Eq zero_b ab
    let zm = zero_mul_eq_zero(d, b); // Eq zero_b zero
    let flip = d.isymm(zero_b, ab, congr); // Eq ab zero_b
    d.itrans(ab, zero_b, zero, flip, zm)
}

/// From `heq : Eq Int zero b`, derive `Eq Int (mul a b) zero`.
fn product_zero_of_right_zero(d: &mut IntDev<'_>, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let ab = d.imul(a, b);
    let a_zero = d.imul(a, zero);
    let congr = d.icongr(zero, b, heq, &|d, t| d.imul(a, t)); // Eq a_zero ab
    let az = d.const_app(p.mul_zero, &[a]); // Eq a_zero zero
    let flip = d.isymm(a_zero, ab, congr); // Eq ab a_zero
    d.itrans(ab, a_zero, zero, flip, az)
}

// ---------------------------------------------------------------------------
// Sign flips: no case split, just `add_le_add_left`/`add_lt_add_of_le_of_lt`
// shifted by `-x` and collapsed by `add_left_neg`/`add_zero`.
// ---------------------------------------------------------------------------

/// From `h : le x zero`, derive `le zero (neg x)`.
fn nonneg_of_nonpos(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let neg_x = d.ineg(x);
    let raw = d.const_app(p.add_le_add_left, &[x, zero, neg_x, h]); // le (neg_x+x) (neg_x+zero)
    let sum1 = d.iadd(neg_x, x);
    let sum2 = d.iadd(neg_x, zero);
    let eq_left = d.const_app(p.add_left_neg, &[x]); // Eq sum1 zero
    let eq_right = d.const_app(p.add_zero, &[neg_x]); // Eq sum2 neg_x
    let step1 = d.int_eq_rewrite(sum1, zero, eq_left, raw, &|d, t| d.ile(t, sum2));
    d.int_eq_rewrite(sum2, neg_x, eq_right, step1, &|d, t| d.ile(zero, t))
}

/// From `h : lt x zero`, derive `lt zero (neg x)`.
fn pos_of_neg(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let neg_x = d.ineg(x);
    let refl_neg_x = d.const_app(p.le_refl, &[neg_x]);
    let raw = d.const_app(
        p.add_lt_add_of_le_of_lt,
        &[neg_x, neg_x, x, zero, refl_neg_x, h],
    ); // lt (neg_x+x) (neg_x+zero)
    let sum1 = d.iadd(neg_x, x);
    let sum2 = d.iadd(neg_x, zero);
    let eq_left = d.const_app(p.add_left_neg, &[x]); // Eq sum1 zero
    let eq_right = d.const_app(p.add_zero, &[neg_x]); // Eq sum2 neg_x
    let step1 = d.int_eq_rewrite(sum1, zero, eq_left, raw, &|d, t| d.ilt(t, sum2));
    d.int_eq_rewrite(sum2, neg_x, eq_right, step1, &|d, t| d.ilt(zero, t))
}

/// From `h : lt zero x`, derive `lt (neg x) zero`.
fn neg_of_pos(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let neg_x = d.ineg(x);
    let refl_neg_x = d.const_app(p.le_refl, &[neg_x]);
    let raw = d.const_app(
        p.add_lt_add_of_le_of_lt,
        &[neg_x, neg_x, zero, x, refl_neg_x, h],
    ); // lt (neg_x+zero) (neg_x+x)
    let sum1 = d.iadd(neg_x, zero);
    let sum2 = d.iadd(neg_x, x);
    let eq_left = d.const_app(p.add_zero, &[neg_x]); // Eq sum1 neg_x
    let eq_right = d.const_app(p.add_left_neg, &[x]); // Eq sum2 zero
    let step1 = d.int_eq_rewrite(sum1, neg_x, eq_left, raw, &|d, t| d.ilt(t, sum2));
    d.int_eq_rewrite(sum2, zero, eq_right, step1, &|d, t| d.ilt(neg_x, t))
}

/// `Eq Int (mul (neg a) (neg b)) (mul a b)`, from `gcd.rs`'s `neg_mul` (`(-a)*c
/// = -(a*c)`), `Int.mul_neg` (`a*(-b) = -(a*b)`) and `neg_neg`
/// (double-negation), chained: `(-a)*(-b) = -(a*(-b)) = -(-(a*b)) = a*b`.
fn neg_mul_neg(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let neg_b = d.ineg(b);
    let start = d.imul(neg_a, neg_b);
    let a_negb = d.imul(a, neg_b);
    let ab = d.imul(a, b);
    let step1 = neg_mul(d, a, neg_b); // Eq start (neg a_negb)
    let next1 = d.ineg(a_negb);
    let mul_neg_proof = d.const_app(p.mul_neg, &[a, b]); // Eq a_negb (neg ab)
    let neg_ab = d.ineg(ab);
    let step2 = d.icongr(a_negb, neg_ab, mul_neg_proof, &|d, t| d.ineg(t)); // Eq next1 next2
    let next2 = d.ineg(neg_ab);
    let step3 = neg_neg(d, ab); // Eq next2 ab
    let (_, proof) = d.ichain(start, &[(next1, step1), (next2, step2), (ab, step3)]);
    proof
}

// ---------------------------------------------------------------------------
// The six sign quadrants.
// ---------------------------------------------------------------------------

/// From `ha : le a zero`, `hb : le b zero`, derive `le zero (mul a b)`.
fn mul_nonneg_of_nonpos_of_nonpos(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let neg_b = d.ineg(b);
    let fa = nonneg_of_nonpos(d, a, ha); // le zero neg_a
    let fb = nonneg_of_nonpos(d, b, hb); // le zero neg_b
    let prod = d.const_app(p.mul_nonneg, &[neg_a, neg_b, fa, fb]); // le zero (mul neg_a neg_b)
    let eq = neg_mul_neg(d, a, b); // Eq (mul neg_a neg_b) (mul a b)
    let lhs = d.imul(neg_a, neg_b);
    let ab = d.imul(a, b);
    d.int_eq_rewrite(lhs, ab, eq, prod, &|d, t| {
        let zero = d.izero();
        d.ile(zero, t)
    })
}

/// From `ha : lt a zero`, `hb : lt b zero`, derive `lt zero (mul a b)`.
fn mul_pos_of_neg_of_neg(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let neg_b = d.ineg(b);
    let fa = pos_of_neg(d, a, ha); // lt zero neg_a
    let fb = pos_of_neg(d, b, hb); // lt zero neg_b
    let prod = d.const_app(p.mul_pos, &[neg_a, neg_b, fa, fb]); // lt zero (mul neg_a neg_b)
    let eq = neg_mul_neg(d, a, b);
    let lhs = d.imul(neg_a, neg_b);
    let ab = d.imul(a, b);
    d.int_eq_rewrite(lhs, ab, eq, prod, &|d, t| {
        let zero = d.izero();
        d.ilt(zero, t)
    })
}

/// From `ha : le zero a`, `hb : le b zero`, derive `le (mul a b) zero` — no
/// neg reasoning needed: `a*b ≤ a*0 = 0` via `mul_le_mul_of_nonneg_left`.
fn mul_nonpos_of_nonneg_of_nonpos(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let raw = d.const_app(p.mul_le_mul_of_nonneg_left, &[a, b, zero, ha, hb]); // le (mul a b) (mul a zero)
    let ab = d.imul(a, b);
    let a_zero = d.imul(a, zero);
    let eq = d.const_app(p.mul_zero, &[a]); // Eq a_zero zero
    d.int_eq_rewrite(a_zero, zero, eq, raw, &|d, t| d.ile(ab, t))
}

/// From `ha : le a zero`, `hb : le zero b`, derive `le (mul a b) zero`, by
/// commuting into [`mul_nonpos_of_nonneg_of_nonpos`].
fn mul_nonpos_of_nonpos_of_nonneg(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let swapped = mul_nonpos_of_nonneg_of_nonpos(d, b, a, hb, ha); // le (mul b a) zero
    let ba = d.imul(b, a);
    let ab = d.imul(a, b);
    let eq = d.const_app(p.mul_comm, &[b, a]); // Eq ba ab
    d.int_eq_rewrite(ba, ab, eq, swapped, &|d, t| d.ile(t, zero))
}

/// From `ha : lt zero a`, `hb : lt b zero`, derive `lt (mul a b) zero`.
fn mul_neg_of_pos_of_neg(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let neg_b = d.ineg(b);
    let fb = pos_of_neg(d, b, hb); // lt zero neg_b
    let prod = d.const_app(p.mul_pos, &[a, neg_b, ha, fb]); // lt zero (mul a neg_b)
    let a_negb = d.imul(a, neg_b);
    let ab = d.imul(a, b);
    let neg_ab = d.ineg(ab);
    let mn = d.const_app(p.mul_neg, &[a, b]); // Eq a_negb neg_ab
    let step1 = d.int_eq_rewrite(a_negb, neg_ab, mn, prod, &|d, t| d.ilt(zero, t)); // lt zero neg_ab
    let flipped = neg_of_pos(d, neg_ab, step1); // lt (neg neg_ab) zero
    let double_neg = d.ineg(neg_ab);
    let nn = neg_neg(d, ab); // Eq double_neg ab
    d.int_eq_rewrite(double_neg, ab, nn, flipped, &|d, t| d.ilt(t, zero))
}

/// From `ha : lt a zero`, `hb : lt zero b`, derive `lt (mul a b) zero`, by
/// commuting into [`mul_neg_of_pos_of_neg`].
fn mul_neg_of_neg_of_pos(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let swapped = mul_neg_of_pos_of_neg(d, b, a, hb, ha); // lt (mul b a) zero
    let ba = d.imul(b, a);
    let ab = d.imul(a, b);
    let eq = d.const_app(p.mul_comm, &[b, a]); // Eq ba ab
    d.int_eq_rewrite(ba, ab, eq, swapped, &|d, t| d.ilt(t, zero))
}

// ---------------------------------------------------------------------------
// Strict-from-nonstrict, at a same-sign quadrant whose product hypothesis is
// strict (`mul_pos_iff`'s forward direction: `0 < a*b` at `0≤a,0≤b` or
// `a≤0,b≤0`).
// ---------------------------------------------------------------------------

/// `0<a*b`, `0≤a` ⊢ `0<a` — if `a=0` the product is `0`, contradicting
/// strict positivity; otherwise `Int.lt_of_le_of_ne` upgrades directly.
fn strict_pos_from_nonneg_left(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(zero, a);
    let eq_branch = d.ieq(zero, a);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[zero, a]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let eq0 = product_zero_of_left_zero(d, a, b, heq); // Eq ab zero
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(zero, t)); // lt zero zero
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[zero, a, ha, hne]),
    )
}

/// `0<a*b`, `0≤b` ⊢ `0<b` — mirror of [`strict_pos_from_nonneg_left`].
fn strict_pos_from_nonneg_right(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    hb: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(zero, b);
    let eq_branch = d.ieq(zero, b);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[zero, b]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let eq0 = product_zero_of_right_zero(d, a, b, heq); // Eq ab zero
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(zero, t));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[zero, b, hb, hne]),
    )
}

/// `0<a*b`, `a≤0` ⊢ `a<0`.
fn strict_neg_from_nonpos_left(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(a, zero);
    let eq_branch = d.ieq(a, zero);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[a, zero]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let flipped = d.isymm(a, zero, heq); // Eq zero a
            let eq0 = product_zero_of_left_zero(d, a, b, flipped); // Eq ab zero
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(zero, t));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[a, zero, ha, hne]),
    )
}

/// `0<a*b`, `b≤0` ⊢ `b<0` — mirror of [`strict_neg_from_nonpos_left`].
fn strict_neg_from_nonpos_right(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    hb: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(b, zero);
    let eq_branch = d.ieq(b, zero);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[b, zero]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let flipped = d.isymm(b, zero, heq); // Eq zero b
            let eq0 = product_zero_of_right_zero(d, a, b, flipped); // Eq ab zero
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(zero, t));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[b, zero, hb, hne]),
    )
}

// ---------------------------------------------------------------------------
// Strict-from-nonstrict, at a MIXED-sign quadrant whose product hypothesis is
// strict (`mul_neg_iff`'s forward direction: `a*b<0` at `0≤a,b≤0` or
// `a≤0,0≤b`). Same shape as the four above, mirrored because the product
// hypothesis now reads `lt ab zero` rather than `lt zero ab`.
// ---------------------------------------------------------------------------

/// `a*b<0`, `0≤a` ⊢ `0<a`.
fn pos_from_nonneg_left_lt(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(zero, a);
    let eq_branch = d.ieq(zero, a);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[zero, a]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let eq0 = product_zero_of_left_zero(d, a, b, heq);
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(t, zero)); // lt zero zero
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[zero, a, ha, hne]),
    )
}

/// `a*b<0`, `b≤0` ⊢ `b<0`.
fn neg_from_nonpos_right_lt(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    hb: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(b, zero);
    let eq_branch = d.ieq(b, zero);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[b, zero]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let flipped = d.isymm(b, zero, heq); // Eq zero b
            let eq0 = product_zero_of_right_zero(d, a, b, flipped);
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(t, zero));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[b, zero, hb, hne]),
    )
}

/// `a*b<0`, `a≤0` ⊢ `a<0`.
fn neg_from_nonpos_left_lt(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(a, zero);
    let eq_branch = d.ieq(a, zero);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[a, zero]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let flipped = d.isymm(a, zero, heq); // Eq zero a
            let eq0 = product_zero_of_left_zero(d, a, b, flipped);
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(t, zero));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[a, zero, ha, hne]),
    )
}

/// `a*b<0`, `0≤b` ⊢ `0<b`.
fn pos_from_nonneg_right_lt(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    hb: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let goal = d.ilt(zero, b);
    let eq_branch = d.ieq(zero, b);
    let ne_branch = d.not(eq_branch);
    let disj = d.const_app(p.eq_em, &[zero, b]);
    d.or_elim(
        eq_branch,
        ne_branch,
        goal,
        disj,
        &|d, heq| {
            let eq0 = product_zero_of_right_zero(d, a, b, heq);
            let ab = d.imul(a, b);
            let rewritten = d.int_eq_rewrite(ab, zero, eq0, h, &|d, t| d.ilt(t, zero));
            let false_pf = d.const_app(p.lt_irrefl, &[zero, rewritten]);
            d.absurd(goal, false_pf)
        },
        &|d, hne| d.const_app(p.lt_of_le_of_ne, &[zero, b, hb, hne]),
    )
}

// ---------------------------------------------------------------------------
// The four `Iff` forward directions.
// ---------------------------------------------------------------------------

/// From `h : le zero (mul a b)`, derive `(0≤a∧0≤b) ∨ (a≤0∧b≤0)`.
fn nonneg_iff_forward(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let ab = d.imul(a, b);
    let a_nonneg = d.ile(zero, a);
    let a_nonpos = d.ile(a, zero);
    let b_nonneg = d.ile(zero, b);
    let b_nonpos = d.ile(b, zero);
    let dis1 = d.and(a_nonneg, b_nonneg);
    let dis2 = d.and(a_nonpos, b_nonpos);
    let goal = d.or(dis1, dis2);
    let split_a = d.const_app(p.le_total, &[zero, a]);

    d.or_elim(
        a_nonneg,
        a_nonpos,
        goal,
        split_a,
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let pair = and_intro(d, a_nonneg, b_nonneg, ha, hb);
                    d.or_inl(dis1, dis2, pair)
                },
                &|d, hb| {
                    let mixed = mul_nonpos_of_nonneg_of_nonpos(d, a, b, ha, hb); // le ab zero
                    let eq_flip = d.const_app(p.le_antisymm, &[zero, ab, h, mixed]); // Eq zero ab
                    let eq = d.isymm(zero, ab, eq_flip); // Eq ab zero
                    let disj = d.const_app(p.mul_eq_zero, &[a, b, eq]);
                    let eq_a = d.ieq(a, zero);
                    let eq_b = d.ieq(b, zero);
                    d.or_elim(
                        eq_a,
                        eq_b,
                        goal,
                        disj,
                        &|d, hae| {
                            let (_, a_np) = from_eq_zero(d, a, hae);
                            let pair = and_intro(d, a_nonpos, b_nonpos, a_np, hb);
                            d.or_inr(dis1, dis2, pair)
                        },
                        &|d, hbe| {
                            let (b_nn, _) = from_eq_zero(d, b, hbe);
                            let pair = and_intro(d, a_nonneg, b_nonneg, ha, b_nn);
                            d.or_inl(dis1, dis2, pair)
                        },
                    )
                },
            )
        },
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let mixed = mul_nonpos_of_nonpos_of_nonneg(d, a, b, ha, hb); // le ab zero
                    let eq_flip = d.const_app(p.le_antisymm, &[zero, ab, h, mixed]);
                    let eq = d.isymm(zero, ab, eq_flip);
                    let disj = d.const_app(p.mul_eq_zero, &[a, b, eq]);
                    let eq_a = d.ieq(a, zero);
                    let eq_b = d.ieq(b, zero);
                    d.or_elim(
                        eq_a,
                        eq_b,
                        goal,
                        disj,
                        &|d, hae| {
                            let (a_nn, _) = from_eq_zero(d, a, hae);
                            let pair = and_intro(d, a_nonneg, b_nonneg, a_nn, hb);
                            d.or_inl(dis1, dis2, pair)
                        },
                        &|d, hbe| {
                            let (_, b_np) = from_eq_zero(d, b, hbe);
                            let pair = and_intro(d, a_nonpos, b_nonpos, ha, b_np);
                            d.or_inr(dis1, dis2, pair)
                        },
                    )
                },
                &|d, hb| {
                    let pair = and_intro(d, a_nonpos, b_nonpos, ha, hb);
                    d.or_inr(dis1, dis2, pair)
                },
            )
        },
    )
}

/// From `h : lt zero (mul a b)`, derive `(0<a∧0<b) ∨ (a<0∧b<0)`.
fn pos_iff_forward(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let ab = d.imul(a, b);
    let a_pos_ty = d.ilt(zero, a);
    let a_neg_ty = d.ilt(a, zero);
    let b_pos_ty = d.ilt(zero, b);
    let b_neg_ty = d.ilt(b, zero);
    let a_nonneg = d.ile(zero, a);
    let a_nonpos = d.ile(a, zero);
    let b_nonneg = d.ile(zero, b);
    let b_nonpos = d.ile(b, zero);
    let dis1 = d.and(a_pos_ty, b_pos_ty);
    let dis2 = d.and(a_neg_ty, b_neg_ty);
    let goal = d.or(dis1, dis2);
    let split_a = d.const_app(p.le_total, &[zero, a]);

    d.or_elim(
        a_nonneg,
        a_nonpos,
        goal,
        split_a,
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let a_pos = strict_pos_from_nonneg_left(d, a, b, ha, h);
                    let b_pos = strict_pos_from_nonneg_right(d, a, b, hb, h);
                    let pair = and_intro(d, a_pos_ty, b_pos_ty, a_pos, b_pos);
                    d.or_inl(dis1, dis2, pair)
                },
                &|d, hb| {
                    let mixed = mul_nonpos_of_nonneg_of_nonpos(d, a, b, ha, hb); // le ab zero
                    let contra = d.const_app(p.lt_of_lt_of_le, &[zero, ab, zero, h, mixed]);
                    let false_pf = d.const_app(p.lt_irrefl, &[zero, contra]);
                    d.absurd(goal, false_pf)
                },
            )
        },
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let mixed = mul_nonpos_of_nonpos_of_nonneg(d, a, b, ha, hb); // le ab zero
                    let contra = d.const_app(p.lt_of_lt_of_le, &[zero, ab, zero, h, mixed]);
                    let false_pf = d.const_app(p.lt_irrefl, &[zero, contra]);
                    d.absurd(goal, false_pf)
                },
                &|d, hb| {
                    let a_neg = strict_neg_from_nonpos_left(d, a, b, ha, h);
                    let b_neg = strict_neg_from_nonpos_right(d, a, b, hb, h);
                    let pair = and_intro(d, a_neg_ty, b_neg_ty, a_neg, b_neg);
                    d.or_inr(dis1, dis2, pair)
                },
            )
        },
    )
}

/// From `h : lt (mul a b) zero`, derive `(0<a∧b<0) ∨ (a<0∧0<b)`.
fn neg_iff_forward(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let ab = d.imul(a, b);
    let a_pos_ty = d.ilt(zero, a);
    let a_neg_ty = d.ilt(a, zero);
    let b_pos_ty = d.ilt(zero, b);
    let b_neg_ty = d.ilt(b, zero);
    let a_nonneg = d.ile(zero, a);
    let a_nonpos = d.ile(a, zero);
    let b_nonneg = d.ile(zero, b);
    let b_nonpos = d.ile(b, zero);
    let dis1 = d.and(a_pos_ty, b_neg_ty);
    let dis2 = d.and(a_neg_ty, b_pos_ty);
    let goal = d.or(dis1, dis2);
    let split_a = d.const_app(p.le_total, &[zero, a]);

    d.or_elim(
        a_nonneg,
        a_nonpos,
        goal,
        split_a,
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let same_sign = d.const_app(p.mul_nonneg, &[a, b, ha, hb]); // le zero ab
                    let contra = d.const_app(p.lt_of_le_of_lt, &[zero, ab, zero, same_sign, h]);
                    let false_pf = d.const_app(p.lt_irrefl, &[zero, contra]);
                    d.absurd(goal, false_pf)
                },
                &|d, hb| {
                    let a_pos = pos_from_nonneg_left_lt(d, a, b, ha, h);
                    let b_neg = neg_from_nonpos_right_lt(d, a, b, hb, h);
                    let pair = and_intro(d, a_pos_ty, b_neg_ty, a_pos, b_neg);
                    d.or_inl(dis1, dis2, pair)
                },
            )
        },
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let a_neg = neg_from_nonpos_left_lt(d, a, b, ha, h);
                    let b_pos = pos_from_nonneg_right_lt(d, a, b, hb, h);
                    let pair = and_intro(d, a_neg_ty, b_pos_ty, a_neg, b_pos);
                    d.or_inr(dis1, dis2, pair)
                },
                &|d, hb| {
                    let same_sign = mul_nonneg_of_nonpos_of_nonpos(d, a, b, ha, hb); // le zero ab
                    let contra = d.const_app(p.lt_of_le_of_lt, &[zero, ab, zero, same_sign, h]);
                    let false_pf = d.const_app(p.lt_irrefl, &[zero, contra]);
                    d.absurd(goal, false_pf)
                },
            )
        },
    )
}

/// From `h : le (mul a b) zero`, derive `(0≤a∧b≤0) ∨ (a≤0∧0≤b)`.
fn nonpos_iff_forward(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let ab = d.imul(a, b);
    let a_nonneg = d.ile(zero, a);
    let a_nonpos = d.ile(a, zero);
    let b_nonneg = d.ile(zero, b);
    let b_nonpos = d.ile(b, zero);
    let dis1 = d.and(a_nonneg, b_nonpos);
    let dis2 = d.and(a_nonpos, b_nonneg);
    let goal = d.or(dis1, dis2);
    let split_a = d.const_app(p.le_total, &[zero, a]);

    d.or_elim(
        a_nonneg,
        a_nonpos,
        goal,
        split_a,
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let same_sign = d.const_app(p.mul_nonneg, &[a, b, ha, hb]); // le zero ab
                    let eq_flip = d.const_app(p.le_antisymm, &[zero, ab, same_sign, h]); // Eq zero ab
                    let eq = d.isymm(zero, ab, eq_flip);
                    let disj = d.const_app(p.mul_eq_zero, &[a, b, eq]);
                    let eq_a = d.ieq(a, zero);
                    let eq_b = d.ieq(b, zero);
                    d.or_elim(
                        eq_a,
                        eq_b,
                        goal,
                        disj,
                        &|d, hae| {
                            let (_, a_np) = from_eq_zero(d, a, hae);
                            let pair = and_intro(d, a_nonpos, b_nonneg, a_np, hb);
                            d.or_inr(dis1, dis2, pair)
                        },
                        &|d, hbe| {
                            let (_, b_np) = from_eq_zero(d, b, hbe);
                            let pair = and_intro(d, a_nonneg, b_nonpos, ha, b_np);
                            d.or_inl(dis1, dis2, pair)
                        },
                    )
                },
                &|d, hb| {
                    let pair = and_intro(d, a_nonneg, b_nonpos, ha, hb);
                    d.or_inl(dis1, dis2, pair)
                },
            )
        },
        &|d, ha| {
            let split_b = d.const_app(p.le_total, &[zero, b]);
            d.or_elim(
                b_nonneg,
                b_nonpos,
                goal,
                split_b,
                &|d, hb| {
                    let pair = and_intro(d, a_nonpos, b_nonneg, ha, hb);
                    d.or_inr(dis1, dis2, pair)
                },
                &|d, hb| {
                    let same_sign = mul_nonneg_of_nonpos_of_nonpos(d, a, b, ha, hb); // le zero ab
                    let eq_flip = d.const_app(p.le_antisymm, &[zero, ab, same_sign, h]);
                    let eq = d.isymm(zero, ab, eq_flip);
                    let disj = d.const_app(p.mul_eq_zero, &[a, b, eq]);
                    let eq_a = d.ieq(a, zero);
                    let eq_b = d.ieq(b, zero);
                    d.or_elim(
                        eq_a,
                        eq_b,
                        goal,
                        disj,
                        &|d, hae| {
                            let (a_nn, _) = from_eq_zero(d, a, hae);
                            let pair = and_intro(d, a_nonneg, b_nonpos, a_nn, hb);
                            d.or_inl(dis1, dis2, pair)
                        },
                        &|d, hbe| {
                            let (b_nn, _) = from_eq_zero(d, b, hbe);
                            let pair = and_intro(d, a_nonpos, b_nonneg, ha, b_nn);
                            d.or_inr(dis1, dis2, pair)
                        },
                    )
                },
            )
        },
    )
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// Declare the five sign-of-a-product mirrors.
///
/// Must run after `ring::declare_ring_all` (needs `Int.mul_eq_zero`), which is
/// why this is the last call in `build_int_prelude_uncached`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed proof term does
/// not check.
pub(super) fn declare_sign_product_theorems(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // mul_nonneg_of_nonneg_or_nonpos :
    //   (0≤a ∧ 0≤b) ∨ (a≤0 ∧ b≤0) → 0 ≤ a*b.
    d.int_theorem(p.mul_nonneg_of_nonneg_or_nonpos, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ab = d.imul(a, b);
        let a_nonneg = d.ile(zero, a);
        let a_nonpos = d.ile(a, zero);
        let b_nonneg = d.ile(zero, b);
        let b_nonpos = d.ile(b, zero);
        let dis1 = d.and(a_nonneg, b_nonneg);
        let dis2 = d.and(a_nonpos, b_nonpos);
        let hyp_ty = d.or(dis1, dis2);
        let concl = d.ile(zero, ab);
        let stmt = d.arrow(hyp_ty, concl);

        let proof = with_hyp(d, hyp_ty, &|d, h| {
            d.or_elim(
                dis1,
                dis2,
                concl,
                h,
                &|d, hpos| {
                    let ha = d.and_left(a_nonneg, b_nonneg, hpos);
                    let hb = d.and_right(a_nonneg, b_nonneg, hpos);
                    d.const_app(p.mul_nonneg, &[a, b, ha, hb])
                },
                &|d, hneg| {
                    let ha = d.and_left(a_nonpos, b_nonpos, hneg);
                    let hb = d.and_right(a_nonpos, b_nonpos, hneg);
                    mul_nonneg_of_nonpos_of_nonpos(d, a, b, ha, hb)
                },
            )
        });
        (stmt, proof)
    })?;

    // mul_nonneg_iff : 0 ≤ a*b ↔ (0≤a ∧ 0≤b) ∨ (a≤0 ∧ b≤0).
    d.int_theorem(p.mul_nonneg_iff, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ab = d.imul(a, b);
        let a_nonneg = d.ile(zero, a);
        let a_nonpos = d.ile(a, zero);
        let b_nonneg = d.ile(zero, b);
        let b_nonpos = d.ile(b, zero);
        let dis1 = d.and(a_nonneg, b_nonneg);
        let dis2 = d.and(a_nonpos, b_nonpos);
        let left_ty = d.ile(zero, ab);
        let right_ty = d.or(dis1, dis2);

        let mp = with_hyp(d, left_ty, &|d, h| nonneg_iff_forward(d, a, b, h));
        let mpr = with_hyp(d, right_ty, &|d, h| {
            d.const_app(p.mul_nonneg_of_nonneg_or_nonpos, &[a, b, h])
        });

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // mul_pos_iff : 0 < a*b ↔ (0<a ∧ 0<b) ∨ (a<0 ∧ b<0).
    d.int_theorem(p.mul_pos_iff, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ab = d.imul(a, b);
        let a_pos = d.ilt(zero, a);
        let a_neg = d.ilt(a, zero);
        let b_pos = d.ilt(zero, b);
        let b_neg = d.ilt(b, zero);
        let dis1 = d.and(a_pos, b_pos);
        let dis2 = d.and(a_neg, b_neg);
        let left_ty = d.ilt(zero, ab);
        let right_ty = d.or(dis1, dis2);

        let mp = with_hyp(d, left_ty, &|d, h| pos_iff_forward(d, a, b, h));
        let mpr = with_hyp(d, right_ty, &|d, h| {
            d.or_elim(
                dis1,
                dis2,
                left_ty,
                h,
                &|d, hpos| {
                    let ha = d.and_left(a_pos, b_pos, hpos);
                    let hb = d.and_right(a_pos, b_pos, hpos);
                    d.const_app(p.mul_pos, &[a, b, ha, hb])
                },
                &|d, hneg| {
                    let ha = d.and_left(a_neg, b_neg, hneg);
                    let hb = d.and_right(a_neg, b_neg, hneg);
                    mul_pos_of_neg_of_neg(d, a, b, ha, hb)
                },
            )
        });

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // mul_neg_iff : a*b < 0 ↔ (0<a ∧ b<0) ∨ (a<0 ∧ 0<b).
    d.int_theorem(p.mul_neg_iff, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ab = d.imul(a, b);
        let a_pos = d.ilt(zero, a);
        let a_neg = d.ilt(a, zero);
        let b_pos = d.ilt(zero, b);
        let b_neg = d.ilt(b, zero);
        let dis1 = d.and(a_pos, b_neg);
        let dis2 = d.and(a_neg, b_pos);
        let left_ty = d.ilt(ab, zero);
        let right_ty = d.or(dis1, dis2);

        let mp = with_hyp(d, left_ty, &|d, h| neg_iff_forward(d, a, b, h));
        let mpr = with_hyp(d, right_ty, &|d, h| {
            d.or_elim(
                dis1,
                dis2,
                left_ty,
                h,
                &|d, h1| {
                    let ha = d.and_left(a_pos, b_neg, h1);
                    let hb = d.and_right(a_pos, b_neg, h1);
                    mul_neg_of_pos_of_neg(d, a, b, ha, hb)
                },
                &|d, h2| {
                    let ha = d.and_left(a_neg, b_pos, h2);
                    let hb = d.and_right(a_neg, b_pos, h2);
                    mul_neg_of_neg_of_pos(d, a, b, ha, hb)
                },
            )
        });

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    // mul_nonpos_iff : a*b ≤ 0 ↔ (0≤a ∧ b≤0) ∨ (a≤0 ∧ 0≤b).
    d.int_theorem(p.mul_nonpos_iff, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ab = d.imul(a, b);
        let a_nonneg = d.ile(zero, a);
        let a_nonpos = d.ile(a, zero);
        let b_nonneg = d.ile(zero, b);
        let b_nonpos = d.ile(b, zero);
        let dis1 = d.and(a_nonneg, b_nonpos);
        let dis2 = d.and(a_nonpos, b_nonneg);
        let left_ty = d.ile(ab, zero);
        let right_ty = d.or(dis1, dis2);

        let mp = with_hyp(d, left_ty, &|d, h| nonpos_iff_forward(d, a, b, h));
        let mpr = with_hyp(d, right_ty, &|d, h| {
            d.or_elim(
                dis1,
                dis2,
                left_ty,
                h,
                &|d, h1| {
                    let ha = d.and_left(a_nonneg, b_nonpos, h1);
                    let hb = d.and_right(a_nonneg, b_nonpos, h1);
                    mul_nonpos_of_nonneg_of_nonpos(d, a, b, ha, hb)
                },
                &|d, h2| {
                    let ha = d.and_left(a_nonpos, b_nonneg, h2);
                    let hb = d.and_right(a_nonpos, b_nonneg, h2);
                    mul_nonpos_of_nonpos_of_nonneg(d, a, b, ha, hb)
                },
            )
        });

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;

    Ok(())
}
