//! `Rat.abs` and the triangle inequality — the piece [`super::decide`]'s
//! module doc named and deliberately left open, and [`super::lattice`]'s
//! deliberately did not need.
//!
//! ## Why this is not another `Int.rec` case split
//!
//! `Rat.max` and `Rat.min` are defined **on the representation** — an
//! `Int.rec` on the sign of the cross-multiplication gap — precisely because
//! deriving them from [`super::RatPrelude::le_or_lt`] would eliminate a
//! `Prop` into `Type`, which this kernel refuses (see `lattice`'s module
//! doc). `Rat.abs` does not have to pay that price a second time: it is
//! **defined as** `Rat.max a (Rat.neg a)`, so it inherits `max`'s branch
//! structure for free, and every law below is an ordinary lattice argument —
//! `max_le`, `le_max_left`, `le_max_right`, `le_antisymm` — never a fresh
//! `Int.rec`.
//!
//! [`super::RatPrelude::zero_le_max_neg`] already exists precisely because
//! `CReal.abs_nonneg` needed `0 ≤ max a (neg a)` one level up without a name
//! for `max a (neg a)` itself; `abs_nonneg` here is that theorem restated
//! through the new constant, unchanged.
//!
//! ## Two lattice facts this file needs and `lattice` deliberately omits
//!
//! `lattice`'s module doc records "no `max a a = a`, no commutativity …
//! nothing consumes them yet". This file is the first consumer of both:
//!
//! - `max_comm : max a b = max b a`, needed to turn `max (neg a) (neg (neg
//!   a))` back into `max a (neg a)` for [`RatPrelude::abs_neg`](super::RatPrelude::abs_neg).
//! - `max_self : max a a = a`, needed for [`RatPrelude::abs_zero`](super::RatPrelude::abs_zero)
//!   (`max 0 (neg 0) = max 0 0 = 0`).
//!
//! Both are one `max_le` + `le_antisymm` argument each and stay private to
//! this file rather than joining `lattice`'s public surface, since nothing
//! else needs them yet.
//!
//! ## The triangle inequality
//!
//! [`RatPrelude::abs_add`](super::RatPrelude::abs_add) — `|a + b| ≤ |a| +
//! |b|` — is `max_le` applied to two `add_le_add` facts:
//!
//! - `a + b ≤ |a| + |b|`, from `le_abs_self` at `a` and `b`.
//! - `−(a + b) ≤ |a| + |b|`, from `neg_le_abs` at `a` and `b`, giving
//!   `−a + −b ≤ |a| + |b|`, then rewritten along `neg_add` (`−(a+b) = −a +
//!   −b`) the same way [`super::group`]'s `bounds_add` rewrites its lower
//!   half — this is in fact the same computation `bounds_add` already does
//!   in its `−b ≤ a ∧ a ≤ b` encoding, restated with a real `abs`.
//!
//! No case split on the sign of `a`, `b`, or `a + b` is needed anywhere in
//! this file.

use super::RatPrelude;
use super::group::rsub;
use super::lattice::rmax;
use super::ops::{
    int_eq_to_nat, num, radd, rat_eq_rewrite, rat_theorem, rat_ty, rchain, rcongr, req,
    req_congr_int, rle, rlt, rmul, rneg, rsymm, rtrans, rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.abs`: above `Rat.max`/`Rat.min` (32, `lattice`'s
/// `LATTICE_HEIGHT`) and above `Rat.neg` (6, in `int_prelude`), so a proof
/// that needs `Rat.abs` to reduce outranks both of the constants it unfolds
/// to.
const ABS_HEIGHT: u16 = 33;

/// `Rat.abs a`.
pub(crate) fn rabs(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.abs, &[a])
}

/// Declare `Rat.abs` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_abs(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_abs_def(d, p)?;
    declare_basic_laws(d, p)?;
    declare_abs_add(d, p)?;
    declare_abs_mul(d, p)?;
    declare_abs_le(d, p)?;
    declare_abs_sub_comm(d, p)
}

/// `Rat.abs a := Rat.max a (Rat.neg a)`.
fn declare_abs_def(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let negated = rneg(d, a);
    let body = rmax(d, p, a, negated);
    let value = d.lam_fv(a_fv, carrier, body);
    let ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.abs,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ABS_HEIGHT),
    })
}

/// `max a b = max b a` — private: `lattice` has no commutativity law because
/// nothing consumed one before this file. Two `max_le` applications (each
/// `max x y ≤ max y x` from `le_max_left`/`le_max_right` swapped) plus
/// `le_antisymm`.
fn max_comm(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let combined_ab = rmax(d, p, a, b);
    let combined_ba = rmax(d, p, b, a);
    let forward = {
        let a_le = d.lemma(p.le_max_right, &[b, a]);
        let b_le = d.lemma(p.le_max_left, &[b, a]);
        d.lemma(p.max_le, &[a, b, combined_ba, a_le, b_le])
    };
    let backward = {
        let b_le = d.lemma(p.le_max_right, &[a, b]);
        let a_le = d.lemma(p.le_max_left, &[a, b]);
        d.lemma(p.max_le, &[b, a, combined_ab, b_le, a_le])
    };
    d.lemma(
        p.le_antisymm,
        &[combined_ab, combined_ba, forward, backward],
    )
}

/// `max a a = a` — private, same reason as [`max_comm`].
fn max_self(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    let combined = rmax(d, p, a, a);
    let upper = {
        let refl1 = d.lemma(p.le_refl, &[a]);
        let refl2 = d.lemma(p.le_refl, &[a]);
        d.lemma(p.max_le, &[a, a, a, refl1, refl2])
    };
    let lower = d.lemma(p.le_max_left, &[a, a]);
    d.lemma(p.le_antisymm, &[combined, a, upper, lower])
}

/// `abs_nonneg`, `le_abs_self`, `neg_le_abs`, `abs_zero`, `abs_neg`.
fn declare_basic_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // abs_nonneg : 0 ≤ abs a — literally `zero_le_max_neg` at `a`.
    rat_theorem(d, p.abs_nonneg, 1, &|d, v| {
        let a = v[0];
        let zero = rzero(d, p);
        let magnitude = rabs(d, p, a);
        let stmt = rle(d, p, zero, magnitude);
        let proof = d.lemma(p.zero_le_max_neg, &[a]);
        (stmt, proof)
    })?;

    // le_abs_self : a ≤ abs a.
    rat_theorem(d, p.le_abs_self, 1, &|d, v| {
        let a = v[0];
        let negated = rneg(d, a);
        let magnitude = rabs(d, p, a);
        let stmt = rle(d, p, a, magnitude);
        let proof = d.lemma(p.le_max_left, &[a, negated]);
        (stmt, proof)
    })?;

    // neg_le_abs : neg a ≤ abs a.
    rat_theorem(d, p.neg_le_abs, 1, &|d, v| {
        let a = v[0];
        let negated = rneg(d, a);
        let magnitude = rabs(d, p, a);
        let stmt = rle(d, p, negated, magnitude);
        let proof = d.lemma(p.le_max_right, &[a, negated]);
        (stmt, proof)
    })?;

    // abs_zero : abs 0 = 0 — max 0 (neg 0) = max 0 0 [neg_zero, congr] = 0
    // [max_self].
    rat_theorem(d, p.abs_zero, 0, &|d, _v| {
        let zero = rzero(d, p);
        let negated_zero = rneg(d, zero);
        let magnitude = rabs(d, p, zero);
        let stmt = req(d, magnitude, zero);

        let start = rmax(d, p, zero, negated_zero);
        let after_collapse = rmax(d, p, zero, zero);
        let collapse = {
            let vanish = d.lemma(p.neg_zero, &[]);
            rcongr(d, negated_zero, zero, vanish, &|d, t| rmax(d, p, zero, t))
        };
        let idempotent = max_self(d, p, zero);
        let (_, proof) = rchain(d, start, &[(after_collapse, collapse), (zero, idempotent)]);
        (stmt, proof)
    })?;

    // abs_neg : abs (neg a) = abs a — max (neg a) (neg (neg a))
    //   = max (neg a) a       [neg_neg, congr]
    //   = max a (neg a)       [max_comm]
    rat_theorem(d, p.abs_neg, 1, &|d, v| {
        let a = v[0];
        let negated = rneg(d, a);
        let double_negated = rneg(d, negated);
        let magnitude_negated = rabs(d, p, negated);
        let magnitude_a = rabs(d, p, a);
        let stmt = req(d, magnitude_negated, magnitude_a);

        let start = rmax(d, p, negated, double_negated);
        let after_cancel = rmax(d, p, negated, a);
        let cancel = {
            let unwind = d.lemma(p.neg_neg, &[a]);
            rcongr(d, double_negated, a, unwind, &|d, t| rmax(d, p, negated, t))
        };
        let swapped = rmax(d, p, a, negated);
        let commute = max_comm(d, p, negated, a);
        let (_, proof) = rchain(d, start, &[(after_cancel, cancel), (swapped, commute)]);
        (stmt, proof)
    })
}

/// `abs_add : |a + b| ≤ |a| + |b|` — the triangle inequality.
fn declare_abs_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.abs_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let sum = radd(d, a, b);
        let magnitude_a = rabs(d, p, a);
        let magnitude_b = rabs(d, p, b);
        let rhs = radd(d, magnitude_a, magnitude_b);
        let magnitude_sum = rabs(d, p, sum);
        let stmt = rle(d, p, magnitude_sum, rhs);

        // upper : a + b ≤ |a| + |b|.
        let upper = {
            let h_a = d.lemma(p.le_abs_self, &[a]);
            let h_b = d.lemma(p.le_abs_self, &[b]);
            d.lemma(p.add_le_add, &[a, magnitude_a, b, magnitude_b, h_a, h_b])
        };

        // lower : −(a + b) ≤ |a| + |b|, via −a + −b ≤ |a| + |b| rewritten
        // along `neg_add : −(a+b) = −a + −b`.
        let negated_a = rneg(d, a);
        let negated_b = rneg(d, b);
        let negated_sum = rneg(d, sum);
        let lower = {
            let h_a = d.lemma(p.neg_le_abs, &[a]);
            let h_b = d.lemma(p.neg_le_abs, &[b]);
            let raw = d.lemma(
                p.add_le_add,
                &[negated_a, magnitude_a, negated_b, magnitude_b, h_a, h_b],
            );
            let negated_pair = radd(d, negated_a, negated_b);
            let split = d.lemma(p.neg_add, &[a, b]);
            let back = rsymm(d, negated_sum, negated_pair, split);
            rat_eq_rewrite(d, negated_pair, negated_sum, back, raw, &|d, x| {
                rle(d, p, x, rhs)
            })
        };

        let proof = d.lemma(p.max_le, &[sum, negated_sum, rhs, upper, lower]);
        (stmt, proof)
    })
}

/// `Rat.abs a = a`, given `0 ≤ a`. Private: only [`declare_abs_mul`] and
/// [`declare_abs_le`] need this and its `_nonpos` twin, not a public law —
/// Mathlib names them `abs_of_nonneg`/`abs_of_nonpos` but nothing else in this
/// development consumes them yet.
///
/// `neg a ≤ a` (via `neg_nonpos_of_nonneg` then `le_trans` through `0`) makes
/// `a` the upper bound `max_le` needs; `le_max_left` is the other half of
/// `le_antisymm`.
fn abs_of_nonneg(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, ha: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let negated = rneg(d, a);
    let combined = rmax(d, p, a, negated);
    let neg_le_zero = d.lemma(p.neg_nonpos_of_nonneg, &[a, ha]);
    let neg_le_a = d.lemma(p.le_trans, &[negated, zero, a, neg_le_zero, ha]);
    let a_le_a = d.lemma(p.le_refl, &[a]);
    let upper = d.lemma(p.max_le, &[a, negated, a, a_le_a, neg_le_a]);
    let lower = d.lemma(p.le_max_left, &[a, negated]);
    d.lemma(p.le_antisymm, &[combined, a, upper, lower])
}

/// `Rat.abs a = neg a`, given `a ≤ 0`. The mirror of [`abs_of_nonneg`]: `a ≤
/// neg a` (via `neg_le_neg` at `(a, 0)`, rewritten along `neg_zero`, then
/// `le_trans`) makes `neg a` the upper bound, and `le_max_right` the other
/// half of `le_antisymm`.
fn abs_of_nonpos(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, ha: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let negated = rneg(d, a);
    let combined = rmax(d, p, a, negated);
    let flipped = d.lemma(p.neg_le_neg, &[a, zero, ha]);
    let negated_zero = rneg(d, zero);
    let collapse = d.lemma(p.neg_zero, &[]);
    let zero_le_negated = rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, x| {
        rle(d, p, x, negated)
    });
    let a_le_negated = d.lemma(p.le_trans, &[a, zero, negated, ha, zero_le_negated]);
    let negated_le_negated = d.lemma(p.le_refl, &[negated]);
    let upper = d.lemma(
        p.max_le,
        &[a, negated, negated, a_le_negated, negated_le_negated],
    );
    let lower = d.lemma(p.le_max_right, &[a, negated]);
    d.lemma(p.le_antisymm, &[combined, negated, upper, lower])
}

/// `0 ≤ neg a`, given `a ≤ 0` — the fact [`abs_of_nonpos`] derives inline and
/// the `a < 0, b < 0` branch of [`declare_abs_mul`] needs a second time, for
/// both factors.
fn zero_le_neg_of_nonpos(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, ha: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let negated = rneg(d, a);
    let flipped = d.lemma(p.neg_le_neg, &[a, zero, ha]);
    let negated_zero = rneg(d, zero);
    let collapse = d.lemma(p.neg_zero, &[]);
    rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, x| {
        rle(d, p, x, negated)
    })
}

/// `Rat.abs_mul : |a * b| = |a| * |b|`.
///
/// **Not** the lattice route `abs_add` takes: `max` does not commute with
/// multiplication without sign information, so this needs a genuine case
/// split. It is a *Prop*-level one — [`RatPrelude::le_or_lt`], nested twice,
/// giving the four sign combinations of `(a, b)` — never a fresh `Int.rec` on
/// a numerator; `Rat.abs`'s only representation-level cost is already paid in
/// `Rat.max`. Each of the four branches is ordinary ordered-ring algebra:
/// `mul_nonneg`/`mul_neg`/`neg_mul`/`neg_neg` once [`abs_of_nonneg`] or
/// [`abs_of_nonpos`] pins down what `|a|`, `|b|` and `|a*b|` actually are.
fn declare_abs_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.abs_mul, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let magnitude_a = rabs(d, p, a);
        let magnitude_b = rabs(d, p, b);
        let product = rmul(d, a, b);
        let magnitude_product = rabs(d, p, product);
        let rhs = rmul(d, magnitude_a, magnitude_b);
        let stmt = req(d, magnitude_product, rhs);

        let case_a = rle(d, p, zero, a);
        let case_na = rlt(d, p, a, zero);
        let decision_a = d.lemma(p.le_or_lt, &[zero, a]);

        let proof = d.or_elim(
            case_a,
            case_na,
            stmt,
            decision_a,
            &|d, ha| {
                let case_b = rle(d, p, zero, b);
                let case_nb = rlt(d, p, b, zero);
                let decision_b = d.lemma(p.le_or_lt, &[zero, b]);
                d.or_elim(
                    case_b,
                    case_nb,
                    stmt,
                    decision_b,
                    &|d, hb| {
                        // 0 ≤ a, 0 ≤ b: |a*b| = a*b = |a|*|b|.
                        let ab_nonneg = d.lemma(p.mul_nonneg, &[a, b, ha, hb]);
                        let abs_ab = abs_of_nonneg(d, p, product, ab_nonneg);
                        let abs_a = abs_of_nonneg(d, p, a, ha);
                        let abs_b = abs_of_nonneg(d, p, b, hb);
                        let mid = rmul(d, a, magnitude_b);
                        let step1 =
                            rcongr(d, magnitude_a, a, abs_a, &|d, t| rmul(d, t, magnitude_b));
                        let step2 = rcongr(d, magnitude_b, b, abs_b, &|d, t| rmul(d, a, t));
                        let (_, rhs_eq_product) = rchain(d, rhs, &[(mid, step1), (product, step2)]);
                        let product_eq_rhs = rsymm(d, rhs, product, rhs_eq_product);
                        rtrans(d, magnitude_product, product, rhs, abs_ab, product_eq_rhs)
                    },
                    &|d, hb| {
                        // 0 ≤ a, b < 0: a*b ≤ 0, so |a*b| = neg(a*b) = |a|*|b|.
                        let hb_le = d.lemma(p.le_of_lt, &[b, zero, hb]);
                        let bound = d.lemma(p.mul_le_mul_of_nonneg_left, &[a, b, zero, ha, hb_le]);
                        let scaled_zero = rmul(d, a, zero);
                        let vanish = d.lemma(p.mul_zero, &[a]);
                        let ab_nonpos =
                            rat_eq_rewrite(d, scaled_zero, zero, vanish, bound, &|d, x| {
                                rle(d, p, product, x)
                            });
                        let abs_ab = abs_of_nonpos(d, p, product, ab_nonpos);
                        let abs_a = abs_of_nonneg(d, p, a, ha);
                        let abs_b = abs_of_nonpos(d, p, b, hb_le);
                        let neg_b = rneg(d, b);
                        let neg_product = rneg(d, product);
                        let mid = rmul(d, a, magnitude_b);
                        let a_neg_b = rmul(d, a, neg_b);
                        let step1 =
                            rcongr(d, magnitude_a, a, abs_a, &|d, t| rmul(d, t, magnitude_b));
                        let step2 = rcongr(d, magnitude_b, neg_b, abs_b, &|d, t| rmul(d, a, t));
                        let step3 = d.lemma(p.mul_neg, &[a, b]);
                        let (_, rhs_eq_neg_product) = rchain(
                            d,
                            rhs,
                            &[(mid, step1), (a_neg_b, step2), (neg_product, step3)],
                        );
                        let neg_product_eq_rhs = rsymm(d, rhs, neg_product, rhs_eq_neg_product);
                        rtrans(
                            d,
                            magnitude_product,
                            neg_product,
                            rhs,
                            abs_ab,
                            neg_product_eq_rhs,
                        )
                    },
                )
            },
            &|d, ha| {
                let ha_le = d.lemma(p.le_of_lt, &[a, zero, ha]);
                let case_b = rle(d, p, zero, b);
                let case_nb = rlt(d, p, b, zero);
                let decision_b = d.lemma(p.le_or_lt, &[zero, b]);
                d.or_elim(
                    case_b,
                    case_nb,
                    stmt,
                    decision_b,
                    &|d, hb| {
                        // a < 0, 0 ≤ b: a*b ≤ 0, so |a*b| = neg(a*b) = |a|*|b|.
                        let bound = d.lemma(p.mul_le_mul_of_nonneg_right, &[a, zero, b, hb, ha_le]);
                        let zero_b = rmul(d, zero, b);
                        let b_zero = rmul(d, b, zero);
                        let commute = d.lemma(p.mul_comm, &[zero, b]);
                        let vanish = d.lemma(p.mul_zero, &[b]);
                        let (_, zero_b_eq_zero) =
                            rchain(d, zero_b, &[(b_zero, commute), (zero, vanish)]);
                        let ab_nonpos =
                            rat_eq_rewrite(d, zero_b, zero, zero_b_eq_zero, bound, &|d, x| {
                                rle(d, p, product, x)
                            });
                        let abs_ab = abs_of_nonpos(d, p, product, ab_nonpos);
                        let abs_a = abs_of_nonpos(d, p, a, ha_le);
                        let abs_b = abs_of_nonneg(d, p, b, hb);
                        let neg_a = rneg(d, a);
                        let neg_product = rneg(d, product);
                        let mid = rmul(d, neg_a, magnitude_b);
                        let neg_a_b = rmul(d, neg_a, b);
                        let step1 = rcongr(d, magnitude_a, neg_a, abs_a, &|d, t| {
                            rmul(d, t, magnitude_b)
                        });
                        let step2 = rcongr(d, magnitude_b, b, abs_b, &|d, t| rmul(d, neg_a, t));
                        let step3 = d.lemma(p.neg_mul, &[a, b]);
                        let (_, rhs_eq_neg_product) = rchain(
                            d,
                            rhs,
                            &[(mid, step1), (neg_a_b, step2), (neg_product, step3)],
                        );
                        let neg_product_eq_rhs = rsymm(d, rhs, neg_product, rhs_eq_neg_product);
                        rtrans(
                            d,
                            magnitude_product,
                            neg_product,
                            rhs,
                            abs_ab,
                            neg_product_eq_rhs,
                        )
                    },
                    &|d, hb| {
                        // a < 0, b < 0: 0 ≤ (neg a)*(neg b) = a*b, so
                        // |a*b| = a*b = |a|*|b|.
                        let hb_le = d.lemma(p.le_of_lt, &[b, zero, hb]);
                        let neg_a = rneg(d, a);
                        let neg_b = rneg(d, b);
                        let neg_a_nonneg = zero_le_neg_of_nonpos(d, p, a, ha_le);
                        let neg_b_nonneg = zero_le_neg_of_nonpos(d, p, b, hb_le);
                        let negs_nonneg =
                            d.lemma(p.mul_nonneg, &[neg_a, neg_b, neg_a_nonneg, neg_b_nonneg]);

                        let negs_product = rmul(d, neg_a, neg_b);
                        let a_neg_b = rmul(d, a, neg_b);
                        let neg_a_neg_b = rneg(d, a_neg_b);
                        let neg_neg_product = {
                            let neg_product = rneg(d, product);
                            rneg(d, neg_product)
                        };
                        let step_a = d.lemma(p.neg_mul, &[a, neg_b]);
                        let step_b = {
                            let inner = d.lemma(p.mul_neg, &[a, b]);
                            let neg_product = rneg(d, product);
                            rcongr(d, a_neg_b, neg_product, inner, &|d, t| rneg(d, t))
                        };
                        let step_c = d.lemma(p.neg_neg, &[product]);
                        let (_, negs_eq_product) = rchain(
                            d,
                            negs_product,
                            &[
                                (neg_a_neg_b, step_a),
                                (neg_neg_product, step_b),
                                (product, step_c),
                            ],
                        );

                        let ab_nonneg = rat_eq_rewrite(
                            d,
                            negs_product,
                            product,
                            negs_eq_product,
                            negs_nonneg,
                            &|d, x| rle(d, p, zero, x),
                        );
                        let abs_ab = abs_of_nonneg(d, p, product, ab_nonneg);
                        let abs_a = abs_of_nonpos(d, p, a, ha_le);
                        let abs_b = abs_of_nonpos(d, p, b, hb_le);
                        let step1 = rcongr(d, magnitude_a, neg_a, abs_a, &|d, t| {
                            rmul(d, t, magnitude_b)
                        });
                        let mid = rmul(d, neg_a, magnitude_b);
                        let step2 = rcongr(d, magnitude_b, neg_b, abs_b, &|d, t| rmul(d, neg_a, t));
                        let (_, rhs_eq_product) = rchain(
                            d,
                            rhs,
                            &[
                                (mid, step1),
                                (negs_product, step2),
                                (product, negs_eq_product),
                            ],
                        );
                        let product_eq_rhs = rsymm(d, rhs, product, rhs_eq_product);
                        rtrans(d, magnitude_product, product, rhs, abs_ab, product_eq_rhs)
                    },
                )
            },
        );
        (stmt, proof)
    })
}

/// `Rat.abs_le_of_le_of_neg_le`, `Rat.le_of_abs_le`, `Rat.neg_le_of_abs_le` —
/// the bridge to ADR-0512's `−q ≤ r ∧ r ≤ q` encoding, in both directions.
/// This development has no `Iff`, so the converse of the introduction rule is
/// two names rather than one.
fn declare_abs_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // abs_le_of_le_of_neg_le : neg b ≤ a → a ≤ b → |a| ≤ b.
    rat_theorem(d, p.abs_le_of_le_of_neg_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let negated_b = rneg(d, b);
        let lower = rle(d, p, negated_b, a);
        let upper = rle(d, p, a, b);
        let magnitude = rabs(d, p, a);
        let conclusion = rle(d, p, magnitude, b);
        let stmt = {
            let inner = d.arrow(upper, conclusion);
            d.arrow(lower, inner)
        };

        let lower_fv = d.fresh_fvar();
        let lower_h = d.kernel().fvar(lower_fv);
        let upper_fv = d.fresh_fvar();
        let upper_h = d.kernel().fvar(upper_fv);

        // neg a ≤ b: from neg b ≤ a via neg_le_neg, rewritten along neg_neg.
        let negated_a = rneg(d, a);
        let flipped = d.lemma(p.neg_le_neg, &[negated_b, a, lower_h]);
        let double_negated_b = rneg(d, negated_b);
        let collapse = d.lemma(p.neg_neg, &[b]);
        let neg_a_le_b = rat_eq_rewrite(d, double_negated_b, b, collapse, flipped, &|d, x| {
            rle(d, p, negated_a, x)
        });
        let body = d.lemma(p.max_le, &[a, negated_a, b, upper_h, neg_a_le_b]);
        let with_upper = d.lam_fv(upper_fv, upper, body);
        let proof = d.lam_fv(lower_fv, lower, with_upper);
        (stmt, proof)
    })?;

    // le_of_abs_le : |a| ≤ b → a ≤ b.
    rat_theorem(d, p.le_of_abs_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let magnitude = rabs(d, p, a);
        let hypothesis = rle(d, p, magnitude, b);
        let conclusion = rle(d, p, a, b);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let self_le = d.lemma(p.le_abs_self, &[a]);
        let body = d.lemma(p.le_trans, &[a, magnitude, b, self_le, h]);
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // neg_le_of_abs_le : |a| ≤ b → neg b ≤ a.
    rat_theorem(d, p.neg_le_of_abs_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let magnitude = rabs(d, p, a);
        let hypothesis = rle(d, p, magnitude, b);
        let negated_b = rneg(d, b);
        let conclusion = rle(d, p, negated_b, a);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let negated_a = rneg(d, a);
        let neg_le = d.lemma(p.neg_le_abs, &[a]);
        let neg_a_le_b = d.lemma(p.le_trans, &[negated_a, magnitude, b, neg_le, h]);
        let flipped = d.lemma(p.neg_le_neg, &[negated_a, b, neg_a_le_b]);
        let double_negated_a = rneg(d, negated_a);
        let collapse = d.lemma(p.neg_neg, &[a]);
        let body = rat_eq_rewrite(d, double_negated_a, a, collapse, flipped, &|d, x| {
            rle(d, p, negated_b, x)
        });
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// `Rat.abs_sub_comm : |a − b| = |b − a|` — `abs_neg` and `neg_sub` alone, no
/// sign case split (unlike [`declare_abs_mul`]): `sub a b` and `sub b a` are
/// already related by `neg`.
fn declare_abs_sub_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.abs_sub_comm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let forward = rsub(d, p, a, b);
        let backward = rsub(d, p, b, a);
        let magnitude_forward = rabs(d, p, forward);
        let magnitude_backward = rabs(d, p, backward);
        let stmt = req(d, magnitude_forward, magnitude_backward);

        let negated_forward = rneg(d, forward);
        let swap = d.lemma(p.neg_sub, &[a, b]); // neg (a-b) = (b-a)
        let backward_eq_negated = rsymm(d, negated_forward, backward, swap);
        let magnitude_negated = rabs(d, p, negated_forward);
        let congr_abs = rcongr(
            d,
            backward,
            negated_forward,
            backward_eq_negated,
            &|d, t| rabs(d, p, t),
        );
        let abs_neg_law = d.lemma(p.abs_neg, &[forward]);
        let (_, proof) = rchain(
            d,
            magnitude_backward,
            &[
                (magnitude_negated, congr_abs),
                (magnitude_forward, abs_neg_law),
            ],
        );
        let final_proof = rsymm(d, magnitude_backward, magnitude_forward, proof);
        (stmt, final_proof)
    })
}

// --- helpers for `CReal.mul_self_abs` --------------------------------------
//
// Neither of the two functions below is a declared Lean theorem — both are
// Rust-level proof-construction helpers, like [`abs_of_nonneg`] itself, kept
// `pub(crate)` (not `rat_theorem`-declared) because nothing outside
// `creal/product.rs`'s `CReal.mul_self_abs` consumes them and a named `Rat`
// lemma would need its own environment-coverage bookkeeping for no reader.

/// `Int.natAbs (Rat.num (Rat.abs q)) = Int.natAbs (Rat.num q)` — what
/// `CReal.bound (CReal.abs x) = CReal.bound x` needs at the index-0 sample,
/// since `CReal.bound y := succ (natAbs (num (seq y 0)))` and
/// `seq (abs x) 0` is definitionally `Rat.abs (seq x 0)`.
///
/// `0 ≤ q` makes `abs q = q` and the claim is congruence through `num`. The
/// `q < 0` branch cannot be: `Rat.abs`/`Rat.max` decide on the *sign of an
/// integer* (an `Int.rec`), so nothing about `abs q` reduces at a *symbolic*
/// `q` without first knowing which side of zero it is on — the same
/// obstruction the module doc's "not another `Int.rec` case split" section
/// describes, paid here at one level up. [`RatPrelude::le_or_lt`] supplies
/// exactly that `Prop`-level disjunction; `abs_of_nonpos` turns it into
/// `abs q = neg q`, and `Rat.num (Rat.neg q)` is `Int.neg (Rat.num q)`
/// **definitionally** (`Rat.neg` builds a fresh `Rat.mk` with that numerator
/// field, and `Rat.num` projects it out by iota), so
/// [`IntPrelude::nat_abs_neg`](crate::int_prelude::IntPrelude::nat_abs_neg)
/// closes it with no further `Rat`-level lemma.
pub(crate) fn abs_num_nat_abs_eq(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let magnitude = rabs(d, p, q);
    let num_q = num(d, q);
    let num_abs_q = num(d, magnitude);
    let nat_abs_q = d.const_app(p.int.nat_abs, &[num_q]);
    let nat_abs_abs_q = d.const_app(p.int.nat_abs, &[num_abs_q]);
    let stmt = NatOps::eq(d, nat_abs_abs_q, nat_abs_q);

    let case_pos = rle(d, p, zero, q);
    let case_neg = rlt(d, p, q, zero);
    let decision = d.lemma(p.le_or_lt, &[zero, q]);

    d.or_elim(
        case_pos,
        case_neg,
        stmt,
        decision,
        &|d, hq| {
            let habs = abs_of_nonneg(d, p, q, hq);
            let hnum = req_congr_int(d, magnitude, q, habs, &|d, x| num(d, x));
            int_eq_to_nat(d, num_abs_q, num_q, hnum, &|d, x| {
                d.const_app(p.int.nat_abs, &[x])
            })
        },
        &|d, hq| {
            let hq_le = d.lemma(p.le_of_lt, &[q, zero, hq]);
            let habs = abs_of_nonpos(d, p, q, hq_le);
            let neg_q = rneg(d, q);
            let hnum = req_congr_int(d, magnitude, neg_q, habs, &|d, x| num(d, x));
            // `hnum`'s actual type mentions `num neg_q`; `neg_num_q` below is
            // definitionally that same term (`Rat.neg`'s `Mk` unfolds and
            // `Rat.num` projects it out by iota), so using `hnum` at this
            // differently-*written* but defeq type is exactly the technique
            // `declare_of_rat_mul`'s `rrefl(d, scalar)` already relies on.
            let neg_num_q = d.ineg(num_q);
            let nat_abs_neg_num_q = d.const_app(p.int.nat_abs, &[neg_num_q]);
            let step1 = int_eq_to_nat(d, num_abs_q, neg_num_q, hnum, &|d, x| {
                d.const_app(p.int.nat_abs, &[x])
            });
            let step2 = d.lemma(p.int.nat_abs_neg, &[num_q]);
            NatOps::trans(d, nat_abs_abs_q, nat_abs_neg_num_q, nat_abs_q, step1, step2)
        },
    )
}

/// `Rat.mul (Rat.abs q) (Rat.abs q) = Rat.mul q q` — the per-index identity
/// `CReal.mul_self_abs` needs once both products sample at the same index.
///
/// `0 ≤ q`: `abs q = q`, congruence closes it. `q < 0`: `abs q = neg q`, and
/// `neg q * neg q = q * q` is exactly [`declare_abs_mul`]'s fourth branch
/// (`neg_a * neg_b = a * b` via `neg_mul`/`mul_neg`/`neg_neg`) specialised to
/// `a = b = q`.
pub(crate) fn mul_self_abs_rat(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId) -> ExprId {
    let zero = rzero(d, p);
    let magnitude = rabs(d, p, q);
    let lhs = rmul(d, magnitude, magnitude);
    let rhs = rmul(d, q, q);
    let stmt = req(d, lhs, rhs);

    let case_pos = rle(d, p, zero, q);
    let case_neg = rlt(d, p, q, zero);
    let decision = d.lemma(p.le_or_lt, &[zero, q]);

    d.or_elim(
        case_pos,
        case_neg,
        stmt,
        decision,
        &|d, hq| {
            let habs = abs_of_nonneg(d, p, q, hq);
            let mid = rmul(d, q, magnitude);
            let step1 = rcongr(d, magnitude, q, habs, &|d, t| rmul(d, t, magnitude));
            let step2 = rcongr(d, magnitude, q, habs, &|d, t| rmul(d, q, t));
            let (_, chain) = rchain(d, lhs, &[(mid, step1), (rhs, step2)]);
            chain
        },
        &|d, hq| {
            let hq_le = d.lemma(p.le_of_lt, &[q, zero, hq]);
            let habs = abs_of_nonpos(d, p, q, hq_le);
            let neg_q = rneg(d, q);
            let mid = rmul(d, neg_q, magnitude);
            let negs_product = rmul(d, neg_q, neg_q);
            let q_neg_q = rmul(d, q, neg_q);
            let neg_q_neg_q = rneg(d, q_neg_q);
            let neg_neg_product = {
                let neg_rhs = rneg(d, rhs);
                rneg(d, neg_rhs)
            };
            let step_a = d.lemma(p.neg_mul, &[q, neg_q]);
            let step_b = {
                let inner = d.lemma(p.mul_neg, &[q, q]);
                let neg_rhs = rneg(d, rhs);
                rcongr(d, q_neg_q, neg_rhs, inner, &|d, t| rneg(d, t))
            };
            let step_c = d.lemma(p.neg_neg, &[rhs]);
            let (_, negs_eq_rhs) = rchain(
                d,
                negs_product,
                &[
                    (neg_q_neg_q, step_a),
                    (neg_neg_product, step_b),
                    (rhs, step_c),
                ],
            );
            let step1 = rcongr(d, magnitude, neg_q, habs, &|d, t| rmul(d, t, magnitude));
            let step2 = rcongr(d, magnitude, neg_q, habs, &|d, t| rmul(d, neg_q, t));
            let (_, chain) = rchain(
                d,
                lhs,
                &[(mid, step1), (negs_product, step2), (rhs, negs_eq_rhs)],
            );
            chain
        },
    )
}
