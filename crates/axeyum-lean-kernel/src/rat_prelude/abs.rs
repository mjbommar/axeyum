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
use super::lattice::rmax;
use super::ops::{
    radd, rat_eq_rewrite, rat_theorem, rat_ty, rchain, rcongr, req, rle, rneg, rsymm, rzero,
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
    declare_abs_add(d, p)
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
