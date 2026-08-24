//! `Rat.ble` — a **decidable** `≤`, in `Type`, and the bridge back to the
//! `Prop`-valued [`Rat.le`](super::RatPrelude::le).
//!
//! ## Why this file exists
//!
//! [`Rat.le_or_lt`](super::RatPrelude::le_or_lt) already proves ℚ's order is
//! total, but it is `Or`-valued — a `Prop` — and a `Prop` cannot be eliminated
//! into `Type` in this kernel (the same wall
//! [`super::lattice`]'s module documentation describes for `Rat.max`). Nothing
//! that needs to *branch on* a comparison — a search, a bisection, the
//! `natSqrt`-style construction this slice exists to unblock — can pattern
//! match on `Rat.le_or_lt`'s proof term.
//!
//! `Rat.ble` sidesteps the wall exactly the way `Rat.max`/`Rat.min` do: it is
//! not *derived* from the order, it is **defined on the representation**.
//! `Rat.le a b` is `Int.le (num a · den b) (num b · den a)` by definition, so
//! the sign of the gap
//!
//! ```text
//! gap a b := num b · den a  −  num a · den b
//! ```
//!
//! is a fact about an `Int` **constructor** — `Int.ofNat` or `Int.negSucc` —
//! and `Int.rec` eliminates into `Bool` (a `Type`) freely:
//!
//! ```text
//! ble a b := Int.rec (fun _ => Bool) (fun _ => true) (fun _ => false) (gap a b)
//! ```
//!
//! `gap` is exactly [`super::lattice`]'s `cross_gap` — the same one `Rat.max`
//! and `Rat.min` dispatch on — rebuilt locally rather than exposed from that
//! module, so this file stays self-contained.
//!
//! ## The spec, split in two
//!
//! This development has no `Iff`, so `Rat.ble a b = true ↔ Rat.le a b` is two
//! named theorems:
//!
//! - [`RatPrelude::ble_eq_true_of_le`](super::RatPrelude::ble_eq_true_of_le):
//!   `Rat.le a b → Rat.ble a b = true`. Given `h : Rat.le a b`, shift it by
//!   `−(num a · den b)` (`Int.add_le_add` against `Int.le_refl`, then
//!   `Int.add_neg` to collapse the left side to `Int.zero`) to get
//!   `Int.le Int.zero (gap a b)`, then case-split on the gap: the `ofNat`
//!   branch is `Bool.refl true` outright, and the `negSucc` branch is
//!   impossible (`Int.le Int.zero (negSucc m)` ι-reduces to `False`).
//! - [`RatPrelude::le_of_ble_eq_true`](super::RatPrelude::le_of_ble_eq_true):
//!   the converse. Case-split on the gap directly: the `ofNat` branch always
//!   gives `Rat.le a b` (via [`super::lattice`]'s ordered-group shift, rebuilt
//!   locally as [`le_of_nonneg_gap`]), independent of the `Bool` hypothesis;
//!   the `negSucc` branch makes that hypothesis `Eq Bool false true`, which
//!   [`crate::nat_prelude::NatOps::false_true_elim`] discharges into anything.
//!
//! Both case splits use the same trick [`super::lattice::declare_cases`] does
//! for `max_cases`: eliminate `Int.rec` into a motive of the shape
//! `fun z => (gap = z) → …`, then apply it to `Int.refl (gap)` so the elim
//! type-checks against a **symbolic** (non-constructor) scrutinee.
//!
//! [`RatPrelude::ble_refl`](super::RatPrelude::ble_refl),
//! [`RatPrelude::ble_trans`](super::RatPrelude::ble_trans) and
//! [`RatPrelude::ble_total`](super::RatPrelude::ble_total) fall out of the spec
//! plus the already-proved `Prop`-level order
//! ([`RatPrelude::le_refl`](super::RatPrelude::le_refl),
//! [`RatPrelude::le_trans`](super::RatPrelude::le_trans),
//! [`RatPrelude::le_or_lt`](super::RatPrelude::le_or_lt),
//! [`RatPrelude::le_of_lt`](super::RatPrelude::le_of_lt)) with no further case
//! analysis. `ble_total` is the constructively interesting one: it is a
//! genuine *decision* (`Or` of two `Bool` facts), not a classical dichotomy,
//! obtained from `le_or_lt`'s `Prop`-level totality by pushing each branch
//! through the spec.
//!
//! ## What is not here
//!
//! **`Rat.abs`** is not attempted in this file. It is a separate, independent
//! piece of the assigned slice and gets its own module if it lands.

use super::RatPrelude;
use super::ops::{den_z, num, rat_theorem, rat_ty, rle, rlt};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.ble`: above `Rat.le` (30) and the lattice (32), so a
/// proof that needs `Rat.ble` to reduce outranks everything it dispatches on.
const BLE_HEIGHT: u16 = 33;

// --- local rebuilds of `super::lattice`'s representation facts -------------
//
// `super::lattice::cross`/`cross_gap`/`le_of_nonneg_gap` are private to that
// module (by design — see this crate's multi-agent hygiene notes on not
// widening a live file's surface). Rebuilt here rather than exposed, so this
// file has no dependency on `lattice`'s internals staying stable.

/// `num a · den b` — the **left** side of `Rat.le a b`'s cross-multiplication.
fn cross(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let numerator = num(d, a);
    let scale = den_z(d, b);
    d.imul(numerator, scale)
}

/// `num b · den a − num a · den b`, the integer `Rat.ble` dispatches on.
///
/// `Rat.le a b` unfolds to `Int.le (cross a b) (cross b a)`, so this is
/// non-negative exactly when `a ≤ b`.
fn cross_gap(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let left = cross(d, a, b);
    let right = cross(d, b, a);
    let negated = d.ineg(left);
    d.iadd(right, negated)
}

/// `Eq Int (Int.add (Int.add y (Int.neg x)) x) y` — adding `x` back to the gap.
fn int_gap_add(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId) -> ExprId {
    let int = p.int;
    let negated = d.ineg(x);
    let gap = d.iadd(y, negated);
    let start = d.iadd(gap, x);

    let tail = d.iadd(negated, x);
    let regrouped = d.iadd(y, tail);
    let regroup = d.lemma(int.add_assoc, &[y, negated, x]);

    let swapped = d.iadd(x, negated);
    let swap = {
        let commute = d.lemma(int.add_comm, &[negated, x]);
        d.icongr(tail, swapped, commute, &|d, t| d.iadd(y, t))
    };
    let swapped_sum = d.iadd(y, swapped);

    let zero = d.izero();
    let vanish = {
        let cancel = d.lemma(int.add_neg, &[x]);
        d.icongr(swapped, zero, cancel, &|d, t| d.iadd(y, t))
    };
    let padded = d.iadd(y, zero);
    let strip = d.lemma(int.add_zero, &[y]);

    let (_, proof) = d.ichain(
        start,
        &[
            (regrouped, regroup),
            (swapped_sum, swap),
            (padded, vanish),
            (y, strip),
        ],
    );
    proof
}

/// `Eq Int (Int.add Int.zero x) x`.
fn int_zero_add(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let int = p.int;
    let zero = d.izero();
    let start = d.iadd(zero, x);
    let flipped = d.iadd(x, zero);
    let commute = d.lemma(int.add_comm, &[zero, x]);
    let collapse = d.lemma(int.add_zero, &[x]);
    let (_, proof) = d.ichain(start, &[(flipped, commute), (x, collapse)]);
    proof
}

/// `h : Int.le Int.zero (gap a b)  ⊢  Rat.le a b` (definitionally
/// `Int.le (cross a b) (cross b a)`) — the same ordered-group shift
/// `super::lattice::le_of_nonneg_gap` uses for `max_cases`.
fn le_of_nonneg_gap(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let int = p.int;
    let x = cross(d, a, b);
    let y = cross(d, b, a);
    let gap = cross_gap(d, a, b);
    let zero = d.izero();
    let reflexive = d.lemma(int.le_refl, &[x]);
    let scaled = d.lemma(int.add_le_add, &[zero, gap, x, x, h, reflexive]);
    let left_start = d.iadd(zero, x);
    let right_start = d.iadd(gap, x);
    let left_eq = int_zero_add(d, p, x);
    let right_eq = int_gap_add(d, p, x, y);
    let at_left = d.int_eq_rewrite(left_start, x, left_eq, scaled, &|d, t| {
        d.ile(t, right_start)
    });
    d.int_eq_rewrite(right_start, y, right_eq, at_left, &|d, t| d.ile(x, t))
}

// --- the definition ----------------------------------------------------------

/// `Int.rec.{1} (fun _ => Bool) (fun _ => true) (fun _ => false) z` — the body
/// of `Rat.ble` as a function of the integer it dispatches on.
fn ble_body(d: &mut IntDev<'_>, z: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let nat_ty = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, int_ty, bool_ty, BinderInfo::Default);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let minor_of_nat = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, nat_ty, true_)
    };
    let minor_neg_succ = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, nat_ty, false_)
    };
    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, z])
}

/// Admit `Rat.ble a b := ble_body (gap a b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ble(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let bool_ty = d.bool_ty();
    let ty = {
        let inner = d.arrow(carrier, bool_ty);
        d.arrow(carrier, inner)
    };
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let gap = cross_gap(d, a, b);
    let body = ble_body(d, gap);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ble,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(BLE_HEIGHT),
    })
}

// --- the spec: two directions, no `Iff` --------------------------------------

/// `h : Int.le Int.zero z  ⊢  Eq Bool (ble_body z) true`, for a **symbolic**
/// `z` — proved once by the `Int.rec`-on-its-own-reflexivity trick
/// [`super::lattice::declare_cases`] uses for `max_cases`, then applied at
/// `z := gap a b`.
fn ble_true_of_nonneg(d: &mut IntDev<'_>, gap: ExprId, nonneg: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();
    let zero_level = d.kernel().level_zero();
    let true_ = d.bool_true();

    // motive z := (gap = z) → (Int.le zero z) → Eq Bool (ble_body z) true
    let motive = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let eq_ty = d.ieq(gap, z);
        let zero = d.izero();
        let nonneg_ty = d.ile(zero, z);
        let dispatched = ble_body(d, z);
        let concl = d.bool_eq(dispatched, true_);
        let inner = d.arrow(nonneg_ty, concl);
        let with_eq = d.arrow(eq_ty, inner);
        d.lam_fv(z_fv, int_ty, with_eq)
    };

    // `gap = ofNat n`: `ble_body (ofNat n)` ι-reduces to `true` outright.
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let target_z = d.of_nat(n);
        let proof_concl = {
            let true_ = d.bool_true();
            d.bool_refl(true_)
        };
        let h2_fv = d.fresh_fvar();
        let nonneg_ty = {
            let zero = d.izero();
            d.ile(zero, target_z)
        };
        let with_h2 = d.lam_fv(h2_fv, nonneg_ty, proof_concl);
        let eq_ty = d.ieq(gap, target_z);
        let e_fv = d.fresh_fvar();
        let with_e = d.lam_fv(e_fv, eq_ty, with_h2);
        d.lam_fv(n_fv, nat_ty, with_e)
    };

    // `gap = negSucc m`: `Int.le Int.zero (negSucc m)` ι-reduces to `False`.
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let target_z = d.neg_succ(m);
        let concl_ty = {
            let dispatched = ble_body(d, target_z);
            let true_ = d.bool_true();
            d.bool_eq(dispatched, true_)
        };
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let proof_concl = d.absurd(concl_ty, h2);
        let nonneg_ty = {
            let zero = d.izero();
            d.ile(zero, target_z)
        };
        let with_h2 = d.lam_fv(h2_fv, nonneg_ty, proof_concl);
        let eq_ty = d.ieq(gap, target_z);
        let e_fv = d.fresh_fvar();
        let with_e = d.lam_fv(e_fv, eq_ty, with_h2);
        d.lam_fv(m_fv, nat_ty, with_e)
    };

    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![zero_level]);
    let split = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, gap]);
    let reflexive = d.irefl(gap);
    d.apply(split, &[reflexive, nonneg])
}

/// `Rat.ble_eq_true_of_le : ∀ a b, Rat.le a b → Rat.ble a b = true`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ble_of_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.ble_eq_true_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp = rle(d, p, a, b);
        let true_ = d.bool_true();
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let concl = d.bool_eq(ble_ab, true_);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // Shift `h : Int.le (cross a b) (cross b a)` by `−(cross a b)` on both
        // sides: `Int.le zero (cross b a − cross a b)`, i.e. `Int.le zero gap`.
        let cross_ab = cross(d, a, b);
        let cross_ba = cross(d, b, a);
        let negated = d.ineg(cross_ab);
        let int = p.int;
        let refl_neg = d.lemma(int.le_refl, &[negated]);
        let scaled = d.lemma(
            int.add_le_add,
            &[cross_ab, cross_ba, negated, negated, h, refl_neg],
        );
        let gap = d.iadd(cross_ba, negated);
        let left_start = d.iadd(cross_ab, negated);
        let left_eq = d.lemma(int.add_neg, &[cross_ab]);
        let zero = d.izero();
        let nonneg = d.int_eq_rewrite(left_start, zero, left_eq, scaled, &|d, t| d.ile(t, gap));

        let result = ble_true_of_nonneg(d, gap, nonneg);
        let proof = d.lam_fv(h_fv, hyp, result);
        (stmt, proof)
    })
}

/// `(gap a b) = z → (Eq Bool (ble_body z) true) → Rat.le a b`, eliminated at
/// `z := gap a b` — the converse case split.
fn le_of_ble_case_split(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let gap = cross_gap(d, a, b);
    let nat_ty = d.nat_ty();
    let int_ty = d.int_ty();
    let zero_level = d.kernel().level_zero();
    let true_ = d.bool_true();
    let target = rle(d, p, a, b);

    // motive z := (gap = z) → (Eq Bool (ble_body z) true) → Rat.le a b
    let motive = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let eq_ty = d.ieq(gap, z);
        let dispatched = ble_body(d, z);
        let ble_eq_ty = d.bool_eq(dispatched, true_);
        let inner = d.arrow(ble_eq_ty, target);
        let with_eq = d.arrow(eq_ty, inner);
        d.lam_fv(z_fv, int_ty, with_eq)
    };

    // `gap = ofNat n`: `Rat.le a b` holds unconditionally (the `Bool`
    // hypothesis is not even needed) via `int_zero_le_of_nat` shifted back.
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let target_z = d.of_nat(n);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let constructor = d.lemma(p.int_zero_le_of_nat, &[n]);
        let back = d.isymm(gap, target_z, e);
        let at_gap = d.int_eq_rewrite(target_z, gap, back, constructor, &|d, t| {
            let zero = d.izero();
            d.ile(zero, t)
        });
        let ordered = le_of_nonneg_gap(d, p, a, b, at_gap);
        let h2_fv = d.fresh_fvar();
        let ble_eq_ty2 = {
            let dispatched = ble_body(d, target_z);
            d.bool_eq(dispatched, true_)
        };
        let with_h2 = d.lam_fv(h2_fv, ble_eq_ty2, ordered);
        let eq_ty2 = d.ieq(gap, target_z);
        let with_e = d.lam_fv(e_fv, eq_ty2, with_h2);
        d.lam_fv(n_fv, nat_ty, with_e)
    };

    // `gap = negSucc m`: `ble_body (negSucc m)` ι-reduces to `false`, so the
    // hypothesis is `Eq Bool false true` — impossible.
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let target_z = d.neg_succ(m);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let target_rle = rle(d, p, a, b);
        let body = d.false_true_elim(target_rle, h2);
        let ble_eq_ty2 = {
            let dispatched = ble_body(d, target_z);
            d.bool_eq(dispatched, true_)
        };
        let with_h2 = d.lam_fv(h2_fv, ble_eq_ty2, body);
        let eq_ty2 = d.ieq(gap, target_z);
        let e_fv = d.fresh_fvar();
        let with_e = d.lam_fv(e_fv, eq_ty2, with_h2);
        d.lam_fv(m_fv, nat_ty, with_e)
    };

    let rec_name = p.int.rec;
    let rec = d.kernel().const_(rec_name, vec![zero_level]);
    let split = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, gap]);
    let reflexive = d.irefl(gap);
    d.apply(split, &[reflexive])
}

/// `Rat.le_of_ble_eq_true : ∀ a b, Rat.ble a b = true → Rat.le a b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_le_of_ble(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.le_of_ble_eq_true, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let true_ = d.bool_true();
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let hyp = d.bool_eq(ble_ab, true_);
        let concl = rle(d, p, a, b);
        let stmt = d.arrow(hyp, concl);
        let proof = le_of_ble_case_split(d, p, a, b);
        (stmt, proof)
    })
}

// --- what falls out: refl, trans, total --------------------------------------

/// `Rat.ble_refl : ∀ a, Rat.ble a a = true`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ble_refl(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.ble_refl, 1, &|d, v| {
        let a = v[0];
        let true_ = d.bool_true();
        let ble_aa = d.const_app(p.ble, &[a, a]);
        let stmt = d.bool_eq(ble_aa, true_);
        let le_aa = d.lemma(p.le_refl, &[a]);
        let proof = d.lemma(p.ble_eq_true_of_le, &[a, a, le_aa]);
        (stmt, proof)
    })
}

/// `Rat.ble_trans : ∀ a b c, Rat.ble a b = true → Rat.ble b c = true →
/// Rat.ble a c = true`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ble_trans(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.ble_trans, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let true_ = d.bool_true();
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let ble_bc = d.const_app(p.ble, &[b, c]);
        let ble_ac = d.const_app(p.ble, &[a, c]);
        let h1_ty = d.bool_eq(ble_ab, true_);
        let h2_ty = d.bool_eq(ble_bc, true_);
        let concl = d.bool_eq(ble_ac, true_);
        let stmt = {
            let inner = d.arrow(h2_ty, concl);
            d.arrow(h1_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let le_ab = d.lemma(p.le_of_ble_eq_true, &[a, b, h1]);
        let le_bc = d.lemma(p.le_of_ble_eq_true, &[b, c, h2]);
        let le_ac = d.lemma(p.le_trans, &[a, b, c, le_ab, le_bc]);
        let body = d.lemma(p.ble_eq_true_of_le, &[a, c, le_ac]);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
        let proof = d.lam_fv(h1_fv, h1_ty, with_h2);
        (stmt, proof)
    })
}

/// `Rat.ble_total : ∀ a b, Or (Rat.ble a b = true) (Rat.ble b a = true)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_ble_total(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.ble_total, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let true_ = d.bool_true();
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let ble_ba = d.const_app(p.ble, &[b, a]);
        let left = d.bool_eq(ble_ab, true_);
        let right = d.bool_eq(ble_ba, true_);
        let stmt = d.or(left, right);

        let le_ab = rle(d, p, a, b);
        let lt_ba = rlt(d, p, b, a);
        let decision = d.lemma(p.le_or_lt, &[a, b]);

        let proof = d.or_elim(
            le_ab,
            lt_ba,
            stmt,
            decision,
            &|d, h| {
                let ble_true = d.lemma(p.ble_eq_true_of_le, &[a, b, h]);
                d.or_inl(left, right, ble_true)
            },
            &|d, h| {
                let le_ba = d.lemma(p.le_of_lt, &[b, a, h]);
                let ble_true = d.lemma(p.ble_eq_true_of_le, &[b, a, le_ba]);
                d.or_inr(left, right, ble_true)
            },
        );
        (stmt, proof)
    })
}

/// Admit `Rat.ble`, its two-directional spec, and the three theorems that fall
/// out of it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_decide(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_ble(d, p)?;
    declare_ble_of_le(d, p)?;
    declare_le_of_ble(d, p)?;
    declare_ble_refl(d, p)?;
    declare_ble_trans(d, p)?;
    declare_ble_total(d, p)
}
