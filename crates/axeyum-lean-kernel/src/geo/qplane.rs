//! `Geo.QPlane` — **the rational coordinate plane as a model of
//! [`Geo.Incidence`](super)**, and therefore the proof that the incidence
//! axioms of ADR-1635 are consistent.
//!
//! # The construction
//!
//! ```text
//! inductive Geo.QPoint : Type 0 | mk : Rat → Rat → Geo.QPoint
//! Geo.QPoint.x, Geo.QPoint.y : Geo.QPoint → Rat
//!
//! inductive Geo.QLine0 : Type 0 | mk : Rat → Rat → Rat → Geo.QLine0
//! Geo.QLine0.a, Geo.QLine0.b, Geo.QLine0.c : Geo.QLine0 → Rat
//! Geo.QLine0.Nondeg (l) : Prop := (a l = 0 ∧ b l = 0) → False
//!
//! Geo.QLine : Type 0 := Subtype Geo.QLine0 Geo.QLine0.Nondeg
//! Geo.QPlane.onRaw P l : Prop := a l * x P + b l * y P + c l = 0
//! Geo.QPlane.on P l    : Prop := onRaw P (Subtype.val … l)
//! ```
//!
//! Point equality is the kernel's own `Eq`: ℚ's reduced representative is
//! unique (`Rat.eq_of_cross`), so two `Geo.QPoint`s are equal exactly when
//! their coordinates are, and `Geo.QPoint.ext` proves it. Line equality is
//! **extensional** — `l ≈ m` iff they have the same points — which makes
//! reflexivity, symmetry and transitivity free and puts the whole cost of the
//! model in one place, `joinUnique`.
//!
//! # Where the work is: `joinUnique`, and the pivot lemma
//!
//! Everything algebraic in this file routes through one ℚ identity, stated
//! over eight bare rationals and proved by the `ring::rat` producer (never by
//! hand):
//!
//! ```text
//! Geo.QPlane.onPivot : ∀ u v w U V W s t,
//!     (u = 0 → False) → u*V = v*U → u*W = w*U →
//!     u*s + v*t + w = 0 → U*s + V*t + W = 0
//! ```
//!
//! Read it as: *if the line `(u,v,w)` is proportional to `(U,V,W)` through a
//! nonzero pivot `u`, every point on the first is on the second.* The
//! underlying identity is
//!
//! ```text
//! u*(U*s + V*t + W) = U*(u*s + v*t + w) + ((u*V)*t + u*W) + -(((v*U)*t) + w*U)
//! ```
//!
//! which is unconditional — the two hypotheses are then substituted into the
//! right-hand side (turning the last two summands into a term and its
//! negation) and the incidence hypothesis kills the first, leaving
//! `u*(U*s+V*t+W) = 0`; `Rat.mul_eq_zero` and `u ≠ 0` finish.
//!
//! [`Geo.QPlane.onOfProp`] wraps it in the `a ≠ 0 ∨ b ≠ 0` case split, and
//! **uses the same lemma in both branches** — the `b` branch is `onPivot` with
//! `(u,v,s,t)` and `(U,V)` swapped, so the second case costs three `ring`
//! rearrangements rather than a second proof.
//!
//! The proportionality itself comes from the explicit join
//!
//! ```text
//! Geo.QPlane.join P Q := Geo.QLine0.mk (y Q - y P) (x P - x Q) (y P * x Q - x P * y Q)
//! ```
//!
//! and [`Geo.QPlane.joinProp`]: *any* line through `P` and `Q` is proportional
//! to `join P Q`, with **no** non-degeneracy hypothesis at all. The three
//! proportionality relations are three unconditional ring identities with the
//! two incidence hypotheses added as summands on either side:
//!
//! ```text
//! a*B + e₂ = b*A + e₁      a*C + qy*e₁ = c*A + py*e₂      b*C + px*e₂ = c*B + qx*e₁
//! ```
//!
//! where `e₁`/`e₂` are the two `onRaw` left-hand sides. Substituting
//! `e₁ = e₂ = 0` leaves the relation. `joinUnique` then routes both lines
//! through `join P Q`, which is where — and the **only** where — the
//! distinctness of `P` and `Q` is consumed: `Geo.QPlane.joinNondeg` turns
//! `P ≠ Q` into `join P Q`'s non-degeneracy.
//!
//! # `twoPoints`, and why the shift is uniform
//!
//! A line's second point is its first plus the direction `(-b, a)`:
//! [`Geo.QPlane.shift`]. `shiftOn` is one ring identity (the `a*b` terms
//! cancel) and `shiftApart` needs only `Nondeg` — so the case split on which
//! coefficient is nonzero is needed **only** to produce the first point, where
//! `Rat.inv` and `Rat.mul_inv_cancel_of_ne_zero` do the work — at exactly one
//! site in this file, shared by both cases of the split.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::GeoPrelude;
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::RatPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::{mk_instance, subst, trans_of};
use crate::rat_prelude::ops::{
    radd, rat_ty, rchain, rcongr, rmul, rneg, rone, rsymm, rtrans, rzero,
};

/// The interned names [`declare_all`] produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QPlaneNames {
    /// `Geo.QPoint : Type 0`.
    pub qpoint: NameId,
    /// `Geo.QPoint.mk : Rat → Rat → Geo.QPoint`.
    pub qpoint_mk: NameId,
    /// `Geo.QPoint.rec`.
    pub qpoint_rec: NameId,
    /// `Geo.QPoint.x : Geo.QPoint → Rat`.
    pub qpoint_x: NameId,
    /// `Geo.QPoint.y : Geo.QPoint → Rat`.
    pub qpoint_y: NameId,
    /// `Geo.QPoint.eta : ∀ P, Eq Geo.QPoint P (Geo.QPoint.mk (x P) (y P))`.
    pub qpoint_eta: NameId,
    /// `Geo.QPoint.ext : ∀ P Q, x P = x Q → y P = y Q → P = Q`.
    pub qpoint_ext: NameId,
    /// `Geo.QPoint.eq_trans : ∀ P Q R, P = Q → Q = R → P = R`.
    pub qpoint_eq_trans: NameId,

    /// `Geo.QLine0 : Type 0` — a raw coefficient triple.
    pub qline0: NameId,
    /// `Geo.QLine0.mk : Rat → Rat → Rat → Geo.QLine0`.
    pub qline0_mk: NameId,
    /// `Geo.QLine0.rec`.
    pub qline0_rec: NameId,
    /// `Geo.QLine0.a : Geo.QLine0 → Rat`.
    pub qline0_a: NameId,
    /// `Geo.QLine0.b : Geo.QLine0 → Rat`.
    pub qline0_b: NameId,
    /// `Geo.QLine0.c : Geo.QLine0 → Rat`.
    pub qline0_c: NameId,
    /// `Geo.QLine0.Nondeg : Geo.QLine0 → Prop` — `(a l = 0 ∧ b l = 0) → False`.
    pub nondeg: NameId,
    /// `Geo.QLine0.nondeg_or : ∀ l, Nondeg l → (a l = 0 → False) ∨ (b l = 0 → False)`
    /// — the disjunction the pivot needs, and the only place ℚ's **decidable**
    /// equality is used.
    pub nondeg_or: NameId,
    /// `Geo.QLine : Type 0 := Subtype Geo.QLine0 Geo.QLine0.Nondeg`.
    pub qline: NameId,

    /// `Geo.Rat.eqOrNe : ∀ a b : Rat, a = b ∨ (a = b → False)` — from
    /// `Rat.lt_trichotomy`, no excluded middle.
    pub eq_or_ne: NameId,

    /// `Geo.QPlane.onRaw : Geo.QPoint → Geo.QLine0 → Prop`.
    pub on_raw: NameId,
    /// `Geo.QPlane.on : Geo.QPoint → Geo.QLine → Prop`.
    pub on: NameId,
    /// `Geo.QPlane.Apart : Geo.QPoint → Geo.QPoint → Prop` — `P = Q → False`.
    pub apart: NameId,
    /// `Geo.QLine.Equiv : Geo.QLine → Geo.QLine → Prop` — extensional.
    pub line_equiv: NameId,
    /// `Geo.QLine.equiv_refl`.
    pub line_equiv_refl: NameId,
    /// `Geo.QLine.equiv_symm`.
    pub line_equiv_symm: NameId,
    /// `Geo.QLine.equiv_trans`.
    pub line_equiv_trans: NameId,

    /// `Geo.QPlane.onPoint : ∀ P Q l, P = Q → on P l → on Q l`.
    pub on_point: NameId,
    /// `Geo.QPlane.onLine : ∀ P l m, Equiv l m → on P l → on P m`.
    pub on_line: NameId,
    /// `Geo.QPlane.apartNe : ∀ P Q, Apart P Q → P = Q → False`.
    pub apart_ne: NameId,
    /// `Geo.QPlane.apartSymm : ∀ P Q, Apart P Q → Apart Q P`.
    pub apart_symm: NameId,
    /// `Geo.QPlane.apartCongr : ∀ P P' Q, P = P' → Apart P Q → Apart P' Q`.
    pub apart_congr: NameId,

    /// `Geo.QPlane.join : Geo.QPoint → Geo.QPoint → Geo.QLine0`.
    pub join: NameId,
    /// `Geo.QPlane.joinOnLeft : ∀ P Q, onRaw P (join P Q)`.
    pub join_on_left: NameId,
    /// `Geo.QPlane.joinOnRight : ∀ P Q, onRaw Q (join P Q)`.
    pub join_on_right: NameId,
    /// `Geo.QPlane.joinNondeg : ∀ P Q, (P = Q → False) → Nondeg (join P Q)`.
    pub join_nondeg: NameId,
    /// `Geo.QPlane.joinExists : ∀ P Q, Apart P Q → ∃ l, on P l ∧ on Q l`.
    pub join_exists: NameId,

    /// `Geo.QPlane.onPivot` — the one algebraic lemma; see the module docs.
    pub on_pivot: NameId,
    /// `Geo.QPlane.onOfProp` — [`Self::on_pivot`] under `u ≠ 0 ∨ v ≠ 0`.
    pub on_of_prop: NameId,
    /// `Geo.QPlane.joinProp : ∀ l P Q, onRaw P l → onRaw Q l →
    /// (a l * B = b l * A) ∧ ((a l * C = c l * A) ∧ (b l * C = c l * B))`,
    /// `(A,B,C) := join P Q`. **No non-degeneracy hypothesis.**
    pub join_prop: NameId,
    /// `Geo.QPlane.joinUnique : ∀ P Q l m, Apart P Q →
    /// on P l → on Q l → on P m → on Q m → Equiv l m`.
    pub join_unique: NameId,

    /// `Geo.QPlane.shift : Geo.QPoint → Geo.QLine0 → Geo.QPoint` —
    /// `P + (-b, a)`.
    pub shift: NameId,
    /// `Geo.QPlane.shiftOn : ∀ P l, onRaw P l → onRaw (shift P l) l`.
    pub shift_on: NameId,
    /// `Geo.QPlane.shiftApart : ∀ P l, Nondeg l → (P = shift P l → False)`.
    pub shift_apart: NameId,
    /// `Geo.QPlane.basePoint : ∀ (l : Geo.QLine0), Nondeg l → ∃ P, onRaw P l`.
    pub base_point: NameId,
    /// `Geo.QPlane.twoPoints : ∀ l, ∃ P Q, Apart P Q ∧ (on P l ∧ on Q l)`.
    pub two_points: NameId,
    /// `Geo.QPlane.triangle` — `(0,0)`, `(1,0)`, `(0,1)` are pairwise apart
    /// and no line carries all three.
    pub triangle: NameId,

    /// `Geo.qplane : Geo.Incidence` — the model itself.
    pub instance: NameId,
}

/// Pre-compute every name this module declares. `geo` is the `Geo` namespace
/// root interned by [`super::intern`].
pub(crate) fn intern(kernel: &mut Kernel, geo: NameId) -> QPlaneNames {
    let qpoint = kernel.name_str(geo, "QPoint");
    let qline0 = kernel.name_str(geo, "QLine0");
    let qline = kernel.name_str(geo, "QLine");
    let plane = kernel.name_str(geo, "QPlane");
    let rat_ns = kernel.name_str(geo, "Rat");

    QPlaneNames {
        qpoint,
        qpoint_mk: kernel.name_str(qpoint, "mk"),
        qpoint_rec: kernel.name_str(qpoint, "rec"),
        qpoint_x: kernel.name_str(qpoint, "x"),
        qpoint_y: kernel.name_str(qpoint, "y"),
        qpoint_eta: kernel.name_str(qpoint, "eta"),
        qpoint_ext: kernel.name_str(qpoint, "ext"),
        qpoint_eq_trans: kernel.name_str(qpoint, "eq_trans"),

        qline0,
        qline0_mk: kernel.name_str(qline0, "mk"),
        qline0_rec: kernel.name_str(qline0, "rec"),
        qline0_a: kernel.name_str(qline0, "a"),
        qline0_b: kernel.name_str(qline0, "b"),
        qline0_c: kernel.name_str(qline0, "c"),
        nondeg: kernel.name_str(qline0, "Nondeg"),
        nondeg_or: kernel.name_str(qline0, "nondeg_or"),
        qline,

        eq_or_ne: kernel.name_str(rat_ns, "eqOrNe"),

        on_raw: kernel.name_str(plane, "onRaw"),
        on: kernel.name_str(plane, "on"),
        apart: kernel.name_str(plane, "Apart"),
        line_equiv: kernel.name_str(qline, "Equiv"),
        line_equiv_refl: kernel.name_str(qline, "equiv_refl"),
        line_equiv_symm: kernel.name_str(qline, "equiv_symm"),
        line_equiv_trans: kernel.name_str(qline, "equiv_trans"),

        on_point: kernel.name_str(plane, "onPoint"),
        on_line: kernel.name_str(plane, "onLine"),
        apart_ne: kernel.name_str(plane, "apartNe"),
        apart_symm: kernel.name_str(plane, "apartSymm"),
        apart_congr: kernel.name_str(plane, "apartCongr"),

        join: kernel.name_str(plane, "join"),
        join_on_left: kernel.name_str(plane, "joinOnLeft"),
        join_on_right: kernel.name_str(plane, "joinOnRight"),
        join_nondeg: kernel.name_str(plane, "joinNondeg"),
        join_exists: kernel.name_str(plane, "joinExists"),

        on_pivot: kernel.name_str(plane, "onPivot"),
        on_of_prop: kernel.name_str(plane, "onOfProp"),
        join_prop: kernel.name_str(plane, "joinProp"),
        join_unique: kernel.name_str(plane, "joinUnique"),

        shift: kernel.name_str(plane, "shift"),
        shift_on: kernel.name_str(plane, "shiftOn"),
        shift_apart: kernel.name_str(plane, "shiftApart"),
        base_point: kernel.name_str(plane, "basePoint"),
        two_points: kernel.name_str(plane, "twoPoints"),
        triangle: kernel.name_str(plane, "triangle"),

        instance: kernel.name_str(geo, "qplane"),
    }
}

// ---------------------------------------------------------------------------
// Term shorthands.
// ---------------------------------------------------------------------------

fn point_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qpoint, vec![])
}

fn line0_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qline0, vec![])
}

fn line_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qline, vec![])
}

fn px(d: &mut IntDev<'_>, q: QPlaneNames, p: ExprId) -> ExprId {
    d.const_app(q.qpoint_x, &[p])
}

fn py(d: &mut IntDev<'_>, q: QPlaneNames, p: ExprId) -> ExprId {
    d.const_app(q.qpoint_y, &[p])
}

fn pmk(d: &mut IntDev<'_>, q: QPlaneNames, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(q.qpoint_mk, &[x, y])
}

fn la(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_a, &[l])
}

fn lb(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_b, &[l])
}

fn lc(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_c, &[l])
}

fn lmk(d: &mut IntDev<'_>, q: QPlaneNames, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    d.const_app(q.qline0_mk, &[a, b, c])
}

/// `Eq.{1} Geo.QPoint a b`.
fn peq(d: &mut IntDev<'_>, q: QPlaneNames, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.eq;
    let eq = d.kernel().const_(name, vec![one]);
    let ty = point_ty(d, q);
    d.apply(eq, &[ty, a, b])
}

/// `a * s + b * t + c`, the raw incidence expression.
fn eval(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, s: ExprId, t: ExprId) -> ExprId {
    let m1 = rmul(d, a, s);
    let m2 = rmul(d, b, t);
    let sum = radd(d, m1, m2);
    radd(d, sum, c)
}

fn false_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().logic.false_;
    d.kernel().const_(name, vec![])
}

fn and_ty(d: &mut IntDev<'_>, p: ExprId, r: ExprId) -> ExprId {
    let name = d.int().logic.and;
    d.const_app(name, &[p, r])
}

fn and_intro(d: &mut IntDev<'_>, p: ExprId, r: ExprId, hp: ExprId, hr: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[p, r, hp, hr])
}

fn and_l(d: &mut IntDev<'_>, p: ExprId, r: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_left;
    d.const_app(name, &[p, r, h])
}

fn and_r(d: &mut IntDev<'_>, p: ExprId, r: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_right;
    d.const_app(name, &[p, r, h])
}

fn or_ty(d: &mut IntDev<'_>, p: ExprId, r: ExprId) -> ExprId {
    let name = d.int().logic.or;
    d.const_app(name, &[p, r])
}

/// `Exists.intro.{1} ty pred w proof`.
fn exists_intro(d: &mut IntDev<'_>, ty: ExprId, pred: ExprId, w: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[ty, pred, w, proof])
}

/// A ring identity over ℚ, searched for and emitted by `ring::rat` — never
/// written by hand.
///
/// # Panics
///
/// Panics when the producer declines: every call site here is an identity
/// this file claims is a ring identity, so a decline is an internal
/// inconsistency of the same kind `declare_record`'s own asserts catch, and
/// the rendered goal is what a reader needs to see.
fn ring_eq(d: &mut IntDev<'_>, rat: &RatPrelude, lhs: ExprId, rhs: ExprId) -> ExprId {
    match crate::ring::rat::prove_eq(d, rat, lhs, rhs) {
        Ok(proof) => proof,
        Err(decline) => {
            let l = d.kernel().render_lean(lhs);
            let r = d.kernel().render_lean(rhs);
            panic!("ring::rat declined {decline:?} on\n  {l}\n=\n  {r}");
        }
    }
}

/// `h : Eq src a b` ⊢ `Eq dst (f a) (f b)`, for an `f : src → dst` **between
/// two different carriers**, both at `Sort 1`.
///
/// [`crate::nat_prelude::structures::congr_arg`] cannot do this: it threads
/// one `ty`/`lvl` pair through both the hypothesis equation and the
/// conclusion, so it is `f : ty → ty` only. Every congruence this module
/// needs crosses `Geo.QPoint` and `Rat` in one direction or the other —
/// `Geo.QPoint.ext` builds a point out of two coordinate equations, and
/// `shiftApart`/`triangle` read a coordinate out of a point equation.
fn congr_cross(
    d: &mut IntDev<'_>,
    src: ExprId,
    dst: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let one = d.level_one();
    let logic = d.int().logic;
    let fa = f(d, a);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let fx = f(d, x);
    let concl = {
        let c = d.kernel().const_(logic.eq, vec![one]);
        d.apply(c, &[dst, fa, fx])
    };
    let hyp = {
        let c = d.kernel().const_(logic.eq, vec![one]);
        d.apply(c, &[src, a, x])
    };
    let anon = d.anon_name();
    let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
    let motive = d.lam_fv(x_fv, src, inner);
    let refl_case = {
        let c = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(c, &[dst, fa])
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.eq_rec, vec![zero, one]);
    d.apply(rec, &[src, a, motive, refl_case, b, h])
}

/// `Subtype.val.{1} Geo.QLine0 Geo.QLine0.Nondeg l`.
fn lval(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let val = d.kernel().const_(sigma.subtype_val, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(val, &[base, nd, l])
}

/// `Subtype.mk.{1} Geo.QLine0 Geo.QLine0.Nondeg l proof`.
fn lsub(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let mk = d.kernel().const_(sigma.subtype_mk, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(mk, &[base, nd, l, proof])
}

/// `Subtype.property.{1} Geo.QLine0 Geo.QLine0.Nondeg l`.
fn lprop(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let prop = d.kernel().const_(sigma.subtype_property, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(prop, &[base, nd, l])
}

/// The three coefficients of `Geo.QPlane.join P Q`, spelled out (so
/// `ring::rat` sees rationals rather than a stuck projection).
fn join_coeffs(d: &mut IntDev<'_>, q: QPlaneNames, p: ExprId, r: ExprId) -> [ExprId; 3] {
    let pxv = px(d, q, p);
    let pyv = py(d, q, p);
    let qxv = px(d, q, r);
    let qyv = py(d, q, r);
    let big_a = {
        let n = rneg(d, pyv);
        radd(d, qyv, n)
    };
    let big_b = {
        let n = rneg(d, qxv);
        radd(d, pxv, n)
    };
    let big_c = {
        let m1 = rmul(d, pyv, qxv);
        let m2 = rmul(d, pxv, qyv);
        let n = rneg(d, m2);
        radd(d, m1, n)
    };
    [big_a, big_b, big_c]
}

// ---------------------------------------------------------------------------
// The build.
// ---------------------------------------------------------------------------

/// Declare the whole ℚ model and the `Geo.qplane` instance.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics when the `ring::rat` producer declines an identity this file claims
/// is a ring identity — see [`ring_eq`].
pub(crate) fn declare_all(kernel: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let rat = p.cpoint.creal.rat;
    let q = p.qplane;
    let mut dev = IntDev::new(kernel, rat.int);
    let d = &mut dev;

    declare_carriers(d, q)?;
    declare_point_lemmas(d, q)?;
    declare_nondeg(d, rat, q)?;
    declare_eq_or_ne(d, rat, q)?;
    declare_nondeg_or(d, rat, q)?;
    declare_incidence(d, rat, q)?;
    declare_line_equiv(d, q)?;
    declare_congruences(d, q)?;
    declare_join(d, rat, q)?;
    declare_pivot(d, rat, q)?;
    declare_join_prop(d, rat, q)?;
    declare_join_unique(d, rat, q)?;
    declare_two_points(d, rat, q)?;
    declare_triangle(d, rat, q)?;
    declare_instance(d, p, q)
}

/// `Geo.QPoint`, `Geo.QLine0` and their projections.
fn declare_carriers(d: &mut IntDev<'_>, q: QPlaneNames) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // inductive Geo.QPoint | mk : Rat → Rat → Geo.QPoint
    {
        let point = point_ty(d, q);
        let mk_ty = {
            let inner = d.arrow(rt, point);
            d.arrow(rt, inner)
        };
        d.kernel()
            .add_inductive(q.qpoint, &[], 0, type0, &[(q.qpoint_mk, mk_ty)])?;
    }
    declare_projection(d, q.qpoint, q.qpoint_rec, q.qpoint_x, 2, 0)?;
    declare_projection(d, q.qpoint, q.qpoint_rec, q.qpoint_y, 2, 1)?;

    // inductive Geo.QLine0 | mk : Rat → Rat → Rat → Geo.QLine0
    {
        let line = line0_ty(d, q);
        let mk_ty = {
            let inner = d.arrow(rt, line);
            let inner = d.arrow(rt, inner);
            d.arrow(rt, inner)
        };
        d.kernel()
            .add_inductive(q.qline0, &[], 0, type0, &[(q.qline0_mk, mk_ty)])?;
    }
    declare_projection(d, q.qline0, q.qline0_rec, q.qline0_a, 3, 0)?;
    declare_projection(d, q.qline0, q.qline0_rec, q.qline0_b, 3, 1)?;
    declare_projection(d, q.qline0, q.qline0_rec, q.qline0_c, 3, 2)?;
    Ok(())
}

/// The `index`-th of `arity` `Rat` fields of a one-constructor `Type 0`
/// record, by large elimination — `creal_point`'s `declare_projections`,
/// generalized over the field count.
fn declare_projection(
    d: &mut IntDev<'_>,
    ind: NameId,
    rec: NameId,
    name: NameId,
    arity: usize,
    index: usize,
) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let one = d.level_one();
    let anon = d.anon_name();
    let carrier = d.kernel().const_(ind, vec![]);

    let motive = d.kernel().lam(anon, carrier, rt, BinderInfo::Default);
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let picked = d.kernel().fvar(fvs[index]);
    let mut minor = picked;
    for &fv in fvs.iter().rev() {
        minor = d.lam_fv(fv, rt, minor);
    }
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let rec_c = d.kernel().const_(rec, vec![one]);
    let body = d.apply(rec_c, &[motive, minor, t]);
    let value = d.lam_fv(t_fv, carrier, body);
    let ty = d.arrow(carrier, rt);
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Geo.QPoint.eta`, `Geo.QPoint.ext`, `Geo.QPoint.eq_trans`.
fn declare_point_lemmas(d: &mut IntDev<'_>, q: QPlaneNames) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let one = d.level_one();
    let logic = d.int().logic;

    // eta : ∀ P, Eq QPoint P (mk (x P) (y P)) — by QPoint.rec, ι on the ctor.
    {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let motive = {
            let xt = px(d, q, t);
            let yt = py(d, q, t);
            let rebuilt = pmk(d, q, xt, yt);
            let body = peq(d, q, t, rebuilt);
            d.lam_fv(t_fv, point, body)
        };
        let minor = {
            let a_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b = d.kernel().fvar(b_fv);
            let built = pmk(d, q, a, b);
            let refl = {
                let name = logic.eq_refl;
                let c = d.kernel().const_(name, vec![one]);
                d.apply(c, &[point, built])
            };
            let rt = rat_ty(d);
            let inner = d.lam_fv(b_fv, rt, refl);
            d.lam_fv(a_fv, rt, inner)
        };
        let l0 = d.kernel().level_zero();
        let rec = d.kernel().const_(q.qpoint_rec, vec![l0]);
        let p_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let body = d.apply(rec, &[motive, minor, pt]);
        let value = d.lam_fv(p_fv, point, body);
        let ty = {
            let xt = px(d, q, pt);
            let yt = py(d, q, pt);
            let rebuilt = pmk(d, q, xt, yt);
            let stmt = peq(d, q, pt, rebuilt);
            d.pi_fv(p_fv, point, stmt)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.qpoint_eta,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // eq_trans : ∀ P Q R, P = Q → Q = R → P = R.
    {
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let c = d.kernel().fvar(c_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let ab = peq(d, q, a, b);
        let bc = peq(d, q, b, c);
        let ac = peq(d, q, a, c);
        let scratch = d.fresh_fvar();
        let proof = trans_of(d.kernel(), &logic, one, point, a, b, c, h1, h2, scratch);
        let ty = {
            let t = d.arrow(bc, ac);
            let t = d.arrow(ab, t);
            let t = d.pi_fv(c_fv, point, t);
            let t = d.pi_fv(b_fv, point, t);
            d.pi_fv(a_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h2_fv, bc, proof);
            let t = d.lam_fv(h1_fv, ab, t);
            let t = d.lam_fv(c_fv, point, t);
            let t = d.lam_fv(b_fv, point, t);
            d.lam_fv(a_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.qpoint_eq_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // ext : ∀ P Q, x P = x Q → y P = y Q → P = Q.
    {
        let rt = rat_ty(d);
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let hx_fv = d.fresh_fvar();
        let hy_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rt_pt = d.kernel().fvar(r_fv);
        let hx = d.kernel().fvar(hx_fv);
        let hy = d.kernel().fvar(hy_fv);

        let pxv = px(d, q, pt);
        let pyv = py(d, q, pt);
        let qxv = px(d, q, rt_pt);
        let qyv = py(d, q, rt_pt);
        let hx_ty = crate::rat_prelude::ops::req(d, pxv, qxv);
        let hy_ty = crate::rat_prelude::ops::req(d, pyv, qyv);

        // mk (x P) (y P) = mk (x Q) (y P) = mk (x Q) (y Q).
        let start = pmk(d, q, pxv, pyv);
        let mid = pmk(d, q, qxv, pyv);
        let end = pmk(d, q, qxv, qyv);
        let s1 = congr_cross(d, rt, point, pxv, qxv, hx, &|d, hole| pmk(d, q, hole, pyv));
        let s2 = congr_cross(d, rt, point, pyv, qyv, hy, &|d, hole| pmk(d, q, qxv, hole));
        let sc = d.fresh_fvar();
        let mk_eq = trans_of(d.kernel(), &logic, one, point, start, mid, end, s1, s2, sc);

        // P = mk (x P) (y P) = mk (x Q) (y Q) = Q.
        let eta_p = d.const_app(q.qpoint_eta, &[pt]);
        let eta_q = d.const_app(q.qpoint_eta, &[rt_pt]);
        let eta_q_symm = {
            let c = d.kernel().const_(logic.eq_symm, vec![one]);
            d.apply(c, &[point, rt_pt, end, eta_q])
        };
        let sc2 = d.fresh_fvar();
        let step1 = trans_of(
            d.kernel(),
            &logic,
            one,
            point,
            pt,
            start,
            end,
            eta_p,
            mk_eq,
            sc2,
        );
        let sc3 = d.fresh_fvar();
        let proof = trans_of(
            d.kernel(),
            &logic,
            one,
            point,
            pt,
            end,
            rt_pt,
            step1,
            eta_q_symm,
            sc3,
        );

        let concl = peq(d, q, pt, rt_pt);
        let ty = {
            let t = d.arrow(hy_ty, concl);
            let t = d.arrow(hx_ty, t);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(hy_fv, hy_ty, proof);
            let t = d.lam_fv(hx_fv, hx_ty, t);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.qpoint_ext,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Geo.QLine0.Nondeg` and `Geo.QLine`.
fn declare_nondeg(d: &mut IntDev<'_>, rat: RatPrelude, q: QPlaneNames) -> Result<(), KernelError> {
    let line0 = line0_ty(d, q);
    let prop = {
        let l0 = d.kernel().level_zero();
        d.kernel().sort(l0)
    };
    {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let z = rzero(d, rat);
        let ea = crate::rat_prelude::ops::req(d, av, z);
        let eb = crate::rat_prelude::ops::req(d, bv, z);
        let both = and_ty(d, ea, eb);
        let f = false_ty(d);
        let body = d.arrow(both, f);
        let value = d.lam_fv(l_fv, line0, body);
        let ty = d.arrow(line0, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: q.nondeg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    // Geo.QLine := Subtype Geo.QLine0 Geo.QLine0.Nondeg.
    {
        let one = d.level_one();
        let sigma = d.int().logic.sigma;
        let sub = d.kernel().const_(sigma.subtype, vec![one]);
        let nd = d.kernel().const_(q.nondeg, vec![]);
        let value = d.apply(sub, &[line0, nd]);
        let ty = d.kernel().sort(one);
        d.kernel().add_declaration(Declaration::Definition {
            name: q.qline,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

/// `Geo.Rat.eqOrNe : ∀ a b : Rat, (a = b) ∨ (a = b → False)`, from
/// `Rat.lt_trichotomy` — the only place this model uses ℚ's decidability.
fn declare_eq_or_ne(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let logic = d.int().logic;
    let one = d.level_one();
    let a_fv = d.fresh_fvar();
    let b_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b = d.kernel().fvar(b_fv);

    let eq_ab = crate::rat_prelude::ops::req(d, a, b);
    let f = false_ty(d);
    let ne_ab = d.arrow(eq_ab, f);
    let target = or_ty(d, eq_ab, ne_ab);

    let lt_ab = crate::rat_prelude::ops::rlt(d, rat, a, b);
    let lt_ba = crate::rat_prelude::ops::rlt(d, rat, b, a);
    let inner_or = or_ty(d, eq_ab, lt_ba);
    let tri = d.const_app(rat.lt_trichotomy, &[a, b]);

    // From `lt x y` and `x = y`, `Rat.lt_irrefl` closes.
    let proof = d.or_elim(
        lt_ab,
        inner_or,
        target,
        tri,
        &|d, hlt| {
            // hlt : lt a b, and h : a = b gives lt b b.
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let shifted = crate::rat_prelude::ops::rat_eq_rewrite(d, a, b, h, hlt, &|d, x| {
                crate::rat_prelude::ops::rlt(d, rat, x, b)
            });
            let irr = d.const_app(rat.lt_irrefl, &[b]);
            let body = d.apply(irr, &[shifted]);
            let ne = d.lam_fv(h_fv, eq_ab, body);
            let inr = d.kernel().const_(logic.or_inr, vec![]);
            d.apply(inr, &[eq_ab, ne_ab, ne])
        },
        &|d, hinner| {
            d.or_elim(
                eq_ab,
                lt_ba,
                target,
                hinner,
                &|d, heq| {
                    let inl = d.kernel().const_(logic.or_inl, vec![]);
                    d.apply(inl, &[eq_ab, ne_ab, heq])
                },
                &|d, hlt| {
                    // hlt : lt b a, and h : a = b gives lt b b.
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let shifted =
                        crate::rat_prelude::ops::rat_eq_rewrite(d, a, b, h, hlt, &|d, x| {
                            crate::rat_prelude::ops::rlt(d, rat, b, x)
                        });
                    let irr = d.const_app(rat.lt_irrefl, &[b]);
                    let body = d.apply(irr, &[shifted]);
                    let ne = d.lam_fv(h_fv, eq_ab, body);
                    let inr = d.kernel().const_(logic.or_inr, vec![]);
                    d.apply(inr, &[eq_ab, ne_ab, ne])
                },
            )
        },
    );

    let _ = one;
    let ty = {
        let t = d.pi_fv(b_fv, rt, target);
        d.pi_fv(a_fv, rt, t)
    };
    let value = {
        let t = d.lam_fv(b_fv, rt, proof);
        d.lam_fv(a_fv, rt, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: q.eq_or_ne,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.QLine0.nondeg_or : ∀ l, Nondeg l → (a l = 0 → False) ∨ (b l = 0 → False)`.
fn declare_nondeg_or(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let line0 = line0_ty(d, q);
    let logic = d.int().logic;
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let av = la(d, q, l);
    let bv = lb(d, q, l);
    let z = rzero(d, rat);
    let ea = crate::rat_prelude::ops::req(d, av, z);
    let eb = crate::rat_prelude::ops::req(d, bv, z);
    let f = false_ty(d);
    let ne_a = d.arrow(ea, f);
    let ne_b = d.arrow(eb, f);
    let target = or_ty(d, ne_a, ne_b);

    let hyp_ty = d.const_app(q.nondeg, &[l]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let tri_a = d.const_app(q.eq_or_ne, &[av, z]);
    let proof = d.or_elim(
        ea,
        ne_a,
        target,
        tri_a,
        &|d, ha| {
            let tri_b = d.const_app(q.eq_or_ne, &[bv, z]);
            d.or_elim(
                eb,
                ne_b,
                target,
                tri_b,
                &|d, hb| {
                    let both = and_intro(d, ea, eb, ha, hb);
                    let contra = d.apply(h, &[both]);
                    d.absurd(target, contra)
                },
                &|d, hnb| {
                    let inr = d.kernel().const_(logic.or_inr, vec![]);
                    d.apply(inr, &[ne_a, ne_b, hnb])
                },
            )
        },
        &|d, hna| {
            let inl = d.kernel().const_(logic.or_inl, vec![]);
            d.apply(inl, &[ne_a, ne_b, hna])
        },
    );

    let ty = {
        let t = d.arrow(hyp_ty, target);
        d.pi_fv(l_fv, line0, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        d.lam_fv(l_fv, line0, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: q.nondeg_or,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.QPlane.onRaw`, `Geo.QPlane.on`, `Geo.QPlane.Apart`.
fn declare_incidence(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);
    let prop = {
        let l0 = d.kernel().level_zero();
        d.kernel().sort(l0)
    };

    // onRaw P l := a l * x P + b l * y P + c l = 0.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let cv = lc(d, q, l);
        let s = px(d, q, pt);
        let t = py(d, q, pt);
        let lhs = eval(d, av, bv, cv, s, t);
        let z = rzero(d, rat);
        let body = crate::rat_prelude::ops::req(d, lhs, z);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.on_raw,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // on P l := onRaw P (Subtype.val l).
    {
        let line = line_ty(d, q);
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let raw = lval(d, q, l);
        let body = d.const_app(q.on_raw, &[pt, raw]);
        let value = {
            let inner = d.lam_fv(l_fv, line, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // Apart P Q := (P = Q) → False.
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let e = peq(d, q, pt, rp);
        let f = false_ty(d);
        let body = d.arrow(e, f);
        let value = {
            let inner = d.lam_fv(r_fv, point, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(point, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.apart,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

/// `Geo.QLine.Equiv` and its three laws.
fn declare_line_equiv(d: &mut IntDev<'_>, q: QPlaneNames) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let prop = {
        let l0 = d.kernel().level_zero();
        d.kernel().sort(l0)
    };

    // Equiv l m := ∀ P, (on P l → on P m) ∧ (on P m → on P l).
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let p_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let pt = d.kernel().fvar(p_fv);
        let opl = d.const_app(q.on, &[pt, l]);
        let opm = d.const_app(q.on, &[pt, m]);
        let fwd = d.arrow(opl, opm);
        let bwd = d.arrow(opm, opl);
        let both = and_ty(d, fwd, bwd);
        let quantified = d.pi_fv(p_fv, point, both);
        let value = {
            let inner = d.lam_fv(m_fv, line, quantified);
            d.lam_fv(l_fv, line, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(line, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.line_equiv,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // equiv_refl : ∀ l, Equiv l l.
    {
        let l_fv = d.fresh_fvar();
        let p_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let pt = d.kernel().fvar(p_fv);
        let opl = d.const_app(q.on, &[pt, l]);
        let fwd = d.arrow(opl, opl);
        let id = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, opl, h)
        };
        let body = and_intro(d, fwd, fwd, id, id);
        let inner = d.lam_fv(p_fv, point, body);
        let value = d.lam_fv(l_fv, line, inner);
        let ty = {
            let stmt = d.const_app(q.line_equiv, &[l, l]);
            d.pi_fv(l_fv, line, stmt)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.line_equiv_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // equiv_symm : ∀ l m, Equiv l m → Equiv m l.
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let p_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let h = d.kernel().fvar(h_fv);
        let pt = d.kernel().fvar(p_fv);
        let hyp = d.const_app(q.line_equiv, &[l, m]);
        let concl = d.const_app(q.line_equiv, &[m, l]);
        let opl = d.const_app(q.on, &[pt, l]);
        let opm = d.const_app(q.on, &[pt, m]);
        let fwd = d.arrow(opl, opm);
        let bwd = d.arrow(opm, opl);
        let at_p = d.apply(h, &[pt]);
        let left = and_l(d, fwd, bwd, at_p);
        let right = and_r(d, fwd, bwd, at_p);
        let body = and_intro(d, bwd, fwd, right, left);
        let value = {
            let t = d.lam_fv(p_fv, point, body);
            let t = d.lam_fv(h_fv, hyp, t);
            let t = d.lam_fv(m_fv, line, t);
            d.lam_fv(l_fv, line, t)
        };
        let ty = {
            let t = d.arrow(hyp, concl);
            let t = d.pi_fv(m_fv, line, t);
            d.pi_fv(l_fv, line, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.line_equiv_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // equiv_trans : ∀ l m n, Equiv l m → Equiv m n → Equiv l n.
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let n_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let p_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let n = d.kernel().fvar(n_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let pt = d.kernel().fvar(p_fv);
        let hyp1 = d.const_app(q.line_equiv, &[l, m]);
        let hyp2 = d.const_app(q.line_equiv, &[m, n]);
        let concl = d.const_app(q.line_equiv, &[l, n]);
        let opl = d.const_app(q.on, &[pt, l]);
        let opm = d.const_app(q.on, &[pt, m]);
        let opn = d.const_app(q.on, &[pt, n]);
        let f_lm = d.arrow(opl, opm);
        let b_lm = d.arrow(opm, opl);
        let f_mn = d.arrow(opm, opn);
        let b_mn = d.arrow(opn, opm);
        let f_ln = d.arrow(opl, opn);
        let b_ln = d.arrow(opn, opl);
        let at1 = d.apply(h1, &[pt]);
        let at2 = d.apply(h2, &[pt]);
        let lm_f = and_l(d, f_lm, b_lm, at1);
        let lm_b = and_r(d, f_lm, b_lm, at1);
        let mn_f = and_l(d, f_mn, b_mn, at2);
        let mn_b = and_r(d, f_mn, b_mn, at2);
        let fwd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let step = d.apply(lm_f, &[h]);
            let body = d.apply(mn_f, &[step]);
            d.lam_fv(h_fv, opl, body)
        };
        let bwd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let step = d.apply(mn_b, &[h]);
            let body = d.apply(lm_b, &[step]);
            d.lam_fv(h_fv, opn, body)
        };
        let body = and_intro(d, f_ln, b_ln, fwd, bwd);
        let value = {
            let t = d.lam_fv(p_fv, point, body);
            let t = d.lam_fv(h2_fv, hyp2, t);
            let t = d.lam_fv(h1_fv, hyp1, t);
            let t = d.lam_fv(n_fv, line, t);
            let t = d.lam_fv(m_fv, line, t);
            d.lam_fv(l_fv, line, t)
        };
        let ty = {
            let t = d.arrow(hyp2, concl);
            let t = d.arrow(hyp1, t);
            let t = d.pi_fv(n_fv, line, t);
            let t = d.pi_fv(m_fv, line, t);
            d.pi_fv(l_fv, line, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.line_equiv_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `onPoint`, `onLine`, `apartNe`, `apartSymm`, `apartCongr`.
fn declare_congruences(d: &mut IntDev<'_>, q: QPlaneNames) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let logic = d.int().logic;
    let one = d.level_one();

    // onPoint : ∀ P Q l, P = Q → on P l → on Q l.
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let ho_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let l = d.kernel().fvar(l_fv);
        let he = d.kernel().fvar(he_fv);
        let ho = d.kernel().fvar(ho_fv);
        let eq_ty = peq(d, q, pt, rp);
        let opl = d.const_app(q.on, &[pt, l]);
        let oql = d.const_app(q.on, &[rp, l]);
        let sc = d.fresh_fvar();
        let proof = subst(
            d.kernel(),
            &logic,
            one,
            point,
            pt,
            rp,
            he,
            sc,
            &|k, hole| {
                let c = k.const_(q.on, vec![]);
                let e = k.app(c, hole);
                k.app(e, l)
            },
            ho,
        );
        let ty = {
            let t = d.arrow(opl, oql);
            let t = d.arrow(eq_ty, t);
            let t = d.pi_fv(l_fv, line, t);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(ho_fv, opl, proof);
            let t = d.lam_fv(he_fv, eq_ty, t);
            let t = d.lam_fv(l_fv, line, t);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.on_point,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // onLine : ∀ P l m, Equiv l m → on P l → on P m.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let he = d.kernel().fvar(he_fv);
        let hyp = d.const_app(q.line_equiv, &[l, m]);
        let opl = d.const_app(q.on, &[pt, l]);
        let opm = d.const_app(q.on, &[pt, m]);
        let fwd = d.arrow(opl, opm);
        let bwd = d.arrow(opm, opl);
        let at_p = d.apply(he, &[pt]);
        let proof = and_l(d, fwd, bwd, at_p);
        let ty = {
            let t = d.arrow(opl, opm);
            let t = d.arrow(hyp, t);
            let t = d.pi_fv(m_fv, line, t);
            let t = d.pi_fv(l_fv, line, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(he_fv, hyp, proof);
            let t = d.lam_fv(m_fv, line, t);
            let t = d.lam_fv(l_fv, line, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.on_line,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartNe : ∀ P Q, Apart P Q → P = Q → False. `Apart` unfolds to exactly
    // this, so the proof is the hypothesis.
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let h = d.kernel().fvar(h_fv);
        let ap = d.const_app(q.apart, &[pt, rp]);
        let eq_ty = peq(d, q, pt, rp);
        let f = false_ty(d);
        let ty = {
            let t = d.arrow(eq_ty, f);
            let t = d.arrow(ap, t);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, ap, h);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.apart_ne,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartSymm : ∀ P Q, Apart P Q → Apart Q P.
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let e_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let h = d.kernel().fvar(h_fv);
        let e = d.kernel().fvar(e_fv);
        let ap = d.const_app(q.apart, &[pt, rp]);
        let ap_rev = d.const_app(q.apart, &[rp, pt]);
        let eq_qp = peq(d, q, rp, pt);
        let flipped = {
            let c = d.kernel().const_(logic.eq_symm, vec![one]);
            d.apply(c, &[point, rp, pt, e])
        };
        let body = d.apply(h, &[flipped]);
        let proof = d.lam_fv(e_fv, eq_qp, body);
        let ty = {
            let t = d.arrow(ap, ap_rev);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, ap, proof);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.apart_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartCongr : ∀ P P' Q, P = P' → Apart P Q → Apart P' Q.
    {
        let p_fv = d.fresh_fvar();
        let p2_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let p2 = d.kernel().fvar(p2_fv);
        let rp = d.kernel().fvar(r_fv);
        let he = d.kernel().fvar(he_fv);
        let ha = d.kernel().fvar(ha_fv);
        let eq_ty = peq(d, q, pt, p2);
        let ap = d.const_app(q.apart, &[pt, rp]);
        let ap2 = d.const_app(q.apart, &[p2, rp]);
        let sc = d.fresh_fvar();
        let proof = subst(
            d.kernel(),
            &logic,
            one,
            point,
            pt,
            p2,
            he,
            sc,
            &|k, hole| {
                let c = k.const_(q.apart, vec![]);
                let e = k.app(c, hole);
                k.app(e, rp)
            },
            ha,
        );
        let ty = {
            let t = d.arrow(ap, ap2);
            let t = d.arrow(eq_ty, t);
            let t = d.pi_fv(r_fv, point, t);
            let t = d.pi_fv(p2_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(ha_fv, ap, proof);
            let t = d.lam_fv(he_fv, eq_ty, t);
            let t = d.lam_fv(r_fv, point, t);
            let t = d.lam_fv(p2_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.apart_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `join`, `joinOnLeft`, `joinOnRight`, `joinNondeg`, `joinExists`.
fn declare_join(d: &mut IntDev<'_>, rat: RatPrelude, q: QPlaneNames) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);
    let logic = d.int().logic;
    let one = d.level_one();

    // join P Q := QLine0.mk (qy - py) (px - qx) (py*qx - px*qy).
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let [big_a, big_b, big_c] = join_coeffs(d, q, pt, rp);
        let body = lmk(d, q, big_a, big_b, big_c);
        let value = {
            let inner = d.lam_fv(r_fv, point, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(point, line0);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.join,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // joinOnLeft / joinOnRight: pure ring identities at the SPELLED-OUT
    // coefficients; the kernel iota-reduces the projections of `join`'s `mk`.
    for (name, at_left) in [(q.join_on_left, true), (q.join_on_right, false)] {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let [big_a, big_b, big_c] = join_coeffs(d, q, pt, rp);
        let target = if at_left { pt } else { rp };
        let s = px(d, q, target);
        let t = py(d, q, target);
        let lhs = eval(d, big_a, big_b, big_c, s, t);
        let z = rzero(d, rat);
        let proof = ring_eq(d, &rat, lhs, z);
        let joined = d.const_app(q.join, &[pt, rp]);
        let stmt = d.const_app(q.on_raw, &[target, joined]);
        let ty = {
            let t2 = d.pi_fv(r_fv, point, stmt);
            d.pi_fv(p_fv, point, t2)
        };
        let value = {
            let t2 = d.lam_fv(r_fv, point, proof);
            d.lam_fv(p_fv, point, t2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // joinNondeg : ∀ P Q, (P = Q → False) → Nondeg (join P Q).
    {
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let hne_fv = d.fresh_fvar();
        let hand_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let hne = d.kernel().fvar(hne_fv);
        let hand = d.kernel().fvar(hand_fv);
        let [big_a, big_b, _big_c] = join_coeffs(d, q, pt, rp);
        let z = rzero(d, rat);
        let ea = crate::rat_prelude::ops::req(d, big_a, z);
        let eb = crate::rat_prelude::ops::req(d, big_b, z);
        let both = and_ty(d, ea, eb);
        let ha = and_l(d, ea, eb, hand);
        let hb = and_r(d, ea, eb, hand);

        let pxv = px(d, q, pt);
        let pyv = py(d, q, pt);
        let qxv = px(d, q, rp);
        let qyv = py(d, q, rp);

        // From `px - qx = 0`, `px = px + (-qx) + qx = 0 + qx = qx`.
        let hx = {
            let mid = radd(d, big_b, qxv);
            let s1 = ring_eq(d, &rat, pxv, mid);
            let s2 = rcongr(d, big_b, z, hb, &|d, hole| radd(d, hole, qxv));
            let zqx = radd(d, z, qxv);
            let s3 = ring_eq(d, &rat, zqx, qxv);
            let (_, proof) = rchain(d, pxv, &[(mid, s1), (zqx, s2), (qxv, s3)]);
            proof
        };
        // From `qy - py = 0`, `qy = py`, then symm for `py = qy`.
        let hy = {
            let mid = radd(d, big_a, pyv);
            let s1 = ring_eq(d, &rat, qyv, mid);
            let s2 = rcongr(d, big_a, z, ha, &|d, hole| radd(d, hole, pyv));
            let zpy = radd(d, z, pyv);
            let s3 = ring_eq(d, &rat, zpy, pyv);
            let (_, proof) = rchain(d, qyv, &[(mid, s1), (zpy, s2), (pyv, s3)]);
            rsymm(d, qyv, pyv, proof)
        };
        let same = d.const_app(q.qpoint_ext, &[pt, rp, hx, hy]);
        let body = d.apply(hne, &[same]);
        let proof = d.lam_fv(hand_fv, both, body);

        let f = false_ty(d);
        let eq_pq = peq(d, q, pt, rp);
        let ne_ty = d.arrow(eq_pq, f);
        let joined = d.const_app(q.join, &[pt, rp]);
        let concl = d.const_app(q.nondeg, &[joined]);
        let ty = {
            let t = d.arrow(ne_ty, concl);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(hne_fv, ne_ty, proof);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.join_nondeg,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // joinExists : ∀ P Q, Apart P Q → ∃ (l : QLine), on P l ∧ on Q l.
    {
        let line = line_ty(d, q);
        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let h = d.kernel().fvar(h_fv);
        let l = d.kernel().fvar(l_fv);

        let ap = d.const_app(q.apart, &[pt, rp]);
        let opl = d.const_app(q.on, &[pt, l]);
        let oql = d.const_app(q.on, &[rp, l]);
        let body = and_ty(d, opl, oql);
        let pred = d.lam_fv(l_fv, line, body);
        let ex = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(ex_c, &[line, pred])
        };

        let joined = d.const_app(q.join, &[pt, rp]);
        let nd = d.const_app(q.join_nondeg, &[pt, rp, h]);
        let witness = lsub(d, q, joined, nd);
        let hp = d.const_app(q.join_on_left, &[pt, rp]);
        let hq = d.const_app(q.join_on_right, &[pt, rp]);
        let w_on_p = d.const_app(q.on, &[pt, witness]);
        let w_on_q = d.const_app(q.on, &[rp, witness]);
        let pair = and_intro(d, w_on_p, w_on_q, hp, hq);
        let proof = exists_intro(d, line, pred, witness, pair);

        let ty = {
            let t = d.arrow(ap, ex);
            let t = d.pi_fv(r_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, ap, proof);
            let t = d.lam_fv(r_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.join_exists,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `onPivot` and `onOfProp` — the module's one piece of algebra.
fn declare_pivot(d: &mut IntDev<'_>, rat: RatPrelude, q: QPlaneNames) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let logic = d.int().logic;

    // onPivot : ∀ u v w U V W s t, (u = 0 → False) → u*V = v*U → u*W = w*U →
    //           u*s + v*t + w = 0 → U*s + V*t + W = 0.
    {
        let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (u, v, w) = (vars[0], vars[1], vars[2]);
        let (bu, bv, bw) = (vars[3], vars[4], vars[5]);
        let (s, t) = (vars[6], vars[7]);
        let z = rzero(d, rat);

        let hn_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h3_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.kernel().fvar(h3_fv);

        let eu = crate::rat_prelude::ops::req(d, u, z);
        let f = false_ty(d);
        let hn_ty = d.arrow(eu, f);
        let uv = rmul(d, u, bv);
        let vu = rmul(d, v, bu);
        let h1_ty = crate::rat_prelude::ops::req(d, uv, vu);
        let uw = rmul(d, u, bw);
        let wu = rmul(d, w, bu);
        let h2_ty = crate::rat_prelude::ops::req(d, uw, wu);
        let small = eval(d, u, v, w, s, t);
        let h3_ty = crate::rat_prelude::ops::req(d, small, z);
        let big = eval(d, bu, bv, bw, s, t);
        let concl = crate::rat_prelude::ops::req(d, big, z);

        // `residue(e, m1, m2) := U*e + (m1*t + m2) + -((v*U)*t + w*U)`.
        let residue = |d: &mut IntDev<'_>, e: ExprId, m1: ExprId, m2: ExprId| -> ExprId {
            let head = rmul(d, bu, e);
            let mt = rmul(d, m1, t);
            let mid = radd(d, mt, m2);
            let vut = rmul(d, vu, t);
            let tail = radd(d, vut, wu);
            let ntail = rneg(d, tail);
            let sum = radd(d, head, mid);
            radd(d, sum, ntail)
        };

        let r0 = residue(d, small, uv, uw);
        let r1 = residue(d, small, vu, uw);
        let r2 = residue(d, small, vu, wu);
        let r3 = residue(d, z, vu, wu);

        let u_big = rmul(d, u, big);
        let step0 = ring_eq(d, &rat, u_big, r0);
        let step1 = rcongr(d, uv, vu, h1, &|d, hole| residue(d, small, hole, uw));
        let step2 = rcongr(d, uw, wu, h2, &|d, hole| residue(d, small, vu, hole));
        let step3 = rcongr(d, small, z, h3, &|d, hole| residue(d, hole, vu, wu));
        let step4 = ring_eq(d, &rat, r3, z);
        let (_, prod_zero) = rchain(
            d,
            u_big,
            &[
                (r0, step0),
                (r1, step1),
                (r2, step2),
                (r3, step3),
                (z, step4),
            ],
        );

        let split = d.const_app(rat.mul_eq_zero, &[u, big, prod_zero]);
        let eu_case = crate::rat_prelude::ops::req(d, u, z);
        let ebig_case = crate::rat_prelude::ops::req(d, big, z);
        let proof = d.or_elim(
            eu_case,
            ebig_case,
            concl,
            split,
            &|d, hu| {
                let contra = d.apply(hn, &[hu]);
                d.absurd(concl, contra)
            },
            &|_d, hb| hb,
        );

        let ty = {
            let mut t2 = d.arrow(h3_ty, concl);
            t2 = d.arrow(h2_ty, t2);
            t2 = d.arrow(h1_ty, t2);
            t2 = d.arrow(hn_ty, t2);
            for &fv in fvs.iter().rev() {
                t2 = d.pi_fv(fv, rt, t2);
            }
            t2
        };
        let value = {
            let mut v2 = d.lam_fv(h3_fv, h3_ty, proof);
            v2 = d.lam_fv(h2_fv, h2_ty, v2);
            v2 = d.lam_fv(h1_fv, h1_ty, v2);
            v2 = d.lam_fv(hn_fv, hn_ty, v2);
            for &fv in fvs.iter().rev() {
                v2 = d.lam_fv(fv, rt, v2);
            }
            v2
        };
        let _ = logic;
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.on_pivot,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // onOfProp : ∀ u v w U V W s t,
    //   ((u = 0 → False) ∨ (v = 0 → False)) →
    //   u*V = v*U → u*W = w*U → v*W = w*V →
    //   u*s + v*t + w = 0 → U*s + V*t + W = 0.
    {
        let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (u, v, w) = (vars[0], vars[1], vars[2]);
        let (bu, bv, bw) = (vars[3], vars[4], vars[5]);
        let (s, t) = (vars[6], vars[7]);
        let z = rzero(d, rat);

        let hor_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h3_fv = d.fresh_fvar();
        let h4_fv = d.fresh_fvar();
        let hor = d.kernel().fvar(hor_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.kernel().fvar(h3_fv);
        let h4 = d.kernel().fvar(h4_fv);

        let f = false_ty(d);
        let eu = crate::rat_prelude::ops::req(d, u, z);
        let ev = crate::rat_prelude::ops::req(d, v, z);
        let ne_u = d.arrow(eu, f);
        let ne_v = d.arrow(ev, f);
        let hor_ty = or_ty(d, ne_u, ne_v);

        let uv = rmul(d, u, bv);
        let vu = rmul(d, v, bu);
        let h1_ty = crate::rat_prelude::ops::req(d, uv, vu);
        let uw = rmul(d, u, bw);
        let wu = rmul(d, w, bu);
        let h2_ty = crate::rat_prelude::ops::req(d, uw, wu);
        let vw = rmul(d, v, bw);
        let wv = rmul(d, w, bv);
        let h3_ty = crate::rat_prelude::ops::req(d, vw, wv);
        let small = eval(d, u, v, w, s, t);
        let h4_ty = crate::rat_prelude::ops::req(d, small, z);
        let big = eval(d, bu, bv, bw, s, t);
        let concl = crate::rat_prelude::ops::req(d, big, z);

        let proof = d.or_elim(
            ne_u,
            ne_v,
            concl,
            hor,
            &|d, hnu| d.const_app(q.on_pivot, &[u, v, w, bu, bv, bw, s, t, hnu, h1, h2, h4]),
            &|d, hnv| {
                // The pivot with (u,v,s,t) and (U,V) swapped: the SAME lemma.
                let swapped_small = eval(d, v, u, w, t, s);
                let swapped_big = eval(d, bv, bu, bw, t, s);
                let h1s = rsymm(d, uv, vu, h1);
                let h4s = {
                    let step = ring_eq(d, &rat, swapped_small, small);
                    rtrans(d, swapped_small, small, z, step, h4)
                };
                let got = d.const_app(q.on_pivot, &[v, u, w, bv, bu, bw, t, s, hnv, h1s, h3, h4s]);
                let step = ring_eq(d, &rat, big, swapped_big);
                rtrans(d, big, swapped_big, z, step, got)
            },
        );

        let ty = {
            let mut t2 = d.arrow(h4_ty, concl);
            t2 = d.arrow(h3_ty, t2);
            t2 = d.arrow(h2_ty, t2);
            t2 = d.arrow(h1_ty, t2);
            t2 = d.arrow(hor_ty, t2);
            for &fv in fvs.iter().rev() {
                t2 = d.pi_fv(fv, rt, t2);
            }
            t2
        };
        let value = {
            let mut v2 = d.lam_fv(h4_fv, h4_ty, proof);
            v2 = d.lam_fv(h3_fv, h3_ty, v2);
            v2 = d.lam_fv(h2_fv, h2_ty, v2);
            v2 = d.lam_fv(h1_fv, h1_ty, v2);
            v2 = d.lam_fv(hor_fv, hor_ty, v2);
            for &fv in fvs.iter().rev() {
                v2 = d.lam_fv(fv, rt, v2);
            }
            v2
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.on_of_prop,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `lhs = rhs`, given the unconditional ring identity `lhs + k2*e2 = rhs + k1*e1`
/// and `h1 : e1 = 0`, `h2 : e2 = 0`.
fn cancel_pair(
    d: &mut IntDev<'_>,
    rat: &RatPrelude,
    lhs: ExprId,
    rhs: ExprId,
    k1: ExprId,
    e1: ExprId,
    h1: ExprId,
    k2: ExprId,
    e2: ExprId,
    h2: ExprId,
) -> ExprId {
    let z = rzero(d, *rat);
    let lhs_zero = {
        let m = rmul(d, k2, z);
        radd(d, lhs, m)
    };
    let lhs_e2 = {
        let m = rmul(d, k2, e2);
        radd(d, lhs, m)
    };
    let rhs_e1 = {
        let m = rmul(d, k1, e1);
        radd(d, rhs, m)
    };
    let rhs_zero = {
        let m = rmul(d, k1, z);
        radd(d, rhs, m)
    };
    let s1 = ring_eq(d, rat, lhs, lhs_zero);
    let h2s = rsymm(d, e2, z, h2);
    let s2 = rcongr(d, z, e2, h2s, &|d, hole| {
        let m = rmul(d, k2, hole);
        radd(d, lhs, m)
    });
    let s3 = ring_eq(d, rat, lhs_e2, rhs_e1);
    let s4 = rcongr(d, e1, z, h1, &|d, hole| {
        let m = rmul(d, k1, hole);
        radd(d, rhs, m)
    });
    let s5 = ring_eq(d, rat, rhs_zero, rhs);
    let (_, proof) = rchain(
        d,
        lhs,
        &[
            (lhs_zero, s1),
            (lhs_e2, s2),
            (rhs_e1, s3),
            (rhs_zero, s4),
            (rhs, s5),
        ],
    );
    proof
}

/// `Geo.QPlane.joinProp` — every line through `P` and `Q` is proportional to
/// `join P Q`. **No non-degeneracy hypothesis anywhere.**
fn declare_join_prop(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);

    let l_fv = d.fresh_fvar();
    let p_fv = d.fresh_fvar();
    let r_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let pt = d.kernel().fvar(p_fv);
    let rp = d.kernel().fvar(r_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);

    let av = la(d, q, l);
    let bv = lb(d, q, l);
    let cv = lc(d, q, l);
    let pxv = px(d, q, pt);
    let pyv = py(d, q, pt);
    let qxv = px(d, q, rp);
    let qyv = py(d, q, rp);
    let [big_a, big_b, big_c] = join_coeffs(d, q, pt, rp);

    let e1 = eval(d, av, bv, cv, pxv, pyv);
    let e2 = eval(d, av, bv, cv, qxv, qyv);
    let one = rone(d, rat);

    let ab = rmul(d, av, big_b);
    let ba = rmul(d, bv, big_a);
    let ac = rmul(d, av, big_c);
    let ca = rmul(d, cv, big_a);
    let bc = rmul(d, bv, big_c);
    let cb = rmul(d, cv, big_b);

    let p1 = cancel_pair(d, &rat, ab, ba, one, e1, h1, one, e2, h2);
    let p2 = cancel_pair(d, &rat, ac, ca, pyv, e2, h2, qyv, e1, h1);
    let p3 = cancel_pair(d, &rat, bc, cb, qxv, e1, h1, pxv, e2, h2);

    let z = rzero(d, rat);
    let t1 = crate::rat_prelude::ops::req(d, ab, ba);
    let t2 = crate::rat_prelude::ops::req(d, ac, ca);
    let t3 = crate::rat_prelude::ops::req(d, bc, cb);
    let tail = and_ty(d, t2, t3);
    let concl = and_ty(d, t1, tail);
    let tail_proof = and_intro(d, t2, t3, p2, p3);
    let proof = and_intro(d, t1, tail, p1, tail_proof);
    let _ = z;

    let hyp1 = d.const_app(q.on_raw, &[pt, l]);
    let hyp2 = d.const_app(q.on_raw, &[rp, l]);
    let ty = {
        let t = d.arrow(hyp2, concl);
        let t = d.arrow(hyp1, t);
        let t = d.pi_fv(r_fv, point, t);
        let t = d.pi_fv(p_fv, point, t);
        d.pi_fv(l_fv, line0, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, hyp2, proof);
        let t = d.lam_fv(h1_fv, hyp1, t);
        let t = d.lam_fv(r_fv, point, t);
        let t = d.lam_fv(p_fv, point, t);
        d.lam_fv(l_fv, line0, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: q.join_prop,
        uparams: vec![],
        ty,
        value,
    })
}

/// Reverse a proportionality relation: from `h : x*Y = y*X`, build `X*y = Y*x`.
/// Both sides differ from `h`'s only by `Rat.mul_comm`, so `ring` does it.
fn flip_rel(
    d: &mut IntDev<'_>,
    rat: &RatPrelude,
    x: ExprId,
    big_y: ExprId,
    y: ExprId,
    big_x: ExprId,
    h: ExprId,
) -> ExprId {
    let xy = rmul(d, x, big_y);
    let yx = rmul(d, y, big_x);
    let target_l = rmul(d, big_x, y);
    let target_r = rmul(d, big_y, x);
    let s1 = ring_eq(d, rat, target_l, yx);
    let s2 = rsymm(d, xy, yx, h);
    let s3 = ring_eq(d, rat, xy, target_r);
    let (_, proof) = rchain(d, target_l, &[(yx, s1), (xy, s2), (target_r, s3)]);
    proof
}

/// `Geo.QPlane.joinUnique` — the one axiom that consumes distinctness.
fn declare_join_unique(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);

    let p_fv = d.fresh_fvar();
    let r_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let hap_fv = d.fresh_fvar();
    let hpl_fv = d.fresh_fvar();
    let hql_fv = d.fresh_fvar();
    let hpm_fv = d.fresh_fvar();
    let hqm_fv = d.fresh_fvar();
    let big_r_fv = d.fresh_fvar();

    let pt = d.kernel().fvar(p_fv);
    let rp = d.kernel().fvar(r_fv);
    let l = d.kernel().fvar(l_fv);
    let m = d.kernel().fvar(m_fv);
    let hap = d.kernel().fvar(hap_fv);
    let hpl = d.kernel().fvar(hpl_fv);
    let hql = d.kernel().fvar(hql_fv);
    let hpm = d.kernel().fvar(hpm_fv);
    let hqm = d.kernel().fvar(hqm_fv);
    let big_r = d.kernel().fvar(big_r_fv);

    let l0 = lval(d, q, l);
    let m0 = lval(d, q, m);
    let al = la(d, q, l0);
    let bl = lb(d, q, l0);
    let cl = lc(d, q, l0);
    let am = la(d, q, m0);
    let bm = lb(d, q, m0);
    let cm = lc(d, q, m0);
    let [big_a, big_b, big_c] = join_coeffs(d, q, pt, rp);
    let rx = px(d, q, big_r);
    let ry = py(d, q, big_r);

    // Non-degeneracy of the two lines and of the join.
    let nd_l = lprop(d, q, l);
    let or_l = d.const_app(q.nondeg_or, &[l0, nd_l]);
    let nd_m = lprop(d, q, m);
    let or_m = d.const_app(q.nondeg_or, &[m0, nd_m]);
    let joined = d.const_app(q.join, &[pt, rp]);
    let nd_j = d.const_app(q.join_nondeg, &[pt, rp, hap]);
    let or_j = d.const_app(q.nondeg_or, &[joined, nd_j]);

    // The two proportionality bundles.
    let prop_l = d.const_app(q.join_prop, &[l0, pt, rp, hpl, hql]);
    let prop_m = d.const_app(q.join_prop, &[m0, pt, rp, hpm, hqm]);

    let split =
        |d: &mut IntDev<'_>, av: ExprId, bv: ExprId, cv: ExprId, bundle: ExprId| -> [ExprId; 3] {
            let t1 = {
                let x = rmul(d, av, big_b);
                let y = rmul(d, bv, big_a);
                crate::rat_prelude::ops::req(d, x, y)
            };
            let t2 = {
                let x = rmul(d, av, big_c);
                let y = rmul(d, cv, big_a);
                crate::rat_prelude::ops::req(d, x, y)
            };
            let t3 = {
                let x = rmul(d, bv, big_c);
                let y = rmul(d, cv, big_b);
                crate::rat_prelude::ops::req(d, x, y)
            };
            let tail_ty = and_ty(d, t2, t3);
            let first = and_l(d, t1, tail_ty, bundle);
            let tail = and_r(d, t1, tail_ty, bundle);
            let second = and_l(d, t2, t3, tail);
            let third = and_r(d, t2, t3, tail);
            [first, second, third]
        };
    let [l1, l2, l3] = split(d, al, bl, cl, prop_l);
    let [m1, m2, m3] = split(d, am, bm, cm, prop_m);

    // Reversed: `join P Q` is proportional to the line, not the other way.
    let j_l1 = flip_rel(d, &rat, al, big_b, bl, big_a, l1);
    let j_l2 = flip_rel(d, &rat, al, big_c, cl, big_a, l2);
    let j_l3 = flip_rel(d, &rat, bl, big_c, cl, big_b, l3);
    let j_m1 = flip_rel(d, &rat, am, big_b, bm, big_a, m1);
    let j_m2 = flip_rel(d, &rat, am, big_c, cm, big_a, m2);
    let j_m3 = flip_rel(d, &rat, bm, big_c, cm, big_b, m3);

    let on_r_l = d.const_app(q.on, &[big_r, l]);
    let on_r_m = d.const_app(q.on, &[big_r, m]);

    let forward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let to_join = d.const_app(
            q.on_of_prop,
            &[al, bl, cl, big_a, big_b, big_c, rx, ry, or_l, l1, l2, l3, h],
        );
        let body = d.const_app(
            q.on_of_prop,
            &[
                big_a, big_b, big_c, am, bm, cm, rx, ry, or_j, j_m1, j_m2, j_m3, to_join,
            ],
        );
        d.lam_fv(h_fv, on_r_l, body)
    };
    let backward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let to_join = d.const_app(
            q.on_of_prop,
            &[am, bm, cm, big_a, big_b, big_c, rx, ry, or_m, m1, m2, m3, h],
        );
        let body = d.const_app(
            q.on_of_prop,
            &[
                big_a, big_b, big_c, al, bl, cl, rx, ry, or_j, j_l1, j_l2, j_l3, to_join,
            ],
        );
        d.lam_fv(h_fv, on_r_m, body)
    };

    let fwd_ty = d.arrow(on_r_l, on_r_m);
    let bwd_ty = d.arrow(on_r_m, on_r_l);
    let at_r = and_intro(d, fwd_ty, bwd_ty, forward, backward);
    let proof = d.lam_fv(big_r_fv, point, at_r);

    let ap = d.const_app(q.apart, &[pt, rp]);
    let hpl_ty = d.const_app(q.on, &[pt, l]);
    let hql_ty = d.const_app(q.on, &[rp, l]);
    let hpm_ty = d.const_app(q.on, &[pt, m]);
    let hqm_ty = d.const_app(q.on, &[rp, m]);
    let concl = d.const_app(q.line_equiv, &[l, m]);
    let ty = {
        let t = d.arrow(hqm_ty, concl);
        let t = d.arrow(hpm_ty, t);
        let t = d.arrow(hql_ty, t);
        let t = d.arrow(hpl_ty, t);
        let t = d.arrow(ap, t);
        let t = d.pi_fv(m_fv, line, t);
        let t = d.pi_fv(l_fv, line, t);
        let t = d.pi_fv(r_fv, point, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(hqm_fv, hqm_ty, proof);
        let t = d.lam_fv(hpm_fv, hpm_ty, t);
        let t = d.lam_fv(hql_fv, hql_ty, t);
        let t = d.lam_fv(hpl_fv, hpl_ty, t);
        let t = d.lam_fv(hap_fv, ap, t);
        let t = d.lam_fv(m_fv, line, t);
        let t = d.lam_fv(l_fv, line, t);
        let t = d.lam_fv(r_fv, point, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: q.join_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// Eliminate `witness : Exists.{1} ty pred` into `target`.
fn exists_elim_at(
    d: &mut IntDev<'_>,
    ty: ExprId,
    pred: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let logic = d.int().logic;
    let ex_c = d.kernel().const_(logic.exists_, vec![one]);
    let ex_ty = d.apply(ex_c, &[ty, pred]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, ex_ty, target)
    };
    let rec = d.kernel().const_(logic.exists_rec, vec![one]);
    d.apply(rec, &[ty, pred, motive, minor, witness])
}

/// `shift`, `shiftOn`, `shiftApart`, `basePoint`, `twoPoints`.
fn declare_two_points(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);
    let line = line_ty(d, q);
    let logic = d.int().logic;
    let one_lvl = d.level_one();

    // shift P l := mk (x P + -(b l)) (y P + a l).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let sx = {
            let n = rneg(d, bv);
            let s = px(d, q, pt);
            radd(d, s, n)
        };
        let sy = {
            let s = py(d, q, pt);
            radd(d, s, av)
        };
        let body = pmk(d, q, sx, sy);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, point);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: q.shift,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // shiftOn : ∀ P l, onRaw P l → onRaw (shift P l) l.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let h = d.kernel().fvar(h_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let cv = lc(d, q, l);
        let pxv = px(d, q, pt);
        let pyv = py(d, q, pt);
        let sx = {
            let n = rneg(d, bv);
            radd(d, pxv, n)
        };
        let sy = radd(d, pyv, av);
        let shifted = eval(d, av, bv, cv, sx, sy);
        let plain = eval(d, av, bv, cv, pxv, pyv);
        let z = rzero(d, rat);
        let step = ring_eq(d, &rat, shifted, plain);
        let proof = rtrans(d, shifted, plain, z, step, h);

        let hyp = d.const_app(q.on_raw, &[pt, l]);
        let moved = d.const_app(q.shift, &[pt, l]);
        let concl = d.const_app(q.on_raw, &[moved, l]);
        let ty = {
            let t = d.arrow(hyp, concl);
            let t = d.pi_fv(l_fv, line0, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, hyp, proof);
            let t = d.lam_fv(l_fv, line0, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.shift_on,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // shiftApart : ∀ P l, Nondeg l → (P = shift P l → False).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let hnd_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let hnd = d.kernel().fvar(hnd_fv);
        let he = d.kernel().fvar(he_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let pxv = px(d, q, pt);
        let pyv = py(d, q, pt);
        let sx = {
            let n = rneg(d, bv);
            radd(d, pxv, n)
        };
        let sy = radd(d, pyv, av);
        let moved = d.const_app(q.shift, &[pt, l]);
        let rt = rat_ty(d);
        let z = rzero(d, rat);

        // hx : x P = x P + -(b l); hy : y P = y P + a l.
        let hx = congr_cross(d, point, rt, pt, moved, he, &|d, hole| px(d, q, hole));
        let hy = congr_cross(d, point, rt, pt, moved, he, &|d, hole| py(d, q, hole));

        // b l = 0, via `-(x P) + x P = 0` and `-(x P + -b) + x P = b`.
        let hb = {
            let start = {
                let n = rneg(d, pxv);
                radd(d, n, pxv)
            };
            let after = {
                let n = rneg(d, sx);
                radd(d, n, pxv)
            };
            let s1 = ring_eq(d, &rat, z, start);
            let s2 = rcongr(d, pxv, sx, hx, &|d, hole| {
                let n = rneg(d, hole);
                radd(d, n, pxv)
            });
            let s3 = ring_eq(d, &rat, after, bv);
            let (_, proof) = rchain(d, z, &[(start, s1), (after, s2), (bv, s3)]);
            rsymm(d, z, bv, proof)
        };
        // a l = 0, via `x + -x = 0` on the y coordinate.
        let ha = {
            let start = {
                let n = rneg(d, pyv);
                radd(d, pyv, n)
            };
            let after = {
                let n = rneg(d, pyv);
                radd(d, sy, n)
            };
            let s1 = ring_eq(d, &rat, z, start);
            let s2 = rcongr(d, pyv, sy, hy, &|d, hole| {
                let n = rneg(d, pyv);
                radd(d, hole, n)
            });
            let s3 = ring_eq(d, &rat, after, av);
            let (_, proof) = rchain(d, z, &[(start, s1), (after, s2), (av, s3)]);
            rsymm(d, z, av, proof)
        };
        let _ = rt;

        let ea = crate::rat_prelude::ops::req(d, av, z);
        let eb = crate::rat_prelude::ops::req(d, bv, z);
        let both = and_intro(d, ea, eb, ha, hb);
        let body = d.apply(hnd, &[both]);

        let eq_ty = peq(d, q, pt, moved);
        let f = false_ty(d);
        let nd_ty = d.const_app(q.nondeg, &[l]);
        let ty = {
            let t = d.arrow(eq_ty, f);
            let t = d.arrow(nd_ty, t);
            let t = d.pi_fv(l_fv, line0, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(he_fv, eq_ty, body);
            let t = d.lam_fv(hnd_fv, nd_ty, t);
            let t = d.lam_fv(l_fv, line0, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.shift_apart,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // basePoint : ∀ l, Nondeg l → ∃ P, onRaw P l.
    {
        let l_fv = d.fresh_fvar();
        let hnd_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let hnd = d.kernel().fvar(hnd_fv);
        let av = la(d, q, l);
        let bv = lb(d, q, l);
        let cv = lc(d, q, l);
        let z = rzero(d, rat);
        let one = rone(d, rat);
        let _ = one;

        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let pred = {
            let body = d.const_app(q.on_raw, &[w, l]);
            d.lam_fv(w_fv, point, body)
        };
        let target = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
            d.apply(ex_c, &[point, pred])
        };

        let ea = crate::rat_prelude::ops::req(d, av, z);
        let eb = crate::rat_prelude::ops::req(d, bv, z);
        let f = false_ty(d);
        let ne_a = d.arrow(ea, f);
        let ne_b = d.arrow(eb, f);
        let or_h = d.const_app(q.nondeg_or, &[l, hnd]);

        // A base point from a nonzero pivot `piv`, at coordinates
        // `(s, t)` with the free one carrying `-c / piv`.
        let branch =
            |d: &mut IntDev<'_>, piv: ExprId, other: ExprId, on_x: bool, hne: ExprId| -> ExprId {
                let inv = d.const_app(rat.inv, &[piv]);
                let coord = {
                    let n = rneg(d, cv);
                    rmul(d, n, inv)
                };
                let witness = if on_x {
                    pmk(d, q, coord, z)
                } else {
                    pmk(d, q, z, coord)
                };
                let (s, t) = if on_x { (coord, z) } else { (z, coord) };
                let lhs = eval(d, av, bv, cv, s, t);
                let cancel = d.const_app(rat.mul_inv_cancel_of_ne_zero, &[piv, hne]);
                let pv = rmul(d, piv, inv);
                let mid = {
                    let m = rmul(d, cv, pv);
                    let n = rneg(d, m);
                    radd(d, n, cv)
                };
                let one_r = rone(d, rat);
                let after = {
                    let m = rmul(d, cv, one_r);
                    let n = rneg(d, m);
                    radd(d, n, cv)
                };
                let s1 = ring_eq(d, &rat, lhs, mid);
                let s2 = rcongr(d, pv, one_r, cancel, &|d, hole| {
                    let m = rmul(d, cv, hole);
                    let n = rneg(d, m);
                    radd(d, n, cv)
                });
                let s3 = ring_eq(d, &rat, after, z);
                let (_, proof) = rchain(d, lhs, &[(mid, s1), (after, s2), (z, s3)]);
                let _ = other;
                exists_intro(d, point, pred, witness, proof)
            };

        let proof = d.or_elim(
            ne_a,
            ne_b,
            target,
            or_h,
            &|d, hna| branch(d, av, bv, true, hna),
            &|d, hnb| branch(d, bv, av, false, hnb),
        );

        let nd_ty = d.const_app(q.nondeg, &[l]);
        let ty = {
            let t = d.arrow(nd_ty, target);
            d.pi_fv(l_fv, line0, t)
        };
        let value = {
            let t = d.lam_fv(hnd_fv, nd_ty, proof);
            d.lam_fv(l_fv, line0, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.base_point,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // twoPoints : ∀ (l : QLine), ∃ P Q, Apart P Q ∧ (on P l ∧ on Q l).
    {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let l0 = lval(d, q, l);
        let nd = lprop(d, q, l);

        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(p_fv);
        let rv = d.kernel().fvar(r_fv);
        let inner_body = {
            let ap = d.const_app(q.apart, &[pv, rv]);
            let opl = d.const_app(q.on, &[pv, l]);
            let oql = d.const_app(q.on, &[rv, l]);
            let ons = and_ty(d, opl, oql);
            and_ty(d, ap, ons)
        };
        let inner_pred = d.lam_fv(r_fv, point, inner_body);
        let inner_ex = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
            d.apply(ex_c, &[point, inner_pred])
        };
        let outer_pred = d.lam_fv(p_fv, point, inner_ex);
        let target = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
            d.apply(ex_c, &[point, outer_pred])
        };

        // The base-point existential this eliminates.
        let base_w_fv = d.fresh_fvar();
        let base_w = d.kernel().fvar(base_w_fv);
        let base_pred = {
            let body = d.const_app(q.on_raw, &[base_w, l0]);
            d.lam_fv(base_w_fv, point, body)
        };
        let base = d.const_app(q.base_point, &[l0, nd]);

        let minor = {
            let w_fv = d.fresh_fvar();
            let hw_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let hw = d.kernel().fvar(hw_fv);
            let hw_ty = d.const_app(q.on_raw, &[w, l0]);

            let moved = d.const_app(q.shift, &[w, l0]);
            let hmoved = d.const_app(q.shift_on, &[w, l0, hw]);
            let hap = d.const_app(q.shift_apart, &[w, l0, nd]);

            let ap_ty = d.const_app(q.apart, &[w, moved]);
            let on_w = d.const_app(q.on, &[w, l]);
            let on_moved = d.const_app(q.on, &[moved, l]);
            let ons_ty = and_ty(d, on_w, on_moved);
            let ons = and_intro(d, on_w, on_moved, hw, hmoved);
            let triple = and_intro(d, ap_ty, ons_ty, hap, ons);

            let inner_at_w = {
                let r2_fv = d.fresh_fvar();
                let r2 = d.kernel().fvar(r2_fv);
                let ap = d.const_app(q.apart, &[w, r2]);
                let opl = d.const_app(q.on, &[w, l]);
                let oql = d.const_app(q.on, &[r2, l]);
                let ons2 = and_ty(d, opl, oql);
                let body = and_ty(d, ap, ons2);
                d.lam_fv(r2_fv, point, body)
            };
            let inner = exists_intro(d, point, inner_at_w, moved, triple);
            let outer = exists_intro(d, point, outer_pred, w, inner);
            let t = d.lam_fv(hw_fv, hw_ty, outer);
            d.lam_fv(w_fv, point, t)
        };

        let proof = exists_elim_at(d, point, base_pred, target, base, minor);
        let ty = d.pi_fv(l_fv, line, target);
        let value = d.lam_fv(l_fv, line, proof);
        d.kernel().add_declaration(Declaration::Theorem {
            name: q.two_points,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Geo.QPlane.triangle` — `(0,0)`, `(1,0)`, `(0,1)`.
fn declare_triangle(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let logic = d.int().logic;
    let one_lvl = d.level_one();
    let z = rzero(d, rat);
    let one = rone(d, rat);

    let a_pt = pmk(d, q, z, z);
    let b_pt = pmk(d, q, one, z);
    let c_pt = pmk(d, q, z, one);

    // Apart, from a coordinate projection landing on `one = zero`.
    let apartness = |d: &mut IntDev<'_>, u: ExprId, v: ExprId, use_x: bool, flip: bool| -> ExprId {
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let eq_ty = peq(d, q, u, v);
        let rt = rat_ty(d);
        let coord = congr_cross(d, point, rt, u, v, he, &|d, hole| {
            if use_x {
                px(d, q, hole)
            } else {
                py(d, q, hole)
            }
        });
        // `coord` proves `0 = 1` or `1 = 0` after iota; orient it as `1 = 0`.
        let oriented = if flip { rsymm(d, z, one, coord) } else { coord };
        let ne = d.const_app(rat.one_ne_zero, &[]);
        let body = d.apply(ne, &[oriented]);
        d.lam_fv(he_fv, eq_ty, body)
    };
    let ab = apartness(d, a_pt, b_pt, true, true);
    let ac = apartness(d, a_pt, c_pt, false, true);
    let bc = apartness(d, b_pt, c_pt, true, false);

    // No line carries all three.
    let no_line = {
        let l_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let hb_fv = d.fresh_fvar();
        let hc_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let ha = d.kernel().fvar(ha_fv);
        let hb = d.kernel().fvar(hb_fv);
        let hc = d.kernel().fvar(hc_fv);
        let l0 = lval(d, q, l);
        let nd = lprop(d, q, l);
        let av = la(d, q, l0);
        let bv = lb(d, q, l0);
        let cv = lc(d, q, l0);

        // c = 0, straight from the origin being on the line.
        let at_origin = eval(d, av, bv, cv, z, z);
        let hc0 = {
            let s1 = ring_eq(d, &rat, cv, at_origin);
            let (_, proof) = rchain(d, cv, &[(at_origin, s1), (z, ha)]);
            proof
        };
        // a = 0, from (1,0) plus `c = 0`.
        let at_b = eval(d, av, bv, cv, one, z);
        let ha0 = {
            let start = {
                let n = rneg(d, cv);
                radd(d, at_b, n)
            };
            let mid = {
                let n = rneg(d, cv);
                radd(d, z, n)
            };
            let end = {
                let n = rneg(d, z);
                radd(d, z, n)
            };
            let s1 = ring_eq(d, &rat, av, start);
            let s2 = rcongr(d, at_b, z, hb, &|d, hole| {
                let n = rneg(d, cv);
                radd(d, hole, n)
            });
            let s3 = rcongr(d, cv, z, hc0, &|d, hole| {
                let n = rneg(d, hole);
                radd(d, z, n)
            });
            let s4 = ring_eq(d, &rat, end, z);
            let (_, proof) = rchain(d, av, &[(start, s1), (mid, s2), (end, s3), (z, s4)]);
            proof
        };
        // b = 0, from (0,1) plus `c = 0`.
        let at_c = eval(d, av, bv, cv, z, one);
        let hb0 = {
            let start = {
                let n = rneg(d, cv);
                radd(d, at_c, n)
            };
            let mid = {
                let n = rneg(d, cv);
                radd(d, z, n)
            };
            let end = {
                let n = rneg(d, z);
                radd(d, z, n)
            };
            let s1 = ring_eq(d, &rat, bv, start);
            let s2 = rcongr(d, at_c, z, hc, &|d, hole| {
                let n = rneg(d, cv);
                radd(d, hole, n)
            });
            let s3 = rcongr(d, cv, z, hc0, &|d, hole| {
                let n = rneg(d, hole);
                radd(d, z, n)
            });
            let s4 = ring_eq(d, &rat, end, z);
            let (_, proof) = rchain(d, bv, &[(start, s1), (mid, s2), (end, s3), (z, s4)]);
            proof
        };

        let ea = crate::rat_prelude::ops::req(d, av, z);
        let eb = crate::rat_prelude::ops::req(d, bv, z);
        let both = and_intro(d, ea, eb, ha0, hb0);
        let body = d.apply(nd, &[both]);

        let ha_ty = d.const_app(q.on, &[a_pt, l]);
        let hb_ty = d.const_app(q.on, &[b_pt, l]);
        let hc_ty = d.const_app(q.on, &[c_pt, l]);
        let t = d.lam_fv(hc_fv, hc_ty, body);
        let t = d.lam_fv(hb_fv, hb_ty, t);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        d.lam_fv(l_fv, line, t)
    };

    // Assemble `∃ A B C, apart ∧ (apart ∧ (apart ∧ no-line))`.
    let no_line_ty = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let ha_ty = d.const_app(q.on, &[a_pt, l]);
        let hb_ty = d.const_app(q.on, &[b_pt, l]);
        let hc_ty = d.const_app(q.on, &[c_pt, l]);
        let f = false_ty(d);
        let t = d.arrow(hc_ty, f);
        let t = d.arrow(hb_ty, t);
        let t = d.arrow(ha_ty, t);
        d.pi_fv(l_fv, line, t)
    };
    let ab_ty = d.const_app(q.apart, &[a_pt, b_pt]);
    let ac_ty = d.const_app(q.apart, &[a_pt, c_pt]);
    let bc_ty = d.const_app(q.apart, &[b_pt, c_pt]);
    let lvl3_ty = and_ty(d, bc_ty, no_line_ty);
    let lvl3 = and_intro(d, bc_ty, no_line_ty, bc, no_line);
    let lvl2_ty = and_ty(d, ac_ty, lvl3_ty);
    let lvl2 = and_intro(d, ac_ty, lvl3_ty, ac, lvl3);
    let lvl1 = and_intro(d, ab_ty, lvl2_ty, ab, lvl2);

    // The three nested predicates, as the statement requires them.
    let triple_pred = |d: &mut IntDev<'_>, ua: ExprId, ub: ExprId| -> ExprId {
        let c_fv = d.fresh_fvar();
        let cv = d.kernel().fvar(c_fv);
        let t_ab = d.const_app(q.apart, &[ua, ub]);
        let t_ac = d.const_app(q.apart, &[ua, cv]);
        let t_bc = d.const_app(q.apart, &[ub, cv]);
        let nl = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let h1 = d.const_app(q.on, &[ua, l]);
            let h2 = d.const_app(q.on, &[ub, l]);
            let h3 = d.const_app(q.on, &[cv, l]);
            let f = false_ty(d);
            let t = d.arrow(h3, f);
            let t = d.arrow(h2, t);
            let t = d.arrow(h1, t);
            d.pi_fv(l_fv, line, t)
        };
        let t3 = and_ty(d, t_bc, nl);
        let t2 = and_ty(d, t_ac, t3);
        let body = and_ty(d, t_ab, t2);
        d.lam_fv(c_fv, point, body)
    };
    let pred_c = triple_pred(d, a_pt, b_pt);
    let ex_c_term = exists_intro(d, point, pred_c, c_pt, lvl1);

    let pred_b = {
        let b_fv = d.fresh_fvar();
        let bv = d.kernel().fvar(b_fv);
        let inner = triple_pred(d, a_pt, bv);
        let body = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
            d.apply(ex_c, &[point, inner])
        };
        d.lam_fv(b_fv, point, body)
    };
    let ex_b_term = exists_intro(d, point, pred_b, b_pt, ex_c_term);

    let pred_a = {
        let a_fv = d.fresh_fvar();
        let av = d.kernel().fvar(a_fv);
        let inner_b = {
            let b_fv = d.fresh_fvar();
            let bv = d.kernel().fvar(b_fv);
            let inner = triple_pred(d, av, bv);
            let body = {
                let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
                d.apply(ex_c, &[point, inner])
            };
            d.lam_fv(b_fv, point, body)
        };
        let body = {
            let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
            d.apply(ex_c, &[point, inner_b])
        };
        d.lam_fv(a_fv, point, body)
    };
    let proof = exists_intro(d, point, pred_a, a_pt, ex_b_term);
    let ty = {
        let ex_c = d.kernel().const_(logic.exists_, vec![one_lvl]);
        d.apply(ex_c, &[point, pred_a])
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: q.triangle,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// `Geo.qplane : Geo.Incidence`.
fn declare_instance(d: &mut IntDev<'_>, p: GeoPrelude, q: QPlaneNames) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let one = d.level_one();
    let logic = d.int().logic;

    let peq_fn = {
        let c = d.kernel().const_(logic.eq, vec![one]);
        d.apply(c, &[point])
    };
    let prefl = {
        let c = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(c, &[point])
    };
    let psymm = {
        let c = d.kernel().const_(logic.eq_symm, vec![one]);
        d.apply(c, &[point])
    };
    let ptrans = d.kernel().const_(q.qpoint_eq_trans, vec![]);
    let leq = d.kernel().const_(q.line_equiv, vec![]);
    let lrefl = d.kernel().const_(q.line_equiv_refl, vec![]);
    let lsymm = d.kernel().const_(q.line_equiv_symm, vec![]);
    let ltrans = d.kernel().const_(q.line_equiv_trans, vec![]);
    let on = d.kernel().const_(q.on, vec![]);
    let on_point = d.kernel().const_(q.on_point, vec![]);
    let on_line = d.kernel().const_(q.on_line, vec![]);
    let apart = d.kernel().const_(q.apart, vec![]);
    let apart_ne = d.kernel().const_(q.apart_ne, vec![]);
    let apart_symm = d.kernel().const_(q.apart_symm, vec![]);
    let apart_congr = d.kernel().const_(q.apart_congr, vec![]);
    let join_exists = d.kernel().const_(q.join_exists, vec![]);
    let join_unique = d.kernel().const_(q.join_unique, vec![]);
    let two_points = d.kernel().const_(q.two_points, vec![]);
    let triangle = d.kernel().const_(q.triangle, vec![]);

    let args = [
        point,
        line,
        peq_fn,
        prefl,
        psymm,
        ptrans,
        leq,
        lrefl,
        lsymm,
        ltrans,
        on,
        on_point,
        on_line,
        apart,
        apart_ne,
        apart_symm,
        apart_congr,
        join_exists,
        join_unique,
        two_points,
        triangle,
    ];
    assert_eq!(
        args.len(),
        super::FIELD_COUNT,
        "the instance's argument list is out of step with the record"
    );
    let value = mk_instance(d.kernel(), &p.record, &args);
    let ty = d.kernel().const_(p.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: q.instance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}
