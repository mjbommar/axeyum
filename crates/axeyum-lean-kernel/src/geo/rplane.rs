//! `Geo.RPlane` — **the real coordinate plane as a model of
//! [`Geo.Incidence`](super)**, and therefore the second, harder consistency
//! proof for the ADR-1635 axioms.
//!
//! # Why this file exists, and what ADR-1635 predicted
//!
//! [`geo.rs`](super)'s module doc says the record carries `apart` as a field
//! of its own *because* an ℝ² model cannot state `joinUnique` with `¬ Equiv`:
//! over `CReal` a double-negated hypothesis constructs nothing, and every
//! division in this development goes through `CReal.inv`, which consumes a
//! `CReal.PosBound` witness. This file is that prediction discharged. Point
//! apartness here is
//!
//! ```text
//! Geo.RPlane.Apart P Q := ∃ (k : Nat), CReal.PosBound (CPoint.distSq P Q) k
//! ```
//!
//! and line non-degeneracy is the same idiom one dimension down:
//!
//! ```text
//! Geo.RLine0.Nondeg l := ∃ (k : Nat), CReal.PosBound (a l * a l + b l * b l) k
//! ```
//!
//! # The construction
//!
//! ```text
//! Geo.RLine0 : Type 0 | mk : CReal → CReal → CReal → Geo.RLine0
//! Geo.RLine0.a, .b, .c : Geo.RLine0 → CReal
//! Geo.RLine  : Type 0 := Subtype Geo.RLine0 Geo.RLine0.Nondeg
//! Geo.RPlane.onRaw P l : Prop := CReal.Equiv (a l * x P + b l * y P + c l) 0
//! Geo.RPlane.on    P l : Prop := onRaw P (Subtype.val … l)
//! ```
//!
//! Points are `CPoint`, and point equality is `CPoint.Equiv` — **not** `Eq`,
//! which is the first structural difference from [`qplane`](super::qplane):
//! two reals are equal here only up to `CReal.Equiv`, so every incidence
//! statement is an `Equiv` and every substitution is a congruence, never a
//! `Eq.rec`.
//!
//! # The second structural difference: **no case split anywhere**
//!
//! `Geo.qplane` needs ℚ's decidable equality twice — `Geo.QLine0.nondeg_or`
//! turns `Nondeg` into `a ≠ 0 ∨ b ≠ 0` for the pivot, and the same
//! disjunction produces a line's first point. Neither is available over ℝ:
//! `a² + b² > 0` does not constructively hand you which of `a`, `b` is the
//! nonzero one, and `Or.rec` could not eliminate into a `CPoint` if it did.
//!
//! So the ℝ model divides by a **quantity that is positive outright**, and
//! there are exactly two of them:
//!
//! | divided by | supplied by | used for |
//! | --- | --- | --- |
//! | `distSq P Q` | `Apart P Q` | `pivotAB` — the two lines' coefficient vectors are parallel |
//! | `a*a + b*b` | `Nondeg l` | `onOfDefects` and `twoPointsRaw` |
//!
//! Both are sums of two squares, both are exactly the `PosBound`-witnessed
//! hypothesis the statement already carries, and neither needs to know which
//! summand is large. **The ℝ model is shorter than the ℚ one for this
//! reason**, not longer: `Geo.QPlane` pays for `Rat.inv` at a case split
//! (`Geo.QPlane.basePoint`, `Geo.QPlane.onOfProp`), and this file pays
//! nothing.
//!
//! # Where the work is: three defects, then one pivot
//!
//! Write `l = (a,b,c)`, `m = (A,B,C)`, and call the three *defects*
//!
//! ```text
//! dAB := a*B − b*A     dAC := a*C − c*A     dBC := b*C − c*B
//! ```
//!
//! Two lines are the same line exactly when all three vanish. `joinUnique`
//! establishes them in order:
//!
//! 1. `Geo.RPlane.pivotAB` — over six bare reals `a b A B u v`, from
//!    `a*u + b*v ~ 0` and `A*u + B*v ~ 0`, conclude `dAB * (u*u + v*v) ~ 0`.
//!    The underlying identity is unconditional:
//!    `(a*B − b*A)*(u² + v²) = (B*u − A*v)*(a*u + b*v) + (a*v − b*u)*(A*u + B*v)`.
//!    At `u := x P − x Q`, `v := y P − y Q` the second factor is
//!    **definitionally** `CPoint.distSq P Q` (`distSq` is `dot` of `sub` with
//!    itself, and both unfold), so `Apart P Q`'s own witness cancels it —
//!    `Geo.RPlane.cancelPosBound` — leaving `dAB ~ 0`.
//! 2. `Geo.RPlane.defectAC` / `Geo.RPlane.defectBC` — the other two
//!    defects follow from `dAB ~ 0` and the incidence at **one** point, with
//!    no further division:
//!    `a*C − c*A = a*E₁ − A*e₁ − q*dAB` and `b*C − c*B = b*E₁ − B*e₁ + p*dAB`,
//!    both unconditional ring identities in `e₁ := a*p + b*q + c` and
//!    `E₁ := A*p + B*q + C`.
//! 3. `Geo.RPlane.onOfDefects` — with all three defects zero and `l`
//!    non-degenerate, every point of `l` is a point of `m`:
//!    `(a² + b²)*(A*x + B*y + C)
//!       = (a*A + b*B)*(a*x + b*y + c) + (a*y − b*x)*dAB + a*dAC + b*dBC`,
//!    and `Nondeg l` cancels the left factor.
//!
//! `Geo.RPlane.defectSwap` flips a defect (`α*β' − β*α' ~ 0` gives
//! `α'*β − β'*α ~ 0`, by multiplying through by `−1`), so `joinUnique`'s two
//! directions are the same lemma applied twice rather than two proofs.
//!
//! Every polynomial identity above is emitted by `rn_ring_proof` — the
//! `CReal` ring normaliser `creal_point.rs` already carries — and never
//! written by hand.
//!
//! # `twoPoints` and `triangle`
//!
//! A non-degenerate line's first point is `(−a*c/N, −b*c/N)` with
//! `N := a² + b²`, and its second is that plus the direction `(−b, a)`; their
//! `distSq` is `N` itself, so the two points are apart **by the line's own
//! non-degeneracy witness** with nothing new to prove. The triangle is
//! `(0,0)`, `(1,0)`, `(0,1)`, whose three squared distances are `1`, `1` and
//! `CPoint.Scalar.two`; positivity comes from `CReal.zero_lt_one` and
//! `CPoint.Scalar.twoPosBound` through `CReal.pos_bound_of_lt`.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::GeoPrelude;
use crate::CPointPrelude;
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::creal_point::{
    RnExpr, rn_cadd, rn_cchain, rn_cmul, rn_cneg, rn_cone, rn_crefl, rn_csymm, rn_ctrans, rn_czero,
    rn_ring_proof,
};
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;

/// The interned names [`declare_all`] produces.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RPlaneNames {
    /// `Geo.RLine0 : Type 0` — a raw `CReal` coefficient triple.
    pub rline0: NameId,
    /// `Geo.RLine0.mk : CReal → CReal → CReal → Geo.RLine0`.
    pub rline0_mk: NameId,
    /// `Geo.RLine0.rec`.
    pub rline0_rec: NameId,
    /// `Geo.RLine0.a : Geo.RLine0 → CReal`.
    pub rline0_a: NameId,
    /// `Geo.RLine0.b : Geo.RLine0 → CReal`.
    pub rline0_b: NameId,
    /// `Geo.RLine0.c : Geo.RLine0 → CReal`.
    pub rline0_c: NameId,
    /// `Geo.RLine0.Nondeg : Geo.RLine0 → Prop` —
    /// `∃ k, CReal.PosBound (a l * a l + b l * b l) k`.
    ///
    /// **Apartness, not `¬ Equiv`.** The witnessed form is what
    /// [`Self::on_of_defects`] and [`Self::two_points_raw`] can actually
    /// divide by; `(a ~ 0 ∧ b ~ 0) → False` would construct nothing.
    pub nondeg: NameId,
    /// `Geo.RLine : Type 0 := Subtype Geo.RLine0 Geo.RLine0.Nondeg`.
    pub rline: NameId,

    /// `Geo.RPlane.onRaw : CPoint → Geo.RLine0 → Prop`.
    pub on_raw: NameId,
    /// `Geo.RPlane.on : CPoint → Geo.RLine → Prop`.
    pub on: NameId,
    /// `Geo.RPlane.Apart : CPoint → CPoint → Prop` —
    /// `∃ k, CReal.PosBound (CPoint.distSq P Q) k`.
    pub apart: NameId,

    /// `Geo.RLine.Equiv : Geo.RLine → Geo.RLine → Prop` — extensional.
    pub line_equiv: NameId,
    /// `Geo.RLine.equiv_refl`.
    pub line_equiv_refl: NameId,
    /// `Geo.RLine.equiv_symm`.
    pub line_equiv_symm: NameId,
    /// `Geo.RLine.equiv_trans`.
    pub line_equiv_trans: NameId,

    /// `Geo.RPlane.posBoundCongr : ∀ x y k, CReal.Equiv x y →
    /// CReal.PosBound x k → CReal.PosBound y k` — `CReal.le_congr` at the
    /// definitional unfolding of `PosBound`, which `creal.rs` never stated.
    pub pos_bound_congr: NameId,
    /// `Geo.RPlane.notZeroOfPosBound : ∀ x k, CReal.PosBound x k →
    /// CReal.Equiv x CReal.zero → False`.
    pub not_zero_of_pos_bound: NameId,
    /// `Geo.RPlane.cancelPosBound : ∀ n m k, CReal.PosBound n k →
    /// CReal.Equiv (CReal.mul m n) CReal.zero → CReal.Equiv m CReal.zero`.
    ///
    /// **The one division this model performs**, factored out so both places
    /// that need it (`joinUnique`'s pivot and `onOfDefects`) share one
    /// `CReal.inv`/`CReal.mul_inv_cancel` route.
    pub cancel_pos_bound: NameId,

    /// `Geo.RPlane.pointRefl : ∀ P, CPoint.Equiv P P`.
    ///
    /// `CPoint.Equiv` is a `Definition` and `creal_point.rs` builds its setoid
    /// laws inline without ever naming them; the record's `pEq` slot needs all
    /// three as terms.
    ///
    /// **These are the THIRD copies of these three propositions, and that is a
    /// deliberate trade, not an oversight.** `metric.rs` already declares
    /// `Metric.CPoint.equivRefl`/`equivSymm`/`equivTrans` — its own doc says
    /// "the plane prelude builds this inline and never names it" — but
    /// `build_geo_prelude` depends on `build_cpoint_prelude`, not on
    /// `build_metric_prelude`, and reusing them would put the whole metric
    /// prelude into every geo build to save three one-line lemmas. The right
    /// long-term home for them is `creal_point.rs` beside `CPoint.Equiv`
    /// itself, at which point both copies here and in `metric.rs` should go.
    /// Recorded rather than quietly duplicated, because the search that would
    /// have found `metric.rs`'s copies is the one this lane skipped: the
    /// `CPointPrelude` field list is not the authority for names under
    /// `CPoint`, since another prelude may declare into that namespace.
    pub point_refl: NameId,
    /// `Geo.RPlane.pointSymm : ∀ P Q, CPoint.Equiv P Q → CPoint.Equiv Q P`.
    pub point_symm: NameId,
    /// `Geo.RPlane.pointTrans : ∀ P Q R, CPoint.Equiv P Q → CPoint.Equiv Q R →
    /// CPoint.Equiv P R`.
    pub point_trans: NameId,

    /// `Geo.RPlane.onPoint : ∀ P Q l, CPoint.Equiv P Q → on P l → on Q l`.
    pub on_point: NameId,
    /// `Geo.RPlane.onLine : ∀ P l m, Geo.RLine.Equiv l m → on P l → on P m`.
    pub on_line: NameId,
    /// `Geo.RPlane.apartNe : ∀ P Q, Apart P Q → CPoint.Equiv P Q → False`.
    pub apart_ne: NameId,
    /// `Geo.RPlane.apartSymm : ∀ P Q, Apart P Q → Apart Q P`.
    pub apart_symm: NameId,
    /// `Geo.RPlane.apartCongr : ∀ P P' Q, CPoint.Equiv P P' → Apart P Q →
    /// Apart P' Q`.
    pub apart_congr: NameId,

    /// `Geo.RPlane.join : CPoint → CPoint → Geo.RLine0` — the cross product
    /// `(y Q − y P, x P − x Q, y P * x Q − x P * y Q)`.
    pub join: NameId,
    /// `Geo.RPlane.joinOnLeft : ∀ P Q, onRaw P (join P Q)`.
    pub join_on_left: NameId,
    /// `Geo.RPlane.joinOnRight : ∀ P Q, onRaw Q (join P Q)`.
    pub join_on_right: NameId,
    /// `Geo.RPlane.joinNondeg : ∀ P Q k, CReal.PosBound (CPoint.distSq P Q) k
    /// → Geo.RLine0.Nondeg (join P Q)` — **the join's own sum of squares IS
    /// `distSq P Q`**, up to a ring identity, so this consumes the apartness
    /// witness verbatim and invents no new modulus.
    pub join_nondeg: NameId,
    /// `Geo.RPlane.joinExists : ∀ P Q, Apart P Q → ∃ l, on P l ∧ on Q l`.
    pub join_exists: NameId,

    /// `Geo.RPlane.pivotAB` — see the module docs. The only place `distSq` is
    /// divided by.
    pub pivot_ab: NameId,
    /// `Geo.RPlane.defectAC`.
    pub defect_ac: NameId,
    /// `Geo.RPlane.defectBC`.
    pub defect_bc: NameId,
    /// `Geo.RPlane.defectSwap : ∀ α β α' β',
    /// Equiv (α*β' − β*α') 0 → Equiv (α'*β − β'*α) 0`.
    pub defect_swap: NameId,
    /// `Geo.RPlane.onOfDefects` — see the module docs.
    pub on_of_defects: NameId,
    /// `Geo.RPlane.joinUnique : ∀ P Q l m, Apart P Q →
    /// on P l → on Q l → on P m → on Q m → Geo.RLine.Equiv l m`.
    pub join_unique: NameId,

    /// `Geo.RPlane.twoPointsRaw : ∀ (l : Geo.RLine0) (k : Nat),
    /// CReal.PosBound (a l * a l + b l * b l) k →
    /// ∃ P Q, Apart P Q ∧ (onRaw P l ∧ onRaw Q l)` — the `k` is bound
    /// **outside** the existential because `CReal.inv` takes it as data.
    pub two_points_raw: NameId,
    /// `Geo.RPlane.twoPoints : ∀ l, ∃ P Q, Apart P Q ∧ (on P l ∧ on Q l)`.
    pub two_points: NameId,
    /// `Geo.RPlane.triangle` — `(0,0)`, `(1,0)`, `(0,1)` are pairwise apart
    /// and no non-degenerate line carries all three.
    pub triangle: NameId,

    /// `Geo.rplane : Geo.Incidence` — the model itself.
    pub instance: NameId,
}

/// Pre-compute every name this module declares. `geo` is the `Geo` namespace
/// root interned by [`super::intern`].
pub(crate) fn intern(kernel: &mut Kernel, geo: NameId) -> RPlaneNames {
    let rline0 = kernel.name_str(geo, "RLine0");
    let rline = kernel.name_str(geo, "RLine");
    let plane = kernel.name_str(geo, "RPlane");

    RPlaneNames {
        rline0,
        rline0_mk: kernel.name_str(rline0, "mk"),
        rline0_rec: kernel.name_str(rline0, "rec"),
        rline0_a: kernel.name_str(rline0, "a"),
        rline0_b: kernel.name_str(rline0, "b"),
        rline0_c: kernel.name_str(rline0, "c"),
        nondeg: kernel.name_str(rline0, "Nondeg"),
        rline,

        on_raw: kernel.name_str(plane, "onRaw"),
        on: kernel.name_str(plane, "on"),
        apart: kernel.name_str(plane, "Apart"),

        line_equiv: kernel.name_str(rline, "Equiv"),
        line_equiv_refl: kernel.name_str(rline, "equiv_refl"),
        line_equiv_symm: kernel.name_str(rline, "equiv_symm"),
        line_equiv_trans: kernel.name_str(rline, "equiv_trans"),

        pos_bound_congr: kernel.name_str(plane, "posBoundCongr"),
        not_zero_of_pos_bound: kernel.name_str(plane, "notZeroOfPosBound"),
        cancel_pos_bound: kernel.name_str(plane, "cancelPosBound"),

        point_refl: kernel.name_str(plane, "pointRefl"),
        point_symm: kernel.name_str(plane, "pointSymm"),
        point_trans: kernel.name_str(plane, "pointTrans"),

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

        pivot_ab: kernel.name_str(plane, "pivotAB"),
        defect_ac: kernel.name_str(plane, "defectAC"),
        defect_bc: kernel.name_str(plane, "defectBC"),
        defect_swap: kernel.name_str(plane, "defectSwap"),
        on_of_defects: kernel.name_str(plane, "onOfDefects"),
        join_unique: kernel.name_str(plane, "joinUnique"),

        two_points_raw: kernel.name_str(plane, "twoPointsRaw"),
        two_points: kernel.name_str(plane, "twoPoints"),
        triangle: kernel.name_str(plane, "triangle"),

        instance: kernel.name_str(geo, "rplane"),
    }
}

// ---------------------------------------------------------------------------
// Term shorthands. `CReal` algebra goes through `creal_point`'s `rn_*`
// family so that every expression this file builds is the shape
// `rn_ring_proof` renders — a hand-rolled `add`/`mul` would be defeq but not
// syntactically identical, and the ring producer's output has to land on the
// nose.
// ---------------------------------------------------------------------------

fn real_ty(d: &mut IntDev<'_>, cr: CRealPrelude) -> ExprId {
    d.kernel().const_(cr.creal, vec![])
}

fn point_ty(d: &mut IntDev<'_>, cp: CPointPrelude) -> ExprId {
    d.kernel().const_(cp.point, vec![])
}

fn line0_ty(d: &mut IntDev<'_>, r: RPlaneNames) -> ExprId {
    d.kernel().const_(r.rline0, vec![])
}

fn line_ty(d: &mut IntDev<'_>, r: RPlaneNames) -> ExprId {
    d.kernel().const_(r.rline, vec![])
}

fn prop_ty(d: &mut IntDev<'_>) -> ExprId {
    let l0 = d.kernel().level_zero();
    d.kernel().sort(l0)
}

fn px(d: &mut IntDev<'_>, cp: CPointPrelude, p: ExprId) -> ExprId {
    d.const_app(cp.x, &[p])
}

fn py(d: &mut IntDev<'_>, cp: CPointPrelude, p: ExprId) -> ExprId {
    d.const_app(cp.y, &[p])
}

fn pmk(d: &mut IntDev<'_>, cp: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(cp.mk, &[x, y])
}

fn la(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_a, &[l])
}

fn lb(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_b, &[l])
}

fn lc(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_c, &[l])
}

fn lmk(d: &mut IntDev<'_>, r: RPlaneNames, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    d.const_app(r.rline0_mk, &[a, b, c])
}

/// `CReal.Equiv a b`.
fn ceq(d: &mut IntDev<'_>, cr: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cr.equiv, &[a, b])
}

/// `CPoint.distSq P Q`.
fn dist_sq(d: &mut IntDev<'_>, cp: CPointPrelude, p: ExprId, q: ExprId) -> ExprId {
    d.const_app(cp.dist_sq, &[p, q])
}

/// `CReal.PosBound x k`.
fn pos_bound(d: &mut IntDev<'_>, cr: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(cr.pos_bound, &[x, k])
}

/// `a * s + b * t + c`, the raw incidence expression, left-associated exactly
/// as [`RnExpr`] renders it.
fn eval3(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    s: ExprId,
    t: ExprId,
) -> ExprId {
    let m1 = rn_cmul(d, cr, a, s);
    let m2 = rn_cmul(d, cr, b, t);
    let sum = rn_cadd(d, cr, m1, m2);
    rn_cadd(d, cr, sum, c)
}

fn false_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().logic.false_;
    d.kernel().const_(name, vec![])
}

fn and_ty(d: &mut IntDev<'_>, p: ExprId, q: ExprId) -> ExprId {
    let name = d.int().logic.and;
    d.const_app(name, &[p, q])
}

fn and_intro(d: &mut IntDev<'_>, p: ExprId, q: ExprId, hp: ExprId, hq: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[p, q, hp, hq])
}

fn and_l(d: &mut IntDev<'_>, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_left;
    d.const_app(name, &[p, q, h])
}

fn and_r(d: &mut IntDev<'_>, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_right;
    d.const_app(name, &[p, q, h])
}

/// `Exists.{1} ty pred`.
fn exists_ty(d: &mut IntDev<'_>, ty: ExprId, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let c = d.kernel().const_(name, vec![one]);
    d.apply(c, &[ty, pred])
}

/// `Exists.intro.{1} ty pred w proof`.
fn exists_intro(d: &mut IntDev<'_>, ty: ExprId, pred: ExprId, w: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let c = d.kernel().const_(name, vec![one]);
    d.apply(c, &[ty, pred, w, proof])
}

/// `Subtype.val.{1} Geo.RLine0 Geo.RLine0.Nondeg l`.
fn lval(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let val = d.kernel().const_(sigma.subtype_val, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(val, &[base, nd, l])
}

/// `Subtype.mk.{1} Geo.RLine0 Geo.RLine0.Nondeg l proof`.
fn lsub(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let mk = d.kernel().const_(sigma.subtype_mk, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(mk, &[base, nd, l, proof])
}

/// `Subtype.property.{1} Geo.RLine0 Geo.RLine0.Nondeg l`.
fn lprop(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let prop = d.kernel().const_(sigma.subtype_property, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(prop, &[base, nd, l])
}

/// A ring identity over ℝ, searched for and emitted by `rn_ring_proof` —
/// never written by hand.
///
/// # Panics
///
/// `rn_ring_proof` panics itself when the two normal forms differ; this
/// wrapper exists only to keep the call sites readable.
fn ring(d: &mut IntDev<'_>, cr: CRealPrelude, lhs: &RnExpr, rhs: &RnExpr) -> ExprId {
    rn_ring_proof(d, cr, lhs, rhs)
}

/// `RnExpr::Atom`, spelled short.
fn at(e: ExprId) -> RnExpr {
    RnExpr::Atom(e)
}

/// `a − b`, as `RnExpr`.
fn rsub(a: RnExpr, b: RnExpr) -> RnExpr {
    RnExpr::add(a, RnExpr::neg(b))
}

/// `a*s + b*t + c`, as `RnExpr` — the [`eval3`] shape.
fn rev3(a: RnExpr, b: RnExpr, c: RnExpr, s: RnExpr, t: RnExpr) -> RnExpr {
    RnExpr::add(RnExpr::add(RnExpr::mul(a, s), RnExpr::mul(b, t)), c)
}

/// Given `h : Equiv x CReal.zero`, a proof of `Equiv (mul f x) CReal.zero`.
fn mul_hyp_zero(d: &mut IntDev<'_>, cr: CRealPrelude, f: ExprId, x: ExprId, h: ExprId) -> ExprId {
    let zero = rn_czero(d, cr);
    let refl_f = rn_crefl(d, cr, f);
    let step = d.lemma(cr.mul_congr, &[f, f, x, zero, refl_f, h]);
    let f_zero = rn_cmul(d, cr, f, zero);
    let collapse = d.lemma(cr.mul_zero, &[f]);
    let start = rn_cmul(d, cr, f, x);
    rn_ctrans(d, cr, start, f_zero, zero, step, collapse)
}

/// Given `(fᵢ, xᵢ, hᵢ : Equiv xᵢ 0)`, a proof that the left-nested sum
/// `((f₁*x₁ + f₂*x₂) + …)` is `Equiv` to `CReal.zero`.
///
/// # Panics
///
/// Panics on an empty slice: every call site here has a fixed, nonempty
/// summand list, so an empty one is a coding error in this file.
fn sum_hyp_zero(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    terms: &[(ExprId, ExprId, ExprId)],
) -> ExprId {
    assert!(!terms.is_empty(), "sum_hyp_zero needs at least one summand");
    let zero = rn_czero(d, cr);
    let (f0, x0, h0) = terms[0];
    let mut acc_term = rn_cmul(d, cr, f0, x0);
    let mut acc_proof = mul_hyp_zero(d, cr, f0, x0, h0);
    for &(f, x, h) in &terms[1..] {
        let next = rn_cmul(d, cr, f, x);
        let next_proof = mul_hyp_zero(d, cr, f, x, h);
        let summed = rn_cadd(d, cr, acc_term, next);
        let both = d.lemma(
            cr.add_congr,
            &[acc_term, zero, next, zero, acc_proof, next_proof],
        );
        let zz = rn_cadd(d, cr, zero, zero);
        let trim = d.lemma(cr.add_zero, &[zero]);
        acc_proof = rn_ctrans(d, cr, summed, zz, zero, both, trim);
        acc_term = summed;
    }
    acc_proof
}

/// `CReal.ofRat (Rat.natDivSucc 1 k)` — the left-hand side `CReal.PosBound`
/// unfolds to, needed verbatim to apply `CReal.le_congr` at it.
fn pos_gap(d: &mut IntDev<'_>, cr: CRealPrelude, k: ExprId) -> ExprId {
    let one = d.num(1);
    let q = d.const_app(cr.rat.nat_div_succ, &[one, k]);
    d.const_app(cr.of_rat, &[q])
}

// ---------------------------------------------------------------------------
// The build.
// ---------------------------------------------------------------------------

/// Declare the whole ℝ model and the `Geo.rplane` instance.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics when `rn_ring_proof` declines an identity this file claims is a ring
/// identity — see [`ring`].
pub(crate) fn declare_all(kernel: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let cp = p.cpoint;
    let cr = cp.creal;
    let r = p.rplane;
    let mut dev = IntDev::new(kernel, cr.rat.int);
    let d = &mut dev;

    declare_carriers(d, cr, r)?;
    declare_nondeg(d, cr, r)?;
    declare_incidence(d, cp, cr, r)?;
    declare_line_equiv(d, cp, r)?;
    declare_pos_bound_lemmas(d, cr, r)?;
    declare_point_setoid(d, cp, cr, r)?;
    declare_congruences(d, cp, cr, r)?;
    declare_defects(d, cr, r)?;
    declare_join(d, cp, cr, r)?;
    declare_join_unique(d, cp, cr, r)?;
    declare_two_points(d, cp, cr, r)?;
    declare_triangle(d, cp, cr, r)?;
    declare_instance(d, p, r)
}

/// `Geo.RLine0` and its three projections.
fn declare_carriers(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let rt = real_ty(d, cr);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    let line = line0_ty(d, r);
    let mk_ty = {
        let inner = d.arrow(rt, line);
        let inner = d.arrow(rt, inner);
        d.arrow(rt, inner)
    };
    d.kernel()
        .add_inductive(r.rline0, &[], 0, type0, &[(r.rline0_mk, mk_ty)])?;

    declare_projection(d, cr, r.rline0, r.rline0_rec, r.rline0_a, 3, 0)?;
    declare_projection(d, cr, r.rline0, r.rline0_rec, r.rline0_b, 3, 1)?;
    declare_projection(d, cr, r.rline0, r.rline0_rec, r.rline0_c, 3, 2)
}

/// The `index`-th of `arity` `CReal` fields of a one-constructor `Type 0`
/// record, by large elimination — `qplane`'s own `declare_projection` at
/// `CReal` instead of `Rat`.
fn declare_projection(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    ind: NameId,
    rec: NameId,
    name: NameId,
    arity: usize,
    index: usize,
) -> Result<(), KernelError> {
    let rt = real_ty(d, cr);
    let one = d.level_one();
    let anon = d.anon_name();
    let carrier = d.kernel().const_(ind, vec![]);

    let motive = d
        .kernel()
        .lam(anon, carrier, rt, crate::BinderInfo::Default);
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

/// `Geo.RLine0.Nondeg` and `Geo.RLine`.
fn declare_nondeg(d: &mut IntDev<'_>, cr: CRealPrelude, r: RPlaneNames) -> Result<(), KernelError> {
    let line0 = line0_ty(d, r);
    let prop = prop_ty(d);

    {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let av = la(d, r, l);
        let bv = lb(d, r, l);
        let aa = rn_cmul(d, cr, av, av);
        let bb = rn_cmul(d, cr, bv, bv);
        let n = rn_cadd(d, cr, aa, bb);
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pb = pos_bound(d, cr, n, k);
        let pred = d.lam_fv(k_fv, nat, pb);
        let body = exists_ty(d, nat, pred);
        let value = d.lam_fv(l_fv, line0, body);
        let ty = d.arrow(line0, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: r.nondeg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // Geo.RLine := Subtype Geo.RLine0 Geo.RLine0.Nondeg.
    {
        let one = d.level_one();
        let sigma = d.int().logic.sigma;
        let sub = d.kernel().const_(sigma.subtype, vec![one]);
        let nd = d.kernel().const_(r.nondeg, vec![]);
        let value = d.apply(sub, &[line0, nd]);
        let ty = d.kernel().sort(one);
        d.kernel().add_declaration(Declaration::Definition {
            name: r.rline,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

/// `onRaw`, `on`, `Apart`.
fn declare_incidence(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line0 = line0_ty(d, r);
    let prop = prop_ty(d);

    // onRaw P l := Equiv (a l * x P + b l * y P + c l) 0.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let av = la(d, r, l);
        let bv = lb(d, r, l);
        let cv = lc(d, r, l);
        let s = px(d, cp, pt);
        let t = py(d, cp, pt);
        let lhs = eval3(d, cr, av, bv, cv, s, t);
        let z = rn_czero(d, cr);
        let body = ceq(d, cr, lhs, z);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: r.on_raw,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // on P l := onRaw P (Subtype.val l).
    {
        let line = line_ty(d, r);
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let raw = lval(d, r, l);
        let body = d.const_app(r.on_raw, &[pt, raw]);
        let value = {
            let inner = d.lam_fv(l_fv, line, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: r.on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // Apart P Q := ∃ k, PosBound (distSq P Q) k.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let dd = dist_sq(d, cp, pt, qt);
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pb = pos_bound(d, cr, dd, k);
        let pred = d.lam_fv(k_fv, nat, pb);
        let body = exists_ty(d, nat, pred);
        let value = {
            let inner = d.lam_fv(q_fv, point, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(point, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: r.apart,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

/// `Geo.RLine.Equiv` and its three laws — extensional line equality, so all
/// three are structural.
fn declare_line_equiv(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let prop = prop_ty(d);

    // Equiv l m := ∀ P, (on P l → on P m) ∧ (on P m → on P l).
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let p_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let pt = d.kernel().fvar(p_fv);
        let opl = d.const_app(r.on, &[pt, l]);
        let opm = d.const_app(r.on, &[pt, m]);
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
            name: r.line_equiv,
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
        let opl = d.const_app(r.on, &[pt, l]);
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
            let stmt = d.const_app(r.line_equiv, &[l, l]);
            d.pi_fv(l_fv, line, stmt)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.line_equiv_refl,
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
        let hyp = d.const_app(r.line_equiv, &[l, m]);
        let concl = d.const_app(r.line_equiv, &[m, l]);
        let opl = d.const_app(r.on, &[pt, l]);
        let opm = d.const_app(r.on, &[pt, m]);
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
            name: r.line_equiv_symm,
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
        let hyp1 = d.const_app(r.line_equiv, &[l, m]);
        let hyp2 = d.const_app(r.line_equiv, &[m, n]);
        let concl = d.const_app(r.line_equiv, &[l, n]);
        let opl = d.const_app(r.on, &[pt, l]);
        let opm = d.const_app(r.on, &[pt, m]);
        let opn = d.const_app(r.on, &[pt, n]);
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
            name: r.line_equiv_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `posBoundCongr`, `notZeroOfPosBound`, `cancelPosBound` — the three facts
/// about `CReal.PosBound` this model needs and `creal.rs` does not state.
fn declare_pos_bound_lemmas(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let carrier = real_ty(d, cr);
    let nat = d.nat_ty();

    // posBoundCongr : ∀ x y k, Equiv x y → PosBound x k → PosBound y k.
    {
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let hb_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let k = d.kernel().fvar(k_fv);
        let he = d.kernel().fvar(he_fv);
        let hb = d.kernel().fvar(hb_fv);

        let gap = pos_gap(d, cr, k);
        let refl_gap = rn_crefl(d, cr, gap);
        let proof = d.lemma(cr.le_congr, &[gap, gap, x, y, refl_gap, he, hb]);

        let he_ty = ceq(d, cr, x, y);
        let hb_ty = pos_bound(d, cr, x, k);
        let concl = pos_bound(d, cr, y, k);
        let ty = {
            let t = d.arrow(hb_ty, concl);
            let t = d.arrow(he_ty, t);
            let t = d.pi_fv(k_fv, nat, t);
            let t = d.pi_fv(y_fv, carrier, t);
            d.pi_fv(x_fv, carrier, t)
        };
        let value = {
            let t = d.lam_fv(hb_fv, hb_ty, proof);
            let t = d.lam_fv(he_fv, he_ty, t);
            let t = d.lam_fv(k_fv, nat, t);
            let t = d.lam_fv(y_fv, carrier, t);
            d.lam_fv(x_fv, carrier, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.pos_bound_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // notZeroOfPosBound : ∀ x k, PosBound x k → Equiv x zero → False.
    {
        let x_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let hb_fv = d.fresh_fvar();
        let hz_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let k = d.kernel().fvar(k_fv);
        let hb = d.kernel().fvar(hb_fv);
        let hz = d.kernel().fvar(hz_fv);

        let zero = rn_czero(d, cr);
        let refl_zero = rn_crefl(d, cr, zero);
        let positive = d.lemma(cr.pos_of_pos_bound, &[x, k, hb]);
        let degenerate = d.lemma(cr.lt_congr, &[zero, zero, x, zero, refl_zero, hz, positive]);
        let irrefl = d.lemma(cr.lt_irrefl, &[zero]);
        let proof = d.apply(irrefl, &[degenerate]);

        let hb_ty = pos_bound(d, cr, x, k);
        let hz_ty = ceq(d, cr, x, zero);
        let f = false_ty(d);
        let ty = {
            let t = d.arrow(hz_ty, f);
            let t = d.arrow(hb_ty, t);
            let t = d.pi_fv(k_fv, nat, t);
            d.pi_fv(x_fv, carrier, t)
        };
        let value = {
            let t = d.lam_fv(hz_fv, hz_ty, proof);
            let t = d.lam_fv(hb_fv, hb_ty, t);
            let t = d.lam_fv(k_fv, nat, t);
            d.lam_fv(x_fv, carrier, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.not_zero_of_pos_bound,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // cancelPosBound : ∀ n m k, PosBound n k → Equiv (mul n m) zero →
    //                           Equiv m zero.
    {
        let n_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let hb_fv = d.fresh_fvar();
        let hz_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = d.kernel().fvar(m_fv);
        let k = d.kernel().fvar(k_fv);
        let hb = d.kernel().fvar(hb_fv);
        let hz = d.kernel().fvar(hz_fv);

        let zero = rn_czero(d, cr);
        let one = rn_cone(d, cr);
        let ninv = d.const_app(cr.inv, &[n, k, hb]);
        let cancel = d.lemma(cr.mul_inv_cancel, &[n, k, hb]); // Equiv (n*ninv) one

        let m_one = rn_cmul(d, cr, m, one);
        let step1 = {
            let mo = d.lemma(cr.mul_one, &[m]); // Equiv (m*one) m
            rn_csymm(d, cr, m_one, m, mo)
        };
        let n_ninv = rn_cmul(d, cr, n, ninv);
        let m_nninv = rn_cmul(d, cr, m, n_ninv);
        let step2 = {
            let refl_m = rn_crefl(d, cr, m);
            let back = rn_csymm(d, cr, n_ninv, one, cancel);
            d.lemma(cr.mul_congr, &[m, m, one, n_ninv, refl_m, back])
        };
        let mn = rn_cmul(d, cr, m, n);
        let mn_ninv = rn_cmul(d, cr, mn, ninv);
        let step3 = {
            let assoc = d.lemma(cr.mul_assoc, &[m, n, ninv]); // (m*n)*ninv ~ m*(n*ninv)
            rn_csymm(d, cr, mn_ninv, m_nninv, assoc)
        };
        let nm = rn_cmul(d, cr, n, m);
        let nm_ninv = rn_cmul(d, cr, nm, ninv);
        let step4 = {
            let comm = d.lemma(cr.mul_comm, &[m, n]); // m*n ~ n*m
            let refl_inv = rn_crefl(d, cr, ninv);
            d.lemma(cr.mul_congr, &[mn, nm, ninv, ninv, comm, refl_inv])
        };
        let zero_ninv = rn_cmul(d, cr, zero, ninv);
        let step5 = {
            let refl_inv = rn_crefl(d, cr, ninv);
            d.lemma(cr.mul_congr, &[nm, zero, ninv, ninv, hz, refl_inv])
        };
        let ninv_zero = rn_cmul(d, cr, ninv, zero);
        let step6 = d.lemma(cr.mul_comm, &[zero, ninv]);
        let step7 = d.lemma(cr.mul_zero, &[ninv]);

        let (_, proof) = rn_cchain(
            d,
            cr,
            m,
            &[
                (m_one, step1),
                (m_nninv, step2),
                (mn_ninv, step3),
                (nm_ninv, step4),
                (zero_ninv, step5),
                (ninv_zero, step6),
                (zero, step7),
            ],
        );

        let hb_ty = pos_bound(d, cr, n, k);
        let hz_ty = ceq(d, cr, nm, zero);
        let concl = ceq(d, cr, m, zero);
        let ty = {
            let t = d.arrow(hz_ty, concl);
            let t = d.arrow(hb_ty, t);
            let t = d.pi_fv(k_fv, nat, t);
            let t = d.pi_fv(m_fv, carrier, t);
            d.pi_fv(n_fv, carrier, t)
        };
        let value = {
            let t = d.lam_fv(hz_fv, hz_ty, proof);
            let t = d.lam_fv(hb_fv, hb_ty, t);
            let t = d.lam_fv(k_fv, nat, t);
            let t = d.lam_fv(m_fv, carrier, t);
            d.lam_fv(n_fv, carrier, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.cancel_pos_bound,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CPoint.Equiv Q Q`, built inline — the `CPoint` prelude has no reflexivity
/// lemma for its own point equality.
fn point_equiv_refl(d: &mut IntDev<'_>, cp: CPointPrelude, cr: CRealPrelude, q: ExprId) -> ExprId {
    let qx = px(d, cp, q);
    let qy = py(d, cp, q);
    let ex = ceq(d, cr, qx, qx);
    let ey = ceq(d, cr, qy, qy);
    let hx = rn_crefl(d, cr, qx);
    let hy = rn_crefl(d, cr, qy);
    and_intro(d, ex, ey, hx, hy)
}

/// `onPoint`, `onLine`, `apartNe`, `apartSymm`, `apartCongr`.
fn declare_congruences(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();

    // onPoint : ∀ P Q l, CPoint.Equiv P Q → on P l → on Q l.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let hon_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let l = d.kernel().fvar(l_fv);
        let he = d.kernel().fvar(he_fv);
        let hon = d.kernel().fvar(hon_fv);

        let raw = lval(d, r, l);
        let av = la(d, r, raw);
        let bv = lb(d, r, raw);
        let cv = lc(d, r, raw);
        let pxv = px(d, cp, pt);
        let pyv = py(d, cp, pt);
        let qxv = px(d, cp, qt);
        let qyv = py(d, cp, qt);

        let ex_ty = ceq(d, cr, pxv, qxv);
        let ey_ty = ceq(d, cr, pyv, qyv);
        let hx = and_l(d, ex_ty, ey_ty, he);
        let hy = and_r(d, ex_ty, ey_ty, he);
        let hx_back = rn_csymm(d, cr, pxv, qxv, hx);
        let hy_back = rn_csymm(d, cr, pyv, qyv, hy);

        let mx_q = rn_cmul(d, cr, av, qxv);
        let mx_p = rn_cmul(d, cr, av, pxv);
        let my_q = rn_cmul(d, cr, bv, qyv);
        let my_p = rn_cmul(d, cr, bv, pyv);
        let refl_a = rn_crefl(d, cr, av);
        let refl_b = rn_crefl(d, cr, bv);
        let refl_c = rn_crefl(d, cr, cv);
        let cx = d.lemma(cr.mul_congr, &[av, av, qxv, pxv, refl_a, hx_back]);
        let cy = d.lemma(cr.mul_congr, &[bv, bv, qyv, pyv, refl_b, hy_back]);
        let sum_q = rn_cadd(d, cr, mx_q, my_q);
        let sum_p = rn_cadd(d, cr, mx_p, my_p);
        let csum = d.lemma(cr.add_congr, &[mx_q, mx_p, my_q, my_p, cx, cy]);
        let full_q = rn_cadd(d, cr, sum_q, cv);
        let full_p = rn_cadd(d, cr, sum_p, cv);
        let cfull = d.lemma(cr.add_congr, &[sum_q, sum_p, cv, cv, csum, refl_c]);
        let zero = rn_czero(d, cr);
        let proof = rn_ctrans(d, cr, full_q, full_p, zero, cfull, hon);

        let he_ty = d.const_app(cp.point_equiv, &[pt, qt]);
        let hon_ty = d.const_app(r.on, &[pt, l]);
        let concl = d.const_app(r.on, &[qt, l]);
        let ty = {
            let t = d.arrow(hon_ty, concl);
            let t = d.arrow(he_ty, t);
            let t = d.pi_fv(l_fv, line, t);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(hon_fv, hon_ty, proof);
            let t = d.lam_fv(he_fv, he_ty, t);
            let t = d.lam_fv(l_fv, line, t);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.on_point,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // onLine : ∀ P l m, Geo.RLine.Equiv l m → on P l → on P m.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let hon_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let he = d.kernel().fvar(he_fv);
        let hon = d.kernel().fvar(hon_fv);

        let opl = d.const_app(r.on, &[pt, l]);
        let opm = d.const_app(r.on, &[pt, m]);
        let fwd = d.arrow(opl, opm);
        let bwd = d.arrow(opm, opl);
        let at_p = d.apply(he, &[pt]);
        let forward = and_l(d, fwd, bwd, at_p);
        let proof = d.apply(forward, &[hon]);

        let he_ty = d.const_app(r.line_equiv, &[l, m]);
        let ty = {
            let t = d.arrow(opl, opm);
            let t = d.arrow(he_ty, t);
            let t = d.pi_fv(m_fv, line, t);
            let t = d.pi_fv(l_fv, line, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(hon_fv, opl, proof);
            let t = d.lam_fv(he_fv, he_ty, t);
            let t = d.lam_fv(m_fv, line, t);
            let t = d.lam_fv(l_fv, line, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.on_line,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartNe : ∀ P Q, Apart P Q → CPoint.Equiv P Q → False.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let ha = d.kernel().fvar(ha_fv);
        let he = d.kernel().fvar(he_fv);

        let dd = dist_sq(d, cp, pt, qt);
        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, dd, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let f = false_ty(d);
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, dd, k);
            let zeroed = d.lemma(cp.dist_sq_eq_zero_of_equiv, &[pt, qt, he]);
            let body = d.lemma(r.not_zero_of_pos_bound, &[dd, k, hk, zeroed]);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let proof = exists_elim(d, pred, f, ha, minor);

        let ha_ty = d.const_app(r.apart, &[pt, qt]);
        let he_ty = d.const_app(cp.point_equiv, &[pt, qt]);
        let ty = {
            let t = d.arrow(he_ty, f);
            let t = d.arrow(ha_ty, t);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(he_fv, he_ty, proof);
            let t = d.lam_fv(ha_fv, ha_ty, t);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.apart_ne,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartSymm : ∀ P Q, Apart P Q → Apart Q P.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let ha = d.kernel().fvar(ha_fv);

        let dpq = dist_sq(d, cp, pt, qt);
        let dqp = dist_sq(d, cp, qt, pt);
        let pred_pq = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, dpq, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let pred_qp = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, dqp, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let target = d.const_app(r.apart, &[qt, pt]);
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, dpq, k);
            let comm = d.lemma(cp.dist_sq_comm, &[pt, qt]);
            let moved = d.lemma(r.pos_bound_congr, &[dpq, dqp, k, comm, hk]);
            let body = exists_intro(d, nat, pred_qp, k, moved);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let proof = exists_elim(d, pred_pq, target, ha, minor);

        let ha_ty = d.const_app(r.apart, &[pt, qt]);
        let ty = {
            let t = d.arrow(ha_ty, target);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(ha_fv, ha_ty, proof);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.apart_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // apartCongr : ∀ P P' Q, CPoint.Equiv P P' → Apart P Q → Apart P' Q.
    {
        let p_fv = d.fresh_fvar();
        let p2_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let p2 = d.kernel().fvar(p2_fv);
        let qt = d.kernel().fvar(q_fv);
        let he = d.kernel().fvar(he_fv);
        let ha = d.kernel().fvar(ha_fv);

        let dpq = dist_sq(d, cp, pt, qt);
        let d2q = dist_sq(d, cp, p2, qt);
        let pred_pq = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, dpq, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let pred_2q = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, d2q, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let target = d.const_app(r.apart, &[p2, qt]);
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, dpq, k);
            let hqq = point_equiv_refl(d, cp, cr, qt);
            let moved_eq = d.lemma(cp.dist_sq_congr, &[pt, p2, qt, qt, he, hqq]);
            let moved = d.lemma(r.pos_bound_congr, &[dpq, d2q, k, moved_eq, hk]);
            let body = exists_intro(d, nat, pred_2q, k, moved);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let proof = exists_elim(d, pred_pq, target, ha, minor);

        let he_ty = d.const_app(cp.point_equiv, &[pt, p2]);
        let ha_ty = d.const_app(r.apart, &[pt, qt]);
        let ty = {
            let t = d.arrow(ha_ty, target);
            let t = d.arrow(he_ty, t);
            let t = d.pi_fv(q_fv, point, t);
            let t = d.pi_fv(p2_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(ha_fv, ha_ty, proof);
            let t = d.lam_fv(he_fv, he_ty, t);
            let t = d.lam_fv(q_fv, point, t);
            let t = d.lam_fv(p2_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.apart_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `pivotAB`, `defectAC`, `defectBC`, `defectSwap`, `onOfDefects` — the whole
/// algebraic content of the model, over bare reals with no point or line in
/// sight.
fn declare_defects(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let carrier = real_ty(d, cr);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);

    // pivotAB : ∀ a b A B u v,
    //   Equiv (a*u + b*v) 0 → Equiv (A*u + B*v) 0 →
    //   Equiv ((u*u + v*v) * (a*B − b*A)) 0.
    {
        let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
        let terms: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
        let (a, b, aa, bb, u, v) = (terms[0], terms[1], terms[2], terms[3], terms[4], terms[5]);
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);

        let e_small = {
            let m1 = rn_cmul(d, cr, a, u);
            let m2 = rn_cmul(d, cr, b, v);
            rn_cadd(d, cr, m1, m2)
        };
        let e_big = {
            let m1 = rn_cmul(d, cr, aa, u);
            let m2 = rn_cmul(d, cr, bb, v);
            rn_cadd(d, cr, m1, m2)
        };
        let f_left = {
            let m1 = rn_cmul(d, cr, bb, u);
            let m2 = rn_cmul(d, cr, aa, v);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let g_left = {
            let m1 = rn_cmul(d, cr, a, v);
            let m2 = rn_cmul(d, cr, b, u);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let dab = {
            let m1 = rn_cmul(d, cr, a, bb);
            let m2 = rn_cmul(d, cr, b, aa);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let norm = {
            let m1 = rn_cmul(d, cr, u, u);
            let m2 = rn_cmul(d, cr, v, v);
            rn_cadd(d, cr, m1, m2)
        };
        let lhs = rn_cmul(d, cr, norm, dab);

        let lhs_rn = RnExpr::mul(
            RnExpr::add(RnExpr::mul(at(u), at(u)), RnExpr::mul(at(v), at(v))),
            rsub(RnExpr::mul(at(a), at(bb)), RnExpr::mul(at(b), at(aa))),
        );
        let rhs_rn = RnExpr::add(
            RnExpr::mul(
                rsub(RnExpr::mul(at(bb), at(u)), RnExpr::mul(at(aa), at(v))),
                RnExpr::add(RnExpr::mul(at(a), at(u)), RnExpr::mul(at(b), at(v))),
            ),
            RnExpr::mul(
                rsub(RnExpr::mul(at(a), at(v)), RnExpr::mul(at(b), at(u))),
                RnExpr::add(RnExpr::mul(at(aa), at(u)), RnExpr::mul(at(bb), at(v))),
            ),
        );
        let identity = ring(d, cr, &lhs_rn, &rhs_rn);
        let vanish = sum_hyp_zero(d, cr, &[(f_left, e_small, h1), (g_left, e_big, h2)]);
        let rhs = {
            let t1 = rn_cmul(d, cr, f_left, e_small);
            let t2 = rn_cmul(d, cr, g_left, e_big);
            rn_cadd(d, cr, t1, t2)
        };
        let proof = rn_ctrans(d, cr, lhs, rhs, zero, identity, vanish);

        let h1_ty = ceq(d, cr, e_small, zero);
        let h2_ty = ceq(d, cr, e_big, zero);
        let concl = ceq(d, cr, lhs, zero);
        let ty = {
            let t = d.arrow(h2_ty, concl);
            let mut t = d.arrow(h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, carrier, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(h2_fv, h2_ty, proof);
            let mut t = d.lam_fv(h1_fv, h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, carrier, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.pivot_ab,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // defectAC / defectBC : ∀ a b c A B C p q,
    //   Equiv (a*p + b*q + c) 0 → Equiv (A*p + B*q + C) 0 →
    //   Equiv (a*B − b*A) 0 → Equiv (a*C − c*A) 0   [resp. (b*C − c*B)]
    for which_bc in [false, true] {
        let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
        let terms: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
        let (a, b, c, aa, bb, cc, p, q) = (
            terms[0], terms[1], terms[2], terms[3], terms[4], terms[5], terms[6], terms[7],
        );
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h3_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.kernel().fvar(h3_fv);

        let e_small = eval3(d, cr, a, b, c, p, q);
        let e_big = eval3(d, cr, aa, bb, cc, p, q);
        let dab = {
            let m1 = rn_cmul(d, cr, a, bb);
            let m2 = rn_cmul(d, cr, b, aa);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        // The "left" coefficient of the defect being proved: `a` for `dAC`,
        // `b` for `dBC`; the correction's sign flips with it.
        let left = if which_bc { b } else { a };
        let mid = if which_bc { bb } else { aa };
        let target = {
            let m1 = rn_cmul(d, cr, left, cc);
            let m2 = rn_cmul(d, cr, c, mid);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let neg_mid = rn_cneg(d, cr, mid);
        let corr = if which_bc { p } else { rn_cneg(d, cr, q) };

        let left_rn = at(left);
        let mid_rn = at(mid);
        let e_small_rn = rev3(at(a), at(b), at(c), at(p), at(q));
        let e_big_rn = rev3(at(aa), at(bb), at(cc), at(p), at(q));
        let dab_rn = rsub(RnExpr::mul(at(a), at(bb)), RnExpr::mul(at(b), at(aa)));
        let corr_rn = if which_bc { at(p) } else { RnExpr::neg(at(q)) };
        let target_rn = rsub(
            RnExpr::mul(left_rn.clone(), at(cc)),
            RnExpr::mul(at(c), mid_rn.clone()),
        );
        let rhs_rn = RnExpr::add(
            RnExpr::add(
                RnExpr::mul(left_rn, e_big_rn),
                RnExpr::mul(RnExpr::neg(mid_rn), e_small_rn),
            ),
            RnExpr::mul(corr_rn, dab_rn),
        );
        let identity = ring(d, cr, &target_rn, &rhs_rn);
        let vanish = sum_hyp_zero(
            d,
            cr,
            &[(left, e_big, h2), (neg_mid, e_small, h1), (corr, dab, h3)],
        );
        let rhs = {
            let t1 = rn_cmul(d, cr, left, e_big);
            let t2 = rn_cmul(d, cr, neg_mid, e_small);
            let t3 = rn_cmul(d, cr, corr, dab);
            let s = rn_cadd(d, cr, t1, t2);
            rn_cadd(d, cr, s, t3)
        };
        let proof = rn_ctrans(d, cr, target, rhs, zero, identity, vanish);

        let h1_ty = ceq(d, cr, e_small, zero);
        let h2_ty = ceq(d, cr, e_big, zero);
        let h3_ty = ceq(d, cr, dab, zero);
        let concl = ceq(d, cr, target, zero);
        let ty = {
            let t = d.arrow(h3_ty, concl);
            let t = d.arrow(h2_ty, t);
            let mut t = d.arrow(h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, carrier, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(h3_fv, h3_ty, proof);
            let t = d.lam_fv(h2_fv, h2_ty, t);
            let mut t = d.lam_fv(h1_fv, h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, carrier, t);
            }
            t
        };
        let name = if which_bc { r.defect_bc } else { r.defect_ac };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // defectSwap : ∀ α β α' β', Equiv (α*β' − β*α') 0 → Equiv (α'*β − β'*α) 0.
    {
        let fvs: Vec<u64> = (0..4).map(|_| d.fresh_fvar()).collect();
        let terms: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
        let (al, be, al2, be2) = (terms[0], terms[1], terms[2], terms[3]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let src = {
            let m1 = rn_cmul(d, cr, al, be2);
            let m2 = rn_cmul(d, cr, be, al2);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let target = {
            let m1 = rn_cmul(d, cr, al2, be);
            let m2 = rn_cmul(d, cr, be2, al);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let one = rn_cone(d, cr);
        let minus_one = rn_cneg(d, cr, one);
        let scaled = rn_cmul(d, cr, minus_one, src);

        let src_rn = rsub(RnExpr::mul(at(al), at(be2)), RnExpr::mul(at(be), at(al2)));
        let target_rn = rsub(RnExpr::mul(at(al2), at(be)), RnExpr::mul(at(be2), at(al)));
        let scaled_rn = RnExpr::mul(RnExpr::neg(RnExpr::One), src_rn);
        let identity = ring(d, cr, &target_rn, &scaled_rn);
        let vanish = mul_hyp_zero(d, cr, minus_one, src, h);
        let proof = rn_ctrans(d, cr, target, scaled, zero, identity, vanish);

        let h_ty = ceq(d, cr, src, zero);
        let concl = ceq(d, cr, target, zero);
        let ty = {
            let mut t = d.arrow(h_ty, concl);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, carrier, t);
            }
            t
        };
        let value = {
            let mut t = d.lam_fv(h_fv, h_ty, proof);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, carrier, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.defect_swap,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // onOfDefects : ∀ a b c A B C x y k, PosBound (a*a + b*b) k →
    //   Equiv (a*B − b*A) 0 → Equiv (a*C − c*A) 0 → Equiv (b*C − c*B) 0 →
    //   Equiv (a*x + b*y + c) 0 → Equiv (A*x + B*y + C) 0.
    {
        let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
        let terms: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
        let (a, b, c, aa, bb, cc, x, y) = (
            terms[0], terms[1], terms[2], terms[3], terms[4], terms[5], terms[6], terms[7],
        );
        let k_fv = d.fresh_fvar();
        let hk_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h3_fv = d.fresh_fvar();
        let hx_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk = d.kernel().fvar(hk_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.kernel().fvar(h3_fv);
        let hx = d.kernel().fvar(hx_fv);

        let norm = {
            let m1 = rn_cmul(d, cr, a, a);
            let m2 = rn_cmul(d, cr, b, b);
            rn_cadd(d, cr, m1, m2)
        };
        let ex = eval3(d, cr, a, b, c, x, y);
        let big = eval3(d, cr, aa, bb, cc, x, y);
        let dab = {
            let m1 = rn_cmul(d, cr, a, bb);
            let m2 = rn_cmul(d, cr, b, aa);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let dac = {
            let m1 = rn_cmul(d, cr, a, cc);
            let m2 = rn_cmul(d, cr, c, aa);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let dbc = {
            let m1 = rn_cmul(d, cr, b, cc);
            let m2 = rn_cmul(d, cr, c, bb);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let f1 = {
            let m1 = rn_cmul(d, cr, a, aa);
            let m2 = rn_cmul(d, cr, b, bb);
            rn_cadd(d, cr, m1, m2)
        };
        let f2 = {
            let m1 = rn_cmul(d, cr, a, y);
            let m2 = rn_cmul(d, cr, b, x);
            let n2 = rn_cneg(d, cr, m2);
            rn_cadd(d, cr, m1, n2)
        };
        let product = rn_cmul(d, cr, norm, big);

        let lhs_rn = RnExpr::mul(
            RnExpr::add(RnExpr::mul(at(a), at(a)), RnExpr::mul(at(b), at(b))),
            rev3(at(aa), at(bb), at(cc), at(x), at(y)),
        );
        let dab_rn = rsub(RnExpr::mul(at(a), at(bb)), RnExpr::mul(at(b), at(aa)));
        let dac_rn = rsub(RnExpr::mul(at(a), at(cc)), RnExpr::mul(at(c), at(aa)));
        let dbc_rn = rsub(RnExpr::mul(at(b), at(cc)), RnExpr::mul(at(c), at(bb)));
        let rhs_rn = RnExpr::add(
            RnExpr::add(
                RnExpr::add(
                    RnExpr::mul(
                        RnExpr::add(RnExpr::mul(at(a), at(aa)), RnExpr::mul(at(b), at(bb))),
                        rev3(at(a), at(b), at(c), at(x), at(y)),
                    ),
                    RnExpr::mul(
                        rsub(RnExpr::mul(at(a), at(y)), RnExpr::mul(at(b), at(x))),
                        dab_rn,
                    ),
                ),
                RnExpr::mul(at(a), dac_rn),
            ),
            RnExpr::mul(at(b), dbc_rn),
        );
        let identity = ring(d, cr, &lhs_rn, &rhs_rn);
        let vanish = sum_hyp_zero(
            d,
            cr,
            &[(f1, ex, hx), (f2, dab, h1), (a, dac, h2), (b, dbc, h3)],
        );
        let rhs = {
            let t1 = rn_cmul(d, cr, f1, ex);
            let t2 = rn_cmul(d, cr, f2, dab);
            let t3 = rn_cmul(d, cr, a, dac);
            let t4 = rn_cmul(d, cr, b, dbc);
            let s = rn_cadd(d, cr, t1, t2);
            let s = rn_cadd(d, cr, s, t3);
            rn_cadd(d, cr, s, t4)
        };
        let product_zero = rn_ctrans(d, cr, product, rhs, zero, identity, vanish);
        let proof = d.lemma(r.cancel_pos_bound, &[norm, big, k, hk, product_zero]);

        let hk_ty = pos_bound(d, cr, norm, k);
        let h1_ty = ceq(d, cr, dab, zero);
        let h2_ty = ceq(d, cr, dac, zero);
        let h3_ty = ceq(d, cr, dbc, zero);
        let hx_ty = ceq(d, cr, ex, zero);
        let concl = ceq(d, cr, big, zero);
        let ty = {
            let t = d.arrow(hx_ty, concl);
            let t = d.arrow(h3_ty, t);
            let t = d.arrow(h2_ty, t);
            let t = d.arrow(h1_ty, t);
            let t = d.arrow(hk_ty, t);
            let mut t = d.pi_fv(k_fv, nat, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, carrier, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(hx_fv, hx_ty, proof);
            let t = d.lam_fv(h3_fv, h3_ty, t);
            let t = d.lam_fv(h2_fv, h2_ty, t);
            let t = d.lam_fv(h1_fv, h1_ty, t);
            let t = d.lam_fv(hk_fv, hk_ty, t);
            let mut t = d.lam_fv(k_fv, nat, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, carrier, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.on_of_defects,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `pointRefl`, `pointSymm`, `pointTrans` — `CPoint.Equiv`'s three setoid
/// laws, which `creal_point.rs` defines the relation without ever stating.
fn declare_point_setoid(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);

    // pointRefl : ∀ P, CPoint.Equiv P P.
    {
        let p_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let proof = point_equiv_refl(d, cp, cr, pt);
        let stmt = d.const_app(cp.point_equiv, &[pt, pt]);
        let ty = d.pi_fv(p_fv, point, stmt);
        let value = d.lam_fv(p_fv, point, proof);
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.point_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // pointSymm : ∀ P Q, CPoint.Equiv P Q → CPoint.Equiv Q P.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let h = d.kernel().fvar(h_fv);
        let pxv = px(d, cp, pt);
        let pyv = py(d, cp, pt);
        let qxv = px(d, cp, qt);
        let qyv = py(d, cp, qt);
        let ex = ceq(d, cr, pxv, qxv);
        let ey = ceq(d, cr, pyv, qyv);
        let hx = and_l(d, ex, ey, h);
        let hy = and_r(d, ex, ey, h);
        let bx = rn_csymm(d, cr, pxv, qxv, hx);
        let by = rn_csymm(d, cr, pyv, qyv, hy);
        let rx = ceq(d, cr, qxv, pxv);
        let ry = ceq(d, cr, qyv, pyv);
        let proof = and_intro(d, rx, ry, bx, by);

        let hyp = d.const_app(cp.point_equiv, &[pt, qt]);
        let concl = d.const_app(cp.point_equiv, &[qt, pt]);
        let ty = {
            let t = d.arrow(hyp, concl);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, hyp, proof);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.point_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // pointTrans : ∀ P Q R, CPoint.Equiv P Q → CPoint.Equiv Q R →
    //              CPoint.Equiv P R.
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let s_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let st = d.kernel().fvar(s_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let pxv = px(d, cp, pt);
        let pyv = py(d, cp, pt);
        let qxv = px(d, cp, qt);
        let qyv = py(d, cp, qt);
        let sxv = px(d, cp, st);
        let syv = py(d, cp, st);
        let ex1 = ceq(d, cr, pxv, qxv);
        let ey1 = ceq(d, cr, pyv, qyv);
        let ex2 = ceq(d, cr, qxv, sxv);
        let ey2 = ceq(d, cr, qyv, syv);
        let ax = and_l(d, ex1, ey1, h1);
        let ay = and_r(d, ex1, ey1, h1);
        let bx = and_l(d, ex2, ey2, h2);
        let by = and_r(d, ex2, ey2, h2);
        let tx = rn_ctrans(d, cr, pxv, qxv, sxv, ax, bx);
        let tyy = rn_ctrans(d, cr, pyv, qyv, syv, ay, by);
        let rx = ceq(d, cr, pxv, sxv);
        let ry = ceq(d, cr, pyv, syv);
        let proof = and_intro(d, rx, ry, tx, tyy);

        let hyp1 = d.const_app(cp.point_equiv, &[pt, qt]);
        let hyp2 = d.const_app(cp.point_equiv, &[qt, st]);
        let concl = d.const_app(cp.point_equiv, &[pt, st]);
        let ty = {
            let t = d.arrow(hyp2, concl);
            let t = d.arrow(hyp1, t);
            let t = d.pi_fv(s_fv, point, t);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(h2_fv, hyp2, proof);
            let t = d.lam_fv(h1_fv, hyp1, t);
            let t = d.lam_fv(s_fv, point, t);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.point_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// The three coefficients of `Geo.RPlane.join P Q`, spelled out so that
/// `rn_ring_proof` sees reals rather than a stuck projection.
fn join_coeffs(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    p: ExprId,
    q: ExprId,
) -> [ExprId; 3] {
    let pxv = px(d, cp, p);
    let pyv = py(d, cp, p);
    let qxv = px(d, cp, q);
    let qyv = py(d, cp, q);
    let big_a = {
        let n = rn_cneg(d, cr, pyv);
        rn_cadd(d, cr, qyv, n)
    };
    let big_b = {
        let n = rn_cneg(d, cr, qxv);
        rn_cadd(d, cr, pxv, n)
    };
    let big_c = {
        let m1 = rn_cmul(d, cr, pyv, qxv);
        let m2 = rn_cmul(d, cr, pxv, qyv);
        let n = rn_cneg(d, cr, m2);
        rn_cadd(d, cr, m1, n)
    };
    [big_a, big_b, big_c]
}

/// `join`, `joinOnLeft`, `joinOnRight`, `joinNondeg`, `joinExists`.
fn declare_join(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line0 = line0_ty(d, r);
    let nat = d.nat_ty();

    // join P Q := mk (y Q − y P) (x P − x Q) (y P * x Q − x P * y Q).
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let [ca, cb, cc] = join_coeffs(d, cp, cr, pt, qt);
        let body = lmk(d, r, ca, cb, cc);
        let value = {
            let inner = d.lam_fv(q_fv, point, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(point, line0);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: r.join,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // joinOnLeft / joinOnRight : ∀ P Q, onRaw P (join P Q) / onRaw Q (join P Q).
    for at_right in [false, true] {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let pxv = px(d, cp, pt);
        let pyv = py(d, cp, pt);
        let qxv = px(d, cp, qt);
        let qyv = py(d, cp, qt);
        let (sx, sy) = if at_right { (qxv, qyv) } else { (pxv, pyv) };
        let a_rn = rsub(at(qyv), at(pyv));
        let b_rn = rsub(at(pxv), at(qxv));
        let c_rn = rsub(RnExpr::mul(at(pyv), at(qxv)), RnExpr::mul(at(pxv), at(qyv)));
        let lhs_rn = rev3(a_rn, b_rn, c_rn, at(sx), at(sy));
        let proof = ring(d, cr, &lhs_rn, &RnExpr::Zero);

        let joined = d.const_app(r.join, &[pt, qt]);
        let target = if at_right {
            d.const_app(r.on_raw, &[qt, joined])
        } else {
            d.const_app(r.on_raw, &[pt, joined])
        };
        let ty = {
            let t = d.pi_fv(q_fv, point, target);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(q_fv, point, proof);
            d.lam_fv(p_fv, point, t)
        };
        let name = if at_right {
            r.join_on_right
        } else {
            r.join_on_left
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // joinNondeg : ∀ P Q k, PosBound (distSq P Q) k → Nondeg (join P Q).
    {
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let hk_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let k = d.kernel().fvar(k_fv);
        let hk = d.kernel().fvar(hk_fv);

        let pxv = px(d, cp, pt);
        let pyv = py(d, cp, pt);
        let qxv = px(d, cp, qt);
        let qyv = py(d, cp, qt);
        let joined = d.const_app(r.join, &[pt, qt]);
        let ja = la(d, r, joined);
        let jb = lb(d, r, joined);
        let norm = {
            let m1 = rn_cmul(d, cr, ja, ja);
            let m2 = rn_cmul(d, cr, jb, jb);
            rn_cadd(d, cr, m1, m2)
        };
        let pred = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let pb = pos_bound(d, cr, norm, k2);
            d.lam_fv(k2_fv, nat, pb)
        };

        let dd = dist_sq(d, cp, pt, qt);
        let lhs_rn = RnExpr::add(
            RnExpr::mul(rsub(at(pxv), at(qxv)), rsub(at(pxv), at(qxv))),
            RnExpr::mul(rsub(at(pyv), at(qyv)), rsub(at(pyv), at(qyv))),
        );
        let a_rn = rsub(at(qyv), at(pyv));
        let b_rn = rsub(at(pxv), at(qxv));
        let rhs_rn = RnExpr::add(
            RnExpr::mul(a_rn.clone(), a_rn),
            RnExpr::mul(b_rn.clone(), b_rn),
        );
        let same = ring(d, cr, &lhs_rn, &rhs_rn);
        let moved = d.lemma(r.pos_bound_congr, &[dd, norm, k, same, hk]);
        let proof = exists_intro(d, nat, pred, k, moved);

        let hk_ty = pos_bound(d, cr, dd, k);
        let concl = d.const_app(r.nondeg, &[joined]);
        let ty = {
            let t = d.arrow(hk_ty, concl);
            let t = d.pi_fv(k_fv, nat, t);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(hk_fv, hk_ty, proof);
            let t = d.lam_fv(k_fv, nat, t);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.join_nondeg,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // joinExists : ∀ P Q, Apart P Q → ∃ l, on P l ∧ on Q l.
    {
        let line = line_ty(d, r);
        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let ha = d.kernel().fvar(ha_fv);

        let line_pred = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let opl = d.const_app(r.on, &[pt, l]);
            let oql = d.const_app(r.on, &[qt, l]);
            let both = and_ty(d, opl, oql);
            d.lam_fv(l_fv, line, both)
        };
        let target = exists_ty(d, line, line_pred);

        let dd = dist_sq(d, cp, pt, qt);
        let apart_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = pos_bound(d, cr, dd, k);
            d.lam_fv(k_fv, nat, pb)
        };
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, dd, k);
            let joined = d.const_app(r.join, &[pt, qt]);
            let nd = d.lemma(r.join_nondeg, &[pt, qt, k, hk]);
            let sub = lsub(d, r, joined, nd);
            let left = d.lemma(r.join_on_left, &[pt, qt]);
            let right = d.lemma(r.join_on_right, &[pt, qt]);
            let opl = d.const_app(r.on, &[pt, sub]);
            let oql = d.const_app(r.on, &[qt, sub]);
            let pair = and_intro(d, opl, oql, left, right);
            let body = exists_intro(d, line, line_pred, sub, pair);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let proof = exists_elim(d, apart_pred, target, ha, minor);

        let ha_ty = d.const_app(r.apart, &[pt, qt]);
        let ty = {
            let t = d.arrow(ha_ty, target);
            let t = d.pi_fv(q_fv, point, t);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(ha_fv, ha_ty, proof);
            let t = d.lam_fv(q_fv, point, t);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.join_exists,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `joinUnique` — the whole point of the file.
fn declare_join_unique(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);
    let one = rn_cone(d, cr);

    let p_fv = d.fresh_fvar();
    let q_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let ha_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let h3_fv = d.fresh_fvar();
    let h4_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let qt = d.kernel().fvar(q_fv);
    let l = d.kernel().fvar(l_fv);
    let m = d.kernel().fvar(m_fv);
    let ha = d.kernel().fvar(ha_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);
    let h3 = d.kernel().fvar(h3_fv);
    let h4 = d.kernel().fvar(h4_fv);

    let raw_l = lval(d, r, l);
    let raw_m = lval(d, r, m);
    let a = la(d, r, raw_l);
    let b = lb(d, r, raw_l);
    let c = lc(d, r, raw_l);
    let aa = la(d, r, raw_m);
    let bb = lb(d, r, raw_m);
    let cc = lc(d, r, raw_m);

    let pxv = px(d, cp, pt);
    let pyv = py(d, cp, pt);
    let qxv = px(d, cp, qt);
    let qyv = py(d, cp, qt);
    let u = {
        let n = rn_cneg(d, cr, qxv);
        rn_cadd(d, cr, pxv, n)
    };
    let v = {
        let n = rn_cneg(d, cr, qyv);
        rn_cadd(d, cr, pyv, n)
    };
    let norm_pq = {
        let m1 = rn_cmul(d, cr, u, u);
        let m2 = rn_cmul(d, cr, v, v);
        rn_cadd(d, cr, m1, m2)
    };

    let e1 = eval3(d, cr, a, b, c, pxv, pyv);
    let e2 = eval3(d, cr, a, b, c, qxv, qyv);
    let f1 = eval3(d, cr, aa, bb, cc, pxv, pyv);
    let f2 = eval3(d, cr, aa, bb, cc, qxv, qyv);

    // hu : Equiv (a*u + b*v) 0, hU : Equiv (A*u + B*v) 0.
    let minus_one = rn_cneg(d, cr, one);
    let mut differences: Vec<ExprId> = Vec::with_capacity(2);
    for (ca, cb, cc_, ea, eb, hx, hy) in [(a, b, c, e1, e2, h1, h2), (aa, bb, cc, f1, f2, h3, h4)] {
        let lhs = {
            let m1 = rn_cmul(d, cr, ca, u);
            let m2 = rn_cmul(d, cr, cb, v);
            rn_cadd(d, cr, m1, m2)
        };
        let lhs_rn = RnExpr::add(
            RnExpr::mul(at(ca), rsub(at(pxv), at(qxv))),
            RnExpr::mul(at(cb), rsub(at(pyv), at(qyv))),
        );
        let rhs_rn = RnExpr::add(
            RnExpr::mul(RnExpr::One, rev3(at(ca), at(cb), at(cc_), at(pxv), at(pyv))),
            RnExpr::mul(
                RnExpr::neg(RnExpr::One),
                rev3(at(ca), at(cb), at(cc_), at(qxv), at(qyv)),
            ),
        );
        let identity = ring(d, cr, &lhs_rn, &rhs_rn);
        let vanish = sum_hyp_zero(d, cr, &[(one, ea, hx), (minus_one, eb, hy)]);
        let rhs = {
            let t1 = rn_cmul(d, cr, one, ea);
            let t2 = rn_cmul(d, cr, minus_one, eb);
            rn_cadd(d, cr, t1, t2)
        };
        differences.push(rn_ctrans(d, cr, lhs, rhs, zero, identity, vanish));
    }
    let hu = differences[0];
    let h_big_u = differences[1];

    let dab = {
        let m1 = rn_cmul(d, cr, a, bb);
        let m2 = rn_cmul(d, cr, b, aa);
        let n2 = rn_cneg(d, cr, m2);
        rn_cadd(d, cr, m1, n2)
    };
    let pivot = d.lemma(r.pivot_ab, &[a, b, aa, bb, u, v, hu, h_big_u]);

    // The three `Nat` witnesses: `Apart P Q`, `Nondeg l`, `Nondeg m`.
    let k_fv = d.fresh_fvar();
    let hk_fv = d.fresh_fvar();
    let kl_fv = d.fresh_fvar();
    let hkl_fv = d.fresh_fvar();
    let km_fv = d.fresh_fvar();
    let hkm_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk = d.kernel().fvar(hk_fv);
    let kl = d.kernel().fvar(kl_fv);
    let hkl = d.kernel().fvar(hkl_fv);
    let km = d.kernel().fvar(km_fv);
    let hkm = d.kernel().fvar(hkm_fv);

    let hdab = d.lemma(r.cancel_pos_bound, &[norm_pq, dab, k, hk, pivot]);
    let hdac = d.lemma(r.defect_ac, &[a, b, c, aa, bb, cc, pxv, pyv, h1, h3, hdab]);
    let hdbc = d.lemma(r.defect_bc, &[a, b, c, aa, bb, cc, pxv, pyv, h1, h3, hdab]);
    let hdab2 = d.lemma(r.defect_swap, &[a, b, aa, bb, hdab]);
    let hdac2 = d.lemma(r.defect_swap, &[a, c, aa, cc, hdac]);
    let hdbc2 = d.lemma(r.defect_swap, &[b, c, bb, cc, hdbc]);

    let target = d.const_app(r.line_equiv, &[l, m]);
    let body = {
        let x_fv = d.fresh_fvar();
        let xt = d.kernel().fvar(x_fv);
        let xx = px(d, cp, xt);
        let xy = py(d, cp, xt);
        let oxl = d.const_app(r.on, &[xt, l]);
        let oxm = d.const_app(r.on, &[xt, m]);
        let fwd_ty = d.arrow(oxl, oxm);
        let bwd_ty = d.arrow(oxm, oxl);
        let fwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.lemma(
                r.on_of_defects,
                &[a, b, c, aa, bb, cc, xx, xy, kl, hkl, hdab, hdac, hdbc, hx],
            );
            d.lam_fv(hx_fv, oxl, step)
        };
        let bwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.lemma(
                r.on_of_defects,
                &[
                    aa, bb, cc, a, b, c, xx, xy, km, hkm, hdab2, hdac2, hdbc2, hx,
                ],
            );
            d.lam_fv(hx_fv, oxm, step)
        };
        let pair = and_intro(d, fwd_ty, bwd_ty, fwd, bwd);
        d.lam_fv(x_fv, point, pair)
    };

    // Wrap the three eliminations, innermost first.
    let norm_m = {
        let m1 = rn_cmul(d, cr, aa, aa);
        let m2 = rn_cmul(d, cr, bb, bb);
        rn_cadd(d, cr, m1, m2)
    };
    let norm_l = {
        let m1 = rn_cmul(d, cr, a, a);
        let m2 = rn_cmul(d, cr, b, b);
        rn_cadd(d, cr, m1, m2)
    };
    let pred_m = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pb = pos_bound(d, cr, norm_m, j);
        d.lam_fv(j_fv, nat, pb)
    };
    let pred_l = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pb = pos_bound(d, cr, norm_l, j);
        d.lam_fv(j_fv, nat, pb)
    };
    let dd = dist_sq(d, cp, pt, qt);
    let pred_a = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pb = pos_bound(d, cr, dd, j);
        d.lam_fv(j_fv, nat, pb)
    };

    let minor_m = {
        let hkm_ty = pos_bound(d, cr, norm_m, km);
        let inner = d.lam_fv(hkm_fv, hkm_ty, body);
        d.lam_fv(km_fv, nat, inner)
    };
    let prop_m = lprop(d, r, m);
    let after_m = exists_elim(d, pred_m, target, prop_m, minor_m);

    let minor_l = {
        let hkl_ty = pos_bound(d, cr, norm_l, kl);
        let inner = d.lam_fv(hkl_fv, hkl_ty, after_m);
        d.lam_fv(kl_fv, nat, inner)
    };
    let prop_l = lprop(d, r, l);
    let after_l = exists_elim(d, pred_l, target, prop_l, minor_l);

    let minor_a = {
        let hk_ty = pos_bound(d, cr, dd, k);
        let inner = d.lam_fv(hk_fv, hk_ty, after_l);
        d.lam_fv(k_fv, nat, inner)
    };
    let proof = exists_elim(d, pred_a, target, ha, minor_a);

    let ha_ty = d.const_app(r.apart, &[pt, qt]);
    let h1_ty = d.const_app(r.on, &[pt, l]);
    let h2_ty = d.const_app(r.on, &[qt, l]);
    let h3_ty = d.const_app(r.on, &[pt, m]);
    let h4_ty = d.const_app(r.on, &[qt, m]);
    let ty = {
        let t = d.arrow(h4_ty, target);
        let t = d.arrow(h3_ty, t);
        let t = d.arrow(h2_ty, t);
        let t = d.arrow(h1_ty, t);
        let t = d.arrow(ha_ty, t);
        let t = d.pi_fv(m_fv, line, t);
        let t = d.pi_fv(l_fv, line, t);
        let t = d.pi_fv(q_fv, point, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(h4_fv, h4_ty, proof);
        let t = d.lam_fv(h3_fv, h3_ty, t);
        let t = d.lam_fv(h2_fv, h2_ty, t);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(m_fv, line, t);
        let t = d.lam_fv(l_fv, line, t);
        let t = d.lam_fv(q_fv, point, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: r.join_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// `twoPointsRaw` and `twoPoints`.
fn declare_two_points(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line0 = line0_ty(d, r);
    let line = line_ty(d, r);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);

    // twoPointsRaw : ∀ l k, PosBound (a*a + b*b) k →
    //                ∃ P Q, Apart P Q ∧ (onRaw P l ∧ onRaw Q l).
    {
        let l_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let hk_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let k = d.kernel().fvar(k_fv);
        let hk = d.kernel().fvar(hk_fv);

        let a = la(d, r, l);
        let b = lb(d, r, l);
        let c = lc(d, r, l);
        let norm = {
            let m1 = rn_cmul(d, cr, a, a);
            let m2 = rn_cmul(d, cr, b, b);
            rn_cadd(d, cr, m1, m2)
        };
        let ninv = d.const_app(cr.inv, &[norm, k, hk]);
        let cancel = d.lemma(cr.mul_inv_cancel, &[norm, k, hk]);

        let x0 = {
            let ac = rn_cmul(d, cr, a, c);
            let n = rn_cneg(d, cr, ac);
            rn_cmul(d, cr, n, ninv)
        };
        let y0 = {
            let bc = rn_cmul(d, cr, b, c);
            let n = rn_cneg(d, cr, bc);
            rn_cmul(d, cr, n, ninv)
        };
        let p0 = pmk(d, cp, x0, y0);
        let x1 = {
            let n = rn_cneg(d, cr, b);
            rn_cadd(d, cr, x0, n)
        };
        let y1 = rn_cadd(d, cr, y0, a);
        let p1 = pmk(d, cp, x1, y1);

        // onRaw P0 l.
        let on_p0 = {
            let lhs = eval3(d, cr, a, b, c, x0, y0);
            let n_ninv = rn_cmul(d, cr, norm, ninv);
            let c_nninv = rn_cmul(d, cr, c, n_ninv);
            let neg_c_nninv = rn_cneg(d, cr, c_nninv);
            let mid = rn_cadd(d, cr, neg_c_nninv, c);

            let x0_rn = RnExpr::mul(RnExpr::neg(RnExpr::mul(at(a), at(c))), at(ninv));
            let y0_rn = RnExpr::mul(RnExpr::neg(RnExpr::mul(at(b), at(c))), at(ninv));
            let norm_rn = RnExpr::add(RnExpr::mul(at(a), at(a)), RnExpr::mul(at(b), at(b)));
            let lhs_rn = rev3(at(a), at(b), at(c), x0_rn, y0_rn);
            let mid_rn = RnExpr::add(
                RnExpr::neg(RnExpr::mul(at(c), RnExpr::mul(norm_rn, at(ninv)))),
                at(c),
            );
            let identity = ring(d, cr, &lhs_rn, &mid_rn);

            let one = rn_cone(d, cr);
            let refl_c = rn_crefl(d, cr, c);
            let to_one = d.lemma(cr.mul_congr, &[c, c, n_ninv, one, refl_c, cancel]);
            let c_one = rn_cmul(d, cr, c, one);
            let strip = d.lemma(cr.mul_one, &[c]);
            let collapse = rn_ctrans(d, cr, c_nninv, c_one, c, to_one, strip);
            let neg_c = rn_cneg(d, cr, c);
            let negged = d.lemma(cr.neg_congr, &[c_nninv, c, collapse]);
            let tail = rn_cadd(d, cr, neg_c, c);
            let lifted = d.lemma(cr.add_congr, &[neg_c_nninv, neg_c, c, c, negged, refl_c]);
            let tail_rn = RnExpr::add(RnExpr::neg(at(c)), at(c));
            let finish = ring(d, cr, &tail_rn, &RnExpr::Zero);
            let (_, proof) = rn_cchain(
                d,
                cr,
                lhs,
                &[(mid, identity), (tail, lifted), (zero, finish)],
            );
            proof
        };

        // onRaw P1 l — the shift by `(−b, a)` cancels in the ring.
        let on_p1 = {
            let lhs = eval3(d, cr, a, b, c, x1, y1);
            let rhs = eval3(d, cr, a, b, c, x0, y0);
            let lhs_rn = rev3(
                at(a),
                at(b),
                at(c),
                RnExpr::add(at(x0), RnExpr::neg(at(b))),
                RnExpr::add(at(y0), at(a)),
            );
            let rhs_rn = rev3(at(a), at(b), at(c), at(x0), at(y0));
            let same = ring(d, cr, &lhs_rn, &rhs_rn);
            rn_ctrans(d, cr, lhs, rhs, zero, same, on_p0)
        };

        // Apart P0 P1 — their distSq IS the line's own `a*a + b*b`.
        let apart_p0p1 = {
            let dd = dist_sq(d, cp, p0, p1);
            let lhs_rn = RnExpr::add(RnExpr::mul(at(a), at(a)), RnExpr::mul(at(b), at(b)));
            let x1_rn = RnExpr::add(at(x0), RnExpr::neg(at(b)));
            let y1_rn = RnExpr::add(at(y0), at(a));
            let du = rsub(at(x0), x1_rn);
            let dv = rsub(at(y0), y1_rn);
            let rhs_rn = RnExpr::add(RnExpr::mul(du.clone(), du), RnExpr::mul(dv.clone(), dv));
            let same = ring(d, cr, &lhs_rn, &rhs_rn);
            let moved = d.lemma(r.pos_bound_congr, &[norm, dd, k, same, hk]);
            let pred = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let pb = pos_bound(d, cr, dd, j);
                d.lam_fv(j_fv, nat, pb)
            };
            exists_intro(d, nat, pred, k, moved)
        };

        let apart_ty = d.const_app(r.apart, &[p0, p1]);
        let on0_ty = d.const_app(r.on_raw, &[p0, l]);
        let on1_ty = d.const_app(r.on_raw, &[p1, l]);
        let ons_ty = and_ty(d, on0_ty, on1_ty);
        let ons = and_intro(d, on0_ty, on1_ty, on_p0, on_p1);
        let payload = and_intro(d, apart_ty, ons_ty, apart_p0p1, ons);

        let inner_pred = {
            let qq_fv = d.fresh_fvar();
            let qq = d.kernel().fvar(qq_fv);
            let ap = d.const_app(r.apart, &[p0, qq]);
            let o0 = d.const_app(r.on_raw, &[p0, l]);
            let o1 = d.const_app(r.on_raw, &[qq, l]);
            let os = and_ty(d, o0, o1);
            let both = and_ty(d, ap, os);
            d.lam_fv(qq_fv, point, both)
        };
        let outer_pred = {
            let pp_fv = d.fresh_fvar();
            let pp = d.kernel().fvar(pp_fv);
            let qq_fv = d.fresh_fvar();
            let qq = d.kernel().fvar(qq_fv);
            let ap = d.const_app(r.apart, &[pp, qq]);
            let o0 = d.const_app(r.on_raw, &[pp, l]);
            let o1 = d.const_app(r.on_raw, &[qq, l]);
            let os = and_ty(d, o0, o1);
            let both = and_ty(d, ap, os);
            let inner = d.lam_fv(qq_fv, point, both);
            let ex = exists_ty(d, point, inner);
            d.lam_fv(pp_fv, point, ex)
        };
        let inner_witness = exists_intro(d, point, inner_pred, p1, payload);
        let proof = exists_intro(d, point, outer_pred, p0, inner_witness);

        let hk_ty = pos_bound(d, cr, norm, k);
        let concl = exists_ty(d, point, outer_pred);
        let ty = {
            let t = d.arrow(hk_ty, concl);
            let t = d.pi_fv(k_fv, nat, t);
            d.pi_fv(l_fv, line0, t)
        };
        let value = {
            let t = d.lam_fv(hk_fv, hk_ty, proof);
            let t = d.lam_fv(k_fv, nat, t);
            d.lam_fv(l_fv, line0, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.two_points_raw,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // twoPoints : ∀ l, ∃ P Q, Apart P Q ∧ (on P l ∧ on Q l).
    {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let raw = lval(d, r, l);
        let a = la(d, r, raw);
        let b = lb(d, r, raw);
        let norm = {
            let m1 = rn_cmul(d, cr, a, a);
            let m2 = rn_cmul(d, cr, b, b);
            rn_cadd(d, cr, m1, m2)
        };
        let pred = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let pb = pos_bound(d, cr, norm, j);
            d.lam_fv(j_fv, nat, pb)
        };
        let outer_pred = {
            let pp_fv = d.fresh_fvar();
            let pp = d.kernel().fvar(pp_fv);
            let qq_fv = d.fresh_fvar();
            let qq = d.kernel().fvar(qq_fv);
            let ap = d.const_app(r.apart, &[pp, qq]);
            let o0 = d.const_app(r.on, &[pp, l]);
            let o1 = d.const_app(r.on, &[qq, l]);
            let os = and_ty(d, o0, o1);
            let both = and_ty(d, ap, os);
            let inner = d.lam_fv(qq_fv, point, both);
            let ex = exists_ty(d, point, inner);
            d.lam_fv(pp_fv, point, ex)
        };
        let target = exists_ty(d, point, outer_pred);
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, norm, k);
            let body = d.lemma(r.two_points_raw, &[raw, k, hk]);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let prop = lprop(d, r, l);
        let proof = exists_elim(d, pred, target, prop, minor);

        let ty = d.pi_fv(l_fv, line, target);
        let value = d.lam_fv(l_fv, line, proof);
        d.kernel().add_declaration(Declaration::Theorem {
            name: r.two_points,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `triangle` — `(0,0)`, `(1,0)`, `(0,1)`, pairwise apart, on no common line.
fn declare_triangle(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);
    let one = rn_cone(d, cr);

    let a0 = pmk(d, cp, zero, zero);
    let b0 = pmk(d, cp, one, zero);
    let c0 = pmk(d, cp, zero, one);

    // `Equiv <literal> (distSq X Y)` for each pair, then `pos_bound_of_lt`.
    let refl_zero = rn_crefl(d, cr, zero);
    let two_const = d.kernel().const_(cp.two, vec![]);
    let zero_nat = d.num(0);
    let two_witness = d.kernel().const_(cp.two_pos_bound, vec![]);
    let two_pos = d.lemma(cr.pos_of_pos_bound, &[two_const, zero_nat, two_witness]);
    let one_pos = d.kernel().const_(cr.zero_lt_one, vec![]);
    let one_const = d.kernel().const_(cr.one, vec![]);

    let mut aparts: Vec<ExprId> = Vec::with_capacity(3);
    for (left, right, lx, ly, rx, ry, is_two) in [
        (
            a0,
            b0,
            RnExpr::Zero,
            RnExpr::Zero,
            RnExpr::One,
            RnExpr::Zero,
            false,
        ),
        (
            a0,
            c0,
            RnExpr::Zero,
            RnExpr::Zero,
            RnExpr::Zero,
            RnExpr::One,
            false,
        ),
        (
            b0,
            c0,
            RnExpr::One,
            RnExpr::Zero,
            RnExpr::Zero,
            RnExpr::One,
            true,
        ),
    ] {
        let dd = dist_sq(d, cp, left, right);
        let expanded = RnExpr::add(
            RnExpr::mul(rsub(lx.clone(), rx.clone()), rsub(lx, rx)),
            RnExpr::mul(rsub(ly.clone(), ry.clone()), rsub(ly, ry)),
        );
        let literal = if is_two {
            RnExpr::add(RnExpr::One, RnExpr::One)
        } else {
            RnExpr::One
        };
        let same = ring(d, cr, &literal, &expanded);
        let (scalar, positive) = if is_two {
            (two_const, two_pos)
        } else {
            (one_const, one_pos)
        };
        let lifted = d.lemma(
            cr.lt_congr,
            &[zero, zero, scalar, dd, refl_zero, same, positive],
        );
        aparts.push(d.lemma(cr.pos_bound_of_lt, &[dd, lifted]));
    }

    // ∀ l, on A l → on B l → on C l → False.
    let no_line = {
        let l_fv = d.fresh_fvar();
        let ha_fv = d.fresh_fvar();
        let hb_fv = d.fresh_fvar();
        let hc_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let ha = d.kernel().fvar(ha_fv);
        let hb = d.kernel().fvar(hb_fv);
        let hc = d.kernel().fvar(hc_fv);

        let raw = lval(d, r, l);
        let a = la(d, r, raw);
        let b = lb(d, r, raw);
        let c = lc(d, r, raw);

        // c ~ 0, from `on A l` at the origin.
        let at_origin = eval3(d, cr, a, b, c, zero, zero);
        let origin_rn = rev3(at(a), at(b), at(c), RnExpr::Zero, RnExpr::Zero);
        let to_c = ring(d, cr, &origin_rn, &at(c));
        let back_c = rn_csymm(d, cr, at_origin, c, to_c);
        let hc_zero = rn_ctrans(d, cr, c, at_origin, zero, back_c, ha);

        // a ~ 0 and b ~ 0, from the two unit points.
        let mut vanishing: Vec<ExprId> = Vec::with_capacity(2);
        for (coeff, sx, sy, sx_rn, sy_rn, hyp) in [
            (a, one, zero, RnExpr::One, RnExpr::Zero, hb),
            (b, zero, one, RnExpr::Zero, RnExpr::One, hc),
        ] {
            let at_unit = eval3(d, cr, a, b, c, sx, sy);
            let unit_rn = rev3(at(a), at(b), at(c), sx_rn, sy_rn);
            let pair = rn_cadd(d, cr, coeff, c);
            let pair_rn = RnExpr::add(at(coeff), at(c));
            let to_pair = ring(d, cr, &unit_rn, &pair_rn);
            let back = rn_csymm(d, cr, at_unit, pair, to_pair);
            let pair_zero = rn_ctrans(d, cr, pair, at_unit, zero, back, hyp);

            let coeff_zero = rn_cadd(d, cr, coeff, zero);
            let strip = d.lemma(cr.add_zero, &[coeff]);
            let step1 = rn_csymm(d, cr, coeff_zero, coeff, strip);
            let refl_coeff = rn_crefl(d, cr, coeff);
            let back_c_zero = rn_csymm(d, cr, c, zero, hc_zero);
            let step2 = d.lemma(
                cr.add_congr,
                &[coeff, coeff, zero, c, refl_coeff, back_c_zero],
            );
            let (_, done) = rn_cchain(
                d,
                cr,
                coeff,
                &[(coeff_zero, step1), (pair, step2), (zero, pair_zero)],
            );
            vanishing.push(done);
        }
        let ha_zero = vanishing[0];
        let hb_zero = vanishing[1];

        // a*a + b*b ~ 0, contradicting the line's own non-degeneracy witness.
        let norm = {
            let m1 = rn_cmul(d, cr, a, a);
            let m2 = rn_cmul(d, cr, b, b);
            rn_cadd(d, cr, m1, m2)
        };
        let sq_a = rn_cmul(d, cr, a, a);
        let sq_b = rn_cmul(d, cr, b, b);
        let zz = rn_cmul(d, cr, zero, zero);
        let ca = d.lemma(cr.mul_congr, &[a, zero, a, zero, ha_zero, ha_zero]);
        let cb = d.lemma(cr.mul_congr, &[b, zero, b, zero, hb_zero, hb_zero]);
        let both = rn_cadd(d, cr, zz, zz);
        let lifted = d.lemma(cr.add_congr, &[sq_a, zz, sq_b, zz, ca, cb]);
        let both_rn = RnExpr::add(
            RnExpr::mul(RnExpr::Zero, RnExpr::Zero),
            RnExpr::mul(RnExpr::Zero, RnExpr::Zero),
        );
        let finish = ring(d, cr, &both_rn, &RnExpr::Zero);
        let (_, norm_zero) = rn_cchain(d, cr, norm, &[(both, lifted), (zero, finish)]);

        let pred = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let pb = pos_bound(d, cr, norm, j);
            d.lam_fv(j_fv, nat, pb)
        };
        let f = false_ty(d);
        let minor = {
            let k_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = pos_bound(d, cr, norm, k);
            let body = d.lemma(r.not_zero_of_pos_bound, &[norm, k, hk, norm_zero]);
            let inner = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let prop = lprop(d, r, l);
        let body = exists_elim(d, pred, f, prop, minor);

        let oal = d.const_app(r.on, &[a0, l]);
        let obl = d.const_app(r.on, &[b0, l]);
        let ocl = d.const_app(r.on, &[c0, l]);
        let t = d.lam_fv(hc_fv, ocl, body);
        let t = d.lam_fv(hb_fv, obl, t);
        let t = d.lam_fv(ha_fv, oal, t);
        d.lam_fv(l_fv, line, t)
    };

    // Assemble `∃ A B C, …`.
    let no_line_ty = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let oal = d.const_app(r.on, &[a0, l]);
        let obl = d.const_app(r.on, &[b0, l]);
        let ocl = d.const_app(r.on, &[c0, l]);
        let f = false_ty(d);
        let t = d.arrow(ocl, f);
        let t = d.arrow(obl, t);
        let t = d.arrow(oal, t);
        d.pi_fv(l_fv, line, t)
    };
    let ab_ty = d.const_app(r.apart, &[a0, b0]);
    let ac_ty = d.const_app(r.apart, &[a0, c0]);
    let bc_ty = d.const_app(r.apart, &[b0, c0]);
    let tail_ty = and_ty(d, bc_ty, no_line_ty);
    let tail = and_intro(d, bc_ty, no_line_ty, aparts[2], no_line);
    let mid_ty = and_ty(d, ac_ty, tail_ty);
    let mid = and_intro(d, ac_ty, tail_ty, aparts[1], tail);
    let payload = and_intro(d, ab_ty, mid_ty, aparts[0], mid);

    // The three predicates, built with the outer points still free so that the
    // statement is the record's `triangle` shape verbatim.
    let body_at = |d: &mut IntDev<'_>, x: ExprId, y: ExprId, z: ExprId| -> ExprId {
        let ab = d.const_app(r.apart, &[x, y]);
        let ac = d.const_app(r.apart, &[x, z]);
        let bc = d.const_app(r.apart, &[y, z]);
        let nl = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let oal = d.const_app(r.on, &[x, l]);
            let obl = d.const_app(r.on, &[y, l]);
            let ocl = d.const_app(r.on, &[z, l]);
            let f = false_ty(d);
            let t = d.arrow(ocl, f);
            let t = d.arrow(obl, t);
            let t = d.arrow(oal, t);
            d.pi_fv(l_fv, line, t)
        };
        let t = and_ty(d, bc, nl);
        let t = and_ty(d, ac, t);
        and_ty(d, ab, t)
    };

    let pred_c = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let body = body_at(d, a0, b0, z);
        d.lam_fv(z_fv, point, body)
    };
    let pred_b = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let body = body_at(d, a0, y, z);
        let inner = d.lam_fv(z_fv, point, body);
        let ex = exists_ty(d, point, inner);
        d.lam_fv(y_fv, point, ex)
    };
    let pred_a = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let body = body_at(d, x, y, z);
        let inner = d.lam_fv(z_fv, point, body);
        let ex_inner = exists_ty(d, point, inner);
        let mid = d.lam_fv(y_fv, point, ex_inner);
        let ex_mid = exists_ty(d, point, mid);
        d.lam_fv(x_fv, point, ex_mid)
    };
    let level_c = exists_intro(d, point, pred_c, c0, payload);
    let level_b = exists_intro(d, point, pred_b, b0, level_c);
    let proof = exists_intro(d, point, pred_a, a0, level_b);
    let ty = exists_ty(d, point, pred_a);

    d.kernel().add_declaration(Declaration::Theorem {
        name: r.triangle,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// `Geo.rplane : Geo.Incidence` — the model itself.
fn declare_instance(d: &mut IntDev<'_>, p: GeoPrelude, r: RPlaneNames) -> Result<(), KernelError> {
    let cp = p.cpoint;
    let point = point_ty(d, cp);
    let line = line_ty(d, r);

    let peq = d.kernel().const_(cp.point_equiv, vec![]);
    let prefl = d.kernel().const_(r.point_refl, vec![]);
    let psymm = d.kernel().const_(r.point_symm, vec![]);
    let ptrans = d.kernel().const_(r.point_trans, vec![]);
    let leq = d.kernel().const_(r.line_equiv, vec![]);
    let lrefl = d.kernel().const_(r.line_equiv_refl, vec![]);
    let lsymm = d.kernel().const_(r.line_equiv_symm, vec![]);
    let ltrans = d.kernel().const_(r.line_equiv_trans, vec![]);
    let on = d.kernel().const_(r.on, vec![]);
    let on_point = d.kernel().const_(r.on_point, vec![]);
    let on_line = d.kernel().const_(r.on_line, vec![]);
    let apart = d.kernel().const_(r.apart, vec![]);
    let apart_ne = d.kernel().const_(r.apart_ne, vec![]);
    let apart_symm = d.kernel().const_(r.apart_symm, vec![]);
    let apart_congr = d.kernel().const_(r.apart_congr, vec![]);
    let join_exists = d.kernel().const_(r.join_exists, vec![]);
    let join_unique = d.kernel().const_(r.join_unique, vec![]);
    let two_points = d.kernel().const_(r.two_points, vec![]);
    let triangle = d.kernel().const_(r.triangle, vec![]);

    let args = [
        point,
        line,
        peq,
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
        name: r.instance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}
