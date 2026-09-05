//! `Geo.Incidence` — **synthetic incidence geometry as a record**, with the
//! rational coordinate plane as its model.
//!
//! Roadmap W3-8, ADR-1635. The real plane `CPoint` is **not** a model here:
//! the record is shaped so it can become one (that is what `apart` is for,
//! and the field layout below says so), but no ℝ² instance is built. See
//! [`qplane`] for the one that is, and the lane status file for the sized
//! obstruction on the ℝ side.
//!
//! # Why a record, and why this shape
//!
//! An incidence structure is two carriers and a relation between them, plus
//! Hilbert's three incidence axioms. It is declared through the same
//! [`declare_record`] spine every algebraic structure in this kernel uses
//! (ADR-1578), at `Sort 2`, with the ADR-1595 setoid discipline: both
//! carriers come with their **own** equivalence relation and the incidence
//! relation carries a congruence field for each. Nothing here uses `funext`
//! or `Quot.sound`; the record is an ordinary one-constructor inductive and
//! every derived theorem is built from its generated recursor.
//!
//! # The one design decision worth naming: `apart`, not `¬ pEq`
//!
//! Hilbert's first axiom is "two **distinct** points lie on exactly one
//! line". The obvious spelling of "distinct" is `pEq P Q → False`, and it is
//! the wrong one *for this kernel*, for a reason that only shows up at the
//! second model:
//!
//! - Over ℚ, point equality is the kernel's own `Eq` (ℚ's reduced
//!   representative is unique — `Rat.eq_of_cross`), the order is decidable
//!   (`Rat.lt_trichotomy`), and `Eq P Q → False` is a perfectly usable
//!   hypothesis: it *constructs* the nonzero coefficient the line-through
//!   construction needs.
//! - Over ℝ (`CReal`), `CPoint.Equiv P Q → False` constructs nothing. This
//!   kernel has neither Markov's principle nor a `CReal.inv` at a
//!   double-negated hypothesis: `CReal.inv` consumes a `CReal.PosBound`
//!   witness, and `CPoint.collinear_of_area_zero` — the theorem an ℝ model's
//!   uniqueness axiom has to route through — takes `PosBound (distSq A B) k`
//!   for exactly this reason and says so in its own doc.
//!
//! So `Geo.Incidence` carries **`apart`** as a field of its own, with three
//! laws (it refutes `pEq`, it is symmetric, it respects `pEq`), and the two
//! axioms that need "distinct" (`joinExists`, `joinUnique`) and the two
//! existence axioms (`twoPoints`, `triangle`) are stated with it. Each model
//! then supplies its own notion:
//!
//! | model | `pEq` | `apart` |
//! | --- | --- | --- |
//! | `Geo.QPlane` (ℚ²) | `Eq` | `Eq P Q → False` |
//! | an ℝ² model (`CPoint`) | `CPoint.Equiv` | `∃ k, CReal.PosBound (distSq P Q) k` |
//!
//! **Which axiom needs it**: `joinUnique` is the one. `joinExists` could be
//! stated with `¬ Equiv` in either model (the line through two points is
//! computed from their coordinates and never divides), and `twoPoints` and
//! `triangle` only ever *produce* distinctness, so a stronger notion makes
//! them harder to supply but never unstatable. `joinUnique` **consumes**
//! distinctness, and over ℝ the consumption is a division by `distSq P Q` —
//! which is `CReal.inv`, which is `PosBound`-indexed. Abstracting `apart`
//! is what lets one record serve both.
//!
//! # Field layout
//!
//! | # | field | type |
//! |---|---|---|
//! | 0 | `point` | `Sort 1` |
//! | 1 | `line` | `Sort 1` |
//! | 2 | `pEq` | `point → point → Prop` |
//! | 3 | `pRefl` | `∀ P, pEq P P` |
//! | 4 | `pSymm` | `∀ P Q, pEq P Q → pEq Q P` |
//! | 5 | `pTrans` | `∀ P Q R, pEq P Q → pEq Q R → pEq P R` |
//! | 6 | `lEq` | `line → line → Prop` |
//! | 7 | `lRefl` | `∀ l, lEq l l` |
//! | 8 | `lSymm` | `∀ l m, lEq l m → lEq m l` |
//! | 9 | `lTrans` | `∀ l m n, lEq l m → lEq m n → lEq l n` |
//! | 10 | `on` | `point → line → Prop` |
//! | 11 | `onPoint` | `∀ P Q l, pEq P Q → on P l → on Q l` |
//! | 12 | `onLine` | `∀ P l m, lEq l m → on P l → on P m` |
//! | 13 | `apart` | `point → point → Prop` |
//! | 14 | `apartNe` | `∀ P Q, apart P Q → pEq P Q → False` |
//! | 15 | `apartSymm` | `∀ P Q, apart P Q → apart Q P` |
//! | 16 | `apartCongr` | `∀ P P' Q, pEq P P' → apart P Q → apart P' Q` |
//! | 17 | `joinExists` | `∀ P Q, apart P Q → ∃ l, on P l ∧ on Q l` |
//! | 18 | `joinUnique` | `∀ P Q l m, apart P Q → on P l → on Q l → on P m → on Q m → lEq l m` |
//! | 19 | `twoPoints` | `∀ l, ∃ P Q, apart P Q ∧ (on P l ∧ on Q l)` |
//! | 20 | `triangle` | `∃ A B C, apart A B ∧ (apart A C ∧ (apart B C ∧ ∀ l, on A l → on B l → on C l → False))` |
//!
//! Fields 17–18 are Hilbert I.1 split into its existence and uniqueness
//! halves (this kernel has no `ExistsUnique`); 19 is I.2; 20 is I.3.
//!
//! # Derived theorems
//!
//! Everything below is proved **once, over an arbitrary `I : Geo.Incidence`**
//! — the whole point of having the record at all.
//!
//! ```text
//! Geo.Incidence.Collinear : Π (I : Geo.Incidence) (A B C : Geo.Incidence.point I), Prop
//!   := ∃ l, on I A l ∧ (on I B l ∧ on I C l)
//! Geo.Incidence.collinear_intro : ∀ I l A B C,
//!     on I A l → on I B l → on I C l → Collinear I A B C
//! Geo.Incidence.collinear_perm  : ∀ I A B C, Collinear I A B C → Collinear I B A C
//! Geo.Incidence.distinct_lines_meet_once : ∀ I P Q l m,
//!     (lEq I l m → False) → apart I P Q →
//!     on I P l → on I Q l → on I P m → on I Q m → False
//! Geo.Incidence.triangle_not_collinear : ∀ I A B C,
//!     (∀ l, on I A l → on I B l → on I C l → False) → Collinear I A B C → False
//! ```
//!
//! `distinct_lines_meet_once` **is** "two distinct lines meet in at most one
//! point", in the only form this kernel can state without a subtraction on
//! points: hand it two points that are apart and both on both lines, and the
//! two lines cannot be distinct.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::BinderInfo;
use crate::CPointPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::structures::{
    FieldKind, FieldSpec, MAX_FIELDS, RecordNames, arrow, declare_record, pi_over,
};
use crate::prelude::LogicPrelude;

pub mod qplane;

#[cfg(test)]
mod geo_tests;

pub use qplane::QPlaneNames;

// ---------------------------------------------------------------------------
// Field indices. Index a field through these, never with a bare integer.
// ---------------------------------------------------------------------------

/// `Geo.Incidence.point`.
pub const POINT: usize = 0;
/// `Geo.Incidence.line`.
pub const LINE: usize = 1;
/// `Geo.Incidence.pEq`.
pub const P_EQ: usize = 2;
/// `Geo.Incidence.pRefl`.
pub const P_REFL: usize = 3;
/// `Geo.Incidence.pSymm`.
pub const P_SYMM: usize = 4;
/// `Geo.Incidence.pTrans`.
pub const P_TRANS: usize = 5;
/// `Geo.Incidence.lEq`.
pub const L_EQ: usize = 6;
/// `Geo.Incidence.lRefl`.
pub const L_REFL: usize = 7;
/// `Geo.Incidence.lSymm`.
pub const L_SYMM: usize = 8;
/// `Geo.Incidence.lTrans`.
pub const L_TRANS: usize = 9;
/// `Geo.Incidence.on`.
pub const ON: usize = 10;
/// `Geo.Incidence.onPoint`.
pub const ON_POINT: usize = 11;
/// `Geo.Incidence.onLine`.
pub const ON_LINE: usize = 12;
/// `Geo.Incidence.apart`.
pub const APART: usize = 13;
/// `Geo.Incidence.apartNe`.
pub const APART_NE: usize = 14;
/// `Geo.Incidence.apartSymm`.
pub const APART_SYMM: usize = 15;
/// `Geo.Incidence.apartCongr`.
pub const APART_CONGR: usize = 16;
/// `Geo.Incidence.joinExists`.
pub const JOIN_EXISTS: usize = 17;
/// `Geo.Incidence.joinUnique`.
pub const JOIN_UNIQUE: usize = 18;
/// `Geo.Incidence.twoPoints`.
pub const TWO_POINTS: usize = 19;
/// `Geo.Incidence.triangle`.
pub const TRIANGLE: usize = 20;

/// The number of fields the record carries.
pub const FIELD_COUNT: usize = 21;

/// The selector suffixes, in field order. Paired against [`declare_record`]'s
/// own output in [`build_geo_prelude`] so this file's two descriptions of one
/// record cannot drift apart.
pub(crate) const FIELD_SUFFIXES: [&str; FIELD_COUNT] = [
    "point",
    "line",
    "pEq",
    "pRefl",
    "pSymm",
    "pTrans",
    "lEq",
    "lRefl",
    "lSymm",
    "lTrans",
    "on",
    "onPoint",
    "onLine",
    "apart",
    "apartNe",
    "apartSymm",
    "apartCongr",
    "joinExists",
    "joinUnique",
    "twoPoints",
    "triangle",
];

// Free-variable ids used inside the field-shape closures and the derived
// declarations. Disjoint from `structures::CTOR_FVAR_BASE` (10_000),
// `SELECTOR_S_FV` (10_900), `metric`'s 20_800 band and `sigma_prelude`'s
// 71_000 band.
const G_P: u64 = 82_000;
const G_Q: u64 = 82_001;
const G_R: u64 = 82_002;
const G_L: u64 = 82_003;
const G_M: u64 = 82_004;
const G_A: u64 = 82_006;
const G_B: u64 = 82_007;
const G_C: u64 = 82_008;

/// The bound `I : Geo.Incidence` of every derived declaration.
const G_I: u64 = 82_100;
const G_H1: u64 = 82_110;
const G_H2: u64 = 82_111;
const G_H3: u64 = 82_112;
const G_H4: u64 = 82_113;
const G_H5: u64 = 82_114;
const G_H6: u64 = 82_115;

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

fn app_all(k: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
    let mut e = head;
    for &a in args {
        e = k.app(e, a);
    }
    e
}

fn capp(k: &mut Kernel, name: NameId, args: &[ExprId]) -> ExprId {
    let head = k.const_(name, vec![]);
    app_all(k, head, args)
}

fn prop_sort(k: &mut Kernel) -> ExprId {
    let l0 = k.level_zero();
    k.sort(l0)
}

/// `a → b → Prop`.
fn rel_ty(k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
    let prop = prop_sort(k);
    let inner = arrow(k, b, prop);
    arrow(k, a, inner)
}

fn and_of(k: &mut Kernel, lg: &LogicPrelude, p: ExprId, q: ExprId) -> ExprId {
    capp(k, lg.and, &[p, q])
}

fn and_left(k: &mut Kernel, lg: &LogicPrelude, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    capp(k, lg.and_left, &[p, q, h])
}

fn and_right(k: &mut Kernel, lg: &LogicPrelude, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    capp(k, lg.and_right, &[p, q, h])
}

fn false_of(k: &mut Kernel, lg: &LogicPrelude) -> ExprId {
    k.const_(lg.false_, vec![])
}

/// `Exists.{lvl} ty pred`.
fn exists_of(k: &mut Kernel, lg: &LogicPrelude, lvl: LevelId, ty: ExprId, pred: ExprId) -> ExprId {
    let head = k.const_(lg.exists_, vec![lvl]);
    app_all(k, head, &[ty, pred])
}

/// `fun (x : ty) => body`, with `x` the free variable `fv`.
fn lam_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let abstracted = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.lam(anon, ty, abstracted, BinderInfo::Default)
}

/// `∃ (x : ty), body(x)`, with `x` the free variable `fv`.
fn exists_over(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
) -> ExprId {
    let pred = lam_over(k, fv, ty, body);
    exists_of(k, lg, lvl, ty, pred)
}

// ---------------------------------------------------------------------------
// Field shapes.
// ---------------------------------------------------------------------------

fn carrier_field(suffix: &'static str) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// A binary relation between the carriers at `left` and `right`.
fn relation_field(suffix: &'static str, left: usize, right: usize) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[left];
            let b = vals[right];
            rel_ty(k, a, b)
        }),
    }
}

/// `∀ x, rel x x`.
fn refl_field(suffix: &'static str, carrier: usize, rel: usize) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[carrier];
            let r = vals[rel];
            let x = k.fvar(G_P);
            let body = app_all(k, r, &[x, x]);
            pi_over(k, G_P, ty, body)
        }),
    }
}

/// `∀ x y, rel x y → rel y x`.
fn symm_field(suffix: &'static str, carrier: usize, rel: usize) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[carrier];
            let r = vals[rel];
            let x = k.fvar(G_P);
            let y = k.fvar(G_Q);
            let xy = app_all(k, r, &[x, y]);
            let yx = app_all(k, r, &[y, x]);
            let imp = arrow(k, xy, yx);
            let t = pi_over(k, G_Q, ty, imp);
            pi_over(k, G_P, ty, t)
        }),
    }
}

/// `∀ x y z, rel x y → rel y z → rel x z`.
fn trans_field(suffix: &'static str, carrier: usize, rel: usize) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[carrier];
            let r = vals[rel];
            let x = k.fvar(G_P);
            let y = k.fvar(G_Q);
            let z = k.fvar(G_R);
            let xy = app_all(k, r, &[x, y]);
            let yz = app_all(k, r, &[y, z]);
            let xz = app_all(k, r, &[x, z]);
            let inner = arrow(k, yz, xz);
            let imp = arrow(k, xy, inner);
            let t = pi_over(k, G_R, ty, imp);
            let t = pi_over(k, G_Q, ty, t);
            pi_over(k, G_P, ty, t)
        }),
    }
}

/// `∀ P Q l, pEq P Q → on P l → on Q l`.
fn on_point_field() -> FieldSpec {
    FieldSpec {
        suffix: "onPoint",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let peq = vals[P_EQ];
            let on = vals[ON];
            let p = k.fvar(G_P);
            let q = k.fvar(G_Q);
            let l = k.fvar(G_L);
            let h = app_all(k, peq, &[p, q]);
            let opl = app_all(k, on, &[p, l]);
            let oql = app_all(k, on, &[q, l]);
            let inner = arrow(k, opl, oql);
            let imp = arrow(k, h, inner);
            let t = pi_over(k, G_L, ln, imp);
            let t = pi_over(k, G_Q, pt, t);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ P l m, lEq l m → on P l → on P m`.
fn on_line_field() -> FieldSpec {
    FieldSpec {
        suffix: "onLine",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let leq = vals[L_EQ];
            let on = vals[ON];
            let p = k.fvar(G_P);
            let l = k.fvar(G_L);
            let m = k.fvar(G_M);
            let h = app_all(k, leq, &[l, m]);
            let opl = app_all(k, on, &[p, l]);
            let opm = app_all(k, on, &[p, m]);
            let inner = arrow(k, opl, opm);
            let imp = arrow(k, h, inner);
            let t = pi_over(k, G_M, ln, imp);
            let t = pi_over(k, G_L, ln, t);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ P Q, apart P Q → pEq P Q → False`.
fn apart_ne_field() -> FieldSpec {
    FieldSpec {
        suffix: "apartNe",
        kind: FieldKind::Law,
        build: Box::new(|k, lg, _l1, vals| {
            let pt = vals[POINT];
            let peq = vals[P_EQ];
            let ap = vals[APART];
            let p = k.fvar(G_P);
            let q = k.fvar(G_Q);
            let a = app_all(k, ap, &[p, q]);
            let e = app_all(k, peq, &[p, q]);
            let f = false_of(k, lg);
            let inner = arrow(k, e, f);
            let imp = arrow(k, a, inner);
            let t = pi_over(k, G_Q, pt, imp);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ P P' Q, pEq P P' → apart P Q → apart P' Q`.
fn apart_congr_field() -> FieldSpec {
    FieldSpec {
        suffix: "apartCongr",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let pt = vals[POINT];
            let peq = vals[P_EQ];
            let ap = vals[APART];
            let p = k.fvar(G_P);
            let p2 = k.fvar(G_R);
            let q = k.fvar(G_Q);
            let h = app_all(k, peq, &[p, p2]);
            let a1 = app_all(k, ap, &[p, q]);
            let a2 = app_all(k, ap, &[p2, q]);
            let inner = arrow(k, a1, a2);
            let imp = arrow(k, h, inner);
            let t = pi_over(k, G_Q, pt, imp);
            let t = pi_over(k, G_R, pt, t);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ P Q, apart P Q → ∃ l, on P l ∧ on Q l`.
fn join_exists_field() -> FieldSpec {
    FieldSpec {
        suffix: "joinExists",
        kind: FieldKind::Law,
        build: Box::new(|k, lg, l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let ap = vals[APART];
            let on = vals[ON];
            let p = k.fvar(G_P);
            let q = k.fvar(G_Q);
            let l = k.fvar(G_L);
            let opl = app_all(k, on, &[p, l]);
            let oql = app_all(k, on, &[q, l]);
            let body = and_of(k, lg, opl, oql);
            let ex = exists_over(k, lg, l1, G_L, ln, body);
            let a = app_all(k, ap, &[p, q]);
            let imp = arrow(k, a, ex);
            let t = pi_over(k, G_Q, pt, imp);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ P Q l m, apart P Q → on P l → on Q l → on P m → on Q m → lEq l m`.
fn join_unique_field() -> FieldSpec {
    FieldSpec {
        suffix: "joinUnique",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let leq = vals[L_EQ];
            let ap = vals[APART];
            let on = vals[ON];
            let p = k.fvar(G_P);
            let q = k.fvar(G_Q);
            let l = k.fvar(G_L);
            let m = k.fvar(G_M);
            let a = app_all(k, ap, &[p, q]);
            let opl = app_all(k, on, &[p, l]);
            let oql = app_all(k, on, &[q, l]);
            let opm = app_all(k, on, &[p, m]);
            let oqm = app_all(k, on, &[q, m]);
            let concl = app_all(k, leq, &[l, m]);
            let body = arrow(k, oqm, concl);
            let body = arrow(k, opm, body);
            let body = arrow(k, oql, body);
            let body = arrow(k, opl, body);
            let body = arrow(k, a, body);
            let t = pi_over(k, G_M, ln, body);
            let t = pi_over(k, G_L, ln, t);
            let t = pi_over(k, G_Q, pt, t);
            pi_over(k, G_P, pt, t)
        }),
    }
}

/// `∀ l, ∃ P Q, apart P Q ∧ (on P l ∧ on Q l)`.
fn two_points_field() -> FieldSpec {
    FieldSpec {
        suffix: "twoPoints",
        kind: FieldKind::Law,
        build: Box::new(|k, lg, l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let ap = vals[APART];
            let on = vals[ON];
            let l = k.fvar(G_L);
            let p = k.fvar(G_P);
            let q = k.fvar(G_Q);
            let a = app_all(k, ap, &[p, q]);
            let opl = app_all(k, on, &[p, l]);
            let oql = app_all(k, on, &[q, l]);
            let ons = and_of(k, lg, opl, oql);
            let body = and_of(k, lg, a, ons);
            let inner = exists_over(k, lg, l1, G_Q, pt, body);
            let outer = exists_over(k, lg, l1, G_P, pt, inner);
            pi_over(k, G_L, ln, outer)
        }),
    }
}

/// `∃ A B C, apart A B ∧ (apart A C ∧ (apart B C ∧ ∀ l, on A l → on B l → on C l → False))`.
fn triangle_field() -> FieldSpec {
    FieldSpec {
        suffix: "triangle",
        kind: FieldKind::Law,
        build: Box::new(|k, lg, l1, vals| {
            let pt = vals[POINT];
            let ln = vals[LINE];
            let ap = vals[APART];
            let on = vals[ON];
            let a = k.fvar(G_A);
            let b = k.fvar(G_B);
            let c = k.fvar(G_C);
            let l = k.fvar(G_L);
            let oal = app_all(k, on, &[a, l]);
            let obl = app_all(k, on, &[b, l]);
            let ocl = app_all(k, on, &[c, l]);
            let f = false_of(k, lg);
            let chain = arrow(k, ocl, f);
            let chain = arrow(k, obl, chain);
            let chain = arrow(k, oal, chain);
            let noline = pi_over(k, G_L, ln, chain);
            let ab = app_all(k, ap, &[a, b]);
            let ac = app_all(k, ap, &[a, c]);
            let bc = app_all(k, ap, &[b, c]);
            let body = and_of(k, lg, bc, noline);
            let body = and_of(k, lg, ac, body);
            let body = and_of(k, lg, ab, body);
            let inner = exists_over(k, lg, l1, G_C, pt, body);
            let inner = exists_over(k, lg, l1, G_B, pt, inner);
            exists_over(k, lg, l1, G_A, pt, inner)
        }),
    }
}

/// The 21 field shapes, in declaration order.
pub(crate) fn incidence_fields() -> Vec<FieldSpec> {
    vec![
        carrier_field("point"),
        carrier_field("line"),
        relation_field("pEq", POINT, POINT),
        refl_field("pRefl", POINT, P_EQ),
        symm_field("pSymm", POINT, P_EQ),
        trans_field("pTrans", POINT, P_EQ),
        relation_field("lEq", LINE, LINE),
        refl_field("lRefl", LINE, L_EQ),
        symm_field("lSymm", LINE, L_EQ),
        trans_field("lTrans", LINE, L_EQ),
        relation_field("on", POINT, LINE),
        on_point_field(),
        on_line_field(),
        relation_field("apart", POINT, POINT),
        apart_ne_field(),
        symm_field("apartSymm", POINT, APART),
        apart_congr_field(),
        join_exists_field(),
        join_unique_field(),
        two_points_field(),
        triangle_field(),
    ]
}

// ---------------------------------------------------------------------------
// The prelude handle.
// ---------------------------------------------------------------------------

/// The interned names produced by [`build_geo_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeoPrelude {
    /// The real plane the second model would live on, and through it `CReal`,
    /// `Rat`, `Int`, `Nat` and the logical prelude.
    pub cpoint: CPointPrelude,
    /// The `Geo.Incidence` record: its inductive, `mk`, `rec` and 21
    /// selectors.
    pub record: RecordNames,

    // --- theorems derived once, over an arbitrary incidence structure ------
    /// `Geo.Incidence.Collinear : Π (I : Geo.Incidence) (A B C : point I), Prop`
    /// — `∃ l, on A l ∧ (on B l ∧ on C l)`. A `Definition`, so it unfolds.
    pub collinear: NameId,
    /// `Geo.Incidence.collinear_intro : ∀ I l A B C,
    /// on I A l → on I B l → on I C l → Collinear I A B C`.
    pub collinear_intro: NameId,
    /// `Geo.Incidence.collinear_perm : ∀ I A B C,
    /// Collinear I A B C → Collinear I B A C` — the first two points swap,
    /// by `Exists.rec` and a re-association of the three `on` conjuncts.
    pub collinear_perm: NameId,
    /// `Geo.Incidence.distinct_lines_meet_once : ∀ I P Q l m,
    /// (lEq I l m → False) → apart I P Q →
    /// on I P l → on I Q l → on I P m → on I Q m → False` — **two distinct
    /// lines meet in at most one point.**
    pub distinct_lines_meet_once: NameId,
    /// `Geo.Incidence.triangle_not_collinear : ∀ I A B C,
    /// (∀ l, on I A l → on I B l → on I C l → False) → Collinear I A B C → False`
    /// — the `triangle` axiom's fourth conjunct is exactly the negation of
    /// [`Self::collinear`], which this makes checkable rather than asserted.
    pub triangle_not_collinear: NameId,

    /// The rational coordinate plane, the model that proves these axioms
    /// consistent.
    pub qplane: QPlaneNames,
}

/// Pre-compute every name this module declares.
pub(crate) fn intern(kernel: &mut Kernel, cpoint: CPointPrelude) -> GeoPrelude {
    let anon = kernel.anon();
    let geo = kernel.name_str(anon, "Geo");
    let inc = kernel.name_str(geo, "Incidence");

    let mk = kernel.name_str(inc, "mk");
    let rec = kernel.name_str(inc, "rec");
    let mut selectors = [mk; MAX_FIELDS];
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        selectors[i] = kernel.name_str(inc, *suffix);
    }

    GeoPrelude {
        cpoint,
        record: RecordNames {
            ind: inc,
            mk,
            rec,
            selectors,
            len: FIELD_COUNT,
        },
        collinear: kernel.name_str(inc, "Collinear"),
        collinear_intro: kernel.name_str(inc, "collinear_intro"),
        collinear_perm: kernel.name_str(inc, "collinear_perm"),
        distinct_lines_meet_once: kernel.name_str(inc, "distinct_lines_meet_once"),
        triangle_not_collinear: kernel.name_str(inc, "triangle_not_collinear"),
        qplane: qplane::intern(kernel, geo),
    }
}

/// Build (or return, if already built) the `Geo.*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics if the field list has drifted from [`FIELD_COUNT`] or if
/// [`declare_record`] returns selectors under names other than the ones
/// [`intern`] pre-computed — the two internal descriptions of one record.
pub fn build_geo_prelude(kernel: &mut Kernel) -> Result<GeoPrelude, KernelError> {
    let cpoint = crate::build_cpoint_prelude(kernel)?;
    let p = intern(kernel, cpoint);
    if kernel.environment().get(p.record.ind).is_some() {
        return Ok(p);
    }

    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);
    let logic = cpoint.creal.rat.int.logic;
    let specs = incidence_fields();
    assert_eq!(
        specs.len(),
        FIELD_COUNT,
        "field list out of step with FIELD_COUNT"
    );
    let record = declare_record(kernel, &logic, l0, l1, l2, p.record.ind, &specs)?;
    assert_eq!(
        record.field_count(),
        FIELD_COUNT,
        "declare_record produced the wrong field count"
    );
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        assert_eq!(
            record.sel(i),
            p.record.sel(i),
            "selector {i} ({suffix}) was interned under a different name"
        );
    }

    declare_collinear(kernel, &logic, p)?;
    declare_collinear_intro(kernel, &logic, p)?;
    declare_collinear_perm(kernel, &logic, p)?;
    declare_distinct_lines_meet_once(kernel, &logic, p)?;
    declare_triangle_not_collinear(kernel, &logic, p)?;

    qplane::declare_all(kernel, p)?;

    Ok(p)
}

// ---------------------------------------------------------------------------
// Shorthands over a bound `I : Geo.Incidence`.
// ---------------------------------------------------------------------------

/// `Geo.Incidence` (the record's own type).
fn inc_ty(k: &mut Kernel, p: GeoPrelude) -> ExprId {
    k.const_(p.record.ind, vec![])
}

/// Selector `i` applied to `s`.
fn field(k: &mut Kernel, p: GeoPrelude, i: usize, s: ExprId) -> ExprId {
    capp(k, p.record.sel(i), &[s])
}

/// `Geo.Incidence.on I P l`.
fn on_of(k: &mut Kernel, p: GeoPrelude, i: ExprId, pt: ExprId, l: ExprId) -> ExprId {
    let on = field(k, p, ON, i);
    app_all(k, on, &[pt, l])
}

/// The predicate `Collinear I A B C` unfolds to: `fun l => on A l ∧ (on B l ∧ on C l)`,
/// with `l` bound at `fv`.
fn collinear_pred(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
    i: ExprId,
    ln: ExprId,
    fv: u64,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let l = k.fvar(fv);
    let oal = on_of(k, p, i, a, l);
    let obl = on_of(k, p, i, b, l);
    let ocl = on_of(k, p, i, c, l);
    let tail = and_of(k, lg, obl, ocl);
    let body = and_of(k, lg, oal, tail);
    lam_over(k, fv, ln, body)
}

// ---------------------------------------------------------------------------
// The derived declarations.
// ---------------------------------------------------------------------------

/// `Geo.Incidence.Collinear I A B C := ∃ l, on I A l ∧ (on I B l ∧ on I C l)`.
fn declare_collinear(k: &mut Kernel, lg: &LogicPrelude, p: GeoPrelude) -> Result<(), KernelError> {
    let inc = inc_ty(k, p);
    let i = k.fvar(G_I);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let a = k.fvar(G_A);
    let b = k.fvar(G_B);
    let c = k.fvar(G_C);
    let pred = collinear_pred(k, lg, p, i, ln, G_L, a, b, c);
    let ex = exists_of(k, lg, l1, ln, pred);

    let value = {
        let t = lam_over(k, G_C, pt, ex);
        let t = lam_over(k, G_B, pt, t);
        let t = lam_over(k, G_A, pt, t);
        lam_over(k, G_I, inc, t)
    };
    let ty = {
        let prop = prop_sort(k);
        let t = pi_over(k, G_C, pt, prop);
        let t = pi_over(k, G_B, pt, t);
        let t = pi_over(k, G_A, pt, t);
        pi_over(k, G_I, inc, t)
    };
    k.add_declaration(Declaration::Definition {
        name: p.collinear,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Geo.Incidence.collinear_intro : ∀ I l A B C,
/// on I A l → on I B l → on I C l → Collinear I A B C`.
fn declare_collinear_intro(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let inc = inc_ty(k, p);
    let i = k.fvar(G_I);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let a = k.fvar(G_A);
    let b = k.fvar(G_B);
    let c = k.fvar(G_C);
    let l = k.fvar(G_L);
    let oal = on_of(k, p, i, a, l);
    let obl = on_of(k, p, i, b, l);
    let ocl = on_of(k, p, i, c, l);

    // `M` (not `L`) binds the predicate, so abstracting `L` for the outer Pi
    // cannot reach inside it.
    let pred = collinear_pred(k, lg, p, i, ln, G_M, a, b, c);

    let ha = k.fvar(G_H1);
    let hb = k.fvar(G_H2);
    let hc = k.fvar(G_H3);
    let tail_ty = and_of(k, lg, obl, ocl);
    let tail_proof = capp(k, lg.and_intro, &[obl, ocl, hb, hc]);
    let witness_proof = capp(k, lg.and_intro, &[oal, tail_ty, ha, tail_proof]);
    let intro = k.const_(lg.exists_intro, vec![l1]);
    let proof = app_all(k, intro, &[ln, pred, l, witness_proof]);

    let concl = capp(k, p.collinear, &[i, a, b, c]);
    let ty = {
        let t = arrow(k, ocl, concl);
        let t = arrow(k, obl, t);
        let t = arrow(k, oal, t);
        let t = pi_over(k, G_C, pt, t);
        let t = pi_over(k, G_B, pt, t);
        let t = pi_over(k, G_A, pt, t);
        let t = pi_over(k, G_L, ln, t);
        pi_over(k, G_I, inc, t)
    };
    let value = {
        let t = lam_over(k, G_H3, ocl, proof);
        let t = lam_over(k, G_H2, obl, t);
        let t = lam_over(k, G_H1, oal, t);
        let t = lam_over(k, G_C, pt, t);
        let t = lam_over(k, G_B, pt, t);
        let t = lam_over(k, G_A, pt, t);
        let t = lam_over(k, G_L, ln, t);
        lam_over(k, G_I, inc, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.collinear_intro,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.Incidence.collinear_perm : ∀ I A B C, Collinear I A B C → Collinear I B A C`.
fn declare_collinear_perm(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let inc = inc_ty(k, p);
    let i = k.fvar(G_I);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let a = k.fvar(G_A);
    let b = k.fvar(G_B);
    let c = k.fvar(G_C);

    let pred = collinear_pred(k, lg, p, i, ln, G_M, a, b, c);
    let source = capp(k, p.collinear, &[i, a, b, c]);
    let target = capp(k, p.collinear, &[i, b, a, c]);

    // minor : ∀ (l : line I), (on A l ∧ (on B l ∧ on C l)) → Collinear I B A C
    let minor = {
        let l = k.fvar(G_L);
        let oal = on_of(k, p, i, a, l);
        let obl = on_of(k, p, i, b, l);
        let ocl = on_of(k, p, i, c, l);
        let tail_ty = and_of(k, lg, obl, ocl);
        let hyp_ty = and_of(k, lg, oal, tail_ty);
        let h = k.fvar(G_H2);
        let ha = and_left(k, lg, oal, tail_ty, h);
        let tail = and_right(k, lg, oal, tail_ty, h);
        let hb = and_left(k, lg, obl, ocl, tail);
        let hc = and_right(k, lg, obl, ocl, tail);
        let body = capp(k, p.collinear_intro, &[i, l, b, a, c, hb, ha, hc]);
        let inner = lam_over(k, G_H2, hyp_ty, body);
        lam_over(k, G_L, ln, inner)
    };

    let h_col = k.fvar(G_H1);
    let motive = lam_over(k, G_H3, source, target);
    let rec = k.const_(lg.exists_rec, vec![l1]);
    let proof = app_all(k, rec, &[ln, pred, motive, minor, h_col]);

    let ty = {
        let t = arrow(k, source, target);
        let t = pi_over(k, G_C, pt, t);
        let t = pi_over(k, G_B, pt, t);
        let t = pi_over(k, G_A, pt, t);
        pi_over(k, G_I, inc, t)
    };
    let value = {
        let t = lam_over(k, G_H1, source, proof);
        let t = lam_over(k, G_C, pt, t);
        let t = lam_over(k, G_B, pt, t);
        let t = lam_over(k, G_A, pt, t);
        lam_over(k, G_I, inc, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.collinear_perm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.Incidence.distinct_lines_meet_once : ∀ I P Q l m,
/// (lEq I l m → False) → apart I P Q →
/// on I P l → on I Q l → on I P m → on I Q m → False`.
fn declare_distinct_lines_meet_once(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let inc = inc_ty(k, p);
    let i = k.fvar(G_I);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);

    let pp = k.fvar(G_P);
    let qq = k.fvar(G_Q);
    let l = k.fvar(G_L);
    let m = k.fvar(G_M);

    let leq = field(k, p, L_EQ, i);
    let same = app_all(k, leq, &[l, m]);
    let ap = field(k, p, APART, i);
    let apart = app_all(k, ap, &[pp, qq]);
    let opl = on_of(k, p, i, pp, l);
    let oql = on_of(k, p, i, qq, l);
    let opm = on_of(k, p, i, pp, m);
    let oqm = on_of(k, p, i, qq, m);

    let hne = k.fvar(G_H1);
    let hap = k.fvar(G_H2);
    let h1 = k.fvar(G_H3);
    let h2 = k.fvar(G_H4);
    let h3 = k.fvar(G_H5);
    let h4 = k.fvar(G_H6);

    let join = field(k, p, JOIN_UNIQUE, i);
    let derived = app_all(k, join, &[pp, qq, l, m, hap, h1, h2, h3, h4]);
    let proof = k.app(hne, derived);

    let false_ty = false_of(k, lg);
    let hne_ty = arrow(k, same, false_ty);

    let ty = {
        let t = arrow(k, oqm, false_ty);
        let t = arrow(k, opm, t);
        let t = arrow(k, oql, t);
        let t = arrow(k, opl, t);
        let t = arrow(k, apart, t);
        let t = arrow(k, hne_ty, t);
        let t = pi_over(k, G_M, ln, t);
        let t = pi_over(k, G_L, ln, t);
        let t = pi_over(k, G_Q, pt, t);
        let t = pi_over(k, G_P, pt, t);
        pi_over(k, G_I, inc, t)
    };
    let value = {
        let t = lam_over(k, G_H6, oqm, proof);
        let t = lam_over(k, G_H5, opm, t);
        let t = lam_over(k, G_H4, oql, t);
        let t = lam_over(k, G_H3, opl, t);
        let t = lam_over(k, G_H2, apart, t);
        let t = lam_over(k, G_H1, hne_ty, t);
        let t = lam_over(k, G_M, ln, t);
        let t = lam_over(k, G_L, ln, t);
        let t = lam_over(k, G_Q, pt, t);
        let t = lam_over(k, G_P, pt, t);
        lam_over(k, G_I, inc, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.distinct_lines_meet_once,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.Incidence.triangle_not_collinear : ∀ I A B C,
/// (∀ l, on I A l → on I B l → on I C l → False) → Collinear I A B C → False`.
fn declare_triangle_not_collinear(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let inc = inc_ty(k, p);
    let i = k.fvar(G_I);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let a = k.fvar(G_A);
    let b = k.fvar(G_B);
    let c = k.fvar(G_C);
    let false_ty = false_of(k, lg);

    // `∀ l, on A l → on B l → on C l → False`, the hypothesis.
    let no_line_ty = {
        let l = k.fvar(G_L);
        let oal = on_of(k, p, i, a, l);
        let obl = on_of(k, p, i, b, l);
        let ocl = on_of(k, p, i, c, l);
        let t = arrow(k, ocl, false_ty);
        let t = arrow(k, obl, t);
        let t = arrow(k, oal, t);
        pi_over(k, G_L, ln, t)
    };
    let hno = k.fvar(G_H1);

    let pred = collinear_pred(k, lg, p, i, ln, G_M, a, b, c);
    let source = capp(k, p.collinear, &[i, a, b, c]);

    let minor = {
        let l = k.fvar(G_L);
        let oal = on_of(k, p, i, a, l);
        let obl = on_of(k, p, i, b, l);
        let ocl = on_of(k, p, i, c, l);
        let tail_ty = and_of(k, lg, obl, ocl);
        let hyp_ty = and_of(k, lg, oal, tail_ty);
        let h = k.fvar(G_H3);
        let ha = and_left(k, lg, oal, tail_ty, h);
        let tail = and_right(k, lg, oal, tail_ty, h);
        let hb = and_left(k, lg, obl, ocl, tail);
        let hc = and_right(k, lg, obl, ocl, tail);
        let body = app_all(k, hno, &[l, ha, hb, hc]);
        let inner = lam_over(k, G_H3, hyp_ty, body);
        lam_over(k, G_L, ln, inner)
    };

    let h_col = k.fvar(G_H2);
    let motive = lam_over(k, G_H4, source, false_ty);
    let rec = k.const_(lg.exists_rec, vec![l1]);
    let proof = app_all(k, rec, &[ln, pred, motive, minor, h_col]);

    let ty = {
        let t = arrow(k, source, false_ty);
        let t = arrow(k, no_line_ty, t);
        let t = pi_over(k, G_C, pt, t);
        let t = pi_over(k, G_B, pt, t);
        let t = pi_over(k, G_A, pt, t);
        pi_over(k, G_I, inc, t)
    };
    let value = {
        let t = lam_over(k, G_H2, source, proof);
        let t = lam_over(k, G_H1, no_line_ty, t);
        let t = lam_over(k, G_C, pt, t);
        let t = lam_over(k, G_B, pt, t);
        let t = lam_over(k, G_A, pt, t);
        lam_over(k, G_I, inc, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.triangle_not_collinear,
        uparams: vec![],
        ty,
        value,
    })
}
