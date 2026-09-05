//! `Top.Frame` — a **topological carrier built as a frame**, and the open-ball
//! frame of the real line as its first instance.
//!
//! Roadmap W2-21, ADR-1602's recommendation, ADR-1643's measurement.
//!
//! ## Why a frame and not a family of open sets
//!
//! [ADR-1602](../../../docs/research/09-decisions/adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
//! decided that when a topological carrier is finally built it is built
//! **pointfree**: a frame is an *algebraic structure over a carrier*, which is
//! exactly the shape [`declare_record`] already builds nine of, whereas a
//! family of open subsets needs closure under arbitrary unions over an index
//! `Sort` — pushing the record's universe up and putting undecidable
//! membership in a union on the critical path. This module is that decision,
//! executed.
//!
//! ## The record
//!
//! | # | field | type |
//! |---|---|---|
//! | 0 | `carrier` | `Sort 1` |
//! | 1 | `le` | `carrier → carrier → Prop` |
//! | 2 | `leRefl` | `∀ a, le a a` |
//! | 3 | `leTrans` | `∀ a b c, le a b → le b c → le a c` |
//! | 4 | `inf` | `carrier → carrier → carrier` |
//! | 5 | `top` | `carrier` |
//! | 6 | `bot` | `carrier` |
//! | 7 | `sup` | `(Nat → carrier) → carrier` |
//! | 8 | `infLeLeft` | `∀ a b, le (inf a b) a` |
//! | 9 | `infLeRight` | `∀ a b, le (inf a b) b` |
//! | 10 | `leInf` | `∀ a b c, le c a → le c b → le c (inf a b)` |
//! | 11 | `leTop` | `∀ a, le a top` |
//! | 12 | `botLe` | `∀ a, le bot a` |
//! | 13 | `leSup` | `∀ f n, le (f n) (sup f)` |
//! | 14 | `supLe` | `∀ f a, (∀ n, le (f n) a) → le (sup f) a` |
//! | 15 | `frameLe` | `∀ a f, le (inf a (sup f)) (sup (fun n => inf a (f n)))` |
//!
//! ### Three design choices that are not cosmetic
//!
//! **The joins are `Nat`-indexed.** ADR-1612's predicativity constraint says an
//! arbitrary join over a `Sort`-indexed family has to be stated at a fixed
//! universe; a `(I : Sort 1) → (I → carrier) → carrier` field would push the
//! record up and buy nothing here, because the one instance this module builds
//! — the real line — is **second countable**, so every open really is a
//! countable union of basic opens. `Nat` is therefore not a restriction of the
//! ℝ instance, it is a faithful description of it. A genuinely uncountable
//! frame is out of scope and would need a new field shape, not a new law.
//!
//! **The setoid equivalence is DERIVED, not a field.** Every other `AlgS`
//! record carries `equiv` plus three laws plus a congruence field per
//! operation, because on `CReal` the equality is genuinely independent data
//! (ADR-0512). On a *poset* it is not: antisymmetry forces
//! `Equiv a b := le a b ∧ le b a`, and [`TopFramePrelude::equiv_refl`],
//! [`TopFramePrelude::equiv_symm`] and [`TopFramePrelude::equiv_trans`] are
//! then theorems off `leRefl`/`leTrans` rather than obligations an instance has
//! to discharge. That removes four fields and two congruence fields from every
//! future instance. The cost is recorded in ADR-1643: it is zero.
//!
//! **Only ONE direction of the frame distributive law is a field.** The other
//! direction, `sup (fun n => inf a (f n)) ≤ inf a (sup f)`, holds in every
//! complete lattice and is proved here once and for all as
//! [`TopFramePrelude::le_inf_sup`]. [`TopFramePrelude::frame_law`] glues the
//! two into the equivalence a textbook states as the axiom. An instance that
//! had to supply both halves would be supplying a theorem.
//!
//! ## The instance: the open-ball frame of ℝ
//!
//! An **open** is a set of basic balls, and a basic ball is a rational centre
//! `q` together with a radius index `k` standing for `1/(k+1)`. So
//!
//! ```text
//! Top.Opens : Type := Rat → Nat → Prop
//! ```
//!
//! and `inf` is pointwise `And`, `top` is pointwise `True`, `bot` is pointwise
//! `False`, and `sup f` is pointwise `Exists`. The frame law is then
//! distributivity of `∧` over `∃`, which is constructively free.
//!
//! ### Two divergences from the brief, both forced, both measured
//!
//! **`Nat → Bool` cannot carry a countable join.** ADR-1624's `Nat.Subsets`
//! representation makes `inf` a pointwise `Bool.and`, which is why it is the
//! natural first guess; but `sup f i` is `∃ n, f n i`, and that is not a
//! `Bool`. A frame whose carrier is a decidable predicate is not closed under
//! the joins a frame is defined by. The carrier here is therefore `Prop`-valued
//! and `sup` is `Exists`, which needs no re-indexing at all.
//!
//! **No pairing function is used, and none may be.** The brief's route re-indexes
//! a countable union through `Nat.pair`/`Nat.unpairLeft`, which would require
//! the round-trip `unpairLeft (pair a b) = a`. That statement is the content of
//! the family `natural-avg-pair` (`Batteries.Data.Nat.Bisect` +
//! `Mathlib.Data.Nat.Pairing`), registered **held-out** with ten rows in
//! `artifacts/autogenesis/drawn-population-component-census-v1.json`; `Nat.pair`
//! and `Nat.unpairLeft` are declared in this kernel as *constructions only*,
//! with no theorem about either, for exactly that reason (ADR-1060, ADR-1220).
//! Proving the round-trip would spend a blind evaluation population. Indexing a
//! ball by its centre and radius directly — `Rat → Nat → Prop` rather than
//! `Nat → Prop` — removes the need for a pairing, and with it the need for a
//! surjective `Rat.enum : Nat → Rat` that the brief sized as its own commit.
//!
//! ## What connects the frame back to the reals
//!
//! [`TopFramePrelude::mem_ball`] is membership in a basic ball, written as the
//! two-sided rational sandwich `CReal.le x (ofRat (q + 1/(k+1)))` and
//! `CReal.le (ofRat (q − 1/(k+1))) x` — `creal/density.rs`'s own encoding,
//! chosen there so that no `CReal.add`, `CReal.neg` or `CReal.abs` appears in
//! the estimate, and reused here for the same reason.
//!
//! - [`TopFramePrelude::ball_mem_self`] — a ball contains its own centre. The
//!   **non-vacuity** witness: every law below holds of the empty predicate.
//! - [`TopFramePrelude::ball_density`] — every real lies in a ball of every
//!   radius. This is `CReal.density` restated in the frame's vocabulary, and
//!   the restatement type-checks by δβ alone, which is the finding: the reals
//!   prelude's density lemma *is* the covering property of this frame.
//! - [`TopFramePrelude::mem_top`] — the frame's `top` contains every real.
//! - [`TopFramePrelude::mem_open_mono`] — the points-of-an-open assignment is
//!   monotone for the frame's own order.
//! - [`TopFramePrelude::ball_separated`] — **Hausdorff, the half that is
//!   geometry**: two balls whose brackets are strictly separated share no
//!   point. What it does not do is *produce* the separated pair from
//!   `CReal.Apart x y`; see ADR-1643 for that step and its size.

// Same shape and the same suppression as `metric.rs`: `TopFramePrelude` is a
// `Copy` handle carrying the whole `CRealPrelude` plus the record's fixed-size
// selector array, so every `declare_*` below trips
// `large_types_passed_by_value`. These are long, straight-line term
// constructions and the handle is a `Copy` snapshot by design.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::{
    FieldKind, FieldSpec, RecordNames, arrow, declare_record, lam_over, mk_instance, pi_over,
};

#[cfg(test)]
mod top_frame_tests;

// ---------------------------------------------------------------------------
// Field indices. Fixed across the record; index a field through these, never
// with a bare integer.
// ---------------------------------------------------------------------------

/// `Top.Frame.carrier`.
pub const CARRIER: usize = 0;
/// `Top.Frame.le`.
pub const LE: usize = 1;
/// `Top.Frame.leRefl`.
pub const LE_REFL: usize = 2;
/// `Top.Frame.leTrans`.
pub const LE_TRANS: usize = 3;
/// `Top.Frame.inf`.
pub const INF: usize = 4;
/// `Top.Frame.top`.
pub const TOP: usize = 5;
/// `Top.Frame.bot`.
pub const BOT: usize = 6;
/// `Top.Frame.sup`.
pub const SUP: usize = 7;
/// `Top.Frame.infLeLeft`.
pub const INF_LE_LEFT: usize = 8;
/// `Top.Frame.infLeRight`.
pub const INF_LE_RIGHT: usize = 9;
/// `Top.Frame.leInf`.
pub const LE_INF: usize = 10;
/// `Top.Frame.leTop`.
pub const LE_TOP: usize = 11;
/// `Top.Frame.botLe`.
pub const BOT_LE: usize = 12;
/// `Top.Frame.leSup`.
pub const LE_SUP: usize = 13;
/// `Top.Frame.supLe`.
pub const SUP_LE: usize = 14;
/// `Top.Frame.frameLe`.
pub const FRAME_LE: usize = 15;

/// The number of fields the record carries.
pub const FIELD_COUNT: usize = 16;

// Free-variable ids used inside the field-shape closures. Disjoint from
// `structures::CTOR_FVAR_BASE` (10_000), `SELECTOR_S_FV` (10_900) and
// `metric.rs`'s block (20_800..20_805).
const F_A: u64 = 21_800;
const F_B: u64 = 21_801;
const F_C: u64 = 21_802;
const F_F: u64 = 21_803;
const F_N: u64 = 21_804;

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

fn prop_sort(k: &mut Kernel) -> ExprId {
    let l0 = k.level_zero();
    k.sort(l0)
}

fn nat_const(k: &mut Kernel, nat: NameId) -> ExprId {
    k.const_(nat, vec![])
}

// ---------------------------------------------------------------------------
// Field shapes.
// ---------------------------------------------------------------------------

fn carrier_field() -> FieldSpec {
    FieldSpec {
        suffix: "carrier",
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// `carrier -> carrier -> Prop`.
fn le_field() -> FieldSpec {
    FieldSpec {
        suffix: "le",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let prop = prop_sort(k);
            let inner = arrow(k, a, prop);
            arrow(k, a, inner)
        }),
    }
}

/// `forall a, le a a`.
fn le_refl_field() -> FieldSpec {
    FieldSpec {
        suffix: "leRefl",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let a = k.fvar(F_A);
            let body = app_all(k, le, &[a, a]);
            pi_over(k, F_A, ty, body)
        }),
    }
}

/// `forall a b c, le a b -> le b c -> le a c`.
fn le_trans_field() -> FieldSpec {
    FieldSpec {
        suffix: "leTrans",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let c = k.fvar(F_C);
            let ab = app_all(k, le, &[a, b]);
            let bc = app_all(k, le, &[b, c]);
            let ac = app_all(k, le, &[a, c]);
            let inner = arrow(k, bc, ac);
            let imp = arrow(k, ab, inner);
            let t = pi_over(k, F_C, ty, imp);
            let t = pi_over(k, F_B, ty, t);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `carrier -> carrier -> carrier`.
fn inf_field() -> FieldSpec {
    FieldSpec {
        suffix: "inf",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let inner = arrow(k, a, a);
            arrow(k, a, inner)
        }),
    }
}

/// `carrier` — the top element.
fn top_field() -> FieldSpec {
    FieldSpec {
        suffix: "top",
        kind: FieldKind::Data,
        build: Box::new(|_k, _lg, _l1, vals| vals[CARRIER]),
    }
}

/// `carrier` — the bottom element.
fn bot_field() -> FieldSpec {
    FieldSpec {
        suffix: "bot",
        kind: FieldKind::Data,
        build: Box::new(|_k, _lg, _l1, vals| vals[CARRIER]),
    }
}

/// `(Nat -> carrier) -> carrier` — the COUNTABLE join. See the module doc for
/// why the index is `Nat` and not an arbitrary `Sort`.
fn sup_field(nat: NameId) -> FieldSpec {
    FieldSpec {
        suffix: "sup",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let n = nat_const(k, nat);
            let family = arrow(k, n, a);
            arrow(k, family, a)
        }),
    }
}

/// `forall a b, le (inf a b) a` (or `b`, per `right`).
fn inf_le_field(suffix: &'static str, right: bool) -> FieldSpec {
    FieldSpec {
        suffix,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let inf = vals[INF];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let meet = app_all(k, inf, &[a, b]);
            let target = if right { b } else { a };
            let concl = app_all(k, le, &[meet, target]);
            let t = pi_over(k, F_B, ty, concl);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b c, le c a -> le c b -> le c (inf a b)`.
fn le_inf_field() -> FieldSpec {
    FieldSpec {
        suffix: "leInf",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let inf = vals[INF];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let c = k.fvar(F_C);
            let ca = app_all(k, le, &[c, a]);
            let cb = app_all(k, le, &[c, b]);
            let meet = app_all(k, inf, &[a, b]);
            let concl = app_all(k, le, &[c, meet]);
            let inner = arrow(k, cb, concl);
            let imp = arrow(k, ca, inner);
            let t = pi_over(k, F_C, ty, imp);
            let t = pi_over(k, F_B, ty, t);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a, le a top`.
fn le_top_field() -> FieldSpec {
    FieldSpec {
        suffix: "leTop",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let top = vals[TOP];
            let a = k.fvar(F_A);
            let concl = app_all(k, le, &[a, top]);
            pi_over(k, F_A, ty, concl)
        }),
    }
}

/// `forall a, le bot a`.
fn bot_le_field() -> FieldSpec {
    FieldSpec {
        suffix: "botLe",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let bot = vals[BOT];
            let a = k.fvar(F_A);
            let concl = app_all(k, le, &[bot, a]);
            pi_over(k, F_A, ty, concl)
        }),
    }
}

/// `forall (f : Nat -> carrier) (n : Nat), le (f n) (sup f)`.
fn le_sup_field(nat: NameId) -> FieldSpec {
    FieldSpec {
        suffix: "leSup",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let sup = vals[SUP];
            let nat_ty = nat_const(k, nat);
            let family = arrow(k, nat_ty, ty);
            let f = k.fvar(F_F);
            let n = k.fvar(F_N);
            let fn_ = k.app(f, n);
            let join = k.app(sup, f);
            let concl = app_all(k, le, &[fn_, join]);
            let t = pi_over(k, F_N, nat_ty, concl);
            pi_over(k, F_F, family, t)
        }),
    }
}

/// `forall (f : Nat -> carrier) (a : carrier),
/// (forall n, le (f n) a) -> le (sup f) a`.
fn sup_le_field(nat: NameId) -> FieldSpec {
    FieldSpec {
        suffix: "supLe",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let sup = vals[SUP];
            let nat_ty = nat_const(k, nat);
            let family = arrow(k, nat_ty, ty);
            let f = k.fvar(F_F);
            let a = k.fvar(F_A);
            let n = k.fvar(F_N);
            let fn_ = k.app(f, n);
            let pointwise = app_all(k, le, &[fn_, a]);
            let hyp = pi_over(k, F_N, nat_ty, pointwise);
            let join = k.app(sup, f);
            let concl = app_all(k, le, &[join, a]);
            let imp = arrow(k, hyp, concl);
            let t = pi_over(k, F_A, ty, imp);
            pi_over(k, F_F, family, t)
        }),
    }
}

/// `forall (a : carrier) (f : Nat -> carrier),
/// le (inf a (sup f)) (sup (fun n => inf a (f n)))` — **the frame law**, one
/// direction only. The converse is a theorem in every complete lattice; see
/// the module doc.
fn frame_le_field(nat: NameId) -> FieldSpec {
    FieldSpec {
        suffix: "frameLe",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[LE];
            let inf = vals[INF];
            let sup = vals[SUP];
            let nat_ty = nat_const(k, nat);
            let family = arrow(k, nat_ty, ty);
            let a = k.fvar(F_A);
            let f = k.fvar(F_F);
            let join = k.app(sup, f);
            let lhs = app_all(k, inf, &[a, join]);
            let rhs = {
                let n = k.fvar(F_N);
                let fn_ = k.app(f, n);
                let body = app_all(k, inf, &[a, fn_]);
                let lam = lam_over(k, F_N, nat_ty, body);
                k.app(sup, lam)
            };
            let concl = app_all(k, le, &[lhs, rhs]);
            let t = pi_over(k, F_F, family, concl);
            pi_over(k, F_A, ty, t)
        }),
    }
}

fn frame_fields(nat: NameId) -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        le_field(),
        le_refl_field(),
        le_trans_field(),
        inf_field(),
        top_field(),
        bot_field(),
        sup_field(nat),
        inf_le_field("infLeLeft", false),
        inf_le_field("infLeRight", true),
        le_inf_field(),
        le_top_field(),
        bot_le_field(),
        le_sup_field(nat),
        sup_le_field(nat),
        frame_le_field(nat),
    ]
}

// ---------------------------------------------------------------------------
// The prelude handle.
// ---------------------------------------------------------------------------

/// The interned names produced by [`build_top_frame_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TopFramePrelude {
    /// The reals this module's one instance is built over.
    pub creal: CRealPrelude,
    /// The `Top.Frame` record: its inductive, `mk`, `rec` and sixteen
    /// selectors.
    pub record: RecordNames,

    // --- derived, generic in the frame -------------------------------------
    /// `Top.Frame.Equiv : (F : Top.Frame) → F.carrier → F.carrier → Prop`
    /// `:= fun F a b => And (F.le a b) (F.le b a)`. Antisymmetry AS the
    /// setoid equality; see the module doc for why it is not a field.
    pub equiv: NameId,
    /// `Top.Frame.equiv_refl : ∀ F a, Top.Frame.Equiv F a a`.
    pub equiv_refl: NameId,
    /// `Top.Frame.equiv_symm : ∀ F a b, Equiv F a b → Equiv F b a`.
    pub equiv_symm: NameId,
    /// `Top.Frame.equiv_trans : ∀ F a b c, Equiv F a b → Equiv F b c →
    /// Equiv F a c`.
    pub equiv_trans: NameId,
    /// `Top.Frame.sup_mono : ∀ F f g, (∀ n, F.le (f n) (g n)) →
    /// F.le (F.sup f) (F.sup g)`.
    pub sup_mono: NameId,
    /// `Top.Frame.sup_const : ∀ F a, Equiv F (F.sup (fun _ => a)) a` — the
    /// join of a constant family. The `≤` half needs a `Nat` to evaluate the
    /// family at, which is where the countability of the index shows up as
    /// something other than a restriction.
    pub sup_const: NameId,
    /// `Top.Frame.le_inf_sup : ∀ F a f,
    /// F.le (F.sup (fun n => F.inf a (f n))) (F.inf a (F.sup f))` — the
    /// direction of the frame law that is NOT an axiom.
    pub le_inf_sup: NameId,
    /// `Top.Frame.frame_law : ∀ F a f,
    /// Equiv F (F.inf a (F.sup f)) (F.sup (fun n => F.inf a (f n)))` — the
    /// distributive law as the textbook states it, both directions.
    pub frame_law: NameId,
    /// `Top.Frame.inf_comm : ∀ F a b, Equiv F (F.inf a b) (F.inf b a)`.
    pub inf_comm: NameId,

    // --- the open-ball frame of ℝ ------------------------------------------
    /// `Top.Opens : Type := Rat → Nat → Prop` — an open is a set of basic
    /// balls; a basic ball is a rational centre and a radius index `k`
    /// standing for `1/(k+1)`.
    pub opens: NameId,
    /// `Top.Opens.le : Top.Opens → Top.Opens → Prop`.
    pub opens_le: NameId,
    /// `Top.Opens.inf : Top.Opens → Top.Opens → Top.Opens` — pointwise `And`.
    pub opens_inf: NameId,
    /// `Top.Opens.top : Top.Opens` — pointwise `True`.
    pub opens_top: NameId,
    /// `Top.Opens.bot : Top.Opens` — pointwise `False`.
    pub opens_bot: NameId,
    /// `Top.Opens.sup : (Nat → Top.Opens) → Top.Opens` — pointwise `Exists`.
    pub opens_sup: NameId,
    /// `Top.Opens.le_refl`.
    pub opens_le_refl: NameId,
    /// `Top.Opens.le_trans`.
    pub opens_le_trans: NameId,
    /// `Top.Opens.inf_le_left`.
    pub opens_inf_le_left: NameId,
    /// `Top.Opens.inf_le_right`.
    pub opens_inf_le_right: NameId,
    /// `Top.Opens.le_inf`.
    pub opens_le_inf: NameId,
    /// `Top.Opens.le_top`.
    pub opens_le_top: NameId,
    /// `Top.Opens.bot_le`.
    pub opens_bot_le: NameId,
    /// `Top.Opens.le_sup`.
    pub opens_le_sup: NameId,
    /// `Top.Opens.sup_le`.
    pub opens_sup_le: NameId,
    /// `Top.Opens.frame_le` — distributivity of `And` over `Exists`.
    pub opens_frame_le: NameId,
    /// `Top.ballFrame : Top.Frame` — **the instance**.
    pub ball_frame: NameId,
    /// `Top.ballFrame_inf : ∀ s t,
    /// Eq Top.Opens (Top.Frame.inf Top.ballFrame s t) (Top.Opens.inf s t)` —
    /// proved by `Eq.refl`, so its admission IS the statement that the record
    /// selector reduces definitionally on the instance. The `AlgS` spine's
    /// reduction probe, transplanted; it uses SYMBOLIC arguments because
    /// ADR-1602 §5 measured that a concrete probe on a computing carrier is
    /// vacuous.
    pub ball_frame_inf: NameId,

    // --- the frame's points ------------------------------------------------
    /// `Top.MemBall : CReal → Rat → Nat → Prop` — the two-sided rational
    /// sandwich, `creal/density.rs`'s own encoding.
    pub mem_ball: NameId,
    /// `Top.MemOpen : CReal → Top.Opens → Prop` — `x` lies in some ball the
    /// open contains.
    pub mem_open: NameId,
    /// `Top.ball_mem_self : ∀ q k, Top.MemBall (CReal.ofRat q) q k` — the
    /// **non-vacuity** witness for [`Self::mem_ball`].
    pub ball_mem_self: NameId,
    /// `Top.ball_density : ∀ x k, ∃ q, Top.MemBall x q k`.
    pub ball_density: NameId,
    /// `Top.mem_top : ∀ x, Top.MemOpen x Top.Opens.top`.
    pub mem_top: NameId,
    /// `Top.mem_open_mono : ∀ x s t, Top.Opens.le s t → Top.MemOpen x s →
    /// Top.MemOpen x t`.
    pub mem_open_mono: NameId,
    /// `Top.ball_separated : ∀ q r k m,
    /// CReal.lt (ofRat (q + 1/(k+1))) (ofRat (r − 1/(m+1))) →
    /// ∀ z, Top.MemBall z q k → Top.MemBall z r m → False`.
    pub ball_separated: NameId,
}

// ---------------------------------------------------------------------------
// Name interning.
// ---------------------------------------------------------------------------

/// The record's field suffixes, in declaration order. Used both to build the
/// record and to re-intern its selectors on the already-declared path.
const FIELD_SUFFIXES: [&str; FIELD_COUNT] = [
    "carrier",
    "le",
    "leRefl",
    "leTrans",
    "inf",
    "top",
    "bot",
    "sup",
    "infLeLeft",
    "infLeRight",
    "leInf",
    "leTop",
    "botLe",
    "leSup",
    "supLe",
    "frameLe",
];

fn intern(kernel: &mut Kernel, creal: CRealPrelude) -> TopFramePrelude {
    let root = kernel.anon();
    let top = kernel.name_str(root, "Top");
    let frame = kernel.name_str(top, "Frame");
    let opens = kernel.name_str(top, "Opens");

    let mk = kernel.name_str(frame, "mk");
    let rec = kernel.name_str(frame, "rec");
    let mut selectors = [mk; crate::nat_prelude::structures::MAX_FIELDS];
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        selectors[i] = kernel.name_str(frame, *suffix);
    }
    let record = RecordNames {
        ind: frame,
        mk,
        rec,
        selectors,
        len: FIELD_COUNT,
    };

    TopFramePrelude {
        creal,
        record,
        equiv: kernel.name_str(frame, "Equiv"),
        equiv_refl: kernel.name_str(frame, "equiv_refl"),
        equiv_symm: kernel.name_str(frame, "equiv_symm"),
        equiv_trans: kernel.name_str(frame, "equiv_trans"),
        sup_mono: kernel.name_str(frame, "sup_mono"),
        sup_const: kernel.name_str(frame, "sup_const"),
        le_inf_sup: kernel.name_str(frame, "le_inf_sup"),
        frame_law: kernel.name_str(frame, "frame_law"),
        inf_comm: kernel.name_str(frame, "inf_comm"),
        opens,
        opens_le: kernel.name_str(opens, "le"),
        opens_inf: kernel.name_str(opens, "inf"),
        opens_top: kernel.name_str(opens, "top"),
        opens_bot: kernel.name_str(opens, "bot"),
        opens_sup: kernel.name_str(opens, "sup"),
        opens_le_refl: kernel.name_str(opens, "le_refl"),
        opens_le_trans: kernel.name_str(opens, "le_trans"),
        opens_inf_le_left: kernel.name_str(opens, "inf_le_left"),
        opens_inf_le_right: kernel.name_str(opens, "inf_le_right"),
        opens_le_inf: kernel.name_str(opens, "le_inf"),
        opens_le_top: kernel.name_str(opens, "le_top"),
        opens_bot_le: kernel.name_str(opens, "bot_le"),
        opens_le_sup: kernel.name_str(opens, "le_sup"),
        opens_sup_le: kernel.name_str(opens, "sup_le"),
        opens_frame_le: kernel.name_str(opens, "frame_le"),
        ball_frame: kernel.name_str(top, "ballFrame"),
        ball_frame_inf: kernel.name_str(top, "ballFrame_inf"),
        mem_ball: kernel.name_str(top, "MemBall"),
        mem_open: kernel.name_str(top, "MemOpen"),
        ball_mem_self: kernel.name_str(top, "ball_mem_self"),
        ball_density: kernel.name_str(top, "ball_density"),
        mem_top: kernel.name_str(top, "mem_top"),
        mem_open_mono: kernel.name_str(top, "mem_open_mono"),
        ball_separated: kernel.name_str(top, "ball_separated"),
    }
}

/// Build (or return, if already built) the `Top.*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics if the field-shape list has drifted from [`FIELD_COUNT`], or if
/// [`declare_record`] returns selectors under names other than the ones
/// `intern` pre-computed. Both are internal-consistency assertions between
/// this file's two descriptions of the same record.
pub fn build_top_frame_prelude(kernel: &mut Kernel) -> Result<TopFramePrelude, KernelError> {
    let creal = crate::build_creal_prelude(kernel)?;
    let p = intern(kernel, creal);
    if kernel.environment().get(p.record.ind).is_some() {
        return Ok(p);
    }

    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);
    let logic = creal.rat.int.logic;
    let nat = creal.rat.int.nat.nat;
    let specs = frame_fields(nat);
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

    let mut d = IntDev::new(kernel, creal.rat.int);
    declare_equiv(&mut d, p)?;
    declare_equiv_refl(&mut d, p)?;
    declare_equiv_symm(&mut d, p)?;
    declare_equiv_trans(&mut d, p)?;
    declare_sup_mono(&mut d, p)?;
    declare_sup_const(&mut d, p)?;
    declare_le_inf_sup(&mut d, p)?;
    declare_frame_law(&mut d, p)?;
    declare_inf_comm(&mut d, p)?;

    declare_opens(&mut d, p)?;
    declare_opens_le(&mut d, p)?;
    declare_opens_inf(&mut d, p)?;
    declare_opens_top(&mut d, p)?;
    declare_opens_bot(&mut d, p)?;
    declare_opens_sup(&mut d, p)?;
    declare_opens_le_refl(&mut d, p)?;
    declare_opens_le_trans(&mut d, p)?;
    declare_opens_inf_le(&mut d, p, false)?;
    declare_opens_inf_le(&mut d, p, true)?;
    declare_opens_le_inf(&mut d, p)?;
    declare_opens_le_top(&mut d, p)?;
    declare_opens_bot_le(&mut d, p)?;
    declare_opens_le_sup(&mut d, p)?;
    declare_opens_sup_le(&mut d, p)?;
    declare_opens_frame_le(&mut d, p)?;
    declare_ball_frame(&mut d, p)?;
    declare_ball_frame_inf(&mut d, p)?;

    declare_mem_ball(&mut d, p)?;
    declare_mem_open(&mut d, p)?;
    declare_ball_mem_self(&mut d, p)?;
    declare_ball_density(&mut d, p)?;
    declare_mem_top(&mut d, p)?;
    declare_mem_open_mono(&mut d, p)?;
    declare_ball_separated(&mut d, p)?;

    Ok(p)
}

// ---------------------------------------------------------------------------
// Small helpers over a frame.
// ---------------------------------------------------------------------------

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

fn definition(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// A frame variable `F`, its carrier, and the family type `Nat → F.carrier`.
struct Generic {
    frame_ty: ExprId,
    f_fv: u64,
    frame: ExprId,
    carrier: ExprId,
    family: ExprId,
}

fn generic(d: &mut IntDev<'_>, p: TopFramePrelude) -> Generic {
    let frame_ty = d.kernel().const_(p.record.ind, vec![]);
    let f_fv = d.fresh_fvar();
    let frame = d.kernel().fvar(f_fv);
    let s = d.kernel().const_(p.record.sel(CARRIER), vec![]);
    let carrier = d.apply(s, &[frame]);
    let nat = d.nat_ty();
    let family = d.arrow(nat, carrier);
    Generic {
        frame_ty,
        f_fv,
        frame,
        carrier,
        family,
    }
}

fn field(d: &mut IntDev<'_>, p: TopFramePrelude, frame: ExprId, i: usize) -> ExprId {
    let s = d.kernel().const_(p.record.sel(i), vec![]);
    d.apply(s, &[frame])
}

/// `F.le a b`.
fn fle(d: &mut IntDev<'_>, p: TopFramePrelude, frame: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let le = field(d, p, frame, LE);
    d.apply(le, &[a, b])
}

/// `Top.Frame.Equiv F a b`.
fn fequiv(d: &mut IntDev<'_>, p: TopFramePrelude, frame: ExprId, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.equiv, &[frame, a, b])
}

/// `And.intro left right lp rp`.
fn and_intro(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.creal.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

// ---------------------------------------------------------------------------
// Derived, generic in the frame.
// ---------------------------------------------------------------------------

/// `Top.Frame.Equiv F a b := And (F.le a b) (F.le b a)`.
fn declare_equiv(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ab = fle(d, p, g.frame, a, b);
    let ba = fle(d, p, g.frame, b, a);
    let body = d.and(ab, ba);
    let value = {
        let t = d.lam_fv(b_fv, g.carrier, body);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.carrier, prop);
        let t = d.arrow(g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    definition(d, p.equiv, ty, value)
}

/// `Top.Frame.equiv_refl : ∀ F a, Equiv F a a`.
fn declare_equiv_refl(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let refl = field(d, p, g.frame, LE_REFL);
    let h = d.apply(refl, &[a]);
    let aa = fle(d, p, g.frame, a, a);
    let body = and_intro(d, p, aa, aa, h, h);

    let value = {
        let t = d.lam_fv(a_fv, g.carrier, body);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, a, a);
        let t = d.pi_fv(a_fv, g.carrier, concl);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.equiv_refl, ty, value)
}

/// `Top.Frame.equiv_symm : ∀ F a b, Equiv F a b → Equiv F b a`.
fn declare_equiv_symm(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ab = fle(d, p, g.frame, a, b);
    let ba = fle(d, p, g.frame, b, a);
    let hyp = fequiv(d, p, g.frame, a, b);
    let left = d.and_left(ab, ba, h);
    let right = d.and_right(ab, ba, h);
    let body = and_intro(d, p, ba, ab, right, left);

    let value = {
        let t = d.lam_fv(h_fv, hyp, body);
        let t = d.lam_fv(b_fv, g.carrier, t);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, b, a);
        let imp = d.arrow(hyp, concl);
        let t = d.pi_fv(b_fv, g.carrier, imp);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.equiv_symm, ty, value)
}

/// `Top.Frame.equiv_trans : ∀ F a b c, Equiv F a b → Equiv F b c →
/// Equiv F a c`.
fn declare_equiv_trans(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let ab = fle(d, p, g.frame, a, b);
    let ba = fle(d, p, g.frame, b, a);
    let bc = fle(d, p, g.frame, b, c);
    let cb = fle(d, p, g.frame, c, b);
    let ac = fle(d, p, g.frame, a, c);
    let ca = fle(d, p, g.frame, c, a);
    let hyp1 = fequiv(d, p, g.frame, a, b);
    let hyp2 = fequiv(d, p, g.frame, b, c);

    let trans = field(d, p, g.frame, LE_TRANS);
    let h_ab = d.and_left(ab, ba, h1);
    let h_ba = d.and_right(ab, ba, h1);
    let h_bc = d.and_left(bc, cb, h2);
    let h_cb = d.and_right(bc, cb, h2);
    let forward = d.apply(trans, &[a, b, c, h_ab, h_bc]);
    let backward = d.apply(trans, &[c, b, a, h_cb, h_ba]);
    let body = and_intro(d, p, ac, ca, forward, backward);

    let value = {
        let t = d.lam_fv(h2_fv, hyp2, body);
        let t = d.lam_fv(h1_fv, hyp1, t);
        let t = d.lam_fv(c_fv, g.carrier, t);
        let t = d.lam_fv(b_fv, g.carrier, t);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, a, c);
        let inner = d.arrow(hyp2, concl);
        let imp = d.arrow(hyp1, inner);
        let t = d.pi_fv(c_fv, g.carrier, imp);
        let t = d.pi_fv(b_fv, g.carrier, t);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.equiv_trans, ty, value)
}

/// `Top.Frame.sup_mono : ∀ F f g, (∀ n, F.le (f n) (g n)) →
/// F.le (F.sup f) (F.sup g)`.
fn declare_sup_mono(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = d.nat_ty();
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let gg_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(gg_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sup = field(d, p, g.frame, SUP);
    let sup_f = d.apply(sup, &[f]);
    let sup_g = d.apply(sup, &[gg]);

    let hyp = {
        let fn_ = d.apply(f, &[n]);
        let gn = d.apply(gg, &[n]);
        let pointwise = fle(d, p, g.frame, fn_, gn);
        d.pi_fv(n_fv, nat, pointwise)
    };

    // minor : ∀ n, F.le (f n) (F.sup g), by leTrans through `g n`.
    let minor = {
        let fn_ = d.apply(f, &[n]);
        let gn = d.apply(gg, &[n]);
        let hn = d.apply(h, &[n]);
        let le_sup = field(d, p, g.frame, LE_SUP);
        let step = d.apply(le_sup, &[gg, n]);
        let trans = field(d, p, g.frame, LE_TRANS);
        let body = d.apply(trans, &[fn_, gn, sup_g, hn, step]);
        d.lam_fv(n_fv, nat, body)
    };
    let sup_le = field(d, p, g.frame, SUP_LE);
    let body = d.apply(sup_le, &[f, sup_g, minor]);

    let value = {
        let t = d.lam_fv(h_fv, hyp, body);
        let t = d.lam_fv(gg_fv, g.family, t);
        let t = d.lam_fv(f_fv, g.family, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fle(d, p, g.frame, sup_f, sup_g);
        let imp = d.arrow(hyp, concl);
        let t = d.pi_fv(gg_fv, g.family, imp);
        let t = d.pi_fv(f_fv, g.family, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.sup_mono, ty, value)
}

/// `Top.Frame.sup_const : ∀ F a, Equiv F (F.sup (fun _ => a)) a`.
fn declare_sup_const(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();

    let constant = {
        let dummy = d.kernel().fvar(n_fv);
        let _ = dummy;
        d.lam_fv(n_fv, nat, a)
    };
    let sup = field(d, p, g.frame, SUP);
    let join = d.apply(sup, &[constant]);

    // `F.sup (fun _ => a) ≤ a` — supLe at the pointwise `leRefl`.
    let down = {
        let refl = field(d, p, g.frame, LE_REFL);
        let ra = d.apply(refl, &[a]);
        let minor = d.lam_fv(n_fv, nat, ra);
        let sup_le = field(d, p, g.frame, SUP_LE);
        d.apply(sup_le, &[constant, a, minor])
    };
    // `a ≤ F.sup (fun _ => a)` — leSup at index `0`. THE COUNTABLE INDEX HAS
    // TO BE INHABITED for this half; `Nat.zero` is the witness.
    let up = {
        let zero = d.zero();
        let le_sup = field(d, p, g.frame, LE_SUP);
        d.apply(le_sup, &[constant, zero])
    };

    let join_le_a = fle(d, p, g.frame, join, a);
    let a_le_join = fle(d, p, g.frame, a, join);
    let body = and_intro(d, p, join_le_a, a_le_join, down, up);

    let value = {
        let t = d.lam_fv(a_fv, g.carrier, body);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, join, a);
        let t = d.pi_fv(a_fv, g.carrier, concl);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.sup_const, ty, value)
}

/// The term `F.sup (fun n => F.inf a (f n))`, shared by [`declare_le_inf_sup`]
/// and [`declare_frame_law`].
fn meet_join(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    frame: ExprId,
    a: ExprId,
    f: ExprId,
    n_fv: u64,
) -> ExprId {
    let nat = d.nat_ty();
    let n = d.kernel().fvar(n_fv);
    let fn_ = d.apply(f, &[n]);
    let inf = field(d, p, frame, INF);
    let body = d.apply(inf, &[a, fn_]);
    let lam = d.lam_fv(n_fv, nat, body);
    let sup = field(d, p, frame, SUP);
    d.apply(sup, &[lam])
}

/// `Top.Frame.le_inf_sup : ∀ F a f,
/// F.le (F.sup (fun n => F.inf a (f n))) (F.inf a (F.sup f))`.
///
/// The direction of the frame law that is NOT an axiom: it holds in every
/// complete lattice, off the two universal properties alone.
fn declare_le_inf_sup(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sup = field(d, p, g.frame, SUP);
    let sup_f = d.apply(sup, &[f]);
    let inf = field(d, p, g.frame, INF);
    let meet = d.apply(inf, &[a, sup_f]);
    let lhs = meet_join(d, p, g.frame, a, f, n_fv);

    // The family `fun n => F.inf a (f n)`, which both `supLe` uses take.
    let meet_family = {
        let fn2 = d.apply(f, &[n]);
        let inf2 = field(d, p, g.frame, INF);
        let body = d.apply(inf2, &[a, fn2]);
        d.lam_fv(n_fv, nat, body)
    };

    // `lhs ≤ a` — supLe at infLeLeft.
    let to_a = {
        let fn_ = d.apply(f, &[n]);
        let ill = field(d, p, g.frame, INF_LE_LEFT);
        let step = d.apply(ill, &[a, fn_]);
        let minor = d.lam_fv(n_fv, nat, step);
        let sup_le = field(d, p, g.frame, SUP_LE);
        d.apply(sup_le, &[meet_family, a, minor])
    };
    // `lhs ≤ F.sup f` — supLe at (infLeRight then leSup).
    let to_sup = {
        let fn_ = d.apply(f, &[n]);
        let ilr = field(d, p, g.frame, INF_LE_RIGHT);
        let inf3 = field(d, p, g.frame, INF);
        let meet_n = d.apply(inf3, &[a, fn_]);
        let step1 = d.apply(ilr, &[a, fn_]);
        let le_sup = field(d, p, g.frame, LE_SUP);
        let step2 = d.apply(le_sup, &[f, n]);
        let trans = field(d, p, g.frame, LE_TRANS);
        let chained = d.apply(trans, &[meet_n, fn_, sup_f, step1, step2]);
        let minor = d.lam_fv(n_fv, nat, chained);
        let sup_le = field(d, p, g.frame, SUP_LE);
        d.apply(sup_le, &[meet_family, sup_f, minor])
    };
    let le_inf = field(d, p, g.frame, LE_INF);
    let body = d.apply(le_inf, &[a, sup_f, lhs, to_a, to_sup]);

    let value = {
        let t = d.lam_fv(f_fv, g.family, body);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fle(d, p, g.frame, lhs, meet);
        let t = d.pi_fv(f_fv, g.family, concl);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.le_inf_sup, ty, value)
}

/// `Top.Frame.frame_law : ∀ F a f,
/// Equiv F (F.inf a (F.sup f)) (F.sup (fun n => F.inf a (f n)))`.
fn declare_frame_law(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();

    let sup = field(d, p, g.frame, SUP);
    let sup_f = d.apply(sup, &[f]);
    let inf = field(d, p, g.frame, INF);
    let meet = d.apply(inf, &[a, sup_f]);
    let joined = meet_join(d, p, g.frame, a, f, n_fv);

    let frame_le = field(d, p, g.frame, FRAME_LE);
    let forward = d.apply(frame_le, &[a, f]);
    let backward = d.lemma(p.le_inf_sup, &[g.frame, a, f]);
    let fwd_stmt = fle(d, p, g.frame, meet, joined);
    let bwd_stmt = fle(d, p, g.frame, joined, meet);
    let body = and_intro(d, p, fwd_stmt, bwd_stmt, forward, backward);

    let value = {
        let t = d.lam_fv(f_fv, g.family, body);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, meet, joined);
        let t = d.pi_fv(f_fv, g.family, concl);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.frame_law, ty, value)
}

/// `F.le (F.inf x y) (F.inf y x)` — `leInf` fed the two projections crossed.
fn inf_comm_side(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    frame: ExprId,
    x: ExprId,
    y: ExprId,
    meet: ExprId,
) -> ExprId {
    let ill = field(d, p, frame, INF_LE_LEFT);
    let ilr = field(d, p, frame, INF_LE_RIGHT);
    let to_x = d.apply(ill, &[x, y]);
    let to_y = d.apply(ilr, &[x, y]);
    let le_inf = field(d, p, frame, LE_INF);
    d.apply(le_inf, &[y, x, meet, to_y, to_x])
}

/// `Top.Frame.inf_comm : ∀ F a b, Equiv F (F.inf a b) (F.inf b a)`.
fn declare_inf_comm(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let inf = field(d, p, g.frame, INF);
    let ab = d.apply(inf, &[a, b]);
    let ba = d.apply(inf, &[b, a]);

    let forward = inf_comm_side(d, p, g.frame, a, b, ab);
    let backward = inf_comm_side(d, p, g.frame, b, a, ba);

    let fwd_stmt = fle(d, p, g.frame, ab, ba);
    let bwd_stmt = fle(d, p, g.frame, ba, ab);
    let body = and_intro(d, p, fwd_stmt, bwd_stmt, forward, backward);

    let value = {
        let t = d.lam_fv(b_fv, g.carrier, body);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.f_fv, g.frame_ty, t)
    };
    let ty = {
        let concl = fequiv(d, p, g.frame, ab, ba);
        let t = d.pi_fv(b_fv, g.carrier, concl);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.f_fv, g.frame_ty, t)
    };
    theorem(d, p.inf_comm, ty, value)
}

// ---------------------------------------------------------------------------
// The open-ball frame of ℝ.
//
// An open is a set of basic balls; a basic ball is a rational centre `q` and a
// radius index `k` standing for `1/(k+1)`. So the carrier is `Rat → Nat → Prop`
// and every operation is pointwise. See the module doc for why the carrier is
// `Prop`-valued (a `Nat → Bool` predicate is not closed under countable joins)
// and why no pairing function appears (the round-trip is held-out).
// ---------------------------------------------------------------------------

/// `Rat`.
fn rat_ty(d: &mut IntDev<'_>, p: TopFramePrelude) -> ExprId {
    let n = p.creal.rat.int.rat;
    d.kernel().const_(n, vec![])
}

/// `Top.Opens`.
fn opens_ty(d: &mut IntDev<'_>, p: TopFramePrelude) -> ExprId {
    d.kernel().const_(p.opens, vec![])
}

/// `Top.Opens.le s t`.
fn ole(d: &mut IntDev<'_>, p: TopFramePrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.opens_le, &[s, t])
}

/// `Rat.natDivSucc 1 k` — the radius `1/(k+1)`. The `+1` is inside
/// `Rat.natDivSucc`'s own definition, which is what makes the radius
/// **total**: there is no index at which it divides by zero.
fn radius(d: &mut IntDev<'_>, p: TopFramePrelude, k: ExprId) -> ExprId {
    let one = d.num(1);
    let n = p.creal.rat.nat_div_succ;
    d.const_app(n, &[one, k])
}

/// `CReal.ofRat q`.
fn embed(d: &mut IntDev<'_>, p: TopFramePrelude, q: ExprId) -> ExprId {
    let n = p.creal.of_rat;
    d.const_app(n, &[q])
}

/// `CReal.le x y`.
fn cle(d: &mut IntDev<'_>, p: TopFramePrelude, x: ExprId, y: ExprId) -> ExprId {
    let n = p.creal.le;
    d.const_app(n, &[x, y])
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: TopFramePrelude) -> ExprId {
    let n = p.creal.creal;
    d.kernel().const_(n, vec![])
}

/// `Exists.{1} ty predicate`.
fn exists_at(d: &mut IntDev<'_>, p: TopFramePrelude, ty: ExprId, predicate: ExprId) -> ExprId {
    let one = d.level_one();
    let n = p.creal.rat.int.logic.exists_;
    let c = d.kernel().const_(n, vec![one]);
    d.apply(c, &[ty, predicate])
}

/// `Exists.intro.{1} ty predicate witness proof`.
fn exists_intro_at(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    ty: ExprId,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let n = p.creal.rat.int.logic.exists_intro;
    let c = d.kernel().const_(n, vec![one]);
    d.apply(c, &[ty, predicate, witness, proof])
}

/// `Exists.rec.{1}` at an arbitrary `Sort 1`-valued quantified type. The
/// `int_prelude::ops::exists_elim` this mirrors is hardwired to `Nat`; `Rat` is
/// the other carrier this module quantifies over.
fn exists_elim_at(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let ex = exists_at(d, p, ty, predicate);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, ex, target)
    };
    let n = p.creal.rat.int.logic.exists_rec;
    let c = d.kernel().const_(n, vec![one]);
    d.apply(c, &[ty, predicate, motive, minor, witness])
}

/// `Top.Opens : Type := Rat → Nat → Prop`.
fn declare_opens(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let inner = d.arrow(nat, prop);
    let value = d.arrow(rat, inner);
    let one = d.level_one();
    let ty = d.kernel().sort(one);
    definition(d, p.opens, ty, value)
}

/// `Top.Opens.le s t := ∀ q k, s q k → t q k`.
fn declare_opens_le(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let sqk = d.apply(s, &[q, k]);
    let tqk = d.apply(t, &[q, k]);
    let imp = d.arrow(sqk, tqk);
    let body = {
        let over_k = d.pi_fv(k_fv, nat, imp);
        d.pi_fv(q_fv, rat, over_k)
    };
    let value = {
        let inner = d.lam_fv(t_fv, opens, body);
        d.lam_fv(s_fv, opens, inner)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let inner = d.arrow(opens, prop);
        d.arrow(opens, inner)
    };
    definition(d, p.opens_le, ty, value)
}

/// `Top.Opens.inf s t := fun q k => And (s q k) (t q k)`.
fn declare_opens_inf(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let sqk = d.apply(s, &[q, k]);
    let tqk = d.apply(t, &[q, k]);
    let conj = d.and(sqk, tqk);
    let value = {
        let over_k = d.lam_fv(k_fv, nat, conj);
        let over_q = d.lam_fv(q_fv, rat, over_k);
        let inner = d.lam_fv(t_fv, opens, over_q);
        d.lam_fv(s_fv, opens, inner)
    };
    let ty = {
        let inner = d.arrow(opens, opens);
        d.arrow(opens, inner)
    };
    definition(d, p.opens_inf, ty, value)
}

/// `Top.Opens.top := fun q k => True` / `Top.Opens.bot := fun q k => False`.
fn declare_opens_const(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    name: NameId,
    body: ExprId,
) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let value = {
        let over_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(q_fv, rat, over_k)
    };
    definition(d, name, opens, value)
}

fn declare_opens_top(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let body = d.true_ty();
    declare_opens_const(d, p, p.opens_top, body)
}

fn declare_opens_bot(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let body = d.false_ty();
    declare_opens_const(d, p, p.opens_bot, body)
}

/// `Top.Opens.sup f := fun q k => ∃ n, f n q k` — the countable join, as an
/// `Exists` and NOT as a re-indexed enumeration. See the module doc.
fn declare_opens_sup(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let family = d.arrow(nat, opens);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let fnqk = d.apply(f, &[n, q, k]);
    let predicate = d.lam_fv(n_fv, nat, fnqk);
    let body = exists_at(d, p, nat, predicate);
    let value = {
        let over_k = d.lam_fv(k_fv, nat, body);
        let over_q = d.lam_fv(q_fv, rat, over_k);
        d.lam_fv(f_fv, family, over_q)
    };
    let ty = d.arrow(family, opens);
    definition(d, p.opens_sup, ty, value)
}

/// The two binders `(q : Rat) (k : Nat)` every `Top.Opens.le` proof opens with.
struct PointArgs {
    q_fv: u64,
    q: ExprId,
    k_fv: u64,
    k: ExprId,
}

fn point_args(d: &mut IntDev<'_>) -> PointArgs {
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    PointArgs { q_fv, q, k_fv, k }
}

/// Close `body` under `fun (q : Rat) (k : Nat) (h : hyp) => …`.
fn close_point(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    pa: &PointArgs,
    h_fv: u64,
    hyp: ExprId,
    body: ExprId,
) -> ExprId {
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let t = d.lam_fv(h_fv, hyp, body);
    let t = d.lam_fv(pa.k_fv, nat, t);
    d.lam_fv(pa.q_fv, rat, t)
}

/// `Top.Opens.le_refl : ∀ s, Top.Opens.le s s`.
fn declare_opens_le_refl(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let sqk = d.apply(s, &[pa.q, pa.k]);

    let inner = close_point(d, p, &pa, h_fv, sqk, h);
    let value = d.lam_fv(s_fv, opens, inner);
    let ty = {
        let concl = ole(d, p, s, s);
        d.pi_fv(s_fv, opens, concl)
    };
    theorem(d, p.opens_le_refl, ty, value)
}

/// `Top.Opens.le_trans : ∀ s t u, le s t → le t u → le s u`.
fn declare_opens_le_trans(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp1 = ole(d, p, s, t);
    let hyp2 = ole(d, p, t, u);
    let sqk = d.apply(s, &[pa.q, pa.k]);
    let step = d.apply(h1, &[pa.q, pa.k, h]);
    let body = d.apply(h2, &[pa.q, pa.k, step]);

    let inner = close_point(d, p, &pa, h_fv, sqk, body);
    let value = {
        let t2 = d.lam_fv(h2_fv, hyp2, inner);
        let t2 = d.lam_fv(h1_fv, hyp1, t2);
        let t2 = d.lam_fv(u_fv, opens, t2);
        let t2 = d.lam_fv(t_fv, opens, t2);
        d.lam_fv(s_fv, opens, t2)
    };
    let ty = {
        let concl = ole(d, p, s, u);
        let i = d.arrow(hyp2, concl);
        let i = d.arrow(hyp1, i);
        let i = d.pi_fv(u_fv, opens, i);
        let i = d.pi_fv(t_fv, opens, i);
        d.pi_fv(s_fv, opens, i)
    };
    theorem(d, p.opens_le_trans, ty, value)
}

/// `Top.Opens.inf_le_left/right : ∀ s t, le (inf s t) s` (resp. `t`).
fn declare_opens_inf_le(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    right: bool,
) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sqk = d.apply(s, &[pa.q, pa.k]);
    let tqk = d.apply(t, &[pa.q, pa.k]);
    let hyp = d.and(sqk, tqk);
    let body = if right {
        d.and_right(sqk, tqk, h)
    } else {
        d.and_left(sqk, tqk, h)
    };

    let inner = close_point(d, p, &pa, h_fv, hyp, body);
    let value = {
        let i = d.lam_fv(t_fv, opens, inner);
        d.lam_fv(s_fv, opens, i)
    };
    let ty = {
        let meet = d.const_app(p.opens_inf, &[s, t]);
        let target = if right { t } else { s };
        let concl = ole(d, p, meet, target);
        let i = d.pi_fv(t_fv, opens, concl);
        d.pi_fv(s_fv, opens, i)
    };
    let name = if right {
        p.opens_inf_le_right
    } else {
        p.opens_inf_le_left
    };
    theorem(d, name, ty, value)
}

/// `Top.Opens.le_inf : ∀ s t u, le u s → le u t → le u (inf s t)`.
fn declare_opens_le_inf(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp1 = ole(d, p, u, s);
    let hyp2 = ole(d, p, u, t);
    let uqk = d.apply(u, &[pa.q, pa.k]);
    let sqk = d.apply(s, &[pa.q, pa.k]);
    let tqk = d.apply(t, &[pa.q, pa.k]);
    let ls = d.apply(h1, &[pa.q, pa.k, h]);
    let rs = d.apply(h2, &[pa.q, pa.k, h]);
    let body = and_intro(d, p, sqk, tqk, ls, rs);

    let inner = close_point(d, p, &pa, h_fv, uqk, body);
    let value = {
        let i = d.lam_fv(h2_fv, hyp2, inner);
        let i = d.lam_fv(h1_fv, hyp1, i);
        let i = d.lam_fv(u_fv, opens, i);
        let i = d.lam_fv(t_fv, opens, i);
        d.lam_fv(s_fv, opens, i)
    };
    let ty = {
        let meet = d.const_app(p.opens_inf, &[s, t]);
        let concl = ole(d, p, u, meet);
        let i = d.arrow(hyp2, concl);
        let i = d.arrow(hyp1, i);
        let i = d.pi_fv(u_fv, opens, i);
        let i = d.pi_fv(t_fv, opens, i);
        d.pi_fv(s_fv, opens, i)
    };
    theorem(d, p.opens_le_inf, ty, value)
}

/// `Top.Opens.le_top : ∀ s, le s Top.Opens.top`.
fn declare_opens_le_top(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let sqk = d.apply(s, &[pa.q, pa.k]);
    let body = d.true_intro();

    let inner = close_point(d, p, &pa, h_fv, sqk, body);
    let value = d.lam_fv(s_fv, opens, inner);
    let ty = {
        let top = d.kernel().const_(p.opens_top, vec![]);
        let concl = ole(d, p, s, top);
        d.pi_fv(s_fv, opens, concl)
    };
    theorem(d, p.opens_le_top, ty, value)
}

/// `Top.Opens.bot_le : ∀ s, le Top.Opens.bot s`.
fn declare_opens_bot_le(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hyp = d.false_ty();
    let sqk = d.apply(s, &[pa.q, pa.k]);
    let body = d.absurd(sqk, h);

    let inner = close_point(d, p, &pa, h_fv, hyp, body);
    let value = d.lam_fv(s_fv, opens, inner);
    let ty = {
        let bot = d.kernel().const_(p.opens_bot, vec![]);
        let concl = ole(d, p, bot, s);
        d.pi_fv(s_fv, opens, concl)
    };
    theorem(d, p.opens_bot_le, ty, value)
}

/// `Top.Opens.le_sup : ∀ f n, le (f n) (Top.Opens.sup f)`.
fn declare_opens_le_sup(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let nat = d.nat_ty();
    let family = d.arrow(nat, opens);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp = d.apply(f, &[n, pa.q, pa.k]);
    let predicate = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let fmqk = d.apply(f, &[m, pa.q, pa.k]);
        d.lam_fv(m_fv, nat, fmqk)
    };
    let body = exists_intro_at(d, p, nat, predicate, n, h);

    let inner = close_point(d, p, &pa, h_fv, hyp, body);
    let value = {
        let i = d.lam_fv(n_fv, nat, inner);
        d.lam_fv(f_fv, family, i)
    };
    let ty = {
        let fn_ = d.apply(f, &[n]);
        let join = d.const_app(p.opens_sup, &[f]);
        let concl = ole(d, p, fn_, join);
        let i = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(f_fv, family, i)
    };
    theorem(d, p.opens_le_sup, ty, value)
}

/// `Top.Opens.sup_le : ∀ f s, (∀ n, le (f n) s) → le (Top.Opens.sup f) s`.
fn declare_opens_sup_le(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let nat = d.nat_ty();
    let family = d.arrow(nat, opens);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let hh_fv = d.fresh_fvar();
    let hh = d.kernel().fvar(hh_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp_family = {
        let fn_ = d.apply(f, &[n]);
        let pointwise = ole(d, p, fn_, s);
        d.pi_fv(n_fv, nat, pointwise)
    };
    let predicate = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let fmqk = d.apply(f, &[m, pa.q, pa.k]);
        d.lam_fv(m_fv, nat, fmqk)
    };
    let target = d.apply(s, &[pa.q, pa.k]);
    let minor = {
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let fnqk = d.apply(f, &[n, pa.q, pa.k]);
        let applied = d.apply(hh, &[n, pa.q, pa.k, hn]);
        let t = d.lam_fv(hn_fv, fnqk, applied);
        d.lam_fv(n_fv, nat, t)
    };
    let hyp = exists_at(d, p, nat, predicate);
    let body = exists_elim_at(d, p, nat, predicate, target, h, minor);

    let inner = close_point(d, p, &pa, h_fv, hyp, body);
    let value = {
        let i = d.lam_fv(hh_fv, hyp_family, inner);
        let i = d.lam_fv(s_fv, opens, i);
        d.lam_fv(f_fv, family, i)
    };
    let ty = {
        let join = d.const_app(p.opens_sup, &[f]);
        let concl = ole(d, p, join, s);
        let i = d.arrow(hyp_family, concl);
        let i = d.pi_fv(s_fv, opens, i);
        d.pi_fv(f_fv, family, i)
    };
    theorem(d, p.opens_sup_le, ty, value)
}

/// `Top.Opens.frame_le : ∀ s f,
/// le (inf s (sup f)) (sup (fun n => inf s (f n)))`.
///
/// **Distributivity of `And` over `Exists`**, and that is the whole content of
/// the frame law on this carrier: no arithmetic, no re-indexing, no choice.
fn declare_opens_frame_le(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let nat = d.nat_ty();
    let family = d.arrow(nat, opens);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let pa = point_args(d);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sqk = d.apply(s, &[pa.q, pa.k]);
    let inner_pred = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let fmqk = d.apply(f, &[m, pa.q, pa.k]);
        d.lam_fv(m_fv, nat, fmqk)
    };
    let ex = exists_at(d, p, nat, inner_pred);
    let hyp = d.and(sqk, ex);
    let hs = d.and_left(sqk, ex, h);
    let he = d.and_right(sqk, ex, h);

    let out_pred = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let fmqk = d.apply(f, &[m, pa.q, pa.k]);
        let conj = d.and(sqk, fmqk);
        d.lam_fv(m_fv, nat, conj)
    };
    let target = exists_at(d, p, nat, out_pred);
    let minor = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let fnqk = d.apply(f, &[n, pa.q, pa.k]);
        let conj = and_intro(d, p, sqk, fnqk, hs, hn);
        let intro = exists_intro_at(d, p, nat, out_pred, n, conj);
        let t = d.lam_fv(hn_fv, fnqk, intro);
        d.lam_fv(n_fv, nat, t)
    };
    let body = exists_elim_at(d, p, nat, inner_pred, target, he, minor);

    let closed = close_point(d, p, &pa, h_fv, hyp, body);
    let value = {
        let i = d.lam_fv(f_fv, family, closed);
        d.lam_fv(s_fv, opens, i)
    };
    let ty = {
        let join = d.const_app(p.opens_sup, &[f]);
        let lhs = d.const_app(p.opens_inf, &[s, join]);
        let rhs = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let fn_ = d.apply(f, &[n]);
            let meet = d.const_app(p.opens_inf, &[s, fn_]);
            let lam = d.lam_fv(n_fv, nat, meet);
            d.const_app(p.opens_sup, &[lam])
        };
        let concl = ole(d, p, lhs, rhs);
        let i = d.pi_fv(f_fv, family, concl);
        d.pi_fv(s_fv, opens, i)
    };
    theorem(d, p.opens_frame_le, ty, value)
}

/// `Top.ballFrame : Top.Frame` — **the instance**.
fn declare_ball_frame(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let names = [
        p.opens_le,
        p.opens_le_refl,
        p.opens_le_trans,
        p.opens_inf,
        p.opens_top,
        p.opens_bot,
        p.opens_sup,
        p.opens_inf_le_left,
        p.opens_inf_le_right,
        p.opens_le_inf,
        p.opens_le_top,
        p.opens_bot_le,
        p.opens_le_sup,
        p.opens_sup_le,
        p.opens_frame_le,
    ];
    let mut args = Vec::with_capacity(FIELD_COUNT);
    args.push(opens);
    for n in names {
        let c = d.kernel().const_(n, vec![]);
        args.push(c);
    }
    assert_eq!(args.len(), FIELD_COUNT, "instance argument count drifted");
    let value = mk_instance(d.kernel(), &p.record, &args);
    let ty = d.kernel().const_(p.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ball_frame,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Top.ballFrame_inf : ∀ s t,
/// Eq Top.Opens (Top.Frame.inf Top.ballFrame s t) (Top.Opens.inf s t)`.
///
/// Proved by `Eq.refl`, so its ADMISSION is the statement that the record
/// selector reduces definitionally on the instance. The arguments are
/// **symbolic**: ADR-1602 §5 measured that a probe at concrete values on a
/// carrier that computes cannot distinguish "the selector reduced" from "both
/// sides happened to evaluate alike".
fn declare_ball_frame_inf(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let opens = opens_ty(d, p);
    let one = d.level_one();
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let frame = d.kernel().const_(p.ball_frame, vec![]);
    let lhs = {
        let sel = field(d, p, frame, INF);
        d.apply(sel, &[s, t])
    };
    let rhs = d.const_app(p.opens_inf, &[s, t]);

    let eq_name = p.creal.rat.int.logic.eq;
    let eq_c = d.kernel().const_(eq_name, vec![one]);
    let stmt = d.apply(eq_c, &[opens, lhs, rhs]);
    let refl_name = p.creal.rat.int.logic.eq_refl;
    let refl_c = d.kernel().const_(refl_name, vec![one]);
    let proof = d.apply(refl_c, &[opens, lhs]);

    let value = {
        let i = d.lam_fv(t_fv, opens, proof);
        d.lam_fv(s_fv, opens, i)
    };
    let ty = {
        let i = d.pi_fv(t_fv, opens, stmt);
        d.pi_fv(s_fv, opens, i)
    };
    theorem(d, p.ball_frame_inf, ty, value)
}

// ---------------------------------------------------------------------------
// The frame's points: what connects `Top.ballFrame` back to `Metric.creal`.
// ---------------------------------------------------------------------------

/// `Top.MemBall x q k` — the two-sided rational sandwich
/// `x ≤ ofRat (q + 1/(k+1))` and `ofRat (q − 1/(k+1)) ≤ x`.
///
/// `creal/density.rs`'s own encoding, chosen there so the estimate mentions no
/// `CReal.add`, `CReal.neg` or `CReal.abs`, and reused verbatim so that
/// [`declare_ball_density`] is `CReal.density` and not a re-derivation of it.
fn mem_ball_body(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    x: ExprId,
    q: ExprId,
    k: ExprId,
) -> ExprId {
    let eps = radius(d, p, k);
    let upper = {
        let add = p.creal.rat.int.rat_add;
        let hi = d.const_app(add, &[q, eps]);
        let embedded = embed(d, p, hi);
        cle(d, p, x, embedded)
    };
    let lower = {
        let sub = p.creal.rat.sub;
        let lo = d.const_app(sub, &[q, eps]);
        let embedded = embed(d, p, lo);
        cle(d, p, embedded, x)
    };
    d.and(upper, lower)
}

fn declare_mem_ball(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = mem_ball_body(d, p, x, q, k);
    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        let t = d.lam_fv(q_fv, rat, t);
        d.lam_fv(x_fv, creal, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(nat, prop);
        let t = d.arrow(rat, t);
        d.arrow(creal, t)
    };
    definition(d, p.mem_ball, ty, value)
}

/// `Top.MemOpen x s := ∃ q k, s q k ∧ Top.MemBall x q k` — the points of a
/// formal open. This is where the frame stops being pointfree and meets ℝ.
fn mem_open_body(d: &mut IntDev<'_>, p: TopFramePrelude, x: ExprId, s: ExprId) -> ExprId {
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let inner = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sqk = d.apply(s, &[q, k]);
        let mem = d.const_app(p.mem_ball, &[x, q, k]);
        let conj = d.and(sqk, mem);
        let pred = d.lam_fv(k_fv, nat, conj);
        exists_at(d, p, nat, pred)
    };
    let pred = d.lam_fv(q_fv, rat, inner);
    exists_at(d, p, rat, pred)
}

fn declare_mem_open(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let opens = opens_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);

    let body = mem_open_body(d, p, x, s);
    let value = {
        let t = d.lam_fv(s_fv, opens, body);
        d.lam_fv(x_fv, creal, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(opens, prop);
        d.arrow(creal, t)
    };
    definition(d, p.mem_open, ty, value)
}

/// `Top.ball_mem_self : ∀ q k, Top.MemBall (CReal.ofRat q) q k`.
///
/// **The non-vacuity witness.** Every law in `Top.Opens` above holds of the
/// everywhere-false predicate; this is the statement that `Top.MemBall` is not
/// the empty relation. Both halves are `CReal.ofRat_le` applied to a rational
/// inequality obtained by padding with the nonnegative radius
/// (`Rat.zero_le_natDivSucc`) and trimming the `+ 0` (`Rat.add_zero`); the
/// lower half then goes through `Rat.sub_le_of_le`, which is stated exactly in
/// the `le u (add v q) → le (sub u v) q` shape this needs.
fn declare_ball_mem_self(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rle, rzero};

    let rat_p = p.creal.rat;
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let eps = radius(d, p, k);
    let zero = rzero(d, rat_p);
    let one_nat = d.num(1);

    // `Rat.le (q + 0) (q + eps)`.
    let refl_q = d.lemma(rat_p.le_refl, &[q]);
    let nonneg = d.lemma(rat_p.zero_le_nat_div_succ, &[one_nat, k]);
    let widened = d.lemma(rat_p.add_le_add, &[q, q, zero, eps, refl_q, nonneg]);
    let padded = radd(d, q, zero);
    let hi = radd(d, q, eps);
    // `Rat.le q (q + eps)`.
    let trim = d.lemma(rat_p.add_zero, &[q]);
    let q_le_hi = rat_eq_rewrite(d, padded, q, trim, widened, &|d, t| rle(d, rat_p, t, hi));
    // `Rat.le q (eps + q)`, the shape `Rat.sub_le_of_le` consumes.
    let swap = d.lemma(rat_p.add_comm, &[q, eps]);
    let flipped = radd(d, eps, q);
    let q_le_flipped = rat_eq_rewrite(d, hi, flipped, swap, q_le_hi, &|d, t| rle(d, rat_p, q, t));
    // `Rat.le (q − eps) q`.
    let lo_le_q = d.lemma(rat_p.sub_le_of_le, &[q, eps, q, q_le_flipped]);

    let upper = d.lemma(p.creal.of_rat_le, &[q, hi, q_le_hi]);
    let lower = {
        let sub = rat_p.sub;
        let lo = d.const_app(sub, &[q, eps]);
        d.lemma(p.creal.of_rat_le, &[lo, q, lo_le_q])
    };

    let xq = embed(d, p, q);
    let stmt = d.const_app(p.mem_ball, &[xq, q, k]);
    let (left, right) = {
        let hi_e = embed(d, p, hi);
        let sub = rat_p.sub;
        let lo = d.const_app(sub, &[q, eps]);
        let lo_e = embed(d, p, lo);
        let l = cle(d, p, xq, hi_e);
        let r = cle(d, p, lo_e, xq);
        (l, r)
    };
    let body = and_intro(d, p, left, right, upper, lower);

    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        d.lam_fv(q_fv, rat, t)
    };
    let ty = {
        let t = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(q_fv, rat, t)
    };
    theorem(d, p.ball_mem_self, ty, value)
}

/// `Top.ball_density : ∀ x k, ∃ q, Top.MemBall x q k`.
///
/// **`CReal.density`, restated in the frame's vocabulary** — the proof term is
/// the reals prelude's own lemma applied, and the restatement type-checks by
/// δβ alone. That is the finding, not a shortcut: the density of ℚ in ℝ *is*
/// the covering property of the open-ball frame, and no new estimate is
/// needed to see it.
fn declare_ball_density(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = d.lemma(p.creal.density, &[x, k]);
    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        d.lam_fv(x_fv, creal, t)
    };
    let ty = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let mem = d.const_app(p.mem_ball, &[x, q, k]);
        let pred = d.lam_fv(q_fv, rat, mem);
        let stmt = exists_at(d, p, rat, pred);
        let t = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(x_fv, creal, t)
    };
    theorem(d, p.ball_density, ty, value)
}

/// `Top.mem_top : ∀ x, Top.MemOpen x Top.Opens.top` — the frame's top element
/// contains every real, at radius index `0`.
fn declare_mem_top(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero = d.zero();
    let top = d.kernel().const_(p.opens_top, vec![]);

    let target = mem_open_body(d, p, x, top);

    // The predicate `CReal.density x 0` is an `Exists` over.
    let dens_pred = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let mem = mem_ball_body(d, p, x, q, zero);
        d.lam_fv(q_fv, rat, mem)
    };
    let witness = d.lemma(p.creal.density, &[x, zero]);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = mem_ball_body(d, p, x, q, zero);

        // `And (Top.Opens.top q 0) (Top.MemBall x q 0)`, i.e. `And True _`.
        let true_ty = d.true_ty();
        let mem = d.const_app(p.mem_ball, &[x, q, zero]);
        let tt = d.true_intro();
        let conj = and_intro(d, p, true_ty, mem, tt, h);

        let inner_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let tqk = d.apply(top, &[q, k]);
            let m = d.const_app(p.mem_ball, &[x, q, k]);
            let c = d.and(tqk, m);
            d.lam_fv(k_fv, nat, c)
        };
        let inner = exists_intro_at(d, p, nat, inner_pred, zero, conj);

        let outer_pred = {
            let q2_fv = d.fresh_fvar();
            let q2 = d.kernel().fvar(q2_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let tqk = d.apply(top, &[q2, k]);
            let m = d.const_app(p.mem_ball, &[x, q2, k]);
            let c = d.and(tqk, m);
            let ip = d.lam_fv(k_fv, nat, c);
            let e = exists_at(d, p, nat, ip);
            d.lam_fv(q2_fv, rat, e)
        };
        let outer = exists_intro_at(d, p, rat, outer_pred, q, inner);
        let t = d.lam_fv(h_fv, hyp, outer);
        d.lam_fv(q_fv, rat, t)
    };
    let body = exists_elim_at(d, p, rat, dens_pred, target, witness, minor);

    let value = d.lam_fv(x_fv, creal, body);
    let ty = {
        let concl = d.const_app(p.mem_open, &[x, top]);
        d.pi_fv(x_fv, creal, concl)
    };
    theorem(d, p.mem_top, ty, value)
}

/// `Top.mem_open_mono : ∀ x s t, Top.Opens.le s t → Top.MemOpen x s →
/// Top.MemOpen x t` — the points-of-an-open assignment is monotone for the
/// frame's OWN order. Without this the frame and its points are two unrelated
/// objects that happen to share a file.
fn declare_mem_open_mono(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let opens = opens_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let hyp_le = ole(d, p, s, t);
    let hyp_mem = d.const_app(p.mem_open, &[x, s]);
    let target = d.const_app(p.mem_open, &[x, t]);

    // `fun q => ∃ k, s q k ∧ MemBall x q k` — the predicate `hm` witnesses.
    let outer_pred_s = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sqk = d.apply(s, &[q, k]);
        let m = d.const_app(p.mem_ball, &[x, q, k]);
        let c = d.and(sqk, m);
        let ip = d.lam_fv(k_fv, nat, c);
        let e = exists_at(d, p, nat, ip);
        d.lam_fv(q_fv, rat, e)
    };
    let outer_pred_t = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let tqk = d.apply(t, &[q, k]);
        let m = d.const_app(p.mem_ball, &[x, q, k]);
        let c = d.and(tqk, m);
        let ip = d.lam_fv(k_fv, nat, c);
        let e = exists_at(d, p, nat, ip);
        d.lam_fv(q_fv, rat, e)
    };

    let minor_outer = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);

        let inner_pred_s = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sqk = d.apply(s, &[q, k]);
            let m = d.const_app(p.mem_ball, &[x, q, k]);
            let c = d.and(sqk, m);
            d.lam_fv(k_fv, nat, c)
        };
        let inner_pred_t = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let tqk = d.apply(t, &[q, k]);
            let m = d.const_app(p.mem_ball, &[x, q, k]);
            let c = d.and(tqk, m);
            d.lam_fv(k_fv, nat, c)
        };
        let hyp_inner = exists_at(d, p, nat, inner_pred_s);

        let minor_inner = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let sqk = d.apply(s, &[q, k]);
            let tqk = d.apply(t, &[q, k]);
            let m = d.const_app(p.mem_ball, &[x, q, k]);
            let hs = d.and_left(sqk, m, hk);
            let hmem = d.and_right(sqk, m, hk);
            let moved = d.apply(hle, &[q, k, hs]);
            let conj = and_intro(d, p, tqk, m, moved, hmem);
            let intro = exists_intro_at(d, p, nat, inner_pred_t, k, conj);
            let outer = exists_intro_at(d, p, rat, outer_pred_t, q, intro);
            let hyp_k = d.and(sqk, m);
            let z = d.lam_fv(hk_fv, hyp_k, outer);
            d.lam_fv(k_fv, nat, z)
        };
        let body = exists_elim_at(d, p, nat, inner_pred_s, target, hq, minor_inner);
        let z = d.lam_fv(hq_fv, hyp_inner, body);
        d.lam_fv(q_fv, rat, z)
    };
    let body = exists_elim_at(d, p, rat, outer_pred_s, target, hm, minor_outer);

    let value = {
        let i = d.lam_fv(hm_fv, hyp_mem, body);
        let i = d.lam_fv(hle_fv, hyp_le, i);
        let i = d.lam_fv(t_fv, opens, i);
        let i = d.lam_fv(s_fv, opens, i);
        d.lam_fv(x_fv, creal, i)
    };
    let ty = {
        let i = d.arrow(hyp_mem, target);
        let i = d.arrow(hyp_le, i);
        let i = d.pi_fv(t_fv, opens, i);
        let i = d.pi_fv(s_fv, opens, i);
        d.pi_fv(x_fv, creal, i)
    };
    theorem(d, p.mem_open_mono, ty, value)
}

/// `Top.ball_separated : ∀ q r k m,
/// CReal.lt (ofRat (q + 1/(k+1))) (ofRat (r − 1/(m+1))) →
/// ∀ z, Top.MemBall z q k → Top.MemBall z r m → False`.
///
/// **Hausdorff, the half that is geometry**: two balls whose brackets are
/// strictly separated share no point. Four steps and no arithmetic —
/// `le_trans` through the shared point, then `lt_of_le_of_lt` against the
/// separation hypothesis, then `lt_irrefl`.
///
/// What it does NOT do is produce the separated pair from `CReal.Apart x y`.
/// That step is index selection, not geometry, and is sized in ADR-1643.
fn declare_ball_separated(d: &mut IntDev<'_>, p: TopFramePrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let rat = rat_ty(d, p);
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let hsep_fv = d.fresh_fvar();
    let hsep = d.kernel().fvar(hsep_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let eps = radius(d, p, k);
    let delta = radius(d, p, m);
    let add = p.creal.rat.int.rat_add;
    let sub = p.creal.rat.sub;
    let hi = d.const_app(add, &[q, eps]);
    let lo = d.const_app(sub, &[r, delta]);
    let hi_e = embed(d, p, hi);
    let lo_e = embed(d, p, lo);

    let sep_stmt = {
        let n = p.creal.lt;
        d.const_app(n, &[hi_e, lo_e])
    };
    let mem1 = d.const_app(p.mem_ball, &[z, q, k]);
    let mem2 = d.const_app(p.mem_ball, &[z, r, m]);

    // `z ≤ ofRat (q + eps)` and `ofRat (r − delta) ≤ z`.
    let up1 = {
        let l = cle(d, p, z, hi_e);
        let rr = {
            let lo_q = d.const_app(sub, &[q, eps]);
            let lo_qe = embed(d, p, lo_q);
            cle(d, p, lo_qe, z)
        };
        d.and_left(l, rr, h1)
    };
    let low2 = {
        let hi_r = d.const_app(add, &[r, delta]);
        let hi_re = embed(d, p, hi_r);
        let l = cle(d, p, z, hi_re);
        let rr = cle(d, p, lo_e, z);
        d.and_right(l, rr, h2)
    };

    let chained = d.lemma(p.creal.le_trans, &[lo_e, z, hi_e, low2, up1]);
    let bad = d.lemma(p.creal.lt_of_le_of_lt, &[lo_e, hi_e, lo_e, chained, hsep]);
    let irrefl = d.lemma(p.creal.lt_irrefl, &[lo_e]);
    let body = d.apply(irrefl, &[bad]);

    let false_ty = d.false_ty();
    let value = {
        let i = d.lam_fv(h2_fv, mem2, body);
        let i = d.lam_fv(h1_fv, mem1, i);
        let i = d.lam_fv(z_fv, creal, i);
        let i = d.lam_fv(hsep_fv, sep_stmt, i);
        let i = d.lam_fv(m_fv, nat, i);
        let i = d.lam_fv(k_fv, nat, i);
        let i = d.lam_fv(r_fv, rat, i);
        d.lam_fv(q_fv, rat, i)
    };
    let ty = {
        let i = d.arrow(mem2, false_ty);
        let i = d.arrow(mem1, i);
        let i = d.pi_fv(z_fv, creal, i);
        let i = d.arrow(sep_stmt, i);
        let i = d.pi_fv(m_fv, nat, i);
        let i = d.pi_fv(k_fv, nat, i);
        let i = d.pi_fv(r_fv, rat, i);
        d.pi_fv(q_fv, rat, i)
    };
    theorem(d, p.ball_separated, ty, value)
}
