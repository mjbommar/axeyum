//! **What the classical order on ℝ buys, priced as a hypothesis** (roadmap
//! W0-2, reviewers 03.1 and 12.2) — four classical theorems about `CReal`
//! that this development states outright it cannot prove, each stated with
//! the order decision as an **explicit hypothesis** and each admitted with an
//! **empty `Kernel::axiom_footprint`**.
//!
//! ## The question this file answers
//!
//! W0-2 asks whether classical logic should enter the library as a labelled
//! axiom in the footprint, or as a hypothesis discharged at use. That is not
//! a question of taste; it is a question of *cost*, and the cost was never
//! measured. ADR-1595 settled the sibling question (quotients) by building
//! the theorem and counting the obligations. This file does the same thing
//! for the classical order.
//!
//! ## The hypothesis, and why this one
//!
//! ```text
//! OrderDecision  :=  ∀ (x y : CReal), Or (CReal.lt x y) (CReal.le y x)
//! ```
//!
//! Read it as *"either `x` is strictly below `y`, or `y` is at most `x`"* —
//! the constructive co-decision of the order. It is written this way, rather
//! than as `Or (le x y) (le y x)`, because the strict-left form is the one
//! that is **LPO-strength**: applied to `0` and the real coded by a `Bool`
//! sequence, it decides whether the sequence ever fires.
//! [`CReal.le_total_of_order_decision`](CRealOmniscienceNames::le_total_of_order_decision)
//! below derives the weaker `le_total` from it in two steps, which is the
//! measurement of exactly that gap.
//!
//! Three existing declarations show this is the right hypothesis to price:
//!
//! - [`CReal.evt_attained_max_decides_sign`](super::ExtremeValueNames::evt_attained_max_decides_sign)
//!   and [`CReal.ivt_exact_root_decides_sign`](crate::IvtBoundaryNames::ivt_exact_root_decides_sign)
//!   both **reduce** a classical analysis theorem *to* an order decision on
//!   `CReal`. They are the arrow pointing in; this file is the arrow pointing
//!   out, and nobody had drawn it.
//! - `creal.rs`'s own documentation names two of the four conclusions below
//!   as unavailable, in prose, in the field docs:
//!   [`CReal.lt`](super::CRealPrelude::lt) records that there is "no
//!   `le_total` over ℝ to recover it from", and [`CReal.abs`](super::CRealPrelude::abs)
//!   records that "`Equiv (abs x) x ∨ Equiv (abs x) (neg x)` is a decision on
//!   the sign of a real and is **not** available". Both are now theorems, on
//!   a hypothesis.
//!
//! ## The four theorems, and the chain depth
//!
//! ```text
//!   OrderDecision ──> le_total ──────> abs_cases
//!                └──> trichotomy ────> apart_of_not_equiv
//! ```
//!
//! Two of the four **consume another theorem of this file**, which is the
//! point: the measurement is not "what does one statement cost", it is "what
//! does *carrying* the hypothesis through a proof cost".
//!
//! The answer, counted in ADR-1601
//! (`docs/research/09-decisions/adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md`):
//! **one binder per statement, one argument per use site, and zero new
//! obligations.** The hypothesis is never re-derived, never weakened, and
//! never generates a side condition. That is the whole price of the
//! hypothesis route on this family.
//!
//! ## What is NOT claimed
//!
//! This file does **not** prove that `OrderDecision` is equivalent to LPO
//! over `Nat` (`nat_prelude/omniscience.rs`). That reduction needs a real
//! built from a `Bool` sequence — `∑ 2⁻ⁿ [f n = true]` — and the
//! summability estimate that goes with it. It is the natural next
//! declaration and it is **not** here; the connection is stated in the module
//! docs and in ADR-1601 as a citation, not as a theorem.
//!
//! Nor does it prove any of the four conclusions *unconditionally*. Every one
//! of them carries the hypothesis in its type, which is exactly why the
//! footprint stays empty.

#![allow(clippy::doc_markdown)]

use super::{CRealPrelude, cle, clt, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The four theorem names this module admits under `CReal.`.
///
/// Held as its own struct, the way `creal/lub_boundary.rs` holds
/// [`crate::LubBoundaryNames`], so the W0-2 measurement costs
/// [`CRealPrelude`] exactly one field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CRealOmniscienceNames {
    /// `CReal.le_total_of_order_decision :
    /// (∀ x y, Or (lt x y) (le y x)) → ∀ x y, Or (le x y) (le y x)`.
    ///
    /// **`CReal.le_total`, on a hypothesis.** The theorem
    /// [`CReal.lt`](super::CRealPrelude::lt)'s own field documentation says
    /// does not exist over ℝ — "`Rat.le_total` holds for ℚ and does not
    /// lift" — and the decision principle
    /// `docs/curriculum/graded-statement-families-*` measured that every
    /// analysis row 2 extracts. One `Or.elim` and one
    /// [`le_of_lt`](super::CRealPrelude::le_of_lt).
    pub le_total_of_order_decision: NameId,
    /// `CReal.trichotomy_of_order_decision :
    /// (∀ x y, Or (lt x y) (le y x)) →
    /// ∀ x y, Or (lt x y) (Or (Equiv x y) (lt y x))`.
    ///
    /// **Trichotomy on ℝ, on a hypothesis.** `Rat.lt_trichotomy` exists
    /// because ℚ's order is decidable; the `CReal` statement is absent from
    /// the environment for exactly the reason this hypothesis supplies. Two
    /// `Or.elim`s and one
    /// [`equiv_of_le_le`](super::CRealPrelude::equiv_of_le_le) — no
    /// arithmetic, no subtraction, no estimate.
    pub trichotomy_of_order_decision: NameId,
    /// `CReal.apart_of_not_equiv_of_order_decision :
    /// (∀ x y, Or (lt x y) (le y x)) → ∀ x y, Not (Equiv x y) → Apart x y`.
    ///
    /// **The converse of [`CReal.not_equiv_of_apart`](super::CRealPrelude::not_equiv_of_apart),
    /// which that field's own documentation names as "Markov's principle"
    /// and records as "neither proved nor assumed here".** It is now proved,
    /// on a hypothesis. Consumes
    /// [`trichotomy_of_order_decision`](Self::trichotomy_of_order_decision),
    /// so it is the depth-2 node of the chain and the one that measures what
    /// carrying the hypothesis costs.
    pub apart_of_not_equiv_of_order_decision: NameId,
    /// `CReal.abs_cases_of_order_decision :
    /// (∀ x y, Or (lt x y) (le y x)) →
    /// ∀ x, Or (Equiv (abs x) x) (Equiv (abs x) (neg x))`.
    ///
    /// **The statement [`CReal.abs`](super::CRealPrelude::abs)'s field
    /// documentation calls "a decision on the sign of a real" and marks as
    /// "**not** available".** Now available, on a hypothesis. Consumes
    /// [`le_total_of_order_decision`](Self::le_total_of_order_decision) and
    /// the join's universal property
    /// ([`max_le`](super::CRealPrelude::max_le),
    /// [`le_max_left`](super::CRealPrelude::le_max_left),
    /// [`le_max_right`](super::CRealPrelude::le_max_right)); `abs x` unfolds
    /// to `max x (neg x)` definitionally, so no bridge lemma is needed.
    pub abs_cases_of_order_decision: NameId,
}

impl CRealOmniscienceNames {
    /// Intern the four names under the `CReal` namespace root.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            le_total_of_order_decision: kernel.name_str(creal, "le_total_of_order_decision"),
            trichotomy_of_order_decision: kernel.name_str(creal, "trichotomy_of_order_decision"),
            apart_of_not_equiv_of_order_decision: kernel
                .name_str(creal, "apart_of_not_equiv_of_order_decision"),
            abs_cases_of_order_decision: kernel.name_str(creal, "abs_cases_of_order_decision"),
        }
    }
}

/// Admit the four W0-2 measurement theorems.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_omniscience(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_le_total(d, p)?;
    declare_trichotomy(d, p)?;
    declare_apart_of_not_equiv(d, p)?;
    declare_abs_cases(d, p)
}

// --- local term helpers -----------------------------------------------------

/// `CReal.Equiv x y`.
fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `CReal.Apart x y`.
fn capart(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.apart, &[x, y])
}

/// `CReal.neg x`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal.abs x`.
fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

/// `Not a`.
fn cnot(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let name = p.rat.int.logic.not;
    d.const_app(name, &[a])
}

/// `OrderDecision := ∀ (x y : CReal), Or (lt x y) (le y x)`.
///
/// Spelled out inline everywhere it is used rather than hidden behind a
/// `Definition`, so a reader of any rendered type below sees the whole
/// hypothesis and nothing about the conclusion can be smuggled into an
/// abbreviation. This is `least_number.rs`'s discipline, applied to ℝ.
fn order_decision(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let strict = clt(d, p, x, y);
    let weak = cle(d, p, y, x);
    let body = d.or(strict, weak);
    let with_y = d.pi_fv(y_fv, carrier, body);
    d.pi_fv(x_fv, carrier, with_y)
}

// --- `CReal.le_total_of_order_decision` -------------------------------------

/// `CReal.le_total_of_order_decision :
/// (∀ x y, Or (lt x y) (le y x)) → ∀ x y, Or (le x y) (le y x)`
///
/// One `Or.elim`: the strict branch weakens through
/// [`CRealPrelude::le_of_lt`], the other branch *is* the right disjunct.
fn declare_le_total(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let od_ty = order_decision(d, p);
    let od_fv = d.fresh_fvar();
    let od = d.kernel().fvar(od_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let strict = clt(d, p, x, y);
    let flipped = cle(d, p, y, x);
    let forward = cle(d, p, x, y);
    let target = d.or(forward, flipped);

    let decision = d.apply(od, &[x, y]);
    let body = d.or_elim(
        strict,
        flipped,
        target,
        decision,
        &|d, h| {
            let weakened = d.lemma(p.le_of_lt, &[x, y, h]);
            d.or_inl(forward, flipped, weakened)
        },
        &|d, h| d.or_inr(forward, flipped, h),
    );

    let ty = {
        let with_y = d.pi_fv(y_fv, carrier, target);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.arrow(od_ty, with_x)
    };
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(od_fv, od_ty, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.omniscience.le_total_of_order_decision,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.trichotomy_of_order_decision` -----------------------------------

/// `CReal.trichotomy_of_order_decision : (∀ x y, Or (lt x y) (le y x)) →
/// ∀ x y, Or (lt x y) (Or (Equiv x y) (lt y x))`
///
/// Two `Or.elim`s and one [`CRealPrelude::equiv_of_le_le`]. The hypothesis is
/// consumed **twice** — once at `(x, y)` and once at `(y, x)` — which is the
/// smallest honest example of what "carrying a classical hypothesis" costs:
/// one extra argument at each of two use sites, and nothing else.
fn declare_trichotomy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let od_ty = order_decision(d, p);
    let od_fv = d.fresh_fvar();
    let od = d.kernel().fvar(od_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let lt_xy = clt(d, p, x, y);
    let lt_yx = clt(d, p, y, x);
    let le_yx = cle(d, p, y, x);
    let le_xy = cle(d, p, x, y);
    let eq_xy = cequiv(d, p, x, y);
    let tail = d.or(eq_xy, lt_yx);
    let target = d.or(lt_xy, tail);

    let outer = d.apply(od, &[x, y]);
    let body = d.or_elim(
        lt_xy,
        le_yx,
        target,
        outer,
        &|d, h| d.or_inl(lt_xy, tail, h),
        &|d, h_le_yx| {
            // `y ≤ x` is settled; ask the decision again the other way round.
            let inner = d.apply(od, &[y, x]);
            d.or_elim(
                lt_yx,
                le_xy,
                target,
                inner,
                &|d, h| {
                    let right = d.or_inr(eq_xy, lt_yx, h);
                    d.or_inr(lt_xy, tail, right)
                },
                &|d, h_le_xy| {
                    let same = d.lemma(p.equiv_of_le_le, &[x, y, h_le_xy, h_le_yx]);
                    let left = d.or_inl(eq_xy, lt_yx, same);
                    d.or_inr(lt_xy, tail, left)
                },
            )
        },
    );

    let ty = {
        let with_y = d.pi_fv(y_fv, carrier, target);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.arrow(od_ty, with_x)
    };
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(od_fv, od_ty, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.omniscience.trichotomy_of_order_decision,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.apart_of_not_equiv_of_order_decision` ---------------------------

/// `CReal.apart_of_not_equiv_of_order_decision : (∀ x y, Or (lt x y) (le y x))
/// → ∀ x y, Not (Equiv x y) → Apart x y`
///
/// **The direction [`CRealPrelude::not_equiv_of_apart`]'s documentation calls
/// Markov's principle and records as "neither proved nor assumed here".**
///
/// Depth 2 of the chain: it consumes
/// [`trichotomy_of_order_decision`](CRealOmniscienceNames::trichotomy_of_order_decision)
/// rather than the hypothesis directly, and the *entire* cost of that is
/// passing `od` along as one extra argument. `Apart x y` unfolds to
/// `Or (lt x y) (lt y x)` definitionally, so the two strict branches are the
/// conclusion verbatim and only the `Equiv` branch does work — it contradicts
/// the standing `Not (Equiv x y)`.
fn declare_apart_of_not_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let od_ty = order_decision(d, p);
    let od_fv = d.fresh_fvar();
    let od = d.kernel().fvar(od_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let eq_xy = cequiv(d, p, x, y);
    let neq_ty = cnot(d, p, eq_xy);
    let neq_fv = d.fresh_fvar();
    let neq = d.kernel().fvar(neq_fv);

    let lt_xy = clt(d, p, x, y);
    let lt_yx = clt(d, p, y, x);
    let target = capart(d, p, x, y);
    let tail = d.or(eq_xy, lt_yx);

    let tri = d.lemma(p.omniscience.trichotomy_of_order_decision, &[od, x, y]);
    let body = d.or_elim(
        lt_xy,
        tail,
        target,
        tri,
        // `Apart x y` IS `Or (lt x y) (lt y x)`; the first disjunct is done.
        &|d, h| d.or_inl(lt_xy, lt_yx, h),
        &|d, h_tail| {
            d.or_elim(
                eq_xy,
                lt_yx,
                target,
                h_tail,
                &|d, h_eq| {
                    let bad = d.apply(neq, &[h_eq]);
                    d.absurd(target, bad)
                },
                &|d, h_gt| d.or_inr(lt_xy, lt_yx, h_gt),
            )
        },
    );

    let ty = {
        let inner = d.arrow(neq_ty, target);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.arrow(od_ty, with_x)
    };
    let value = {
        let inner = d.lam_fv(neq_fv, neq_ty, body);
        let with_y = d.lam_fv(y_fv, carrier, inner);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(od_fv, od_ty, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.omniscience.apart_of_not_equiv_of_order_decision,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.abs_cases_of_order_decision` ------------------------------------

/// `CReal.abs_cases_of_order_decision : (∀ x y, Or (lt x y) (le y x)) →
/// ∀ x, Or (Equiv (abs x) x) (Equiv (abs x) (neg x))`
///
/// **The statement [`CRealPrelude::abs`]'s own documentation marks as "not
/// available".** Depth 2 of the second chain: it consumes
/// [`le_total_of_order_decision`](CRealOmniscienceNames::le_total_of_order_decision)
/// at `(neg x, x)` and then closes each branch with the join's universal
/// property.
///
/// - `neg x ≤ x`: [`CRealPrelude::max_le`] against
///   [`CRealPrelude::le_refl`] gives `max x (neg x) ≤ x`, and
///   [`CRealPrelude::le_max_left`] the converse.
/// - `x ≤ neg x`: the mirror, through [`CRealPrelude::le_max_right`].
///
/// Both close with [`CRealPrelude::equiv_of_le_le`]. `abs x` is a
/// `Definition` unfolding to `max x (neg x)`, so the conclusion is stated
/// with `abs` and no bridge lemma is needed — the kernel's own conversion
/// does it, which is itself worth having checked.
fn declare_abs_cases(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let od_ty = order_decision(d, p);
    let od_fv = d.fresh_fvar();
    let od = d.kernel().fvar(od_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let nx = cneg(d, p, x);
    let ax = cabs(d, p, x);

    let same = cequiv(d, p, ax, x);
    let flipped = cequiv(d, p, ax, nx);
    let target = d.or(same, flipped);

    let le_nx_x = cle(d, p, nx, x);
    let le_x_nx = cle(d, p, x, nx);

    let total = d.lemma(p.omniscience.le_total_of_order_decision, &[od, nx, x]);
    let body = d.or_elim(
        le_nx_x,
        le_x_nx,
        target,
        total,
        &|d, h| {
            let refl_x = d.lemma(p.le_refl, &[x]);
            let upper = d.lemma(p.max_le, &[x, nx, x, refl_x, h]);
            let lower = d.lemma(p.le_max_left, &[x, nx]);
            let eq = d.lemma(p.equiv_of_le_le, &[ax, x, upper, lower]);
            d.or_inl(same, flipped, eq)
        },
        &|d, h| {
            let refl_nx = d.lemma(p.le_refl, &[nx]);
            let upper = d.lemma(p.max_le, &[x, nx, nx, h, refl_nx]);
            let lower = d.lemma(p.le_max_right, &[x, nx]);
            let eq = d.lemma(p.equiv_of_le_le, &[ax, nx, upper, lower]);
            d.or_inr(same, flipped, eq)
        },
    );

    let ty = {
        let with_x = d.pi_fv(x_fv, carrier, target);
        d.arrow(od_ty, with_x)
    };
    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(od_fv, od_ty, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.omniscience.abs_cases_of_order_decision,
        uparams: vec![],
        ty,
        value,
    })
}
