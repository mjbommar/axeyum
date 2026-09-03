//! `tactic` — a combinator over the four term-emitting producers
//! ([`crate::decide`], [`crate::linarith`], [`crate::ring`], [`crate::simp`]),
//! all over the ℕ carrier ([`crate::NatOps`]).
//!
//! A real proof is rarely one tactic. [`Tactic::Then`] runs one producer,
//! then a second on what the first leaves behind; [`Tactic::First`] tries a
//! list in order and returns the first success. Every leaf still bottoms out
//! at [`Kernel::add_declaration`](crate::Kernel::add_declaration) exactly as
//! before — the combinator adds no trusted surface of its own, only more
//! ways to compose four producers that already had none.
//!
//! ## `Then`'s two regimes
//!
//! Only [`crate::simp`] has a genuine *residue*: it can rewrite a term
//! without fully closing the goal it appears in. `decide`, `linarith` and
//! `ring` each either close a goal outright or decline — neither has a
//! partial result to hand forward. So [`Tactic::Then`] has two behaviours,
//! chosen by what the FIRST tactic is:
//!
//! - **First is [`Tactic::Simp`]**: rewrite `lhs` and `rhs` separately to
//!   their `simp` normal forms (via
//!   [`simp::nat::normalize`](crate::simp::nat), the one entry point this
//!   module adds to `simp` — see that function's docs for why nothing else
//!   needed to move), form the new goal over the two normal forms, run the
//!   second tactic on THAT, and glue the three equalities back into a proof
//!   of the original goal with `Eq.rec`-based transport (`Eq.trans`'s own
//!   shape for an `Eq` goal; the same construction generalizes to `Nat.le`
//!   /`Nat.lt` because [`NatOps::eq_motive`](crate::NatOps::eq_motive) is
//!   generic in the predicate, not specific to `Eq`).
//! - **First is anything else**: there is no residue to chain, so `Then`
//!   degrades to "try the first, and if it declines, try the second on the
//!   SAME goal" — sequential fallback, not gluing. This keeps `Then` total
//!   (every combination of tactics is a legal `Tactic` value) without
//!   pretending a non-`simp` first stage produces a partial result it does
//!   not have. No test in this crate exercises this arm through anything
//!   but a full solve-or-decline on both sides, which is exactly the case it
//!   is honestly built for.
//!
//! ## `First`
//!
//! Try each tactic in order; return the first success. On total failure,
//! [`Decline::First`] carries every sub-decline, in order — the same
//! "declines are data" convention every producer here already follows.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::NatOps;
use crate::NatPrelude;
use crate::decide;
use crate::decide::Shape;
use crate::expr::ExprId;
use crate::linarith;
use crate::ring;
use crate::simp;

/// The context a [`Tactic::run`] needs: the prelude every producer takes,
/// the hypothesis list [`linarith`] searches over, and the rewrite set
/// [`simp`] rewrites with.
pub struct Ctx<'a, D: NatOps> {
    /// The `Nat` prelude every producer is declared against.
    pub prelude: NatPrelude,
    /// Hypotheses `linarith` may use — ignored by every other tactic.
    pub assumptions: &'a [linarith::nat::Assumption],
    /// The rewrite set `simp` rewrites with — ignored by every other tactic.
    pub rules: &'a [simp::nat::Rule<D>],
}

/// A producer, or a way of composing two or more of them.
pub enum Tactic {
    /// [`decide::run`].
    Decide,
    /// [`linarith::nat::prove`].
    Linarith,
    /// [`ring::nat::prove`].
    Ring,
    /// [`simp::nat::prove`].
    Simp,
    /// Run the first; see the module docs for the two regimes.
    Then(Box<Tactic>, Box<Tactic>),
    /// Try each in order; the first success wins.
    First(Vec<Tactic>),
}

/// Why [`run`] produced no term.
///
/// Each producer's own decline is carried through unchanged — a combinator
/// decline is never a NEW way to fail, only a record of which producer(s)
/// were asked and declined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decline {
    /// [`decide::run`] declined.
    Decide(decide::Decline),
    /// [`linarith::nat::prove`] declined.
    Linarith(linarith::Decline),
    /// [`ring::nat::prove`] declined.
    Ring(ring::Decline),
    /// [`simp::nat::prove`] (or, inside a `Then(Simp, _)`, the normalizer
    /// alone) declined.
    Simp(simp::Decline),
    /// [`Tactic::First`] tried every listed tactic and none succeeded; one
    /// entry per tactic, in the order they were tried.
    First(Vec<Decline>),
}

fn build_rel<D: NatOps>(d: &mut D, shape: Shape, a: ExprId, b: ExprId) -> ExprId {
    match shape {
        Shape::Eq => d.eq(a, b),
        Shape::Le => d.le(a, b),
        Shape::Lt => d.lt(a, b),
    }
}

/// `h : Eq from to`, `proof_at_from : rel(from, other)` (`lhs_position`) or
/// `rel(other, from)` (`!lhs_position`) ⊢ the same relation with `from`
/// replaced by `to`. The one piece of `Eq.rec` plumbing both `Then(Simp, _)`
/// and its corrupted-glue test share.
#[allow(clippy::too_many_arguments)]
fn transport_rel<D: NatOps>(
    d: &mut D,
    shape: Shape,
    from: ExprId,
    to: ExprId,
    h: ExprId,
    other: ExprId,
    proof_at_from: ExprId,
    lhs_position: bool,
) -> ExprId {
    let motive = if lhs_position {
        d.eq_motive(from, &|d, x| build_rel(d, shape, x, other))
    } else {
        d.eq_motive(from, &|d, x| build_rel(d, shape, other, x))
    };
    d.transport(from, motive, proof_at_from, to, h)
}

/// Glue a proof of `rel(lhs2, rhs2)` (`residue`) back into a proof of
/// `rel(lhs, rhs)`, given `hl : Eq lhs lhs2` and `hr : Eq rhs rhs2` — the
/// two equalities [`simp::nat::normalize`] produced for each side.
///
/// Private, and deliberately so: the corrupted-glue test in this module's
/// own `tests` submodule calls it directly (via `super::`) with a
/// `residue` that does NOT actually prove `rel(lhs2, rhs2)`, to ask the same
/// question every other producer's corruption tests ask — does the KERNEL
/// refuse the mismatch, or only our own bookkeeping?
#[allow(clippy::too_many_arguments)]
fn glue_rel<D: NatOps>(
    d: &mut D,
    shape: Shape,
    lhs: ExprId,
    lhs2: ExprId,
    hl: ExprId,
    rhs: ExprId,
    rhs2: ExprId,
    hr: ExprId,
    residue: ExprId,
) -> ExprId {
    let hl_rev = d.symm(lhs, lhs2, hl);
    let step1 = transport_rel(d, shape, lhs2, lhs, hl_rev, rhs2, residue, true);
    let hr_rev = d.symm(rhs, rhs2, hr);
    transport_rel(d, shape, rhs2, rhs, hr_rev, lhs, step1, false)
}

fn then_simp<D: NatOps>(
    d: &mut D,
    ctx: &Ctx<'_, D>,
    second: &Tactic,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let (shape, lhs, rhs) = decide::parse_goal(d, &ctx.prelude, goal)
        .ok_or(Decline::Simp(simp::Decline::GoalNotAtomic))?;
    let (lhs2, hl) = simp::nat::normalize(d, ctx.rules, lhs).map_err(Decline::Simp)?;
    let (rhs2, hr) = simp::nat::normalize(d, ctx.rules, rhs).map_err(Decline::Simp)?;
    let new_goal = build_rel(d, shape, lhs2, rhs2);
    let residue = run(d, ctx, second, new_goal)?;
    Ok(glue_rel(d, shape, lhs, lhs2, hl, rhs, rhs2, hr, residue))
}

/// Run `tactic` on `goal`, or decline.
///
/// The returned `ExprId` is an **unchecked** proof term, as every producer
/// here returns — the caller pushes it through
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) (or
/// [`Kernel::infer`](crate::Kernel::infer)); this function adds no trusted
/// surface of its own.
///
/// # Errors
///
/// A [`Decline`] recording which producer(s) were asked and what each said.
pub fn run<D: NatOps>(
    d: &mut D,
    ctx: &Ctx<'_, D>,
    tactic: &Tactic,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    match tactic {
        Tactic::Decide => decide::run(d, &ctx.prelude, goal).map_err(Decline::Decide),
        Tactic::Linarith => {
            linarith::nat::prove(d, &ctx.prelude, ctx.assumptions, goal).map_err(Decline::Linarith)
        }
        Tactic::Ring => ring::nat::prove(d, &ctx.prelude, goal).map_err(Decline::Ring),
        Tactic::Simp => simp::nat::prove(d, &ctx.prelude, ctx.rules, goal).map_err(Decline::Simp),
        Tactic::Then(first, second) => match first.as_ref() {
            Tactic::Simp => then_simp(d, ctx, second, goal),
            _ => match run(d, ctx, first, goal) {
                Ok(term) => Ok(term),
                Err(_) => run(d, ctx, second, goal),
            },
        },
        Tactic::First(list) => {
            let mut declines = Vec::with_capacity(list.len());
            for t in list {
                match run(d, ctx, t, goal) {
                    Ok(term) => return Ok(term),
                    Err(e) => declines.push(e),
                }
            }
            Err(Decline::First(declines))
        }
    }
}

#[cfg(test)]
mod tests;
