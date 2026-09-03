//! `tactic` over ℤ — [`super`]'s ℕ combinator, extended to the carrier
//! ADR-1589 cut (`tactic.rs` is `D: NatOps`-generic, and `IntDev`'s own
//! combinators are inherent methods, not a `NatOps` impl over `Int` — the
//! same non-generic choice `simp::int`/`ring::int` already made, ADR-1582/
//! ADR-1586).
//!
//! Same four producers ([`crate::decide::int`], [`crate::linarith::int`],
//! [`crate::ring::int`], [`crate::simp::int`]), same `Then`/`First`
//! algebra as [`super`]'s own module docs describe — `Then`'s two regimes
//! (`Simp` normalizes via [`crate::simp::int::normalize`] and glues the
//! residue back with `Eq.rec`/`Int.le`/`Int.lt`-generic transport; anything
//! else is sequential fallback on the SAME goal) carry over unchanged, with
//! [`IntDev::ieq_motive`]/[`IntDev::itransport`]/[`IntDev::isymm`] standing
//! in for the `NatOps` trait methods [`super`] uses.

// This whole module is exercised only by its own test suite so far (no
// production `int_prelude` retirement calls into it yet -- a follow-up
// commit in this same lane is what makes it reachable, mirroring
// `decide::int`/`decide::rat`'s own interim state). Remove once a
// retirement lands.
#![cfg_attr(not(test), allow(dead_code))]
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::IntPrelude;
use crate::decide;
use crate::decide::Shape;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::linarith;
use crate::ring;
use crate::simp;

/// The context a [`run`] needs: the prelude every producer takes, the
/// hypothesis list `linarith::int` searches over, and the rewrite set
/// `simp::int` rewrites with.
pub(crate) struct Ctx<'a> {
    /// The `Int` prelude every producer is declared against.
    pub prelude: IntPrelude,
    /// Hypotheses `linarith::int` may use — ignored by every other tactic.
    pub assumptions: &'a [linarith::int::Assumption],
    /// The rewrite set `simp::int` rewrites with — ignored by every other
    /// tactic.
    pub rules: &'a [simp::int::Rule],
}

/// A producer, or a way of composing two or more of them — see [`super::Tactic`].
pub(crate) enum Tactic {
    /// [`decide::int::run`].
    Decide,
    /// [`linarith::int::prove`].
    Linarith,
    /// [`ring::int::prove`].
    Ring,
    /// [`simp::int::prove_eq`] (via goal-parsing, see [`prove`]).
    Simp,
    /// Run the first; see [`super`]'s module docs for the two regimes.
    Then(Box<Tactic>, Box<Tactic>),
    /// Try each in order; the first success wins.
    First(Vec<Tactic>),
}

/// Why [`run`] produced no term — see [`super::Decline`].
// The payload of every variant here is read only through the derived
// `Debug` impl (diagnostic panic messages), which the dead-code lint does
// not credit as a "read" -- see the crate-root `tactic::Decline`'s own
// equivalent fields, exempt only because that enum is `pub` and reachable
// from outside the crate; this one is `pub(crate)`-nested and is not.
#[allow(dead_code)]
#[derive(Debug)]
pub enum Decline {
    /// [`decide::int::run`] declined.
    Decide(decide::Decline),
    /// [`linarith::int::prove`] declined.
    Linarith(linarith::Decline),
    /// [`ring::int::prove`] declined.
    Ring(ring::Decline),
    /// [`simp::int::prove_eq`] (or, inside a `Then(Simp, _)`, the normalizer
    /// alone) declined, or the goal was not `Eq Int` shaped.
    Simp(simp::Decline),
    /// [`Tactic::First`] tried every listed tactic and none succeeded.
    First(Vec<Decline>),
}

fn build_rel(d: &mut IntDev<'_>, shape: Shape, a: ExprId, b: ExprId) -> ExprId {
    match shape {
        Shape::Eq => d.ieq(a, b),
        Shape::Le => d.ile(a, b),
        Shape::Lt => d.ilt(a, b),
    }
}

/// `h : Eq Int from to`, `proof_at_from : rel(from, other)` (`lhs_position`)
/// or `rel(other, from)` (`!lhs_position`) ⊢ the same relation with `from`
/// replaced by `to`. See `crate::tactic::transport_rel`.
#[allow(clippy::too_many_arguments)]
fn transport_rel(
    d: &mut IntDev<'_>,
    shape: Shape,
    from: ExprId,
    to: ExprId,
    h: ExprId,
    other: ExprId,
    proof_at_from: ExprId,
    lhs_position: bool,
) -> ExprId {
    let motive = if lhs_position {
        d.ieq_motive(from, &|d, x| build_rel(d, shape, x, other))
    } else {
        d.ieq_motive(from, &|d, x| build_rel(d, shape, other, x))
    };
    d.itransport(from, motive, proof_at_from, to, h)
}

/// Glue a proof of `rel(lhs2, rhs2)` back into a proof of `rel(lhs, rhs)` —
/// see `crate::tactic::glue_rel`.
#[allow(clippy::too_many_arguments)]
fn glue_rel(
    d: &mut IntDev<'_>,
    shape: Shape,
    lhs: ExprId,
    lhs2: ExprId,
    hl: ExprId,
    rhs: ExprId,
    rhs2: ExprId,
    hr: ExprId,
    residue: ExprId,
) -> ExprId {
    let hl_rev = d.isymm(lhs, lhs2, hl);
    let step1 = transport_rel(d, shape, lhs2, lhs, hl_rev, rhs2, residue, true);
    let hr_rev = d.isymm(rhs, rhs2, hr);
    transport_rel(d, shape, rhs2, rhs, hr_rev, lhs, step1, false)
}

fn then_simp(
    d: &mut IntDev<'_>,
    ctx: &Ctx<'_>,
    second: &Tactic,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let (shape, lhs, rhs) =
        decide::int::parse_goal(d, goal).ok_or(Decline::Simp(simp::Decline::GoalNotAtomic))?;
    let (lhs2, hl) = simp::int::normalize(d, ctx.rules, lhs).map_err(Decline::Simp)?;
    let (rhs2, hr) = simp::int::normalize(d, ctx.rules, rhs).map_err(Decline::Simp)?;
    let new_goal = build_rel(d, shape, lhs2, rhs2);
    let residue = run(d, ctx, second, new_goal)?;
    Ok(glue_rel(d, shape, lhs, lhs2, hl, rhs, rhs2, hr, residue))
}

/// `Eq Int lhs rhs`, parsed and handed to [`simp::int::prove_eq`] — `simp`'s
/// own entry point only proves an already-extracted `(lhs, rhs)` pair, so
/// this is the goal-parsing wrapper `Tactic::Simp` needs, mirroring
/// `simp::nat::prove`'s shape.
fn prove(d: &mut IntDev<'_>, ctx: &Ctx<'_>, goal: ExprId) -> Result<ExprId, Decline> {
    let (shape, lhs, rhs) =
        decide::int::parse_goal(d, goal).ok_or(Decline::Simp(simp::Decline::GoalNotAtomic))?;
    if shape != Shape::Eq {
        return Err(Decline::Simp(simp::Decline::GoalNotAtomic));
    }
    simp::int::prove_eq(d, ctx.rules, lhs, rhs).map_err(Decline::Simp)
}

/// Run `tactic` on `goal`, or decline — see [`super::run`].
///
/// # Errors
///
/// A [`Decline`] recording which producer(s) were asked and what each said.
pub(crate) fn run(
    d: &mut IntDev<'_>,
    ctx: &Ctx<'_>,
    tactic: &Tactic,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    match tactic {
        Tactic::Decide => decide::int::run(d, goal).map_err(Decline::Decide),
        Tactic::Linarith => {
            linarith::int::prove(d, &ctx.prelude, ctx.assumptions, goal).map_err(Decline::Linarith)
        }
        Tactic::Ring => ring::int::prove(d, &ctx.prelude, goal).map_err(Decline::Ring),
        Tactic::Simp => prove(d, ctx, goal),
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
