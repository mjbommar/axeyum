//! `tactic` over ℚ — the third and last carrier this lane closes, and the
//! one with a genuinely SMALLER algebra than [`super`]/[`super::int`]'s.
//!
//! **No `Tactic::Simp` here.** `crate::simp` has no `rat` module — `Rat`'s
//! own ring normalization already lives inside [`crate::ring::rat`] itself
//! (it normalizes to a ring normal form internally, unlike `ring::nat`,
//! which only covers the ring FRAGMENT and leaves order goals to
//! `linarith`), and building a standalone `simp::rat` rewrite-chain engine
//! to feed a `Then(Simp, _)` regime is out of scope for this lane — a
//! disclosed cut, not an oversight (`simp::list` in this same lane's other
//! commit is the example of what building a new carrier from scratch
//! actually costs). [`Tactic::Then`] here is therefore ALWAYS the
//! sequential-fallback regime [`super`]'s module docs describe for "first
//! is anything else": try the first tactic, and on decline try the second
//! on the SAME goal — never a normalize-then-glue composition.
//!
//! **`Linarith` here is `crate::linarith::generic` at `Rat.orderedRing`**,
//! not a `linarith::rat` (which does not exist — `Rat` has no dedicated
//! `IntDev`-shaped linarith the way `Int` does; the generic producer over
//! an arbitrary `Alg.OrderedRing` instance, ADR-1585, is what this lane
//! found already built and unused in production). `linarith::generic::prove`
//! takes `&mut Kernel` directly (not `&mut IntDev`) plus a bundle of
//! structure names; [`linarith_generic`] assembles that bundle entirely
//! from [`RatPrelude`]'s own fields (`algebra_ext.rat_ordered_ring` is the
//! declared `Rat.orderedRing : Alg.OrderedRing` instance term,
//! `ordered_ring_ext` and `int.nat.structures` are the two structure-name
//! bundles the emitter cites) — no separate context is needed. `zero_le_one`
//! is always `None` here: every goal this lane's own retirements reach has
//! an EXACT certificate (residual `0`), which the docs on
//! `linarith::generic::prove` say needs it not at all; a goal that DOES
//! need positive slack is out of reach until a caller supplies
//! `Rat.zero_le_one` through [`Ctx`].
//!
//! **[`Tactic::Psatz`] is the NONLINEAR arm** (ADR-1649), added after the
//! three above. `linarith` decides linear order goals and declines outright on
//! a goal carrying `x*y`; [`crate::psatz::rat`] takes exactly the goals whose
//! difference is a polynomial and searches for a sum-of-squares certificate.
//! The two are complements, not a stronger and a weaker form of one producer,
//! which is why [`Tactic::First`] over both is the useful composition and why
//! `psatz` gets its OWN hypothesis list on [`Ctx`] — see that field's docs.

// This whole module is exercised only by its own test suite so far (no
// production `rat_prelude` retirement calls into it yet). Remove once a
// retirement lands.
#![cfg_attr(not(test), allow(dead_code))]
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::RatPrelude;
use crate::decide;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::linarith;
use crate::nat_prelude::NatOps;
use crate::psatz;
use crate::ring;

/// The context a [`run`] needs: the prelude every producer takes, and the
/// hypothesis list `linarith::generic` searches over.
pub(crate) struct Ctx<'a> {
    /// The `Rat` prelude every producer is declared against.
    pub prelude: RatPrelude,
    /// Hypotheses `linarith::generic` may use — ignored by `Decide`/`Ring`.
    pub assumptions: &'a [linarith::generic::Assumption],
    /// A proof of `Rat.le Rat.zero Rat.one`, when the caller has one —
    /// see the module docs on when `linarith::generic::prove` needs it.
    pub zero_le_one: Option<ExprId>,
    /// Hypotheses [`psatz::rat`] may use, each a `(statement, proof)` pair
    /// whose statement is `Rat.le Rat.zero h`.
    ///
    /// A SEPARATE list from [`Self::assumptions`], not an oversight: those are
    /// stated against the `Alg.OrderedRing` selector applications
    /// `linarith::generic` parses, and `psatz::rat` parses `Rat.le`/`Rat.add`/
    /// `Rat.mul` directly — the same terms `ring::rat` parses, because the
    /// certificate's identity goes through `ring::rat`. Sharing one list would
    /// mean one of the two producers silently seeing hypotheses it cannot read.
    pub psatz_assumptions: &'a [(ExprId, ExprId)],
    /// An optional non-SOS witness for [`psatz::rat`]; see
    /// [`psatz::DualWitness`].
    pub psatz_dual: Option<&'a psatz::DualWitness>,
}

/// A producer, or a way of composing two or more of them. No `Simp` variant
/// — see the module docs.
pub(crate) enum Tactic {
    /// [`decide::rat::run`].
    Decide,
    /// [`ring::rat::prove`].
    Ring,
    /// [`linarith::generic::prove`] at `Rat.orderedRing`.
    Linarith,
    /// [`psatz::rat::prove`] — the NONLINEAR arm. `linarith` decides linear
    /// order goals and declines a `x*y` term outright; this one takes exactly
    /// the goals whose difference is a polynomial, so the two are complements
    /// rather than a stronger and a weaker version of one thing.
    Psatz,
    /// Sequential fallback ONLY — try the first, and on decline try the
    /// second on the SAME goal. See the module docs on why there is no
    /// normalize-then-glue regime here.
    Then(Box<Tactic>, Box<Tactic>),
    /// Try each in order; the first success wins.
    First(Vec<Tactic>),
}

/// Why [`run`] produced no term.
// See `tactic::int::Decline`'s identical comment: the payload is read only
// through the derived `Debug` impl, which the dead-code lint does not
// credit.
#[allow(dead_code)]
#[derive(Debug)]
pub enum Decline {
    /// [`decide::rat::run`] declined.
    Decide(decide::Decline),
    /// [`ring::rat::prove`] declined.
    Ring(ring::Decline),
    /// [`linarith::generic::prove`] declined.
    Linarith(linarith::Decline),
    /// [`psatz::rat::prove`] declined. Two of its variants —
    /// [`psatz::Decline::NotPsd`] and [`psatz::Decline::PsdNotSos`] — are
    /// FINDINGS rather than refusals, and survive into this wrapper unchanged
    /// so a caller that cares can still read them.
    Psatz(psatz::Decline),
    /// [`Tactic::First`] tried every listed tactic and none succeeded.
    First(Vec<Decline>),
}

/// Assemble `linarith::generic::prove`'s structure-name bundle entirely
/// from `ctx.prelude`'s own fields — see the module docs.
fn linarith_generic(
    d: &mut IntDev<'_>,
    ctx: &Ctx<'_>,
    goal: ExprId,
) -> Result<ExprId, linarith::Decline> {
    let p = ctx.prelude;
    let lg = p.int.logic;
    let st = p.int.nat.structures;
    let ext = p.ordered_ring_ext;
    let nat = p.int.nat;
    let ring_name = p.algebra_ext.rat_ordered_ring;
    let k = d.kernel();
    let l1 = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let ring = k.const_(ring_name, vec![]);
    linarith::generic::prove(
        k,
        &lg,
        l1,
        &st,
        &ext,
        &nat,
        ring,
        ctx.zero_le_one,
        ctx.assumptions,
        goal,
    )
}

/// Run `tactic` on `goal`, or decline.
///
/// The returned `ExprId` is an **unchecked** proof term, as every producer
/// here returns — the caller pushes it through
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration); this
/// function adds no trusted surface of its own.
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
        Tactic::Decide => decide::rat::run(d, &ctx.prelude, goal).map_err(Decline::Decide),
        Tactic::Ring => ring::rat::prove(d, &ctx.prelude, goal).map_err(Decline::Ring),
        Tactic::Linarith => linarith_generic(d, ctx, goal).map_err(Decline::Linarith),
        Tactic::Psatz => {
            let psatz_ctx = psatz::rat::Ctx {
                prelude: ctx.prelude,
                assumptions: ctx.psatz_assumptions,
                dual: ctx.psatz_dual,
            };
            psatz::rat::prove(d, &psatz_ctx, goal).map_err(Decline::Psatz)
        }
        Tactic::Then(first, second) => match run(d, ctx, first, goal) {
            Ok(term) => Ok(term),
            Err(_) => run(d, ctx, second, goal),
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
