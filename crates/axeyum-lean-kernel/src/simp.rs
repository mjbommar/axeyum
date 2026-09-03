//! `simp` — a rewrite-chain producer: apply an oriented rewrite set to both
//! sides of a goal to a fixed point, closing `Eq lhs rhs` when the two sides
//! converge to the same normal form.
//!
//! This is the third tactic-layer producer in the sense of
//! [ADR-0601](../../../docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
//! following `linarith`
//! ([ADR-1576](../../../docs/research/09-decisions/adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md))
//! and `ring`
//! ([ADR-1580](../../../docs/research/09-decisions/adr-1580-a-second-tactic-lands-and-its-own-primitives-cannot-be-its-targets.md),
//! [ADR-1582](../../../docs/research/09-decisions/adr-1582-the-ring-producer-over-int-and-rat-and-what-each-carrier-costs-it.md)):
//! untrusted search — outermost-first first-order matching against an
//! oriented rewrite set, no higher-order matching, to a [`MAX_STEPS`] fixed
//! point — trusted checking
//! ([`Kernel::add_declaration`](crate::Kernel::add_declaration)).
//! [ADR-1586](../../../docs/research/09-decisions/adr-1586-a-third-producer-decides-rewrite-chains-and-confluence-is-the-boundary.md)
//! records this producer's own retirement/dispatch/contract story.
//!
//! ## The rewrite set
//!
//! A [`nat::Rule`] (and its ℤ/`List` analogues) pairs a previously-declared
//! lemma `∀ …, Eq lhs(…) rhs(…)` with an [`Orientation`]:
//! [`Orientation::Forward`] rewrites an LHS-shaped subterm to its RHS,
//! [`Orientation::Backward`] the reverse (`d.symm` on the lemma's own
//! instance — the lemma is *never* restated backward). A rule's pattern is
//! never read off the kernel's stored `Pi`-type; it is a stateless `build`
//! closure returning the lemma's LHS/RHS over `arity` fresh pattern
//! variables — exactly the "prove generically, apply concretely" convention
//! `NatOps::try_theorem` / `ring::nat::prove_eq_at` already establish, so no
//! new kernel-introspection machinery is needed.
//!
//! A caller's rewrite set is the per-carrier *default* set (the
//! identity/annihilator/defining laws with no side condition — see
//! [`nat::default_rules`]) plus whatever extra rules that one call supplies
//! (see [`nat::with_extra`]) — e.g. a single defining equation like
//! `List.append_nil`, or `Nat.right_distrib` for a goal whose shape needs
//! one distribution step.
//!
//! ## Matching
//!
//! First-order, over the kernel's own `ExprId` graph: a rule's pattern is
//! built once per attempt by instantiating its `build` closure with fresh
//! `FVar`s that never occur in the goal, then walked against a candidate
//! subterm structurally (`Const`/`App` equality; a pattern `FVar` binds on
//! first occurrence and must repeat the SAME matched `ExprId` on every later
//! occurrence — `Nat.sub_self`'s `n` used twice on the LHS is exactly this
//! case, and the consistency check is the only place that distinguishes it
//! from an unconstrained pattern). No higher-order unification and no
//! delta-unfolding of a `Definition` head — a goal built from a compound
//! defined operation (`Nat.dist`, `Nat.lcm`, …) is out of reach exactly as
//! `div`/`mod`/`sub` are out of `ring`'s fragment, and the procedure
//! declines rather than silently unfolding something a caller did not ask
//! for.
//!
//! ## Traversal, and why some rules can never terminate here
//!
//! Outermost-first: try every rule at the current node; on the first match,
//! rewrite there. Only when nothing matches at a node does the search
//! descend into its immediate `App` children, lifting a child rewrite back
//! up through the carrier's own one-hole-context congruence combinator
//! (`NatOps::congr` for ℕ) — the same position mechanism `linarith`/`ring`
//! already use for their `reassoc`-shaped steps.
//!
//! This makes the fixed point CONFLUENT and TERMINATING only for a rule set
//! whose every pattern requires a specific literal subterm (a numeral, or
//! one operand's own head symbol) that the rule's own output never
//! reintroduces — every default rule below has this shape, and each
//! strictly reduces a Nat's `succ`-depth or removes an annihilated operand,
//! so a default-only run always halts. **A commutativity law
//! (`add_comm`/`mul_comm`) does not have that shape**: its LHS pattern
//! `op a b` matches *any* application of `op`, including its own output, so
//! once such a rule is in the set the very first `add`/`mul` node left
//! anywhere in the term is rewritten back and forth forever. That is not a
//! bug to work around — it is the reason `add_comm`/`mul_comm`/
//! `add_assoc`/`mul_assoc` are never in a default set here, and why the
//! looping-rule-set test below exists: a caller who supplies one of them
//! anyway gets [`Decline::BudgetExceeded`] at [`MAX_STEPS`], never a
//! hang. A one-directional defining/distribution law (`right_distrib`,
//! `succ_mul`, …) is fine as an extra rule as long as the goal's operands
//! are not themselves built from the pattern's own head shape — the budget
//! is the safety net for the cases where that is not obviously true.
//!
//! ## Emission
//!
//! Every step's proof is `d.lemma(rule.name, matched_args)` (optionally
//! `d.symm`'d for [`Orientation::Backward`]), lifted to its position by the
//! carrier's `congr`, and the whole run is `chain`'d into one `Eq.trans`
//! spine per side; the two sides' spines are joined at their shared normal
//! form with one final `trans`/`symm`. Kernel-checked like every other
//! producer here — the procedure's own "did both sides converge" check is
//! not trusted, see [`nat::prove_eq_unverified`].

#![allow(clippy::type_complexity)]

pub mod cost;
pub(crate) mod int;
pub(crate) mod list;
pub mod nat;

#[cfg(test)]
mod int_tests;

#[cfg(test)]
mod tests;

/// The largest number of rewrite steps applied to ONE side of a goal before
/// declining [`Decline::BudgetExceeded`] rather than looping forever —
/// see the module docs on why a rule set containing a bare commutativity law
/// never reaches a fixed point.
pub const MAX_STEPS: usize = 32;

/// Which way a rule rewrites: [`Forward`](Orientation::Forward) turns an
/// LHS-shaped subterm into its RHS; [`Backward`](Orientation::Backward) the
/// reverse, via `symm` on the lemma's own (never restated) instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Orientation {
    /// Rewrite an LHS-shaped subterm to the lemma's RHS.
    Forward,
    /// Rewrite an RHS-shaped subterm to the lemma's LHS, via `symm`.
    Backward,
}

/// Why the procedure produced no term. Shared across every carrier
/// (`nat`/`int`/`list`), exactly as `ring::Decline` and `linarith::Decline`
/// are shared across their own carrier submodules.
///
/// Every variant is a *decline* in the same sense as those two:
/// [`Decline::GoalNotAtomic`] and [`Decline::NoProgress`] and
/// [`Decline::BudgetExceeded`] say only that this producer did not reach a
/// term; [`Decline::SidesDiffer`] is the one *positive* decline — the two
/// sides reached distinct fixed points under this rewrite set, so no
/// further rewriting under exactly this set can equate them (an
/// incompleteness bound relative to the set, not "search exhausted").
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decline {
    /// The goal's shape is not `Eq <carrier> _ _`.
    GoalNotAtomic,
    /// Neither side of the goal matched any rule in the set even once.
    NoProgress,
    /// One side of the goal needed more than [`MAX_STEPS`] rewrite steps to
    /// reach a fixed point (another rewrite was still available at the cap).
    BudgetExceeded,
    /// Both sides reached a fixed point under this rewrite set, and the two
    /// fixed points are different terms.
    SidesDiffer,
}
