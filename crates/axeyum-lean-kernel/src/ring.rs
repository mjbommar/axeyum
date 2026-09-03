//! `ring` — a decision procedure for commutative-ring equalities over ℕ
//! (`+`, `*`, numerals, `succ`) that **emits kernel proof terms**.
//!
//! This is the second tactic-layer producer in the sense of
//! [ADR-0601](../../../docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
//! following `linarith` ([ADR-1576](../../../docs/research/09-decisions/adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)):
//! untrusted search (here, a deterministic normal-form computation, not a
//! bounded search — the fragment has no ambiguity to search over), trusted
//! checking ([`Kernel::add_declaration`](crate::Kernel::add_declaration)).
//!
//! ## The fragment
//!
//! Goals `t₁ = t₂` where `t` is built from variables, numerals, `+`, `*`,
//! `succ`, over `Nat`. `div`, `mod` and `sub` (ℕ's truncated subtraction,
//! which is not a ring operation) are outside the fragment and decline with
//! [`Decline::NonRing`].
//!
//! ## The normal form
//!
//! Both sides are normalized to a sum of monomials — each monomial the
//! left-associated `*`-fold of its factor list **in the order the parser
//! encountered them**, each summand repeated as many times as its
//! coefficient, the whole sum sorted so equal monomials become adjacent
//! (`add_comm`/`add_right_comm`) — and the two normal forms are compared as
//! `Vec<Item>`. A monomial's *internal* factor order **is** re-sorted
//! (`sort_factors`, ring-tactic-2, ADR-1582): `x*y` and `y*x` normalize to
//! the same sorted factor-index key `[x,y]` and the procedure proves them
//! equal — the same three-step `mul_assoc`/`mul_comm`/`symm(mul_assoc)`
//! adjacent-transposition trick the outer sum's `sort_items` already uses,
//! applied to a monomial's own factor list. See [`nat::tests`] for the
//! positive test and its negative control.
//!
//! ## Why coefficients are additive, not `Nat.mul` by a numeral
//!
//! As `linarith` — every numeral in this kernel is unary, so a numeral
//! coefficient is emitted as repeated `+`, never as `Nat.mul` folded back
//! out through `left_distrib`. See [`nat`]'s module docs for the emitted-term
//! table.

#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity
)]

pub mod cost;
pub mod nat;

#[cfg(test)]
mod tests;

/// Coefficient / factor-count type, signed for symmetry with `linarith`
/// though every ℕ coefficient produced by parsing is non-negative.
pub type Coeff = i64;

/// The largest coefficient (repeated-`+` count) the emitter will unroll.
///
/// Every numeral here is unary, so a coefficient of 40 would be a term
/// forming `succ⁴⁰ zero` — decline rather than grow it. Also used as the
/// bound on a numeral-times-numeral product (`Item::Num * Item::Num`).
pub const MAX_COEFF: Coeff = 4;

/// Why the procedure produced no term.
///
/// Every variant is a *decline*: `ring` returning `Decline` says the
/// procedure did not reach a term, never that the goal is false — except
/// [`Decline::NotAnIdentity`], which the deterministic normal-form
/// computation is complete enough (within the fragment) to assert
/// positively: the two sides normalize to different monomial sums, so no
/// combination of `add_assoc`/`add_comm`/`mul_assoc`/`mul_comm`/
/// `left_distrib` can equate them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decline {
    /// The goal's shape is not `Eq Nat _ _`.
    GoalNotAtomic,
    /// A subterm is outside the ring fragment (`div`, `mod`, `sub`).
    NonRing,
    /// The two sides normalize to different monomial sums.
    NotAnIdentity,
    /// A coefficient (repeated-`+` count, or a numeral-times-numeral
    /// product) would exceed [`MAX_COEFF`].
    CoefficientTooLarge,
}
