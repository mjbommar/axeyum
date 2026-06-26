//! # axeyum-property — a typed, bounded-property SDK over the axeyum solver
//!
//! State a property over bounded integers / bit-vectors and get back one of:
//! `Proved(certificate)` · `Counterexample(typed inputs)` · `Unknown(reason)` —
//! where `Proved` carries an independently re-checked certificate (and a
//! standalone Lean module when the result is in the reconstructable fragment).
//!
//! This is a thin, type-safe shell over `axeyum-solver` builders that already
//! exist and are re-checked — it adds typing + lifting, no solver logic. See the
//! design and build plan in `docs/consumer-track/property/PLAN.md`.
//!
//! ## At a glance
//!
//! Typed handles carry their bit-vector width at the type level, so a width
//! mismatch is a *compile* error rather than z3.rs's runtime panic:
//!
//! ```rust
//! use axeyum_property::{property, Bv, Ctx, Outcome};
//!
//! let ctx = Ctx::new();
//! // For all 32-bit a, b with a, b < 2^31: a + b never wraps below a.
//! let outcome = property()
//!     .certificate(true)
//!     .forall::<(Bv<32>, Bv<32>)>(&ctx)
//!     .assuming(|(a, b)| a.ult(Bv::lit(&ctx, 1 << 31)) & b.ult(Bv::lit(&ctx, 1 << 31)))
//!     .check(|(a, b)| (a + b).uge(a))?;
//! match outcome {
//!     Outcome::Proved(cert) => {
//!         assert!(cert.verify()?);
//!     }
//!     Outcome::Counterexample((a, b)) => panic!("overflow at a={a}, b={b}"),
//!     Outcome::Unknown(reason) => eprintln!("undecided: {reason:?}"),
//! }
//! # Ok::<(), axeyum_solver::SolverError>(())
//! ```
#![forbid(unsafe_code)]

mod array;
mod bounded;
mod ctx;
mod handle;
mod property;
mod reproduce;

pub use array::BvArray;
pub use bounded::Bounded;
pub use ctx::Ctx;
pub use handle::{Bool, Bv, Int};
pub use property::{Certificate, Forall, Lifted, Outcome, PropertyBuilder, Slot, Symbolic};
pub use reproduce::{Reproduction, Witness, WitnessBinding, render_reproduction_test};

/// `#[derive(Symbolic)]` — declare a fresh symbolic value per struct field and
/// lift a model back into a typed concrete struct. See [`Symbolic`].
///
/// Lifts the arity-3 tuple ceiling: any struct of `Symbolic` fields becomes a
/// property input type, with a generated `<Name>Concrete` carrying the
/// counterexample. The struct must have exactly one lifetime parameter (the
/// [`Ctx`] borrow).
pub use axeyum_property_derive::Symbolic;

// Re-export the solver types that appear in the public surface so consumers need
// not depend on `axeyum-solver` directly for them.
pub use axeyum_solver::{EvidenceReport, SolverError, UnknownReason};

/// The entry point: a fresh [`PropertyBuilder`] with default budgets.
///
/// Chain `.timeout(..)` / `.node_budget(..)` / `.seed(..)` / `.certificate(..)`,
/// then `.forall::<T>(&ctx)` to declare symbolic inputs, `.assuming(..)` to add a
/// precondition, and `.check(..)` to decide the property.
///
/// ```rust
/// use axeyum_property::{property, Ctx, Int, Outcome};
///
/// let ctx = Ctx::new();
/// // |x| is never negative, over bounded integers.
/// let outcome = property()
///     .forall::<Int>(&ctx)
///     .assuming(|x| x.ge(Int::lit(&ctx, -1000)) & x.le(Int::lit(&ctx, 1000)))
///     .check(|x| x.abs().ge(Int::lit(&ctx, 0)))?;
/// assert!(matches!(outcome, Outcome::Proved(_)));
/// # Ok::<(), axeyum_solver::SolverError>(())
/// ```
#[must_use]
pub fn property() -> PropertyBuilder {
    PropertyBuilder::new()
}
