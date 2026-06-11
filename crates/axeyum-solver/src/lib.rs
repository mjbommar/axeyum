//! Solver backend interface for the Axeyum automated reasoning stack.
//!
//! This crate owns the Axeyum-side solver contract: the [`SolverBackend`]
//! trait, [`CheckResult`] with `Unknown` as a first-class outcome, and
//! [`Model`]s keyed by Axeyum symbols rather than backend AST pointers.
//! Native backends are feature-gated adapters implementing this contract;
//! the default build has no C or C++ dependency (ADR-0002).
//!
//! Enable the `z3` feature for the [`Z3Backend`] oracle (system libz3 via
//! pkg-config) or `z3-static` for a hermetic prebuilt libz3. The milestone
//! M0 doctest lives on the `Z3Backend` module.
//!
//! Design notes: `docs/research/03-architecture/backend-model.md`,
//! `incrementality-and-solver-lifecycle.md`, and
//! `07-verification/evidence-and-checking.md` in the repository.

mod backend;
mod model;
#[cfg(feature = "z3")]
mod z3_backend;

pub use backend::{Capabilities, CheckResult, SolverBackend, SolverConfig, SolverError};
pub use model::Model;
#[cfg(feature = "z3")]
pub use z3_backend::Z3Backend;
