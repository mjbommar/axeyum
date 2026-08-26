//! Untrusted, bounded proof producers.
//!
//! These are the "propose" half of the flywheel: they search for a candidate
//! proof term and hand it back for the *same* kernel to re-check through
//! [`Kernel::add_declaration`](axeyum_lean_kernel::Kernel::add_declaration).
//! Nothing here is trusted — a producer that returns a wrong term produces a
//! kernel rejection, never an admitted theorem.
//!
//! The original two modules were promoted from `examples/*_support/mod.rs` so that the
//! library gates (`cargo test --lib`, `clippy -D warnings` on default
//! features) cover them and so the Python bindings can call them without
//! re-compiling an example.
//!
//! # Why the names stay namespaced
//!
//! Each producer defines its own budgets, candidate, and decline types, and
//! they are **different types with different variants and
//! different budgets** — `bounded_induction::MAX_BINDERS` is pinned by every
//! `mathlib-bounded-induction-family-*` manifest's reproduction contract, and
//! `check-autogenesis-bounded-induction-family.py` refuses a mismatch even
//! when every proof hash agrees. Flattening them into one namespace would make
//! two distinct reproduction contracts look like one constant, so only the
//! unambiguous entry points are re-exported below.

pub mod bounded_application;
pub mod bounded_induction;
pub mod modeq_family;

pub use bounded_application::propose_bounded_application;
pub use bounded_induction::propose_bounded_induction;
pub use modeq_family::{CircularityAudit, audit_circularity, propose_modeq_family};
