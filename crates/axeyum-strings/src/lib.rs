//! Word-level string / sequence theory for Axeyum — the Phase-B core
//! (ADR-0053).
//!
//! This crate implements the cvc5 CAV-2014 normal-form / arrangement procedure
//! over first-class `Sort::Seq` terms (ADR-0051). It depends **only** on
//! [`axeyum_ir`] — input is `Seq`-sorted [`TermId`](axeyum_ir::TermId)s over a
//! shared [`TermArena`](axeyum_ir::TermArena); output is denotation-preserving
//! rewrites (this slice) and, in later slices, verdicts + replay-checked witness
//! assignments. No solver-crate dependency, no C/C++, `forbid(unsafe_code)`,
//! WASM-clean.
//!
//! ## What is here (slice T-B.1): the normalization invariant
//!
//! [`normal_form::normalize`] is a confluent, terminating, **denotation-preserving**
//! rewrite applied before any word-level reasoning. It makes equal strings
//! syntactically comparable and is the precondition for flat/normal-form
//! computation. Its four rule families are:
//!
//! 1. **flatten** nested `str.++` trees into a canonical **right-associated**
//!    spine;
//! 2. **drop** `seq.empty` (ε) components of a concatenation;
//! 3. **fuse** a maximal run of adjacent *constant* components into a single
//!    canonical constant block (see the module docs for why this is a
//!    right-associated `seq.unit` block, not an atomic literal, in this IR);
//! 4. **push `str.len`** through concatenation and constants:
//!    `len(x ++ y) → len(x) + len(y)`, `len(const) → Int`, `len(seq.unit e) → 1`,
//!    `len(seq.empty) → 0`.
//!
//! Every rule is property-tested against the ground evaluator: on random
//! `Seq`-sorted terms and random assignments the rewritten term evaluates
//! identically to the original. The rewrite is **idempotent**
//! (`normalize(normalize(t))` interns to the same [`TermId`](axeyum_ir::TermId)
//! as `normalize(t)`).
//!
//! [`normal_form::concat_components`] exposes the flattened, ε-dropped,
//! constant-fused component view that the later flat/normal-form slices consume.

#![forbid(unsafe_code)]
#![allow(clippy::missing_errors_doc)] // this crate returns no `Result` on its public surface

pub mod normal_form;

pub use normal_form::{concat_components, normalize};
