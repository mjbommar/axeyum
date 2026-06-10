//! Typed term IR for the Axeyum automated reasoning stack.
//!
//! This crate owns the core representations: sorts, symbols, terms stored as
//! an interned DAG in an arena with compact `u32` newtype IDs, typed builder
//! APIs, and the ground evaluator that serves as the executable semantic
//! reference for every other layer.
//!
//! Design notes live in the repository under `docs/research/`, in particular:
//!
//! - `04-data-structures/term-ir.md` — arena, interning, and ID design.
//! - `01-foundations/bv-semantics-and-partial-operations.md` — the SMT-LIB
//!   edge-case semantics this crate implements verbatim.
//! - `06-rust-strategy/api-design-concurrency-and-stability.md` — handle and
//!   ownership rules (lifetime-free `Copy` IDs, append-only arena).
//!
//! Milestone M0 (see `docs/research/09-decisions/adr-0001-vertical-slice-first.md`)
//! scopes the first real contents: `Bool`, `BV(n)` constants and symbols,
//! `not/and/or/xor`, `add`, `eq/ult`, `extract/concat`, `ite`, and a ground
//! evaluator.

#[cfg(test)]
mod tests {
    #[test]
    fn workspace_smoke() {
        // Placeholder until M0 lands real types; keeps the test harness wired.
        assert_eq!(2_u32 + 2, 4);
    }
}
