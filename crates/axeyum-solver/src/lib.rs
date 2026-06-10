//! Solver backend interface for the Axeyum automated reasoning stack.
//!
//! This crate owns the Axeyum-side solver contract: the backend trait, the
//! result type (`Sat` / `Unsat` / `Unknown` as first-class outcomes), models
//! keyed by Axeyum symbols rather than backend AST pointers, capability
//! descriptions, and cooperative cancellation. Native backends (Z3 first,
//! behind the `z3` feature) are adapters implementing this contract.
//!
//! Design notes live in the repository under `docs/research/`, in particular:
//!
//! - `03-architecture/backend-model.md` — trait shape and capabilities.
//! - `03-architecture/incrementality-and-solver-lifecycle.md` —
//!   assumptions-first incrementality and arena/instance lifetimes.
//! - `07-verification/evidence-and-checking.md` — why every `sat` result is
//!   checked by evaluation against the original term.
//!
//! Milestone M0 (see `docs/research/09-decisions/adr-0001-vertical-slice-first.md`)
//! scopes the first real contents: the trait, the Z3 feature backend, and
//! model lifting checked by the `axeyum-ir` evaluator.

#[cfg(test)]
mod tests {
    #[test]
    fn workspace_smoke() {
        // Placeholder until M0 lands the trait; keeps the test harness wired.
        assert_eq!(2_u32 + 2, 4);
    }
}
