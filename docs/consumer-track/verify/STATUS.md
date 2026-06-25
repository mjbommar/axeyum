# axeyum-verify — STATUS

Live tracker for the Rust verifier (App C). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — doc-scaffolded (PLAN/STATUS written).** Crate skeleton deferred
  behind App B (reuses B's typed terms + `Certificate`) and behind App A's
  `bv_*_overflows` helper (shared). Build order: B → A → C.
- Research confirms the lowest-effort path is a **`syn` proc-macro over a restricted
  surface, not MIR** — `tests/symbolic_execution.rs` is the working template
  ([02-research-synthesis §C](../02-research-synthesis.md)).

## Next actions (Phase 1, after B + A's overflow helper)
1. Scaffold `crates/axeyum-verify` (proc-macro + lib; deps axeyum-property, axeyum-solver).
2. `syn`-parse the annotated fn body over the whitelisted subset; lower to App-B
   typed terms; emit overflow / `assert!` / `panic!` / `unwrap`-on-`Option` checks
   (+ explicit `÷0` check — BV div is SMT-total, not Rust-panic).
3. Drive `SymbolicExecutor`; output `Verified(K) | Counterexample(runnable #[test]) | Unknown`.
4. Bench ~20 Kani integer harnesses; DISAGREE=0 vs Kani on the shared subset.

## Gates / discipline
`#![forbid(unsafe_code)]`; fmt + clippy `-D warnings` + tests; build caps; new-crate-only.

## Changelog
- **2026-06-25** — PLAN/STATUS written; crate scaffold queued behind B + A's helper.
