# axeyum-evm — STATUS

Live tracker for the EVM symbolic bug-hunter (App A). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — doc-scaffolded (PLAN/STATUS written).** Crate skeleton +
  `[workspace].members` entry are deferred until App B (`axeyum-property`) lands —
  A reuses B's `Certificate`/typed-term plumbing, and we add A's crate when the
  worktree git is free (avoiding an index race with B's in-flight build).
- Research confirms **unblocked**: the EVM core is QF_BV/QF_ABV; `BV256`, overflow
  predicates, symbolic array memory/storage, uninterpreted keccak, and
  `SymbolicExecutor` all already exist (see [02-research-synthesis §A](../02-research-synthesis.md)).

## Next actions (Phase 1, after B)
1. Scaffold `crates/axeyum-evm` (deps: axeyum-ir, axeyum-solver, axeyum-property).
2. Stack-machine interpreter for the must-have opcode subset → IR terms (BV256,
   `BV256→BV8` memory, `BV256→BV256` storage, symbolic calldata).
3. `SymbolicExecutor`-driven path exploration; bug = feasible REVERT/INVALID/
   `Panic(0x11)` or `bv_uaddo`/`bv_umulo`; emit replayable calldata witness.
4. A handful of overflow/assert micro-contracts as the first corpus; DISAGREE=0 gate.

## Gates / discipline
`#![forbid(unsafe_code)]`; fmt + clippy `-D warnings` + tests per increment; build
caps (`-j4`, `./scripts/mem-run.sh`); new-crate-only; DISAGREE=0 once a corpus exists.

## Changelog
- **2026-06-25** — PLAN/STATUS written; crate scaffold queued behind App B.
