# docs/plan/ — the end-to-end plan

This folder is the full engineering plan to take axeyum to **Z3 + Lean parity**.
It is intentionally long and built to be followed task-by-task over weeks/months.

Start at the root [`PLAN.md`](../../PLAN.md) (map + standing rules) and
[`STATUS.md`](../../STATUS.md) (live state). Then this folder.

## Layout

- [`00-north-star.md`](00-north-star.md) — the definition of "done" for Z3 parity
  and Lean parity; the sizing and status legends used everywhere.
- [`01-dependency-dag.md`](01-dependency-dag.md) — the cross-track dependency DAG,
  the two keystones, the critical paths, and the recommended execution order.
- [`gap-analysis-z3-cvc5-2026-06-22.md`](gap-analysis-z3-cvc5-2026-06-22.md) —
  current practical gap analysis against Z3/cvc5, with concrete next increments.
- [`track-1-engine/`](track-1-engine/README.md) — Engine & Performance.
- [`track-2-theories/`](track-2-theories/README.md) — Theories & Breadth.
- [`track-3-proof-lean/`](track-3-proof-lean/README.md) — Proofs & Lean.
- [`track-4-usecases-frontend/`](track-4-usecases-frontend/README.md) — Use Cases
  & Frontend.
- [`track-5-verified-systems/`](track-5-verified-systems/README.md) — Verified
  Systems (IR reflection): the seL4-inspired application trajectory — reflect
  compiled Rust (MIR + LLVM IR) into the solver, discharge panic-freedom /
  memory-safety / constant-time / equivalence / protocol obligations
  push-button with certificates (adopted by
  [ADR-0056](../research/09-decisions/adr-0056-verified-systems-track.md)).
- [`references/`](references/README.md) — the distilled top-down review of the
  reference solvers this plan is built on (Z3, cvc5, bitwuzla, CaDiCaL, Kissat,
  Carcara, lean4, nanoda_lib, lean-smt, drat-trim).

## Conventions

- **Phase IDs** are `P<track>.<n>` (e.g. `P1.4`). **Task IDs** are
  `T<track>.<n>.<m>` (e.g. `T1.4.2`).
- Each phase file has: **Goal**, **Why / leverage**, **Dependencies**,
  **Tasks** (a table: id, task, key references, size, exit), **Phase exit
  criteria**, and **References**.
- Reference file paths are given relative to the repo root (e.g.
  `references/z3/src/sat/sat_solver.cpp`) so they are clickable and exact.
- **Sizing:** `S` ≈ ≤2 days · `M` ≈ ~1 week · `L` ≈ ~2–4 weeks · `XL` ≈ multi-month.
- **Status:** `TODO` / `WIP` / `DONE` / `BLOCKED` (tracked in
  [`STATUS.md`](../../STATUS.md), not duplicated here).

## Principles carried from the project identity

- **Untrusted fast search, trusted small checking.** Every new `unsat` route
  either gets an independent checker or is recorded in the
  [trust ledger](track-3-proof-lean/P3.0-trust-ledger.md) as an explicit,
  countable trust assumption — never an implicit gap.
- **Measure before tuning.** Performance phases are gated by the benchmarking
  harness ([P4.5](track-4-usecases-frontend/P4.5-benchmarking.md)); we change one
  thing and re-measure against Z3 on a committed slice.
- **Eager → lazy is the recurring upgrade.** Most theories work today by eager
  one-shot reduction; parity means moving them onto the incremental
  e-graph + CDCL(T) loop. That loop is the keystone (Track 1).
