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
- [`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md) —
  **current** scoped evidence map and ranked research program. It separates
  fragment decision parity, production Z3 replacement, certified-result
  coverage, Lean-kernel compatibility, and Lean workflow integration.
- [`generated/proof-gap-matrix.md`](generated/proof-gap-matrix.md) — generated
  per-instance/per-evidence proof pipeline: baseline UNSAT, evidence-audit
  outcome, certification, independent checking, trust holes, Lean
  reconstruction, and the exact residual blockers.
- [`generated/proof-gap-shape-census.md`](generated/proof-gap-shape-census.md) —
  source-hash-bound, parser-backed, exact-content-deduplicated census of the
  uncertified UNSAT population. It retains source syntax and reachable parsed
  IR plus bounded/string side-channel presence while refusing to infer a proof
  mechanism from operator presence alone.
- [`evidence-route-provenance-design-2026-07-21.md`](evidence-route-provenance-design-2026-07-21.md) —
  causal instrumentation design for the four bare-UNSAT exits, including the
  completed dominance-v2 population refresh and vacuous-check correction,
  measured decision-backend prevalence, stable route IDs, obligation
  fingerprints, and the gate for selecting actual proof mechanisms.
- [`lean-selected-evidence-prototype-2026-07-21.md`](lean-selected-evidence-prototype-2026-07-21.md) —
  bounded eight-row prototype showing five direct existing-consumer successes
  (including all three QF_NIA Alethe proofs through EUF) and three distinct
  quantified-BV kernel-closure, compact-spooling, and CPS-reconstruction cost
  cases measured under hard wall/memory bounds.
- [`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) —
  historical pre-neutral-baseline leverage analysis; its p4dfa premise and
  scoreboard totals are superseded by the 2026-07-21 map
  ([`gap-analysis-z3-cvc5-2026-06-22.md`](gap-analysis-z3-cvc5-2026-06-22.md)
  is the still-earlier baseline).
- [`provable-security-integration.md`](provable-security-integration.md) — how
  provable-security/game-based cryptography ideas should feed Track 5,
  proof-cookbook work, scenario corpora, and finite-field demand without
  reordering the current parity queue.
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
