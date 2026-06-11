# Observability And Resource Governance

Status: draft
Last updated: 2026-06-11

## Purpose

Define how Axeyum measures itself and bounds itself. Companion to
[query-cost-control](../03-architecture/query-cost-control.md): that note
says *what* to detect and cap; this one fixes the API shape.

## Core Claims

- Telemetry is **data returned by APIs, not side-channel logs**: stats
  structs are deterministic, testable, serializable into evidence
  artifacts, and impose zero cost when ignored. A `tracing` bridge can be
  feature-gated later; the values come first.
- This serves optimization *and* safety. Optimization: every methodology
  gate is decided by layer-attributed numbers. Safety: adversarial inputs
  (obfuscated code) make quotas DoS-resistance; structured `Unknown`
  prevents reading "budget exhausted" as "unsat" (epistemic safety);
  deterministic budgets (Z3 `rlimit`-style) make failures reproducible
  evidence instead of flaky hangs.
- Term-shape metrics (`TermStats`: DAG nodes vs saturating tree nodes,
  depth, op-class counts) are the admission-control features and the
  representational-vs-search blowup discriminator.
- Budgets are part of the layer contract: `SolverConfig` carries
  wall-clock, deterministic resource, memory, and translation node
  budgets; exhaustion is `Unknown { kind, detail }`, never an error or a
  hang.

## API Shape (implemented this iteration)

- `axeyum_ir::TermStats::compute(arena, roots)` — one memoized pass:
  `dag_nodes`, `tree_nodes` (saturating u64; `u64::MAX` = "astronomical"),
  `max_depth`, `distinct_symbols`, `ite_count`, `mul_div_count`.
- `CheckResult::Unknown(UnknownReason)` with `UnknownKind`
  (`Timeout | ResourceLimit | MemoryLimit | NodeBudget | Incomplete | Other`).
- `SolverConfig { timeout, resource_limit, memory_limit_mb, node_budget }`;
  the Z3 backend maps these to solver `Params` (`timeout`, `rlimit`) and
  the global `memory_max_size` (caveat: Z3 memory cap is process-global).
- `SolveStats { translate, solve, terms_translated, assertion_count, backend }`
  exposed via `SolverBackend::last_stats()` after each check; `backend`
  carries the solver's own counters (Z3 statistics entries) as key/value
  pairs for post-mortems.

## Risks

- Stats surfaces can ossify; mark `SolveStats`/`TermStats` non-exhaustive.
- Z3's memory cap being global weakens per-query isolation; true isolation
  needs process sandboxing (a later, client-level concern).

## Open Questions

- [ ] When does a feature-gated `tracing` bridge earn inclusion?
- [ ] Should evidence artifacts embed `TermStats`/`SolveStats` snapshots by
      default or on request?

## Source Pointers

- Z3 statistics and params: https://github.com/Z3Prover/z3
- Query cost control note: ../03-architecture/query-cost-control.md
