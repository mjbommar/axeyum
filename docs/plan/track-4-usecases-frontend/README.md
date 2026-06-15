# Track 4 — Use Cases & Frontend

The user-facing capabilities and the measurement harness: symbolic execution /
reachability over memory, an angr/unicorn-class CFG frontend, constrained
optimization, SMT-LIB command-surface completeness, and — first and most
important — the **benchmarking harness that gates all of Track 1**.

This track also owns the already-shipped reachability/symexec surface (BMC,
k-induction, certified k-induction, `SymbolicExecutor`); the phases here are what
remains around it.

## Phases

| Phase | Title | Size | Depends on | Note |
|---|---|---|---|---|
| [P4.5](P4.5-benchmarking.md) | Benchmarking & the performance gate | M | — | **do first**; gates Track 1 |
| [P4.1](P4.1-warm-lazy-memory.md) | Warm lazy arrays / symbolic memory | L | P1.4, P1.5, P2.2 (or interim eager) | unblocks fast memory BMC/symexec |
| [P4.2](P4.2-symexec-cfg.md) | Symbolic-execution CFG frontend (angr/unicorn-class) | XL | P4.1 | binary lift + CFG + memory model |
| [P4.3](P4.3-optimization.md) | Optimization: OMT lexicographic/Pareto + MILP hardening | M | — | constrained program optimization |
| [P4.4](P4.4-smtlib-surface.md) | SMT-LIB command-surface completeness | M | — | declare-sort, reset, get-proof, set-option |

## Order
**P4.5 immediately** (nothing in Track 1 is "done" without the measured Z3
head-to-head). Then P4.3 / P4.4 any time (independent). P4.1 once the Track 1
keystones + lazy arrays (P2.2) land — it makes memory BMC/k-induction/symexec
warm. P4.2 (the angr/unicorn-class frontend) is the multi-month capstone of the
symbolic-execution use case, built on P4.1.

Reference reading: [`../references/axeyum-current-state.md`](../references/axeyum-current-state.md)
(performance numbers, symexec status), and the project's existing
`docs/research/08-planning/benchmarking-and-performance-methodology.md`.
