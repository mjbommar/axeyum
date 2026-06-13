# ADR-0012: First Proof-Producing Pure-Rust SAT Core

Status: accepted
Date: 2026-06-13

## Context

[ADR-0011](adr-0011-drat-unsat-proof-checking.md) added a trusted DRAT checker,
but nothing produces DRAT: the `rustsat-batsat` adapter (ADR-0007) does not emit
proofs, so `unsat` is still unchecked in the pipeline. To realize the project
identity — "untrusted fast search, trusted small checking" — for `unsat`, a SAT
search that *emits a DRAT proof* is needed, which the checker then verifies.

ADR-0002 already settles that a custom SAT core is the product (the linked
adapter is scaffolding). The benchmarking methodology gates the *priority* of an
**optimized** core on SAT time dominating; that gate is about performance. This
ADR is motivated instead by **proof production / trust**, which is independent of
performance, so building a first proof-producing core now does not violate the
gate — the fast default remains `rustsat-batsat`.

The key insight: because the DRAT checker is the trusted component, the SAT core
producing the proof can be **untrusted**. A verified DRAT proof guarantees
`unsat` is sound *regardless of bugs in the search*, and `sat` is guaranteed by
model replay. So a minimal, slow, but correct core is enough to deliver
end-to-end checked results.

## Decision

Add a first pure-Rust proof-producing SAT core in `axeyum-cnf`: DPLL with
conflict-clause learning that emits a DRAT proof on `unsat`.

- On a conflict, it learns the negation of the current decision literals (a
  conflict "cube" clause), which is RUP by construction, logs it as a DRAT
  addition, and backjumps; the empty clause is learned at decision level zero,
  proving `unsat`.
- `solve_with_drat_proof(formula)` returns either a satisfying `CnfAssignment`
  or a `Vec<DratStep>` DRAT proof. The proof is verified by
  [`check_drat`](adr-0011-drat-unsat-proof-checking.md), giving end-to-end
  checked `unsat` with no trust in the search.
- This is a correctness/proof reference, **not** the performance default
  (`rustsat-batsat` stays the fast path). It is the seed of the eventual
  optimized CDCL core (1-UIP learning, watched literals, restarts), which
  remains gated by the benchmarking methodology.

## Evidence

- Conflict-cube learned clauses are RUP, so the emitted DRAT is valid by
  construction and accepted by the trusted checker; soundness of `unsat` then
  depends only on the checker, not the search.
- DPLL with clause learning is complete (the decision tree is finite and each
  learned clause excludes a decision prefix), so it terminates on small inputs.
- Tested end to end: small `unsat` formulas produce DRAT proofs that
  `check_drat` accepts; `sat` formulas produce models that satisfy the formula.

## Alternatives

- **varisat adapter** as the producer: pure Rust and proof-capable, but
  unmaintained (2019) and an external dependency; rejected as the first producer
  in favor of an in-tree core that also advances the ADR-0002 identity goal.
- **Full optimized CDCL now** (1-UIP, watched literals): the eventual target,
  but large and performance-gated; the minimal proof-producing core comes first
  and is enough for checked `unsat`.

## Implementation Progress

- 2026-06-13: first cut shipped DPLL with conflict-cube learning; it was then
  upgraded in place to **1-UIP CDCL** conflict analysis (MiniSat-style:
  reason/level tracking, trail-walk resolution to the first unique implication
  point, backjumping, asserting-literal enqueue), with a conflict budget safety
  valve (`ProofSolveOutcome::ResourceOut`). It solves e.g. pigeonhole 3→2 and
  emits a DRAT proof that `check_drat` accepts. `SatBvBackend::prove_unsat`
  drives it for high-assurance QF_BV `unsat`.
- 2026-06-13 (follow-up): added **two-watched-literal propagation**, validated by
  a 400-CNF randomized differential test against the `rustsat-batsat` adapter
  (agree on sat/unsat; `sat` models satisfy; `unsat` proofs pass `check_drat`).
  Restarts/heuristics (e.g. VSIDS) and becoming the default solver remain
  benchmarking-gated.

## Consequences

- `unsat` can be made high-assurance end to end (search → DRAT → `check_drat`),
  pure Rust, no external solver.
- A proof-checked assurance level can now be threaded through solver results
  (next step), distinguishing unchecked / DRAT-checked `unsat`.
- The core is intentionally minimal and slow; growing it into the optimized CDCL
  core, and deciding when it replaces the adapter as the default, remain future
  work under the benchmarking gate.
