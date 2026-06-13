# Incrementality And Solver Lifecycle

Status: draft
Last updated: 2026-06-13

## Purpose

Define how Axeyum models incremental solving and solver instance lifecycle.
Symbolic-execution clients issue thousands of related queries; incrementality
is where most end-to-end wall time is won or lost, yet the backend-model note
treats it only as a capability flag.

## Scope

In scope:

- Push/pop scopes, assumption literals, learned-clause reuse, instance lifecycle.

Out of scope:

- Exact Rust trait signatures.
- Parallel portfolio scheduling (see beyond-bit-blasting note).

## Core Claims

- There are two standard incrementality models: stack-based scopes (push/pop)
  and assumption literals (solve-under-assumptions). Assumptions are the more
  general primitive; scopes can be compiled onto assumptions via activation
  literals, but not vice versa.
- IPASIR is the de facto incremental SAT API (add clause, assume, solve,
  failed assumptions); the Axeyum SAT trait should be expressible as a
  superset of IPASIR so any IPASIR solver is an adapter target.
- IPASIR-UP (user propagators, as in CaDiCaL) is the modern hook for theory
  integration and guided search; the SAT trait should not preclude it.
- Failed assumptions are the poor-man's unsat core: with stable mapping from
  assumption literals to user labels, clients get explanation workflows long
  before proof support exists.
- The term arena and solver state must have independent lifetimes: terms
  outlive any one solver instance, and several solver instances may reference
  one arena.

## Implementation Status

[ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md) realizes
this model end to end (both stages, 2026-06-13):

- Stage 1: `IncrementalSat` (`axeyum-cnf`) is the warm SAT layer — monotone
  clauses, native assumptions, learned-clause reuse across solves.
- Stage 2: `IncrementalLowering` (`axeyum-bv`, persistent AIG + memo) and
  `IncrementalCnf` (`axeyum-cnf`, per-node Tseitin into the warm layer) make
  bit-blast caches survive across queries, and `IncrementalBvSolver`
  (`axeyum-solver`) is the assumptions-first `assert`/`push`/`pop`/`check`/
  `check_assuming` front end, with push/pop compiled to selector literals and
  every `sat` model replayed against the original terms.

Remaining work is performance parity (port the sparse-CNF optimizations to the
incremental encoder) and an activation-literal GC/rebuild policy, not the core
lifecycle.

## Lifecycle Model

```text
Arena (terms, sorts, symbols)        long-lived, append-only
  Query (assertions, assumptions)    cheap value object
    SolverInstance (backend state)   created from query or incrementally fed
      check() / check_assuming()
      model() / failed_assumptions()
    drop or reuse across queries
```

## Design Implications

- Design the public API assumptions-first; offer push/pop as sugar implemented
  with activation literals for backends lacking native scopes.
- The query planner should decide reuse: same instance with new assumptions,
  incremental push, or fresh instance — measured, not hard-coded.
- Do not tie term handles to a solver context lifetime. The z3.rs `'ctx`
  lifetime infecting every type was the documented cautionary example —
  upstream agreed: the z3 crate removed the lifetime-parameterized API in
  0.20 (contexts are now managed internally).
- Learned-clause and bit-blast cache reuse across related queries is a
  research topic in its own right; record per-query reuse statistics from the
  start so the payoff is measurable.

## Risks

- Backends differ in what survives pop (learned clauses, phases, activity);
  the conformance suite needs explicit tests for state retention semantics.
- Activation-literal encodings leak garbage clauses over time; instances need
  a rebuild policy.

## Open Questions

- [x] Should the first release be one-shot only, with the trait already shaped
      for assumptions (recommended), or ship incremental from day one?
  - Answer: one-shot `SolverBackend` first, with the query/façade shaped for
    assumptions, then a warm incremental SAT layer added on top — not a fork.
    See [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md)
    stage 1.
- [x] How does bit-blast caching interact with push/pop in the pure Rust path?
  - Answer: the persistent AIG/CNF (`IncrementalLowering` + `IncrementalCnf`)
    grows monotonically and is never rolled back; push/pop act purely through
    scope selector literals (assumptions), so bit-blast caches are shared across
    scopes while assertions are activated/deactivated by assumption. See
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md) stage 2.
- [ ] Should user propagators (IPASIR-UP style) be in the SAT trait v1 or a
      separate extension trait?

## Source Pointers

- IPASIR interface: https://github.com/biotomas/ipasir
- CaDiCaL (IPASIR-UP): https://github.com/arminbiere/cadical
- z3.rs context lifetimes: https://github.com/prove-rs/z3.rs
