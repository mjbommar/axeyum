# Incrementality And Solver Lifecycle

Status: draft
Last updated: 2026-06-10

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
  lifetime infecting every type is the documented cautionary example.
- Learned-clause and bit-blast cache reuse across related queries is a
  research topic in its own right; record per-query reuse statistics from the
  start so the payoff is measurable.

## Risks

- Backends differ in what survives pop (learned clauses, phases, activity);
  the conformance suite needs explicit tests for state retention semantics.
- Activation-literal encodings leak garbage clauses over time; instances need
  a rebuild policy.

## Open Questions

- [ ] Should the first release be one-shot only, with the trait already shaped
      for assumptions (recommended), or ship incremental from day one?
- [ ] How does bit-blast caching interact with push/pop in the pure Rust path?
- [ ] Should user propagators (IPASIR-UP style) be in the SAT trait v1 or a
      separate extension trait?

## Source Pointers

- IPASIR interface: https://github.com/biotomas/ipasir
- CaDiCaL (IPASIR-UP): https://github.com/arminbiere/cadical
- z3.rs context lifetimes: https://github.com/prove-rs/z3.rs
