# Backend Model

Status: draft
Last updated: 2026-06-10

## Purpose

Define how Axeyum should think about solver backends.

## Scope

In scope:

- Solver trait behavior, capabilities, model lifting, and backend choice.

Out of scope:

- Exact Rust trait signatures.

## Core Claims

- The backend interface should be Axeyum-owned.
- Backends should be replaceable and differential-testable against one another.
- Solver capabilities are not uniform and must be explicit.
- Incrementality, assumptions, proofs, unsat cores, and model completeness are
  optional capabilities, not implied by "solver".

## Conceptual Trait

```text
SolverBackend
  capabilities() -> Capabilities
  check(query) -> Sat | Unsat | Unknown | Error
  model() -> optional model
  unsat_core() -> optional core
  proof() -> optional proof artifact
```

## Capabilities

- Supported logics.
- Incremental push/pop.
- Assumption literals.
- Model production.
- Unsat core production.
- Proof trace production.
- Timeout/resource limits.
- Deterministic seed support.

## Design Implications

- The core result type must include `Unknown`.
- Model values must be indexed by Axeyum symbols, not backend AST pointers.
- Backends should be configured through typed option structs.
- Backend tests should share a conformance suite.

## Risks

- A lowest-common-denominator trait can hide useful backend features.
- A too-rich trait can make simple backends hard to implement.

## Open Questions

- [ ] Should solver calls be one-shot first, then incremental later?
- [ ] Should model completion be requested per query or per backend configuration?
- [ ] How should backend-specific statistics be exposed?

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- cvc5: https://cvc5.github.io/
- Bitwuzla: https://bitwuzla.github.io/docs/

