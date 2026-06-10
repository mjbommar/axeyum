# Differential Testing

Status: draft
Last updated: 2026-06-10

## Purpose

Plan how to validate Axeyum against mature solvers and independent encodings.

## Scope

In scope:

- Differential tests for IR, rewrites, bit-blasting, SAT backends, and model lifting.

Out of scope:

- Specific CI matrix.

## Core Claims

- Differential testing is mandatory because solver bugs can be subtle.
- Native SMT solvers can validate Axeyum rewrites and bit-blasted encodings.
- Generated random tests should be paired with minimized regression fixtures.
- Every lowering layer needs round-trip or equivalence tests.

## Test Classes

- Sort-checking tests.
- Rewrite equivalence tests.
- Bit-blaster equivalence against native SMT.
- CNF model lifting tests.
- SAT solver DIMACS corpus tests.
- Backend conformance tests.
- Serialization round trips.
- Regression queries from real clients.

## Design Implications

- Add corpus directories early, even before full implementation.
- Store minimized failing formulas.
- Keep solver-dependent tests feature-gated.
- Build deterministic random formula generators.

## Risks

- External solvers can disagree on undefined or underspecified constructs.
- Random testing without minimization creates noisy regressions.

## Open Questions

- [ ] Should the first corpus format be SMT-LIB2 or Axeyum-native?
- [ ] Which external solver is the primary oracle?
- [ ] Should fuzzing target term builders, parsers, rewriters, or CNF encoders first?

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- cvc5: https://cvc5.github.io/
- Bitwuzla: https://bitwuzla.github.io/docs/
- SAT Competition: https://satcompetition.github.io/

