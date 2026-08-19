# ADR-0503: Checked-candidate receipts reconstruct in two fresh kernels

Status: accepted
Date: 2026-08-19
Index-summary: Receipt non-reflexive candidates by exact fixed-plan reconstruction in two fresh kernels with source and budget binding

## Context

The trace-contract theorem receipt supports only bounded reflexive source
equations. `Nat.fib_add_two` is a non-reflexive proof assembled from induction,
congruence, symmetry, and transitivity, so reusing that schema would misstate
its authority.

## Decision

Introduce a checked-candidate receipt schema that binds exact source, goal,
candidate observation, proof, declaration, operation, and budget identities.
Require empty axioms and direct theorem dependencies. Its producer-specific
driver must reconstruct the fixed accepted plan in two fresh imported kernels
and require identical independently issued receipts.

## Consequences

Non-reflexive candidates now have a reusable receipt boundary without treating
caller-supplied JSON as proof authority. Receipt replay is not new search and
does not itself admit the fact.

