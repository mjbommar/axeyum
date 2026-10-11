# ADR-6301: Farkas source binding precedes optimality credit

Status: proposed
Date: 2026-10-11

## Context

`FarkasCertificate::verify` checks its carried atom system. A true result does
not establish that those atoms encode the consumer's original constraints.
OMT no-better certificates need both source binding and checked contradiction.

## Decision

Add `verify_against_within(arena, assertions, deadline)` on the existing
certificate. Reconstruct the exact conjunctive LRA system without search,
compare variable columns, assertion origins and atom coefficients/constants/
strictness in deterministic collection order, then run existing exact arithmetic
verification. Declined collection, expired deadline, overflow and trivial-false
sources do not produce acceptance through this Farkas route. Unsupported term
linearization remains an explicit error. The optional absolute deadline belongs
to the caller's overall budget; None explicitly selects no time limit.

This shares source linearization with the producer. It is independent of proof
search, not an independently implemented parser or linearizer. Targeted guard
mutations and changed-source controls are required. Existing internal cached
certificate dispatch remains unchanged; it retains its current controls.

## First OMT integration

Retain each objective's original active context separately from its feasible
model query, which includes the current optimum pin. Build `objective > v`
for maximize or `< v` for minimize against that original context and earlier
lexicographic pins. Reuse deterministic Int-to-Real relaxation, retain the
refutation, and independently rebuild the relaxation and atom binding during
`OptimizationReport::replay_optimality`. A missing refutation returns None.
This covers integer optima whose strict-better real relaxation is infeasible;
integer-only cuts and Boolean composition remain subsequent producers.
Python gold eligibility remains disabled until this route is validated.

## Remaining work

Bind original Int-to-Real relaxation and any Boolean/theory lowering before
using this checker for OMT. Carry the original constraints, objective direction,
exact value and lexicographic prefix; check the feasible model separately.
Integrate a checked strict-better refutation, serialize source-bearing evidence,
verify from another process and mutate each binding guard privately. No gold
eligibility is granted by adding this primitive.
