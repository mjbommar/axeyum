# ADR-0504: Semantic receipt precedes Fibonacci ledger admission

Status: accepted
Date: 2026-08-19
Index-summary: Accept the two-kernel Nat.fib_add_two receipt but keep the fact open until ordinary registered admission

## Context

The fixed v3 plan reconstructed identically in two fresh kernels and issued an
exact source- and budget-bound receipt with no axioms or theorem dependencies.
No admission operation or ledger transaction ran.

## Decision

Accept the semantic theorem receipt as candidate evidence while retaining zero
evaluation and ledger credit. Register an exact receipt-consuming operation and
use the existing crash-safe prepare/apply protocol before changing the fact.

## Consequences

Proof construction and receipt replay are complete. Durable knowledge remains
a separate, recoverable state transition, after which child eligibility must be
derived rather than asserted.

