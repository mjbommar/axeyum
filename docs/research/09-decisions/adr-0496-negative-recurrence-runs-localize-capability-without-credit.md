# ADR-0496: Negative recurrence runs localize capability without earning credit

Status: accepted
Date: 2026-08-19
Index-summary: Retain the one-shot Nat.fib_add_two rejection and repair equality-elimination composition before another target execution

## Context

ADR-0495 preregistered one bounded `Nat.fib_add_two` execution with two plan
templates, two kernel submissions, one executor invocation, and zero retries.
The generic iterator-successor helper passed a zero-target kernel preflight.
The target execution then rejected direct reflexivity and rejected the
helper-backed recurrence term at equality-elimination composition.

## Decision

Retain the rejection as an immutable negative observation. It earns zero
receipt, evaluation, and ledger credit, and the target stays open. Do not retry
or broaden search under the old policy.

Before preregistering another target execution, validate the exact imported
`Eq.rec` telescope and the local congruence/transitivity constructors with
target-independent synthetic controls and stage-local readable diagnostics.
Keep `Nat.fib_add_two` and the Fibonacci/GCD chain as the top-down sequence.

## Consequences

The project has localized the next capability gap without inspecting a proof
body or held-out outcome. The next increment is equality-composition tooling,
not a new theorem family or a larger proof budget. A second target run requires
a new frozen policy and independently passing microbench controls.

