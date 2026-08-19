# ADR-0500: Fibonacci recurrence needs an explicit right-hand bridge

Status: accepted
Date: 2026-08-19
Index-summary: Bridge snd(iter n) to fib(n+1) by reversed fst-helper congruence before composing the recurrence target

## Context

The stage-local control required by ADR-0499 showed that both helper
specializations and both projection congruences infer. The `snd` projection
ends at `fib n + snd (iterate n)`, while the target ends at `fib n + fib
(n+1)`. Those expressions are propositionally equal through another projection
of the helper, not definitionally equal.

## Decision

Project the iterator helper through `fst`, reverse the resulting equality with
a locally constructed `Eq.rec` symmetry term, lift it through right-addition,
and compose that bridge after the first two equalities. Require all eight
closed stages to infer and match before any target submission.

Treat the added bridge as part of the same recurrence plan template, but bind
its exact stage identities in any future v3 policy.

## Consequences

The complete proof term now matches the exact target type without being
submitted as a theorem. This closes the measured v2 gap while preserving the
zero-submission diagnostic boundary. V3 remains a separately preregistered
one-shot evaluation.

