# ADR-0501: V3 is bound to all eight passing recurrence stages

Status: accepted
Date: 2026-08-19
Index-summary: Authorize one Nat.fib_add_two v3 run against the explicit right-hand bridge and unchanged search budget

## Context

ADR-0500 closed the v2 mismatch with an explicit third equality, and all eight
closed stages now infer and match the exact r080 goal without target submission.

## Decision

Authorize one v3 execution bound to tooling `a0ee2a4c9` and the exact stage-
control artifact. Preserve the existing helper, template, submission,
invocation, and retry ceilings. Continue excluding proof bodies, held-out data,
and successful historical target outcomes.

## Consequences

V3 tests the complete measured repair without widening search. Failure is
retained without retry. Success remains an uncredited candidate pending receipt
and admission.

