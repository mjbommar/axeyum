# ADR-0499: V2 rejection requires stage-local projected-equality controls

Status: accepted
Date: 2026-08-19
Index-summary: Retain the second Nat.fib_add_two rejection and infer each projected equality stage before considering v3

## Context

The v2 policy preserved the original budget and bound the corrected generic
equality controls. Those controls passed, but the sole target execution failed
with a new type mismatch during target-specific projected-equality composition.

## Decision

Retain v2 as an immutable zero-credit negative result and do not retry it.
Before any v3 policy, build a zero-submission diagnostic that separately infers
the specialized helper applications, `Prod.fst` congruence, `Prod.snd`
congruence, their transitivity term, and the final target comparison. Record
rendered and canonical expected/inferred types at every boundary.

Keep the target and strategic Fibonacci/GCD sequence unchanged. Do not widen
the proof grammar or inspect Mathlib proof bodies or held-out outcomes.

## Consequences

The flywheel advances by converting a failed theorem attempt into a reusable
typed diagnostic boundary. A v3 run is unauthorized until the exact projected-
equality mismatch is explained and its repair passes mutation-sensitive stage
controls.

