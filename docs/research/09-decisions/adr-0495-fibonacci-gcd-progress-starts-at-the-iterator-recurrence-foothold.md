# ADR-0495: Fibonacci/GCD progress starts at the iterator-recurrence foothold

Status: accepted
Date: 2026-08-19
Index-summary: Select Nat.fib_gcd for two-fact fanout but execute first on zero-dependency Nat.fib_add_two under a bounded iterator-recurrence proof plan

## Context

After the `Int.gcd_def` calibration closed the contract-to-theorem seam, the
real `Int.gcd_fib` horizon still had two open direct premises: `Int.fib_neg`
and `Nat.fib_gcd`.

Top-down, `Nat.fib_gcd` unlocks both `Int.gcd_fib` and `Nat.fib_dvd`, while
`Int.fib_neg` unlocks only the former. Bottom-up, its checked type slice has one
abstraction and 46 retained declarations, versus two and 93 for `Int.fib_neg`.
But `Nat.fib_gcd` itself needs a lower Fibonacci/GCD chain that the reviewed
ledger partially exposes.

## Decision

Select `Nat.fib_gcd` as the strategic premise, and select zero-dependency
`Nat.fib_add_two` as the immediate evaluation foothold. Follow the sequence
through `Nat.fib_coprime_fib_succ` and `Nat.gcd_fib_add_self` before attempting
`Nat.fib_gcd`.

Preregister `bounded-iterate-recurrence-v1` for the foothold with one helper
schema, two plan templates, two kernel submissions, one executor invocation,
and zero retries. Proof bodies, historical target outcomes, held-out data, and
self-reported execution credit are excluded.

## Consequences

No producer has run and no fact status changes. The next increment builds the
bounded iterator-recurrence operation against the already checked, zero-
abstraction `r080` slice. Success begins real evaluation progress; failure
identifies a proof-planning capability gap without widening the experiment.
