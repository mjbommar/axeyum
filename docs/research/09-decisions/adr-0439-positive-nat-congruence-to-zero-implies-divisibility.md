# ADR-0439: Positive Nat congruence to zero implies divisibility

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 and R4.4.

## Context

ADR-0438 maps divisibility to congruence to zero for every natural modulus.
The converse must recover an ordinary multiplicative witness from the balanced
witnesses used by `modEq`. For a positive modulus this is exactly the existing
checked additive-divisibility cancellation principle; no executable remainder
or signed subtraction is needed.

## Decision

Add the zero-axiom theorem

```text
dvd_of_mod_eq_zero_of_pos : Le one d -> modEq d n zero -> dvd d n.
```

Eliminate balanced witnesses `u`, `v` and simplify their equation to
`n+d*u=d*v`. The right witness proves `d | n+d*u`, while `dvd_mul` proves
`d | d*u`. Commute the sum and apply `dvd_add_right_cancel_of_pos` to recover
`d | n`.

The positivity premise is explicit because cancellation at modulus zero would
be unsound. The theorem remains relational and reuses the general arithmetic
API rather than introducing a remainder operator or a client-specific wrapper.

## Evidence

The positive path derives `2 | 10` from a checked proof of `modEq 2 10 0`.
NC60 changes the target dividend from ten to eleven; trusted admission rejects
the malformed proof term. The deterministic prelude census covers 99
definitions and theorems, and the complete environment remains under the
zero-axiom audit.

## Consequences

Positive-modulus clients can move in both directions between divisibility and
congruence to zero. A full all-Nat `Iff` still requires an explicit modulus-zero
branch; that branch remains next rather than being hidden behind a stronger
premise.
