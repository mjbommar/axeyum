# ADR-0438: Divisibility implies Nat congruence to zero

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 and R4.4.

## Context

The relational remainder characterization from ADR-0437 connects modular
congruence to division, but number-theory clients also need the fundamental
bridge between congruence to zero and divisibility. Its forward-from-
divisibility direction is independent of Euclidean division and should hold for
every modulus, including zero.

## Decision

Add the zero-axiom theorem

```text
mod_eq_zero_of_dvd : dvd d n -> modEq d n zero.
```

Eliminate a divisibility witness `n = d*q` and introduce balanced congruence
witnesses zero and `q`. The checked equality chain is

```text
n+d*0 = n+0 = n = d*q = 0+d*q.
```

This proof does not require positivity or an executable remainder operation and
therefore treats modulus zero by the definitions rather than by a hidden side
condition.

## Evidence

The checked proof `2 ∣ 10` now derives `modEq 2 10 0`. NC59 changes the zero
endpoint to one; the trusted admission gate rejects it. The deterministic
prelude census covers 98 definitions and theorems, and the complete environment
remains under the zero-axiom audit.

## Consequences

Every divisibility proof can be consumed as a modular fact. The converse
`modEq d n zero -> dvd d n` remains next; it needs a positive-modulus
cancellation argument plus an explicit zero-modulus branch before the full
`Iff` can honestly claim all naturals.
