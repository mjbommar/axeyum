# ADR-0440: Nat congruence to zero characterizes divisibility

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 and R4.4.

## Context

ADRs 0438 and 0439 provide the two expected directions between divisibility
and congruence to zero, but the converse currently carries a positive-modulus
premise. The public characterization should quantify over every natural
modulus and must not silently discard the degenerate zero case.

## Decision

Add the zero-axiom theorem

```text
mod_eq_zero_iff_dvd : modEq d n zero <-> dvd d n.
```

Prove the forward direction by induction on `d`. For `d = zero`, eliminate the
balanced congruence witnesses `u`, `v`; simplifying
`n + zero*u = zero + zero*v` gives the exact witness equation
`n = zero*v`. For `d = succ k`, construct `Le one (succ k)` from `zero_le k`
and successor monotonicity, then apply ADR-0439. The reverse direction is
ADR-0438 for all moduli.

This keeps the zero-modulus behavior visible in the proof term. It introduces
neither executable remainder nor signed subtraction, and packages general
number-theory infrastructure rather than a theorem-client special case.

## Evidence

Checked instances cover `modEq 2 10 0 <-> 2 | 10` and the degenerate
`modEq 0 0 0 <-> 0 | 0`. NC61 changes only the divisible dividend; trusted
admission rejects the malformed characterization. The deterministic prelude
census covers 100 definitions and theorems, all under the zero-axiom audit.

## Consequences

Divisibility and congruence-to-zero facts are interchangeable without a hidden
positivity condition. The next number-theory layer can build `Acc`-based
well-founded recursion for `gcd`, Bézout, and Gauss rather than adding isolated
client lemmas.
