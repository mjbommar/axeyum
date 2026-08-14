# ADR-0435: Shift relational Nat division by a divisor multiple

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

ADR-0434 maps equal relational Euclidean remainders to congruence. Its converse
must compare two decompositions after a balanced `modEq` witness has shifted
each dividend by a possibly different multiple of the modulus. Encoding that
algebra inside the converse would hide a reusable division law and repeat work
in later modular algorithms.

## Decision

Add the zero-axiom theorem

```text
div_mod_add_multiple :
  divMod d n q r -> divMod d (n+d*k) (q+k) r.
```

Eliminate the relational conjunction, preserve its `r < d` proof, and rebuild
the decomposition equation using checked additive regrouping and left
distribution:

```text
n+d*k = (d*q+r)+d*k = (d*q+d*k)+r = d*(q+k)+r.
```

No positivity hypothesis is added: any supplied `divMod` relation already
contains the strict remainder bound, including the fact that no modulus-zero
instance can be constructed.

## Evidence

The concrete relation `5 = 2*2+1` shifts by three divisor multiples to
`11 = 2*5+1`. NC56 changes the shifted quotient from five to four; the trusted
admission gate rejects it. The deterministic census now covers 95 definitions
and theorems, and the whole environment remains covered by the zero-axiom audit.

## Consequences

Relational division is closed under adding divisor multiples without an
executable quotient operation. The converse modular-remainder bridge can now
shift both decompositions to the one balanced dividend supplied by `modEq`,
transport one relation across the witness equation, and reuse
`div_mod_unique` rather than rebuilding its order proof.
