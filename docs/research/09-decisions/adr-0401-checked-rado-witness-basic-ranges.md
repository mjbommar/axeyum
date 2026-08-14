# ADR-0401: Checked basic ranges for the Rado sharpness witness

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R7.1.

## Context

ADR-0400 checks the paper's closed-form witness equation but deliberately
leaves membership in `[N]` separate. Proving even the unconditional part of
that membership requires reusable order monotonicity for addition and
multiplication. The upper bound `Z <= N` is different: in the paper it is the
signed coefficient condition and must not be hidden inside a weaker theorem.

## Decision

Extend the zero-axiom Nat prelude with checked left monotonicity theorems

```text
add_le_add_left : a <= b -> c+a <= c+b
mul_le_mul_left : a <= b -> c*a <= c*b.
```

For the ADR-0400 closed form, check the four universally valid bounds
`1 <= X`, `1 <= N` (hence `Y=1 <= N`), `X <= N`, and `1 <= Z`, under the
minimal positivity hypotheses needed for the latter three. Keep `Z <= N` as
an explicit side condition pending its signed arithmetic equivalence.

## Evidence

The prelude admits both monotonicity theorems by elimination on checked `Le`
derivations and retains zero axioms. Positive tests reduce `4+2 <= 4+5` and
`3*2 <= 3*5`; mutations changing the common operand or factor are rejected.

The Rado development applies all four range theorems at the paper's `k=3`
corner `a=2,b=3,n=0`, where `N=24`, `X=19`, and `Z=12`. Concrete proofs check
`19 <= 24` and the explicitly supplied `12 <= 24`. A theorem mutation from
the valid `X <= 24` target to `19 <= 18` is rejected without insertion.

## Consequences

The closed-form witness now has checked lower bounds and the complete `X,Y`
membership proof. The signed equivalence discharging `Z <= N`, followed by
the colouring argument, remains before `thm:sharp` can receive theorem credit.
