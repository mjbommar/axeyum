# ADR-0419: Constructive relational Nat Euclidean division

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

R4.7 needs quotient/remainder reasoning for integer rounding, but introducing
trusted division functions would conflate computation with evidence and a
well-founded definition would first require the still-absent `Acc` prelude.
Ordinary induction on the dividend is sufficient when the result is relational.

## Decision

Define

```text
Nat.divMod d n q r := n = d*q+r and r<d
```

and prove

```text
Nat.div_mod_exists : forall d n, 1<=d -> exists q r, divMod d n q r.
```

At each successor, ADR-0418 splits `succ r<=d` into strict and equality cases.
The strict case increments the remainder; the equality case increments the
quotient and resets the remainder to zero. All witnesses are proof terms built
from the existing Nat recursion, order, and arithmetic laws.

## Evidence

The theorem produces a checked existential decomposition for five by two, and
the concrete relation `5=2*2+1` with `1<2` admits independently. A negative
control changes the dividend from five to four; declaration checking rejects
the inherited proof without insertion. All 19 focused Nat tests pass, the
deterministic declaration census is 73, and the prelude declares zero axioms.

## Consequences

Axeyum now has constructive quotient/remainder existence without host
arithmetic, classical logic, `Acc`, or an opaque quotient function. R4.7
remains partial until uniqueness and the rounding/order lemmas needed by
consumers are proved.
