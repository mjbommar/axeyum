# ADR-0444: Generic accessibility predecessor elimination

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 and Q2.

## Context

ADR-0441--0443 provide `Acc`, `WellFounded`, and a generic checked fixpoint,
but clients cannot yet extract `Acc r y` from `Acc r x` and `r y x` without
assembling an `Acc.rec` motive themselves. Pinned Lean 4.30 uses precisely this
operation, `Acc.inv`, in its proof that Nat strict order is well-founded and in
later closure constructions.

The Rado route-C attempt stopped where reusable Euclidean and Gauss machinery
was absent. Hiding predecessor extraction inside a Nat-only proof would repeat
that failure mode: measure, inverse-image, lexicographic, and algorithm-specific
relations all need the same accessibility operation.

## Decision

Add the zero-axiom, universe-polymorphic theorem

```text
Acc.inv.{u} :
  forall {alpha : Sort u} {r : alpha -> alpha -> Prop} {x y : alpha},
    Acc r x -> r y x -> Acc r y.
```

Prove it by `Acc.rec` with motive

```text
fun x _ => forall y, r y x -> Acc r y
```

and constructor minor `fun _ field _ y h => field y h`. The induction
hypothesis is generated and checked but intentionally unused: the constructor's
recursive field already contains the immediate predecessor accessibility.

## Evidence

The application control uses distinct `Bool.true` and `Bool.false` indices, an
abstract accessible source, and a relation proof selecting the false index.
The kernel infers the result as accessibility of that predecessor. A theorem
mutation that changes the result back to the source index is rejected with
`DeclarationValueMismatch`. The declaration joins promised-name,
deterministic-render, zero-axiom, and pinned Lean 4.30 replay gates.

## Consequences

Any checked well-founded relation can now expose accessibility of a related
predecessor without rebuilding the eliminator. This still does not establish
that Nat strict order is well-founded; that proof is the next increment and
will use the general theorem rather than a private Nat-specific substitute.
