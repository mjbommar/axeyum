# ADR-0404: Order witnesses and additive reflection

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.2 / R7.1.

## Context

The exact Rado witness range criterion requires algebraic rearrangement of
inequalities, not only forward monotonicity. After ADR-0403, the prelude can
split any pair by order, but it cannot expose the additive distance carried by
a `Le` derivation or remove a common additive prefix. Hard-coding those steps
in the Rado development would duplicate a foundational Nat order interface.

## Decision

Add three zero-axiom theorems:

```text
le_intro                 : a+k=b -> a<=b
le_dest                  : a<=b -> Exists (fun k => a+k=b)
le_of_add_le_add_left    : c+a<=c+b -> a<=b.
```

`le_dest` eliminates the checked `Le` derivation and advances its existential
offset at every `Le.step`. Additive reflection eliminates that witness, uses
associativity plus checked equality cancellation to remove `c`, then rebuilds
the unshifted order proof with `le_intro`.

## Evidence

The downstream test round-trips `2<=5` through an existential offset and
reflects `4+2<=4+5` back to `2<=5`. NC21 changes the reconstructed upper
endpoint; NC22 changes an endpoint after prefix reflection. The trusted gate
rejects both without insertion. The deterministic inventory contains 47
theorems and 8 definitions, with zero axioms.

## Consequences

The Nat order layer now supports witness-style algebra and additive inequality
cancellation. Positive-factor multiplicative order cancellation remains the
next reusable dependency for the paper's exact scaled range biconditional.
