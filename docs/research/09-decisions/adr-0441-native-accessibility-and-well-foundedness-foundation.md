# ADR-0441: Native accessibility and well-foundedness foundation

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 and Q2.

## Context

R4.8 requires `gcd`, Bézout, and Gauss without axiomatizing their mathematical
content. The kernel already admits and mutation-tests the indexed,
higher-order recursive shape used by accessibility predicates (ADR-0353), and
official pre-elaborated well-founded fixtures already replay through the
generated recursor. The native logical prelude nevertheless exposed neither
`Acc` nor `WellFounded`, so general library code could not use that capability.

The Rado development made the cost boundary concrete: ordinary Nat induction
was enough for closed-form algebra, while the necessity proof stopped at the
reusable Euclidean/Gauss layer. A fuelled or Rado-specific recursion wrapper
would preserve that library gap rather than close it.

## Decision

Extend the zero-axiom logical prelude with the universe-polymorphic declarations

```text
Acc.{u} {alpha : Sort u} (r : alpha -> alpha -> Prop) : alpha -> Prop
Acc.intro : (forall y, r y x -> Acc r y) -> Acc r x
WellFounded r := forall x, Acc r x.
```

Generate `Acc.rec` through the existing trusted inductive gate. Keep `Acc` at
the general logical layer rather than tying it to Nat, division, or a specific
algorithm. `WellFounded` is a reducible checked definition. Native source
termination elaboration remains a separate frontend concern; this decision
only exposes the core proof objects and eliminator needed by hand-built or
reconstructed terms.

## Evidence

The generated recursor has two parameters, one index, one constructor minor,
and large elimination. A checked empty-relation witness is eliminated by
`Acc.rec` into `Prop`, and iota reduction reaches the selected minor. The same
test checks that `WellFounded` unfolds to pointwise accessibility and that a
proof at one index cannot be admitted at another. Two fresh kernels render the
four public declarations byte-identically. The complete logical environment
contains zero axioms, and the real Lean 4.30 replay gate independently admits
the exported environment.

## Consequences

Axeyum now has the general accessibility predicate required for well-founded
algorithms. It does not yet have a reusable `WellFounded.fix`, a decreasing
Nat relation proof, or `gcd`; those remain explicit next dependencies. The next
increment should define and compute a generic checked fixpoint before any
number-theory function is built on it.
