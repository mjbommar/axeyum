# ADR-0446: Computational Nat equality for constructive algorithms

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R3 and R4.7.

## Context

ADR-0419--0445 establish relational Euclidean division, congruence, and a
computing well-founded-recursion stack. Selecting executable quotient and
remainder values still requires a constructive branch condition. The logic
prelude deliberately has no `Decidable` or classical choice, and a proof-level
`Or` cannot be eliminated into computational data.

Pinned Lean 4.30 likewise branches inside its division model on decidable Nat
conditions. Axeyum needs the smaller underlying capability first: a Boolean Nat
equality test connected exactly to propositional equality.

The Rado development supplied the design lesson, not the target-specific API.
Its case analysis and Bezout witness were authored outside the kernel, and the
machine returned `unknown` where reusable library structure was absent. Hiding
an unproved Rust comparison inside a division generator would repeat that
boundary; the branch itself must be checked and reusable.

## Decision

Add the reducible definition

```text
Nat.beq : Nat -> Nat -> Bool
```

by structural recursion on the first operand, returning a `Nat -> Bool` row.
The successor row consumes the induction hypothesis on both predecessors. No
self-reference, host comparison, literal fast path, axiom, or Prop-to-Type
elimination is involved.

Add checked theorems:

```text
Nat.beq_refl           : forall n, beq n n = true
Nat.eq_of_beq_eq_true  : forall a b, beq a b = true -> a = b
Nat.beq_eq_true_of_eq  : forall a b, a = b -> beq a b = true
Nat.beq_eq_true_iff    : forall a b, beq a b = true <-> a = b
```

The soundness proof performs nested Nat induction. Constructor-mismatch cases
derive `False` by transporting `True.intro` through an assumed
`Bool.false = Bool.true`; successor equality follows by congruence. Completeness
is equality transport from reflexivity.

## Evidence

Closed controls reduce `beq 0 0` and `beq 2 2` to true, and both `beq 2 3`
and `beq 3 2` to false. The reflection theorem turns the checked Boolean proof
at two into propositional `2 = 2`. A mutation claiming `beq 2 3 = true` by
reflexivity is rejected with `DeclarationValueMismatch`.

The definition and four theorems join promised-name, deterministic-render,
zero-axiom, strict Clippy, and pinned Lean 4.30 replay gates.

## Consequences

Nat algorithms can now branch constructively and later justify each branch in
proofs. This increment does not itself define division or satisfy R4.7. The next
step is one structurally recursive quotient/remainder state, shared by both
projections, followed by a theorem connecting the computed values to the
existing `Nat.divMod` relation.
