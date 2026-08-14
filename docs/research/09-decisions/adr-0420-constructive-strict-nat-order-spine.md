# ADR-0420: Constructive strict Nat order spine

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.7.

## Context

Uniqueness of relational Euclidean division compares two reconstructed
dividends. The live Nat prelude could express strict order but lacked the
transitivity, additive monotonicity, and contradiction lemmas needed to make
that comparison reusable.

## Decision

Add four zero-axiom theorems:

```text
lt_of_lt_of_le : a<b -> b<=c -> a<c
lt_of_le_of_lt : a<=b -> b<c -> a<c
lt_irrefl       : not (a<a)
add_lt_add_left : a<b -> c+a<c+b
```

Prove them from the indexed `Nat.le` recursor, successor inversion, and the
existing weak-order/addition laws. Do not introduce a comparison procedure or
classical order interface.

Store the now-larger `NatPrelude` snapshot behind internal indirection in
`PreludeValue`; this keeps the tagged cache value bounded as the public theorem
surface grows, without changing the returned copyable name table.

## Evidence

Positive controls compose the lemmas over `2<3<=5`, `2<=3<5`, and a shifted
strict inequality. Four endpoint/shift mutations are rejected without
insertion. All 19 focused Nat tests pass, the deterministic declaration census
is 77, and the prelude declares zero axioms.

## Consequences

The strict-order core is now sufficient to refute unequal Euclidean quotients
by bounding one reconstruction strictly below the other. These lemmas also
support interval, valuation, and future algorithm-correctness proofs beyond
the motivating Rado development.
