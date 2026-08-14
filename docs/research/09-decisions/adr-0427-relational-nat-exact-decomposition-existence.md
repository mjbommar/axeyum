# ADR-0427: Relational Nat exact decomposition existence

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 / R4.7.

## Context

ADR-0425 characterizes a carried decomposition's zero remainder, but clients
that start from `d ∣ n` should not first request an arbitrary Euclidean
decomposition and then eliminate nested witnesses to recover an exact one.
Algorithms and number-theory proofs need a direct construction boundary.

The relational divisibility design used successfully by the Rado valuation
work already contains the quotient witness. Exact division should reuse that
witness instead of adding computation or choice.

## Decision

Add the zero-axiom theorem

```text
div_mod_exact_exists :
  1 <= d -> dvd d n -> exists q, divMod d n q 0
```

Eliminate the existential factorization, reuse its witness as the quotient,
rewrite `n=d*q` to `n=d*q+0`, and use divisor positivity as the strict
zero-remainder bound.

Do not invoke general Euclidean existence, choice, `/`, `%`, or host
arithmetic. Exact decomposition is a direct constructive consequence of the
existing divisibility witness.

## Evidence

The factorization witness for `2 ∣ 6` constructs `divMod 2 6 3 0`. NC45
changes only the dividend in the existential conclusion and the trusted
declaration gate rejects it without insertion. All 19 focused Nat tests pass,
the deterministic census is 83 definitions/theorems, and the prelude declares
zero axioms.

## Consequences

Divisibility clients can now enter the quotient/remainder API without losing
constructivity or manufacturing an arbitrary remainder first. Together with
existence, uniqueness, both order adjunctions, and ADR-0425, this supplies a
coherent foundational R4.7 interface. Relational congruence modulo a divisor is
the next number-theory layer.
