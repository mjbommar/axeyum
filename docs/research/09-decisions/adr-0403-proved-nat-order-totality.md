# ADR-0403: Proved Nat order totality

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R7.1.

## Context

The exact Rado witness range criterion separates the cases `a<=b` and `b<=a`.
The Nat prelude could carry individual bounds but had no checked theorem that
every pair admits one of those cases. Treating the split as metatheoretic Rust
control flow would leave it outside the checked proof term.

## Decision

Add the zero-axiom theorem

```text
le_total : forall a b, Or (Le a b) (Le b a).
```

Prove it by structural induction on both naturals. The zero branches use
`zero_le`; the successor/successor branch eliminates the recursive `Or` proof
and maps either bound through `le_succ_succ`.

## Evidence

The prelude admits and applies totality at `5` and `2`. A mutation changes one
comparison endpoint while reusing the valid proof; the trusted gate rejects
the declaration without insertion. Deterministic prelude inventory now covers
44 checked theorems and 8 definitions, with no axioms.

## Consequences

R4.1 totality is complete. Antisymmetry and `min` remain. Rado's exact signed
range biconditional can now perform its necessary order case split entirely
inside the kernel.
