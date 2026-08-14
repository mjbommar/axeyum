# ADR-0394: Checked scalar distribution over finite sums

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

After ADR-0393 reindexed powers from `[0,n)` to `[1,n]`, the next algebraic
step in `../axeyum-rado-paper` factors a common `a` through the finite power
sum in `thm:sharp`. Proving that step directly inside a paper-shaped theorem
would duplicate a general induction and leave other mathematical consumers
without finite-sum distribution.

## Decision

Add the zero-axiom checked theorem

`Nat.mul_sumRange : forall a f n,
  a * sumRange f n = sumRange (fun i => a * f i) n`.

Quantify over an arbitrary `Nat -> Nat` summand. Prove the empty case by
definitional reduction and the successor case using `left_distrib` plus the
induction hypothesis. Keep this generic theorem separate from
`mul_sumRange_pow`, which records the power-specific reindexing.

## Evidence

The focused Nat suite admits and applies the theorem to three times the
identity sum over `[0,4)`, whose left side computes to 18. A mutation control
assigns the valid scalar-two proof to the inferred scalar-three proposition
and requires trusted-gate rejection without insertion. The inventory checks
the theorem kind, package determinism, and a zero-axiom environment.

## Alternatives

A `thm:sharp`-specific induction was rejected because scalar distribution is
not paper-specific. A theorem over only powers was rejected because ADR-0393
already owns power reindexing and would still leave general sum algebra absent.

## Consequences

Downstream developments can move a scalar across any finite Nat sum without
new trusted assumptions. The exact sharpness factorization still needs
pointwise/congruence reasoning for scaled powers and ordinary additive
normalization; no paper theorem is credited here.
