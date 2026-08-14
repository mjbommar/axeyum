# Lean Nat finite-sum congruence R4.6 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1;
[ADR-0395](../research/09-decisions/adr-0395-pointwise-congruence-for-finite-sums.md).

## Result

`Nat.sumRange_congr` checks pointwise equality over a finite range without
assuming function extensionality:

```text
(forall i, f i = g i) -> sumRange f n = sumRange g n.
```

The focused Nat run passes 11 tests. The package inventory contains six
definitions and 30 checked theorems. A positive control lifts `0+i=i` through
four summands; the fourteenth mutation control requires rejection when the
range-two proof is assigned the inferred range-three proposition. Package
determinism and the zero-axiom walk remain green.

## Boundary

This is generic finite-sum congruence. It does not itself claim the Rado
factorization or any paper theorem, and range splitting remains open.
