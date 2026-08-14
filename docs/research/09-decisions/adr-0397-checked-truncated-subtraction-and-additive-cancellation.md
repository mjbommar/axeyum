# ADR-0397: Checked truncated subtraction and additive cancellation

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1.

## Context

The Rado sharpness witness uses natural subtraction after the checked
subtraction-free factorization. The dependency report identifies truncated
subtraction and cancellation as the next real cost. Axeyum had neither a
predecessor computation rule nor cancellation facts from which to prove the
conditional subtraction laws.

## Decision

Add zero-axiom `Nat.pred` and `Nat.sub` definitions matching Lean core's
truncated recursion:

- `pred 0 = 0` and `pred (succ n) = n`;
- `sub n 0 = n` and `sub n (succ m) = pred (sub n m)`.

Admit all four computation equations as checked reflexivity theorems. Derive
`succ_injective` by congruence under `pred`, derive `add_right_cancel` by
induction on the recursive second argument of `add`, and reduce
`add_left_cancel` to right cancellation using commutativity.

## Evidence

The focused suite checks `pred 0`, `pred 4`, `7-3`, and the truncating `2-5`
computation, with a false `7-3=5` control. Downstream declarations apply
successor injectivity and both cancellation orientations. A mutation assigns
an untransported `b=c` cancellation proof to `c=b`; the trusted gate rejects
it without insertion. The complete Nat package rebuilds deterministically,
and its environment walk finds zero axioms.

## Consequences

The foundational computation and additive-cancellation half of R4.2 is
checked. R4.2 remains WIP: conditional restoration such as
`m <= n -> n-m+m=n`, subtraction/order interaction, and multiplicative
cancellation still require separate proofs. The paper theorem receives no
credit from this infrastructure increment.
