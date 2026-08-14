# Lean Nat subtraction and cancellation result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1;
[ADR-0397](../research/09-decisions/adr-0397-checked-truncated-subtraction-and-additive-cancellation.md).

## Result

The zero-axiom Nat prelude now contains checked predecessor and truncated
subtraction computation plus `succ_injective`, `add_right_cancel`, and
`add_left_cancel`. The proofs use only the existing inductive Nat recursor,
equality transport, and checked additive laws.

The focused suite covers truncating and non-truncating closed computation,
downstream reuse of all three cancellation dependencies, a false reduction,
and a trusted-gate rejection for a cancellation proof assigned to the wrong
equality orientation. The deterministic package inventory is now eight
definitions and 37 theorems.

## Boundary

R4.2 is not complete. Conditional subtraction restoration, its order bridge,
and multiplicative cancellation remain. This increment does not construct the
`thm:sharp` witness or earn theorem credit. Publication and hosted CI are not
claimed from local evidence.
