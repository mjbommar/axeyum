# ADR-0398: Order-conditioned subtraction restoration

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1.

## Context

ADR-0397 added truncated subtraction and additive cancellation, but truncation
prevents unconditional restoration. The Rado sharpness witness needs the exact
side-conditioned law that subtracting a bounded quantity and adding it back
recovers the original natural number.

Direct induction on `Nat.le` does not align with `Nat.sub`, which recurses on
its second argument. Treating the mismatch as definitional would conceal the
main proof obligation.

## Decision

First prove the structural laws

- `sub (succ n) (succ m) = sub n m`; and
- `sub n n = 0`.

Then admit the zero-axiom checked theorem

`Nat.sub_add_cancel : forall m n, Le m n -> add (sub n m) m = n`.

Prove it by induction on `m`. In the successor case, eliminate the `Le`
derivation so its successor structure aligns with `succ_sub_succ`; transport
the outer induction hypothesis through `succ`. Do not add a decision procedure,
order axiom, or unconditional subtraction rule.

## Evidence

The focused suite admits downstream applications at the equal boundary `3<=3`
and the nontrivial bound `3<=7`, the latter supplied by checked
`le_add_right 3 4`. A mutation reuses the valid restoration proof against a
target restoring six instead of seven; the trusted gate rejects it without
insertion. The complete Nat package is eight definitions and 40 theorems,
rebuilds deterministically, and contains zero axioms.

## Consequences

The first order/subtraction bridge required by the Rado witness is checked.
R4.2 remains WIP because multiplicative cancellation and a broader
subtraction/order library remain absent. This infrastructure theorem does not
construct the witness or earn theorem credit.
