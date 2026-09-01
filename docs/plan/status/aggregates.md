# Lane: aggregates

**Status:** active — investigating what the right finite-aggregate representation is
for this kernel (`List` vs `Nat.Fin`-indexed function-plus-bound vs `Prod`), and
whether determinant multiplicativity (ADR-1135) is blocked by the aggregate or by
something deeper.

## Question

Several documents state as a LAW that "this kernel has no `List`/`Finset`/`Prod`,
so a finite family is a function plus a bound". That is an INVENTORY, not a law:
`Nat.Pair` and `Nat.Primrec` were both declared on 2026-08-30/31, so this kernel
adds inductives routinely.

## Next actions

- Measure the current inductive inventory and what an inductive costs in the
  trust accounting (`axiom_footprint`, `check-trust-closure`, `nat_axiom_inventory`).
- Establish precisely what `Nat.Fin`-indexed function-plus-bound cannot express
  that the blocked determinant proofs need.
- Decide, record in an ADR, and correct every document stating the absence as a law.

## Landed changes

_(none yet)_
