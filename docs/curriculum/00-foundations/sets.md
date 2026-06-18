# Sets

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: BV / enumeration (finite sets) · status: `covered`

## What it is

Collections of objects, with **membership** (∈), **subset** (⊆), and the
operations **union** (∪), **intersection** (∩), **complement**, and **power
set**. The ambient language (informally, ZFC) in which modern mathematics is
built.

## Role in the tour

The universal substrate: numbers, relations, functions, and structures are all
*defined as* sets. The set identities (distributivity, De Morgan for sets) are
the same Boolean laws as in propositional logic, one level up — a nice place to
show that connection.

## Prerequisites

- [Propositional Logic](propositional-logic.md) — `x ∈ A ∩ B ⟺ x ∈ A ∧ x ∈ B`.

## Unlocks

- [Relations & Functions](relations-and-functions.md)
- [Predicate Logic](predicate-logic.md)
- [Natural Numbers (Peano)](../01-number-systems/naturals.md)

## Testable in axeyum

Over a **finite universe**, a set is a bit-vector (one bit per element), and the
set operations are bitwise operations. Set identities then become bit-vector
identities, exhaustively checkable — the same machinery as the bitwise-identity
family.

Example exercise: encode subsets of a 4-element universe as `BitVec(4)`; the set
De Morgan law `∁(A ∩ B) = ∁A ∪ ∁B` is `¬(a & b) = ¬a | ¬b`, refuted-by-negation
over all 2⁸ pairs. The learner sees set algebra *is* Boolean algebra.

**Built** (`Family::Sets`, subsets as `BitVec` bitmasks, exhaustive UNSAT of the
negation): `distributivity` (A∩(B∪C)=(A∩B)∪(A∩C)), `absorption` (A∪(A∩B)=A),
`complement_union_is_universe` (A∪∁A=U) — making concrete that set algebra and
propositional logic are the same Boolean lattice.

## Lean-horizon

Infinite sets, the ZFC axioms themselves, and cardinal arithmetic are
Lean-horizon (cf. Metamath's set.mm, which builds everything from the ZFC axioms).

## References

- Halmos, *Naive Set Theory*.
- axeyum: `axeyum-bv` bitwise lowering; the `identity` family pattern.
