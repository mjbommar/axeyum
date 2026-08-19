# ADR-0503: Expose binary Witt blocks and order-two character projections

Status: accepted
Date: 2026-08-19
Index-summary: Identify the native principal-unit factors with truncated binary Witt blocks and test exceptional real characters without granting cancellation credit

## Context

ADR-0501 rules out controlling every simultaneous Möbius coset by its best
single translation.  ADR-0502 supplies a quadratic representation of the
Möbius sign, but its per-polynomial rank merely evaluates that sign.  A
characteristic-two obstruction could instead be concentrated in the real,
order-two characters of the principal-unit group.

The native Hayes transform already decomposes the group using generators
`1+x^m` for odd `m`.  In characteristic two,
`(1+x^m)^(2^j)=1+x^(m 2^j)`, so the cyclic factor of order `2^L` is exactly
the additive group of the length-`L` 2-typical Witt block over `GF(2)`.

## Decision

Treat the existing odd-generator factors as checked truncated 2-typical Witt
blocks and expose two bounded CAS operations:

- `binary_principal_unit_witt_report` converts a packed principal unit to its
  mixed-radix/Witt blocks, labels every active slot and highest active slot,
  and checks exact reconstruction;
- `binary_berlekamp_order_two_projection_report` projects the Möbius weights
  in every simultaneous input/inverse coset onto every order-two character,
  labels exact conductors, and checks Parseval on the quotient by squares.

Retain every projection row.  Do not interpret a large individual mode, or a
bounded absence of one, as a uniform analytic estimate.

## Evidence

Every principal unit through level five roundtrips between coefficient and
Witt coordinates.  The Frobenius slot control sends `1+x^4` to coordinate
four in the `m=1` block and labels slot four.

At the known failing single-translation row `(ell,k,d)=(9,11,8)`, all 32
order-two characters are evaluated.  The trivial projected energy is `615`,
the maximum is `1719` at the conductor-nine mask `16`, and exact real Parseval
is `20832=32*651`.  Grouping by exact conductor gives average energies
`615,475,553,505,691,693` at the trivial, `1,3,5,7,9` levels.  The obstruction
is therefore not confined to one or two real modes in this witness.

## Consequences

- The CAS has the exact Witt conversion and conductor metadata needed for a
  tensorized characteristic-two argument.
- Removing a fixed tiny exceptional-real sector is deprioritized unless a
  different family-level identity supplies cancellation of its complement.
- The live local options are a multi-block rank/orthogonality theorem, a joint
  Arf--Artin--Schreier analysis, or cancellation retained across convolution
  orders.  None is credited by this finite diagnostic.
