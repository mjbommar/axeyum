# ADR-0523: Reject projection-preserving extensions of the pinned dyadic fibre

Status: accepted
Date: 2026-08-19
Index-summary: Use an exact mod-four additivity witness to require any joined dyadic Witt law to mix the affine fibre coordinates in its multiplication

## Context

ADR-0522 certified the small auxiliary-unit quadratic projector but left open
how it should be joined to the nonquadratic affine Artin--Schreier fibres.  A
direct product plainly retains the bad fibre.  A tempting next construction is
a central extension whose quotient map still preserves the additive fibre.

The reviewer bridge note gave an independent description of the pinned worst
fibre:

```text
F_t=x^11+1+sum_(j=0)^6 t_j x^(j+2),
D_t=Disc(F_t)Disc(F_(t xor 48)) mod 8.
```

Before searching cocycles or computing commutator ranks, the normalized phase
`d_t=D_t-D_0 mod 4` must pass the cheapest necessary additivity test.

## Decision

Add `pinned_dyadic_fibre_projection_obstruction_report` to the native CAS.  It
reconstructs all 128 product-discriminant residues by exact integer resultant
arithmetic, independently confirms the full-support ANF coefficient `6 mod
8`, normalizes modulo four, and returns the lexicographically first failure of

```text
d_(s xor t)=d_s+d_t mod 4.
```

The first failure is `s=t=1`: the two input phases are both one, the XOR phase
is zero, and the expected additive value is two.

This finite witness gives a general obstruction.  If `pi:G -> F_2^7` is a
surjective homomorphism and `d o pi:G -> Z/4` is a homomorphism, then choosing
preimages of any two fibre coordinates forces `d` to be additive.  Therefore
no projection-preserving central extension can repair the pinned phase.

## Evidence

The ordinary all-feature test pins the family parameters, the independent ANF
coefficient, and the exact `(1,1)` witness.  It uses the existing fraction-free
integer discriminant implementation and no floating-point or external CAS.

## Alternatives

- A direct product was already excluded because it restricts to the original
  nonquadratic fibre.
- Searching arbitrary central cocycles while retaining the fibre quotient was
  rejected by the new theorem: no cocycle in that entire class can make the
  pulled-back phase additive.
- Abandoning the Heisenberg direction entirely was rejected because the
  obstruction does not apply when multiplication genuinely mixes the affine,
  auxiliary, valuation, and Witt coordinates.

## Consequences

- The next group-law search must not keep the seven-bit fibre as a homomorphic
  quotient.  Its multiplication must depend on auxiliary or Witt coordinates.
- Associativity and the exact phase law must be checked before any commutator
  rank is interpreted.
- This rejects a construction class but does not bound the connected endpoint
  sum or settle the cross-order convolution block.
