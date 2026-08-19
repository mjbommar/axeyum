# ADR-0493: Prove no-wrap inverse energy through rational collisions

Status: accepted
Date: 2026-08-19
Index-summary: Stabilize inverse-additive energy for ell at least three d, classify collisions by reduced fractions, and replay their Type-II exponent effect

## Context

ADR-0491 added exact finite inverse-additive energy but deliberately treated
the stable fleet rows as observation only.  The relevant congruence has more
structure.  For `A,B,C,D in V_d`, clearing the unit denominators gives

```text
A^(-1)+B^(-1) = C^(-1)+D^(-1)  (mod x^(ell+1))
iff
(A+B)CD = (C+D)AB               (mod x^(ell+1)).
```

Both cross-products have degree at most `3d`.  Therefore the congruence is an
ordinary polynomial equality whenever `ell>=3d`; the observed stabilization
has an exact threshold sufficient for every degree.

## Decision

Add two CAS routes and one exponent ledger to `axeyum-cas::gf2_hayes`:

1. `principal_unit_inverse_additive_energy_no_wrap` buckets ordered pairs by
   the canonically reduced rational function `(A+B)/(AB)`.  It computes the
   stable energy without allocating the ambient additive group of size
   `2^ell` and is algebraically independent of the Walsh-transform route.
2. `principal_unit_inverse_additive_energy_no_wrap_bound` implements the
   elementary collision classification.  Write `A=ga`, `B=gb`, `(a,b)=1`,
   and `h=(g,a+b)`.  Then

   ```text
   (A+B)/(AB) = ((a+b)/h) / ((g/h)ab).
   ```

   For a fixed reduced fraction `p/q`, a preimage selects an ordered
   factorization `q=cab`; `h=(a+b)/p` and `g=hc` are then forced.  Since
   `deg q<=2d`, the multiplicity is at most `tau_3(q)`.  Splitting irreducible
   factors at degree `R=floor(log2(d)/2)` gives the explicit bound

   ```text
   tau_3(q) <= (2d+1)^(2^(R+2)) * 3^floor(2d/(R+1)) = 2^o(d).
   ```

   Hence `E_inv(ell,d)<=2^(2d+o(d))` for `ell>=3d`.
3. `binary_bilinear_energy_exponent` substitutes caller-supplied rational
   energy exponents into Bagshaw's characteristic-free `k=2` Hölder formula
   and returns the exact deficit from a requested target.  It grants no
   theorem credit for external hypotheses or suppressed constants.

Do not promote the result to SMT surface.  The bound is a CAS/research
primitive for the Lemire proof and the source-level argument remains outside
the trusted kernel until reconstructed by an accepted proof route.

## Evidence

The rational reducer gives stable energies

```text
d:       1    2    3    4     5      6
energy:  8   40  176  760  3128  12520.
```

For every `1<=d<=6`, these agree with the independent modular-inverse/Walsh
route at both `ell=3d` and `ell=3d+1`.  At `(ell,d)=(8,4)`, the modular value
is `928`, while the stable rational value is `760`, pinning that the
no-wrap hypothesis is substantive.  Direct tests through `d=7` also require
the explicit divisor bound to dominate both the largest rational-fibre
multiplicity and the exact energy.

In modulus-degree notation the no-wrap hypothesis is strict: `3d<r`.  The
generic exponent ledger verifies that *idealized* energy exponents `2d` on two
intervals of size exponent `d=100` at the first valid modulus degree `r=301`
would improve the trivial bilinear exponent `200` to `187.625`.  At modulus
degree `400`, where the total interval exponent is exactly `r/2`, the same
ideal input merely reaches the trivial exponent.  This calculation does not
substitute the explicit divisor envelope or reserve epsilon/constants.
ADR-0494 adds the loss-aware operation that does so and extends the energy
theorem through the wrapped range.

## Alternatives

- Retain stabilization as fleet evidence: rejected because the degree bound
  proves it uniformly.
- Compute the stable value with a transform at `ell=3d`: rejected as the only
  route because it allocates `2^(3d)` cells and hides the collision
  classification.
- State `2^(2d+o(d))` without an explicit bound: rejected because the CAS and
  exponent ledger need a finite replayable envelope.

## Consequences

- The characteristic-two inverse-energy input is now proved in the no-wrap
  range rather than inferred from bounded experiments.
- Rational collision fibres expose the exact divisor-counting problem for
  sharper constants or exponents.
- Every later energy improvement can be tested immediately against the
  Type-II exponent target, with explicit loss accounting supplied by
  ADR-0494.
- The remaining endpoint work needs cancellation across the full Möbius
  convolution; the wrapped energy range is no longer itself open.
