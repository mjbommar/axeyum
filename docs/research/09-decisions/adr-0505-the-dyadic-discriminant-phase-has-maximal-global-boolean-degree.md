# ADR-0505: The dyadic discriminant phase has maximal global Boolean degree

Status: accepted
Date: 2026-08-19
Index-summary: Reject a global bounded-degree Witt-phase shortcut because the full-support discriminant ANF coefficient is provably odd in every degree

## Context

ADR-0504 rewrites the complete binary Möbius weight as four additive phases
of the integral discriminant modulo eight.  This would immediately invite a
generic bounded-degree polynomial-phase estimate if the discriminant became a
low-degree function of the binary coefficient bits after reduction modulo
eight.

## Decision

Expose `binary_discriminant_anf_report` to recover the unique multilinear
`Z/8` algebraic normal form, classify its coefficients by support degree and
2-adic valuation, and check full truth-table reconstruction.  Reject the
global bounded-degree route: for degree `k`, the coefficient on the monomial
containing all `k-1` free coefficient bits is always odd.

Indeed, modulo two that top coefficient is the XOR of the discriminant parity
over the complete coefficient cube.  Discriminant parity is the squarefree
indicator, and the already proved population is

```text
(2^k-(-1)^k)/3,
```

which is odd.  Hence the phase has maximal Boolean support degree `k-1` in
every degree.

## Evidence

The native operation computes every integral discriminant residue by
fraction-free Bareiss elimination, applies subset Möbius inversion over
`Z/8`, and applies the inverse subset transform as an exact reconstruction
check.  Exhaustive cubes through degree ten agree with the general
full-support parity argument.  Caller-selected degree and table-cell limits
are checked before enumeration.

## Consequences

- The four-phase dyadic representation remains exact, but no theorem for
  globally bounded-degree `Z/8` phases applies to the unrestricted coefficient
  cube.
- The next rank/finite-difference analysis must first impose the affine
  Artin--Schreier and inverse-coset constraints, where the full-support term
  may collapse or become structured.
- Cross-order cancellation remains the other live route; this decision grants
  no endpoint estimate.
