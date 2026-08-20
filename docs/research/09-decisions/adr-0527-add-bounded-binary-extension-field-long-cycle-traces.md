# ADR-0527: Add bounded binary extension-field long-cycle traces

Status: accepted
Date: 2026-08-19
Index-summary: Compute fixed-degree short-interval Mangoldt traces over `GF(2^r)` natively, with certified field moduli and explicit population limits

## Context

The fixed-long-cycle refinement of Sawin's geometry is measured by varying the
base field while keeping the polynomial degree and number of prescribed
coefficients fixed.  For

```text
I_(n,m)(GF(2^r))
  = {T^n + a_(h-1)T^(h-1) + ... + a_0 : h=n-m},
```

put

```text
A_r(n,m) = sum_(f in I_(n,m)(GF(2^r))) Lambda(f) - (2^r)^h.
```

This is the trace of the `r`-th Frobenius power on the effective
long-cycle complex.  It is not supplied by the existing Hayes operation:
`identity_class_count(m,n)` computes the `r=1` population over `GF(2)`, not
the fixed-degree interval over `GF(2^r)`.

Small reduced zeta factors can reveal whether the long-cycle virtual
cohomology is dramatically smaller than ordinary cohomology.  They remain a
diagnostic; fitting a recurrence from finitely many traces is not a theorem.

## Decision

Add the bounded public module `axeyum_cas::gf2_extension` and operation
`binary_extension_long_cycle_trace`.  It provides:

1. bit-packed arithmetic in `GF(2^r)` from a caller-supplied monic binary
   modulus;
2. production and replay of the existing Rabin certificate proving that the
   modulus is irreducible over `GF(2)`;
3. exact polynomial arithmetic and Rabin irreducibility over `GF(2^r)`;
4. exact prime-power recognition, including inseparable powers, so the
   polynomial von Mangoldt weight is not approximated by squarefreeness; and
5. admission limits for field degree, polynomial degree, and the complete
   interval population before enumeration.

The report returns the field identity, interval dimensions, candidate count,
exact Mangoldt sum, and signed `A_r(n,m)`.  It does not return an inferred zeta
factor or promote finite recurrence fitting to proof evidence.

## Evidence

Focused native tests reproduce

```text
A_r(5,2) = (-4)^r - (-2)^r,  r=1,2,3,
(A_1,A_2,A_3)(9,4) = (5,129,-1771),
```

and reject a reducible field modulus and a one-candidate-too-small resource
limit.  The explicit release-mode research probe over the degree-five field
modulus `x^5+x^2+1` independently enumerated all `32^5=33,554,432` degree-nine
interval polynomials in 206.15 seconds and obtained

```text
mangoldt sum = 33,525,757,
A_5(9,4)     = -28,675.
```

This matches the independently reported scratch row.  The probe remains
ignored in ordinary tests; executing a finite assertion supplies diagnostic
reproducibility, not evidence for a uniform recurrence or degree bound.

## Consequences

- Axeyum can now measure genuine Frobenius-power long-cycle traces without
  SymPy or an external CAS.
- The base-field Hayes count and extension-field zeta diagnostic are no longer
  conflated.
- Ordinary gates exercise only bounded controls.  Large trace rows must report
  exact resource provenance and remain non-credit-bearing finite evidence.
- A complete proof still needs a uniform effective-cohomology or recurrence-
  degree theorem; finite Padé or Berlekamp--Massey output is not such a theorem.
