# ADR-0519: Model the connected trace as a relative Carlitz tower

Status: accepted
Date: 2026-08-19
Index-summary: Identify the connected Hayes trace with a relative Carlitz point trace and expose the exact linear saving over relative Hasse--Weil

## Context

ADR-0518 retains the top Hayes conductor levels inside one signed trace.  To
use characteristic-two geometry without importing an inapplicable theorem, we
need the exact cover, its relative cohomology dimension, and the numerical
saving required at the endpoint.

Let `C_j` denote the smooth projective curve of the binary Carlitz cyclotomic
field of conductor `t^(j+1)`.  The point-population identity is

```text
#C_j(GF(2^n)) = 2^j N_j(1) + 1.
```

Therefore, with `a` as in ADR-0518, the connected trace is exactly

```text
2^ell N_ell(1) - 2^(a-1) N_(a-1)(1)
  = #C_ell(GF(2^n)) - #C_(a-1)(GF(2^n)).       (RC)
```

## Decision

Treat (RC) as the selected geometric representation and add
`carlitz_connected_top_geometry` as its exact CAS ledger.

For coherent Carlitz torsion generators
`C_t(lambda_(r+1))=lambda_r`, the normalized generator
`y_(r+1)=lambda_(r+1)/t` satisfies

```text
y_(r+1)^2+y_(r+1)=lambda_r/t^2.
```

Thus the relative cover from conductor `t^a` to `t^(ell+1)` is a chain of
`ell+1-a` quadratic Artin--Schreier steps.  The ledger independently applies

```text
2 genus(C_j) = (j-2)2^j+2
```

and requires the relative first-cohomology dimension to reproduce exactly the
sum of the separate conductor-level Weil degrees.  It reports the fine,
coarse, and relative extension degrees, both genera, the relative dimension,
the integer Hasse--Weil envelope, and the exact saving required by (CRT).

## Evidence

At `ell=12`, the relative cover has six quadratic steps, fine/coarse Galois
degrees `4096/64`, and relative first-cohomology dimension `40704`.  Its
integer Weil numerator is `333447168`, exactly the separate top-conductor
envelope, against allowance `4194304`; the required integral saving is `80`.

At both `ell=200` endpoints, the ratio is exactly `50641/32`, so the required
integral saving is `1583`.  In general it is asymptotic to `8ell`.

Voloch's cyclotomic-twist theorem produces an error `7m q^(n/2)` and therefore
retains precisely this linear loss at the binary half-degree endpoint.

## Alternatives

The Heisenberg theorem of Ito--Takeuchi--Tsushima applies to the special
one-equation curves

```text
y^2-y=xR(x)
```

with `R` linearized, and uses a length-two Witt Lang torsor.  The Carlitz
relative cover above is a growing chain of Artin--Schreier equations.  Shared
Witt vocabulary is not an isomorphism of covers, so their theorem is not
imported unless a future checked reduction identifies the relative Carlitz
cohomology with their special quadratic class.

## Consequences

- A proposed geometric proof must save a factor asymptotic to `8ell` over
  relative Hasse--Weil while retaining cancellation between the top tower
  steps.
- The exact tower is linearized, but it is not yet a checked Heisenberg
  representation.  Computing more unrestricted Witt spectra does not address
  this missing reduction.
- If no bounded-radical polarization or explicit cohomological induction is
  found for this relative tower, the selected fallback remains the connected
  fourth-cumulant/gcd stratification.
