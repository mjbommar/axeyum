# ADR-0532: Do not import Linnik--Selberg across the fixed wild modulus

Status: accepted
Date: 2026-08-20

## Context

The exact Lemire endpoint is a signed Möbius convolution whose inverse phases
are Kloosterman sums modulo the fixed prime power `x^(ell+1)`. Pointwise
Vaughan bounds lose cancellation between convolution orders, so the
function-field Linnik--Selberg theorem is a natural candidate: it supplies
cancellation between Kloosterman sums before absolute values are taken.

The 2026 shifted-convolution theorem of Florea--Lalín--Malik--Sahay uses this
input to improve on pointwise Weil estimates. Its equations must be matched to
the Axeyum sum before any exponent saving is entered in the endpoint ledger.

## Decision

Do not apply the published Linnik--Selberg estimate to the Lemire endpoint.
The theorem bounds

```text
sum_(g monic, deg g=j) S(f,h;g),
```

so the cancellation variable is the **modulus** `g`. In the endpoint
convolution, the modulus is the single ramified polynomial `x^(ell+1)` and the
degree-`d` interval variables occur in the two Kloosterman arguments. Neither
renaming variables nor polynomial reciprocity interchanges these roles: the
inverse congruence is still taken in the fixed local ring
`GF(2)[x]/x^(ell+1)`.

The published source further distinguishes its untwisted modulus average from
the twisted/divisibility version, which it says remains open with no explicit
uniform dependence. The endpoint carries both Möbius weights and the fixed
wild local condition, so that unavailable version cannot be inserted as a
black box either.

## Evidence

Equation (18) of
[The shifted convolution problem in function fields](https://doi.org/10.1007/s00208-026-03340-9)
is the modulus average above. In the same source, the error-term derivation
first reorganizes by `deg(g_1)=j` and only then invokes Linnik--Selberg on
`sum_(g_1 in M_j) S(h,lambda f;g_1)`. The paper explicitly reverts to a
pointwise Weil bound when a multiplicative twist remains.

By contrast, Axeyum's exact Möbius identity has the form

```text
Delta_(ell,n)
  = sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)),
```

where every inverse is computed modulo `x^(ell+1)`. The existing
annihilator-depth regroup and summation-by-parts identity preserve cancellation
between `d`; they do not create a varying-modulus Kloosterman family.

## Alternatives

Treating the interval polynomial `u` as the Linnik--Selberg modulus was
rejected because the phase denominator remains `x^(ell+1)`. Applying
reciprocity before the Kloosterman expansion was rejected for the same reason.
Using the conjectural twisted estimate was rejected because it is not a proved
input and its parameter dependence is precisely what the endpoint ledger must
control.

## Consequences

The 2026 theorem is a valuable model for a future fixed-wild-modulus Voronoi or
Kuznetsov formula, but supplies no present proof credit. The live target
remains cancellation in the fixed-modulus, Möbius-weighted, cross-order sum,
equivalently the connected Carlitz/Witt trace. A future spectral route must
state and prove that different theorem rather than cite the varying-modulus
Linnik--Selberg estimate.
