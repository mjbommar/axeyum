# ADR-0489: Expose the binary wild-Kloosterman bound as a bounded CAS primitive

Status: accepted
Date: 2026-08-19
Index-summary: Add a uniform stationary-phase bound for binary principal-unit Kloosterman sums and top-interval product multiplicities, with direct finite controls

## Context

The inverse-coefficient diagnostic in the Lemire lane computes the Walsh
transform of

```text
q_ell(a_1,...,a_ell) = [x^ell] (1+a_1x+...+a_ell x^ell)^(-1).
```

This is not a new transform family.  After reversing the frequency
coefficients it is the wild Kloosterman sum

```text
K_2(c)=sum_(u in R^x) psi(u^(-1)+cu),
R=GF(2)[x]/(x^(ell+1)),
psi(z)=(-1)^[x^ell]z.
```

Sawin's stationary-phase analysis of wild Kloosterman sums over equal-
characteristic local rings identifies the relevant scale
`ceil(ell/3)` (Will Sawin, *The size of wild Kloosterman sums in number
fields and function fields*, J. Analyse Math. 151 (2023), 303--341,
doi:10.1007/s11854-023-0325-9).  Axeyum needs only a specialized elementary
bound, not a general Kloosterman engine.

The paper's later displayed sharpening cannot be imported for this binary
specialization without qualification.  At modulus `x^4` and `c=1+x^2`, every
one of the eight units has top phase zero, so `K_2(c)=8`; the displayed
equal-characteristic specialization of Theorem 1.1 would give
`|K_2(c)|<=2^(5/2)`.  The earlier stationary-phase scale and the independent
bound below agree with the exact sum.  Axeyum therefore records and proves the
specialized statement it actually uses instead of laundering the stronger
external claim.

## Decision

Add `principal_unit_kloosterman_bound` to the bounded `gf2_hayes` CAS surface.
Its report contains the modulus, affine-coset and stationary precisions, the
maximum number of contributing cosets, the uniform Kloosterman bound, and the
consequent pointwise bound on the centered multiplicity of
`V_(ell-1)^2`.

Keep the operation CAS-local.  It evaluates a proved closed form with exact
bignums and existing Hayes admission limits.  It allocates no Walsh or product
table, adds no solver logic, and does not promote the still-open prime
cancellation step.

## Evidence

Put `m=ell+1`, `c=ceil(m/3)`, and `s=ceil((m-1)/3)`.  In characteristic two,
the quadratic mixed term in the second difference of `u^(-1)` vanishes.  Its
first possible mixed terms are `z^2y+zy^2`, of total degree three.  Since
`3c>=m`, the phase is an affine additive character on every coset modulo
`x^c`; a coset therefore contributes either zero or its full size `2^(m-c)`.

Suppose two contributing cosets first differ in degree `d<s`.  Choose a
variation `y` of degree `m-1-2d`, which is at least `c`.  In the second
difference, `z^2y` has the unique lowest valuation `m-1` and a nonzero top
coefficient; `zy^2` and every term of higher total degree have larger
valuation.  This contradicts triviality of both affine characters.  Thus all
contributing cosets agree modulo `x^s`, and there are at most `2^(c-s)` of
them.  Consequently

```text
|K_2(c)| <= 2^(c-s) 2^(m-c) = 2^(m-s)
          = 2^(ell+1-ceil(ell/3)).
```

For `H=V_(ell-1)`, orthogonality gives

```text
r(e)-2^(ell-2)=(+/-)K_2(c(e))/4,
```

so the centered product multiplicity is at most
`2^(ell-1-ceil(ell/3))`.

Unit tests enumerate every frequency and every unit through `ell=9`, compare
the exact Kloosterman sums with the bound, and independently enumerate the
full `H^2` product tables.  A pinned `ell=3` control attains the value eight,
and invalid/resource-limited calls decline before a transform allocation.

## Alternatives

- Add a generic Walsh-Hadamard API first: rejected because the proof evaluates
  a uniform bound without constructing the exponential table.
- Cite the strongest displayed external theorem unchanged: rejected because
  the eight-term modulus-`x^4` sum is a direct counterexample to that binary
  specialization.
- Treat the Kloosterman bound as a prime-counting theorem: rejected because it
  controls one Type-II product distribution, not the connected cross-degree
  Mangoldt terms.

## Consequences

- The observed inverse spectrum now has a uniform proved amplitude bound; its
  exact three-valued support formula remains an optional refinement rather
  than a proof dependency.
- Axeyum gains a native pointwise Type-II bound stronger than the previously
  recorded energy alone.
- The remaining paper obligation is narrower but still weighted: a valid
  fixed-order prime decomposition needs a Möbius-weighted bilinear estimate;
  this unweighted pointwise bound cannot simply replace it.  The alternative
  is a separate aggregate endpoint estimate.  No universal Lemire fact is
  credited by this ADR.
