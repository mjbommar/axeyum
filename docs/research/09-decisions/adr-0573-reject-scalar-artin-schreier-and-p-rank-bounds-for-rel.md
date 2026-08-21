# ADR-0573: Reject scalar Artin--Schreier and p-rank bounds for REL

Status: accepted
Date: 2026-08-20
Index-summary: Price zero 2-rank on the relative Carlitz quotient and require a genuinely collective Witt zero-fibre estimate

## Context

ADR-0572 reduced the paper to the one-sided relative trace

```text
C_(ell,n) > -(2^(2ell)-W_(ell,n)).                    (REL)
```

The connected term is the Frobenius trace of the relative Jacobian quotient
between two levels of the binary Carlitz cyclotomic tower.  Three nearby
point-count technologies therefore needed a source-level audit:

1. Cramer--Xing's improvement for curves with Hasse--Witt invariant zero;
2. Ma--Xing's code-theoretic improvement for scalar Artin--Schreier curves;
3. Yoo--Lee's ramification-sensitive Hasse--Weil--Serre improvement.

## Decision

Do not use any of these results as proof credit for REL.  Retain the Carlitz
`2`-rank computation, but require the next bridge to control the simultaneous
zero fibre of the complete relative Witt system.

Extend `CarlitzConnectedTopGeometry` with the relative abelian dimension and
the exact Cramer--Xing trace-divisibility exponent.  The operation must fail
closed if the relative cohomology dimension is odd or zero.  Its regression
checks both Lemire parities for every `200<=ell<=1024`.

## Evidence

Deuring--Shafarevich gives `2`-rank zero at every Carlitz level.  The coarse
Jacobian is an isogeny factor of the fine Jacobian, so the relative quotient
also has `2`-rank zero.  Cramer--Xing, Theorem 3.12 and Corollary 3.13, give
only the trace divisibility

```text
2^ceil(n/g_rel) | C_(ell,n),
```

where `g_rel` is the dimension of that quotient over `GF(2^n)`.  Axeyum
computes

```text
g_rel = (2g_ell-2g_(a-1))/2 > n
```

at both endpoints for every `ell>=200`.  Cramer--Xing prove the valuation
inequality `v_2(C)>=n/g_rel`; since the valuation is integral, its endpoint
content is `ceil(n/g_rel)=1`, so the guaranteed divisor is exactly two.
Combining this with the Weil--Serre bound can improve its integral envelope by
at most one.  REL instead needs a multiplicative saving of 626 already at
`ell=200`, growing as `4ell+O(log ell)`.  Parity is therefore true but gives no
asymptotic endpoint saving.

Ma--Xing, Theorem 4.3, bounds the point count of one curve
`y^p-y=f(x)` through the minimum distance of a scalar trace code.  Their
source explicitly leaves the relevant higher-degree code distance
undetermined beyond its small exact cases.  More importantly, REL is the sum
of all high-order characters of a non-elementary principal-unit quotient.
Applying a scalar bound character by character takes absolute values before
the conductor sum and returns the already priced relative Hasse--Weil
envelope.

Yoo--Lee's published abstract and indexed section descriptions concern
generic global function fields and applications to elementary abelian
`p`-extensions.  The relative Carlitz quotient is a chain of cyclic
`2`-power Witt blocks, not an elementary abelian cover.  No theorem statement
from that paper has been found that applies to this quotient, and no credit is
assigned from an abstract or analogy.

Primary sources:

- R. Cramer and C. Xing, *An improvement to the Hasse--Weil bound and
  applications to character sums, cryptography and coding*, Advances in
  Mathematics 309 (2017), Theorem 3.12 and Corollary 3.13,
  <https://ir.cwi.nl/pub/28867/28867.pdf>.
- L. Ma and C. Xing, *An improvement of the Hasse--Weil bound for
  Artin--Schreier curves via cyclotomic function fields*, Theorem 4.3,
  <https://arxiv.org/abs/2105.04370>.
- J. Yoo and Y. Lee, *Improvements of the Hasse--Weil--Serre bound over
  global function fields*, Finite Fields and Their Applications 101 (2025),
  102538, <https://doi.org/10.1016/j.ffa.2024.102538>.

## Consequences

- Zero `2`-rank remains a proved structural property, but it cannot be
  advertised as progress on REL without a higher-slope or factor-dimension
  theorem.
- A scalar trace-code minimum distance is the wrong invariant.  A usable
  coding theorem must bound the complete weight/zero-fibre distribution of
  the relative Galois-ring or Witt code before characterwise absolute values.
- Literature that applies only to elementary abelian covers may be used as a
  model for such a theorem, not substituted for the non-elementary Carlitz
  quotient.
- REL remains open and the manuscript's red warning remains mandatory.
