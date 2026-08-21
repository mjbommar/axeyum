# ADR-0576: Remove odd Frobenius-cycle singular local terms

Status: accepted
Date: 2026-08-20
Index-summary: Collapse every proper odd Frobenius-cycle orbit to the cone vertex and certify smooth transverse projective local terms without claiming a trace bound

## Context

ADR-0575 proves smoothness only at the projective eigenlines fixed by the bare
long cycle.  The trace relevant to the endpoint instead uses `Frob*c`, whose
fixed locus is the original prescribed-coefficient count.  Before attempting
an equivariant trace estimate, we need to know whether repeated-root points in
that actual fixed locus introduce singular or higher-multiplicity local terms.

ADR-0554 already classifies a long-cycle-compatible repeated-root tuple by one
Frobenius orbit of degree `e|n`, with characteristic polynomial

```text
P(x)=Q(x)^(n/e).
```

It stops after separating odd multiplicities from Frobenius-square strata.

## Decision

Add `sawin_odd_frobenius_cycle_fixed_locus_report` and certify the complete
odd-endpoint local statement.  Put `n=2ell+1`.  Every divisor and every
multiplicity `n/e` is odd.  If `e<n`, then the least prime divisor of `n/e` is
at least three, so

```text
e <= n/3 <= ell-1.
```

For odd `m=n/e`, the first `e` leading coefficients of `Q^m` recover the `e`
nonleading coefficients of the monic polynomial `Q` triangularly: the current
coefficient occurs with coefficient `m=1` in `GF(2)`, and all remaining terms
use earlier coefficients.  The endpoint equations therefore force
`Q=x^e`, hence `P=x^n`.  Every proper Frobenius-orbit stratum is exactly the
affine cone vertex.

Every nonvertex `Frob*c` fixed point consequently has exact orbit degree `n`
and `n` distinct coordinates.  On the zero-prefix fibre,

```text
d e_j / d a_i = e_(j-1)(a_1,...,a_hat_i,...,a_n) = a_i^(j-1)
```

for `1<=j<=ell`: divide the elementary-symmetric generating series by
`1+a_i t` and use `e_1=...=e_ell=0`.  The Jacobian is the first `ell` rows of
a Vandermonde matrix and has rank `ell`.  Absolute Frobenius has zero
differential in characteristic two, so the graph of `Frob*c` and the diagonal
meet transversely at each projective fixed point.  Every local intersection
multiplicity is one.

Do not convert this into `(REL)`.  The ordinary trace formula now has no
singular projective local corrections at odd degree, but its sum of unit local
terms is the unknown global point count itself.  The report therefore retains
`frobenius_weighted_trace_bound_certified=false`.

## Evidence

- The native report enumerates every proper divisor through the degree-401
  handoff and checks odd multiplicity and `e<=ell-1` before certifying the
  triangular collapse.
- A separate exhaustive extension-field test enumerates every element of
  `GF(2^5)` and `GF(2^7)`, literally multiplies its complete Frobenius-root
  polynomial, tests the zero prefix, and independently confirms that every
  shaped nonzero element has full orbit degree.
- The existing packed-polynomial power test independently checks triangular
  prefix recovery for all odd powers through the bounded test range.
- Focused tests keep the global Frobenius trace flag false.

## Consequences

- At odd endpoints, the repeated-root/singular-local-term branch of the
  `Frob*c` analysis is closed completely; only the affine cone vertex is
  singular, and projectivization removes it.
- A geometric continuation must now bound the global trace on this smooth
  exact-orbit locus.  More local singularity calculations cannot improve the
  endpoint ledger.
- Even endpoints retain genuine Frobenius-square strata and are not covered by
  this theorem.
- The manuscript warning and `(REL)` remain unchanged.

## References

- Hast and Matei, [*Higher moments of arithmetic functions in short intervals:
  a geometric perspective*](https://arxiv.org/abs/1604.02067), especially the
  repeated-root analysis in Lemma 2.4 and Section 4.
- Lu and Zheng, [*Categorical traces and a relative Lefschetz--Verdier
  formula*](https://arxiv.org/abs/2005.08522), for the trace-class framework;
  it supplies no numerical bound for this fixed-point sum.
