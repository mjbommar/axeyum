# ADR-0554: Isolate binary square strata in the Hast--Matei long-cycle sector

Status: accepted
Date: 2026-08-20
Index-summary: Translate the Hast--Matei top variance exactly and confine its long-cycle low-characteristic defect to square proper powers

## Context

ADR-0553 leaves one Frobenius-weighted long-cycle trace.  Hast and Matei's
ordered-root complete intersections are a natural bridge because their
two-polynomial top-weight representation is explicit.  Their general
`m`-polynomial singular-locus theorem, however, assumes characteristic zero
or characteristic greater than `n` when `m>2`.  The restriction enters through
their repeated-root fibre lemma: its Newton-identity Jacobian proof divides by
root multiplicities and coefficient indices, which is invalid in
characteristic two.

The application needs two separate audits.  The known `m=2` top-weight term
must be translated to the exact Lemire endpoint, and the `m=4` binary defect
must be localized before asking whether the connected projector removes it.

## Decision

Add `hast_matei_long_cycle_endpoint_report` as a bounded native ledger.  Put

```text
ell=ceil(n/2)-1,  h=n-ell-1=floor(n/2).
```

Hast--Matei's cutoff is then

```text
n-h-2=ell-1.
```

The character of an `n`-cycle vanishes on every Specht module except a hook
`(n-j,1^j)`, where its value is `(-1)^j`.  The condition
`lambda_1<=n-h-2` leaves exactly `ell-1` hooks.  Consequently their explicit
top-weight `X_(2,n,h)` piece contributes

```text
(ell-1) 2^n
```

to the binary global second-moment scale.  Cauchy compares this with the
squared identity-class mean `2^(2(n-ell))`, so the squared pointwise ratio is

```text
(ell-1) / 2^(n-2ell).
```

The denominator is two at the odd endpoint and four at the even endpoint.
Thus even an idealized top-weight-only second moment misses the unresolved
endpoint; lower weights cannot repair a positive Cauchy bound.

The same operation classifies the repeated-root strata selected by an
`n`-cycle Frobenius condition.  Such a tuple has one distinct-root orbit of
degree `e|n` and root polynomial

```text
P(x)=Q(x)^(n/e).
```

If `a=n/e` is odd, the index-`j` leading coefficient of `Q^a` contains the
index-`j` coefficient of `Q` with coefficient `a=1` in `GF(2)`; every other
term uses earlier coefficients.  The first `e` coefficients therefore recover
`Q` triangularly.  If `a` is even, then

```text
Q(x)^a=(Q(x)^(a/2))^2,
```

and only indices divisible by `2^v2(a)` are visible.  Hence, inside the
long-cycle sector, the low-characteristic failure is confined exactly to
Frobenius-square proper-power strata.  This is narrower than the unrestricted
singular locus, whose arbitrary multiplicity partitions are not claimed to
obey this dichotomy.

## Evidence

- The report checks both endpoint translations and the hook count by exact
  integer arithmetic.  At degrees `401` and `402`, the squared Cauchy ratios
  are respectively `199/2` and `199/4`, so neither closes.
- Every divisor `e|n` below the repeated-root cutoff is classified by the
  parity and lowest set bit of `n/e`.  The degree-12 control gives rows
  `(e,a,stride)=(1,12,4),(2,6,2),(3,4,4),(4,3,1)`; only the last is
  triangular rather than square.
- An independent packed-polynomial expansion exhausts every monic base
  polynomial through degree six and powers through seven.  It checks
  injectivity of the first `e` coefficients for every odd power and the exact
  Frobenius coefficient stride for every even power.
- An exhaustive divisor-identity control runs through degree 128, with pinned
  degree-401 and degree-402 endpoint rows.
- Focused tests and all-target, all-feature `axeyum-cas` Clippy pass.
- The report retains `connected_frobenius_trace_bound_certified=false`.

## Alternatives

- **Use the second moment pointwise:** rejected by the exact endpoint ratios.
- **Declare Hast--Matei's repeated-root lemma valid in characteristic two:**
  rejected; all-even multiplicities give genuine positive-dimensional fibres,
  for example through Frobenius squares.
- **Claim the connected projector removes every square stratum:** deferred.
  The projector is a virtual subtraction across four raw fibre products, and
  an equivariant localization or an exact square-stratum cancellation theorem
  is still required.

## Consequences

- The next geometric theorem has a sharper target: prove that the connected
  long-cycle virtual complex removes or separately bounds the square
  proper-power strata, then control the remaining triangular sector.
- Hast--Matei's `m=2` top representation is useful structural evidence but is
  quantitatively insufficient on its own.
- This increment narrows the characteristic-two obstruction; it does not
  supply the positive Frobenius saving or grant Lemire theorem credit.

## References

- Hast and Matei, [*Higher moments of arithmetic functions in short
  intervals: a geometric perspective*](https://arxiv.org/abs/1604.02067),
  especially Theorem 1.2, Lemma 2.4, Theorem 2.7, and Section 4.
- Sawin, [*Square-root cancellation for sums of factorization functions over
  short intervals in function fields*](https://arxiv.org/abs/1809.05137).
