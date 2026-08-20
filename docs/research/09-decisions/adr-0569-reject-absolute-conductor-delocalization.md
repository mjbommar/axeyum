# ADR-0569: Reject absolute conductor delocalization

Status: superseded by ADR-0570
Date: 2026-08-20
Index-summary: Refute the absolute SUP-L constant by exact endpoint recurrence and retain only a polynomial-loss high-conductor target

## Context

ADR-0568 reduced the endpoint fourth moment to

```text
max_e |D_[j](e)|^2
 <= C ell^a (j-1)^2 2^(j-1+n-2ell).                 (SUP-poly)
```

The first finite rows suggested the stronger choice `C=4,a=0`.  The exact
degree recurrence for a fixed conductor level makes it possible to test that
choice far beyond full `E_ell` population tables.  At the even endpoint
`(ell,n)=(27,56)`, level `j=4` has sibling-difference peak `670285824`, so its
required squared constant is

```text
3594264686842871808 / 648518346341351424 > 4.
```

The arbitrary-precision degree recurrence then gives another exact violation
at `(ell,n,j)=(343,688,4)`, beyond both the declared `ell>=200` threshold and
the independently certified degree-400 handoff.  Its first propagated row is
checked against a fresh population transform before the recurrence is trusted.

This is not an isolated numerical accident.  Let the inverse roots of all
primitive level-`j` Hayes `L`-polynomials be `alpha_(chi,r)`.  Exact degree and
the functional equation, together with Weil, give
`|alpha_(chi,r)|=sqrt(2)`.  Put `z_(chi,r)=alpha_(chi,r)/sqrt(2)`.

For fixed `j`, simultaneous recurrence in the compact torus containing the
finite vector `(z_(chi,r))` supplies integers `n_k -> infinity` with
`z_(chi,r)^(n_k) -> 1` for every `chi,r`.  Therefore

```text
S_chi(n_k)/2^(n_k/2) -> j-1
```

simultaneously.  Fourier inversion at the identity class then gives

```text
sup_(endpoint n>=2j+1) kappa_j(n) = 2^((j-1)/2),
```

which is exactly the trivial triangle ceiling.  Since every sufficiently
large integer `n` is one of the two endpoint forms, no absolute `K` can be
uniform in `j`.

## Decision

Mark the `C=4,a=0` fact refuted.  Retain the polynomial-loss reduction and use
the concrete replacement

```text
C=4, a=4.
```

This target gives `kappa_j<=2ell^2`.  The individual Weil triangle bound
already supplies it whenever

```text
2^(j-1) <= 4 ell^4,
```

so the genuinely open range starts only above approximately
`4 log2(ell)+3`.  The high-conductor theorem is not refuted by fixed-level
recurrence: the degrees needed to approach the triangle ceiling may grow much
faster than any polynomial in `j`.

The exact endpoint implication becomes

```text
M_4 <= 2500 ell^8 2^(3ell),
```

and the proper-power-aware arithmetic checker still closes immediately after
the independently certified degree-400 range.

## Consequences

- The absolute-constant version of `(SUP-L)` must not appear as an open
  conjecture or a conditional theorem premise in the final paper.
- Fixed low conductor levels cannot prove or disprove the polynomial target;
  they are absorbed by the trivial triangle bound.
- New work is confined to the growing high-conductor regime
  `j>4log2(ell)+O(1)`.
- The exact level-four counterexample is retained as a regression so bounded
  experiments cannot select the same false constant again.
- The polynomial-loss statement remains open; no Lemire theorem is claimed.
- ADR-0570 retains it as a sufficient condition but selects the strictly weaker
  top-window Haar target for further proof work.
