# ADR-0580: Reduce identity variance to polynomial local share

Status: accepted
Date: 2026-08-20
Index-summary: Reduce the identity-cylinder variance to a polynomial delocalization estimate on each retained Haar layer

## Context

ADR-0578 reduces the remaining Lemire endpoint to the positive-square estimate

```text
V_id <= 2^(2ell-2).                                      (ICV)
```

Its exact Haar form is

```text
R V_id = sum_(j=c_0+1)^ell 2^(j-c_0-1) F_j(1),          (ICV-H)
```

where `F_j(1)` is the sum of squared level-`j` sibling differences over the
parents in the identity cylinder of `E_(c_0)`.  Put `F_j(global)` for the same
sum over every level-`j` parent.  Exact-conductor Parseval and the ordinary
individual-character Weil bound give

```text
F_j(global) <= (j-1)^2 2^n.                             (G2)
```

The missing issue is therefore localization, not the global second moment.

## Decision

Register the following levelwise statement as the active sufficient candidate:

```text
16 ell^2 F_j(1) <= F_j(global)
for every c_0 < j <= ell.                               (PL2)
```

Substitution of `(PL2)` and `(G2)` into `(ICV-H)`, with the integral bound at
each level rounded down, gives

```text
R V_id <= sum_(j=c_0+1)^ell 2^(j-c_0-1)
          floor((j-1)^2 2^n / (16 ell^2)).              (PL2-H)
```

The native `identity_cylinder_polynomial_share_implication` operation checks
with exact integers that `(PL2-H)` implies `(ICV)`, hence `(REL)`, for both
endpoint degrees and every `ell` from 200 through 1024.  This asks only for a
polynomial improvement over the trivial statement `F_j(1)<=F_j(global)`.

For comparison, the stronger experimental estimate

```text
2^c_0 F_j(1) <= ell F_j(global)                         (LC2)
```

also implies `(ICV)`.  At the first odd endpoint, `ell=200`, `(ICV)` permits
the localization multiplier in the normalization of `(LC2)`

```text
5007710127439295349009662031980010502580210696737863,
```

which exceeds `2^170`; `(LC2)` assumes only `200`.  Thus `(LC2)` has
exponential surplus and is not the selected theorem target.

Do not use the stronger uniform-share statement

```text
2^c_0 F_j(1) <= F_j(global).                            (false)
```

Exact rows refute it.  Neither finite success of `(LC2)` nor failure of uniform
sharing settles the much weaker asymptotic `(PL2)` target.

## Prospective proof route

Expanding `F_j(1)` gives pairs of degree-`n` polynomials which share their
first `j-1` leading coefficients, whose common first `c_0` coefficients are
fixed to the identity cylinder, together with the level-`j` sibling sign.  It
is therefore a linear slice of the `m=2` short-interval variety of Hast and
Matei, not their `m=4` moment problem.

A source-level audit of arXiv `1604.02067` confirms that their `m=2`
complete-intersection and singular-locus calculation is characteristic-free;
the restriction `p>n` enters only for `m>2`.  Their published theorem still
averages over all interval centers and allows constants depending on the
growing degree and interval length.  Fixing the `c_0` common coefficients and
bounding the resulting twisted slice strongly enough to save the factor
`16 ell^2` is new work.  Dimension counting alone does not control its Betti
numbers and therefore is not a proof of `(PL2)`.

There is an equivalent weak global fourth-moment route which may avoid the
slice.  Let `Q_j=sum_(all p) H_j(p)^4`, let `N_j=2^(j-1)` be the number of
global parents, and put `K_j=N_j Q_j/F_j(global)^2`.  Since the identity
cylinder contains `N_j/2^c_0` parents, Cauchy gives

```text
F_j(1)^2 <= (N_j/2^c_0) Q_j.
```

Consequently `(PL2)` follows from

```text
K_j <= 2^c_0/(256 ell^4).                               (WK2)
```

This is vastly weaker than a bounded or Gaussian kurtosis theorem: its allowed
constant is already exponential in `ell`.  It is also the precise way in which
the older fourth-moment geometry can contribute to the new localized target.
Any proposed moment theorem should now be priced against `(WK2)`, rather than
against an unnecessary absolute constant.

## Evidence

- The CAS reconstructs `F_j(1)` and `F_j(global)` from the same exact sibling
  differences used in `(ICV-H)` and fails closed if the Haar sum does not equal
  the direct conditional variance.
- The same report now computes `Q_j` directly and checks `(WK2)` by a
  denominator-free integer comparison; the result is a finite diagnostic, not
  a theorem.
- Exact local rows through `ell=23` satisfy the much stronger `(LC2)` while
  repeatedly refuting the uniform-share control.  On the pinned `b1b4f407a`
  fleet rows `ell=19,20,21,22,23`, the maximum integral `(LC2)` localization
  multipliers were respectively `14,3,3,3,5`; all ten endpoint rows passed
  `(LC2)` and `(ICV)`.  The false uniform-share control failed on respectively
  `10,10,7,6,6` retained layers.  No finite row is universal evidence.
- The symbolic endpoint implication uses the proved envelope `(G2)`, not the
  observed global square sum.
- `F:gf2-hayes-identity-cylinder-polynomial-share` remains conjectured with no
  proof evidence or Autogenesis registration.

## Consequences

- The live theorem target is now a two-polynomial, one-cylinder localization
  estimate requiring only a quadratic saving over trivial concentration.
- More global fourth moments, support-only inequalities, or unsliced average
  variances receive no endpoint credit unless they imply this local estimate
  or the weaker `(ICV)` directly.
- The paper continues to state only `(REL)` as its minimal open lemma.  `(PL2)`
  is a selected sufficient bridge, not a claimed theorem.
