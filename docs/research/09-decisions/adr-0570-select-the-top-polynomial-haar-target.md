# ADR-0570: Select the top-polynomial Haar target

Status: accepted
Date: 2026-08-20
Index-summary: Replace the over-strong conductor-layer fourth-moment premise by one polynomial saving over Weil on the top logarithmic conductor window

## Context

ADR-0569 retained the sufficient conductor-layer estimate

```text
max_e |D_[j](e)|^2
 <= 4 ell^4 (j-1)^2 2^(j-1+n-2ell).
```

At the top level this asks the sibling maximum `H_j^*` to improve the proved
individual-Weil bound by roughly `2^((ell-1)/2)/(2ell^2)`.  Repricing the
already proved population-refinement Haar triangle shows that this is one
factor `ell` stronger than necessary.

Let

```text
H_j^* = max_b |N_j(b)-N_j(b(1+x^j))|.
```

The exact residual statement is

```text
(TOP-POLY)  (12 ell H_j^*)^2 <= 25 (j-1)^2 2^n
```

only for

```text
ell - 4 ceil(log2 ell) <= j <= ell,
n in {2ell+1,2ell+2}.
```

This is a factor `12ell/5` saving over individual Weil.  Below the displayed
window, the proved Weil estimate already fits the weighted Haar triangle.

## Decision

Select `(TOP-POLY)` as the load-bearing endpoint obligation.  Retain the
conductor-layer `4ell^4` fact as a valid but nonpreferred sufficient condition;
do not organize the proof or paper around it.

The native implication uses exact integer arithmetic.  At an even endpoint,
`2^(n/2)` is integral.  At an odd endpoint, `sqrt(2)<3/2` gives the rational
majorants

```text
individual Weil: H_j^* < 3 (j-1) 2^ell / 2,
TOP-POLY:        H_j^* < 5 (j-1) 2^ell / (8ell).
```

After scaling by the common denominator, the operation checks

```text
sum_(j<first) 2^(j-1) H_j^*
 + sum_(j>=first) 2^(j-1) H_j^* <= 2^(2ell)
```

for both parities and every tested symbolic row `200<=ell<=1024`.  The
geometric inequalities in the implementation establish the displayed
arithmetic implication; the finite loop is a regression, not theorem credit
for `(TOP-POLY)`.

## Consequences

- The paper-facing open lemma is a polynomial improvement on a logarithmic
  top window, not uniform square-root delocalization at every conductor.
- The fourth-moment conductor ladder remains useful structural analysis but is
  not the shortest closing route.
- Exact fixed-conductor recurrence does not refute `(TOP-POLY)`, because fixed
  levels eventually lie below the moving top window.
- The mathematical work is now to prove `(TOP-POLY)` uniformly; no Lemire
  theorem is claimed by this decision.
