# ADR-0514: Replace the constant cylinder ceiling with a linear target

Status: accepted
Date: 2026-08-19
Index-summary: Refute the provisional constant-eight cylinder ceiling and retain the sufficient linear Carleson target

## Context

ADR-0513 introduced the exact Witt-cylinder ratio

```text
R_j(b)=2^(ell-j) sum_(e below b) D_e^4
       / (sum_(e below b) D_e^2)^2
```

and proposed `R_j(b)<=8` only as a fleet-tested diagnostic.  That ceiling was
not theorem evidence and the larger endpoint sweep has now refuted it.

## Decision

Retain the local Carleson representation, reject the constant-eight target,
and use the conjectural linear ceiling `R_j(b)<=ell` as the next exact theorem
obligation.  The native report checks this inequality without division and a
separate symbolic ledger checks its endpoint consequence.

## Evidence

The even row at `ell=12` contains

```text
1226465917304832 / 149099338469376 > 8,
```

and the even row at `ell=15` contains

```text
6962575342305280 / 744051749945344 > 9.
```

Thus no argument may use the provisional constant eight.  Both endpoint
parities satisfy the linear ceiling through `ell=19`; this remains finite,
uncredited evidence.

The simpler sufficient bound by a cylinder maximum is already false.  At the
root of `(ell,n)=(8,17)`, its exact max-to-average ratio is
`6150400/693360>8`, while the aggregate `R_0<=8` inequality still holds.  A
proof must therefore retain distribution across descendants rather than
replace `sum f_e^2` by `(max f_e) sum f_e`.

The proved second-moment envelope gives `M_2<=ell^2 2^n`.  At the two endpoint
degrees the root case of the linear target therefore implies

```text
M_4 <= ell M_2^2 / 2^ell <= 16 ell^5 2^(3ell).
```

The existing exact fourth-moment implication verifies that this closes all
endpoints from degrees `401` and `402`, with degrees through `400` delegated to
the separate finite certificates.

## Consequences

- ADR-0513 remains the accepted representation and diagnostic decision; only
  its provisional numerical target is superseded here.
- Finite satisfaction of `R_j(b)<=ell` grants no theorem credit.
- Pointwise max-to-average domination is a checked failed route.
- The proof frontier is now the uniform linear local concentration estimate,
  not another exponent-ledger optimization.
