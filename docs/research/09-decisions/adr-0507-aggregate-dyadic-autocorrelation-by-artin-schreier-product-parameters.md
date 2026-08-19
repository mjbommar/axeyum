# ADR-0507: Aggregate dyadic autocorrelation by Artin--Schreier product parameters

Status: accepted
Date: 2026-08-19
Index-summary: Preserve dyadic cancellation by grouping exact fibres first by shift and inverse difference, then by the normalized product parameter and valuation

## Context

ADR-0506 rejects a uniform quadratic estimate on each exact affine
Artin--Schreier fibre.  At `(ell,k,d)=(9,11,8)`, taking absolute values on
those fibres loses far more than the complete signed off-diagonal
correlation.  A useful next representation must combine fibres using an
algebraically canonical parameter before applying an absolute value.

For a contributing pair put

```text
h=f+g,                 w=f^(-1)+g^(-1)=h/(fg),
h=x^v h_0,             w=x^v w_0.
```

Then `ord_x(h)=ord_x(w)=v`, and cancellation of the common power gives the
normalized parameter

```text
h_0/w_0 = fg = f(f+h) mod x^(ell+1-v).
```

Thus it is exactly the right-hand side of the truncated Artin--Schreier
equation, not a heuristic label.

## Decision

Extend `binary_dyadic_autocorrelation_fibre_report` with a checked aggregation
hierarchy:

1. exact affine fibres `(input coset,h,w)`;
2. exact pairs `(h,w)`, after combining input cosets;
3. normalized parameters `(v,h_0/w_0)`;
4. complete `x`-adic valuation layers `v`.

The implementation rejects unless `h_0/w_0` independently equals
`f(f+h)` for a representative of every exact fibre, and continues to require
that the final signed value reconstruct the existing energy ledger.

Treat every intermediate absolute sum as a bounded CAS diagnostic.  In
particular, do not promote the tempting estimate
`valuationwise_absolute_correlation <= 2^(d+1)`: the finite endpoint matrix
already refutes it.

## Evidence

At `(ell,k,d)=(9,11,8)`, the absolute correlation falls through the hierarchy

```text
exact fibres                  33680
(h,w) pairs                   16972
(v,h_0/w_0) parameters         3956
valuation layers                388
complete signed total            68
```

The valuationwise value is `672` at `(ell,k,d)=(9,12,8)`, exceeding
`2^(d+1)=512`.  Across the selected odd and even endpoint rows with
`5<=ell<=9`, valuation aggregation consistently retains much more
cancellation than either fibrewise or normalized-parameterwise absolute
values.  This is finite evidence for the representation only, not a uniform
bound.

A broader tail sweep makes the boundary sharper.  The coefficient-one
valuationwise square-root estimate also fails and its excess grows: at
`(ell,k,d)=(10,13,9)`, the valuationwise absolute sum is `2502`, so its square
is about `1.49*2^(k+d)`.  The complete signed sum is only `-314` on that row.
The surviving connected diagnostic is therefore

```text
abs(off_diagonal)^2 <= 2^(k+d+1),
```

which keeps all valuation layers combined.  It holds on every endpoint row
through `ell=9` and the selected tail through `ell=10`; the smaller bound
without the factor two fails at `(6,9,5)`, where the signed value is `138`.
These remain finite tests, not evidence for the universal inequality.

## Consequences

- The next local theorem must combine valuation layers through
  Witt/conductor orthogonality rather than take their absolute values.
- The normalized layer can be studied through the family
  `f^2+h f=a mod x^(ell+1-v)` with `a=h_0/w_0`.
- A valid bound must be fed back into the endpoint ledger with its actual
  polynomial factors and losses.
- No Lemire endpoint theorem credit is granted by this diagnostic.
