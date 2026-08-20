# ADR-0515: Prioritize the aggregate connected-cumulant bound

Status: accepted
Date: 2026-08-19
Index-summary: Target root kurtosis at most four so every convolution order cancels before any absolute value

## Context

ADR-0514 retains the sufficient local target `R_j(b)<=ell`, but the largest
local ratios grow with `ell` while the root ratio remains close to three.  The
root identity is

```text
R_0 = 2^ell M_4/M_2^2
    = 3 + K_4/M_2^2,
```

where `K_4=2^ell M_4-3M_2^2` is the connected fourth-cumulant numerator.

## Decision

Make `K_4<=M_2^2`, equivalently `R_0<=4`, the primary aggregate theorem
target.  Keep the local linear statement as an alternate martingale route.
The native CAS must check both equivalent finite forms and separately verify
the endpoint implication.

## Evidence

Both endpoint parities satisfy the bound through `ell=23`.  The exact new root
ratios at `(ell,n)=(22,46),(23,47),(23,48)` are approximately `2.999670`,
`2.994842`, and `3.001146`.  All three rows also satisfy the stronger local
linear cylinder ceiling, while all three fail the max-to-average dominance
shortcut.  The ignored fleet probes are bound to exact commit `03d7502bb` and
their full result/resource logs are content-hashed in the canonical research
note.  Finite satisfaction grants no theorem credit.

The proved estimate `M_2<=ell^2 2^n` turns the assumption into

```text
M_4 <= 4 M_2^2/2^ell <= 64 ell^4 2^(3ell)
```

at both endpoints.  The exact fourth-moment ledger verifies the finite handoff
and proper-power margins from degrees `401` and `402`.

## Consequences

- This target directly addresses cross-order cancellation rather than bounding
  the connected tensor cellwise.
- The conductor identity rewrites it as total nonprincipal square energy at
  most `3 M_2^2`.  The all-level geometric estimate is false at conductor one
  for even `ell=20`; the accepted diagnostic is a buffered low block below
  `ceil(ell/2)` plus the geometric high-conductor tail, which still sums to
  exactly `3 M_2^2` and survives both `ell=20` endpoints.
- The statement remains conjectural until a uniform argument is supplied.
