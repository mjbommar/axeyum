# ADR-0511: Expand the fourth cumulant before classifying gcd strata

Status: accepted
Date: 2026-08-19
Index-summary: Decompose every class discrepancy by convolution order and subtract Wick pairings cellwise before gcd classification

## Context

ADR-0510 closes the simple fibrewise Heisenberg route. The remaining
fourth-moment attack must preserve cancellation across Möbius convolution
orders. Classifying gcd patterns after taking an absolute value at each order
would reproduce the known endpoint loss.

For `1<=d<ell`, define

```text
T_d(e)=d sum_(u in V_d) M_(n-d)(e u^(-1)).
```

Then `D_e=sum_d T_d(e)`. If `C_ab=sum_e T_a(e)T_b(e)`, the connected cell is

```text
K_(a,b,c,d)=2^ell sum_e T_a T_b T_c T_d
 -(C_ab C_cd+C_ac C_bd+C_ad C_bc).
```

## Decision

Make this symmetric connected-order tensor the input to gcd classification.
Verify the classwise sum against the independent Mangoldt distribution,
subtract all three Wick pairings in each cell, and require the
multiplicity-weighted cells to reconstruct `K_4` exactly.

## Evidence

The report passes both endpoints at `ell=4`, including a preallocation
resource decline. At `(ell,n)=(9,19)`, its `330` cells reconstruct
`K_4=-2086965956608`. The largest cell, `(7,7,7,7)`, is
`-70637290307584`; `(6,7,7,7)` and `(6,6,7,7)` are respectively
`54720169771008` and `-53267374669824`. Thus `K_4` uses substantial
cross-order cancellation.

## Consequences

- Gcd graphs must be attached inside signed tensor cells.
- Any future strata must reconstruct every cell and then `K_4`.
- Summing absolute cell bounds cannot be the intended endpoint proof.
- This is a bounded identity, not a uniform fourth-moment theorem.
