# ADR-0540: Test connected Adams Betti budgets over extension fields

Status: accepted
Date: 2026-08-20
Index-summary: Compute the connected fourth-cumulant trace over binary extension fields and refute the universal ell^4 normalized Betti budget without conflating that failure with the cohomology cutoff

## Context

ADR-0539 reduced one geometric proof route to two independent obligations:

```text
H_c^i=0 above degree 4ell,
total normalized Betti number at most ell^4.
```

The existing extension-field operation computes a one-class long-cycle trace.
It does not retain the full class distribution, the three Wick contractions,
or the connected product-constrained trace, so its Hankel sequence cannot test
this geometric target.

## Decision

Add `binary_extension_connected_adams_trace`.  Over `GF(q)`, it enumerates all
`q^n` monic degree-`n` polynomials, retains the Mangoldt population `N_e` in
each of the `q^ell` leading-coefficient classes, and computes exactly

```text
M_2=sum_e (N_e-q^(n-ell))^2,
M_4=sum_e (N_e-q^(n-ell))^4,
T_r=q^(2ell) (q^ell M_4-3M_2^2).
```

The operation is endpoint-only and resource bounded.  It checks the exact
Mangoldt conservation identity, cross-checks both base-field endpoints against
the independent Hayes transform, and reports the least integer `B` satisfying

```text
abs(T_r) <= B q^(2ell+2n).
```

Treat `B<=ell^4` as a stopping test, never as theorem evidence.

## Evidence

For `(ell,n)=(2,5)`, certified field moduli give

| `r` | `T_r` | minimum `B` |
|---:|---:|---:|
| 1 | `-8192` | 1 |
| 2 | `-100663296` | 1 |
| 3 | `10582799417344` | 3 |
| 4 | `700872692009533440` | 10 |
| 5 | `29950594846676670742528` | 26 |

The `r=5` row exhausts all `32^5=33554432` monic polynomials and takes 565.58
seconds in the debug test profile.  Since `ell^4=16`, it gives the exact
counterexample

```text
29950594846676670742528
  > 16 * 32^14
  = 18889465931478580854784.
```

The expensive row remains an explicit ignored probe; ordinary tests pin the
base-field agreement and the nontrivial `r=1,2,3` sequence in 0.32 seconds.

## Consequences

- The normalized Betti budget `ell^4` is false as a universal all-`ell`
  statement and must not appear as a proved or generally plausible lemma.
- This row does **not** refute vanishing above cohomological degree `4ell`.
  A larger Betti constant can produce the observed trace.
- It also does not refute a theorem explicitly scoped to `ell>=200`, the range
  needed after the finite degree-400 handoff.
- The next geometric test is to separate weight growth from multiplicity by
  recovering more of the reduced virtual zeta factor, or to derive an explicit
  replacement `B(ell)` and immediately replay it through the endpoint ledger.
- ADR-0541 performs that separation exactly at level two: the connected trace
  is `q^12(q-1)(q^2-6q+6)`, so its normalized degree is genuinely one above
  the proposed cutoff rather than a bounded multiplicity fluctuation.
