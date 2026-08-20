# ADR-0552: Localize the long-cycle Euler trace before weighted bounds

Status: accepted
Date: 2026-08-20
Index-summary: Prove exact non-top long-cycle Euler cancellation away from power-of-two degrees, while retaining the Frobenius-weighted trace as the endpoint obligation

## Context

ADR-0550 reconstructs the von Mangoldt virtual character as the power sum
`p_n`.  For any virtual `S_n`-representation `H` and an `n`-cycle `c`,

```text
<character(H),p_n> = Tr(c | H),
```

because `p_n` is `n` on the `(n)` conjugacy class, zero elsewhere, and that
class has `(n-1)!` elements.  This permits a direct long-cycle analysis of
Sawin's ordered-root variety `X_(n,ell,0)` before splitting the character into
positive representations.

A naive fixed-locus argument is sound only when the cycle order is prime to
the characteristic.  At even degree the cycle is wild, so identifying the
trace with the Euler characteristic of the full fixed locus would be an
invalid use of the tame Lefschetz formula.

## Decision

Add the bounded native report `sawin_long_cycle_euler_report` for `n>=5`, the
exact range where Sawin's strict hypothesis gives one-dimensional trivial top
cohomology at the Lemire endpoint.  It first
certifies the full-cycle fixed locus.  A fixed tuple has the form
`(a,...,a)`, and its prescribed elementary symmetric functions are

```text
binom(n,j) a^j,  1<=j<=ell.
```

Lucas's theorem says that the least positive odd binomial index is
`q=2^v2(n)`.  Therefore the full fixed locus is a point when `q<=ell` and an
affine line otherwise.  At the Lemire endpoint
`ell=ceil(n/2)-1`, the affine-line case occurs exactly when `n` is a power of
two.  Both loci have compactly supported Euler characteristic one.

The report then applies the finite-order trace reduction of Deligne and
Lusztig rather than using the tame formula outside its domain.  Write

```text
n=q b,  q=2^v2(n),  b odd.
```

The prime-to-characteristic part of `c` has order `b`.  Its fixed tuples are
encoded by a monic degree-`q` block polynomial `G`, repeated `b` times, so the
degree-`n` root polynomial is `G(x)^b`.  If `b>1`, then `q<=n/3<=ell`.
Successively, the coefficient of degree `qb-j` in `G^b` is

```text
b g_j + a polynomial in g_1,...,g_(j-1).
```

Since the image of odd `b` in `GF(2)` is one, vanishing of the first `ell` coefficients forces all
`q` coefficients of `G` to vanish.  The fixed locus of the odd-order part is
therefore the single reduced point `G=x^q`.  The remaining `q`-power part of
the cycle acts trivially on that point.  Deligne--Lusztig reduction gives

```text
Tr(c | H_c^*(X_(n,ell,0))) = 1
```

for every `n` that is not a power of two.  The top compactly supported
cohomology is one-dimensional and trivial under `S_n`, so

```text
Tr(c | H_c,non-top^*(X_(n,ell,0))) = 0.          (E)
```

At a power-of-two degree the odd-order part is the identity and its fixed
locus is all of `X`; the report consequently returns no cycle-trace verdict.

Equation `(E)` is deliberately not promoted to the required estimate.  The
Lemire count contains

```text
Tr(Frob*c | H_c,non-top^*(X_(n,ell,0))),
```

and zero alternating trace after forgetting Frobenius does not bound that
weighted trace.  The report exposes this boundary with
`frobenius_weighted_cancellation_certified=false` in every row.

## Evidence

- Deligne and Lusztig, [*Representations of reductive groups over finite
  fields*](https://publications.ias.edu/sites/default/files/Number27.pdf),
  Section 3, supplies the finite-order decomposition
  `Tr(su,H_c^*(X))=Tr(u,H_c^*(X^s))` with `s` prime-to-characteristic and `u`
  of characteristic-power order.
- The native report checks the endpoint, Sawin's strict top-cohomology
  hypothesis, lowest-set-bit, odd/two-power cycle orders, fixed-locus
  dimensions, top degree, and trace subtraction.  An
  independent Pascal-recurrence test verifies the first odd binomial index
  through degree 128.
- Pinned rows cover odd degree 401, even composite degrees 12 and 402, and the
  exceptional power-of-two degree 512.  Degrees below five and
  resource-excessive inputs fail closed.

## Alternatives

- **Use the full fixed locus for every degree:** rejected because an even
  cycle is wild in characteristic two.
- **Treat zero Euler trace as zero Frobenius trace:** rejected because
  Frobenius can have different eigenvalues on cancelling cohomological pieces.
- **Infer a polynomial Betti bound from the zero virtual dimension:** rejected;
  virtual cancellation does not bound the dimensions of the positive and
  negative eigenspaces.

## Consequences

- The unweighted long-cycle complex has exact non-top Euler cancellation at
  every non-power-of-two degree.  This is a genuine structural theorem, not a
  finite diagnostic.
- Power-of-two degrees need a separate wild trace analysis even before
  Frobenius weights are introduced.
- For all other degrees, the remaining geometric obligation is now precisely
  a Frobenius-weighted refinement of an already zero virtual Euler trace.
- No Lemire existence fact changes status, and no endpoint theorem credit is
  granted.
