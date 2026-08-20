# ADR-0550: Certify the long-cycle Foulkes compression without granting a cyclic Betti bound

Status: accepted
Date: 2026-08-20
Index-summary: Reconstruct the von Mangoldt long-cycle character from cyclic Foulkes modules with exact coefficient mass 2^omega(n), and isolate the still-unproved cyclic cohomology bound

## Context

Sawin's short-interval geometry packages every degree-`n` factorization
function into the compactly supported cohomology of one ordered-root complete
intersection.  His Lemma 3.3 identifies the von Mangoldt function with the
alternating exterior powers of the standard `S_n` representation.  The
corresponding virtual character is

```text
V_n=lambda_(-1)(std),
ch(V_n)=p_n,
```

so it is `n` on an `n`-cycle and zero on every other conjugacy class.  Sawin
obtains his published estimate by splitting the exterior powers into two
positive representations and applying a generic Betti bound to each.  At
fixed `q=2`, that bound is exponentially too large for the Lemire endpoint.

Foulkes's formula, in the notation of Shareshian and Sundaram, is

```text
F_(n,r)=Ind_(C_n)^(S_n) theta_r,
ch(F_(n,r))=(1/n) sum_(d|n) c_d(r) p_d^(n/d).
```

This makes it possible to compress the same virtual character into cyclic
eigenspaces before applying any absolute value.  Because this step changes
the apparent coefficient size dramatically, it must be checked exactly and
must not be conflated with the missing cohomological estimate.

## Decision

Add `sawin_foulkes_endpoint_ledger` to the native CAS.  It certifies, by exact
Ramanujan orthogonality,

```text
p_n = sum_(r mod n) c_n(r)/phi(n) F_(n,r).
```

The `n` residue-indexed modules have only `tau(n)` distinct characters.
Grouping equal characters gives the integral form

```text
p_n = sum_(k|n) mu(k) F_(n,n/k).
```

Thus the exact triangle coefficient mass is

```text
sum_(k|n) |mu(k)| = 2^omega(n)=n^o(1).
```

The implementation computes every `c_n(r)` twice: once from the divisor sum
and once from the von Sterneck totient formula.  It then checks all divisor
power-sum coefficients, the grouped Möbius coefficients, and the `l1` mass.
Explicit degree and residue-by-divisor work limits are checked before the
certificate table is allocated.

For the Lemire endpoints write

```text
ell=ceil(n/2)-1,
h=n-ell.
```

Sawin's characteristic-two weight exponent is exactly `W/2`, where

```text
W=h+floor(n/2)-floor(ell/2)+1
 =2h-floor(ell/2).
```

If every cyclic Foulkes summand had effective Betti multiplicity at most `B`,
the resulting triangle proves a degree-`n` irreducible exactly when

```text
(2^omega(n) B)^2 2^W < (2^h-P_n)^2,                (CF)
```

where `P_n=1` at the odd endpoint.  At the even endpoint the checked
proper-power envelope is

```text
P_n <= (n/2) 2^(n/2-floor(ell/2)) + n 2^ceil(n/3).
```

The CAS takes `B` as a hypothetical input and checks `(CF)` with integers.  It
also inserts Sawin's published generic bound

```text
B <= 3(n+2)^(n+ell),
```

which fails the endpoint comparison.  At the first two degrees beyond the
certified finite handoff, `(CF)` permits respectively

```text
n=401: B <= 2^49-1,
n=402: B <= 2^47-1.
```

These large margins show why a polynomial effective cyclic bound would be
enough, but no such bound is proved here.

The companion `check_sawin_foulkes_polynomial_betti_sufficiency` turns one
particularly clean target into an all-degree implication.  Since
`2^omega(n)<=rad(n)<=n`, the hypothesis

```text
B(n,r) <= n^4  for every n>=401 and every required r
```

makes the squared cost at most `n^10`.  Twelve exact base checks at
`n=401,...,412` reserve half the main term for proper powers and give

```text
n^10 < 2^(floor(ell/2)-2).
```

The checked twelve-degree step

```text
(n+12)^10 < 8n^10
```

holds first at `n=401` and its left/right ratio decreases with `n`, while the
reserved squared margin grows by eight.  Over the same step the exact odd
proper-power term stays one; each of the two even-envelope terms grows by less
than `16` or `32`, while half the main term grows by `64`.  This proves both
the error and proper-power reserves for all `n>=401`.  The same report rejects
the quintic target at the finite handoff; quartic is a sufficient explicit
research target, not a claim about what geometry has established.

## Evidence

- Sawin, [*Square-root cancellation for sums of factorization functions over
  short intervals in function fields*](https://arxiv.org/abs/1809.05137),
  Lemma 3.3 and the propositions labelled `cohomologyestimate` and
  `bettibound`, supplies the factorization-function character and the exact
  cohomological weight exponent.
- Shareshian and Sundaram,
  [*Ramanujan sums and rectangular power sums*](https://arxiv.org/abs/2305.12007),
  the theorem labelled `Foulkes`, records the exact induced-character formula
  and both divisor-sum and von Sterneck formulas for Ramanujan sums.
- Focused native tests pin the complete `n=12` Ramanujan vector, every divisor
  coefficient, the grouped Möbius expansion, both degree-400 handoff rows,
  strict equality failure, odd/even proper-power reserves, the quartic
  all-degree implication, the quintic handoff failure, and resource/parameter
  declines.

## Alternatives

- **Use the parity-split exterior-power bound:** rejected because it replaces
  the signed long-cycle character by two generic positive complexes and
  reproduces Sawin's fatal exponential Betti factor.
- **Transfer the coherent Koszul long-cycle trace to etale cohomology:**
  rejected by ADR-0526; the generic smoothing in the source is not
  `S_n`-equivariant, and no transfer theorem for the singular wild fibre is
  available.
- **Treat `2^omega(n)` as the missing theorem:** rejected.  It controls only
  the coefficients of the virtual representation, not the dimensions or
  Frobenius traces of its cyclic cohomology eigenspaces.

## Consequences

- The representation-theoretic part of the long-cycle bridge is now exact,
  bounded, and replayable in Axeyum.
- The Sawin route has one sharply stated remaining theorem: bound the effective
  cyclic-eigenspace Betti multiplicity by `n^4` (or otherwise below the exact
  integer margin in `(CF)`), or directly bound the Frobenius--long-cycle trace,
  uniformly beyond the finite handoff.
- No endpoint or all-degree Lemire fact changes status.  The new report is a
  conditional exponent ledger and cannot serve as evidence for the open
  conjecture.
