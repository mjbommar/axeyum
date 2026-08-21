# ADR-0586: Measure the complete low-twist shell before claiming cohomology concentration

Status: accepted
Date: 2026-08-21
Index-summary: Reconstruct the joint high-character and exact-low-twist Frobenius trace over binary extension fields and refute repeated weight drops from affine-shell dimension alone

## Context

ADR-0585 proves that Sawin's product monodromy kills the top compactly
supported cohomology of every fixed nontrivial shifted high-character trace.
The remaining statement `(WITT-LOW)` concerns all lower cohomology at fixed
`q=2`.  One possible strengthening was to sum the complete exact-conductor
twist layer before applying weights.  A layer-`i` twist varies over an affine
shell of dimension `i`; if each added parameter forced another cohomological
drop, the first `O(log ell)` layers could provide the polynomial saving needed
by the aggregate identity-path ledger.

That mechanism must be tested on the complete signed layer, not on individual
characters or on a fourth moment.  For a binary extension field of order
`q=2^r`, let `D(g)` be the centered degree-`n` Mangoldt population on the
`q^ell` leading-coefficient classes.  Fix a coarse cutoff `c`, put
`R=q^(ell-c)`, and for each coarse class `a` set

```text
w(a)=R sum_(g above a) D(g)^2-(sum_(g above a)D(g))^2,
A_i=sum_(a whose first i coordinates vanish) w(a).          (A)
```

The q-ary version of ADR-0583's Fourier calculation gives

```text
T_i(q)=q^c (q^i A_i-q^(i-1)A_(i-1)).                       (T)
```

This is the unnormalised correlation summed over every high character and
every low twist of exact conductor `i`.  Consequently `T_i(2^r)` is a genuine
Frobenius-trace sequence for the connected family relevant to `(WITT-LOW)`.

## Decision

Add the bounded operation `binary_extension_witt_shifted_trace`.  It builds
the complete extension-field Mangoldt class vector, independently rechecks
global conservation through the connected-moment constructor, forms every
nonnegative conditional covariance in `(A)`, and returns all signed layers in
`(T)`.  The operation uses integer coefficient cylinders and no numerical
roots of unity.  Invalid endpoints, cutoffs, resource limits, malformed class
partitions, and negative conditional covariances fail closed.

The first nontrivial family has an exact closed form.  At
`(ell,n,c)=(3,7,2)`, the characteristic-two degree-seven population formula is

```text
N(t_1,t_2,t_3)=q^4-q+q^3  if t_2=t_1^2 and t_3=t_1^3,
                  q^4-q   otherwise.                       (P)
```

The centered values are `q(q^2-1)` and `-q`.  In a fixed coarse
`(t_1,t_2)` fibre, direct substitution in `(A)` gives

```text
w(t_1,t_2)=q^6(q-1)  if t_2=t_1^2,
                     0  otherwise.                         (W)
```

There are `q` supported coarse classes, exactly one above the identity after
fixing the first coordinate, and the same one after fixing both.  Therefore

```text
A_0=q^7(q-1),       A_1=A_2=q^6(q-1),
T_1(q)=0,
T_2(q)=q^9(q-1)^2.                                      (CLOSED)
```

The conductor-two trace has q-degree `11`.  Before monodromy cancellation,
the two Adams traces contribute degree `n=7`, primitive conductor-three
characters contribute dimension `3`, and exact conductor-two twists
contribute dimension `2`, for formal top degree `12`.  Thus the complete
low-twist shell removes exactly one full q-degree in `(CLOSED)`, not one drop
per twist parameter.  Full enumeration independently reproduces

```text
q=2: T_1=0, T_2=512,
q=4: T_1=0, T_2=2359296.
```

The next endpoint controls agree with the stopping conclusion.  At
`(ell,c)=(4,3)`, the translation-forced layer vanishes for degree `9` at
`i=1` and for degree `10` at `i=2`, while other layer signs need not be stable
under extension:

```text
             q=2                         q=4
n=9   (0, 1024, -7168)          (0, 43941888, 76677120)
n=10  (9984, 0, -4608)          (842858496, 0, 2196504576).
```

Reject the generic inference

```text
dimension of the exact-low-twist shell
    => repeated compact-cohomology concentration.
```

Any further geometric proof must use special cancellation in the complete
alternating lower trace, the Adams/Mobius virtual representation, or the
cross-conductor sum.  Generic lissity, affineness, product monodromy, and the
number of low-twist parameters prove only the already recorded top-term
vanishing.

## Evidence

- `witt_shifted_trace_matches_degree_seven_closed_form` checks `(CLOSED)`
  against exhaustive polynomial enumeration over both `GF(2)` and `GF(4)`.
- `witt_shifted_trace_declines_outside_its_exact_domain` checks the endpoint,
  cutoff, and extension-degree refusal paths.
- `axeyum-gf2-extension-trace --witt-shifted` emits the complete exact integer
  layer table and reproduced the four `(ell,n,q)` controls above.
- The closed-form proof is symbolic substitution in `(P)` and `(A)`; the
  finite rows are independent controls rather than the universal step.

## Consequences

- The extension-field trace machinery now addresses `(WITT-LOW)` itself,
  rather than the older connected fourth cumulant.
- The conductor-one zero in `(CLOSED)` matches translation; the positive
  conductor-two layer proves that this symmetry does not propagate to the
  whole affine shell.
- The result does not refute an asymptotic bound after summing all requested
  `j` and `i`, nor does it refute cancellation special to the two-Mobius
  virtual trace.  It refutes only the proposed dimension-only reason for such
  a bound.
- `(WITT-LOW)`, `(REL)`, and Lemire's conjecture remain unproved.
