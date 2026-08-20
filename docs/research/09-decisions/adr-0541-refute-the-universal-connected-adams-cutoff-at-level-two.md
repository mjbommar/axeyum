# ADR-0541: Refute the universal connected Adams cutoff at level two

Status: accepted
Date: 2026-08-20
Index-summary: Derive the exact level-two degree-five connected trace from the characteristic-two trace-subtrace formula and prove that its normalized q-degree exceeds the proposed cutoff by one

## Context

ADR-0540 found that the normalized coefficient required by the connected trace
at `(ell,n,r)=(2,5,5)` is 26 rather than `ell^4=16`.  One finite violation of
that coefficient does not distinguish a larger Betti multiplicity from
cohomology of a weight above the proposed degree-`4ell` cutoff.

The first two leading coefficients of a monic polynomial are its trace and
subtrace.  Theorem 2 of Ri--Myong--Kim--Rim, *The Number of Irreducible
Polynomials over Finite Fields of Characteristic 2 with Given Trace and
Subtrace* ([arXiv:1304.0521](https://arxiv.org/abs/1304.0521)), gives the exact
element count for every pair.  Element counts equal the polynomial-Mangoldt
class populations used here.

## Decision

Add `binary_extension_ell_two_degree_five_closed_form`.  For `q=2^r`, the
source theorem at `n=5=4*1+1` specializes to

```text
N_(t,0)=q^3+(-1)^r(q-1)q,
N_(t,s)=q^3-(-1)^r q,             s != 0.
```

There are `q` zero-subtrace classes and `q(q-1)` nonzero-subtrace classes.
The CAS expands their exact moments and obtains

```text
M_2 = q^4(q-1),
M_4 = q^5((q-1)^4+(q-1)),
q^ell M_4-3M_2^2 = q^8(q-1)(q^2-6q+6),
T_r = q^12(q-1)(q^2-6q+6).
```

Retain the leading `q`-degree, Adams weight degree, normalized degree, proposed
degree, and their excess as typed exact output.

## Evidence

The closed form agrees with independent exhaustive polynomial enumeration for
`r=1,2,3` in ordinary tests and for the pinned `r=4,5` ignored stopping rows.
It reproduces every exact moment and the connected trace, not merely its sign
or magnitude.

The trace polynomial has degree 15.  Removing the Adams weight `q^(2n)=q^10`
leaves degree 5.  The proposed degree-`4ell` compact-support cutoff permits
only normalized growth `q^(2ell)=q^4`.  The one-degree excess is exact and
persists as `r` grows; no fixed Betti constant can absorb it.

## Consequences

- The degree-`4ell` cutoff in ADR-0539 is false as a universal all-`ell`
  statement, independently of the already-refuted `ell^4` Betti coefficient.
- The failure is a weight/dimension obstruction, not merely unexpectedly large
  finite multiplicity.
- This fixed-level calculation does not logically refute a different theorem
  scoped to `ell>=200`, but it removes any presumption that Wick subtraction
  automatically lowers the top cohomology to degree `4ell`.
- Before pursuing large-conductor Betti estimates, the next geometric task is
  to identify the surviving top-weight stratum in general `ell` and determine
  whether it cancels only after another operation relevant to the endpoint.
