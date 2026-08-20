# ADR-0568: Reduce the wild moment to conductor-layer delocalization

Status: superseded by ADR-0569
Date: 2026-08-20
Index-summary: Replace the undifferentiated wild fourth-moment target by an exact conductor martingale and one square-root sup bound with polynomial loss allowed

## Context

Write `D_e=N_n(e)-2^(n-ell)` for the endpoint Hayes-class discrepancy and let
`P_j` denote averaging over the kernel of `E_ell -> E_j`.  The exact conductor
martingale differences are

```text
D_[j]=P_j D-P_(j-1)D,                 D=sum_(j=1)^ell D_[j].
```

The existing Hayes `L`-degree theorem and characterwise Weil bound give

```text
||D_[j]||_2^2 <= 2^(n-ell+j-1)(j-1)^2.                 (1)
```

The phase-two conductor audit found that grading by these orthogonal layers,
rather than by Möbius convolution order, removes the exponentially growing
absolute-value loss.  It leaves one arithmetic statement.  For some constants
`C>0` and `a>=0`, uniformly at `n=2ell+1,2ell+2`, require

```text
max_e |D_[j](e)|^2
  <= C ell^a (j-1)^2 2^(j-1+n-2ell).                  (SUP-L)
```

This is square-root cancellation across the exact-conductor character family.
The individual Weil triangle bound is `(SUP-L)` with squared constant
`2^(j-1)`.  Consequently `C=4,a=0` is already a theorem for `j<=3`; only
`j>=4` is new.

## Decision

Make `(SUP-L)` the primary reduced analytic obligation and expose it as a
conjectured fact, with the finite normalization explicitly non-credit-bearing.
Retain polynomial loss: an absolute constant is attractive but unnecessary.

Combine `(SUP-L)` with (1) and
`||f||_4<=||f||_infinity^(1/2)||f||_2^(1/2)`.  Minkowski and

```text
sum_(r=1)^(ell-1) r 2^(r/2) < (5/2) ell 2^(ell/2)
```

give the checked envelope

```text
M_4 <= 625 C ell^(a+4) 2^(3ell).                       (2)
```

The existing proper-power-aware fourth-moment ledger proves that (2), with
any fixed `C,a`, eventually makes the identity Hayes class contain an
irreducible.  For the concrete diagnostic target `C=4,a=0`, it verifies the
degree-400 handoff at degrees 401 and 402.

The CAS must retain three separate objects:

1. the exact conductor decomposition and its telescoping kurtosis product;
2. the finite rational constant required on an enumerated row; and
3. the symbolic implication from an assumed `(C,a)` bound to endpoint
   positivity.

Only the third object is an implication.  The second cannot establish the
universal premise.

## Consequences

- The earlier instruction to merely remove the `p>n` hypothesis from
  Hast--Matei is retired: even a repaired singular-locus lemma leaves an
  uncontrolled degree-dependent Betti constant.
- The unresolved mathematics is a pointwise exact-conductor delocalization
  theorem, not another unrestricted fourth-moment table.
- The bottom levels `j<=3` are discharged unconditionally for `C=4`; work may
  start at `j=4`.
- Finite tests through `ell=20` supported `C=4,a=0`, but a later exact
  `(ell,n,j)=(27,56,4)` row refuted it; ADR-0569 records the correction.
- No Lemire theorem is established by this decision.
