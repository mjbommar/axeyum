# ADR-0487: Keep the half-interval Möbius sieve as a bounded CAS diagnostic

Status: accepted
Date: 2026-08-19
Index-summary: Check the exact half-interval Möbius identity and its positive-composite parity counterexample in bounded axeyum-cas APIs, without promoting divisor weights into SMT

## Context

The Lemire interval has exact divisibility density through the full half-degree
level.  This suggests the truncated weight

```text
w_m(f)=sum_(D|f, deg D<=m) mu(D),  m=floor(deg(f)/2).
```

The aggregate weight over the constant-one interval is exactly one.  If this
weight were nonpositive on every composite, it would prove the conjecture by a
one-line lower-bound sieve.  That pointwise sign is false, and silently using it
would turn an exact CAS calculation into a false mathematical claim.

The existing `gfp` module already supplies native Berlekamp factorization.
Neither symbolic expressions nor an SMT decision problem are needed to check
the divisor-degree identity or a counterexample.

## Decision

Add `half_interval_mobius_sieve_report` to the bounded `gf2_hayes` research
surface.  It will:

1. derive the interval size and aggregate truncated weight with exact bignums;
2. compute the truncated Möbius weight of caller-supplied distinct-factor
   degrees by a checked generating-polynomial recurrence;
3. enforce explicit degree and half-level limits before allocation; and
4. retain a native factorization control for the first positive composite.

Keep this operation CAS-local.  Do not add Möbius weights, polynomial
factorization, or sieve constraints to `axeyum-ir`, `axeyum-solver`, or SMT-LIB.
The remaining theorem is a Type-II/bilinear or equivalent Hayes-character
cancellation statement, not a satisfiability encoding.

## Evidence

For every monic constant-one divisor `D` of degree `d<=m`, triangular division
gives exactly `2^(m-d)` multiples in the interval.  Removing the prime `x` from
the polynomial Euler product gives

```text
product_(P != x)(1-u^deg(P))=(1-2u)/(1-u)=1-u-u^2-...,
```

and therefore aggregate weight one.  Axeyum's Berlekamp factorization checks

```text
x^10+x^5+x^3+x^2+x+1
  =(x+1)(x^2+x+1)^3(x^3+x+1).
```

Its distinct factor degrees are `1,2,3`, so the degree-five truncated weight is
`1-3+3=1`, despite the polynomial being composite.  Focused unit tests check
the aggregate identity through the default admitted range, the factorization,
the positive weight, and malformed/resource-limited declines.  All-target,
all-feature CAS Clippy passes with warnings denied.

## Alternatives

- Treating aggregate weight one as a prime lower bound was rejected because the
  degree-10 composite has positive weight.
- Using SymPy or another external CAS was rejected because Axeyum already has
  exact factorization and the external result would add no independent trust.
- Adding a sieve theory to SMT was rejected because it would encode the known
  finite identities but could not prove the missing uniform cancellation.

## Consequences

- The failed elementary route is replayable and cannot be accidentally cited as
  a proof.
- Future work has an exact boundary: add genuine Type-II information or return
  to the fourth-moment/conductor estimate.
- No public solver logic, model, evidence envelope, or dependency direction is
  changed.
