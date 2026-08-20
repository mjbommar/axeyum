# ADR-0534: Group Hayes characters by Galois orbit and exact order before bounding

Status: accepted
Date: 2026-08-20
Index-summary: Add an exact Ramanujan-orbit trace decomposition, refute one-unit orbit and fixed coefficient-four order-layer bounds, and preserve cancellation across character orders

## Context

The selected connected Carlitz trace sums power sums of power-of-two-valued
Hayes characters.  Odd powering is the Galois action on their cyclotomic value
fields.  A character of exact order `2^s` therefore has a rational orbit of
size `2^(s-1)`, and the sum over that orbit is an integral Ramanujan
projection.  Since generic orbits grow linearly with the conductor level, a
one-Weil-unit bound per orbit would provide exactly the missing linear saving.

## Decision

Add `hayes_galois_orbit_trace_report`.  It partitions every primitive
exact-conductor character under odd powering, reconstructs each signed
integral orbit trace from two independent NTT primes, groups the orbit traces
again by exact character order, and requires both aggregations to reproduce
the independently computed conductor layer.

The tempting orbit estimate

```text
abs(sum_(chi in orbit) S_n(chi)) <= 2^ceil(n/2)
```

is false.  At `(level,degree)=(7,15)`, 18 of 28 orbits violate it and the
maximum is `1696`, against allowance `256`.  Their signed total nevertheless
reconstructs the exact conductor trace `2944`.

Taking one more signed sum by exact character order helps but does not give a
small fixed constant.  At `(11,24)`, the exact-order layer traces include
`663552`, while

```text
(level-1) 2^ceil(degree/2) = 40960.
```

The required integral coefficient is therefore 17.  This refutes the tested
coefficient-four order-layer candidate.  The ordinary bounded test covers
both Lemire endpoint parities through level 12 and pins the smaller factor-two
and factor-three failures at `(3,8)` and `(6,14)` as controls.

## Consequences

- Galois orbits give an exact rational/Ramanujan representation, but applying
  an absolute value to every orbit is still too early.
- Exact character order is a more compressed intermediate layer, but no
  uniform constant-scale bound is credited.  A useful theorem may allow
  explicit conductor growth only if an endpoint ledger proves that the growth
  fits the connected allowance.
- Cancellation across exact character orders, conductor levels, or the full
  connected Carlitz trace remains essential.  The report is a bounded
  diagnostic and grants no Lemire theorem credit.

