# Lean Nat geometric reindexing R4.6 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1;
[ADR-0393](../research/09-decisions/adr-0393-checked-geometric-sum-reindexing.md).

## Result

`Nat.mul_sumRange_pow` is a generic zero-axiom theorem connecting the half-open
power sum to its one-based reindexing:

```text
forall a n,
  a * sumRange (fun i => pow a i) n
    = sumRange (fun i => pow a (succ i)) n
```

The kernel checks its induction proof from existing proved Nat laws. This
replaces the Rado capability test's specialized `geo_shift` recurrence bridge
with reusable prelude surface and handles the paper's empty `k = 3` inner sum
without a side condition.

The focused Nat run passes nine tests. The package inventory now checks six
definitions and 28 theorems. Positive controls apply the theorem at the empty
range and at `a = 3, n = 4`; a twelfth declaration-level mutation control
requires rejection when a valid range-two proof is assigned the range-three
target. Determinism and the zero-axiom walk remain green.

All 211 kernel library tests, every kernel integration suite and doctest,
strict all-target/all-feature Clippy, and strict rustdoc pass locally.

## Boundary

This closes the specific geometric reindexing dependency, not R4.6 as a whole
and not `thm:sharp`. Generic sum congruence/distribution and the exact paper
factorization remain, followed by subtraction, range, divisibility, and colour
obligations. The paper's theorem receives no credit from this library lemma.
