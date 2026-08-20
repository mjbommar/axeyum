# ADR-0529: Shard extension traces and require characteristic-two hook control

Status: accepted
Date: 2026-08-19
Index-summary: Make long-cycle traces deterministically mergeable, compress exact Frobenius orbits, and reject characteristic-zero symmetric-cohomology bounds as an endpoint bridge

## Context

ADR-0527 added exact fixed-degree Mangoldt traces over `GF(2^r)`.  The first
four-fixed-coefficient row has population `(2^r)^5`, so the next useful traces
quickly exceed a single bounded process.  They are finite stopping tests for a
small reduced zeta factor, not theorem evidence.

The geometric alternative is to bound the hook-isotypic part of the
compactly-supported etale cohomology of the singular affine short-interval
complete intersection in characteristic two.  Nearby symmetric-cohomology
results do not have that scope.  [Chenevert's symmetric smooth-projective
hypersurface calculation](https://arxiv.org/abs/0908.1748) assumes `n! != 0`
in the ground field.  The [Basu--Riener multiplicity
bounds](https://arxiv.org/abs/1610.04946) concern rational cohomology of
symmetric semi-algebraic sets over a real closed field.  Neither applies to
the wild binary quotient used here.

## Decision

Add three exact CAS surfaces:

1. `binary_extension_long_cycle_trace_shard` partitions the complete encoded
   coefficient interval using exact `u128` endpoints.  It enumerates only the
   least encoded representative of each coefficientwise Frobenius orbit and
   multiplies its Mangoldt weight by the exact orbit size.
2. `combine_binary_extension_long_cycle_trace_shards` sorts and checks a
   complete shard set and fails closed on missing, duplicated, noncontiguous,
   or differently parameterized input before returning the exact trace.
3. `collapse_binary_extension_long_cycle_trace_subshards` verifies that a
   complete contiguous block from a commensurable fine partition exactly
   covers one coarse parent range.  This permits hierarchical fleet execution
   without synthesizing or trusting unchecked aggregate JSON.

The companion native executable emits one canonical JSON shard or merges a
complete set.  `extension_trace_hankel_minor` computes an exact fraction-free
Hankel determinant.  A nonzero `(d+1)`-square minor proves only that the
observed trace sequence has no constant-coefficient recurrence of order at
most `d`; it does not infer a uniform recurrence from finite data.

Do not cite smooth complex or real semi-algebraic symmetric-cohomology bounds
as the missing long-cycle theorem.  Any proof using this route must establish
hook-isotypic compact-support control in characteristic two, including the
singular/wild contribution.

## Evidence

Ordinary tests compare the orbit-compressed trace against naive enumeration
over `GF(4)` and `GF(8)`, reconstruct the full population from exact orbit
sizes, round-trip shard JSON, and exercise missing, duplicated, mismatched,
and invalid shard failures.  Seven uneven shards merge to the same `GF(4)`
trace as direct execution.

For `(n,m)=(9,4)`, exact traces

```text
(A_1,A_2,A_3,A_4,A_5,A_6,A_7)
  = (5,129,-1771,-3855,-28675,-277767,-2479675)
```

give nonzero consecutive `3 x 3` Hankel determinants

```text
det H_(1,2) =   7,972,848,576,
det H_(2,2) = 569,010,016,512,
det H_(1,3) = -6,852,895,898,075,136.
```

Thus the first nonsupersingular stopping row is not a one-, two-, or three-mode
trace sequence.
The `A_6` computation merged 64 deterministic shards covering all
`64^5=1,073,741,824` candidates.  Its exact Mangoldt sum was `1,073,464,057`.
The `A_7` computation covered all `128^5=34,359,738,368` candidates.  Fifty-four
coarse shards completed directly; 640 fine shards collapsed into the ten
skewed parents before the checked 64-parent merge.  The exact Mangoldt sum was
`34,357,258,693`; the merged JSON SHA-256 is
`70861100bd819777089e997dfc6023972acbe5366fe15962192b6c57a1d02c7c`.
The fine-shard manifests cover 52.997 aggregate process-hours, with 0.71--557.56
seconds per child and 2,692 KiB maximum recorded RSS.  Every admitted child had
empty stderr.

## Consequences

- Large extension traces have a deterministic native execution and merge
  path; ad hoc external-CAS splitting is unnecessary.
- Frobenius compression is an exact quotient, not a sampling heuristic.
- Every explanation with at most three recurrence modes is rigorously excluded
  for this finite row.
- This result is deliberately non-credit-bearing for Lemire's conjecture.  A
  bounded number of traces cannot bound the recurrence order as `m` grows.
- The live proof obligation remains a characteristic-two long-cycle/hook
  theorem or an analytic connected-convolution estimate with the required
  endpoint margin.
