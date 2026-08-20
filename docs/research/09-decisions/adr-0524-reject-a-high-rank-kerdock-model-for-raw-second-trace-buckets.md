# ADR-0524: Reject a high-rank Kerdock model for raw second-trace buckets

Status: accepted
Date: 2026-08-19
Index-summary: Retain pairwise second-trace forms long enough to refute a uniform high-rank Kerdock model before returning to connected cross-bucket cancellation

## Context

The binary Möbius sign is the Arf invariant of a nondegenerate second-trace
quadratic space.  The bridge audit proposed retaining those quadratic forms
inside simultaneous coefficient/inverse buckets.  If their pairwise
differences occupied a bounded collection of uniformly high-rank types,
Kerdock or Delsarte--Goethals theory could plausibly supply the missing
cancellation.

Per-polynomial Arf signs cannot test this: they discard the polar forms and
their radicals before the comparison is made.

## Decision

Add `binary_second_trace_bucket_difference_report`.  For every unordered
distinct squarefree pair in every simultaneous bucket, it evaluates the two
second-trace forms on the common coefficient space, computes the polar rank of
their difference, finds an exact radical basis, tests the phase on that
radical, and checks the resulting quadratic Gauss-sum magnitude directly.

The bounded rows `(ell,k,d)=(6,8,5),(7,9,6),(8,10,7),(9,11,8)` are pinned.  In
the last row, 28,830 pairs realize ten types and every even rank from zero to
ten.  Five phase-trivial pairs have rank two and radical dimension nine.  At
the first two rows, distinct forms already have phase-trivial rank zero and
therefore maximal nonzero correlation.

## Evidence

The ordinary all-feature test pins bucket populations, pair counts, type
counts, minimum nonzero-Gauss ranks, and the five degree-eleven exceptional
differences.  Every type classification is independently checked by summing
the full exact quadratic truth table.

## Alternatives

- Collapsing each form to its Arf sign was rejected because it cannot expose
  pairwise rank.
- Declaring the five rank-two degree-eleven pairs a single exceptional
  translation family was rejected: their polynomial differences have three
  distinct shapes, including a five-term degree-eight difference.
- Continuing larger raw rank tables was rejected by the stopping rule: rank
  zero already occurs, the full rank range is present, and the sought uniform
  high-rank premise is false.

## Consequences

- The raw simultaneous buckets are not a bounded-class high-rank
  Kerdock/Delsarte--Goethals family.
- A second-trace proof would need a new signed aggregation that cancels the
  low-rank sectors across fibres, valuations, or convolution orders.
- The selected whole-sum architecture remains the connected fourth-cumulant
  or equivalent Witt-Haar refinement estimate.  No endpoint theorem credit is
  granted by this finite stopping test.
