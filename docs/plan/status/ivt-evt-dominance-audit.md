# Lane: ivt-evt-dominance-audit

**Status:** IN PROGRESS (early commit — findings incomplete).

## Assignment

Independently audit the claim that IVT and EVT, as this repository states and
proves them, are Pareto-dominant over Mathlib's on the two axes ADR-0692
names (trusted base, computational content), with breadth conceded.

## Progress

- Read `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
  in full. It already concludes EVT is NOT dominant (row 1 absent as of that
  writing) and IVT is, on the two-axis test.
- Next: verify every number from the kernel, re-measure the 0/20 five-risk
  coverage, and run the vacuity check.

## Landed changes

(none yet)
