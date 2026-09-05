# Replay census — every carrier the kernel builds

<!-- plan-section: lane-status -->

Lane: `lean-replay-census-all`. Item 2 of the Next Ten in
[`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md):
*replay every proved theorem in pinned Lean, or name the reason*. Decision:
[ADR-1661](../../research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md).
Predecessor: [ADR-0760](../../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md)
(lane `l0-s4-independent-replay`), which built the same census over `creal`
alone.

## Status

In progress. The `creal` census (ADR-0760) is generalized to a shared harness
and a second suite runs it over the remaining carriers, one `#[test]` per
carrier so each can be run — or reported as *did not run* — on its own.

## The measurement

Published as
[`artifacts/measurements/lean-replay-census-2026-09-05.md`](../../../artifacts/measurements/lean-replay-census-2026-09-05.md).

<!-- plan-section: landed-changes -->

## Landed changes

| date | change | commit |
|---|---|---|
| 2026-09-05 | Lane opened: status file. | (this commit) |
