# Where the gap actually is — 85% of it is arithmetic, not bit-vectors

**Measured 2026-09-08** from the division board in
`docs/plan/smt-parity-plan-2026-09-05.md` (11 divisions carrying per-division
counts). Computed, not eyeballed.

## The distribution

| family | gap | share |
|---|---:|---:|
| arithmetic (QF_LRA, QF_UFLIA, QF_NIA, QF_LIA, QF_IDL, QF_RDL) | 214 | 85.3% |
| bit-vector (QF_BV, QF_ABV) | 24 | 9.6% |
| equality (QF_UF, UF) | 12 | 4.8% |
| strings (QF_SLIA) | 1 | 0.4% |

Board total: we solve 1,455 of 1,706. The frontier-adjusted figure is larger
(~327 across 12 divisions) because measuring against the genuinely strongest
reference per division adds roughly 50 files in 4 divisions; that correction
does not change the SHAPE below, but quote the frontier number, not this one,
for headline claims.

Largest single gaps: **QF_UFLIA 58, QF_LRA 52, QF_NIA 48, QF_LIA 26**.
All four are arithmetic.

## Why this matters, bluntly

The obvious reading of "our search explores 2.5x more of the space" is that we
need better CNF-level simplification -- inprocessing, vivification, variable
elimination. **That work targets QF_BV and QF_ABV, which are 9.6% of the gap.**
QF_BV is already at 96.9% (188 of 194, six files behind). Closing bit-vectors
COMPLETELY would move us 24 files.

The arithmetic divisions are where 214 of the missing files live, and they are
not lost for lack of CNF simplification. They are lost in the theory layer:
simplex quality and its explanation/core extraction, theory propagation and the
SAT/theory interface, integer cuts and branch-and-bound, and (for QF_NIA) an
algorithm class we may not have at all.

## What this changes

1. **The theory-solver and rewriting work outranks the CNF inprocessing work**
   by roughly 9:1 on the current board. Inprocessing is still worth doing --
   it is nearly free once scheduled correctly, and QF_ABV alone is 18 files --
   but it must not be mistaken for the main event.
2. **Preprocessing still matters for arithmetic, at the TERM level, not the
   CNF level.** Word-level rewriting sits above all 12 divisions; CNF-level
   simplification only helps routes that bit-blast.
3. **QF_UFLIA at 58 is the single biggest prize** and it is a COMBINATION
   division -- UF plus integer arithmetic. We are at 122 of 180 with 0 files
   we win that the reference loses. That pattern (no unique wins) suggests a
   systematic capability gap rather than a tuning difference.

## The caution that applies to this document

This is a board-derived allocation, not a diagnosis of any individual failure.
Route attribution already established that on files we lose, the pass that
consumed the budget is not the last one that ran on 348 of 350 files. **So
"arithmetic divisions are behind" says where to look, NOT what is wrong.**
Do not let this table become the explanation; it is only the search light.
