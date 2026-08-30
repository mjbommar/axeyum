# IVT and EVT against Mathlib: what the graded families actually contain

**Status: DRAFT IN PROGRESS.** Findings recorded as they are measured. Nothing
here is a reclassification; no fact was edited.

Audit lane `ivt-evt-pareto`, 2026-08-30.

## What is being audited

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` claims
per-statement dominance plus uncontested axes, explicitly *not* global dominance.
ADR-0603 says a classical theorem lands as a graded family:

| row | content |
| --- | --- |
| 1 | general constructive form |
| 2 | boundary / unprovability refutation |
| 3 | decidable-fragment exact form |
| 4 | labeled import |

Row 2 is the axis a classical library has no counterpart for, so the whole
Pareto claim leans on it.

## Working findings

(To be completed.)
