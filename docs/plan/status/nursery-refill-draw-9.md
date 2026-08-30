# nursery-refill-draw-9

<!-- plan-section: lane-status -->

**Status: DONE — draw 9 is AUTHORED. The dispatchable frontier clears its
floor (1 -> 21 against floor 10) with ZERO new kernel constructions**, against
ADR-0762's (draw 8, declined) conclusion that two new construction-only
declarations were required first.

Decision record:
[ADR-0830](../../research/09-decisions/adr-0830-nursery-draw-9-two-below-floor-held-out-combinations-not-two-new-constructions.md).

## What changed

`scripts/gen-autogenesis-nursery-refill.py`: four new families in
`FAMILY_MODULES`/`FAMILY_ROUTES`.

| family | partition | modules | rows |
| --- | --- | --- | --- |
| `integer-elementary-identities` | held-out | `Init.Data.Int.Basic`, `Init.Data.Int.Compare`, `Init.Data.Int.Linear`, `Mathlib.Data.Int.DivMod` | 10 of 11 |
| `natural-bitwise-basics` | development | `Init.Data.Nat.Bitwise.Lemmas` | 10 of 33 |
| `natural-distance` | train | `Mathlib.Data.Nat.Dist` | 10 of 18 |
| `natural-elementary-bounds` | held-out | 10 small leftover Nat modules (see ADR-0830) | 10 of 12 |

Regenerated: `artifacts/autogenesis/nursery-v2-extension.json` (300 -> 340
entries). 40 new fact files under `artifacts/facts/F-ml430-*.json`.

## Why this route and not ADR-0762's

ADR-0762 measured the un-owned floor at 7 modules, none held-out-safe, and
concluded draw 9 needed two NEW kernel declarations (`Nat.nthRoot` clean, a
second candidate unidentified — `Squarefree` measured and rejected). That
measurement re-derives identically on this tree (`env=2383`, same seven
modules). What ADR-0762 did not check: several modules BELOW the
`PER_FAMILY` floor, already admissible with **zero new declarations**, combine
into a held-out-safe pool the way draws 3/4/5 already did
(`integer-division-boundary-cases`, `range-induction`,
`integer-absolute-value`). Two such combinations exist and both are R9/R11
clean, verified with the real `select()`/`guard()` in memory before being
written — see ADR-0830 for the full reasoning and the exact probe output.

## Screening performed (every family considered, including rejections)

Detail moved to [`../notes/nursery-refill-draw-9.md`](../notes/nursery-refill-draw-9.md).

