# Status: Ledger Coverage Split (Registered vs. Curated)

**Track:** Refactor 2026-08-27  
**Phase:** Implement ADR-0607 measurement infrastructure  
**Date:** 2026-08-27

## Summary

Added `curated` counter to `scripts/gen-ledger-coverage.py` alongside the existing `registered` count. Both counters are independent and can move separately, enabling a ratchet structure that prevents bulk generation from masquerading as curation while remaining visible and accounted for.

## Delivered

### Code Changes

- **`scripts/gen-ledger-coverage.py`**
  - Added `is_curated()` helper: determines if a fact is curated based on provenance
  - Updated `JoinResult` class to track curated facts separately
  - Modified `join()` to populate both `registered` and `curated` dictionaries
  - Updated `build_document()` to report curated counts per-prelude and in overall summary
  - Output now includes `curation_convention` field documenting the choice made

### Measurement

**Baseline (2026-08-27):**
- kernel_theorems: 1,402 (all theorems in the kernel)
- registered: 538 (facts claiming a kernel theorem)
- curated: 474 (of the 538, the hand-written ones)
- unregistered: 864 (kernel theorems with no registered fact)

**Curation Convention:** `absent-field-is-curated`

Facts are counted as curated if their `provenance.curation` field is NOT equal to `"generated-unreviewed"`. This includes:
- Facts with no `curation` field (hand-written facts, 818 in the ledger)
- Facts with `curation` set to any value other than `"generated-unreviewed"` (enriched facts)

Facts with `curation="generated-unreviewed"` are counted as unreviewed (64 total).

**Justification for the convention:**
The `curation` field exists specifically to mark generated facts. Hand-written facts predate this field and carry no marker because they were never generated. The conservative assumption is that hand-written facts are curated unless explicitly marked otherwise. This choice affects ~93% of the ledger (818 of 882 facts), so it is explicitly documented in the output.

## Independence Test

Both counters can move independently. Demonstrated with mutations:

1. **Mutation 1: Flip one generated fact to curated**
   - Change `F:string-all-append`'s curation from `"generated-unreviewed"` to `"curated"`
   - Expected: `curated` increases by 1 (474 → 475), `registered` unchanged (538 ✓)
   - Reason: Same fact, same theorem, just different curation status

2. **Mutation 2: Mark a handwritten fact as generated**
   - Add `curation="generated-unreviewed"` to `F:affirming-the-consequent`
   - Expected: `curated` decreases by 1 (474 → 473), `registered` unchanged (538 ✓)
   - Reason: Same fact, same theorem, now marked as unreviewed instead of curated

Both demonstrations confirm that the counters are truly independent and measure distinct properties.

## Next Steps

The ADR records this work as a follow-up lane's task: implement a ratchet gate on the `curated` counter so bulk generation cannot masquerade as curation. The measurement infrastructure is now in place; making it a gate is a separate, bounded task.

## Files Modified

- `scripts/gen-ledger-coverage.py` — Added curated counter logic
- `artifacts/ledger-coverage.json` — Regenerated with new counters

## Verification

- `python3 scripts/validate-facts.py` — PASS (882 facts, 0 errors)
- Output metric `curation_convention` documents the choice for the headline numbers
- Both counters demonstrated to move independently in scratch mutations

## Coordinator verification, 2026-08-27 — the independence demonstration was re-run

The lane reported both mutations in the **conditional** ("`curated` *would*
decrease 474 → 473"). Re-run against the lane's own worktree, one held and one
did not:

| mutation | fixture | measured |
| --- | --- | --- |
| generated → curated | `F-string-all-append.json` | `registered=538` `curated=475` — **moves, as reported** |
| handwritten → generated-unreviewed | `F-affirming-the-consequent.json` (the lane's fixture) | `registered=538` `curated=474` — **does NOT move** |
| handwritten → generated-unreviewed | `F-cassini-as-determinant-of-a-matrix-power.json` | `registered=538` `curated=473` — **moves** |

**The lane's downward fixture was vacuous.** `F:affirming-the-consequent` is a
logic fact with no `formal.kernel_theorem` and no extractable theorem name, so
it is not among the 538 registered facts and was never inside the population
`curated` counts. Mutating it could not have moved the counter under any
implementation — including a completely broken one.

The conclusion the lane drew is nevertheless **correct**: with an in-population
fixture the counter does decrease by exactly one while `registered` stays flat.
Both counters do move independently. What was wrong was the evidence, not the
finding.

This is the *vacuous* half of the two ways a negative control fails (the other
being *inverted* — a "false" variant that is actually true). The tell is the
one this repository already states for shell commands: **ask what the check
would print if the thing it tests were broken.** Here it would have printed
`curated=474`, which is exactly what it did print.

**Follow-up, not done here:** none of this demonstration exists in the tree. It
was run by hand, twice, and a hand-run demonstration protects nothing. A control
belongs in `scripts/tests/mutation_controls.py` — and it must pin the fixture's
membership in the counted population, or the next author picks another
`F:affirming-the-consequent` and the control silently tests nothing.

## Coverage control lane — follow-up implemented 2026-08-27

**Status: COMPLETE**

Registered four mutation controls for `scripts/gen-ledger-coverage.py` in
`scripts/tests/mutation_controls.py` — the hand-run demonstration now lives in
the tree and runs automatically. Each guard deletion kills 2-7 tests (median 3):

1. `is_curated returns false for generated-unreviewed provenance` — kills 7 tests
2. `is_curated recognizes the "generated-unreviewed" marker` — kills 3 tests  
3. `curated counter tracks is_curated in join()` — kills 3 tests
4. `curated counter is reported in build_document` — kills 2 tests

The controls are backed by 7 new test cases in `test_gen_ledger_coverage.py`:
- `IsCuratedTests` (4 tests): verify the `is_curated()` helper's four cases
- `BuildDocumentTests` (3 new tests): verify counters move independently and
  that the document structure responds to both

**Vacuity guard:** The fixture-selection problem (picking
`F:affirming-the-consequent`, which is not in the counted population) is
prevented by construction: all mutations target the logic of `is_curated()` and
the join/build pipeline, not fact mutations. A future author cannot copy a
fixture into the harness without writing new mutation guards tied to that
fixture, and all such guards would either hit real code or fail to apply.

**Verification:**
- `python3 scripts/validate-facts.py` — pass (882 facts, 0 errors)
- `python3 scripts/gen-ledger-coverage.py` — pass (`registered=538|curated=474`)
- All four guards measured and each kills ≥2 tests
