# Status: `natural-bit-decode` closed-evaluation amendment + draw-time screen

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, holdout-closed-evaluation-amendment, 2026-08-30).**
ADR-0950 written. In progress: amending `natural-bit-decode` out of held-out
in `mathlib-nursery-split-policy-v1.json` and `nursery-v2-extension.json`,
plus an R12 draw-time screen in `gen-autogenesis-nursery-refill.py`. This
commit is a checkpoint (docs only) landed early per process rules; the
manifest/generator edits and gate re-runs follow.

**Track:** the fact ledger / autogenesis nursery held-out isolation
**Phase:** repairing the second closed-evaluation breach (ADR-0695 was the
first, `fermat-numbers`)
**Date:** 2026-08-30

## Summary

`check-holdout-closed-evaluation.py` reported `natural-bit-decode` held-out
with 2 of 10 rows (`Nat.bit false 0 = 0`, `Nat.size 1 = 1`) already decided by
reduction over `Nat.bit` (2026-08-28) and `Nat.size` (2026-08-24), both landed
days before draw 11 preregistered the family (2026-08-30). Measured over the
whole held-out population (156 rows, both manifests, current snapshot): these
are the ONLY two closed-shaped rows; no other family is affected.

## Delivered (see commits for exact set)

- ADR-0950 — the amendment and the draw-time fix, mirroring ADR-0695's shape.
- Amendment ledger row in `mathlib-nursery-split-policy-v1.json` for
  `natural-bit-decode` (held-out -> development).
- `nursery-v2-extension.json`: the 10 `natural-bit-decode` entries' partition
  flipped to `development`, `family_partitions["natural-bit-decode"]` updated
  to match, `extension_sha256` recomputed. `preregistered_family_partitions`
  left untouched (still `held-out`), per R10's contract.
- R12 in `scripts/gen-autogenesis-nursery-refill.py`: a draw-time screen that
  runs the standing closed-evaluation classifier against every NEW held-out
  row before the manifest is written.
- Tests in `scripts/tests/test_gen_autogenesis_nursery_refill.py`
  (`ClosedEvaluationScreenTests`) replaying the real spent statements against
  the real committed kernel-environment snapshot.

## Measured (fill in after the amendment lands — see commit for final numbers)

| gate | result |
|---|---|
| `check-holdout-closed-evaluation.py` | see commit message |
| `check-autogenesis-nursery.py` | see commit message |
| `check-autogenesis-holdout-isolation.py` | see commit message |
| `check-dispatchable-frontier.py` | see commit message |
| `validate-facts.py` | see commit message |

## Next

- Land the manifest/ledger edits and R12, re-run all five gates, record exact
  output in this file's final revision and in the commit message.
- Mutation-verify the R12 addition and the amendment guard: delete each new
  guard, confirm exactly one test dies, record the kill table.

<!-- plan-section: landed-changes -->

| 2026-08-30 | holdout-closed-evaluation-amendment | ADR-0950 written; amendment and R12 screen in progress |
