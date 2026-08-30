# Notes: 321-queue-refill

Detail moved out of [`../status/321-queue-refill.md`](../status/321-queue-refill.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| | |
| --- | --- |
| `scripts/check-dispatchable-frontier.py` | G7 fails below `FLOOR = 10`; `--floor` is a one-way ratchet (exit 2 if asked to lower); `--json` now carries the queue verdict |
| `scripts/tests/test-dispatchable-frontier.sh` | 28 → 35 cases |
| `scripts/propose-nursery-refill.py` | new — the mechanical half of authoring a draw, with R3 failing when the pool cannot refill the queue |
| `artifacts/autogenesis/refill-headroom-v1.json` | new — the tracked measurement, freshness re-derived from every screen input |
| `scripts/tests/test-propose-nursery-refill.sh` | new — 18 cases |
| `justfile`, `scripts/check.sh` | both new steps registered |
| ADR-0617 | the queue refills from the kernel, not from the bridge |

## Two defects found while building this

- **`--json`'s `guard_failures` never contained the queue verdict.** G4 was
  appended to `fails` AFTER `json.dumps`, so an EMPTY dispatchable set emitted
  `guard_failures: []` beside exit 1. The one consumer shape that mode exists
  for was the one shape it lied to. Fixed by deciding the verdict before any
  output. It was untested until a mutation said so — blanking the field
  SURVIVED the first draft of the new suite.
- **`healthy-real-tree-passes` was a control over the SIZE OF THE QUEUE.** It
  demanded exit 0 from the real tree, so it failed the day the queue drained,
  for a reason unrelated to false positives. It now asserts over the ARTIFACT
  guards (G1/G2/G3/G5/S1–S4) plus a positive control that a report was produced
  at all.

## Verification

- Frontier controls: **all 35 pass.** Mutation-verified — `<` → `<=` kills only
  `G7-exactly-at-the-floor-passes`; deleting the ratchet kills only
  `G7-floor-may-not-be-lowered`; blanking the JSON field kills only
  `G7-json-reports-a-starved-queue`.
- Proposer controls: **all 18 pass.** Ten mutants, no survivors, seven of them
  killing exactly one case each. Includes a case that moves `FLOOR` in the
  frontier checker and requires this gate's output to follow — a copied constant
  prints the same number either way.
- Registration verified against the runner, not by grepping for a mention:
  `AXEYUM_CHECK_LIST=1 bash scripts/check.sh` enumerates 389 steps and both new
  ones appear, against a positive control (3 `dispatchable-frontier` steps) and
  a negative one (0 for a name that does not exist).
  `check-control-registration.sh`: 28 controls, 0 orphans.
- `check-autogenesis-holdout-isolation.py`: `references=0` unchanged,
  `files_scanned` 1105 → 1106. The new artifact names modules and counts, never
  a fact id. **That gate is RED for a pre-existing reason another lane owns**
  (`settled=10`); this lane did not touch it.

## What happens the next time the queue empties

`just check` / `check.sh` fails at G7 while the queue still has ~10 rows of
work, naming `propose-nursery-refill.py` in the failure text. That prints the
ready families with their candidate counts;
`propose-nursery-refill.py --names <module>` prints the individual propositions.
Authoring the draw is then two dict entries and a re-run of the generator.

If the pool itself runs out, R3 fails with a different message that says the
terminal condition has been reached and explicitly says not to spend held-out
rows to make it pass.

## Next

- **Author a draw.** Two families clears the floor; nineteen are ready. Highest
  yield: `Init.Data.Int.Gcd` (117), `Mathlib.Data.Nat.ModEq` (87),
  `Init.Data.Nat.Gcd` (82), `Mathlib.Data.Int.ModEq` (80). This lane did not do
  it: another lane holds the nursery manifest for the ADR-0542 amendment, and a
  draw rewrites all 200 entries.
- **Decide `instSubNat`** (ADR-0617). 292 rows sit behind one elaboration
  constant that S2 can never admit.
- **Declare an Int division constant** for pool growth — `Int.lcm` alone is 79
  rows.
