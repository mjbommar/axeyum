# Lane: nursery-ceiling-adr -- who set 300, what it was protecting, and what replaced it

<!-- plan-section: lane-status -->

**Lane block (`DONE -- ADR-0615 accepted, generator fixed, draw 2 landed`,
nursery-ceiling-adr, 2026-08-29).**

## Headline

The ceiling was **not** the blocker, and raising it would have been the wrong
move. The generator had three independent obstacles to a second draw; **two of
them destroy data**, and the ceiling -- the only one anybody had noticed -- was
accidentally shielding the ledger from the other two.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 11 | **31** |
| held-out rows / families / split keys | 67 / 5 / 16 | **87 / 7 / 21** |
| quoted cohort | 80 | **120** of a 214 ceiling |
| existing fact files modified by the draw | -- | **0** |

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 99
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 11
exit 0

python3 scripts/check-autogenesis-holdout-isolation.py     (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Every number in the brief reproduced. Populations: `nursery-v1.json` 216 entries
(214 evaluation + 2 longitudinal), `nursery-v2-extension.json` 80, combined 294
against `EVALUATION_CEILING = 300`.

Two brief numbers refined by measurement rather than contradicted:

- **"39 of 50 closed in a few hours"** is exact. 21 development + 18 train of
  the 50 dispatchable v2 rows are `proved`; the refill landed 17:22 and the
  closures run 18:03 -> 19:19.
- The whole-day figure is larger and is the one that should drive sizing:
  **60 `ml430` mirrors flipped to `proved` today** (135 -> 195), the other 21
  coming from the pre-existing v1 backlog.

## The ceiling's origin -- traced, not assumed

`EVALUATION_CEILING = 300` was introduced **this morning** (`94b3e61`,
`feat(autogenesis): the statable-here screen, and an 80-row refill`), and its
comment cites its source honestly rather than inventing a number:

```python
# R3 -- the ceiling. v1's policy caps the evaluation population at 300.
```

That is a faithful transcription of `nursery-v1.json` ->
`policy.evaluation_fact_count` = `{minimum: 100, maximum: 300}`, itself pinned
as a literal in `scripts/check-autogenesis-nursery.py:82` as *"the 100..300
programme range"*. The range enters on **2026-08-18** (`2d65f19d8`,
`c9717b3bc`), with authority **ADR-0478** and roadmap task **AG2.3** -- both of
which state it as a sizing target for a population that was then **empty**.

Detail moved to [`../notes/294-nursery-ceiling-adr.md`](../notes/294-nursery-ceiling-adr.md).

