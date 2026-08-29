# Lane: nursery-ceiling-adr -- who set 300, what it was protecting, and what replaces it

<!-- plan-section: lane-status -->

**Lane block (`IN PROGRESS`, nursery-ceiling-adr, 2026-08-29).**

## Step 0 -- re-measurement (main merged)

```
python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 99
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 11
exit 0

python3 scripts/check-autogenesis-holdout-isolation.py   (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Populations: `nursery-v1.json` 216 entries (214 evaluation + 2 longitudinal),
`nursery-v2-extension.json` 80. Combined evaluation population 294 against
`EVALUATION_CEILING = 300`.

## The ceiling's origin -- traced, not assumed

`EVALUATION_CEILING = 300` in `scripts/gen-autogenesis-nursery-refill.py:182`
was introduced **today** (`94b3e61`, `feat(autogenesis): the statable-here
screen, and an 80-row refill`) by the `nursery-refill-exec` lane, and its own
comment says where it came from rather than inventing it:

```python
# R3 -- the ceiling. v1's policy caps the evaluation population at 300.
```

That is accurate. The number is a faithful transcription of
`artifacts/autogenesis/nursery-v1.json` -> `policy.evaluation_fact_count`:

```json
"evaluation_fact_count": { "minimum": 100, "maximum": 300 }
```

which is itself pinned as a literal in `scripts/check-autogenesis-nursery.py:82`:

```python
if not isinstance(count, dict) or count.get("minimum") != 100 or count.get("maximum") != 300:
    raise NurseryError("evaluation_fact_count must retain the 100..300 programme range")
```

The `100..300` range predates the nursery's contents. It enters the repository
on **2026-08-18** in `2d65f19d8` (`freeze leakage-safe nursery contract`) and
`c9717b3bc` (`freeze Mathlib evaluation nursery`), and its authority is
**ADR-0478** plus the AG2.3 task line in `docs/autogenesis/02-phased-roadmap.md`:

- ADR-0478: *"it must report not ready until it contains 100--300 evaluation
  facts, all three evaluation partitions, real declared dependency depth,
  multiple provenance and route-hypothesis families, mutations, and at least
  one held-out component."*
- AG2.3: *"define 100-300 provenance-classified Nat/Int facts with real
  dependency depth, route diversity, mutations, and held-out components for
  sustained evaluation."*

**So 300 is the upper end of a design-time SIZING envelope, written when the
population was zero and the open question was how big an evaluation set had to
be before it meant anything.** In every place the range is consumed it is the
**floor** that is load-bearing:
`docs/autogenesis/11-nursery-foundation-result.md` lists *"the 100--300
population floor"* first among nine `ready=false` blockers, and
`--require-ready` was designed to fail until the population was large enough.
The maximum has never rejected anything in this repository until the second
refill hit it on 2026-08-29.

Full reasoning, and the decision, in the ADR (next commit).
