# Lane: nursery-draw-three -- draw 3, and R9 caught what adjacency judgement alone could not

<!-- plan-section: lane-status -->

**Lane block (`DONE -- draw 3 landed, 40 rows, 2 new held-out families`,
nursery-draw-three, 2026-08-29).**

## Headline

Dispatchable was down to **8** (7 of them one family, mostly blocked on
infrastructure). Draw 3 adds **40 rows across 4 new families** under
ADR-0615's per-cohort envelope. Two of the four are the SAME candidates a
first attempt tried and R9 rejected -- the corrected set below is R9-clean.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 8 | **28** |
| held-out rows / families / split keys | 87 / 7 / -- | **107 / 9 / --** |
| quoted cohort | 120 | **160** of a 214 ceiling |
| already-proved fraction of dispatchable | -- | **6/28 (21.4%)** |
| existing fact files modified by the draw | -- | **0** |

## Step 0 -- re-measurement (main merged first: five commits landed in the
hours before this lane started -- coprimality, mul-order, mod-mul families
all closed)

```
python3 scripts/check-dispatchable-frontier.py
  open ml430 mirrors: 99
  held-out: 65   mutation controls: 12   structurally blocked: 11
  DISPATCHABLE: 8
      F:ml430-nat-coprime-coprime-div-left-6f7082bd
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-{,eq-one-}{b6a6596f,d0491d84}
      F:ml430-nat-totient-{coprime-totient-iff,dvd-of-dvd,even,gcd-mul-totient-mul}-*

python3 scripts/check-autogenesis-holdout-isolation.py     (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=87|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Headroom, re-derived from the generator's own constants, not from the brief's
arithmetic: `V1_EVALUATION_ENTRIES = 214` (asserted, matches `nursery-v1.json`'s
214 evaluation entries + 2 longitudinal = 216 total). `nursery-v2-extension.json`
carried **120** entries before this draw, so headroom was **94 rows**, not the
96 the brief quoted (216 − 120, using the 216 total-file figure rather than the
214-evaluation figure the ceiling actually governs). A 40-row draw fits either
way with room to spare.

## Family selection -- two rounds, because the first round was wrong

Detail moved to [`../notes/300-nursery-draw-three.md`](../notes/300-nursery-draw-three.md).

