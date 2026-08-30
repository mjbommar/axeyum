# Lane: nursery-draw-four -- draw 4, a new S6 glyph screen, and attestation found 2 more unclosable rows

<!-- plan-section: lane-status -->

**Lane block (`DONE -- draw 4 landed, 40 rows, attested, 2 new held-out
rows found unclosable`, nursery-draw-four, 2026-08-29).**

## Headline

Dispatchable was down to **8** (7 of them the totient family a sibling lane
was actively closing). Draw 4 adds **40 rows across 4 new families** under
ADR-0615's per-cohort envelope, attests the whole 200-row manifest on s5, and
adds a new S6 screen (`check-dispatchable-frontier.py --statable`) that
rejects a candidate whose statement carries an elided-proof/hygiene glyph
before it can ever be preregistered.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 8 | **28** |
| held-out rows / families | 107 / 12 | **127 / 14** |
| quoted cohort | 160 | **200** of 214 ceiling (14 headroom left) |
| already-proved fraction of new dispatchable rows | -- | **10/28 (35.7%)** |
| rows attested on s5 (real Lean, not quotation) | 160/160 (159 elaborate) | **200/200 (197 elaborate)** |
| new NOT-elaborable rows found this draw | -- | **2**, both `integer-absolute-value` |

## Step 0 -- re-measurement

```
python3 scripts/check-dispatchable-frontier.py   (BEFORE)
  open ml430 mirrors: 136
  held-out: 105   mutation controls: 12   structurally blocked: 11
  DISPATCHABLE: 8
      F:ml430-int-add-assoc-749cb0ff
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-{,eq-one-}{b6a6596f,d0491d84}
      F:ml430-nat-totient-{coprime-totient-iff,dvd-of-dvd,even,gcd-mul-totient-mul}-*

python3 scripts/check-autogenesis-holdout-isolation.py   (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=107|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Headroom, re-derived from `gen-autogenesis-nursery-refill.py --check` rather
than the brief's number (which said 56): `entries=160`, `EXTENSION_CEILING =
V1_EVALUATION_ENTRIES = 214`, so headroom was **54 rows**, not 56. A 40-row
draw fits either way.

## The S6 glyph screen (committed first, before the draw itself)

`docs/contributor-guide/lean-surface-attestation.md` and
`305-lean-attestation-s5.md` asked for exactly this: "screen for `⋯`/`✝` at
extraction, before anything enters your manifest. Nothing does that today."

Added to `scripts/check-dispatchable-frontier.py`'s `--statable` screen as
**S6**: reject a candidate whose statement carries `⋯` (U+22EF), `✝`
(U+271D), `…` (U+2026), or the word `sorry`. The one already-recorded row
(`F:ml430-nat-le-induction-2f088ac3`) is exempted by an explicit, narrow
`KNOWN_GLYPHED_FACT_IDS` allowlist keyed on its exact `fact_id` -- not a
general rule -- per ADR-0615 (never rewrite or delete a preregistered row).

Detail moved to [`../notes/309-nursery-draw-four.md`](../notes/309-nursery-draw-four.md).

