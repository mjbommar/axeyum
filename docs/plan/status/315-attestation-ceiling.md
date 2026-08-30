# Lane: attestation-ceiling -- the ceiling counted membership, so re-attestation bought nothing

<!-- plan-section: lane-status -->

**Lane block (`DONE -- ADR-0616 accepted, R3 counts by attestation, manifest no
longer contradicts itself`, attestation-ceiling, 2026-08-30).**

## Headline

The promotion is right, and the reason is narrower than "the two cohorts are the
same". **On the STATEMENT an attested extension row is v1's grade and slightly
better-evidenced. On the ROW it is not, and that difference is not repaired by
attestation and is not promoted here.** ADR-0615's exit works once R3 stops
counting manifest membership.

| | before | after |
| --- | --- | --- |
| R3 compares | `len(entries)` vs 214 | unattested vs attested |
| attested cohort | not counted at all | **411** (v1 214 + 197 accepted) |
| unattested cohort | not counted at all | **3** (the rows Lean refused) |
| headroom in rows | **14** | **408** |
| manifest limitations | asserted quotation grade beside a 197-row `attested` list | derived from the run |
| DISPATCHABLE | 8 | 8 (unchanged -- no draw here) |

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/gen-autogenesis-nursery-refill.py --check
AUTOGENESIS_NURSERY_REFILL_OK|entries=200|settled_mirrors_admitted=162|bridge=70
  |env=2207|development=60|held-out=90|train=50|combined=414          exit 0

python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 146 | held-out 115 | mutation controls 12
  | structurally blocked 11 | DISPATCHABLE 8                          exit 0
```

Every number in the brief reproduced: 200 entries, `grade =
real-lean-axiom-elaboration-per-row`, `attested` 197, `not_elaborable` 3,
`unattested` 0, 14 rows of headroom against a 40-row minimum draw, queue at 8.

## What the ceiling protects

ADR-0615's rule, quoted from the ADR: *"the unattested cohort may never outweigh
the attested one, which is ADR-0601's 'imports are labeled scaffolding, never
headline' applied to the same distinction."*

So it is a **statement-provenance** rule. It protects the population we measure
ourselves against from being predominantly strings nobody has confirmed are
Mathlib propositions -- the failure the `Nat.le_induction` row is: a
pretty-printed type carrying an elided-proof glyph, preregistered as a
proposition, and not one.

It is **not** a split-integrity rule. Blindness is governed by R1, R8, R9 and
`check-autogenesis-holdout-isolation.py`, per row and per family. Conflating the
two is what made this decision look harder than it is.

## Is an attested extension row the same grade as a v1 row?

Detail moved to [`../notes/315-attestation-ceiling.md`](../notes/315-attestation-ceiling.md).

