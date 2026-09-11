# We benchmark 14 of the corpus's 84 divisions, and the one we added today had the worst bug

**Date:** 2026-09-11

## The count

`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental` holds
**84 logic divisions, 438,631 benchmark files**. `bench-results/PARITY.md`, over
its whole history, has a row for **14** of them — the 12 standing board
divisions plus `QF_UFLRA` and `QF_FP`, both added 2026-09-11.

| | count | share |
|---|---|---|
| divisions in the corpus | 84 | |
| divisions ever benchmarked | **14** | **17%** |
| files in the corpus | 438,631 | |
| files in benchmarked divisions | 258,616 | 59% |

By file count the picture is less stark than by division count, because the
board covers several large logics. But **70 logics have never been run once.**

## Why this is not an accounting curiosity

On 2026-09-11 exactly one new division was added to the board. `QF_UFLRA`
scored **76/200 against cvc5's 198/200** — the worst gap ever recorded here —
and the cause was a fifteen-line missing coercion in `distinct` that had been
wrong the entire time (`82152dbea`). After the fix the `RandomDecoupled` family
alone goes from **1 of 69 decided to 67 of 69**.

Nothing about that bug was hard. It was invisible because nobody had run the
division.

For scale, against the same day's solver work measured on divisions we DO run:

| source | files gained |
|---|---|
| the `distinct` coercion, one new division | **+66** |
| 320 commits (09-09 to 09-10), QF_UFLIA | +34 |
| three targeted solver fixes, all divisions | +10 |

## The largest unmeasured divisions

| division | files | note |
|---|---|---|
| AUFLIRA | 20,011 | |
| **QF_S** | **18,940** | see below |
| QF_ABVFP | 18,129 | |
| QF_BVFP | 17,249 | |
| UFNIA | 13,464 | |
| AUFDTLIRA | 11,043 | |
| UFLIA | 10,128 | |
| QF_DT | 8,700 | datatypes |
| BV | 6,185 | quantified BV |
| ABV | 4,975 | |

## `QF_S` is the next QF_UFLRA, and the evidence is already in the roadmap

Roadmap item 2.5 records that of **66 vendored** string files, **37 the parser
cannot read** (56%). Item 3.6 then measured why: they are *"declined at INGEST
by the ADR-0029 admission test (`attempts=1 last=fd:parse`)"* — and concluded
**DO NOT BUILD** for strings *inference*, correctly, because the parser is what
costs the verdicts.

`attempts=1 last=fd:parse` is the EXACT signature of the QF_UFLRA `distinct`
bug. Both findings say the same thing: files refused at the front door, never
reaching a solver.

The difference is population. 3.6 measured 66 vendored files. **`QF_S` has
18,940 files in the corpus and has never been benchmarked.**

## What this says about where to spend effort

Phase 3 of the 2026-09 roadmap contains **fourteen DO-NOT-BUILD verdicts and,
as of today, zero BUILD items** — every one of them reached by deepening a
division already on the board. The single largest gain of 2026-09-11 came from
*widening* to a division that had never been measured.

That is one data point and should not be over-read. But the asymmetry is large,
the cost of a new division is one pinned list plus one run, and the failure mode
it exposes (front-door refusal) is invisible from every division already on the
board because those files parse.

**Next measurement, not next build:** pin a 200-file `QF_S` list and run it.
If the `attempts=1 last=fd:parse` rate resembles the vendored 56%, the finding
is a parser gap of the same shape and size as the one fixed today.
