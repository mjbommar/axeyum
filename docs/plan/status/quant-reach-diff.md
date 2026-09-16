# Lane: quant-reach-diff — UFLIA's block is REACH, and 60% of the largest countable slice already has a shipped, OFF lever

<!-- plan-section: lane-status -->

**Lane QUANT-REACH-DIFF (`DONE`, quant-reach-diff, 2026-09-16).**
`bench-results/quant-reach-diff-20260916/README.md`.

## What this lane measured

Classified every z3-used instance on ADR-2113's 53 reference-minimal UFLIA
cores (1,025 unique ground bodies) into ADMITTED / MATCHED-REJECTED /
NEVER-MATCHED / NESTED, against our own admitted ground set, rejection
census, and z3's own recovered proof instances (shipped default
configuration, no lever overrides).

| class | count | share |
|---|---:|---:|
| ADMITTED | 11 | 1.1% |
| MATCHED-REJECTED | 169 | 16.5% |
| NEVER-MATCHED | 369 | 36.0% |
| NESTED | 476 | 46.4% |

NESTED's 46.4% independently matches QUANT-INSTANCE-PROBE's own 46% finding
(unresolved outer bound variable in z3's recovered proof). MATCHED-REJECTED's
dominant reason is `rej_nocontext`+`rej_poscap` (102 of 169, 60.4%) — a
context-dependent universal matched and then discarded at
`qinst_egraph.rs:7294`/`:7291` — which is exactly what ADR-2120's
`AXEYUM_QINST_POSITIVE_PATH` (activation-by-assignment) was built to recover,
and which ships OFF. Three worked examples with file:line mechanism
citations are in the README (context-dependent activation, dispatch-order
reach bypass via `q:mbqi-quick`, and a multi-pattern join gap).

## Two real bugs this lane's own classifier shipped and caught

1. Argument-presence checked whole `GROUND` rows, not subterms — a bare
   declared symbol (`this`) essentially never appears as its own row, so
   every param read "missing." Fixed (`flatten_subterms`), regression tests
   added.
2. `UNIVERSAL_RE` was missing `re.M` — the EXACT trap
   `silent-split.py`'s own docstring names. `MATCHED-REJECTED` was 0 on all
   53 cores despite `grep` finding nonzero `rej_nocontext` on 26 of 53 raw
   captures. Fixed, regression test added (`test_a_non_final_line_is_still_parsed`).

Both are documented in `classify.py`'s module docstring and the README's
"Two bugs" section, not silently corrected.

## Host

Briefed for s6 physical pairs `1,9`/`3,11`; this session's worktree exists
only on s4 (verified: no such directory on s6). Ran on s4, pinned physical
pair `6,7`. Recorded in `qrd-run-ours.sh`'s own header.

## Artifacts

`bench-results/quant-reach-diff-20260916/` — `README.md`, `classify.py`,
`qrd-run-ours.sh`, `qrd-classify-all.py`, `qrd-reclassify.py`,
`trigger_derive.py`, `diff/*.tsv` (53 per-core files), `histogram.tsv`,
`histogram-summary.tsv`, `reason-summary.tsv`,
`runs-ours/run-summary.tsv`. Raw solver captures (`runs-ours/dump/`,
`runs-ours/raw/`, ~131 MB) NOT committed, matching ADR-2120 §7e precedent —
`qrd-run-ours.sh` regenerates them. `scripts/tests/test_quant_reach_diff_classify.py`
— 17 unit tests, synthetic fixtures only.

## Next

The block is REACH, named at the mechanism level with file:line in three
worked examples. The one concrete, already-built, currently-OFF lever this
lane's own count supports turning on is `AXEYUM_QINST_POSITIVE_PATH`
(recovers 102 of 169 MATCHED-REJECTED instances directly); ADR-2120 §7e
already found it does not flip verdicts alone on this population (downstream
ground closure), so the next lane's question is whether combining it with a
ground-closure fix (ADR-2120 §7e's own "next lane's question") moves
verdicts where selection- and ladder-only levers (ADR-2113, ADR-2133) did
not.
