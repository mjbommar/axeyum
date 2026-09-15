# Dispatch plan sizing — 2026-09-15

Two measured inventories for `docs/plan/dispatch-and-instrumentation-2026-09-15.md`
(Phase 1 and Phase 2), produced by lane PLAN-SIZING on `bb58b0bc2`. Feeds
ROUTE-OWNERSHIP (Phase 1, `phase1-ceiling.tsv`) and TRACE-API (Phase 2,
`consumers.tsv`). No Rust written, no ADR filed, no cargo run by this lane.

Status: IN PROGRESS — this is the skeleton, committed early per the brief.
Both TSVs are being filled in; this file will carry the final counts before
the final commit.

## Deliverable 1 — `consumers.tsv`

Every Python/shell file under `bench-results/` and `scripts/` matching
`grep -rlE 'route[= ]|decided_by|bound_by|route-trail' --include='*.py'
--include='*.sh' bench-results scripts`, classified BY READING each file
(not by a second grep), against the rubric in the lane brief: `reads`
(prose-route / route-trail / both / other), `handles_partial` (yes/no/n.a.),
`splits_on_semicolon` (yes/no, the ADR-2020 bug), `last_commit`, `note`.

Candidate count from the seed grep: **254** files (the brief's own estimate
was "~175"; the wider `--include` glob against the current tree finds more).

Counts per `reads` class: TBD (filling in below).

Positive controls: TBD.

## Deliverable 2 — `phase1-ceiling.tsv`

Tier 1 divisions (AUFLIRA, UFNIA, UFLIA, AUFDTLIRA, QF_NIA, UF, UFDTLIRA),
undecided rows from `bench-results/tier1-current-20260914/` (the README
there names the current file per division; AUFLIRA's is
`AUFLIRA-postmerge-787bbefee.tsv`, the other six are the base `78ca906c2`
sweep). Undecided = `verdict` not in `{sat, unsat}` (645 rows total,
confirmed against the tier1-current README's own decided counts).

**Per-file route-trail outputs do not exist for this sweep as run.** Full
account below (this is itself a finding, not a search failure — see
"Where the per-file outputs live" below).

TBD: ceiling counts per division, `attempts == 1` counts, ADR-2045
cross-check.
