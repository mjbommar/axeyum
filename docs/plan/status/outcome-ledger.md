# Lane: outcome-ledger — one append-only table three sweeps write and later lanes query

<!-- plan-section: lane-status -->

**Lane outcome-ledger (`DONE`, outcome-ledger, 2026-09-15).** Phase 3 of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md),
closed by [ADR-2102](../../research/09-decisions/adr-2102-the-outcome-ledger.md).
Every sweep this week produced `(file → route that decided → elapsed → routes
declined and why)` and threw it away after grepping one token; that table now
exists, three runner shapes append to it, and the questions that cost a lane
each are queries.

Branch base: `git merge-base main HEAD` is `7d922fe58`, which **is** local
`main`'s HEAD at the time this lane merged it.

## What changed

**`scripts/outcome_ledger.py`** — the plan's §4 schema exactly, plus
`decline_names` (schema 2, added when ADR-2104 landed mid-lane), TSV. The routing columns come from `scripts/route_trace_reader.py` (ADR-2101)
and from nothing else; this lane never anchors on a `; route ` prefix. Three
things carry a deliberate third value rather than a boolean:
`partial` is `yes`/`no`/**`unknown`** (a capture with no trail cannot say
whether the reading was a total), `features` is a class list / `none` /
**empty** (the binary predates the instrument), and `sha_status` is
`main`/`branch`/**`unknown-commit`**.

**`scripts/ledger-run-one.sh`** — runs one file under the caller's envelope
WITH `--trace`, keeps the stdout as a file, and appends one row through the
library. It also carries `--no-trace-control`, which re-runs the same file on
the same binary without `--trace` and prints `INVARIANCE ok|MOVED`.

**Three writers under `scripts/ledger-sweeps/`**, one per runner shape that
exists today — the per-lane A/B (ADR-2100's `ab-run.sh`, same-binary refusal
kept), the 16-division board A/B (`ab-two-bins.sh`) and the Tier 1 single-arm
board (`board-run.sh`). Each keeps its original TSV; none formats a ledger row.

**`; features Int|Real`** — the construct scan the ladder already runs now
records itself (`route_ownership::{record_query_constructs,
last_query_constructs}`, one relaxed compare-exchange, first writer wins) and
the CLI prints it as one extra `--trace` line on both the completed and the
watchdog paths. Re-deriving the classification from `.smt2` text in Python
would have been a second authority that drifts from this one.

## Numbers

| | |
|---|---|
| writers appending to one schema | **3** |
| ledger rows produced, seven sweeps | **220** |
| verdict invariance (`--trace` vs not), three smoke runs | **100 / 100 unchanged, 0 MOVED** |
| ADR-2065's `+14`, re-derived from ledger rows | **+14** (arm A decides 0, arm B decides 14) |
| ADR-2045's `74 of 93`, re-derived from the committed census | **74**; **59 of 93** on today's tree |
| ADR-2075's nine partial rows | **7 of 9 partial on this tree**, both exceptions on the wire |
| control suite | **43 tests**, registered as `step outcome-ledger-tests` |
| mutations | 3 registered, **3 killed**, two of them exactly one named test |

## Findings this lane did not go looking for

- **A mutation SURVIVED and the guard was the problem, not the harness.**
  Deleting the `cat-file -e` existence check from the staleness rule left all
  31 tests green: `git merge-base --is-ancestor <garbage> main` exits non-zero
  on its own, so the row was still flagged. The guard was real and
  unfalsifiable at the same time. Fixed by making the classification
  three-valued, which is a distinction a reader can act on.
- **ADR-2101's correction to ADR-2075 is confirmed from a fresh measurement.**
  `UFNIA/sledgehammer/Hoare/z3.850818.smt2` — the file ADR-2075 attributed its
  "Fourteen lines." to, and which ADR-2101 showed took a `ResourceLimit` path
  printing zero `; partial ` lines — comes back **`partial=no`** here, with a
  complete 21-attempt trail.

## Left undone, named

- **`features` is empty on every row from a pre-ADR-2102 binary**, including
  the whole `2611e14b0` arm of the A/B. That is the column's absent value and
  is distinguishable from `none`; it is not backfillable, because the scan is
  inside the binary.
- **`decline_names` is empty on all 220 rows.** `route_trace.rs`'s `to_json`
  emits `detail` and no `name` member, so ADR-2104's typed variant does not
  cross the JSON boundary. That is a three-line addition to the trace lane's
  wire format, not this lane's surface. The column, the schema version and the
  reader path exist and are driven by a fixture, so it fills itself the day the
  producer emits it.
- **Phase 4 is not started.** No ladder order and no budget constant is derived
  here. The ledger's minimum for deriving a default is the repository's minimum
  for claiming a gain: three passes per arm, a published noise floor, and an
  interleaved comparison.
- **The ledger does not replace the A/B and must not be read as one.** A delta
  between two single-arm ledger runs at different loads is the 77/79/85 error
  with a database in front of it. Every aggregate carries `binary_sha`, `host`,
  `load` and `partial` for that reason.
