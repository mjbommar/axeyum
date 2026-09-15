# The outcome ledger

**ADR-2102**, Phase 3 of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../../docs/plan/dispatch-and-instrumentation-2026-09-15.md).

One append-only TSV per sweep, plus `INDEX.tsv`. Written by
`scripts/ledger-run-one.sh` through `scripts/outcome_ledger.py`, which is the
only writer and the only reader. **Do not parse these files with `cut` and
`awk` for anything you intend to publish** — a `decline_details` field carries
escaped tabs, newlines and `|`, and the library's `_unescape` is what puts them
back.

```sh
python3 scripts/outcome_ledger.py show --sweep-id <id>            # rows, stale flagged
python3 scripts/outcome_ledger.py agg  --sweep-id <id>            # verdict / bound_by
python3 scripts/outcome_ledger.py show --sweep-id <id> --allow-branch
```

## Three things to read before quoting a number from here

1. **A ledger row is not a board row.** The ledger RECORDS; the interleaved A/B
   is how a claim is made. The same binary scored 77, 79 and 85 on one division
   in one day purely on ambient load, so a delta between two single-arm sweeps
   at different loads is that error with a database in front of it. Every row
   carries `host`, `core` and `load` for exactly this reason.
2. **`load()` refuses a sweep measured on a branch binary** unless you pass
   `--allow-branch`. A row whose `binary_sha` this repository has never seen is
   reported as `unknown-commit`, which is a different finding from `branch`.
3. **`verdict_counts` refuses a population containing a `partial=yes` or
   `partial=unknown` row** unless told. `partial=unknown` means the capture had
   no trail at all — that is NOT a synonym for `no`.

## The sweeps in this directory

All seven were produced by lane OUTCOME-LEDGER on 2026-09-15, on s5/s6, one
pinned physical core pair each, 24 s wall / 8 GiB `ulimit -v`, `--trace` on.
Arms: `2611e14b0` (a `main` ancestor) and `cb460e737` (this lane's branch, so
every row from it is correctly flagged stale).

| sweep | writer | population |
|---|---|---|
| `ab-movers-20260915` | `lane-ab-run-ledger.sh` | ADR-2065's 14 `AUFLIRA` movers + 6, both arms |
| `board-qflra-20260915` | `board-ab-run-ledger.sh` | 20 `QF_LRA`, both arms |
| `t1-uflia-20260915` | `t1-board-run-ledger.sh` | 20 Tier 1 `UFLIA` |
| `qflra93-20260915` | `t1-board-run-ledger.sh` | ADR-2045's 93 undecided `QF_LRA` rows |
| `partial9-20260915` (+ `-p2`, `-p3`) | `t1-board-run-ledger.sh` | ADR-2075's nine, three passes |

The raw `--trace` captures are **not committed** — they are large and
mechanically regenerable from each row's `corpus_path` + `binary_sha` through
`scripts/ledger-run-one.sh`. They were produced under
`/nas3/data/axeyum/harness/outcome-ledger/out/<sweep>/` and are not expected to
outlive that scratch area.

The re-derivations that cross-check these rows against the ADRs that first
measured them are in
[../ledger-20260915/rederive.py](../ledger-20260915/rederive.py); its exit
status is the finding.
