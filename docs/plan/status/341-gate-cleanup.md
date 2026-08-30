# Lane 341 — gate cleanup: the 43 `check-fast` failures

<!-- plan-section: lane-status -->

**Status: in progress.** Re-measured all 43 at merged HEAD — all 43 still fail,
so none was a stale-list artifact. Grouped by CAUSE; detail and the per-step
table live in [`docs/plan/notes/341-gate-cleanup.md`](../notes/341-gate-cleanup.md).

Cause groups (counts are of the 43):

| # | cause | n |
| --- | --- | --- |
| A | generated artifact stale — regenerate, and say what moved | 11 |
| B | a TEST pins a count that legitimate work moved | 8 |
| C | nursery population grew; baseline/partition derived from it | 4 |
| D | **genuine defect** — fact-ledger dependency cycle | 3 |
| E | frontier/catalog drift from newly-settled facts | 5 |
| F | host setup — `.venv` absent, `uv run` cannot import `axeyum` | 3 |
| G | **real findings** — the check is right and the tree is wrong | 9 |

The one to read first is **D**: `gen-autogenesis-baseline.py --check` exits **2**
with `dependency cycle reaches F:ml430-nat-log-mono-right-b8939fee`. That is a
real cycle in `depends_on`, introduced by today's log/clog work, and it cascades
into `autogenesis-proposer-isolation` and `autogenesis-apply-search`, which both
shell out to the baseline. Nothing here is fixed by regeneration.

Held-out isolation is intact and stays that way:
`AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1106|settled=0|references=0|verdict=PASS`.

<!-- /plan-section -->
