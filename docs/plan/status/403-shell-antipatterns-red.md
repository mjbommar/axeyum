# Lane: shell-antipatterns-red — fix the five `grep -q`-in-pipeline sites flagged by check-shell-antipatterns.sh

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, shell-antipatterns-red, 2026-09-01).**
`scripts/check-shell-antipatterns.sh` was red on `main`: `bash
scripts/check-shell-antipatterns.sh` exited 1 with 5 `SHELL_ANTIPATTERN_ERROR`
lines, one per file, all "NEW file using `grep -q` in a pipeline under
pipefail" (the baseline only pins known files/counts; these 5 files were
absent from it entirely). All 5 landed 2026-08-30, after the checker's own
last edit that day (09:55) — the checker existed when each landed, nothing
ran it against them before merge.

Flagged sites (file:line, count, git-log date/sha):

| file | line(s) | count | landed |
| --- | --- | --- | --- |
| `scripts/tests/test-checked-interchange-mutations.sh` | 88, 93 | 2 | 2026-08-30 `46fabf264` |
| `scripts/tests/test-credit-transaction-ledger-mutations.sh` | 78 | 1 | 2026-08-30 `917b3456b` |
| `scripts/tests/test-credit-transaction-mutations.sh` | 78 | 1 | 2026-08-30 `2d5ee83e1` |
| `scripts/tests/test-lean-adapter-mutations.sh` | 92, 97 | 2 | 2026-08-30 `e862dc294` |
| `scripts/tests/test-structural-index-mutations.sh` | 110, 115, 155, 160, 166 | 5 | 2026-08-30 `fb82f8bfc` |

Every site was `echo "$x" | grep -q[xE] PATTERN || { … exit 1 }` under
`set -euo pipefail`; each was rewritten to
`[ "$(echo "$x" | grep -c[xE] PATTERN)" -gt 0 ] || { … exit 1 }`, which
consumes the whole pipe and cannot SIGPIPE the producer — meaning preserved
exactly (count-of-matches-`>`-0 is equivalent to first-match-found for these
single/multi-line greps).

Post-fix, each affected mutation-control script was re-run directly (each is
Python-based and copies the checker under test into its own `mktemp -d`
scratch dir before mutating — never the shared worktree, per its own header
comment; none needed a cargo build):

- `test-checked-interchange-mutations.sh` — exit 0, `MUTATION KILL TABLE
  PASSED -- 7 guards, each kills exactly its own fixture`
- `test-credit-transaction-mutations.sh` — exit 0, `MUTATION TABLE: all 9
  guards each killed exactly their own canary`
- `test-credit-transaction-ledger-mutations.sh` — exit 0, `MUTATION TABLE:
  all 9 guards each killed exactly their own canary`
- `test-lean-adapter-mutations.sh` — exit 0, `MUTATION KILL TABLE PASSED --
  7 guards, each kills exactly its own fixture`
- `test-structural-index-mutations.sh` — exit 0, `all 6 guards killed 1:1`

`scripts/check-shell-antipatterns.sh`: before `exit 1` (5
`SHELL_ANTIPATTERN_ERROR` lines); after `exit 0`,
`SHELL_ANTIPATTERNS|scanned=141|files=7|grep_q_in_pipeline=14|pipeline_status_reads=0`
(the remaining 7 files/14 occurrences are the pre-existing baseline, unchanged
and not risen).

Control suites, both green:
- `python3 -m unittest scripts.tests.test_check_shell_antipatterns_scope` —
  `Ran 9 tests in 0.648s, OK`
- `scripts/tests/test-check-shell-antipatterns.sh` (the detector's own
  positive/negative controls, bonus check) —
  `SHELL_ANTIPATTERN_CONTROLS|cases=12|positive=4|negative=6|PASS`

Did not run: `just check`, `check.sh`, or any cargo-based gate — not touched
by this diff (only 5 shell scripts and this status doc changed) and out of
scope per the brief. Nothing was pushed.

<!-- plan-section: landed-changes -->

| 2026-09-01 | shell-antipatterns-red | fix `grep -q` in pipeline under pipefail in 5 mutation-control scripts, check-shell-antipatterns.sh red -> green |
