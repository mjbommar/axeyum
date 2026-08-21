# local-ci-run-2 — getting a PASSING record, and enforcing on it

Continues [`102-local-ci-run`](102-local-ci-run.md) (first completed run, FAIL)
and [`104-local-ci-freshness`](104-local-ci-freshness.md) (the checker, wired
report-only). This lane produced the record those two were blocked on and
removed the `--report-only` flag from both call sites.

## The record

`artifacts/local-ci-runs/57af69142-s4.json`, host `s4`, finished
2026-08-19T01:02:02Z, `verdict: PASS`, `rc: 0`.

| step | status | tests | seconds |
| --- | --- | --- | --- |
| `cargo fmt --all --check` | pass | -1 | 4 |
| `rustup run stable cargo clippy --workspace --all-targets --all-features -- -D warnings` | pass | -1 | 29 |
| `rustup run 1.88.0 cargo check --workspace` | pass | -1 | 15 |
| `cargo nextest run --profile local --workspace --all-features --no-fail-fast` | pass | **7561** | 6588 |
| `cargo test --workspace --all-features --doc` | pass | **179** | 20 |

`-1` on the first three is correct — they print no test count and are not held
to the count rules. Total 6656 s = 110.9 min, against the 107 min the previous
lane predicted.

Verified from the log independently of the record and of the exit status:
`grep -cE '^ *FAIL \[' → 0`; the nextest summary line reads
`7561 tests run: 7561 passed (87 slow), 32 skipped`; the 23 doctest binaries
sum to 179; zero `VACUOUS`/`UNREADABLE` lines.

## Two things the previous record got wrong that this one gets right

* **`tests: -1` on the sweep.** `a6ee37c6a-s4.json` recorded `-1` for a step
  that ran 7511 tests, because `count_tests`' nextest pattern was `^`-anchored
  and nextest indents its `Summary` by five spaces. `-1` is the "no count"
  sentinel, so the zero-test rule could not fire on the only step it exists
  for. Fixed before this run; this record reads `7561`, which is the
  measurement that confirms it.
* **The suite grew.** 7511 → 7561 tests between the two records, so a
  record's count is not a constant to compare against — only its
  non-zero-ness and its own step verdicts are.

## Running it (for whoever refreshes the record next)

    setsid bash -c 'cd <repo> && scripts/local-ci.sh --record > OUT 2>&1; echo $? > RC' </dev/null &

`setsid` is required. A foreground Bash call caps at 10 min, and an ordinary
background job was killed at exactly 59 m 59.9 s on the previous attempt with
6498/7511 tests done and **no record at all** — the recorder writes only after
the last step. Then wait on the pid (`tail --pid=<pid> -f /dev/null`) rather
than polling, and read the record file, never the exit code.

It gates a **detached worktree at the commit** (`/data0/axeyum/local-ci/worktree`),
so the 32 uncommitted paths in the shared checkout were correctly ignored and
the record attributes the verdict to `57af69142` alone.

It does **not** take `scripts/cargo-serialized.sh`'s flock, so it competes with
the other lanes rather than queuing behind them. It has its own lock at
`/data0/axeyum/local-ci/.lock` (exit 75 = queued, not a failure). Observed
contention was mild this run: load average 2.7 at start, and the wall came in
within 4% of prediction.

## Flipping to enforcing, and proving the flip means something

`--report-only` deleted from `scripts/check.sh` (step `local-ci-freshness`) and
the `justfile` recipe of the same name; the checker's own header, which
documented itself as report-only and described the flip as "deliberately left
undone", was updated to say ENFORCING and to tell the next lane how to refresh
a stale record instead of softening the gate.

A flag deletion is exactly the kind of change that can produce a gate that
cannot fail, so the exit status was tested through the real call site (`just
local-ci-freshness`), not only through the control suite:

| perturbation | result |
| --- | --- |
| `AXEYUM_LOCAL_CI_RECORDS` → empty dir | rc=1, `NO_RECORD` |
| this record, `finished_utc` backdated 5 days | rc=1, `STALE: … 120h old, exceeds the 48h budget` |
| this record, nextest step rewritten `verdict: vacuous`, `tests: 0` | rc=1, `STEP VACUOUS: cargo nextest …` |
| unmodified | rc=0, `PASS` |

`scripts/tests/test-check-local-ci-freshness.sh`: 9/9 controls green before and
after.

One nuisance found while doing this: `AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS=0`
does **not** red a record finished minutes ago, because the staleness guard is
`AGE_HOURS -gt MAX_AGE_HOURS` on integer hours and a fresh record is `0`. That
is correct behaviour, not a bug, but it makes `MAX_AGE_HOURS=0` useless as a
negative control — backdate `finished_utc` instead.

## What this now costs everybody

The gate is enforcing with a 48h budget over a ~110 min lock-serialized sweep.
That is roughly one lane per day burning a run and committing the record, and
there is no automation for it (no cron, no systemd timer, no CI trigger — the
previous lane checked four ways). If that turns out to be too heavy in
practice, the honest lever is the budget or an automatic trigger, **not**
re-adding `--report-only`: a checker that cannot fail is worse than no checker.
