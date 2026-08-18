# Lane: local-ci-freshness — a green record proving nothing still reds

<!-- plan-section: lane-status -->

**`scripts/check-local-ci-freshness.sh` exists and is wired in REPORT-ONLY
mode** (`WIP`, local-ci-freshness, 2026-08-18). Continues 102-local-ci-run's
proposed-not-landed piece: a record for `scripts/local-ci.sh --record` proves
nothing by itself — it can be green for a sha nobody has built on in days, a
rebased-away branch, or a step array that disagrees with its own top-level
`verdict`. This checker re-derives pass/fail from the record's own `steps[]`
(never trusts the summary field) and requires the sha be HEAD-or-an-ancestor
and no older than 48h (chosen over a commit-count budget: velocity measured
7–10 commits/h in bursts across lanes, so a fixed commit ceiling is either too
strict in a burst or too loose on a quiet weekend; the run's own cost —
~107 min, one lock across the whole fleet — sets the 48h floor).

**Wiring is `--report-only` in both `scripts/check.sh` and `justfile`'s
`check`, deliberately not enforcing yet**: the only record that exists
(`a6ee37c6a-s4.json`) is `verdict: FAIL` (4 nextest failures, per
102-local-ci-run), so enforcing today reds the aggregate gate for every lane
over an unrelated 107-minute run nobody has re-triggered — "a gate that is red
from the day it lands is a gate people learn to ignore." Report mode runs the
identical guards every check and prints the verdict; the moment a fresh
all-pass record lands, delete `--report-only` from both call sites (one line
each) to make it enforcing. Confirmed on the real repo: it currently reports
FAIL, naming the nextest step, exactly matching 102's record.

9 guards (no-record / non-ancestor-in-loop / no-applicable-record / stale /
fail-step / vacuous-step / unreadable-step / top-verdict-mismatch /
report-only-override), each mutation-tested by hand-deleting it and
confirming exactly one control in
`scripts/tests/test-check-local-ci-freshness.sh` dies — no shared-check
pattern. First draft of the fail/vacuous/unreadable fixtures used a
top-level-FAIL record, which let the top-verdict guard mask a deleted
per-step guard (0 controls died); fixed by using top-level PASS + a bad step,
which is also the actually dangerous direction (a record lying that it
passed).

Left undone: flipping to enforcing (blocked on a fresh PASS record, not on
this checker); no automated mutation-testing harness (done by hand this
session, documented in notes).

Detail: [`../notes/104-local-ci-freshness.md`](../notes/104-local-ci-freshness.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `scripts/check-local-ci-freshness.sh` + `scripts/tests/test-check-local-ci-freshness.sh`: the local-ci record freshness gate, wired `--report-only` into `check.sh` and `justfile`. |
