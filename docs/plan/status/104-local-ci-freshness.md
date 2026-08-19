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

**Wiring is ENFORCING in both `scripts/check.sh` and `justfile`'s `check`**
(`e3e105cd6`, 2026-08-19). It was `--report-only` for one day, deliberately,
because the only record that existed was `a6ee37c6a-s4.json` with
`verdict: FAIL` — enforcing then would have red-ed the aggregate gate for every
lane over a 110-minute run nobody had re-triggered, and a gate that is red from
the day it lands is one people learn to ignore. That was the whole blocker and
it is gone: `57af69142-s4.json` is `PASS`, `rc: 0`, 6656 s, `7561 tests run:
7561 passed`, 179 doctests, no `vacuous` and no `unreadable` step.

Nine guards, each mutation-tested by deletion to kill exactly one control. The
near-miss worth keeping: the first fail/vacuous/unreadable fixtures carried a
top-level `verdict: "FAIL"`, so the separate top-verdict guard silently did the
per-step guards' work and deleting one of them killed **zero** controls. Fixed
by making those fixtures top-level `PASS` with a bad step — which both isolates
the guards and is the more dangerous case: a record falsely claiming PASS while
hiding a bad step.

The flip was re-tested through the real call site, not the control suite.

Detail moved to [`../notes/104-local-ci-freshness.md`](../notes/104-local-ci-freshness.md).

Detail: [`../notes/104-local-ci-freshness.md`](../notes/104-local-ci-freshness.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | `e3e105cd6` | The local-ci freshness gate is ENFORCING in both `check.sh` and `justfile`, on a `PASS` record (`57af69142-s4.json`, 6656 s, 7561 tests + 179 doctests, no vacuous/unreadable step). Landed report-only the day before because the only record was FAIL; that was the sole blocker. Flip re-tested through the real call site: NO_RECORD / STALE / STEP VACUOUS all red, unmodified green. |
