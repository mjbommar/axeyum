# ADR-0612: Control registration is derived, and every exclusion carries a reason

Status: accepted
Date: 2026-08-27
Index-summary: Every `scripts/tests/test_*.py` is discovered and run by `scripts/run-python-controls.py` rather than remembered in a caller, so a new control runs the moment it is committed; the unexplained `PY_ORPHAN_BASELINE=188` floor is replaced by `scripts/control-optout.tsv`, an allowlist where each entry names a file that must exist and carries a written reason, failing in both directions; and a hyphenated `.py` under `scripts/tests/` is forbidden because it is unreachable both by the discovery glob and by `python3 -m unittest`.
Index-status: accepted

## Context

`scripts/check-control-registration.sh` exists because a control nobody invokes
is indistinguishable from a control that does not exist. Its shell half derives
the registry from the filesystem and goes red until some gate names a new
`scripts/tests/*.sh`.

Its Python half did not. It counted the suites no caller named and pinned the
number:

    CONTROL_REGISTRATION|controls=20|orphans=0|py_controls=382|py_orphans=188|py_baseline=188|py=ok

**188 of 382 — 49% — were named by nothing**: not `scripts/check.sh`, not the
`justfile`, not `hooks/pre-push`, not a workflow. The ratchet guarded growth
only, so that floor was permanent and nobody had chosen it; it was whatever the
count happened to be the day the ratchet was written, and it accumulated one
lane at a time.

That is this repository's own audited defect one level out. *A check that cannot
fail and a check that never runs are the same green.* Three orphans appeared on
2026-08-27 alone and all three were checks written that same day to close real
defects — including `test_validate_facts_allowlist`, which was written **because**
two tests could not fail and was then left wired to nothing.

The 188 were triaged rather than counted (measurement in
[`docs/plan/status/154-inert-controls.md`](../../plan/status/154-inert-controls.md)).
Every one was executed. The split was **0 obsolete, 0 needing a slow tier, 188
live** — 160 passing, 16 written in a dialect the gate's invocation form cannot
run, 12 red on `main`. Nothing was obsolete, and nothing was too slow: all 169
that could run take **39 s wall at 8 jobs** and contribute **1,193 tests**.

## Decision

**1. Registration is derived, not remembered.**
`scripts/run-python-controls.py` discovers every `scripts/tests/test_*.py`,
subtracts the suites a caller already names and the exclusions in
`scripts/control-optout.tsv`, and runs the remainder. It is a *catch-all*: a
suite covered by its own named `step` is not re-run, so the set shrinks
automatically as individual steps are added and nothing has to be moved between
lists by hand. A new control runs the moment it is committed.

**2. The numeric floor is replaced by a reasoned allowlist.**
`scripts/control-optout.tsv` is `name<TAB>reason`. It fails in **both**
directions — a missing reason, a missing TAB, a duplicate, or an entry naming a
file that no longer exists are all errors — which is the shape
`scripts/check-shape-duplicates.py` uses for duplicate declarations and
`scripts/check-absence-claims.py` for absence claims. An entry that is *also*
named by a caller is a contradiction and fails: it cannot be both excluded and
run. A ratchet over the list's size makes adding one deliberate and removing one
a recorded result.

**3. A suite that collects zero tests fails the run.**
`python3 -m unittest` collects `TestCase` methods only, so a pytest-dialect file
(bare `def test_x()`) yields `Ran 0 tests`. Ten of the 188 had exactly that
shape. The condition is `tests == 0`, not an exit code: Python ≥ 3.12 exits 5
for "no tests ran" (reads as an ordinary failure, naming nothing) and older
interpreters exit 0 (reads as a pass).

**4. Hyphenated `.py` under `scripts/tests/` is forbidden, not accommodated.**
Confirmed by probe: the `test_*.py` glob does not match `test-foo.py`, **and**
`scripts.tests.test-foo` is not an importable module, so such a file is inert
twice over and cannot be run by any caller in this repository. Making the glob
see it would fix half the problem and leave the invocation form broken. `.sh`
controls keep hyphens — they are invoked by path, and all 21 are registered.

**5. The gate and the runner compute the partition independently and must
agree.** Two implementations of "which suites are covered"; a disagreement means
one is wrong. A single implementation cannot detect the failure this whole file
is about — a covered set that silently shrinks.

## Consequences

- `py_orphans` goes **188 → 0**, and not by absorption: 169 suites now run,
  19 are excluded by name with a written reason, and 194 keep their own steps.
- The aggregate gate gains ~39 s and 1,193 tests.
- Excluding a control is now a diff a reviewer can argue with.
- The 19 exclusions are **liabilities, not settlements**. Six import `pytest`,
  which is installed on no host in this fleet; one is pytest-dialect and red on
  its own terms; eleven are **red on `main` today** — drift detectors that have
  been firing into an empty room, comparing recorded digests against producer
  files that have since moved; one needs an example binary no fast gate builds.
  They are named so they can be fixed, and the ratchet makes each fix visible.
- Both the gate and the runner carry mutation-verified control suites
  (`scripts/tests/test-check-control-registration.sh`,
  `scripts/tests/test_run_python_controls.py`): 12 of 12 guards each, every one
  killed by a named case. The runner's total-tests floor **survived** the first
  round and had a case written for it — a guard nothing kills is decoration.

## Alternatives considered

**Register all 188 by name.** Rejected: it makes the aggregate gate red on 12
suites this lane cannot fix (`artifacts/` and `crates/` are other lanes' scope),
and it leaves the *mechanism* — remembering to register — intact, so the floor
re-accumulates.

**Raise the baseline to 0 by deleting the orphans.** Rejected on measurement:
every one of the 188 has a live subject. Zero were obsolete.

**A slow tier.** Considered and not built. The whole catch-all is 39 s wall; the
13 slowest suites are 250 s of the 334 s *serial* total, but at 8 jobs that
never becomes a reason to split the set, and an unused tier is a mechanism to
maintain for nothing. If the runner ever exceeds the gate's budget, `--list`
plus a per-suite timing is enough to build one then.
