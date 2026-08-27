# 188 control files are run by no gate, and the ratchet accepts it as a floor

Status: **open deficiency**, logged 2026-08-27. Not yet dispatched.

## The measurement

`scripts/check-control-registration.sh` on `main`:

    CONTROL_REGISTRATION|controls=19|orphans=0|py_controls=381|py_orphans=188|py_baseline=188|py=ok

**188 of 381 Python control files — 49% — are named by no gate**: not
`scripts/check.sh`, not the `justfile`, not `hooks/pre-push`, not a workflow.
Spot-checked five at random: three genuinely unnamed, two registered, which
matches the ratio.

They are not broken. They pass when run by hand. They simply never run.

## Why this is a deficiency and not a backlog

The ratchet guards **growth only**. `py_baseline=188` means the gate goes red
when a *new* orphan appears and stays green over the existing 188. Nobody chose
that floor; it accumulated one lane at a time, and the ratchet was set to
whatever the count happened to be when it was written.

That makes it the exact shape of the defect this repository already audits for,
one level out: **a check that cannot fail** and **a check that never runs** are
the same green. A suite of 188 controls that no gate invokes provides the
*appearance* of coverage — they are present, they are committed, they are
listed in status docs — while contributing nothing to any gate's verdict.

## Evidence that the floor is actively harmful, not merely untidy

Three orphans appeared on 2026-08-27 alone, and all three were checks written
**that same day to close real defects**:

| control | what it guards |
| --- | --- |
| `test_validate_facts_allowlist` | the replacement for two tests that could not fail |
| `test_check_shape_duplicates` | the bidirectional duplicate ratchet |
| `test_theorem_inventory_completeness` | the three-way `build_groups` comparison |

Each passes. None would ever have run in aggregate. The first is the sharpest:
it was written **because** two tests could not fail, and was then left wired to
nothing — the same defect one layer out, committed by the person fixing it.

The ratchet caught these three because they were *new*. It is structurally
incapable of noticing the 188 that were already there.

## A second, independent blind spot in the same gate

The sweep lane confirmed by probe — dropping an untracked
`test-scratch-hyphen-probe.py` into the directory and watching `py_controls`
fail to count it — that the gate's glob is `scripts/tests/test_*.py` and is
therefore **blind to hyphenated names**.

The two vacuous tests removed earlier that day (`test-allowlist-fix.py`,
`mutation-verify-guards.py`) were the *only* hyphenated files in the directory.
So the gate could not have seen them even in principle, and a test named with a
hyphen is additionally unreachable by `python3 -m unittest scripts.tests.X`.

## What a fix has to decide, and why it is not mechanical

Registering 188 suites blindly would be wrong. The honest work is triage:

- Some are **genuinely obsolete** — controls for scripts that no longer exist,
  or superseded by a later gate. Those should be deleted, not registered.
- Some are **expensive** and were deliberately left out of the fast path. Those
  belong in a slower gate, and the reason belongs in writing.
- Some are **live controls nobody wired in**, like the three above. Those are
  the real find.

Only the third category is a defect. Reporting all 188 as one number, as this
document's title does, is a deliberate simplification and should not survive
into the fix — **a lane must report the split, not the total.**

## The rule this generalizes

CLAUDE.md already states it for tests: *any test named "every X" must derive its
X from the authority, not from a literal.* The same principle applied to gates:
**a control's registration should be derived, not remembered.** A convention
where every `scripts/tests/test_*.py` is discovered and run — with an explicit,
reasoned opt-out list rather than an unexplained numeric floor — would make the
orphan count structurally zero and turn each exclusion into a written decision.

That is the same move that `scripts/check-shape-duplicates.py` already makes for
duplicate declarations: an allowlist where **every entry carries a reason**, and
which fails both when a new item appears and when an allowlisted one goes stale.
