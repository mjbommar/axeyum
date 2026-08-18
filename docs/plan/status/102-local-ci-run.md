# Lane: local-ci-run — the authoritative gate, actually run

<!-- plan-section: lane-status -->

**`scripts/local-ci.sh` has now completed once, and it was RED** (`WIP`,
local-ci-run, 2026-08-18). Hosted CI has called it "the authoritative gate for
`main`" since it existed; nothing had ever run it. The record is
[`artifacts/local-ci-runs/a6ee37c6a-s4.json`](../../../artifacts/local-ci-runs/a6ee37c6a-s4.json):
**6401 s (1 h 47 m), 7511 tests, 7507 passed, 4 failed, 32 skipped.**

The four were deterministic and one cause: `b760fd6ae` (+863) and `46724faec`
(+777) added **1 640 bytes of module header** to every emitted Lean module and
each re-pinned only the golden module that sits in a gate. Third recurrence;
`6389e0194` documented it for three of these same suites on 2026-08-15.
Re-pinned at cause, green. The structural point is not the pins: **no pre-merge
gate runs those four `tests/*.rs` suites** — `--lib` skips integration targets —
so the only reader of those pins was the gate nobody ran.

Two defects in the gate itself, both found by running it:

- It gated the **WORKING TREE**. In a shared checkout that means a sibling
  lane's uncommitted work decides whether a SHA passes. Now gates a detached
  worktree at the commit, `hooks/pre-push`'s own solution (`a2841965e`).
- `count_tests` anchored nextest's summary at `^`; nextest indents it five
  spaces. It never matched, so the recorder wrote `tests: -1` for the 7511-test
  step and the zero-test rule **could not fire on the sweep it exists for** —
  the control's fixture was typed from the docs, not captured (`e069afa03`).

Cost is not core-bound: 2.47x parallelism on 16 cores, five single-test
binaries being 40% of the wall. Next: a timer on s5/s7 — which **measured today
cannot run it** (no stable, no 1.88.0, no nextest; 342 and 422 commits behind) —
read by a freshness step inside `just check`, not by a dashboard.
Detail in [`../notes/102-local-ci-run.md`](../notes/102-local-ci-run.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | `31442bd5d` | `quant_{affine_growth,counterexample_cover,eq_partition,residue}` — four golden Lean-module pins re-pinned at cause (+1 640 header bytes from `b760fd6ae` and `46724faec`), unredding `main`. Found by the first completed run of the authoritative gate. |
| 2026-08-18 | `e069afa03` | `local-ci`: the zero-test guard could not fire on the workspace sweep — nextest's summary is indented and the pattern was `^`-anchored. Fixtures now captured from the tool; a test step whose count is unparseable is `unreadable` (89), not `pass`. |
| 2026-08-18 | `69c12646c` | `artifacts/local-ci-runs/a6ee37c6a-s4.json` — first completed run of `scripts/local-ci.sh` in this repository's history. FAIL, 6401 s, 4 of 7511. |
| 2026-08-18 | `a2841965e` | `local-ci` gates the COMMIT, not the working tree: stable flock'd detached worktree, `--no-worktree` opt-out, controls mutation-tested. |
