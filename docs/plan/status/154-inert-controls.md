# Lane: inert-controls — the 188 Python controls no gate runs

<!-- plan-section: lane-status -->

**Triaged, fixed structurally, and the floor is gone (`DONE`, inert-controls,
2026-08-27).** Starting state, measured in this worktree at `a00924af0`:

```
CONTROL_REGISTRATION|controls=20|orphans=0|py_controls=382|py_orphans=188|py_baseline=188|py=ok
```

Ending state:

```
CONTROL_REGISTRATION|controls=21|orphans=0|py_controls=383|py_orphans=0|py_named=194|py_catchall=170|py_optout=19|py_optout_ceiling=19
PYTHON_CONTROLS|suites=170|tests=1208|failed=0|vacuous=0|named_elsewhere=194|optout=19|jobs=8|wall=39.6s
```

## The three-way split — and it is not the split the deficiency doc expected

The doc asked for obsolete / deliberately-slow / live-but-unwired. **Measured,
by running all 188 rather than reading them:**

| bucket | count | how it was decided |
| --- | --- | --- |
| **obsolete** | **0** | Every orphan's subject exists on disk. Checked two ways: a literal `scripts/…` path scan (0 of 188 referenced only missing paths) and, for the 14 that reference no literal path, reading each — they resolve their subject through `parents[1]` or a sibling package, and all resolve. **Nothing was deleted.** |
| **deliberately slow** | **0** | The whole set runs in **39 s wall at 8 jobs**. Serial total is 334 s and the 13 slowest are 250 s of it, but that never becomes a reason to split a 39 s step. An unused tier is a mechanism to maintain for nothing. |
| **live, nobody wired them in** | **188** | 160 pass as-is; 16 are written in a dialect the gate's invocation form cannot run; 12 are **red on `main` today**. |

The interesting finding is inside the third bucket, not between the buckets.

**16 suites are structurally unrunnable by every gate in this repository.** All
194 already-registered suites are `unittest.TestCase`; the dialect split falls
entirely inside the orphan set, which is what you would expect of code no gate
ever executed.

Detail moved to [`../notes/154-inert-controls.md`](../notes/154-inert-controls.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `be5fed9ad` | Derive python control registration; delete `PY_ORPHAN_BASELINE=188`. 7 guards, 12/12 mutation-killed; `py_orphans` 188 → 0. |
| 2026-08-27 | `b47deeb93` | `run-python-controls.py` + `control-optout.tsv`: 169 suites / 1193 tests now run; 9 pytest-dialect suites unwrapped from collecting zero tests. |
| 2026-08-27 | `a94a19480` | Open the lane; record the starting measurement. |
