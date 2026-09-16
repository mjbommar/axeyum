# `nra-single-cell-20260915` — ADR-2121 artifacts

Lane `NRA-SINGLE-CELL`. Everything here is reproducible from the committed
scripts; each one prints the control it passed before its result.

## Sizing (exit criterion 1, committed before any code)

- `sizing.py` — joins ADR-2110's `reference-join-83.tsv` (which engine inside z3
  decides each of the 83 undecided QF_NRA files) against its `shape-83.tsv`
  (variables, degree, coefficient magnitude, assertion shape).
- `sizing-45.tsv` — one row per CAD-only file, with both ceiling flags.
- `sizing-report.txt` — the run.

The script refuses to report unless its reconstruction of ADR-2110's CAD-only
set is exactly 45. That control is why the ceiling below can be read as a
statement about the same population the previous lane measured.

**Result: 24 of the 45 fall inside the slice's bounds** (≤ 4 variables,
degree ≤ 8, source coefficients ≤ `1<<40`), and all 24 are also a single
assertion with no top-level `or`, so the bound ceiling and the shape ceiling
coincide at 24. z3's CAD arm decides all 24 in under a second (median 108 ms).

Out of the 45, the excluded 21 split: 8 degree-only, 8 degree *and*
coefficient, 4 variable-count, 1 coefficient-only. **9 of 45 are excluded by
the `1<<40` coefficient clearing alone** — ADR-2110 claim 2's capability gap,
which this slice does not close.

**24 is a ceiling, not a prediction.** It is the count of files the route is
allowed to attempt. What it decides is what the A/B measures.
