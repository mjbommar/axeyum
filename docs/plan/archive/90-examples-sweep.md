# Lane: examples-sweep — Cargo example catalog parity

<!-- plan-section: lane-status -->

**Lane closed (`DONE`, examples-sweep, 2026-08-15).** Task was
`docs/refactor-2026-08` finding #4 ("documents assert what the code does
not"): `python3 scripts/check-parity-docs.py` was red because six landed,
git-tracked Cargo examples were missing from `docs/reference/examples.md`.
Added a catalog row for each, stating the boundary/question the example
answers rather than restating its name, verified against the example's `//!`
header, `main`, and (for the timing/measurement claims) the landing lane's own
status file. All three gates (`check-parity-docs.py`, `check-links.sh`,
`gen-plan.py --check`) are green. No other lane's untracked WIP was touched;
none was found among the flagged files.

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | `docs/reference/examples.md`: documented six landed Cargo examples that `check-parity-docs.py` flagged as missing — `geometry_linear_route`, `lean4export_census`, `nat_add_reduction_probe`, `arith_model_witness`, `ordered_ring_refutation` (the five named by the task), plus `prelude_build_timing` (flagged by the gate itself, not on the original list). The example-count marker in `docs/documentation-plan.md` and `PLAN.md` was already correct (67) and needed no edit. |
