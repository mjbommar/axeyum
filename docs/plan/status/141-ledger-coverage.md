# Lane: ledger-coverage — measuring how far the fact ledger trails the kernel

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ledger-coverage, 2026-08-27).** Built
`scripts/gen-ledger-coverage.py`, the headline measurement
`docs/plan/status/141-ledger-6-backlog.md`'s closing paragraph asked for and
that no ledger batch had ever run: the full diff of
`prelude_theorem_inventory --include-constructed`'s theorem list against
`artifacts/facts/`'s registered names. Registered in `scripts/check.sh` and
`justfile` (`generated-trackers`) as a permanent `--check` gate, matching the
`gen-import-backlog.py` convention exactly.

**Headline, measured 2026-08-27 (post-merge with `main`):** denominator is
every distinct `Declaration::Theorem` across every constructed prelude —
**1,397** (up from the "1,332+" this lane's brief was given; a `mvt.rs` /
`extreme_value.rs` batch landed the same day). Of those, **474 registered,
923 unregistered — 34% coverage**. By prelude: `creal` 132/369, `nat`
86/329, `rat` 116/244, `integer` 53/153, `complex` 36/117, `cpoint` 27/89,
`logic` 24/32, **`string` 0/64** (a real finding, not a join gap — zero
facts mention any `axeyum.string.2.*` name at all). Full per-prelude
unregistered name lists are in `artifacts/ledger-coverage.json`, which is
the work queue this measurement exists to produce, not just a count.

Denominator rule and full reasoning: `docs/autogenesis/297-ledger-coverage-gate.md`.

Detail moved to [`../notes/141-ledger-coverage.md`](../notes/141-ledger-coverage.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Added `scripts/gen-ledger-coverage.py` + `scripts/tests/test_gen_ledger_coverage.py` (26 tests) + `scripts/tests/mutation_controls.py` `ledger-coverage` suite (7 guards) + `artifacts/ledger-coverage.json` + one-line registrations in `scripts/check.sh` and `justfile`. Headline: 1,397 kernel theorems, 474 registered, 923 unregistered (34%). |
