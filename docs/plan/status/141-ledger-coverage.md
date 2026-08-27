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

**Join reliability, all 818 facts:** 576 are `kernel-lean` +
`proved`/`computed`. A single-tier join (the sibling
`check-fact-depends-derived.py::theorem_of` extraction alone) undercounted
badly for two preludes — `logic` at 2/32, `string` at 0/64 as fictitious
near-zeroes — because that extraction's namespace allowlist has no
provision for `And`/`Or`/`Iff`/`Decidable`/`Eq` or bare (non-namespaced)
logic-prelude names. Added a second tier reading the declared name straight
out of a `lean4` fact's own `formal.statement` head (`theorem <Name> :` /
bare `<Name> :`), which raised `logic` to 24/32 and the overall registered
count from 451 to 474. Final tier breakdown: 127 resolved via the explicit
`formal.kernel_theorem` field, 374 via the statement-name tier, 2 via the
checker_command fallback, **74 unresolved** — genuinely unrecoverable from
the fact's own recorded evidence (mostly `lean4-surface` statements whose
`checker_command` names a Rust test function, not a dotted kernel name),
reported in `join.unresolved_fact_ids` rather than guessed at. One
placeholder-rejection guard was needed: a literal `"TODO: the formal
statement..."` fact would otherwise parse as declared name `TODO`.

**The gate demonstrated red, not just asserted:** appended one synthetic
theorem name to a copy of the real `prelude_theorem_inventory` TSV output
and ran `gen-ledger-coverage.py --check --theorem-tsv <fixture>` — exits 1
against the committed artifact, while the real `--check` (no override)
stays green. `--theorem-tsv` is a documented testing/demo hook, never used
in production. 7 mutation guards registered in
`scripts/tests/mutation_controls.py ledger-coverage`, each killed by exactly
one of 26 tests in `scripts/tests/test_gen_ledger_coverage.py`
(`python3 scripts/tests/mutation_controls.py ledger-coverage` — all 7
`killed 1`).

Did not register anything in `artifacts/facts/` (other lanes own it, per
scope) and did not touch `crates/`, `hooks/`, or the other validators.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Added `scripts/gen-ledger-coverage.py` + `scripts/tests/test_gen_ledger_coverage.py` (26 tests) + `scripts/tests/mutation_controls.py` `ledger-coverage` suite (7 guards) + `artifacts/ledger-coverage.json` + one-line registrations in `scripts/check.sh` and `justfile`. Headline: 1,397 kernel theorems, 474 registered, 923 unregistered (34%). |
