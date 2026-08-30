# Notes: 141-ledger-coverage

Detail moved out of [`../status/141-ledger-coverage.md`](../status/141-ledger-coverage.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
