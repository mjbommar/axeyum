# Lane: py-fields-registries — the Python prelude-field table and the gate that keeps it current

<!-- plan-section: lane-status -->

**Your lane's block (`done`, py-fields-registries, 2026-09-01).** Both defects
left by the ADR-1512 registry split are closed, and the reason they were
possible is closed with them.

**What was measured.** `CRealPrelude` is 606 names: 537 flat plus 69 in 14
per-module registries (`completeness` 5, `cos_sign` 6, `crossing` 9,
`ratio_test` 2, `inverse_fn` 2, `deriv_unique` 1, `mvt` 1, `polynomial` 10,
`extreme_value` 3, `ivt_boundary` 7, `lub_boundary` 4, `exp_fn` 4, `evt_row1` 1,
`pi` 14 — the brief's "62 in 13" was one migration behind). The Python table
carried 537 of them. `gen-py-prelude-fields.py --check` was registered in NO
gate: zero hits across `scripts/check.sh`, `scripts/check-merge-hygiene.sh`, the
`justfile` and `hooks/pre-push`, which is the whole explanation for how a stale
generated file reached main.

**What landed.** (1) The generator flattens a `*Names` field under a dotted name
(`("pi.pi_le_four", p.pi.pi_le_four)`), resolving the defining file by scanning
for `pub struct <T> {` rather than trusting the field-name-is-module-name
convention — and an unclassified field type is now a HARD ERROR rather than a
skip, which is the actual root cause. Table back to 606; workspace total
2,712 → 2,781. (2) `--check` registered in `check-merge-hygiene.sh` (guard 8),
`check.sh` and the `justfile`, with two controls and two mutants that kill
exactly one test each; its exit 2 means "no `rustfmt`, cannot answer" and is
reported as skipped rather than as drift. (3) `creal-migrate-registry.py` now
refuses a move whose fields are read by any workspace `.rs` file the rewriter
will not fix, naming each site as [GENERATED] or [hand-written]; nine controls,
seven mutants, all killed.

**What the next lane should know.** Every remaining module is currently
"blocked" by `prelude_fields.rs`, because that generated file names every field.
That is correct and the workflow is now: `--allow-external`, migrate, then rerun
BOTH `creal-declare-deps.py` and `gen-py-prelude-fields.py` — both are gated by
`check-merge-hygiene.sh`. This lane moved no fields.

**Not run:** `cargo test` (out of scope by brief). `cargo check -p axeyum-py`
and `clippy -p axeyum-py --all-targets -D warnings` both exit 0.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `f3a74e653` | generator reads ADR-1512 registries: `creal` Python table 537 → 606 names |
| 2026-09-01 | `9a6ef752b` | `gen-py-prelude-fields.py --check` registered in the merge gate, 2 mutants |
| 2026-09-01 | `5df5e43d3` | migration refuses a move that breaks a consumer outside the kernel crate |
