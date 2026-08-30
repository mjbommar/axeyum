# Lane: creal-steps — level-1 phase-order fix applied to `creal.rs`

<!-- plan-section: lane-status -->

**Landed and green** (`WIP`, creal-steps, 2026-08-27). Applied the spike's
level 1 ([2026-08-27-prelude-build-spike.md](../../research/11-design-review/2026-08-27-prelude-build-spike.md))
to `crates/axeyum-lean-kernel/src/creal.rs`, exactly as recommended: one
`BuildStep` per top-level call in the existing 135-call
`build_creal_prelude_uncached` sequence (441 `CRealPrelude` fields; a
module's internal `declare_*` helpers fold into their module's single
dispatch entry, same granularity `poly.rs` used in the `complex.rs`
prototype). No field moved out of `CRealPrelude` — Part B stays explicitly
out of scope here, per the spike's own ~8,997-call-site estimate for a full
module split.

Headline: `validate_step_order` finds **0 violations across 2,264
requirement edges** against the existing hand-written order — it was
already topologically valid, same result as the `complex.rs` prototype.
Every one of the 443 fields is provided by exactly one step (0 duplicates,
0 gaps), confirmed by the extraction's own self-consistency check before
generating the table.

Detail moved to [`../notes/creal-steps.md`](../notes/creal-steps.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `de853af65` | Level-1 fix: `STEPS` (135 entries) + `validate_step_order` structural preflight for `creal.rs`, replacing the hand-written `declare_*` sequence in `build_creal_prelude_uncached` with `for step in STEPS { (step.run)(&mut d, prelude)?; }`. 0 violations across 2,264 edges against the existing order. `cargo check -p axeyum-lean-kernel --lib` clean, 0 warnings. |
| 2026-08-27 | `146927d8f` | Deliberate-failure controls + order pin: `steps_table_matches_recorded_extraction`, `existing_step_order_is_topologically_valid`, `order_violation_is_detected_and_precise`, `order_violation_reports_missing_provider_as_table_bug`. All green; failure controls verified to actually fail via a temporary mutation, reverted. `every_creal_declaration_is_checked_and_axiom_free` green (debug and `--release`). |
