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

Extraction method: a throwaway Python static-analysis script (not
committed, per the spike's own precedent), reusing its approach —
transitive call-graph reachability per top-level step (same-file bare
calls plus `module::fn` calls), `name: p.<field>` / `add_inductive(...)`
literals for `provides`, kernel-generated recursors attributed to their
inductive (`add_inductive` never names the recursor literally), plus a
generalization the `complex.rs` prototype resolved by hand: a generic pass
over this file's `name: NameId`-parameter closures/helpers (`constant`,
`projection`, `declare_operation`, `declare_universal`,
`declare_congruence`, `declare_domination`, `declare_ivt_bisect_*`) that
declare via a parameter rather than a literal, attributing the call-site
argument at the `name` parameter's position.

Zero behaviour change: the hand-written `declare_*` sequence became `for
step in STEPS { (step.run)(&mut d, prelude)?; }`, calling the same
functions in the same order (pinned by
`steps_table_matches_recorded_extraction`). `every_creal_declaration_is_
checked_and_axiom_free` (environment-derived) stayed green throughout,
`--release` too. `creal_prelude_builds` measured 29.87s / 29.98s
(two runs) against a documented baseline band of ~32-38s under load — no
regression. No `creal/*.rs` file needed a signature change (every
`declare_*` already matched `fn(&mut IntDev<'_>, CRealPrelude) ->
Result<(), KernelError>`), so this lane touched only `creal.rs` and
`creal_tests.rs`.

Two deliberate-failure tests (`order_violation_is_detected_and_precise`,
`order_violation_reports_missing_provider_as_table_bug`) mirror
`complex_tests`'s own controls and were verified to actually fail: flipped
one assertion's expected value, reran, confirmed `FAILED`, reverted.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `de853af65` | Level-1 fix: `STEPS` (135 entries) + `validate_step_order` structural preflight for `creal.rs`, replacing the hand-written `declare_*` sequence in `build_creal_prelude_uncached` with `for step in STEPS { (step.run)(&mut d, prelude)?; }`. 0 violations across 2,264 edges against the existing order. `cargo check -p axeyum-lean-kernel --lib` clean, 0 warnings. |
| 2026-08-27 | `146927d8f` | Deliberate-failure controls + order pin: `steps_table_matches_recorded_extraction`, `existing_step_order_is_topologically_valid`, `order_violation_is_detected_and_precise`, `order_violation_reports_missing_provider_as_table_bug`. All green; failure controls verified to actually fail via a temporary mutation, reverted. `every_creal_declaration_is_checked_and_axiom_free` green (debug and `--release`). |
