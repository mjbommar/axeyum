# Notes: creal-steps

Detail moved out of [`../status/creal-steps.md`](../status/creal-steps.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
