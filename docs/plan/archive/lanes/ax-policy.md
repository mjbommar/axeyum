# Lane: ax-policy — which model a `sat` returns (ADR-2140; items 6, 7, 9 of the 2026-09-16 list)

<!-- plan-section: lane-status -->

**AX-POLICY (`WIP`, ax-policy, 2026-09-17).** `ModelPreference { Any, PreferZero,
LeastUnsigned }` on `SolverConfig`, reaching the one-shot and warm SAT cores as a
forced decision polarity and finishing the model with a replay-checked shrink;
`solve_smtlib_least_witness` (the 1/16/256/4096 magnitude ladder) behind
`(set-option :model-preference …)`, `AXEYUM_MODEL_PREFERENCE` and
`axeyum.smt.least_witness`; typed `IncrementalStats` with a `profiled` field in
the Python bindings. **`Any` ships; no default moved.** The sizing finding that
shaped the design: the Boolean core already decides `false` first, and the forced
phase alone moved 0 of 15 corpus models (gate variables, not input bits, are what
the search decides) while costing +25-27 % wall on the QF_BV pinned list with one
stable gain against one stable loss; so `PreferZero` finishes on the lifted model
(replay-checked shrink, +12 %, no movers, 0 `:status` disagreements) and the
SAT-core phase ships off behind `AXEYUM_MODEL_PREFERENCE_PHASE=on`. Next: the
defects example (`check.py`) can drop its `BOUNDS` loop for `smt.least_witness`
once item 1 (call the library, not the subprocess) lands; Glaurung's
concretization sweep is now a one-variable experiment.

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-policy | ADR-2140: `ModelPreference` on `SolverConfig` (SAT-core forced phase + replay-checked shrink), `solve_smtlib_least_witness`, `:model-preference` option, `AXEYUM_MODEL_PREFERENCE` lever, `smt.least_witness`, typed `IncrementalStats`; `tests/model_preference_2140.rs` (identity, non-vacuity, determinism, replay) + mutation controls; three model-choice seeds in `corpus/regression/qf_bv/`. |
