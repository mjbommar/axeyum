# Lane 360 — `CReal.supOn` (EVT row 1)

<!-- plan-section: lane-status -->

## Status

**IN PROGRESS.** Lane opened 2026-08-30 against ADR-0675's split verdict:
IVT's Pareto claim holds, EVT's does not, because EVT has a row-2
impossibility result (`CReal.evt_attained_max_decides_sign`) with no
constructive row 1 behind it. `CReal.supOn` is the declaration that converts
that trade into a dominance.

Starting state read from `crates/axeyum-lean-kernel/src/creal/supremum.rs`'s
module doc: rungs 1-6 landed (`maxRange` + order facts, `meshLevelCount`,
`meshMax`, `meshMax_step_le`/`_mono`, `expOfModulus`/`trueExpOfModulus` +
monotonicity, `meshPointNearCoarse`, `maxRange_le_add_of_exists`,
`meshMax_le_add_of_step_close`). Not landed: `supOn`.

## Next

Discharge `mesh_max_le_add_of_step_close`'s `hclose` hypothesis from
`uc_spec` (modulus arithmetic, no mesh geometry), then the telescope and
`CReal.mk (speedup f_lambda K) (regular_of_scaled_cauchy ...)`.
