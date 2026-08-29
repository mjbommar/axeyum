# Lane: solver-cycle-regression — dependency-cycle regression in `axeyum-solver`

<!-- plan-section: lane-status -->

**Fixed and committed** (`WIP`, solver-cycle-regression, 2026-08-29).

## What the gate actually said (correcting the task text)

The exact FAIL text this task was handed — `NEW CYCLE MEMBERS: grp, x`,
`LARGEST CYCLE GREW: 0 -> 3 lines (from nothing)`, `LARGEST CYCLE GREW:
2 -> 802 lines (401.00x)` — is **not from `scripts/analyze_solver_module_graph.py
--check`**, the gate `check.sh` actually runs (`scripts/check.sh:711`). It is
stdout from `scripts/tests/test_analyze_solver_group_collapse.py`'s own
mutation-control fixtures: `grp`/`x` are literal synthetic module names that
test file constructs on purpose to prove the guard fires on a deliberately-bad
grouping. Confirmed by running that suite directly: **14/14 tests pass**, and
the "401x" figure is also independently a *documented historical example* in
`analyze_solver_module_graph.py`'s own source comments (a 2026-08-17 measurement
on a proposed `arith/` directory, never landed). Neither is a live regression.

The real gate, run directly (`python3 scripts/analyze_solver_module_graph.py
--check`), reported different names and different numbers throughout this
investigation — see below.

## When and why (the real regression)

`docs/refactor-2026-08/solver-module-graph-baseline.json` was last written by
commit `90ef09a80` on **2026-08-17 09:32:14 -0400**. The gate has been red
since **~11:27 that same day** — 12 days as of this writing, unrelated to any
lean-kernel work from today. Two commits landed in the intervening two hours,
each independently closing a previously-acyclic module into the 26-module
theory-core cycle:

1. `8f8c12dce` "feat(solver): wire N-induction into `solve`" (10:58) added
   `auto.rs -> nat_induction::prove_by_nat_induction` (the dispatch rung).
   `nat_induction.rs` already had `use crate::auto::check_auto;` (to discharge
   its base/step obligations), present since the file's creation
   (`7d1c7ceed`, before the baseline). The new edge closed `auto <-> nat_induction`.
2. `287556743` "feat(solver): the e-matching driver can now hand out the
   instances it used" (11:27) **created** `quant_instance_set_cert.rs`,
   importing `qinst_egraph::{QuantifierGroundDerivation,
   check_quantifier_ground_derivation}`, while wiring `qinst_egraph.rs` to
   call `quant_instance_set_cert::collect_ground_derivations` (named
   `build_instance_set_certificate` at the time) at 5 call sites. A
   self-contained mutual dependency closed within one commit.

Verified nothing else in the 26-module cycle referenced either new module —
`grep -rl` across all cycle members turned up only `auto.rs`↔`nat_induction.rs`
and `qinst_egraph.rs`↔`quant_instance_set_cert.rs`, so these two edges were the
whole story.

## The fix (landed, commit `0348564ab`)

Both broken by dependency inversion / relocation, no behavior change:

- **`nat_induction`/`auto`**: `prove_by_nat_induction` and its private
  `refuted` helper now take a `Discharge` function-pointer parameter
  (`fn(&mut TermArena, &[TermId], &SolverConfig) -> Result<CheckResult,
  SolverError>`) instead of importing `crate::auto::check_auto` directly.
  `auto.rs`'s one call site passes `check_auto`. The 4 test files under
  `tests/nat_induction*.rs` (6 call sites) updated to pass `check_auto` too.
- **`quant_instance_set_cert`/`qinst_egraph`**: `collect_ground_derivations`
  moved from `quant_instance_set_cert.rs` into `qinst_egraph.rs`. It was
  `qinst_egraph`'s only caller and operates purely on `qinst_egraph`'s own
  `QuantifierGroundDerivation` type and `check_quantifier_ground_derivation`
  function, so it belonged there. `qinst_egraph.rs`'s 5 call sites dropped the
  `crate::quant_instance_set_cert::` prefix. The reverse edge
  (`quant_instance_set_cert -> qinst_egraph`, for `portable_certificate`'s
  `&[QuantifierGroundDerivation]` parameter) is the only one left, so the pair
  is no longer mutual.

### Measured before/after

```
                          before fix    after fix     baseline (pre-regression)
NEW CYCLE MEMBERS         nat_induction, quant_instance_set_cert   (none)
largest cycle             26 modules, 60,298 lines  24 modules, 59,175 lines  24 modules, 58,215 lines
modules_in_cycles (total) 43            41           41
```

`modules_in_cycles` (the full set, all cycles) is now **byte-for-byte
identical** to the baseline — verified programmatically (set difference both
directions is empty). `NEW CYCLE MEMBERS` no longer fires.

Ran the affected suites directly (not the aggregate gate):
`cargo test -p axeyum-solver --features full --test nat_induction --test
nat_induction_adversarial` → **15/15 pass**. `cargo check -p axeyum-solver
--all-targets --features full` clean.

## What's left on this gate, and why it's out of scope here

Two failures remain, from the same `analyze_solver_module_graph.py --check`
run, and neither is from a newly-closed cut point (membership is unchanged
from baseline):

- `LARGEST CYCLE GREW: 58,215 -> 59,175` lines (+1.6%, down from the
  regression's 60,298).
- `EVIDENCE LAYER FAN-OUT WIDENED: evidence 67 -> 77, reconstruct 55 -> 60`.

Both are organic line-count / fan-out growth in modules that were *already*
in the cycle / evidence layer at baseline time, accumulated over 12 days of
ordinary feature work (NRA/NIA certificate modules, string routes, etc. all
needed wiring into `evidence.rs`). This is exactly the mass problem
`docs/refactor-2026-08/03-solver-decomposition.md` D1/D3 already scopes — not
a new phenomenon this task introduced or found, and not fixable by a small
edge change. Left for that track; **did not touch `evidence.rs` or
`reconstruct.rs`**, and did not raise the baseline.

## Files changed

- `crates/axeyum-solver/src/nat_induction.rs` — `Discharge` type, threaded
  through `prove_by_nat_induction`/`refuted`.
- `crates/axeyum-solver/src/auto.rs` — one call site updated to pass
  `check_auto`.
- `crates/axeyum-solver/src/qinst_egraph.rs` — `collect_ground_derivations`
  moved in; 5 call sites updated.
- `crates/axeyum-solver/src/quant_instance_set_cert.rs` —
  `collect_ground_derivations` moved out, replaced with a comment pointing to
  its new home.
- `crates/axeyum-solver/tests/nat_induction.rs`,
  `tests/nat_induction_adversarial.rs`, `tests/nat_induction_corpus.rs` — 6
  call sites updated to pass `check_auto`.

<!-- plan-section: landed-changes -->

| 2026-08-29 | `0348564ab` | Break the `auto<->nat_induction` and `qinst_egraph<->quant_instance_set_cert` cycle-closing edges from 2026-08-17; `modules_in_cycles` now matches the pre-regression baseline exactly. Residual mass/fan-out growth on the same gate is pre-existing, tracked by D1/D3, left untouched. |
