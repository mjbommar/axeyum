# Lane: s4-simplex-warm-start — the simplex was already warm; what cost 84% of the budget was one pivot

<!-- plan-section: lane-status -->

**S4 of the [SMT/SAT parity plan](../smt-parity-plan-2026-09-05.md) landed:
the pivot's redundant `O(rows × columns)` value pass is gone (4.5x on the
committed simplex bench, 20x on a traced file whose search is byte-identical
between arms) and implied bounds are now computed over the whole linear form
rather than one variable** (`DONE`, s4-simplex-warm-start, 2026-09-05).

Commits `21b5f29f1`, `e9117040a`, `1266c3abd`, and this one. Full measurement:
[the S4 note](../../research/11-design-review/2026-09-05-s4-simplex-warm-start-measured.md).

## Deliverable 0 — the brief's premise was measurably false

The plan §2.2 and the lane brief both located the QF_LRA cost in a missing warm
start: "each final check appears to re-decide feasibility from the current
bounds rather than resuming the previous tableau". Six counters were wired
through a new defaulted `TheorySolver::engine_counters` before anything was
changed. On `QF_LRA/2019-ezsmt/blending/1.smt2` at the merge-base:
`simplex_checks = 6,571`, `simplex_pivots = 15,375` (**2.3 per check**),
`simplex_cold_restarts = **0**`, tableau 350 × 425,
`theory_final_check_ms = 21,686` of 24,000.

Not one of those 6,571 checks discarded the basis, and `bound_assertions`
tracked the search's own total live pushes, i.e. each asserted constraint
entered the tableau exactly once. **The warm start already existed.** What the
counters price is one pivot: 1.41 ms on that file, 3.39 ms on
`_count_by_k.i_3_3_2.bpl_7`.

Propagation was separately near-inert: 79 literals offered across those 6,571
checks, because `unit_bound` returned `None` for any constraint naming more
than one variable — which is most LRA atoms.

## What landed

1. **`Tableau::pivot_and_update` does Dutertre–de Moura's `pivotAndUpdate`.**
   The entering column is read once before the elimination zeroes it, θ comes
   from the old values, and every other basic variable moves by
   `a_{i,enter}·θ` in `O(rows)` — replacing a second `O(rows × columns)` pass
   that recomputed each basic value from its row in `ℚ(δ)` (two rationals per
   cell, so the more expensive half), re-deriving numbers the update already
   determines. Zero cells are skipped in both the pivot-row rewrite and the
   elimination.
2. **Implied bounds over the linear form.** `assign_forms` gives every
   constraint template its canonical functional (divide through by the
   lowest-indexed variable's coefficient; direction kept for a positive leading
   coefficient, flipped for a negative one). `bound_lower`/`bound_upper` are
   indexed by form, not by variable, so `x + y ≤ 3` now settles `2x + 2y ≤ 8`
   by one rational comparison, and two crossing bounds on a multi-variable form
   are refuted by `assert` with a two-literal core and no simplex run. A single
   variable is the form with one coefficient, so nothing that propagated before
   stops. `MAX_BOUND_PROPAGATIONS_PER_CALL = 256` bounds a call and costs no
   completeness — the driver runs propagation to a fixpoint, so a capped call
   resumes on the next iteration rather than discarding.
3. **The counters**, out to `smtcomp_cli --trace`, where an absent counter
   prints `n/a` and never a measured `0`.
4. **`scripts/gen-plan.py` now rebases links in global sections too.**
   `check-links.sh` was red on main: `rebase_links` was applied to lane bodies
   only, so the first `../`-relative link in a `docs/plan/global/` section
   (`20-next-actions.md`, landed with the parity plan) escaped the repository
   once inlined into `PLAN.md`. Not this lane's link, but its gate.

## Measured

| measurement | before | after |
|---|---|---|
| criterion `simplex_pivot` (12 vars, 18 rows) | 207.30 µs | **46.25 µs** (4.5x, non-overlapping CIs) |
| `p-driverlogNumeric_s7` final-check, identical search both arms | 968 ms / 75 checks | **48 ms / 75 checks** (20x) |
| `blending/1` ms per final check | 3.18 | **0.80** |
| `blending/5` ms per final check | 4.00 | **0.65** |
| 33-file QF_LRA population, same-protocol arms | 4 / 33 decided | **5 / 33** |

The conversion is `2019-ezsmt/blending/5.smt2`, unknown 24,156 ms → **unsat
21,343 ms**. **No P0**: not one verdict in either arm contradicts the
population's `declared` column across 66 runs.

## The exit criterion is not met as written, and the reason is structural

The criterion was *per-call final-check time and call count both fall on the
five*. Per-call time falls on 4 of 5 (up to 20x) and rises 1.45x on
`_count_by_k`. The call count falls on **1** of 5, is flat on one, and rises on
three — sharply on the two blending files (6,798 → 17,016 and 5,125 → 18,410).

That conjunction is self-defeating on a fixed budget. `final_checks` is not a
fixed amount of work; it is how many total Boolean assignments the search
reached in 24 seconds. Make each check 4x cheaper and the search reaches more
of them — on `blending/5`, 2.8x more decisions and 3.6x more final checks in
the same budget, which is exactly what converted the file to `unsat`. A falling
call count at a fixed budget would mean the search got *slower* per assignment.

The count falls the way the criterion intends only where propagation prunes
faster than the cheaper check adds. That happened on `_count_by_k`
(propagations 926 → 7,315, final checks 880 → 611) and **did not pay**: more
live constraints per check drove 73 pivots per check against 5.5, per-call time
rose, and `theory_final_check_ms` came out flat. **The propagation half is not
uniformly a win**, and that file is the recorded counter-example.

## Mutation controls

| mutation | effect | verdict |
|---|---|---|
| warm start disabled (`check` rebuilds the pristine basis every call) on `p-driverlogNumeric_s7` | pivots per final check **5.25 → 127.0** (24.2x); final-check 48 → 528 ms; `simplex_cold_restarts` 0 → 75; decisions/final_checks/conflicts identical (1904/75/180) | `sat`, **unchanged** |
| the `O(rows)` value-update loop deleted | `tableau_invariant_holds_after_every_pivot` fails at `seed 0 … after pivot 0` | — |

Both restored; the suites re-run green after restore.

## Gates

`--lib --features full` 1450 passed · `--test cdclt_lra_online` 9 · `--test
corpus_regression` 1 (159 s) · z3 fuzzes `qf_lra_differential_fuzz` 5,
`simplex_lra_fallback_differential` 1, `qf_uflra_differential_fuzz` 1 (the
documented 5+1+1) · `progress_frontier --features full --test-threads=1`
**12 passed** on the second attempt; the first reported `REGRESSION
[bv_reduction] 27 < 30`, and the control says it was contention, not this
change: run alone, `frontier_bv_reduction` **passes in both arms** · `check
--workspace --all-targets` · `clippy -p axeyum-solver --all-targets
--all-features -D warnings` · wasm32 build · `check-links.sh` all links ok.

## Not done

- `scripts/parity-run.sh QF_LRA` / `QF_UFLIA` on an idle host — the plan §6
  protocol for a division count. This lane measured the 33-file population, not
  the 200-file parity list.
- QF_UFLIA was **not** scored: `bench-results/parity-losses-20260905/QF_UFLIA.txt`
  did not exist on local main at measurement time.
- The tableau-**row** implied-bound scan the brief named literally. In this
  encoding bounds live only on slack variables while every problem variable is
  unbounded, so at the pristine basis no row implies a finite bound on
  anything; the form-indexed check is the derivation that pays here, and the
  reasoning is recorded in the note rather than left as an omission.
- The first three commits of this lane carry `Agent: retire-generic-1`: the
  session's `AXEYUM_AGENT` was stale from an earlier lane and was not
  overridden until `1266c3abd`. Recorded, not rewritten.
