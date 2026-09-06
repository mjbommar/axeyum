# Lane: s4-simplex-warm-start — the simplex was already warm; what cost 84% of the budget was one pivot

<!-- plan-section: lane-status -->

**S4 of the [SMT/SAT parity plan](../smt-parity-plan-2026-09-05.md) (§2.2, §4
row S4). IN PROGRESS, s4-simplex-warm-start, 2026-09-05.**

## Deliverable 0 — the counters, and what they say about the brief's premise

The brief and [the parity plan §2.2](../smt-parity-plan-2026-09-05.md) frame the
QF_LRA lever as "warm-start each final check from the previous tableau instead of
re-deciding feasibility", on the reading that "each final check appears to
re-decide feasibility from the current bounds rather than resuming the previous
tableau". **That premise is measurably false**, and the same counters name the
real cost.

Six counters were wired to `TheorySolver::engine_counters` (defaulted, so every
other implementor is unchanged) and out through `TheoryLayerStats` to
`smtcomp_cli --trace`: `simplex_pivots`, `simplex_checks`,
`simplex_cold_restarts`, `bound_retractions`, `bound_assertions`,
`propagations_offered`, plus the tableau's `simplex_rows` × `simplex_columns`.
An absent counter prints `n/a`, never `0`.

Measured on the traced files, `taskset -c 0-7`, `--timeout-ms 24000`, load 20–31
on a 16-thread shared host:

| file | final_check_ms | simplex_checks | simplex_pivots | pivots/check | ms/pivot | cold_restarts | rows × cols | propagations_offered |
|---|---:|---:|---:|---:|---:|---:|---|---:|
| `2017-Heizmann/_count_by_k.i_3_3_2.bpl_7` | 17,002 | 917 | 5,009 | 5.5 | 3.39 | **0** | — | 963 |
| `2019-ezsmt/blending/1` | 21,686 | 6,571 | 15,375 | 2.3 | 1.41 | **0** | 350 × 425 | 79 |

Three findings, each a number rather than a reading:

1. **The basis already persists.** `simplex_cold_restarts = 0` on both files:
   not one of the 7,488 checks discarded the basis. `SimplexEngine::sync`
   reconciles a shared prefix and `Incremental::check` resumes
   `Tableau::run` from whatever basis it holds — the warm start the module
   header claims is real. `bound_assertions` (80,389 on `blending/1`) tracks the
   search's own `decisions` (15,220) and total live pushes, i.e. each asserted
   constraint enters the tableau **once**, which is the minimum an incremental
   engine can do.
2. **The pivot count is already small; the pivot COST is not.** 2.3–5.5 pivots
   per check, at **1.4–3.4 ms each**. With a 350 × 425 dense tableau one pivot
   is `O(rows × columns)` exact-rational work, and until this lane
   `pivot_and_update` paid it **twice**: once to rewrite the rows, and again to
   recompute every basic variable's value from its row — in `ℚ(δ)`, two
   rationals per cell, so the more expensive of the two halves. Dutertre–de
   Moura's `pivotAndUpdate` derives those values in `O(rows)`.
3. **Propagation is nearly inert.** 79 literals offered across 6,571 final
   checks on `blending/1`. `propagate_bounds` only fires for an atom whose
   constraint is a **one-variable** bound (`LraTheory::unit_bound`), and most
   LRA atoms are multi-variable, so it returns nothing for them.

So the exit criterion's two halves have two different levers: per-call
final-check time is the per-pivot cost (finding 2), and the call count is
propagation (finding 3). Rebuilding a warm start that already exists would have
moved neither.

## Landed so far

- `simplex.rs`: `pivot_and_update` now performs the Dutertre–de Moura `O(rows)`
  value update instead of an `O(rows × columns)` recompute, reads the entering
  column once before the elimination zeroes it, and skips zero cells in both the
  pivot-row rewrite and the elimination. New test
  `tableau_invariant_holds_after_every_pivot` steps the pivot loop one pivot at
  a time (`budget = 1`) over 300 random systems and asserts
  `β(basic[i]) = Σ row[i][v]·β(v)` between every pair of pivots, with a
  non-vacuity floor on the pivots exercised. **Mutation control:** deleting the
  value-update loop fails it at `seed 0 … after pivot 0`; restored.
- The counters above, and their `--trace` line.

## Next

Implied-bound propagation over the whole linear form rather than a single
variable, then the before/after measurement on the 33-file LRA population.
