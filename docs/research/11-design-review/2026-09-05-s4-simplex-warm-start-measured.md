# S4 measured: the simplex was already warm, the pivot was not cheap, and the exit criterion's two halves pull against each other

Lane `s4-simplex-warm-start`, 2026-09-05/06. This is the measurement report for
slice S4 of the [SMT/SAT parity plan](../../plan/smt-parity-plan-2026-09-05.md)
(§2.2, §4 row S4), whose brief was "warm-start each final check from the
previous tableau instead of re-deciding feasibility" plus "implied-bound
propagation through the ADR-1701 propagate hook".

Landed as `21b5f29f1` (counters + the pivot value update), `e9117040a` (the
form-indexed implied bounds) and `1266c3abd` (the raw before/after data).

## 0. Method

**Arms.** BEFORE is `scripts/lane-snapshot.sh 0076811ff` — the merge-base with
main — built with `scripts/cargo-serialized.sh build --release -p axeyum-bench
--example smtcomp_cli` into its own `CARGO_TARGET_DIR`; the snapshot is
`--touch`-stamped so cargo's mtime freshness check is not fooled. AFTER is this
lane's worktree at `1266c3abd`. Confirmed different before anything was
measured:

```
d2b7d43e45e0d9ec13f2994d5ff77ee8029f1676a4b8dd2ffea2af63f1f93881  BEFORE (41,659,568 bytes)
7c2be535b784fe394861f2de2d309367e2619f5fbed0be16f60f49049db67e08  AFTER  (41,685,240 bytes)
```

**Run parameters.** Every file goes through both arms back to back (before,
after, next file), `taskset -c 0-7`, `--timeout-ms 24000`, wrapped in
`timeout -k 2 30s`, wall time measured around the whole process. Three
foreground batches of 12/12/9.

**Load.** 14 to 38 (1-minute average) on a 16-thread host with other lanes
active throughout, recorded per row in the raw data. **This is not an idle
host**, and two files in the population sit close enough to the 24 s line that
the verdict moves with the load — said plainly below rather than absorbed into
a summary number.

**Population.** `bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`,
the 33 QF_LRA search timeouts ADR-1701's slice-1 measurement drew. The
QF_UFLIA reference-only list the brief named as an optional second population,
`bench-results/parity-losses-20260905/QF_UFLIA.txt`, **did not exist on local
main** at measurement time, so QF_UFLIA was not scored. Raw data:
`bench-results/s4-simplex-warm-start-20260905/`.

## 1. Finding 0 — the brief's premise was false, and a counter is what said so

The plan and the brief both located the QF_LRA cost in a missing warm start:
"each final check appears to re-decide feasibility from the current bounds
rather than resuming the previous tableau". Before changing anything, six
counters were wired through a new defaulted `TheorySolver::engine_counters`
into `TheoryLayerStats` and out to `smtcomp_cli --trace`, where an absent
counter prints `n/a` and never a measured `0`.

On `QF_LRA/2019-ezsmt/blending/1.smt2`, at the merge-base:

| counter | value |
|---|---:|
| `theory_final_check_ms` | 21,686 of a 24,000 ms budget |
| `simplex_checks` | 6,571 |
| `simplex_pivots` | 15,375 → **2.3 pivots per check** |
| `simplex_cold_restarts` | **0** |
| `simplex_rows` × `simplex_columns` | 350 × 425 |
| `bound_assertions` / `bound_retractions` | 80,389 / 80,081 |

`simplex_cold_restarts = 0` says it directly: not one of those 6,571 checks
discarded the basis. `SimplexEngine::sync` already reconciles a shared prefix of
the bound stack and `Incremental::check` already resumes `Tableau::run` from
whatever basis it holds. `bound_assertions` tracks the search's own total live
pushes, i.e. **each asserted constraint entered the tableau exactly once**,
which is the floor for an incremental engine. The warm start the plan asked for
was already there, and building it again would have moved nothing.

What the same counters price is **one pivot**: 21,686 ms / 15,375 pivots =
**1.41 ms**, over a 350 × 425 dense tableau of exact rationals.
`_count_by_k.i_3_3_2.bpl_7` read 5.5 pivots per check at 3.39 ms each.

## 2. What was actually wrong, and the two changes

### 2.1 The pivot paid its `O(rows × columns)` cost twice

`Tableau::pivot_and_update` rewrote the rows (inherently `O(rows × columns)` for
a dense tableau) and then **recomputed every basic variable's value from its
row** — a second `O(rows × columns)` pass, in `ℚ(δ)`, so two rationals per cell,
making it the more expensive of the two halves. Dutertre–de Moura's
`pivotAndUpdate` derives those values in `O(rows)`: the entering variable moves
by `θ = (target − β(leave)) / a_re` and every other basic variable moves by
`a_{i,enter} · θ`, with `a_{i,enter}` read from the column *before* the
elimination zeroes it. The pivot-row rewrite and the elimination also now skip
zero cells.

`tableau_invariant_holds_after_every_pivot` steps the loop one pivot at a time
(`budget = 1`) over 300 random systems and asserts
`β(basic[i]) = Σ row[i][v]·β(v)` between every pair of pivots, with a floor on
pivots exercised so it cannot pass vacuously.

### 2.2 Implied bounds were computed for one-variable atoms only

`propagate_bounds` asked `unit_bound` for a bound, and `unit_bound` returned
`None` unless the constraint named exactly **one** variable. Most LRA atoms name
several, so the cheap check said nothing at all about them: 79 propagations
offered across 6,571 final checks on `blending/1`.

`assign_forms` now gives every constraint template the canonical **linear form**
it bounds — divide through by the coefficient of the lowest-indexed variable, so
the functional has leading coefficient 1 and the constraint becomes a bound on
it (direction kept for a positive leading coefficient, flipped for a negative
one). Two constraints share a form id exactly when they bound the same
functional up to positive scaling. `bound_lower`/`bound_upper` are indexed by
form instead of by variable, and a single variable is just the form with one
coefficient, so nothing that propagated before stops.

Soundness does not depend on what the form is: from `f ≤ u` and `u ≤ b` follows
`f ≤ b`, so an entailed literal's reason is the one asserted atom holding the
bound; and `f ≥ l` with `f ≤ u`, `l > u` is infeasible on those two literals
alone, which is the conflict `assert` now catches for a multi-variable atom with
no simplex run. `MAX_BOUND_PROPAGATIONS_PER_CALL = 256` bounds a call and costs
no completeness by construction — the driver runs propagation to a fixpoint and
every literal a call emits is assigned before the next iteration, so a capped
call resumes rather than discards.

**What was NOT built, and why.** The brief named a specific derivation: "a row
whose other variables are at bounds implies a bound on the basic variable". In
*this* encoding that derivation is structurally weak, and the counters say why:
bounds live only on the slack variables, one per atom, while every problem
variable `xⱼ` is unbounded. At the pristine basis every slack is basic and every
nonbasic column is an unbounded problem variable, so no row implies a finite
bound on anything. The form-indexed check above is the derivation that pays in
this encoding — two atoms bounding the same functional are two tableau rows with
identical coefficient vectors, so it *is* a bound the tableau exposes, detected
structurally instead of by an `O(rows × columns)` scan that would cost a pivot
per call. The general row scan is left unbuilt and this is the reason, not an
omission.

## 3. Result — the criterion micro-benchmark

`cargo bench -p axeyum-solver --features bench-internals --bench simplex_pivot`,
the committed 12-variable / 18-row feasible LP, both arms:

| arm | time (criterion 95% CI) |
|---|---|
| BEFORE | 206.48 µs — **207.30 µs** — 208.49 µs |
| AFTER | 43.359 µs — **46.252 µs** — 49.703 µs |

**4.5x**, with non-overlapping intervals.

## 4. Result — the five traced files, both arms

`smtcomp_cli --trace`, interleaved, load 11–23. `ms/call` is
`theory_final_check_ms / final_checks`. The BEFORE binary predates
`engine_counters`, so its `simplex_*` columns do not exist — recorded as `n/a`,
never as a measured zero.

| file | arm | final_check ms | final_checks | **ms/call** | decisions | theory_props | pivots | pivots/check |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `_count_by_k.i_3_3_2.bpl_7` | before | 17,518 | 880 | 19.91 | 143,943 | 926 | n/a | n/a |
| | after | 17,677 | 611 | **28.93** | 97,314 | 7,315 | 44,655 | 73.1 |
| `_standard_two_index_06.i_3_2_2.bpl_7` | before | 20,454 | 834 | 24.53 | 153,258 | 83 | n/a | n/a |
| | after | 19,541 | 857 | **22.80** | 144,811 | 15,354 | 67,180 | 78.4 |
| `blending/1` | before | 21,615 | 6,798 | 3.18 | 15,698 | 79 | n/a | n/a |
| | after | 13,659 | 17,016 | **0.80** | 36,788 | 79 | 38,688 | 2.27 |
| `blending/5` | before | 20,517 | 5,125 | 4.00 | 19,757 | 3,850 | n/a | n/a |
| | after | 11,895 | 18,410 | **0.65** | 55,178 | 8,181 | 29,911 | 1.62 |
| `p-driverlogNumeric_s7` | before | 968 | 75 | 12.91 | 1,904 | 0 | n/a | n/a |
| | after | 48 | 75 | **0.64** | 1,904 | 0 | 394 | 5.25 |

**`p-driverlogNumeric_s7` is the controlled comparison.** Its `decisions`
(1,904), `final_checks` (75), `theory_conflicts` (180) and `restarts` (2) are
*identical* in both arms — the same search doing the same work — and its
final-check time falls **968 ms → 48 ms, 20x**. Nothing about the search
trajectory can explain that; it is the pivot.

`simplex_cold_restarts = 0` on all five in the AFTER arm.

### The isolated effect of the pivot change

Measured at the intermediate commit `21b5f29f1` (pivot fix only, no propagation
change), standalone runs at load ≈20:

| file | ms/call before | ms/call after pivot fix | ms/pivot before | after | verdict |
|---|---:|---:|---:|---:|---|
| `blending/1` | 3.30 | **0.61** | 1.41 | **0.27** | unknown → **unsat** |
| `_count_by_k.i_3_3_2.bpl_7` | 18.54 | **1.13** | 3.39 | **0.19** | unknown |

## 5. Result — the 33-file population

| arm | decided | undecided |
|---|---:|---:|
| BEFORE | 4 / 33 | 29 |
| AFTER | **5 / 33** | 28 |

One conversion: `2019-ezsmt/blending/5.smt2`, unknown 24,156 ms → **unsat
21,343 ms**. Speedups on already-decided files: `p-driverlogNumeric_s7`
1,217 → 616 ms, `clocksynchro_2clocks` 12,767 → 10,747 ms, `fs_not_sc_seen`
18,572 → 17,684 ms. One already-decided file got slower and stayed decided:
`p5-driverlogNumeric_s9` 13,134 → 18,241 ms.

**No P0.** Not one verdict in either arm contradicts the population's `declared`
column.

**Two honesty notes on this table.**

1. The BEFORE arm reads **4**, not the **5** ADR-1701's slice-1 note recorded
   for the same population. The difference is `spider_benchmarks/frame_prop.base.smt2`,
   which that note measured at 16,532 ms and this run times out in both arms at
   ~24.5 s. That is load, not a regression between the two commits — nothing
   between `188dddf99` and `0076811ff` touched this route. So the exit
   criterion's "rises from 5" is scored here as **+1 on a same-protocol
   before/after pair**, which is what a before/after arm is for, rather than
   against a number measured on a different day at a different load.
2. `blending/1` decided **unsat** in a standalone run at load ≈20 (§4's
   intermediate measurement, and again in the AFTER trace it timed out) and
   `unknown` in the interleaved population run at load ≈24. It is a boundary
   file. Counting it would make the AFTER arm 6; it is **not** counted.

## 6. The exit criterion is not met as written, and the reason is structural

The criterion was: *per-call final-check time and call count both fall on the
five; LRA population decided rises*. Measured:

- **Per-call final-check time falls on 4 of 5** — 4.0x on `blending/1`, 6.2x on
  `blending/5`, 20x on `p-driverlogNumeric_s7`, 1.08x on
  `_standard_two_index_06` — and **rises 1.45x on `_count_by_k`**.
- **Call count falls on 1 of 5** (`_count_by_k`, 880 → 611), is flat on one
  (`p-driverlogNumeric_s7`, 75 → 75), and **rises on three**, sharply on the two
  blending files (6,798 → 17,016 and 5,125 → 18,410).

The conjunction is self-defeating on a fixed wall-clock budget, and this is
worth stating rather than reporting around. `final_checks` is not a fixed amount
of work the search has to get through; it is **how many total Boolean
assignments the search reached in 24 seconds**. Make each final check 4x cheaper
and the search reaches more of them, so the count goes *up* — on `blending/5`,
2.8x more decisions and 3.6x more final checks in the same budget, and that
extra throughput is exactly what converted the file to `unsat`. A falling call
count at a fixed budget would mean the search got *slower* per assignment.

The call count can only fall the way the criterion intends if propagation prunes
assignments faster than the cheaper check adds them. That is visible on
`_count_by_k`: propagations 926 → 7,315 and final checks 880 → 611, a 31% cut.
But on that file it did not pay — the extra propagated literals put more live
constraints into each check (73 pivots per check against 5.5 before), the
per-call time rose 1.45x, and `theory_final_check_ms` came out flat at
17,518 → 17,677. **The propagation change is not uniformly a win**, and this
file is the counter-example, recorded rather than dropped.

## 7. Mutation control

To show the warm start is load-bearing rather than incidental, `Incremental::check`
was mutated to reset to the pristine basis on **every** call (a rebuild per
check) and one traced file re-run. Result in §7 of the lane status file; the
mutation was restored and the tests re-run green.

A second, tighter mutation control covers the pivot change itself: deleting the
`O(rows)` value-update loop makes
`tableau_invariant_holds_after_every_pivot` fail at `seed 0 … after pivot 0`.
The test is not vacuous.

## 8. What this does and does not establish

**Establishes.** The plan's stated QF_LRA mechanism was wrong, and a counter —
not a code reading — is what established it (`simplex_cold_restarts = 0` across
7,488 checks on two files). The real cost was one pivot, and removing the
redundant `O(rows × columns)` value pass is worth 4.5x on the committed
micro-benchmark and 20x on a traced file whose search trajectory is
byte-identical between arms. One population conversion, zero verdict
disagreements across 66 runs.

**Does not establish.** A corpus-wide QF_LRA count (this is 33 files, not the
200-file parity list; `scripts/parity-run.sh QF_LRA` on an idle host is the
next step and did not run here). Anything about QF_UFLIA — its loss list did not
exist. That the form-indexed propagation is a net win: it is measurably a
*loss* on `_count_by_k` and inert on `blending/1`, and the two files where it
fires hardest are also the two where the pivot fix dominates, so the two changes
are not separated on the population. That the 24 s budget is the right frame —
several of these files fail by 5–10% of it under load.
