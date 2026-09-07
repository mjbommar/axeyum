# Lane: s7b-engine-unification — the same instrument on both engines, then the move

<!-- plan-section: lane-status -->

**S7b step 1 landed: the native CDCL core carries the driver-side stage timings
and counters `CdclT` has carried since S1b, opt-in, with the shipping DRAT
stream byte-identical. The `CdclT` instrument was re-measured on the five
profiled QF_IDL files first and reproduces S1b's numbers exactly** (`WIP`,
s7b-engine-unification, 2026-09-07, plan slice S7b).

S7a ([`s7-engine-unification.md`](s7-engine-unification.md)) made the native
core decide under a theory and produce the ADR-1704 artifact. Nothing in the
solver reaches it: every shipping entry point still constructs the search with
`NullTheory`, and `crates/axeyum-solver/src/cdclt.rs` is untouched. S7b is the
slice that changes that, and it is ordered so the measurement exists before the
thing being measured moves.

## Step 1 — the instrument, validated before anything moved

A swap of one CDCL(T) engine for another is only measurable if the **same**
counters report from both sides. So the port came first, and the existing
instrument was re-validated first of all.

### The `CdclT` side reproduces S1b's numbers

Idle s5 (load 0.00 at start), `taskset -c 0-7`, `--timeout-ms 24000`,
`smtcomp_cli --trace`, binary built from a `--touch`-extracted snapshot of
`fcc988900` (`main`). `RVpredict_13` is the file S1b pinned:

| | S1b recorded (`9a0615cfe`) | here (`fcc988900`) |
|---|---:|---:|
| verdict | `sat` | `sat` |
| `decisions` | 2,364,618 | **2,364,618** |
| conflicts / `theory_conflicts` | 3,415 | **3,415** |
| `restarts` | 17 | **17** |

Exact on all four, across the S2, S4 and S7a merges that landed in between. The
instrument is sound and the before-numbers are reproducible, which is the
precondition this slice was gated on.

Full line, for the next lane to diff against:

```
; theory-layer boolean_propagate_ms=471 theory_assert_ms=347 theory_propagate_ms=42
  theory_push_pop_ms=92 conflict_analysis_ms=1 theory_final_check_ms=0 theory_explain_ms=0
  theory_conflicts=3415 theory_propagations=0 final_checks=1 decisions=2364618 restarts=17
  learned_clauses=3415 learned_literals=21485 learned_literals_premin=21486
```

`jobshop20-2-10-10-4-4-16` likewise reproduces its S1b shape — 20,861 ms of
21.0 s inside `theory_propagate`, `decisions=76386`, `theory_conflicts=835` —
i.e. still S4's subject and not this lane's.

One thing that has moved since S1: **all five files now emit a trace line.**
S1 reported three of five printing none in either arm (its Finding 0, the
watchdog dying inside routing); on `fcc988900` every one of the five prints a
full theory-layer line. S2's shared shrinking deadline closed that, and the two
`asp` files it unblocked are the ones where Boolean propagation dominates again
(15,488 ms and 16,642 ms of ~22 s), which is the shape S7b's engine move acts
on.

### The native side now carries the same counters

`axeyum_cnf::NativeLayerStats` is the `axeyum-cnf` half of
`axeyum_solver::layers::TheoryLayerStats`: the fifteen **driver-side** fields,
computed at the same increment sites (`analyze`'s asserting-clause branch, a
theory-attributed conflict, one heap pick, one completed `final_check`, one
theory-assigned literal), with `restarts` derived as `restart_count - 1`
exactly as `CdclT::restarts` derives it.

The theory-side engine counters (`simplex_pivots`, `bound_retractions`, …) are
deliberately **not** ported: they belong to the `TheorySolver` implementation,
not to the driver, and the solver-side adapter will keep filling them from
`TheorySolver::engine_counters`.

Collection is opt-in through `solve_with_theory_and_drat_proof_traced`. With it
off — every other entry point — no stage reads a clock and no counter is
touched, so an unmeasured run is all-zero rather than a partial measurement, and
"the stage cost nothing" can never be confused with "collection was off".

## Measured: the shipping SAT trajectory is byte-identical

`crates/axeyum-cnf/examples/drat_stream_dump.rs` over the three committed DIMACS
files plus the 30 seeded random 3-SAT instances, release build:

| | recorded by S6 and again by S7a | this slice |
|---|---|---|
| DRAT text | 38,333 bytes, `84a620da…` | 38,333 bytes, **`84a620da…`** |

The digest is one two prior lanes wrote down before this change existed, so
matching it is a real check and not a self-comparison. A defect in `analyze` or
`minimize` moves this text while leaving every verdict intact, which is why it
is the observable used rather than a verdict sweep.

## What the tests can fail on

`proof_sat::layer_stats_tests`, 6 tests, over a **Boolean-satisfiable** fixture
refuted only by the theory — so no theory-side counter can be nonzero for an
uninteresting reason, and that premise is its own test.

- `every_driver_side_counter_moves_on_a_theory_search` — each of the eleven
  counters and each of the five timed stages, separately asserted. A counter
  that can never move is an instrument that cannot report a regression in the
  stage it names.
- `an_untraced_solve_reports_the_all_zero_snapshot` — the control, and a live
  one: it first asserts the traced arm is nonzero on the *same* fixture, so an
  instrument that never records anything fails it rather than passing it.
- `a_null_theory_search_moves_only_the_boolean_counters` — the theory half
  vanishes at monomorphization; the Boolean half does not.
- `tracing_changes_neither_the_verdict_nor_the_boolean_stream` — the hooks are
  output-only, checked rather than argued.
- `restarts_reads_zero_on_a_search_that_never_restarted` — the derived counter
  is off by one or it is not; paired with the nonzero assertions so an
  always-zero derivation cannot pass as a measurement.

## What S7b still has to do

Unchanged from S7a's scoping, minus step 1:

2. Thread `theory: &mut T` through `run`/`search_loop` instead of storing it, so
   `HAS_THEORY` still monomorphizes and `CdclT::new`'s signature and its call
   sites stand.
   **Correction to S7a's plan:** the solver-side adapter cannot be a blanket
   `impl<T: TheorySolver> NativeTheory for T`. `NativeTheory` is foreign to
   `axeyum-solver` and the impl covers foreign types, so the orphan rule rejects
   it; it has to be a local newtype (`NativeTheoryAdapter<'_, T>`) doing the
   clause/asserted-literal negation once at the boundary.
3. Dormant variables and the permanent-clause/resume protocol. `CdclT::active`
   maps onto the native core's existing `branchable` and
   `activate_variables` onto `heap_insert`; what the native core has no
   counterpart for is `pending_clauses` (the one full evaluation a clause
   inserted under an assignment needs) and the atom↔variable map.
4. `CdclT` becomes the adapter; measure both scoring populations.

<!-- plan-section: landed-changes -->
