# Instrument coverage: exposing what already exists and timing what nothing measured

Lane `instrument-coverage`, 2026-09-07. Running diary. Read
[`docs/research/12-performance/bench-divisions-2026-09-07.md`](bench-divisions-2026-09-07.md)
first — this lane exists because that one measured only 15.6% of sampled wall
clock as traced by `smtcomp_cli --trace`, with five of twelve divisions at
**0.0%** coverage, and named the concrete follow-ons this lane executes.

## The question

Not "why is a query slow" (that is every other performance lane's job) but
"can we even SEE where the time goes, on the divisions where today the answer
is no instrument at all." This lane adds no capability and decides no query
differently; its product is visibility.

## Baseline (before)

From `bench-results/bench-divisions-2026-09-07/aggregate.json` /
`report.md`, at commit `d51d4ef04878b40f5d00a1a6b4aed405b35cae4e`: **15.6%**
traced (222.3 s of 1422.8 s sampled wall clock, 93 files across 12
divisions). Zero-coverage divisions: QF_ABV, QF_BV, QF_IDL, QF_RDL,
QF_UFLIA.

## What was already there but not wired up

`crates/axeyum-solver/src/layers.rs`'s `BvLayerStats` already lifts the
`sat-bv` (bit-blast) backend's own internal `Instant` timings
(`bit_blast_ms`, `cnf_encode_ms`, `inprocess_ms`, `solve`, `model_lift`) out
of the untyped `SolveStats::backend` counter list — and those timings are
computed **unconditionally** by `SatBvBackend::check_with_replay_internal`
regardless of any flag (confirmed by reading `crates/axeyum-solver/src/
sat_bv_backend.rs`: every `Instant::now()` around bit-blast/CNF-encode/solve
runs on every check, flag or no flag). Nothing published it anywhere a CLI
could read it — `crates/axeyum-bench/examples/smtcomp_cli.rs`'s
`parse_cli_args` only ever wired `--timeout-ms` / `--evidence` / `--progress`
/ `--trace`, confirmed by reading it before touching it. This is the
"cheapest coverage available" item named in the brief: the data already
exists, only the publish path was missing.

## A methodology bug found while wiring it: `model_lift` already double-counted

While adding the publish path, read `sat_bv_backend.rs`'s `handle_sat_result`
closely enough to time it precisely, and found the SAME class of bug
`bench-divisions-2026-09-07` found in `theory_assert_ms`: `stats.model_lift`
was stamped from an `Instant` taken BEFORE `replay_model(...)` was called,
but the assignment `stats.model_lift = lift_start.elapsed()` ran AFTER
`replay_model` returned successfully. So the field documented as "time
lifting a satisfying assignment into an Axeyum model" silently included the
soundness-gate replay-check cost too. Split into two separately-timed
sub-stages (`model_lift`, `model_replay`) at the same call site — see
`crates/axeyum-solver/src/sat_bv_backend.rs`'s `handle_sat_result` and its
comment. This is a pure additional-measurement change: neither sub-timing
existed as an externally-observable API before (no CLI flag read
`BvLayerStats` at all), so no caller's behavior changes, and the returned
`CheckResult` is byte-identical (verified: the split only adds a second
`Instant::now()`/`.elapsed()` pair and a `push_duration_ms` call between two
statements that already ran in the same order).

## Instruments added, and what each nests inside

Every new instrument follows the SAME shape already established by
`crate::cdclt::TheoryLayerStatsGuard` / `crate::cdclt::last_theory_layer_stats`:
a thread-local `Cell<bool>` collection flag (default `false`), a thread-local
accumulator, a `*Guard::enable()` RAII type that flips the flag and resets
the accumulator, restoring the previous flag on `Drop`, and a `last_*`
reader function. Off by default costs **zero** extra clock reads: every call
site gates the `Instant::now()` itself behind the collection flag
(`flag.then(Instant::now)`), not just the recording step — confirmed by
reading each call site below, not merely by writing the type.

1. **`BvLayerStatsGuard` / `last_bv_layer_stats()`**
   (`crates/axeyum-solver/src/layers.rs`). Publishes at the single funnel
   point every `SatBvBackend::new()` construction eventually reaches:
   `SolverBackend::check` / `check_query` in
   `crates/axeyum-solver/src/sat_bv_backend.rs`. **Not gated on a new clock
   read** — the underlying `SolveStats` durations are already computed
   unconditionally (see above), so the guard only gates the
   `Option<BvLayerStats>` clone into the thread-local. Covers **QF_BV**
   directly and **QF_ABV** through `abv.rs`'s `eliminate_arrays` reduction,
   which dispatches the reduced query to `SatBvBackend` the same way.
   `BvLayerStats::total()` is documented (and now doubly so, given the
   `model_lift` finding above) to sum only the six top-level stage fields,
   never `bit_demand_analysis` / `range_demand_admission`, which are nested
   inside `bit_blast` (measured during the same lowering call `bit_blast`
   wraps) — the same non-double-counting discipline
   `bench-divisions-2026-09-07` established for `theory_assert_ms`.

2. **`FrontDoorStatsGuard` / `last_front_door_stats()`**
   (`crates/axeyum-solver/src/smtlib.rs`). Times the single call site of
   `axeyum_smtlib::parse_script_with_string_bound_within` inside
   `solve_smtlib_at_string_bound` — **universal**: every division's front
   door reaches this exact call, at least once (accumulated across
   string-bound-ladder rungs when a query re-parses at a wider window).
   Timed around the whole `match`, not just the `Ok` arm, so an
   ingest-deadline decline is still charged its real parse cost.
   **Sequential with, never nested inside, any other instrument** — parsing
   finishes before dispatch begins.

3. **`DlOnlineStatsGuard` / `last_dl_online_stats()`**
   (`crates/axeyum-solver/src/dl_online.rs`). Times the whole
   `try_check_qf_dl` call from its single call site,
   `crate::auto::dispatch_difference_logic` — deliberately NOT instrumented
   inside `dl_online.rs` itself, because that function has several internal
   early-return paths (a `?` on `scan_dl`, multiple budget-exhausted
   `Some(timeout_result(..))` returns) and timing at the one call site
   covers all of them without touching any. Coarser than the other three by
   design: reports only total wall time inside the whole probe, not an
   internal stage breakdown — "enough to say where a query's wall clock
   went," per the brief, not a full stage instrument for `dl-online`
   internals (that would be a follow-on, not this slice). Returns
   `(Duration, u64)` — a call count alongside the duration — because
   `dispatch_difference_logic` is NOT reached by every query (e.g. `QF_BV`
   never enters the linear-arithmetic dispatch chain at all), and a bare
   accumulated `Duration` cannot distinguish "ran, cost near-zero" from
   "never ran" when both round to the same small number; `smtcomp_cli` only
   prints the `; dl-online …` line when the count is nonzero. Covers
   **QF_IDL** and **QF_RDL** directly: their dominant route
   IS `dl-online`, confirmed by the original `bench-divisions-2026-09-07`
   "First finding" (0 of 2 smoke-tested QF_IDL files printed any
   `; theory-layer` line, not even `unavailable:`) — this line is now their
   PRIMARY stage instrument, not a supplement.

All four are wired to the SAME `--trace` / `AXEYUM_TRACE=1` flag in
`smtcomp_cli.rs` (no new CLI surface), each printing its own `;`-prefixed
line (never matching `^(sat|unsat)$` / `^unknown$`) when applicable — see
that file's module header for the exact line formats. The `solve()` closure's
return type changed from `(&'static str, Option<String>, Option<String>)` to
`(&'static str, Option<String>, Vec<String>)` to carry an arbitrary number of
trace lines; both call sites (no-timeout and watchdog-timeout) and both
existing unit tests were updated to match, and both still pass.

## Non-additivity guard

`bench-results/instrument-coverage-2026-09-07/scripts/aggregate.py` sums,
per file: `front_door_ms + dl_online_ms + bv_layer_ms + theory_layer_ms`
(`bv_layer_ms` and `theory_layer_ms` each already using their own
non-double-counting decomposition — `BvLayerStats::total()`'s six fields,
and the original `bench-divisions-2026-09-07/scripts/aggregate.py`'s
boolean-search-gross-plus-theory-work-conservative split, ported verbatim).
These four are non-overlapping by construction (parse precedes dispatch;
dl-online is a probe that returns before the decisive route starts; bv-layer
and theory-layer are mutually exclusive per query), but the script does not
trust that claim silently: it asserts, for every file, `traced_ms <=
wall_ms * 1.15` (a small slop for harness-vs-binary clock skew, not
double-counting) and **exits 1** if any file violates it, printing which
file and by how much. `bench-results/instrument-coverage-2026-09-07/scripts/
test_aggregate_guard.py` mutation-checks this guard directly: a synthetic
fixture with an honest `; bv-layer … total_ms=5302` against a 24000 ms wall
must PASS, and the same line against a 1000 ms wall (total_ms exceeds
wall_ms) must FAIL with the guard's own message — confirmed both ways before
trusting the guard on real data (evidence-and-checker-discipline: "make the
exit status depend on the finding").

## Verdict-invariance and zero-cost-when-off checks

- Every new call site gates its `Instant::now()` behind the collection flag,
  never behind a branch that also affects control flow — confirmed by
  reading each site (listed above), not by convention alone.
- `crates/axeyum-bench/examples/smtcomp_cli.rs`'s two existing `--trace`
  regression tests (`watchdog_unavailable_line_is_empty_off_trace_and_one_line_on_trace`,
  `a_worker_that_outlives_the_deadline_still_yields_a_theory_layer_line`,
  renamed/updated for the `Vec<String>` return type) still pass.
- Smoke-tested directly (not just unit-tested): `--trace` off vs. on for the
  same file prints the SAME verdict (`sat` for a trivial `QF_BV` query,
  `unknown` for a real `QF_BV` timeout, `unknown` for a real `QF_IDL`
  timeout) — the trace lines are additional stdout lines before the verdict,
  never a changed verdict.

## Re-run: coverage after

<!-- filled in after the sweep -->

## What remains untraced, and why

- **Rewrite/preprocessing time** (`canonicalize_terms` /
  `propagate_values` / `solve_eqs_bounded` / `elim_unconstrained`) is called
  from at least 7 distinct sites across `auto.rs`, `preprocess.rs`,
  `incremental.rs`, and `quant_bool_model_sat.rs`, each with its own
  fixpoint loop and its own dispatch context — there is no single funnel
  point the way `parse_script_with_string_bound_within` and
  `try_check_qf_dl` are. `crates/axeyum-solver/src/preprocess.rs`'s
  `check_with_preprocessing` IS such a funnel, but it is only reached from
  `abv.rs` (the QF_ABV local-search path) — not the general dispatch most
  divisions use. Instrumenting this honestly (not just at one convenient
  site that happens to compile) is a follow-on slice, not done here.
- **Generic (non-`sat-bv`) model replay** — every non-BV route that produces
  a `sat` model does its own replay check at its own call site (`auto.rs`,
  `euf.rs`, `evidence.rs`, `uf_fmf.rs`, …); only the `sat-bv` route's replay
  (item 1 above) was split out and timed, because that route's replay is a
  single funnel and directly served the two zero-coverage divisions this
  lane's priority-1 item targets. Did not attempt to instrument the other
  replay call sites.
- **Dispatch-decline** (the QF_UFLIA class: 8/8 sampled files printed no
  `; theory-layer` line at all in the original sweep, and mostly resolve
  fast rather than time out — `bench-divisions-2026-09-07` attributes this
  to dispatch/admission-decline before any worker spawns). The existing
  `crate::route_trace::RouteTrace` instrument records exactly this (which
  routes were tried, with per-attempt timing), but it is reached only
  through `check_auto_explained`, a SEPARATE function from the one
  `solve_smtlib` actually calls (`check_auto`) — wiring `--trace` to run
  `check_auto_explained` instead would mean running dispatch through a
  different entry point than the shipped front door, which is exactly the
  divergence CLAUDE.md's Gotchas section already warns about
  (`explain_corpus` disagreeing with the shipped front door on 134/397
  benchmarks). Did not build this — reported as "did not run," not
  attempted and hidden.
