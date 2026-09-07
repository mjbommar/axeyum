# Per-division timing profile: where the budget goes on the files we lose

Lane `bench-divisions`, 2026-09-07. Running diary. Read
[`docs/plan/families/README.md`](../../plan/families/README.md) for what the
twelve divisions are; the ledger at
[`bench-results/PARITY.md`](../../../bench-results/PARITY.md) is authoritative
for current ratios.

## The question

Nobody has answered per-division: when we lose a file, where does the 24
seconds actually go? Not which route declined — which *stage*, and in what
proportion, across a division rather than a handful of traced files.

## Instruments

- `smtcomp_cli --trace` (`AXEYUM_TRACE=1`) is the real front door
  (`solve_smtlib`). When a generic CDCL(T) route decided (or a watchdog fired
  mid-search), it prints one `; theory-layer …` line with duration fields:
  `boolean_propagate_ms`, `theory_assert_ms`, `theory_propagate_ms`,
  `theory_push_pop_ms`, `conflict_analysis_ms`, `theory_final_check_ms`,
  `theory_explain_ms`, plus counters. These are **per-stage accumulators**,
  not readings from one shared clock — `stats.boolean_propagate.as_millis()`
  etc. are independent `Duration` totals accumulated at their own call sites
  in `crates/axeyum-solver/src/cdclt.rs`, not deltas off one `t0`.
  **Correction, found during the sweep (see "Methodology correction"
  below): they are still not safe to sum blindly** — `theory_assert_ms` is
  *nested inside* `boolean_propagate_ms` for a portion of its total, so the
  two are not disjoint stages. Read that section before trusting any sum in
  this file.
- `explain_corpus --json --timed-trace` is diagnostic only (its own banner
  says so, and it disagrees with the front door on 134/397 benchmarks per the
  2026-09-05 loss census correction). Not used to classify anything here; not
  used at all in the first pass.
- No instrument in this tree exposes parse time, rewrite/preprocessing time,
  bit-blast/CNF-encode time (`BvLayerStats` exists in
  `crates/axeyum-solver/src/layers.rs` but is not wired to any CLI flag), or
  model-replay time. Expect a real, possibly large, untraced remainder — and
  say so per-division rather than paper over it.

## Population and selection rule

Reused, not rebuilt: the 2026-09-05 loss census
(`bench-results/parity-losses-20260905/<DIV>.txt`, `bench-results/parity-losses-20260906/QF_NRA.txt`)
already lists, per division, the reference-only files (axeyum `unsolved`,
reference `sat`/`unsat`) from a clean sweep at a pinned commit. Its `class`/
`last_route` columns are **refuted** (67/70 wrong across two divisions,
per that dataset's own README) — never used here. The **file list itself**
is stated as unaffected and is what this lane samples from.

**Selection rule (deterministic, reproducible):** the first `min(8, N)` lines
of the committed `<DIV>.txt`, in file order, where `N` is the list length.
No shuffling, no cherry-picking after seeing results. Anyone can reproduce a
division's sample by taking `head -n 8` of the same committed file.

**Protocol:** identical to `scripts/parity-run.sh` — 24s wall budget, 8 GiB
`ulimit -v`, one run per file, `AXEYUM_TRACE=1` added (trace collection is
documented as adding negligible overhead; it is off by default only because
any clock read must never silently move a scored parity baseline — this run
is not a scored baseline).

## Build

`d51d4ef04878b40f5d00a1a6b4aed405b35cae4e` (local `main` == `origin/main` at
lane start). Built on **s7** (16 cores, idle, `/proc/loadavg` ~1.0 at start)
in a throwaway clone at `/home/mjbommar/bench-divisions/repo`, branch
`bench-divisions-work`, via `cargo build --release -p axeyum-bench --example
smtcomp_cli` (no `--features full` — that flag does not exist on
`axeyum-bench` and errors; confirmed by trying it first). Binary:
`target/release/examples/smtcomp_cli`, 42 MB, built in 1m52s.

## First finding, before the sweep even finished one division

QF_IDL's own division file
(`docs/plan/families/smt-quantifier-free/qf-idl.md`) says the census's
`dominant_stage` for its timeout population is `dl-online` — a **dedicated
difference-logic route**, not the generic CDCL(T) driver `--trace`
instruments. Smoke-tested directly: neither an unsolved (timeout, 24021 ms
wall) nor a solved (`sat`, 1110 ms wall) QF_IDL loss-census file printed
*any* `; theory-layer` line — not even the `unavailable:` fallback, which
only fires when the watchdog interrupts a spawned CDCL(T) worker. So for a
route that never enters the generic driver at all, `--trace`'s coverage is
not "small", it is **zero** — the whole wall clock for that file is
untraced by this instrument. That is itself the finding for QF_IDL, and it
means the primary instrument this lane was pointed at is blind on whichever
divisions route through a specialized (non-CDCL(T)) engine. Confirmed the
instrument does work on other divisions first (QF_NIA: three smoke files, one
printed a real `theory_propagate_ms=705` of ~24000ms wall, one printed
`unavailable: watchdog fired...`, one printed `theory_propagate_ms=6553`) —
so this is a per-route property, not a broken build.

## Sweep

Ran on s7 (`/home/mjbommar/bench-divisions/sweep.sh`, sequential across all 12
divisions, in loss-census order QF_ABV → QF_BV → QF_IDL → QF_LIA → QF_LRA →
QF_NIA → QF_RDL → QF_SLIA → QF_UF → QF_UFLIA → UF → QF_NRA).
`/proc/loadavg` recorded before/after each division:
start `0.98 1.45 0.84` (16 cores, s7 otherwise idle), end `1.06 1.08 1.02` —
the host stayed idle for the whole ~24-minute run (11:06:50 → 11:30:34
local), so nothing here is contention-taxed. Raw per-file TSVs
(`division\tfile\twall_ms\tverdict\ttrace_line`) are committed at
`bench-results/bench-divisions-2026-09-07/<DIV>.tsv`; the aggregation script
is `bench-results/bench-divisions-2026-09-07/scripts/aggregate.py`, its
output `aggregate.json`, and a rendered table `report.md`.

## Methodology correction: `theory_assert_ms` double-counts inside `boolean_propagate_ms`

The first aggregation pass summed all seven `; theory-layer` duration fields
per file and divided by wall clock. **QF_UF came back at 130.7% traced** —
proof the sum was wrong, since a stage breakdown cannot exceed the wall it
was measured inside. Isolated to one file first:
`QF_UF_rushhour.3.prop1_ab_cti_max.smt2`, wall 24224 ms,
`boolean_propagate_ms=17655` **plus** `theory_assert_ms=18630` alone already
sums to 36285 ms — 12 seconds over the wall clock for that one file, before
adding anything else.

Traced to source: `crates/axeyum-solver/src/cdclt.rs`, `assign()` (~line
993) times `theory.assert()` into `self.time_theory_assert`. `assign()` is
called from inside `unit_propagate()` (~line 1102) while walking the trail —
and `propagate()` (~lines 2005-2010) wraps the *entire* `unit_propagate()`
call in `self.time_boolean_propagate`. So every `theory_assert_ms`
millisecond spent while `assign()` runs during unit propagation is counted
twice: once in `theory_assert_ms`, again inside the enclosing
`boolean_propagate_ms`. (`assign()` is *also* called from
`theory_propagate()`'s queue-drain, a sibling call not nested under
`boolean_propagate_ms` — so the double-count is partial, not total, and
cannot be subtracted exactly without further instrumentation than this lane
built.)

**Fix applied:** report two numbers, never one. `boolean_search_ms` stays
gross (`boolean_propagate_ms + conflict_analysis_ms`, since it already
subsumes whatever assert time happened during propagation). `theory work` is
reported **conservatively**, excluding `theory_assert_ms`
(`theory_propagate_ms + theory_push_pop_ms + theory_final_check_ms +
theory_explain_ms`) so the two buckets are non-overlapping to the best of
what the source proves. `theory_assert_ms` is reported separately, folded
into neither bucket, flagged `_excluded_overlap` in the JSON. The naive
(double-counting) sum is *also* kept in the JSON as
`naive_traced_total_ms_DO_NOT_TRUST` so the QF_UF anomaly stays visible
rather than silently disappearing when the fix landed — anyone re-deriving
this from `aggregate.json` sees both. This is the same class of hazard named
in this lane's brief for the quantified ladder (timings that look additive
but are not); here it is nested instrumentation rather than one shared
clock, and it was caught the same way: by summing and finding the total
exceeds a known ceiling.

## Results

Deterministic 8-file-or-fewer sample per division (all of QF_BV's 6 losses,
all of QF_SLIA's 7; `min(8, N)` elsewhere), 24 s / 8 GiB protocol,
`AXEYUM_TRACE=1`. 93 files total, 1422.8 s of wall clock. **Traced total:
222.3 s — 15.6% of the sampled wall clock, across all 12 divisions
combined.** The other 84.4% is untraced by any instrument in this tree.

| Division | Files | Total wall | theory-layer present | watchdog-unavailable | no line at all | Boolean search (gross) | Theory work (conservative) | Traced total | Untraced | Traced % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_ABV | 8 | 170.7s | 0 | 4 | 4 | 0.00s | 0.00s | 0.00s | 170.7s | 0.0% |
| QF_BV | 6 | 147.6s | 0 | 1 | 5 | 0.00s | 0.00s | 0.00s | 147.6s | 0.0% |
| QF_IDL | 8 | 65.3s | 0 | 0 | 8 | 0.00s | 0.00s | 0.00s | 65.3s | 0.0% |
| QF_LIA | 8 | 161.2s | 2 | 4 | 2 | 10.03s | 7.76s | 17.79s | 143.4s | 11.0% |
| QF_LRA | 8 | 143.6s | 6 | 0 | 2 | 0.87s | 101.53s | 102.41s | 41.2s | 71.3% |
| QF_NIA | 8 | 156.6s | 5 | 3 | 0 | 0.62s | 20.79s | 21.40s | 135.2s | 13.7% |
| QF_NRA | 8 | 81.6s | 5 | 3 | 0 | 0.00s | 0.07s | 0.08s | 81.5s | 0.1% |
| QF_RDL | 8 | 147.9s | 0 | 3 | 5 | 0.00s | 0.00s | 0.00s | 147.9s | 0.0% |
| QF_SLIA | 7 | 64.5s | 3 | 2 | 2 | 0.01s | 0.08s | 0.08s | 64.4s | 0.1% |
| QF_UF | 8 | 87.5s | 8 | 0 | 0 | 41.79s | 18.80s | 60.59s | 26.9s | 69.2% |
| QF_UFLIA | 8 | 55.6s | 0 | 0 | 8 | 0.00s | 0.00s | 0.00s | 55.6s | 0.0% |
| UF | 8 | 140.6s | 6 | 1 | 1 | 2.53s | 17.42s | 19.95s | 120.7s | 14.2% |

`theory-layer present` / `watchdog-unavailable` / `no line at all` are file
counts (columns sum to the division's file count): `present` means a real
stage line printed, `watchdog-unavailable` means the `--trace` watchdog
fired but the worker thread's snapshot was unreachable (still zero traced
ms for that file, but it at least confirms a CDCL(T) worker was spawned),
`no line at all` means the process printed no `; theory-layer` line of
either kind — the route never entered the instrumented driver.

### Five of twelve divisions are **zero-coverage** for this instrument

QF_ABV, QF_BV, QF_IDL, QF_RDL, QF_UFLIA never print a real stage line on
any sampled file. Cross-checked against each division's own cause doc,
and each has an independent, already-documented reason the generic
CDCL(T) `--trace` driver was never going to see it:

- **QF_IDL**: `docs/plan/families/smt-quantifier-free/qf-idl.md` names
  `dl-online` as the dominant route — a dedicated difference-logic engine,
  not the generic driver. Confirmed directly (see "First finding" above):
  0 of 2 smoke-tested files printed any line, not even
  `watchdog-unavailable`.
- **QF_BV**: `qf-bv.md` says the cause is "measured at the SAT level...on
  identical CNF" — the `sat-bv` bit-blast-to-CNF route, which has its own
  stage stats (`BvLayerStats` in `crates/axeyum-solver/src/layers.rs`:
  `bit_blast`, `cnf_encode`, `solve`, `model_lift`, and ~50 more counters)
  but **no CLI flag exposes them** — confirmed by reading
  `crates/axeyum-bench/examples/smtcomp_cli.rs`'s `parse_cli_args`: only
  `--timeout-ms`, `--evidence`, `--progress`, `--trace` exist, nothing
  reaches `BvLayerStats`.
  QF_ABV is QF_BV plus array elimination ahead of the same bit-blast route
  (`eliminate_arrays`, ADR-0010), so the same gap applies, and its own
  `watchdog-unavailable` count (4/8) shows a worker DID spawn on some
  files — just never one whose engine touches `cdclt.rs`'s timers.
- **QF_RDL**: real difference logic, same `dl-online` engine as QF_IDL by
  construction (both are difference-logic fragments) — not independently
  re-derived here, but consistent with QF_IDL's confirmed zero.
- **QF_UFLIA**: 8/8 files print *nothing at all* (not even
  `watchdog-unavailable`), and most resolve fast (109-3710 ms, well under
  the 24 s budget) rather than timing out — this population is not a
  CDCL(T) search cost at all, it is dispatch/admission-decline before any
  worker spawns. Matches `qf-uflia.md`'s own open question ("instrument,
  then S7" — 21 of 58 unexplained) from the other direction: the
  generic-driver instrument this lane used cannot see this population
  either, so a real answer needs a dispatch-level trace, not a theory-layer
  one.

### The three divisions with the highest traced coverage

- **QF_LRA (71.3%)**: dominated by `theory_final_check_ms` (56.96 s) and
  `theory_propagate_ms` (44.24 s) summed across the 8-file sample —
  simplex feasibility work, consistent in direction with `qf-lra.md`'s
  established cause ("final check into feasibility into simplex was 84% of
  wall" on its own, larger, census population). This lane's 71.3% is a
  different, smaller population (8 files, deterministic-first vs. that
  census's 54) — not a replacement measurement, a corroboration from a
  different instrument angle.
- **QF_UF (69.2%)**: `boolean_propagate_ms` (41.5 s gross, includes nested
  assert time) plus `theory_propagate_ms` (17.2 s) plus `theory_push_pop_ms`
  (1.6 s). The excluded `theory_assert_ms` (53.8 s, *larger* than the gross
  boolean-propagate bucket that contains part of it) is congruence-closure
  assert cost — direction matches `qf-uf.md`'s established cause
  ("`euf-online` is entered first and spends 23.5 s of a 24 s budget").
- **UF (14.2%), QF_NIA (13.7%), QF_LIA (11.0%)**: real but minority
  coverage — `theory_propagate_ms` is the largest single field in all
  three (17.4 s / 20.8 s / 7.8 s respectively), consistent with a
  propagation-heavy theory loop, but the majority of each division's
  sampled wall clock is still outside this instrument's reach.

### What is untraced everywhere, by construction

No instrument reachable from this lane's brief exposes, for **any**
division: SMT-LIB parse time, rewrite/preprocessing time,
admission-decline/dispatch-probe time (the time spent trying and declining
routes *before* the one that runs to the deadline — `explain_corpus
--json --timed-trace` sees this but is diagnostic-only and was not used
here), or model-replay time. For QF_BV/QF_ABV specifically, bit-blast and
CNF-encode time is measured internally (`BvLayerStats`) but not exposed by
any CLI this lane found. **84.4% of the sampled wall clock across all 12
divisions is unaccounted for by any stage this lane could read.** That
remainder is this lane's headline finding, not a footnote: on 7 of 12
divisions (everything except QF_LRA and QF_UF) it is the overwhelming
majority of the budget, and on 5 of 12 it is the *entire* budget.

## What this lane did not measure

- Did not build or wire a dispatch-level (`RouteTrace` / `explain_corpus
  --json --timed-trace`) breakdown for the zero-coverage divisions, even
  diagnostically — ran out of scope at the 5-minute-per-division budget
  target. That is the concrete next step for QF_ABV/QF_BV/QF_IDL/QF_RDL/
  QF_UFLIA: none of them can get a real stage breakdown from `--trace`
  alone, ever, because their dominant routes do not run the instrumented
  driver.
- Did not wire `BvLayerStats` to any CLI flag, so QF_BV/QF_ABV's
  bit-blast/CNF-encode/SAT-solve/model-lift split (which the underlying
  code already measures) stays invisible from the front door. A follow-on
  slice could add a `--bv-stats` flag to `smtcomp_cli` mirroring `--trace`.
- Did not measure parse time, rewrite time, or model-replay time
  separately for any division — no instrument in this tree isolates them
  from the front door today.
- Did not re-run any division at a larger sample size; 8-or-fewer files is
  what fits the 5-minutes-per-division target, not a claim that it is
  representative of each division's full loss population (33-401 files).

