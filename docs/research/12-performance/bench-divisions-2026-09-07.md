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
  etc. are independent `Duration` totals, so summing them is valid (checked
  against `crates/axeyum-bench/examples/smtcomp_cli.rs` lines ~213-250 before
  trusting this).
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

Running on s7 in the background (`/home/mjbommar/bench-divisions/sweep.sh`,
log at `/home/mjbommar/bench-divisions/sweep.log`), sequential across all 12
divisions, `/proc/loadavg` recorded before/after each division. Results land
under `bench-results/bench-divisions-2026-09-07/<DIV>.sample.tsv` (raw,
per-file: division, file, wall_ms, verdict, trace_line) plus one aggregated
JSON stage breakdown. This section is updated once the sweep completes.
