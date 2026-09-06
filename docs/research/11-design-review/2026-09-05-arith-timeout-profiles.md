# Arithmetic timeout profiles: which functions inside the CDCL(T) driver, 2026-09-05

This answers the question the 2026-08-21/2026-09-05 diagnoses left open: the
[2026-09-05 architecture review](2026-09-05-sat-smt-performance-and-architecture-review.md)
and [ADR-1701 slice 1 measurement](2026-09-05-adr-1701-slice-1-measured.md)
established that QF_IDL timeouts spend 18-20 s of 24 in "the CDCL(T) driver's
Boolean propagation and almost nothing in the theory," but named the driver,
not the function. This is a measurement-only lane; it changes no production
Rust.

## Method

**Host/binary.** All runs on s5 (16 cores, idle), pinned `taskset -c 0-7`,
against `~/axeyum-parity-20260905` (commit `9914a1c0e`, "today's main"),
`target/release/examples/smtcomp_cli` (41,090,616 bytes, **not stripped** —
confirmed with `file`, so symbols would have been present had `perf` worked).
`target/release/examples/explain_corpus` was built fresh in the same
worktree/target dir (`cargo build --release -p axeyum-bench --example
explain_corpus`, no source changes, cache-warm build, 1.29 s).

**`perf` was refused.** Confirmed by the coordinator in parallel:
`perf_event_paranoid=4` and no sudo on s5, so `perf record -e cpu-clock -F 999
-g` fails with "Failure to open any events for recording." Step 1(b) did not
run. Everything below is the 1(c) fallback: the binary's own `--trace`
instrumentation (`TheoryLayerStats`, `crates/axeyum-solver/src/layers.rs:440`),
`explain_corpus --json --timed-trace` for the per-route wall-clock split, and
a code-level reading of `crates/axeyum-solver/src/cdclt.rs`. **This is
inference from counters and source, not a sampled profile** — stated plainly
per the task's instruction, and italicized again wherever a conclusion rests
on it below.

**Per-file run.** For each of the 10 files: `taskset -c 0-7 smtcomp_cli
<file> --timeout-ms 24000 --trace` under `/usr/bin/time -v` for wall clock,
budget 24 s (raw output: `bench-results/arith-timeout-profiles-20260905/*.trace.txt`).
Separately, `taskset -c 0-7 explain_corpus --list filelist.txt 24000 --json
--timed-trace` (raw output: `explain_corpus.jsonl`) for the per-route
attempt split. `explain_corpus` is diagnostic-only — its own stderr banner
says it disagrees with the real front door (`solve_smtlib`, what
`smtcomp_cli` runs) on 134 of 397 committed benchmarks (measured 2026-08-21;
this is also CLAUDE.md's own gotcha for this tool) — so its verdicts are
never treated as authoritative here, only its route-dispatch timings, which
come from the same `auto.rs` dispatch chain both tools call into.

**Counters available, and what is *not* available.** `--trace` exposes
seven stage durations (`boolean_propagate`, `theory_assert`,
`theory_propagate`, `theory_push_pop`, `conflict_analysis`,
`theory_final_check`, `theory_explain`) and six counters (`theory_conflicts`,
`theory_propagations`, `final_checks`, `decisions`, `restarts`,
`simplex_pivots` — always `None`, unwired per D2). There is **no** counter for
total Boolean-only conflicts or total literal-level BCP propagations
distinct from the theory-attributed ones (`cdclt.rs` tracks
`conflicts_since_restart` for the Luby schedule but never exposes it; grep
confirms no other conflict/propagation counter exists). So "conflicts/sec"
and "propagations/sec" below are `theory_conflicts`/`theory_propagations`
rates — the only conflict/propagation counters the driver exposes — not a
total-BCP rate. `decisions/sec` is exact (`CdclT::pick_unassigned` calls).
Rates are wall-clock (`/usr/bin/time` elapsed), not CPU time (CPU was 99% in
every run, so the two are within noise). The `sat-stats-vs-kissat` native-core
comparison lane's note had not landed as of this writing, so no cross-engine
rate comparison is included; that comparison is future work, not inferred
here.

## Finding 0 — three of five QF_IDL files never emit a trace line at all

`RVpredict_13`, `jobshop20-2-10-10-4-4-16` and `jobshop26-2-13-13-4-4-16` ran
to wall-clock **25.00-25.01 s** and printed only `unknown` — no `; theory-layer
…` line. That number is exact: `smtcomp_cli.rs`'s watchdog is
`rx.recv_timeout(Duration::from_millis(ms) + WATCHDOG_GRACE)` with
`WATCHDOG_GRACE = Duration::from_secs(1)` (`crates/axeyum-bench/examples/smtcomp_cli.rs:363,686`),
so 24000 ms + 1000 ms = 25.00 s matches to the millisecond. The theory-layer
report line is built only *after* the worker closure's call to `solve_smtlib`
returns (`smtcomp_cli.rs:635-641`); on a watchdog timeout the channel receive
returns the hardcoded default `("unknown", None, None)` regardless of what
the worker thread has computed so far, so a query whose internal dispatch
takes longer than 25 s leaves **nothing** to print, not even a stale partial
stat.

*Inference, from `explain_corpus`'s route split (same nominal 24000 ms
budget, diagnostic-only tool):* on these three files, `dl-online` (an
incremental difference-logic driver that itself constructs and runs a
`CdclT`, `dl_online.rs:2077`) spends 18.0-21.0 s before declining
`budget`-exhausted, then `lia-simplex` declines `unsupported` in a few ms,
then `lia-dpll` spends a further **~8.0-8.03 s** before it too declines
`budget` — summing to **26.9-29.5 s** of internal route budget against a
24000 ms nominal request. That is D3 in the architecture review measured
again: "the diagnosis found 6 s reserved for `lia-dpll`, which then declines
instantly on a size constant it could have evaluated at `t = 0`" — this run
measures that reservation at ~8.0 s, not 6 s, but the shape (a large
fixed decline cost paid regardless of remaining budget) is the same. Because
these per-route budgets are not drawn against one shared, shrinking
deadline, their sum can exceed the caller's nominal timeout, and when it
does, `smtcomp_cli`'s outer watchdog kills the process mid-route before any
diagnostic line — including a real profile, had `perf` worked — could ever
be written. **Fixing D3's shared deadline is a precondition for profiling
the hardest QF_IDL files at all, not just a throughput fix.**

## Table 1 — QF_IDL

| file | verdict | wall (s) | decisions | theory_conflicts | theory_propagations | restarts | boolean_propagate_ms | theory_ms (other 6 stages) |
|---|---|---|---|---|---|---|---|---|
| RVpredict_13 | unknown | 25.01 | *(no trace: watchdog-killed inside routing, Finding 0)* | | | | | |
| jobshop20-2-10-10-4-4-16 | unknown | 25.00 | *(no trace)* | | | | | |
| jobshop26-2-13-13-4-4-16 | unknown | 25.00 | *(no trace)* | | | | | |
| edge-matching-w=7-h=7-c=11 | unknown | 22.51 | 0 | 0 | 0 | 0 | 19,709 | 0 |
| a7.3.0.tweaked.3.asp | unknown | 22.29 | 0 | 0 | 0 | 0 | 19,152 | 0 |

Rates (decisions/s, conflicts/s, propagations/s) are all `0` for the two rows
that have data — the search never completes a single decision. For
`edge-matching` (322,612 CNF vars, 732,578 clauses per `explain_corpus`'s
`dl-online` detail) and `a7.3.0` (330,420 CNF vars, 818,330 clauses),
`boolean_propagate_ms` is 87-88% of wall clock **and every other stage reads
zero**: the entire observed run is spent inside `CdclT::unit_propagate`
before the search ever reaches a decision, a theory assert, or a conflict.

## Table 2 — QF_LRA

| file | verdict | wall (s) | decisions | theory_conflicts | theory_propagations | restarts | boolean_propagate_ms | theory_final_check_ms | other_theory_ms | decisions/s | conflicts/s (theory) | propagations/s (theory) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| _count_by_k.i_3_3_2.bpl_7 | unknown | 24.05 | 190,851 | 1,157 | 1,200 | 7 | 1,488 | 17,345 | 1,307 | 7,936 | 48.1 | 49.9 |
| _standard_two_index_06.i_3_2_2.bpl_7 | unknown | 24.05 | 245,310 | 1,339 | 83 | 9 | 2,526 | 19,541 | 1,719 | 10,199 | 55.7 | 3.5 |
| blending/1 | unknown | 24.03 | 24,464 | 10,939 | 79 | 45 | 1,971 | 21,802 | 188 | 1,018 | 455.2 | 3.3 |
| blending/5 | unknown | 24.01 | 45,910 | 15,084 | 7,434 | 61 | 3,258 | 20,300 | 383 | 1,912 | 628.2 | 309.6 |
| p-driverlogNumeric_s7 *(not a timeout)* | **sat** | 0.47 | 1,904 | 180 | 0 | 2 | 240 | 158 | 8 | 4,051 | 383.0 | 0.0 |

`other_theory_ms` = `theory_assert + theory_propagate + theory_push_pop +
conflict_analysis + theory_explain` (`theory_final_check` broken out
separately since it dominates). `final_checks` tracks `theory_conflicts`
almost 1:1 on every row (e.g. blending/5: 15,070 vs 15,084) — nearly every
completed Boolean assignment this search reaches is theory-infeasible.

**`p-driverlogNumeric_s7` is not a timeout under this build.** The brief
listed it as one of the ten files "for us" that cvc5 decides, but this run
(commit `9914a1c0e`) returns `sat` in 0.47 s wall clock — reported as
measured, not silently dropped from the table. Whatever miss this file
represented in the source diagnosis's population, it does not reproduce
today; it is excluded from every timeout-only average below.

## Ranking of stages by mean self time

**Pooled across the six files that produced a trace line** (2 QF_IDL + 4
QF_LRA genuine timeouts; `p-driverlogNumeric_s7` and the 3 silent QF_IDL rows
excluded):

| rank | stage (→ function) | mean ms | mean % of wall |
|---|---|---|---|
| 1 | `theory_final_check` → `LraTheory::final_check`/`feasibility` (`lra_online.rs:1056,752`) | 13,165 | ~55% |
| 2 | `boolean_propagate` → `CdclT::unit_propagate` (`cdclt.rs:702`) | 8,017 | ~34% |
| 3 | `theory_propagate` → `TheorySolver::propagate_into` | 577 | ~2% |
| 4 | `theory_assert` → `TheorySolver::assert` | 12 | <1% |
| 5 | `theory_push_pop` → `TheorySolver::push`/`pop` | 8 | <1% |
| 6 | `conflict_analysis` → `CdclT::analyze_conflict` (`cdclt.rs:973`) | 3 | <1% |
| 7 | `theory_explain` → `TheorySolver::explain` | 0 | 0% |

**This pooled ranking is misleading on its own** — it averages two divisions
whose bottlenecks do not overlap. Split by division (means over the rows with
data):

- **QF_IDL (n=2):** `boolean_propagate` mean 19,431 ms (~87% of wall); every
  other stage is exactly 0 across both rows.
- **QF_LRA (n=4):** `theory_final_check` mean 19,747 ms (~84% of wall);
  `boolean_propagate` mean 2,311 ms (~10%); `theory_propagate` mean 866 ms
  (~4%); `theory_assert` 18 ms; `theory_push_pop` 12 ms; `conflict_analysis`
  4 ms.

The pooled table's #1/#2 ordering is an artifact of QF_LRA's larger absolute
`final_check` numbers outweighing QF_IDL's `boolean_propagate` numbers in a
4-file/2-file mix; the per-division split is the actionable one.

## What this says about ADR-1701 slice 2

*The following is inference from counters and source reading, not a sampled
profile — no `perf` data exists for this run (Finding 0/method).* Slice 2
should not be one undifferentiated "speed up propagation" task; the two
divisions measured here have different bottlenecks and neither one is what
the brief's premise described for QF_LRA. For **QF_IDL**, the target is
exactly D1's named gap: `CdclT::unit_propagate` (`cdclt.rs:702-758`) is a
full `for ci in 0..self.clauses.len()` rescan of every clause on every
fixpoint round, re-reading every literal of every clause to find its status —
no two-watched-literal indexing, unlike the already-implemented
proof-producing core in `axeyum-cnf`/`proof_sat.rs` that D1 already
identifies as unused on this path. On `edge-matching` (732,578 clauses) this
single stage consumes 87% of the 24 s budget while `decisions` stays at
**zero** — the search never leaves its first propagation fixpoint, so no
theory time, no conflict analysis, and no decision heuristic ever gets a
chance to run. Moving `CdclT`'s clause storage onto a watched-literal/clause-arena
scheme (slice 2 as scoped) is a plausible direct fix for this division, and is
the *only* lever visible here — every other named stage reads exactly 0 on
both QF_IDL rows with data. For **QF_LRA**, the measured bottleneck
contradicts the framing "almost nothing in the theory": `boolean_propagate`
is a minor 10% of wall clock and the dominant cost (~84%) is
`LraTheory::final_check` → `feasibility()` → `simplex::Incremental`'s
resolve (`lra_online.rs:752,1056`), called 1,150-15,000+ times per run at
1.3-15.0 ms/call, with `final_checks` tracking `theory_conflicts` almost 1:1
— nearly every completed Boolean assignment is theory-infeasible, so the
search is paying a full simplex re-check on almost every assignment it
completes. A `CdclT` clause-arena rewrite would not touch this division's
bottleneck at all; the QF_LRA lever is either cheaper incremental re-use
inside `simplex::Incremental` across `final_check` calls or reducing how
often a full assignment is reached before the theory catches the
infeasibility (a cheaper partial/bound-propagation check ahead of
`final_check`, which D2's slice 1 already partially wired via
`propagate_bounds` in deferred mode). Finally, D3's shared-deadline gap
(Finding 0) is a precondition, not an optional cleanup: three of the five
QF_IDL files here produced no counters at all because the dispatcher's
per-route budgets summed past the caller's watchdog, and the same gap would
hide slice 2's own effect from a future before/after measurement on exactly
the hardest files in the population.

## Raw data

- `bench-results/arith-timeout-profiles-20260905/*.trace.txt` — per-file
  `--trace` stage lines and `/usr/bin/time -v` wall-clock output.
- `bench-results/arith-timeout-profiles-20260905/explain_corpus.jsonl` — the
  per-route timed-trace split (diagnostic-only tool, see Method).
- `bench-results/arith-timeout-profiles-20260905/explain_corpus.stderr` — the
  tool's own disagreement-rate banner.
- `bench-results/arith-timeout-profiles-20260905/filelist.txt` — the exact
  10-file list passed to `explain_corpus --list`.
