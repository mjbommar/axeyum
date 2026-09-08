//! SMT-COMP competition interface for axeyum — the exact CLI a Single-Query /
//! Model-Validation / Unsat-Core entrant must expose (SMT-COMP 2026 rules §5).
//!
//! Invocation: the benchmark file is the **first command-line argument**; the
//! solver prints exactly one of `sat` / `unsat` / `unknown` on stdout and
//! nothing verdict-shaped on stderr (the rules treat any stray `sat`/`unsat`
//! text as a reported result — §7.1.2). This wraps the existing
//! [`axeyum_solver::solve_smtlib`]; it adds no solver logic.
//!
//! An optional internal wall-clock timeout can be set with `--timeout-ms N` or
//! the `AXEYUM_TIMEOUT_MS` env var (the competition enforces the real limit
//! externally via `BenchExec`; this is a courtesy soft-stop so the binary yields
//! `unknown` instead of running unbounded when driven by the local harness).
//!
//! Run:
//! ```sh
//! cargo run -q -p axeyum-bench --example smtcomp_cli -- path/to/bench.smt2
//! ```
//!
//! # Evidence mode (`AXEYUM_EVIDENCE=1` / `--evidence`), OFF by default
//!
//! With evidence mode on, the binary routes through
//! [`axeyum_solver::produce_evidence_smtlib`] instead of
//! [`axeyum_solver::solve_smtlib`] and prints ONE extra line before the verdict:
//!
//! ```text
//! ; evidence kind=unsat-drat certified=1 trusted=2:bit-blast+,tseitin+ recheck=ok arena=ok ms=412
//! ```
//!
//! The line starts with `;` (the SMT-LIB comment character) and can never match
//! `^(sat|unsat)$`, so a harness that greps the verdict is unaffected. This is
//! what makes certificate coverage a per-file measurement instead of an essay:
//! `certified=1` means this result
//! carries an independently checkable certificate object, and `recheck=ok` means
//! this process re-validated that certificate **from its serialized text alone**
//! (`UnsatProof::recheck`: re-parse the DIMACS + DRAT/LRAT and re-derive the
//! empty clause), which is exactly what an external `drat-trim` would do.
//!
//! `arena=ok` is the second, broader re-validation: [`axeyum_solver::Evidence::check`]
//! against a **fresh parse of the original file**. Most certificate kinds have no
//! serialized form, so `recheck` can only say `na` for them — the `QF_BV` board shows
//! the gap as `certified 70.8 %` against `re-checked (text-only) 60.0 %`. Those
//! files are un-*text*-checkable, not uncheckable, and `arena` says so without
//! letting either claim borrow the other's strength. It is kept a SEPARATE field
//! for exactly that reason: `recheck` still means what every recorded entry says
//! it means. A bare or uncovered `unsat` remains visibly uncertified; evidence
//! mode measures the gap rather than asserting universal proof coverage.
//!
//! Off by default on purpose: producing and re-checking a proof costs real time
//! on top of deciding, so turning it on silently would invalidate every recorded
//! parity baseline. Same discipline as `AXEYUM_CNF_INPROCESSING` /
//! `AXEYUM_CNF_VIVIFY` below.
//!
//! # Progress mode (`AXEYUM_PROOF_PROGRESS=1` / `--progress`), OFF by default
//!
//! A DRAT certificate run on a hard instance can run for hours with **zero**
//! observable output beyond elapsed time and RSS — the incident that motivates
//! this flag ran 5 h 59 min and produced nothing before being reaped, on a
//! query that the non-certifying path decides in 11.5 s. Progress mode makes
//! that search's own conflict counter and proof growth visible while it runs.
//! Only meaningful together with `--evidence` (progress is a property of the
//! proof-producing SAT search evidence mode invokes on `QF_BV` `unsat`
//! certificate production, `axeyum_solver::produce_qf_bv_evidence`'s DRAT
//! route); it is a silent no-op otherwise, since there is then no such search
//! to watch.
//!
//! Every `axeyum_cnf::DEFAULT_PROGRESS_CONFLICT_INTERVAL` conflicts (override
//! with `AXEYUM_PROOF_PROGRESS_INTERVAL=N`), one line is printed:
//!
//! ```text
//! ; progress conflicts=120000 learned=41230 proof_steps=118872 proof_bytes=9427110 elapsed_ms=8032 conflicts_per_sec=14938.7 proof_bytes_per_sec=1173596.9
//! ```
//!
//! Same convention as the evidence line: `;`-prefixed, so it can never match
//! `^(sat|unsat)$` or `^unknown$` — a harness that greps the verdict never sees
//! it, and it is printed strictly BEFORE the evidence/verdict lines (the
//! search that produced it has already returned by the time those print).
//! `conflicts_per_sec` / `proof_bytes_per_sec` are computed from the snapshot's
//! own cumulative totals over its own elapsed time, so a watcher can state a
//! falsifiable expectation from a single line — "at this rate it finishes by X
//! or it does not" — rather than just observe that the number moved.
//!
//! Off by default for the same reason evidence mode is: it costs real time
//! (periodic snapshots are cheap, but every progress-observed run implies the
//! certificate-producing route) and must never silently change a recorded
//! baseline. Installing the sink cannot change the verdict or the emitted
//! DRAT proof either way — see
//! [`axeyum_cnf::solve_with_drat_proof_with_limits_and_progress`]'s
//! no-behaviour-change guarantee, which this flag relies on rather than
//! re-asserts.
//!
//! ## Checking-stage progress (same `--progress` flag)
//!
//! The lines above cover the SEARCH. The stage that actually got stuck in the
//! motivating incident was the one AFTER it: `axeyum_cnf::check_drat`
//! re-deriving the RUP/RAT refutation, then (if that verifies)
//! `axeyum_cnf::elaborate_drat_to_lrat` recovering explicit hints for the
//! LRAT certificate — a re-scan measured at ~6 h on the same query the search
//! decided in 24.2 s, with zero output the whole time. `--progress` now
//! installs a sink there too (`axeyum_solver::CheckProgress`), printing, every
//! `AXEYUM_CHECK_PROGRESS_INTERVAL` steps (default 50,000) per sub-stage:
//!
//! ```text
//! ; checking stage=drat_check steps=250000 total=827048 active_clauses=193422 elapsed_ms=41230 steps_per_sec=6063.5
//! ; checking stage=lrat_elaborate steps=100000 total=827048 active_clauses=193422 lrat_steps=100000 elapsed_ms=88510 steps_per_sec=1129.7
//! ```
//!
//! A distinct `; checking` prefix (never `; progress`) so the two families are
//! `grep`-separable without parsing fields, and — like every line in this
//! file — it can never match `^(sat|unsat)$` / `^unknown$`. `stage=` names
//! which of the two sub-stages produced the line, which is the direct answer
//! to "is checking or elaboration the one eating the time": compare the two
//! `steps_per_sec` figures. `AXEYUM_CHECK_STEP_LIMIT`, if set, additionally
//! bounds each sub-stage by step count; unset, checking is bounded only by
//! whatever wall-clock deadline `--timeout-ms` implies (it inherits the
//! search's remaining budget). A checking stage that runs out is reported as
//! the honest uncertified `; evidence certified=0` line, never a certified
//! pass — a timeout is not a pass.
//!
//! # Theory-route stage attribution (`AXEYUM_TRACE=1` / `--trace`), OFF by default
//!
//! Every arithmetic/EUF/string/combined-theory route runs the same generic
//! CDCL(T) driver (`crate::cdclt::CdclT`, in `axeyum-solver`), which — until
//! `axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats` — had no
//! stage attribution: the 2026-08-21 linear-arithmetic diagnosis classified
//! ~800 files by hand from per-file TSVs because no instrument said whether a
//! query's time went to Boolean propagation, `TheorySolver::assert`,
//! `TheorySolver::propagate`, or 1-UIP conflict analysis. `--trace` enables
//! collection for this one solve and, if a CDCL(T) route ran and decided,
//! prints one `;`-prefixed line before the verdict:
//!
//! ```text
//! ; theory-layer boolean_propagate_ms=812 theory_assert_ms=241 theory_propagate_ms=96 \
//!   theory_push_pop_ms=4 conflict_analysis_ms=118 theory_conflicts=3110 \
//!   theory_propagations=8842 decisions=4201 restarts=6 \
//!   learned_clauses=3110 learned_literals=51230 learned_literals_premin=68812 \
//!   simplex_pivots=41233 simplex_checks=1157 simplex_cold_restarts=0 \
//!   bound_retractions=88104 bound_assertions=89261 propagations_offered=1200
//! ```
//!
//! `learned_literals / learned_clauses` is the mean learned-clause length;
//! `learned_literals_premin - learned_literals` is exactly the number of
//! literals recursive minimization removed on this run, so the minimizer's
//! effect is readable from one run rather than from a comparison of two.
//!
//! The last six are the theory's own engine counters (S4,
//! `TheorySolver::engine_counters`); they read `n/a` for a theory that keeps
//! no feasibility engine, which is every theory but the LRA one today. `n/a`
//! and `0` are deliberately different: one is "not measured", the other is a
//! measurement.
//!
//! No line is printed when no CDCL(T) route decided the query (e.g. a `QF_BV`
//! `sat-bv` decide, or an `unknown`) — collection has nothing to report.
//! Off by default for the same reason `--evidence`/`--progress` are: reading
//! the clock at every driver stage boundary, however cheap, must never
//! silently change a recorded parity baseline. This is the CDCL(T)
//! stage-timing counterpart to `--evidence`'s certificate reporting; it is
//! **not** the dispatch-level `RouteTrace` (which route was tried and why it
//! declined) — that instrument's opt-in timed JSON form lives in
//! `explain_corpus --json --timed-trace`, the diagnosis tool this file's
//! competition-interface contract (verdict-only stdout) is not shaped for.
//!
//! # BV-layer, front-door, and dl-online stage attribution (same `--trace`
//! flag), 2026-09-07
//!
//! `bench-divisions-2026-09-07` measured `--trace` (the section above)
//! covering only 15.6% of sampled wall clock, with five of twelve divisions
//! (`QF_ABV`, `QF_BV`, `QF_IDL`, `QF_RDL`, `QF_UFLIA`) at **zero** coverage —
//! their dominant routes never touch the generic CDCL(T) driver at all. Three
//! more lines, all gated by the SAME `--trace` flag (no new CLI surface),
//! close most of that gap:
//!
//! ```text
//! ; front-door parse_ms=4
//! ; dl-online total_ms=0
//! ; bv-layer bit_blast_ms=2 cnf_encode_ms=6 cnf_inprocess_ms=0 solve_ms=24089 \
//!   model_lift_ms=0 model_replay_ms=0 total_ms=24098 \
//!   bit_demand_analysis_nested_in_bit_blast_ms=0 \
//!   range_demand_admission_nested_in_bit_blast_ms=0 \
//!   aig_nodes=32251 cnf_variables=12030 cnf_clauses=49146
//! ```
//!
//! - `; front-door …` — cumulative SMT-LIB parse time, summed across every
//!   string-bound-ladder rung. Always printed when `--trace` is on: every
//!   division's front door parses at least once.
//! - `; dl-online …` — total wall time inside the whole difference-logic
//!   probe call (`crate::dl_online::try_check_qf_dl`), timed at its single
//!   call site rather than broken into its own internal stages. Printed only
//!   when the probe actually ran (`QF_BV` and similar bit-vector-only
//!   queries never reach that dispatch branch at all) — this is `QF_IDL` /
//!   `QF_RDL`'s ONLY stage instrument, since their dominant route is exactly
//!   this probe and it never enters the CDCL(T) driver.
//! - `; bv-layer …` — the pure-Rust bit-blast pipeline's own stage
//!   breakdown (`axeyum_solver::BvLayerStats`, previously computed
//!   internally but wired to no CLI flag). Printed only when the `sat-bv`
//!   backend actually ran (covers `QF_BV` directly, `QF_ABV` via array
//!   elimination's reduction to the same backend) — mutually exclusive with
//!   `; theory-layer …` per query, since a `sat-bv` decide never runs the
//!   CDCL(T) driver and vice versa. `total_ms` sums only the six additive
//!   stage fields (`BvLayerStats::total`); the two `_nested_in_bit_blast_ms`
//!   fields are sub-timings taken DURING the `bit_blast_ms` call and are
//!   deliberately excluded from `total_ms` — summing them in would
//!   double-count the same way `theory_assert_ms` did inside
//!   `boolean_propagate_ms` in the section above.
//!
//! Same off-by-default discipline as every other lever in this file: no
//! extra clock read unless `--trace` is set (see
//! `axeyum_solver::BvLayerStatsGuard` / `FrontDoorStatsGuard` /
//! `DlOnlineStatsGuard`), and none of the three can change a verdict — they
//! only add stdout lines before it. Full measurement/methodology:
//! docs/research/12-performance/instrument-coverage-2026-09-07.md.
//!
//! # Which configuration this run used (same `--trace` flag), 2026-09-07
//!
//! Every line above says what the run SPENT. None said what the run was
//! CONFIGURED with, so a stage timing could not be compared against another
//! run's without an assumption nobody wrote down — and `AXEYUM_NRA_ADMISSION`
//! alone selects between two admission policies that differ by 15x while
//! leaving no trace in the output. `--trace` now prints one more line, first:
//!
//! ```text
//! ; config digest=3f2a9c4e17b05d88 entries=113 dated=24 \
//!   env:AXEYUM_NRA_ADMISSION=legacy consulted=2 \
//!   crates/axeyum-solver/src/lra_theory.rs::MAX_ONLINE_LRA_ATOMS \
//!   crates/axeyum-solver/src/nra.rs::MCCORMICK_ATOMS_PER_TRIPLE
//! ```
//!
//! - `digest` — FNV-1a over the registry's sorted `key=value` pairs AND the
//!   active environment overrides. Two runs printing the same digest used the
//!   same configuration; two printing different digests did not, and the
//!   `env:` fields say how. This is the reproducibility handle: it is what a
//!   surprising result gets compared against first.
//! - `entries` / `dated` — the size of the governing surface and how much of
//!   it carries a justification with a date. The ratio is reported in the run
//!   because a registry that did not report it could grow undated entries
//!   indefinitely with nothing noticing.
//! - `env:` — only variables a registry entry NAMES. An unrecognized
//!   `AXEYUM_*` variable is not reported, because a line that reported
//!   everything could not be wrong about anything.
//! - `consulted` — governing values this run actually reached, sorted. This is
//!   the part that traces a verdict to a bound: it is how a `--trace` reader
//!   sees that `nia_linearize::MAX_CONGRUENCE_GROUPS` was consulted at all,
//!   which is a bound that otherwise crosses with no branch and no signal.
//!
//! Printed first among the stage lines because the others have to be read
//! against it. Same off-by-default discipline: with no `--trace` the guard is
//! never constructed, `note_consulted` is one thread-local `Cell<bool>` read,
//! and nothing is allocated. The verdict is byte-identical either way — the
//! registry is a description of the values, never a source of them. Sorted
//! output throughout, from a `BTreeSet`, because determinism is a public API
//! promise here and a `HashSet` would make the line depend on per-process hash
//! seeding. Full record: ADR-1762 and
//! docs/research/12-performance/config-registry-2026-09-07.md.
//!
//! # What a TIMED-OUT file prints (same `--trace` flag), 2026-09-08
//!
//! Every line above is built after `solve()` returns, from thread-local
//! accumulators owned by the worker thread. A wall-clock timeout is enforced
//! from the main thread, on a worker that has not returned — so until now a
//! timed-out file printed none of them: 22 of 33 lost `QF_LRA` files had no
//! theory-layer line at all, which is the opposite of what a diagnostic should
//! do, since the files we lose are the files we most need to explain.
//!
//! The instruments now also mirror onto a cross-thread board
//! (`axeyum_solver::live_instruments`), and the native CDCL(T) search mirrors
//! its own counters from inside its loop on a fixed iteration cadence, so a
//! watchdog kill prints what accumulated up to the kill:
//!
//! ```text
//! ; partial at=watchdog-kill recovered=3 sampled=front-door:complete,\
//!   theory-layer:in-flight,route:in-flight reason: watchdog fired before …
//! ; partial front-door parse_ms=18
//! ; partial theory-layer boolean_propagate_ms=412 … decisions=63623 …
//! ; partial route decided_by=none bound_by=nra last=nra …
//! ```
//!
//! - **The leading token is `; partial `, not the completed line's token.** A
//!   consumer that greps `^; theory-layer ` keeps matching only complete lines,
//!   so a mid-search count cannot be swept into an aggregate that thinks it has
//!   totals — a truncated count that reads like a complete one is worse than no
//!   count, because somebody divides by it. The line BODY is byte-identical to
//!   the completed form, so one parser reads both families.
//! - **The header says where the reading was taken and which instruments were
//!   still running.** `front-door:complete` is a stage that finished inside a
//!   query that did not; `theory-layer:in-flight` is a search that was mid-loop
//!   when it was read, so every counter on that line is a lower bound.
//! - **An instrument that mirrored nothing still says so** (`; theory-layer
//!   unavailable: …`), and a kill before ANY instrument published prints
//!   exactly the two `unavailable` lines it printed before — so "never got far
//!   enough" stays distinguishable from "collection was off" (no lines at all).
//! - **Not everything survives.** The `; config` line does not: its
//!   consulted-key set is thread-local to the worker with no publish site, and
//!   printing the rest of it from this thread would leave a `consulted=` field
//!   silently absent, which reads as "nothing was consulted". A `sat-bv` check
//!   killed mid-solve does not report `; bv-layer` either: its stage timings
//!   are lifted only when the check returns. Its Boolean search is visible
//!   through the `; progress` lines this path already prints — but only when
//!   `--progress` is ALSO on, since `--trace` does not install a progress sink.
//!
//! Same off-by-default discipline: with no `--trace` no board is installed and
//! every mirror site is one thread-local `bool` read.

use std::process::ExitCode;
use std::sync::{Arc, mpsc};
use std::time::{Duration, Instant};

use axeyum_solver::theories::cdclt_diagnostics::{TheoryLayerStatsGuard, last_theory_layer_stats};
use axeyum_solver::{
    BvLayerStats, BvLayerStatsGuard, CheckProgress, CheckResult, CheckingProgress,
    ConfigTraceGuard, DlOnlineStatsGuard, Evidence, EvidenceCheck, EvidenceReport, FrontDoorStats,
    FrontDoorStatsGuard, LiveInstruments, ProofProgress, RouteAttributionGuard, RouteTrace,
    Sampled, SolverConfig, UfArithOverboundStatsGuard, config_trace_line, install_live_instruments,
    instrument, last_bv_layer_stats, last_dl_online_stats, last_front_door_stats,
    last_route_attribution, last_uf_arith_overbound_stats, live_theory_layer_stats,
    produce_evidence_smtlib, solve_smtlib,
};

/// Formats one `axeyum_cnf::ProofSearchProgress` snapshot as the `;`-prefixed
/// progress line documented in the module header. `;` is the SMT-LIB comment
/// character and this can never match `^(sat|unsat)$` / `^unknown$`, exactly
/// like the `; evidence …` line — see [`evidence_report_line`].
///
/// Rates are computed from the snapshot's own cumulative totals over its own
/// elapsed time (not a delta from the previous snapshot), so a single printed
/// line is a complete, falsifiable claim on its own: "`conflicts_per_sec` ×
/// remaining time" is an estimate a reader can check later against what
/// actually happened, with no other line needed.
///
/// The `usize`/`u64` -> `f64` casts below are a display-only rate estimate,
/// not a proof-relevant count (those stay exact `usize`/`u64` earlier in the
/// same line); losing precision in the trailing digits of a conflicts-per-second
/// figure changes nothing anyone checks against.
#[allow(clippy::cast_precision_loss)]
fn progress_report_line(snapshot: &axeyum_cnf::ProofSearchProgress) -> String {
    let elapsed_secs = snapshot.elapsed.as_secs_f64();
    let per_sec = |total: f64| {
        if elapsed_secs > 0.0 {
            total / elapsed_secs
        } else {
            0.0
        }
    };
    format!(
        "; progress conflicts={} learned={} proof_steps={} proof_bytes={} elapsed_ms={} \
         conflicts_per_sec={:.1} proof_bytes_per_sec={:.1}",
        snapshot.conflicts,
        snapshot.learned_clauses,
        snapshot.proof_steps,
        snapshot.proof_bytes,
        snapshot.elapsed.as_millis(),
        per_sec(snapshot.conflicts as f64),
        per_sec(snapshot.proof_bytes as f64),
    )
}

/// Formats a [`axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats`]
/// snapshot as the `;`-prefixed line documented in the module header (the
/// `--trace` section). `;` is the SMT-LIB comment character, so this can
/// never match `^(sat|unsat)$` / `^unknown$` — same convention as
/// [`progress_report_line`] / [`evidence_report_line`].
fn theory_layer_report_line(
    &stats: &axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats,
) -> String {
    /// `n/a` for a counter the driving theory does not keep, so an absent
    /// counter never reads as a measured zero.
    fn optional(value: Option<u64>) -> String {
        value.map_or_else(|| "n/a".to_string(), |v| v.to_string())
    }
    format!(
        "; theory-layer boolean_propagate_ms={} theory_assert_ms={} theory_propagate_ms={} \
         theory_push_pop_ms={} conflict_analysis_ms={} theory_final_check_ms={} \
         theory_explain_ms={} theory_conflicts={} theory_propagations={} \
         final_checks={} decisions={} restarts={} \
         learned_clauses={} learned_literals={} learned_literals_premin={} \
         simplex_pivots={} simplex_checks={} simplex_cold_restarts={} \
         bound_retractions={} bound_assertions={} propagations_offered={} \
         simplex_rows={} simplex_columns={} assert_partial_conflicts={} \
         final_check_conflicts={} final_check_core_literals={} \
         final_check_core_widenings={} final_check_live_rows={} \
         bound_scan_calls={} bound_scan_atoms={} \
         pivot_cells_written={} pivot_rows_combined={} entering_scan_cells={} \
         leaving_scan_rows={} fill_nnz_sum={} fill_samples={} bland_fallbacks={} \
         farkas_certificates={} farkas_declined_basic_not_slack={} \
         farkas_declined_nonbasic_problem_var={} farkas_declined_self_check={}",
        stats.boolean_propagate.as_millis(),
        stats.theory_assert.as_millis(),
        stats.theory_propagate.as_millis(),
        stats.theory_push_pop.as_millis(),
        stats.conflict_analysis.as_millis(),
        stats.theory_final_check.as_millis(),
        stats.theory_explain.as_millis(),
        stats.theory_conflicts,
        stats.theory_propagations,
        stats.final_checks,
        stats.decisions,
        stats.restarts,
        stats.learned_clauses,
        stats.learned_literals,
        stats.learned_literals_before_minimization,
        optional(stats.simplex_pivots),
        optional(stats.simplex_checks),
        optional(stats.simplex_cold_restarts),
        optional(stats.bound_retractions),
        optional(stats.bound_assertions),
        optional(stats.theory_propagations_offered),
        optional(stats.simplex_rows),
        optional(stats.simplex_columns),
        optional(stats.assert_partial_conflicts),
        optional(stats.final_check_conflicts),
        optional(stats.final_check_core_literals),
        optional(stats.final_check_core_widenings),
        optional(stats.final_check_live_rows),
        optional(stats.bound_scan_calls),
        optional(stats.bound_scan_atoms),
        optional(stats.pivot_cells_written),
        optional(stats.pivot_rows_combined),
        optional(stats.entering_scan_cells),
        optional(stats.leaving_scan_rows),
        optional(stats.fill_nnz_sum),
        optional(stats.fill_samples),
        optional(stats.bland_fallbacks),
        optional(stats.farkas_certificates),
        optional(stats.farkas_declined_basic_not_slack),
        optional(stats.farkas_declined_nonbasic_problem_var),
        optional(stats.farkas_declined_self_check),
    )
}

/// Formats an [`axeyum_solver::BvLayerStats`] snapshot as the `;`-prefixed
/// `--trace` line documented in the module header's "BV-layer stage
/// attribution" section.
///
/// The five `_ms` fields plus `total_ms` are [`axeyum_solver::BvLayerStats::total`]'s
/// own additive decomposition — non-overlapping by construction. The last two
/// fields are DELIBERATELY excluded from `total_ms`: both are sub-timings
/// taken *during* `bit_blast_ms`'s own lowering call (see
/// `axeyum_solver::BvLayerStats::total`'s docs), so summing them in would
/// double-count exactly the way `theory_assert_ms` did inside
/// `boolean_propagate_ms` for the `; theory-layer …` line above — the
/// `_nested_in_bit_blast_ms` suffix says so at the point a reader would
/// otherwise be tempted to add it in.
fn bv_layer_report_line(stats: &axeyum_solver::BvLayerStats) -> String {
    format!(
        "; bv-layer bit_blast_ms={} cnf_encode_ms={} cnf_inprocess_ms={} solve_ms={} \
         model_lift_ms={} model_replay_ms={} total_ms={} \
         bit_demand_analysis_nested_in_bit_blast_ms={} \
         range_demand_admission_nested_in_bit_blast_ms={} \
         aig_nodes={} cnf_variables={} cnf_clauses={}",
        stats.bit_blast.as_millis(),
        stats.cnf_encode.as_millis(),
        stats.cnf_inprocess.as_millis(),
        stats.solve.as_millis(),
        stats.model_lift.as_millis(),
        stats.model_replay.as_millis(),
        stats.total().as_millis(),
        stats.bit_demand_analysis.as_millis(),
        stats.range_demand_admission.as_millis(),
        stats.aig_nodes,
        stats.cnf_variables,
        stats.cnf_clauses,
    )
}

/// Formats an [`axeyum_solver::FrontDoorStats`] snapshot as the `;`-prefixed
/// `--trace` line documented in the module header. Currently one field
/// (cumulative parse time across every string-bound-ladder rung this
/// front-door call ran); more front-door stages land here as they are
/// instrumented (docs/research/12-performance/instrument-coverage-2026-09-07.md).
fn front_door_report_line(stats: &axeyum_solver::FrontDoorStats) -> String {
    format!("; front-door parse_ms={}", stats.parse.as_millis())
}

/// Formats this thread's cumulative dl-online call time (see
/// [`axeyum_solver::last_dl_online_stats`]) as the `;`-prefixed `--trace`
/// line documented in the module header. Coarser than the other two lines
/// here on purpose: `QF_IDL`/`QF_RDL`'s dominant route never enters the
/// generic CDCL(T) driver at all (the finding that motivated instrumenting
/// it), and this reports only the ONE number this lane's scope could safely
/// add — total wall time inside the whole `try_check_qf_dl` call, timed at
/// its single call site rather than broken into its own internal stages —
/// enough to say how much of a query's wall clock went into this route, not
/// where inside it the time went.
fn dl_online_report_line(elapsed_ms: u128) -> String {
    format!("; dl-online total_ms={elapsed_ms}")
}

/// Formats this front-door call's route attribution (ADR-1760) as two
/// `;`-prefixed `--trace` lines: a one-line summary and the full ordered trail
/// as JSON.
///
/// # The two questions this answers, and why they are separate fields
///
/// `decided_by=` is **which route produced the verdict** — meaningful exactly
/// when the file was decided.
///
/// `bound_by=` is **which route consumed the budget** — the single most
/// expensive segment of the trail. On an undecided file this is the number that
/// matters, and it is routinely a *different* route from the one that spoke
/// last, which is why `last=` is reported alongside it rather than instead of
/// it. Classifying by the last route's message has been refuted here before: a
/// census of 403 files was wrong on 67 of 70 in two divisions, and one
/// division's "23 admission declines" were timeouts. Both fields are printed on
/// every file so a consumer never has to infer one from the other.
///
/// `bound_ms=` / `total_ms=` give the binding segment's share, so "one route ate
/// the whole budget" is distinguishable from "the budget was spread over
/// twenty routes that each declined cheaply" — two situations with opposite
/// implications for a portfolio.
fn route_attribution_report_lines(trace: &axeyum_solver::RouteTrace) -> Vec<String> {
    if trace.is_empty() {
        return vec!["; route unavailable: no attribution recorded".to_string()];
    }
    let decided = trace
        .decided_by()
        .map_or_else(|| "none".to_string(), |(_, a, _)| a.route.to_string());
    let (bound, bound_ms) = trace.bound_by().map_or_else(
        || ("none".to_string(), 0),
        |(_, a, d)| (a.route.to_string(), d.as_millis()),
    );
    let last = trace
        .last()
        .map_or_else(|| "none".to_string(), |a| a.route.to_string());
    vec![
        format!(
            "; route decided_by={decided} bound_by={bound} last={last} \
             bound_ms={bound_ms} total_ms={} attempts={}",
            trace.total_elapsed().as_millis(),
            trace.attempts().len()
        ),
        format!("; route-trail {}", trace.to_json_with_timing()),
    ]
}

/// S2 dispatch-overrun fix (2026-09-05,
/// `docs/plan/smt-parity-plan-2026-09-05.md` row S2): the `; theory-layer …`
/// line the watchdog-timeout path in `main` prints when it cannot report real
/// [`axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats`] — the
/// worker's snapshot is thread-local to the worker thread (see
/// `crate::theories::cdclt_diagnostics`), so a watchdog firing on the main
/// thread has no live snapshot to read. `None` when `trace_mode` is off, so a
/// default run's output is unaffected — same convention as every other lever
/// in this file.
///
/// Before this fix the watchdog-timeout path printed nothing for `--trace` —
/// not even a stale partial stat — because the whole `(verdict, evidence,
/// trace_line)` triple was hardcoded to `("unknown", None, None)`. Three of
/// five traced `QF_IDL` timeouts hit exactly this path
/// (`docs/research/11-design-review/2026-09-05-arith-timeout-profiles.md`,
/// Finding 0). A caller can tell "the search never got far enough to report
/// anything" (this line) apart from "collection was never enabled" (no line
/// at all, the pre-existing and unchanged behavior of a normal, in-budget
/// return with `trace_mode` off) without guessing.
///
/// Returns a `Vec` (empty when `trace_mode` is off) rather than
/// `Option<String>` so it composes directly with the `Vec<String>` of trace
/// lines `solve()`'s normal-return path produces (2026-09-07, when the
/// `; bv-layer …` / `; front-door …` / `; dl-online …` lines were added
/// alongside `; theory-layer …`) — a caller does
/// `trace_lines.extend(watchdog_unavailable_line(..))` either way. This still
/// reports only the theory-layer line on a watchdog timeout, not one
/// `unavailable` marker per new instrument: every one of them has the exact
/// same thread-local-to-the-worker-thread limitation `TheoryLayerStats` does,
/// but multiplying near-duplicate "unavailable" lines was judged not worth
/// the output-format churn for a diagnostic-only path; see
/// docs/research/12-performance/instrument-coverage-2026-09-07.md.
///
/// # Why `; route unavailable: …` IS worth a second line (2026-09-07, ADR-1760)
///
/// The judgement above — that multiplying near-duplicate `unavailable` markers
/// is not worth the output churn — is kept for the stage-timing instruments and
/// deliberately NOT extended to route attribution, because the measurement that
/// motivated it says otherwise. In the 1,200-file sweep,
/// `bench-results/route-attribution-2026-09-07`, **96 files printed no route
/// line at all, and every one of them was `unsolved`.** That is the population
/// the instrument exists to explain, so its blind spot sits exactly where the
/// question is hardest.
///
/// Making the absence SPEAK does not close the blind spot — the trail really is
/// unreadable from this thread — but it makes "the watchdog fired before
/// anything could be read" distinguishable from "collection was off" and from
/// "the harness dropped the line", without a consumer having to guess which.
/// An aggregation can then count what it cannot attribute instead of quietly
/// shrinking its own denominator, which is how a coverage number becomes wrong
/// while staying stable.
///
/// # The blind spot IS closed now, and this is the fallback (2026-09-08)
///
/// Two judgements above have been superseded by measurement and are kept only
/// as the record of why this function still exists.
///
/// "The trail really is unreadable from this thread" was true of thread-local
/// storage, not of the instrument. `axeyum_solver::live_instruments` gives every
/// instrument a shared board to mirror onto, and the native CDCL(T) search
/// mirrors its own counters on a fixed iteration cadence
/// (`axeyum_cnf::NativeLayerStatsMirror`), so a watchdog now reads real partial
/// data — see [`watchdog_trace_lines`], which is what `main` calls.
///
/// "Rather than add shared mutable state to a hot search loop for a
/// diagnostic-only line" priced that state as expensive without measuring it.
/// Measured: the added cost is one already-loaded `bool` test per search-loop
/// iteration, and an A/B against the pre-change binary put both a default run
/// and a `--trace` run inside a ±1.5% noise band on a loaded host — a
/// fixed-3 s-budget `QF_LRA` run did 0.4–0.6% MORE simplex pivots after. The
/// snapshot copy happens once per 1,024 iterations, never per propagation.
///
/// This function is now reached only when nothing mirrored at all — a query
/// killed before any instrument published — and returns exactly what it always
/// returned, so that case's output is unchanged.
fn watchdog_unavailable_line(trace_mode: bool, reason: &str) -> Vec<String> {
    if !trace_mode {
        return Vec::new();
    }
    vec![
        format!("; theory-layer unavailable: {reason}"),
        format!("; route unavailable: {reason}"),
    ]
}

/// Re-labels one ordinary `--trace` line as a partial reading.
///
/// `; theory-layer x=1` becomes `; partial theory-layer x=1`. The leading token
/// changes rather than a field being appended, and that is the whole point: a
/// consumer that greps `^; theory-layer ` keeps matching only COMPLETE lines,
/// so a mid-search count can never be swept into an aggregate that thinks it
/// has totals. A consumer that wants the partial data asks for `^; partial `
/// and takes on the obligation that comes with it.
///
/// Which reading each recovered instrument gave — `complete` or `in-flight` —
/// is on the header line rather than appended here, so the body of every line
/// (including the route trail's JSON, which ends the line) is byte-identical to
/// what a completed run prints.
fn partial_line(line: &str) -> String {
    // Every renderer in this file emits `"; "`-prefixed lines. One that did not
    // is passed through with the marker in front rather than mangled.
    line.strip_prefix("; ").map_or_else(
        || format!("; partial {line}"),
        |body| format!("; partial {body}"),
    )
}

/// The `--trace` lines a watchdog timeout prints: whatever the instruments
/// mirrored onto `board` before the kill, each labelled partial, plus an
/// `unavailable` line for whichever of the two headline instruments mirrored
/// nothing at all.
///
/// # Why partial data has to be labelled, not just reported
///
/// Every counter here was read while the worker was still running. A truncated
/// count that reads like a complete one is worse than no count, because
/// somebody divides by it — so nothing on these lines shares a leading token
/// with the completed lines, and the header says both where the reading was
/// taken and which instruments were still in flight when it was.
///
/// # What survives, and what still does not
///
/// An instrument survives here exactly when it mirrors onto the board (see
/// `axeyum_solver::live_instruments`): the front door's parse time, the
/// `dl-online` route (entered as well as completed), a completed `sat-bv`
/// check's `bv-layer` stages, the route trail, and — through
/// [`live_theory_layer_stats`], which is the only one that can report from a
/// search that has NOT returned — the theory layer. What does not survive is a
/// stage with no mirror point at all: the `; config` line, whose consulted-key
/// set is thread-local to the worker with no publish site, and a `sat-bv` check
/// killed mid-solve, whose stage timings are lifted only when the check
/// returns — its Boolean search shows up in the `; progress` lines this path
/// already prints, but only when `--progress` is also on.
///
/// With nothing mirrored this returns exactly what it always returned — the two
/// `unavailable` lines — so a run that never got far enough to instrument
/// anything is still distinguishable from a run with collection switched off
/// (no lines at all).
fn watchdog_trace_lines(trace_mode: bool, board: &LiveInstruments, reason: &str) -> Vec<String> {
    if !trace_mode {
        return Vec::new();
    }
    let mut lines = Vec::new();
    // `(instrument name, how the reading was taken)`, for the header.
    let mut provenance: Vec<String> = Vec::new();
    let mut note = |name: &str, sampled: Sampled| {
        provenance.push(format!("{name}:{}", sampled.label()));
    };

    if let Some(front_door) = board.sample::<FrontDoorStats>(instrument::FRONT_DOOR) {
        lines.push(partial_line(&front_door_report_line(&front_door.value)));
        note("front-door", front_door.sampled);
    }
    if let Some(dl) = board.sample::<(Duration, u64)>(instrument::DL_ONLINE) {
        let (elapsed, calls) = dl.value;
        // Same `calls > 0` gate the completed path uses: a zero count means the
        // dispatch branch was never reached, which is not the same as a route
        // that ran and cost nothing.
        if calls > 0 {
            lines.push(partial_line(&dl_online_report_line(elapsed.as_millis())));
            note("dl-online", dl.sampled);
        }
    }
    if let Some(bv) = board.sample::<BvLayerStats>(instrument::BV_LAYER) {
        lines.push(partial_line(&bv_layer_report_line(&bv.value)));
        note("bv-layer", bv.sampled);
    }
    if let Some(theory) = live_theory_layer_stats(board) {
        lines.push(partial_line(&theory_layer_report_line(&theory.value)));
        note("theory-layer", theory.sampled);
    } else {
        lines.push(format!("; theory-layer unavailable: {reason}"));
    }
    match board.sample::<RouteTrace>(instrument::ROUTE) {
        Some(route) if !route.value.is_empty() => {
            for line in route_attribution_report_lines(&route.value) {
                lines.push(partial_line(&line));
            }
            note("route", route.sampled);
        }
        _ => lines.push(format!("; route unavailable: {reason}")),
    }

    if provenance.is_empty() {
        // Nothing was mirrored before the kill. Report exactly what this path
        // reported before any of it existed, rather than a header announcing
        // zero recovered instruments.
        return watchdog_unavailable_line(trace_mode, reason);
    }
    lines.insert(
        0,
        format!(
            "; partial at=watchdog-kill recovered={} sampled={} reason: {reason}",
            provenance.len(),
            provenance.join(",")
        ),
    );
    lines
}

/// Installs the progress sink (see the module header) on `config` when
/// `progress_mode` is set, returning the (possibly updated) config alongside
/// the receiver end. `progress_rx` outlives the `solve` closure built from the
/// returned config (which moves `config`, and with it the sender), so
/// whatever was sent before `solve()` returns is still there for the caller to
/// drain and print afterward — no extra thread or join needed for that
/// ordering. When `progress_mode` is `false` the channel is still created (so
/// both branches return the same types) but never wired to `config`, so
/// `progress_rx.try_iter()` is simply always empty — a silent no-op, exactly
/// like every other lever in this file when its flag is off.
fn install_progress_sink(
    mut config: SolverConfig,
    progress_mode: bool,
) -> (
    SolverConfig,
    mpsc::Receiver<axeyum_cnf::ProofSearchProgress>,
) {
    let (progress_tx, progress_rx) = mpsc::channel();
    if progress_mode {
        let interval = std::env::var("AXEYUM_PROOF_PROGRESS_INTERVAL")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(axeyum_cnf::DEFAULT_PROGRESS_CONFLICT_INTERVAL);
        config = config.with_proof_progress(ProofProgress::new(interval, progress_tx));
    }
    (config, progress_rx)
}

/// Default step cadence between checking-stage snapshots (see
/// [`checking_report_line`]), when `--progress` is on and
/// `AXEYUM_CHECK_PROGRESS_INTERVAL` does not override it. Both checking
/// sub-stages (`axeyum_cnf::check_drat` and `axeyum_cnf::elaborate_drat_to_lrat`)
/// use the same cadence — see [`axeyum_solver::CheckProgress`].
const DEFAULT_CHECK_PROGRESS_INTERVAL: usize = 50_000;

/// Formats one `axeyum_solver::CheckingProgress` snapshot as a `; checking …`
/// line — the checking-stage counterpart of [`progress_report_line`], and the
/// direct answer to "is `check_drat` or `elaborate_drat_to_lrat` the one
/// eating the time": each line names its own `stage`, so the two are never
/// conflated in the output the way they were indistinguishable before this
/// existed (search finishes, then silence, then — unlabelled — the checking
/// stage). A distinct leading token (`; checking` vs `; progress`) rather than
/// reusing `; progress` with a `stage=` field, so the two families are
/// trivially separable with `grep '^; checking '` / `grep '^; progress '`
/// without parsing fields first. Same convention otherwise: `;`-prefixed, so
/// this can never match `^(sat|unsat)$` / `^unknown$`.
#[allow(clippy::cast_precision_loss)]
fn checking_report_line(event: &CheckingProgress) -> String {
    let (stage, steps, total, extra, elapsed) = match event {
        CheckingProgress::DratCheck(snapshot) => (
            "drat_check",
            snapshot.steps_checked,
            snapshot.steps_total,
            format!("active_clauses={}", snapshot.active_clauses),
            snapshot.elapsed,
        ),
        CheckingProgress::LratElaborate(snapshot) => (
            "lrat_elaborate",
            snapshot.steps_processed,
            Some(snapshot.steps_total),
            format!(
                "active_clauses={} lrat_steps={}",
                snapshot.active_clauses, snapshot.lrat_steps_emitted
            ),
            snapshot.elapsed,
        ),
        // The backward LRAT certification stage (ADR-0613) is not
        // step-interruptible, so it reports exactly twice — once opening, once
        // closing. `steps` is therefore 0 or `steps_total`, which is what makes
        // the derived `steps_per_sec` meaningful on the closing line and zero on
        // the opening one, rather than a rate over a partial scan.
        CheckingProgress::BackwardLratCertify(snapshot) => (
            "backward_lrat_certify",
            if snapshot.finished {
                snapshot.steps_total
            } else {
                0
            },
            Some(snapshot.steps_total),
            format!(
                "finished={} certified={}",
                snapshot.finished, snapshot.certified
            ),
            snapshot.elapsed,
        ),
    };
    let elapsed_secs = elapsed.as_secs_f64();
    let steps_per_sec = if elapsed_secs > 0.0 {
        steps as f64 / elapsed_secs
    } else {
        0.0
    };
    let total = total.map_or_else(|| "?".to_owned(), |t| t.to_string());
    format!(
        "; checking stage={stage} steps={steps} total={total} {extra} elapsed_ms={} \
         steps_per_sec={steps_per_sec:.1}",
        elapsed.as_millis(),
    )
}

/// Installs the checking-stage progress/bound sink (see
/// [`checking_report_line`] and the module header's Progress mode section) on
/// `config` when `progress_mode` is set — the same flag
/// [`install_progress_sink`] reads, so `--progress` observes BOTH stages: the
/// proof-producing search (already covered) and, now, the DRAT check +
/// LRAT elaboration that run after it on `unsat` (the stage the motivating
/// incident actually got stuck in — the search returned in 24.2 s; checking
/// ran for ~6 h with zero output). Same "always create the channel, only wire
/// it up when the flag is on" shape as [`install_progress_sink`], for the same
/// reason: both branches return the same types, and `check_progress_rx` is a
/// silent no-op when `progress_mode` is `false`.
///
/// `AXEYUM_CHECK_STEP_LIMIT`, if set, bounds each checking sub-stage by step
/// count in addition to whatever wall-clock deadline `--timeout-ms` implies
/// (checking inherits the search's deadline — see
/// `axeyum_solver::proof::CheckBudget`). Unset (the default) means checking is
/// bounded only by that wall clock, exactly like the search's own
/// conflict budget is unrelated to its deadline.
fn install_check_progress_sink(
    mut config: SolverConfig,
    progress_mode: bool,
) -> (SolverConfig, mpsc::Receiver<CheckingProgress>) {
    let (check_tx, check_rx) = mpsc::channel();
    if progress_mode {
        let interval = std::env::var("AXEYUM_CHECK_PROGRESS_INTERVAL")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(DEFAULT_CHECK_PROGRESS_INTERVAL);
        let max_steps = std::env::var("AXEYUM_CHECK_STEP_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok());
        config = config.with_check_progress(CheckProgress::new(interval, max_steps, check_tx));
    }
    (config, check_rx)
}

/// Extra wall clock the watchdog allows past the configured timeout, so the
/// solver's own soft stop always wins the race when it can see the deadline.
const WATCHDOG_GRACE: Duration = Duration::from_secs(1);
/// Worker stack, sized like `axeyum-bench`'s pool: a deeply-nested input must
/// not turn a timeout into a stack-overflow abort (`deep_nesting_no_abort`).
const WORKER_STACK_BYTES: usize = 512 * 1024 * 1024;

/// One `; evidence …` report line for a produced [`Evidence`], plus the verdict
/// it justifies.
///
/// `certified` is [`Evidence::is_certified`]: the result carries a checkable
/// certificate object rather than a bare verdict. `recheck` is the stronger,
/// consumer-side claim — this process re-validated the certificate from its own
/// serialized text with no access to the solver that produced it:
///
/// * `ok`   — re-checked here and it holds.
/// * `FAIL` — a certificate is attached but does NOT re-check. A soundness alarm;
///   it is reported, never swallowed.
/// * `na`   — no text-only re-check is available for this evidence kind from this
///   process (the certificate's checker needs the term arena, which the
///   text front door does not hand back). Deliberately NOT counted as a
///   success: the whole point is to stop overstating coverage.
///
/// `arena` is the SECOND, weaker-but-broader re-validation, reported as its own
/// field so it can never be mistaken for `recheck`. Most certificate kinds have
/// no serialized form at all — their checker ([`Evidence::check`]) needs the term
/// arena — so `recheck` reports `na` for them and the `QF_BV` board records the
/// gap directly: `certified 92/130 = 70.8 %` against `re-checked here (text-only)
/// 78/130 = 60.0 %`. Those 14 files are not uncheckable, only un-*text*-checkable:
/// the arena is recoverable by RE-PARSING the original file, which is what this
/// field does. It is a genuinely independent check — the fresh parse shares no
/// state with the producing solve — but it is weaker than `recheck` because it
/// re-runs our own checker against our own re-parse rather than replaying a
/// serialized artifact the way an external `drat-trim` would. Two fields, two
/// claims; neither is allowed to borrow the other's strength.
///
/// * `ok`   — the certificate re-validated against a fresh parse of the file.
/// * `FAIL` — a certificate was present and did NOT re-validate. A soundness
///   alarm, reported and never swallowed. This value means the producer and the
///   checker disagree, and nothing else.
/// * `none:<reason>` — there was nothing to re-validate, with the reason named
///   (`none:uncertified-unsat`, `none:undecided`, `none:empty-subject`,
///   `none:unfaithful-subject`). Not a pass and NOT a failure. This field used to
///   print `FAIL` here, because it read [`Evidence::check`], whose `Ok(false)`
///   means both "examined and failed" and "nothing to examine". A bare
///   `Evidence::Unsat(None)` therefore rendered as a soundness alarm on a run
///   where the solver was correct and merely uncertified — and an evidence
///   dashboard built on this string counted absence as failure.
/// * `na`   — the file did not re-parse, or the checker errored (an unbounded
///   re-enumeration, a certificate that will not re-read). Never a success.
fn evidence_report_line(
    input: &str,
    report: &EvidenceReport,
    elapsed_ms: u128,
) -> (&'static str, String) {
    let evidence = &report.evidence;
    let verdict = match evidence {
        Evidence::Sat(_) => "sat",
        Evidence::Unknown(_) => "unknown",
        // Every remaining variant is an `unsat`-family certificate.
        _ => "unsat",
    };
    // Arena-free, self-contained re-validation. Today that is:
    //   * the DRAT/LRAT clausal certificate — `UnsatProof::recheck` re-parses the
    //     DIMACS and the refutation and re-derives the empty clause (RUP+RAT),
    //     exactly what an external `drat-trim` run does; and
    //   * the Alethe refutation — `check_alethe` replays every step, including the
    //     `bitblast_*` steps, so the bit-blast reduction is re-derived too.
    // Everything else needs the term arena the text front door does not return, so
    // it reports `na` rather than being counted as verified.
    let recheck = match evidence {
        Evidence::Unsat(Some(proof)) => match proof.recheck() {
            Ok(true) => "ok",
            _ => "FAIL",
        },
        Evidence::UnsatAletheProof(proof) => match axeyum_cnf::check_alethe(proof) {
            Ok(true) => "ok",
            _ => "FAIL",
        },
        _ => "na",
    };
    // Arena-backed re-validation against a FRESH PARSE of the original file. The
    // producing solve's arena is deliberately not reused — re-reading the file is
    // what makes this independent of anything that run kept in memory.
    //
    // Read through `check_outcome`, NOT `check`. The boolean form collapses "a
    // certificate was examined and FAILED" and "there was no certificate to
    // examine" onto the same `Ok(false)`, and this line rendered both as `FAIL`
    // — so a bare `Evidence::Unsat(None)` printed `arena=FAIL`, which reads as a
    // soundness alarm when the truth is an absence. `EvidenceCheck` already draws
    // that distinction correctly; only this caller threw it away.
    let arena = match evidence {
        Evidence::Unknown(_) => "na".to_owned(),
        _ => match axeyum_smtlib::parse_script(input) {
            Ok(script) => match evidence.check_outcome(&script.arena, &script.assertions) {
                Ok(EvidenceCheck::Verified) => "ok".to_owned(),
                // The only value that is a soundness alarm: producer and checker
                // disagree about a certificate that was actually present.
                Ok(EvidenceCheck::Failed) => "FAIL".to_owned(),
                // Nothing was re-derived, and the reason is carried rather than
                // flattened — `none:uncertified-unsat` and `none:unfaithful-subject`
                // are different findings and neither is a failure.
                Ok(EvidenceCheck::NothingToCheck(reason)) => format!("none:{}", reason.label()),
                // A checker that ERRORS has not validated anything; `na`, never `ok`.
                Err(_) => "na".to_owned(),
            },
            Err(_) => "na".to_owned(),
        },
    };
    let certified = u8::from(evidence.is_certified() && verdict != "unknown");
    (
        verdict,
        format!(
            "; evidence kind={} certified={certified} trusted={} recheck={recheck} arena={arena} ms={elapsed_ms}",
            evidence.kind_label(),
            trusted_field(&report.trusted_steps)
        ),
    )
}

/// The `trusted=` field: how many reductions this result depended on, and which.
///
/// **Why it exists.** The ledger a decision arrives with was invisible from a
/// sweep. This line printed `kind=`, `certified=`, `recheck=` and `arena=`, and
/// [`EvidenceReport::trusted_steps`] — the list of reductions the result leaned
/// on and whether THIS run certified each — appeared nowhere, so
/// "how many refutations carry an ADR-1704 theory step" could only be asserted
/// per query from a test, never counted across a division. A metric that cannot
/// be read at corpus scale is not a metric.
///
/// **Where it goes, and why not at the end.** Between `certified=` and
/// `recheck=`. `scripts/execute-autogenesis-operation.py` parses this line with
/// an ANCHORED regex, `recheck=(\S+)\s+arena=(\S+)\s+ms=(\d+)\s*$`, so a
/// field appended after `ms=` stops that parser dead; the shell consumers
/// (`parity-run.sh`, `check-evidence-portability.sh`) use greedy
/// `.*<key>=\([^ ]*\)` seds, which are unaffected wherever it goes. One
/// position satisfies all three.
///
/// **Format.** `trusted=0` when nothing was leaned on, otherwise
/// `trusted=<n>:<label>[+][,<label>[+]]` with the labels in the report's own
/// order and `+` marking a step this run certified. One whitespace-free token,
/// so every `[^ ]*` extraction keeps working.
fn trusted_field(steps: &[axeyum_solver::trust::TrustStep]) -> String {
    if steps.is_empty() {
        return "0".to_owned();
    }
    let names: Vec<String> = steps
        .iter()
        .map(|step| {
            let mark = if step.certified { "+" } else { "" };
            format!("{}{mark}", step.id.label())
        })
        .collect();
    format!("{}:{}", steps.len(), names.join(","))
}

/// Parsed command-line/env-var configuration: which file to solve, and every
/// off-by-default lever this binary exposes. Split out of `main` purely to
/// keep it under clippy's line-count lint.
struct CliArgs {
    path: Option<String>,
    timeout_ms: Option<u64>,
    /// `SolverConfig::memory_limit_mb`. Off by default, exactly like every other
    /// lever here, so `scripts/parity-run.sh`'s invocation stays the shipped
    /// configuration. It exists because ADR-1752 made that field the online LRA
    /// construction budget, and a budget nobody can set from the command line
    /// cannot be calibrated or reproduced.
    memory_limit_mb: Option<u64>,
    evidence_mode: bool,
    progress_mode: bool,
    trace_mode: bool,
}

fn parse_cli_args() -> CliArgs {
    let mut args = CliArgs {
        path: None,
        timeout_ms: std::env::var("AXEYUM_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.parse().ok()),
        memory_limit_mb: std::env::var("AXEYUM_MEMORY_LIMIT_MB")
            .ok()
            .and_then(|v| v.parse().ok()),
        evidence_mode: std::env::var("AXEYUM_EVIDENCE").is_ok_and(|v| v == "1"),
        progress_mode: std::env::var("AXEYUM_PROOF_PROGRESS").is_ok_and(|v| v == "1"),
        trace_mode: std::env::var("AXEYUM_TRACE").is_ok_and(|v| v == "1"),
    };
    let mut rest = std::env::args().skip(1);
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--timeout-ms" => {
                args.timeout_ms = rest.next().and_then(|v| v.parse().ok());
            }
            "--memory-limit-mb" => {
                args.memory_limit_mb = rest.next().and_then(|v| v.parse().ok());
            }
            "--evidence" => args.evidence_mode = true,
            "--progress" => args.progress_mode = true,
            "--trace" => args.trace_mode = true,
            other if other.starts_with("--") => {
                // Ignore unknown flags: the competition passes only the file.
            }
            other => {
                if args.path.is_none() {
                    args.path = Some(other.to_string());
                }
            }
        }
    }
    args
}

#[allow(clippy::too_many_lines)] // linear CLI driver: arg parsing + solve dispatch + watchdog
fn main() -> ExitCode {
    let CliArgs {
        path,
        timeout_ms,
        memory_limit_mb,
        evidence_mode,
        progress_mode,
        trace_mode,
    } = parse_cli_args();

    let Some(path) = path else {
        eprintln!("usage: smtcomp_cli <benchmark.smt2> [--timeout-ms N] [--memory-limit-mb N]");
        return ExitCode::from(2);
    };

    let input = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("read error: {e}");
            return ExitCode::from(2);
        }
    };

    let mut config = SolverConfig::new();
    if let Some(ms) = timeout_ms {
        config = config.with_timeout(Duration::from_millis(ms));
    }
    if let Some(mb) = memory_limit_mb {
        config = config.with_memory_limit_mb(mb);
    }

    // A/B levers for head-to-head probing, OFF unless explicitly asked for, so
    // the default invocation `scripts/parity-run.sh` uses stays exactly the
    // shipped configuration and recorded baselines keep their meaning.
    //
    // `cnf_inprocessing` (subsumption + BVE) and `cnf_vivify` already exist in
    // `axeyum-cnf` and are sound (model-preserving / equisatisfiable with a
    // reconstruction stack, and every `sat` is still replay-checked against the
    // original terms) — but `cnf_inprocessing` defaults to `false`, and this
    // binary had no way to turn it on, so EVERY parity measurement to date ran
    // with these passes off. (`cnf_vivify` has defaulted to `true` since
    // 2026-09-08; it is a no-op while `cnf_inprocessing` is `false`, which is
    // why the baseline is unaffected.)
    // The 2026-07-07 gap analysis puts ~9 of the residual QF_BV files in the
    // "search-bound" bucket, which is exactly what these passes target, and it
    // says the first step there is a MEASUREMENT, not a build. This makes that
    // measurement a one-line env change instead of a code edit.
    let enabled = |name: &str| std::env::var(name).is_ok_and(|v| v == "1");
    if enabled("AXEYUM_CNF_INPROCESSING") {
        config = config.with_cnf_inprocessing(true);
    }
    if enabled("AXEYUM_CNF_VIVIFY") {
        // A no-op unless inprocessing is also on; turn both on together so the
        // flag cannot silently do nothing.
        config = config.with_cnf_inprocessing(true).with_cnf_vivify(true);
    }
    // `cnf_vivify` defaults to TRUE as of 2026-09-08 (measured: with BVE under
    // its work budget, vivification is cheaper AND shrinks more —
    // `docs/research/03-measurements/inprocessing-admission-2026-09-08.md`), so
    // `AXEYUM_CNF_VIVIFY=1` above is now the same configuration as
    // `AXEYUM_CNF_INPROCESSING=1` alone. This is the off-switch that keeps the
    // un-vivified arm reachable, which a measurement comparing the two needs
    // and which no `=1` flag can express.
    if enabled("AXEYUM_CNF_NO_VIVIFY") {
        config = config.with_cnf_vivify(false);
    }

    let (config, progress_rx) = install_progress_sink(config, progress_mode);
    let (config, check_progress_rx) = install_check_progress_sink(config, progress_mode);

    // The configured timeout is a SOFT stop: the deadline is polled inside the
    // solve, but NOT during SMT-LIB ingest (parsing `stp/testcase15.stp.smt2`,
    // 58 MB, alone takes ~54 s). With only the soft stop, the harness's external
    // `timeout` killed the process mid-parse and no verdict was ever printed —
    // an abort, which is strictly worse than the first-class `unknown` a
    // resource-exhausted solver owes its caller.
    //
    // So run the whole pipeline — ingest included — on a worker thread and let
    // the main thread enforce the wall clock. The grace period keeps the normal
    // path byte-identical: when the internal soft stop fires (it returns at
    // ~`timeout_ms`), it always wins the race, and this watchdog only speaks for
    // the stages the soft stop cannot see.
    //
    // The worker gets an explicit large stack for the same reason
    // `axeyum-bench`'s pool does: a deeply-nested input must not turn a timeout
    // into a stack-overflow abort (see `deep_nesting_no_abort`), and a spawned
    // thread's default stack is far smaller than the main thread's.
    //
    // The second element is the optional `; evidence …` report line: `None` on
    // the DEFAULT path, so the default invocation `scripts/parity-run.sh` uses
    // stays byte-identical output and every recorded baseline keeps its meaning.
    //
    // The third element is every `--trace` report line that applies (see the
    // module header's "Theory-route stage attribution" and "BV-layer stage
    // attribution" sections), in front-door/dispatch/backend order: empty
    // unless `trace_mode` is set, so — like every other lever here — a
    // default run's output is unaffected byte-for-byte. At most one of
    // `; bv-layer …` / `; theory-layer …` prints per query (a `sat-bv`
    // decide never runs the CDCL(T) driver and vice versa), but
    // `; front-door …` and `; dl-online …` are independent stages that can
    // coexist with either.
    // The cross-thread instrument board (`axeyum_solver::live_instruments`).
    // Created HERE, on the thread that enforces the wall clock, so it outlives
    // the worker: a watchdog timeout reads it after giving up on a thread that
    // is still running and will never publish anything again. Installed inside
    // the closure below rather than here, because a thread-local install has to
    // happen on the thread that will do the publishing.
    let board = LiveInstruments::new();
    let worker_board = Arc::clone(&board);
    let solve = move || -> (&'static str, Option<String>, Vec<String>) {
        // The seventh lever on the same `--trace` flag, and the only one that
        // is not itself an instrument: it gives the other six somewhere to
        // publish that is not this thread's thread-local storage. Off without
        // `--trace`, so a default run installs nothing and every publish site
        // returns on one `bool` read.
        let _live_board = trace_mode.then(|| install_live_instruments(&worker_board));
        if evidence_mode {
            let started = Instant::now();
            // A parse or solver error is `unknown` here too — and an evidence run
            // that errors must not be silently scored as an uncertified decide.
            return match produce_evidence_smtlib(&input, &config) {
                Ok(report) => {
                    let (verdict, line) =
                        evidence_report_line(&input, &report, started.elapsed().as_millis());
                    (verdict, Some(line), Vec::new())
                }
                Err(_) => (
                    "unknown",
                    Some(format!(
                        "; evidence kind=unknown certified=0 trusted=0 recheck=na arena=na ms={}",
                        started.elapsed().as_millis()
                    )),
                    Vec::new(),
                ),
            };
        }
        // Each `_*_guard` collects its own stats for the dynamic extent of
        // `solve_smtlib` below when `--trace` is on; dropped (disarmed) right
        // after, restoring whatever this thread's setting was before. A
        // no-op when `trace_mode` is `false` — no extra clock read, for any
        // of the six (same convention every guard in this tree follows). The
        // count is stated because it has been stale twice: ADR-1760's route
        // guard and ADR-1762's config guard landed on the same day, each from a
        // lane that read "four" and left it.
        let _theory_guard = trace_mode.then(TheoryLayerStatsGuard::enable);
        let _bv_guard = trace_mode.then(BvLayerStatsGuard::enable);
        let _dl_guard = trace_mode.then(DlOnlineStatsGuard::enable);
        let _front_door_guard = trace_mode.then(FrontDoorStatsGuard::enable);
        // ADR-1760. Which route decided the file, and which route consumed the
        // budget.
        let _route_guard = trace_mode.then(RouteAttributionGuard::enable);
        // ADR-1762. The sixth guard on the same flag: which governing values
        // this run consulted, and which environment overrides were in force.
        let _config_guard = trace_mode.then(ConfigTraceGuard::enable);
        // The seventh guard on the same flag: what the over-bound UF+arithmetic
        // decision point did. A route that declines and hands back `Unknown`
        // with nothing after it is invisible in a verdict and nearly invisible
        // in a trail; `terminal_unknown` names it outright.
        let _uf_overbound_guard = trace_mode.then(UfArithOverboundStatsGuard::enable);
        // A parse or solver error is reported as `unknown` — never a wrong
        // verdict, and never a crash that the harness would read as an abort.
        let mut give_up: Option<String> = None;
        let verdict = match solve_smtlib(&input, &config) {
            Ok(outcome) => match outcome.result {
                CheckResult::Sat(_) => "sat",
                CheckResult::Unsat => "unsat",
                CheckResult::Unknown(reason) => {
                    // An `unknown` carries a first-class reason and this binary
                    // threw it away, so a resource refusal was indistinguishable
                    // from a search timeout in every recorded run. ADR-1752's
                    // budget refusal states its numbers in exactly this field.
                    if trace_mode {
                        give_up = Some(format!(
                            "; give-up kind={:?} detail={}",
                            reason.kind, reason.detail
                        ));
                    }
                    "unknown"
                }
            },
            Err(_) => "unknown",
        };
        let mut trace_lines = Vec::new();
        if trace_mode {
            // Parse always runs exactly once (or more, on a string-bound
            // ladder rung) per front-door call, so this line is unconditional
            // — unlike `; bv-layer …`/`; theory-layer …` (only the ONE
            // backend a query actually dispatched to ran) it is never
            // legitimately absent when `--trace` is on.
            // ADR-1762: the configuration this run used. Printed FIRST among
            // the stage lines because it is what the others have to be read
            // against — a stage timing means something different under a
            // different admission policy, and until this line existed nothing
            // in a run's own output said which one was in force.
            trace_lines.push(config_trace_line());
            trace_lines.push(front_door_report_line(&last_front_door_stats()));
            // `dispatch_difference_logic` runs on every numeric-featured
            // query ahead of the linear-arithmetic chain (probing whether the
            // query is difference-shaped), but NOT on e.g. a `QF_BV` query,
            // which never reaches that dispatch branch at all — the call
            // count (see `axeyum_solver::last_dl_online_stats`'s docs) is
            // what distinguishes that absence from "ran and cost nothing
            // measurable" (`total_ms=0`), which a bare duration cannot.
            let (dl_online_elapsed, dl_online_calls) = last_dl_online_stats();
            if dl_online_calls > 0 {
                trace_lines.push(dl_online_report_line(dl_online_elapsed.as_millis()));
            }
            if let Some(stats) = last_bv_layer_stats() {
                trace_lines.push(bv_layer_report_line(&stats));
            }
            if let Some(stats) = last_theory_layer_stats() {
                trace_lines.push(theory_layer_report_line(&stats));
            }
            // Only when the eager Ackermann bound actually fired on this query:
            // an all-zero line on every non-UF file would be noise, and the
            // absence of the line is itself the information "this decision point
            // was never reached".
            let uf_overbound = last_uf_arith_overbound_stats();
            if uf_overbound.engaged > 0 {
                trace_lines.push(uf_overbound.trace_line());
            }
            // Route attribution (ADR-1760) LAST, so a reader who scans to the
            // end of the `;` block finds the one line that names which route
            // decided the file and which route consumed the budget -- the two
            // questions every other line here can only be evidence for.
            trace_lines.extend(route_attribution_report_lines(&last_route_attribution()));
        }
        // ADR-1752: the budget-relative atom cap can refuse before any stage
        // runs, and that refusal names the count, the budget and the remedy.
        // It is prepended so a `--trace` reader sees WHY nothing else appears.
        if let Some(g) = give_up {
            trace_lines.insert(0, g);
        }
        (verdict, None, trace_lines)
    };

    let Some(ms) = timeout_ms else {
        // No wall clock configured: nothing to enforce, so stay on the main
        // thread (its stack is the largest one available).
        let (verdict, evidence, trace_lines) = solve();
        // Progress lines come FIRST: they describe the search that already
        // finished producing `verdict`/`evidence`, so printing them after
        // either would be out of order. Still strictly before the evidence
        // line and the verdict, both of which must stay exactly where the
        // rest of this file already puts them.
        for snapshot in progress_rx.try_iter() {
            println!("{}", progress_report_line(&snapshot));
        }
        // Checking-stage lines (see `install_check_progress_sink`) come right
        // after the search's own progress lines and before the evidence/verdict
        // lines, for the same reason: the stage they describe has already run
        // by the time `verdict`/`evidence` exist.
        for event in check_progress_rx.try_iter() {
            println!("{}", checking_report_line(&event));
        }
        for line in &trace_lines {
            println!("{line}");
        }
        if let Some(line) = evidence {
            println!("{line}");
        }
        println!("{verdict}");
        return ExitCode::SUCCESS;
    };

    let (tx, rx) = std::sync::mpsc::channel();
    let worker = std::thread::Builder::new()
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || {
            // A closed channel means the watchdog already answered; drop quietly.
            let _ = tx.send(solve());
        });
    // S2 dispatch-overrun fix (2026-09-05,
    // `docs/plan/smt-parity-plan-2026-09-05.md` row S2): a watchdog timeout used
    // to hardcode `("unknown", None, None)` regardless of `trace_mode`, so a
    // query whose internal dispatch ran past the watchdog printed NOTHING for
    // `--trace` — not even a stale partial stat — because the `; theory-layer …`
    // line is built only after the worker's `solve()` call returns
    // (`TheoryLayerStatsGuard`'s snapshot is thread-local to the worker thread,
    // per `crate::theories::cdclt_diagnostics`, so the main thread cannot read
    // a live in-progress snapshot without new cross-thread state). Three of
    // five traced `QF_IDL` timeouts hit exactly this path
    // (`docs/research/11-design-review/2026-09-05-arith-timeout-profiles.md`,
    // Finding 0). The first fix printed an explicit
    // `; theory-layer unavailable: <reason>` line so a trace was never silently
    // empty. That distinction is kept, but it is now the FALLBACK: the shared
    // cross-thread state it declined to add turned out to cost nothing
    // measurable (see `watchdog_unavailable_line`'s docs for the A/B), so
    // `watchdog_trace_lines` reports the counters the instruments mirrored
    // before the kill, under a `; partial …` token that cannot be mistaken for
    // a completed line.
    let (verdict, evidence, trace_lines) = match worker {
        Ok(_) => match rx.recv_timeout(Duration::from_millis(ms) + WATCHDOG_GRACE) {
            Ok(outcome) => outcome,
            Err(_) => (
                "unknown",
                None,
                watchdog_trace_lines(
                    trace_mode,
                    &board,
                    "watchdog fired before the worker thread returned",
                ),
            ),
        },
        // Could not spawn a worker: a resource failure, which is `unknown` —
        // never a guess and never a crash.
        Err(_) => (
            "unknown",
            None,
            watchdog_trace_lines(
                trace_mode,
                &board,
                "failed to spawn the solver worker thread",
            ),
        ),
    };

    // Progress lines first (see the no-timeout branch above for why), then the
    // evidence line, so the verdict stays the final line of stdout, exactly as
    // the competition interface promises. If the watchdog gave up before the
    // worker finished, this still prints whatever snapshots the search sent
    // before the timeout — an honest partial picture, not nothing.
    for snapshot in progress_rx.try_iter() {
        println!("{}", progress_report_line(&snapshot));
    }
    for event in check_progress_rx.try_iter() {
        println!("{}", checking_report_line(&event));
    }
    for line in &trace_lines {
        println!("{line}");
    }
    if let Some(line) = evidence {
        println!("{line}");
    }
    println!("{verdict}");
    // The worker may still be inside ingest; the verdict is already printed and
    // correct, so exit rather than block on a thread that has no deadline.
    std::io::Write::flush(&mut std::io::stdout()).ok();
    std::process::exit(0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn watchdog_unavailable_line_is_empty_off_trace_and_names_both_instruments_on_trace() {
        assert_eq!(
            watchdog_unavailable_line(false, "anything"),
            Vec::<String>::new(),
            "a default (non-trace) run's output must stay byte-identical"
        );
        let lines = watchdog_unavailable_line(
            true,
            "watchdog fired before the worker thread returned (no CDCL(T) search on this \
             query completed before the deadline)",
        );
        assert_eq!(
            lines.len(),
            2,
            "trace_mode=true must always yield a line, never nothing: got {lines:?}"
        );
        assert!(
            lines[0].starts_with("; theory-layer unavailable: "),
            "got: {}",
            lines[0]
        );
        // ADR-1760: the route line specifically. In the 1,200-file sweep, 96
        // files printed no route line and every one was `unsolved` — the exact
        // population the instrument exists to explain — so an aggregation must
        // be able to COUNT what it cannot attribute rather than silently
        // shrinking its denominator.
        assert!(
            lines[1].starts_with("; route unavailable: "),
            "got: {}",
            lines[1]
        );
        for line in &lines {
            assert!(line.contains("watchdog fired"), "got: {line}");
            assert!(
                line.starts_with("; "),
                "every trace line must be an SMT-LIB comment so it can never \
                 match ^(sat|unsat)$: got {line}"
            );
        }
    }

    /// End-to-end regression for the actual race in `main`: a worker that
    /// never answers before `recv_timeout` gives up must still, when
    /// `--trace` is set, produce SOME `; theory-layer …` line — never
    /// nothing (the measured defect,
    /// `docs/research/11-design-review/2026-09-05-arith-timeout-profiles.md`
    /// Finding 0: three of five traced `QF_IDL` timeouts printed nothing at
    /// all). This exercises the identical `mpsc` + `recv_timeout` shape
    /// `main` uses — a worker that outlives the deadline — not a synthetic
    /// solver: the fix lives entirely in what happens when `recv_timeout`
    /// returns `Err`, which is exactly what this reproduces.
    #[test]
    fn a_worker_that_outlives_the_deadline_still_yields_a_theory_layer_line() {
        let (tx, rx) = std::sync::mpsc::channel::<(&'static str, Option<String>, Vec<String>)>();
        let _worker = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(2));
            let _ = tx.send(("unknown", None, Vec::new()));
        });
        let trace_mode = true;
        let (verdict, _evidence, trace_lines) = match rx.recv_timeout(Duration::from_millis(10)) {
            Ok(outcome) => outcome,
            Err(_) => (
                "unknown",
                None,
                watchdog_unavailable_line(
                    trace_mode,
                    "watchdog fired before the worker thread returned (no CDCL(T) \
                     search on this query completed before the deadline)",
                ),
            ),
        };
        assert_eq!(verdict, "unknown");
        assert_eq!(
            trace_lines.len(),
            2,
            "a timed-out solve with --trace must still print both unavailable \
             lines, never nothing: got {trace_lines:?}"
        );
        assert!(
            trace_lines[0].starts_with("; theory-layer"),
            "got: {}",
            trace_lines[0]
        );
        // ADR-1760: the route line must survive the watchdog path too. This is
        // the ONLY signal a hard-timeout file gives about attribution, and the
        // 1,200-file sweep found 96 such files -- all of them `unsolved`, which
        // is precisely the population the instrument exists to explain.
        assert!(
            trace_lines[1].starts_with("; route unavailable"),
            "got: {}",
            trace_lines[1]
        );
    }

    /// A board nothing published to yields exactly what this path yielded
    /// before any of the mirroring existed — so "the search never got far
    /// enough to instrument anything" stays distinguishable from "collection
    /// was off" (no lines at all).
    #[test]
    fn an_empty_board_falls_back_to_the_unavailable_lines() {
        let board = LiveInstruments::new();
        assert_eq!(
            watchdog_trace_lines(false, &board, "anything"),
            Vec::<String>::new(),
            "a default (non-trace) run's output must stay byte-identical"
        );
        assert_eq!(
            watchdog_trace_lines(true, &board, "watchdog fired"),
            watchdog_unavailable_line(true, "watchdog fired"),
        );
    }

    /// The test that matters: a worker abandoned by the watchdog, whose
    /// instruments mirrored something before the kill, reports that something —
    /// and reports it as PARTIAL.
    ///
    /// The worker below is still blocked when the lines are built, exactly as a
    /// real one is: `recv_timeout` has expired and the thread has published
    /// nothing on its way out because it has no way out yet.
    #[test]
    fn an_abandoned_worker_reports_partial_counters_under_a_distinct_token() {
        let board = LiveInstruments::new();
        let worker_board = Arc::clone(&board);
        let (tx, rx) = std::sync::mpsc::channel::<(&'static str, Option<String>, Vec<String>)>();
        let (published_tx, published_rx) = std::sync::mpsc::channel::<()>();
        let (release_tx, release_rx) = std::sync::mpsc::channel::<()>();
        let _worker = std::thread::spawn(move || {
            let _live = install_live_instruments(&worker_board);
            let stats = axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats {
                decisions: 4_242,
                boolean_propagate: Duration::from_millis(17),
                ..Default::default()
            };
            axeyum_solver::publish_live(instrument::THEORY_LAYER, stats, Sampled::InFlight);
            published_tx.send(()).expect("receiver alive");
            let _ = release_rx.recv();
            let _ = tx.send(("unknown", None, Vec::new()));
        });
        published_rx
            .recv()
            .expect("the worker mirrored its counters");

        let (verdict, _evidence, trace_lines) = match rx.recv_timeout(Duration::from_millis(10)) {
            Ok(outcome) => outcome,
            Err(_) => (
                "unknown",
                None,
                watchdog_trace_lines(true, &board, "watchdog fired"),
            ),
        };
        assert_eq!(verdict, "unknown");

        let joined = trace_lines.join("\n");
        assert!(
            joined.contains("decisions=4242"),
            "the counters the worker mirrored must come back: {joined}"
        );
        // The distinct leading token is the labelling: a consumer that greps
        // `^; theory-layer ` for complete lines must not pick this up, because
        // a truncated count that reads like a complete one is worse than none.
        assert!(
            trace_lines
                .iter()
                .any(|l| l.starts_with("; partial theory-layer ")),
            "{trace_lines:?}"
        );
        assert!(
            !trace_lines.iter().any(|l| l.starts_with("; theory-layer ")),
            "no partial reading may wear the complete line's token: {trace_lines:?}"
        );
        assert!(
            trace_lines[0].starts_with("; partial at=watchdog-kill "),
            "the header says where the reading was taken: {}",
            trace_lines[0]
        );
        assert!(
            trace_lines[0].contains("theory-layer:in-flight"),
            "and that this instrument was still running: {}",
            trace_lines[0]
        );
        // The route mirrored nothing, so it keeps saying so rather than being
        // silently dropped from a partial report.
        assert!(
            trace_lines
                .iter()
                .any(|l| l.starts_with("; route unavailable: ")),
            "{trace_lines:?}"
        );
        for line in &trace_lines {
            assert!(
                line.starts_with("; "),
                "every trace line must be an SMT-LIB comment so it can never \
                 match ^(sat|unsat)$: got {line}"
            );
        }
        let _ = release_tx.send(());
    }

    /// A stage that finished is still reported under the partial token: the
    /// QUERY did not return even when one of its stages did, so nothing on this
    /// path may look like a normal-return line. The header carries the
    /// distinction instead.
    #[test]
    fn a_stage_that_completed_is_still_reported_under_the_partial_token() {
        let board = LiveInstruments::new();
        board.publish(
            instrument::DL_ONLINE,
            (Duration::from_millis(931), 2_u64),
            Sampled::Complete,
        );
        let lines = watchdog_trace_lines(true, &board, "watchdog fired");
        assert!(
            lines
                .iter()
                .any(|l| l == "; partial dl-online total_ms=931"),
            "{lines:?}"
        );
        assert!(
            lines[0].contains("dl-online:complete"),
            "the header distinguishes a finished stage from a mid-flight one: {}",
            lines[0]
        );
        assert!(
            !lines.iter().any(|l| l.starts_with("; dl-online ")),
            "{lines:?}"
        );
    }

    /// `partial_line` re-labels rather than rewrites: the body of the line is
    /// byte-identical to what a completed run prints, which is what lets one
    /// parser read both families.
    #[test]
    fn partial_line_only_replaces_the_leading_token() {
        assert_eq!(
            partial_line("; route-trail {\"schema\":1}"),
            "; partial route-trail {\"schema\":1}"
        );
        assert_eq!(partial_line("no prefix"), "; partial no prefix");
    }
}
