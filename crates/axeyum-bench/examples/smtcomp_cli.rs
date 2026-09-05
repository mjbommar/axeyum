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
//! ; evidence kind=unsat-drat certified=1 recheck=ok arena=ok ms=412
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
//!   theory_propagations=8842 decisions=4201 restarts=6
//! ```
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

use std::process::ExitCode;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use axeyum_solver::theories::cdclt_diagnostics::{TheoryLayerStatsGuard, last_theory_layer_stats};
use axeyum_solver::{
    CheckProgress, CheckResult, CheckingProgress, Evidence, EvidenceCheck, ProofProgress,
    SolverConfig, produce_evidence_smtlib, solve_smtlib,
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
    stats: axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStats,
) -> String {
    format!(
        "; theory-layer boolean_propagate_ms={} theory_assert_ms={} theory_propagate_ms={} \
         theory_push_pop_ms={} conflict_analysis_ms={} theory_conflicts={} \
         theory_propagations={} decisions={} restarts={}",
        stats.boolean_propagate.as_millis(),
        stats.theory_assert.as_millis(),
        stats.theory_propagate.as_millis(),
        stats.theory_push_pop.as_millis(),
        stats.conflict_analysis.as_millis(),
        stats.theory_conflicts,
        stats.theory_propagations,
        stats.decisions,
        stats.restarts,
    )
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
    evidence: &Evidence,
    elapsed_ms: u128,
) -> (&'static str, String) {
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
            "; evidence kind={} certified={certified} recheck={recheck} arena={arena} ms={elapsed_ms}",
            evidence.kind_label()
        ),
    )
}

/// Parsed command-line/env-var configuration: which file to solve, and every
/// off-by-default lever this binary exposes. Split out of `main` purely to
/// keep it under clippy's line-count lint.
struct CliArgs {
    path: Option<String>,
    timeout_ms: Option<u64>,
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
        evidence_mode,
        progress_mode,
        trace_mode,
    } = parse_cli_args();

    let Some(path) = path else {
        eprintln!("usage: smtcomp_cli <benchmark.smt2> [--timeout-ms N]");
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

    // A/B levers for head-to-head probing, OFF unless explicitly asked for, so
    // the default invocation `scripts/parity-run.sh` uses stays exactly the
    // shipped configuration and recorded baselines keep their meaning.
    //
    // `cnf_inprocessing` (subsumption + BVE) and `cnf_vivify` already exist in
    // `axeyum-cnf` and are sound (model-preserving / equisatisfiable with a
    // reconstruction stack, and every `sat` is still replay-checked against the
    // original terms) — but they default to `false`, and this binary had no way
    // to turn them on, so EVERY parity measurement to date ran with them off.
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
    // The third element is the optional `; theory-layer …` report line (see
    // the module header's `--trace` section): `None` unless `trace_mode` is
    // set AND a CDCL(T) route decided the query, so — like every other lever
    // here — a default run's output is unaffected byte-for-byte.
    let solve = move || -> (&'static str, Option<String>, Option<String>) {
        if evidence_mode {
            let started = Instant::now();
            // A parse or solver error is `unknown` here too — and an evidence run
            // that errors must not be silently scored as an uncertified decide.
            return match produce_evidence_smtlib(&input, &config) {
                Ok(report) => {
                    let (verdict, line) = evidence_report_line(
                        &input,
                        &report.evidence,
                        started.elapsed().as_millis(),
                    );
                    (verdict, Some(line), None)
                }
                Err(_) => (
                    "unknown",
                    Some(format!(
                        "; evidence kind=unknown certified=0 recheck=na arena=na ms={}",
                        started.elapsed().as_millis()
                    )),
                    None,
                ),
            };
        }
        // `_guard` collects `TheoryLayerStats` for the dynamic extent of
        // `solve_smtlib` below when `--trace` is on; dropped (disarmed) right
        // after, restoring whatever this thread's setting was before. A
        // no-op when `trace_mode` is `false` — no extra clock read.
        let _guard = trace_mode.then(TheoryLayerStatsGuard::enable);
        // A parse or solver error is reported as `unknown` — never a wrong
        // verdict, and never a crash that the harness would read as an abort.
        let verdict = match solve_smtlib(&input, &config) {
            Ok(outcome) => match outcome.result {
                CheckResult::Sat(_) => "sat",
                CheckResult::Unsat => "unsat",
                CheckResult::Unknown(_) => "unknown",
            },
            Err(_) => "unknown",
        };
        let trace_line = trace_mode
            .then(last_theory_layer_stats)
            .flatten()
            .map(theory_layer_report_line);
        (verdict, None, trace_line)
    };

    let Some(ms) = timeout_ms else {
        // No wall clock configured: nothing to enforce, so stay on the main
        // thread (its stack is the largest one available).
        let (verdict, evidence, trace_line) = solve();
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
        if let Some(line) = trace_line {
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
    let (verdict, evidence, trace_line) = match worker {
        Ok(_) => rx
            .recv_timeout(Duration::from_millis(ms) + WATCHDOG_GRACE)
            .unwrap_or(("unknown", None, None)),
        // Could not spawn a worker: a resource failure, which is `unknown` —
        // never a guess and never a crash.
        Err(_) => ("unknown", None, None),
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
    if let Some(line) = trace_line {
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
