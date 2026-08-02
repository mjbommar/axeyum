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
//! ; evidence kind=unsat-drat certified=1 recheck=ok ms=412
//! ```
//!
//! The line starts with `;` (the SMT-LIB comment character) and can never match
//! `^(sat|unsat)$`, so a harness that greps the verdict is unaffected. This is
//! what makes "Lean parity" — *every `unsat` carries a machine-checkable proof* —
//! a per-file MEASUREMENT instead of an essay: `certified=1` means the result
//! carries an independently checkable certificate object, and `recheck=ok` means
//! this process re-validated that certificate **from its serialized text alone**
//! (`UnsatProof::recheck`: re-parse the DIMACS + DRAT/LRAT and re-derive the
//! empty clause), which is exactly what an external `drat-trim` would do.
//!
//! Off by default on purpose: producing and re-checking a proof costs real time
//! on top of deciding, so turning it on silently would invalidate every recorded
//! parity baseline. Same discipline as `AXEYUM_CNF_INPROCESSING` /
//! `AXEYUM_CNF_VIVIFY` below.

use std::process::ExitCode;
use std::time::{Duration, Instant};

use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence_smtlib, solve_smtlib};

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
fn evidence_report_line(evidence: &Evidence, elapsed_ms: u128) -> (&'static str, String) {
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
    let certified = u8::from(evidence.is_certified() && verdict != "unknown");
    (
        verdict,
        format!(
            "; evidence kind={} certified={certified} recheck={recheck} ms={elapsed_ms}",
            evidence.kind_label()
        ),
    )
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut path: Option<String> = None;
    let mut timeout_ms: Option<u64> = std::env::var("AXEYUM_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok());
    let mut evidence_mode = std::env::var("AXEYUM_EVIDENCE").is_ok_and(|v| v == "1");

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--timeout-ms" => {
                timeout_ms = args.next().and_then(|v| v.parse().ok());
            }
            "--evidence" => evidence_mode = true,
            other if other.starts_with("--") => {
                // Ignore unknown flags: the competition passes only the file.
            }
            other => {
                if path.is_none() {
                    path = Some(other.to_string());
                }
            }
        }
    }

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
    let solve = move || -> (&'static str, Option<String>) {
        if evidence_mode {
            let started = Instant::now();
            // A parse or solver error is `unknown` here too — and an evidence run
            // that errors must not be silently scored as an uncertified decide.
            return match produce_evidence_smtlib(&input, &config) {
                Ok(report) => {
                    let (verdict, line) =
                        evidence_report_line(&report.evidence, started.elapsed().as_millis());
                    (verdict, Some(line))
                }
                Err(_) => (
                    "unknown",
                    Some(format!(
                        "; evidence kind=unknown certified=0 recheck=na ms={}",
                        started.elapsed().as_millis()
                    )),
                ),
            };
        }
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
        (verdict, None)
    };

    let Some(ms) = timeout_ms else {
        // No wall clock configured: nothing to enforce, so stay on the main
        // thread (its stack is the largest one available).
        let (verdict, evidence) = solve();
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
    let (verdict, evidence) = match worker {
        Ok(_) => rx
            .recv_timeout(Duration::from_millis(ms) + WATCHDOG_GRACE)
            .unwrap_or(("unknown", None)),
        // Could not spawn a worker: a resource failure, which is `unknown` —
        // never a guess and never a crash.
        Err(_) => ("unknown", None),
    };

    // The evidence line goes FIRST so the verdict stays the final line of stdout,
    // exactly as the competition interface promises.
    if let Some(line) = evidence {
        println!("{line}");
    }
    println!("{verdict}");
    // The worker may still be inside ingest; the verdict is already printed and
    // correct, so exit rather than block on a thread that has no deadline.
    std::io::Write::flush(&mut std::io::stdout()).ok();
    std::process::exit(0);
}
