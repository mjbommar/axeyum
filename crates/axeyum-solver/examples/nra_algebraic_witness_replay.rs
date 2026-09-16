//! Replay each `sat` the ADR-2134 lever gains, INDEPENDENTLY, and make the exit
//! status depend on the answer.
//!
//! # Why this exists
//!
//! The lever's A/B gains four `QF_NRA` files, every one of them `unknown → sat`.
//! "The route replayed the model before emitting `sat`" is true by construction
//! — `replay_model` is the only path to a `Sat` from that route — but a claim
//! whose only evidence is the producer agreeing with itself is exactly the shape
//! this repository does not accept. The producer is also not the whole pipeline
//! here: the gained files are decided by the `nra` rung, which reaches the
//! single-cell route through `decide_real_poly_constraint` on a SUBPROBLEM, so
//! the model that comes out the front door has passed through more code than the
//! route's own replay covers.
//!
//! So this takes the model the FRONT DOOR returns and evaluates every ORIGINAL
//! assertion at it through the ground evaluator, which does exact algebraic
//! field arithmetic (ADR-0038) and reports an error rather than guessing. Then
//! it prints, per file, whether the replay accepted and how many coordinates
//! were irrational — because a `sat` with no algebraic coordinate is a `sat`
//! this lever did not produce, and counting it would overstate the effect.
//!
//! The arm is NOT set here. `AXEYUM_NRA_CAD` is read once per process through a
//! `OnceLock`, so the caller sets it and the run reports which arm it got:
//!
//! ```text
//! AXEYUM_NRA_CAD=algebraic-witness cargo run --release -p axeyum-solver \
//!     --features full --example nra_algebraic_witness_replay -- FILE.smt2 ...
//! ```
//!
//! # Exit status
//!
//! * `0` — every `sat` replayed, and at least one file produced a `sat` whose
//!   model carries an algebraic coordinate.
//! * `1` — some `sat` did NOT replay. That is a wrong verdict and the loudest
//!   thing this program can say.
//! * `3` — nothing to report: no file produced a `sat` with an algebraic
//!   coordinate. A run that checked nothing must not exit 0, or "replays: 0
//!   failures" becomes a sentence about an empty set.
//! * `2` — a usage or read/parse failure.

use std::time::Duration;

use axeyum_ir::{Value, eval};
use axeyum_solver::{CheckResult, SolverConfig};

fn main() {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: nra_algebraic_witness_replay FILE.smt2 [FILE.smt2 ...]");
        std::process::exit(2);
    }
    let arm = std::env::var("AXEYUM_NRA_CAD").unwrap_or_else(|_| "<unset>".to_owned());
    println!("# AXEYUM_NRA_CAD={arm}");

    let mut sat_with_algebraic = 0usize;
    let mut replay_failures = 0usize;

    for path in &paths {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("read {path}: {e}");
                std::process::exit(2);
            }
        };
        // The SAME front door the A/B measures, under the SAME 24 s envelope.
        // An earlier draft called `check_with_nra` directly and one of the four
        // gained files came back `unknown` from it -- not a contradiction, a
        // different entry point, and exactly the kind of gap that turns a replay
        // report into a statement about some other run. `--timeout-ms 24000` is
        // what the sweep passes, so this is what it has to pass too.
        let config = SolverConfig {
            timeout: Some(Duration::from_secs(24)),
            ..SolverConfig::default()
        };
        let solved = match axeyum_solver::solve_smtlib_with_model(&text, &config) {
            Ok(s) => s,
            Err(e) => {
                println!("error\talgebraic=-\treplay=-\t{path} ({e:?})");
                continue;
            }
        };
        let arena = &solved.script.arena;
        let assertions = solved.assertions.clone();
        let (CheckResult::Sat(_), Some(model)) = (&solved.outcome.result, &solved.model) else {
            let label = match &solved.outcome.result {
                CheckResult::Sat(_) => "sat-without-replayable-model".to_owned(),
                CheckResult::Unsat => "unsat".to_owned(),
                CheckResult::Unknown(_) => "unknown".to_owned(),
            };
            println!("{label}\talgebraic=-\treplay=-\t{path}");
            continue;
        };

        // How many coordinates are genuinely irrational. A `sat` with none is
        // not this lever's.
        let algebraic = model
            .iter()
            .filter(|(_, v)| matches!(v, Value::RealAlgebraic(_)))
            .count();

        // THE INDEPENDENT REPLAY. Every original assertion must evaluate to
        // `true` at the returned point. Anything else -- `false`, an overflow, a
        // non-Bool -- is a failure, never a pass.
        let asg = model.to_assignment();
        let mut failed: Option<usize> = None;
        for (i, &a) in assertions.iter().enumerate() {
            if !matches!(eval(arena, a, &asg), Ok(Value::Bool(true))) {
                failed = Some(i);
                break;
            }
        }

        // And every algebraic coordinate must be NAMEABLE as a root object, or
        // the model could only be reported by rounding it -- which would name a
        // point that does not satisfy the query.
        let mut unnameable = 0usize;
        for (_, v) in model.iter() {
            if let Value::RealAlgebraic(a) = &v
                && a.root_object().is_none()
            {
                unnameable += 1;
            }
        }

        match failed {
            None if unnameable == 0 => {
                if algebraic > 0 {
                    sat_with_algebraic += 1;
                }
                println!("sat\talgebraic={algebraic}\treplay=OK\t{path}");
            }
            None => {
                replay_failures += 1;
                println!("sat\talgebraic={algebraic}\treplay=UNNAMEABLE({unnameable})\t{path}");
            }
            Some(i) => {
                replay_failures += 1;
                println!("sat\talgebraic={algebraic}\treplay=FAILED(assertion #{i})\t{path}");
            }
        }
    }

    println!(
        "REPLAY_SUMMARY|files={}|sat_with_algebraic_coordinate={sat_with_algebraic}|replay_failures={replay_failures}",
        paths.len()
    );

    if replay_failures > 0 {
        eprintln!(
            "FAIL: {replay_failures} `sat` verdict(s) did not replay against their own \
             assertions -- that is a wrong verdict"
        );
        std::process::exit(1);
    }
    if sat_with_algebraic == 0 {
        eprintln!(
            "NOTHING CHECKED: no file produced a `sat` whose model carries an algebraic \
             coordinate, so this run says nothing about the ADR-2134 route. Exiting 3 \
             rather than 0: a clean report over an empty set is not evidence."
        );
        std::process::exit(3);
    }
}
