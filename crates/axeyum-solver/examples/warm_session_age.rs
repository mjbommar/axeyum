//! Does a retained [`IncrementalBvSolver`] get slower as the session ages?
//!
//! Glaurung's six-cell campaign (2026-09-17, Axeyum pin `8df853252`) found
//! that the warm session's per-check latency grows with the number of checks
//! it has served: on DptfDevGen the p90 per check was 0.1 ms in the session's
//! first 50 checks and 178 ms past 500, on queries that solve cold in about
//! 2 ms. This example is the standalone oracle for that finding: it drives ONE
//! retained solver through a long push/assert/check/pop stream, records the
//! wall time of every check, and prints p50/p90/max per band of 50 checks.
//!
//! Two drivers, one measurement:
//!
//! * `--replay <stream>` replays a real session verbatim. `<stream>.smt2`
//!   declares the symbols and asserts every distinct assertion once (parsed
//!   into ONE arena, as Glaurung translates into one arena); `<stream>.ops`
//!   has one line per check: `persistent idx,..;temporary idx,..;outcome;..`.
//!   Each check is synchronised exactly as Glaurung's serial warm owner does
//!   it (`warm_paths.rs::transition_and_check`): pop to the longest common
//!   prefix with the previous check's persistent stack, push+assert the
//!   suffix one scope per assertion, then `check` (no temporaries) or
//!   `check_assuming` (temporaries). The stream for DptfDevGen owner 1 is
//!   extracted from the campaign trace with the lane's `extract_owner.py`.
//! * `--synthetic [checks]` (default 1,200) builds a driver-shaped stream in
//!   process: a depth-first walk over a path-condition tree of 64-bit
//!   extract/zero-extend/add/and chains compared against constants, one
//!   branch-feasibility check per step and an overflow-probe assumption every
//!   few steps, siblings sharing the prefix. No external data.
//!
//! `--assert-flat <ratio>` exits 1 when the last band's p90 exceeds the first
//! band's p90 by more than `ratio` (the bisect oracle); `--timeout-ms <n>`
//! bounds each check (default 2,000 ms). Every `sat` is replayed against the
//! original assertions; a replay failure or an outcome that disagrees with the
//! stream's recorded verdict is counted and fails the run.
//!
//! ```sh
//! cargo run --release -p axeyum-solver --features full \
//!     --example warm_session_age -- --synthetic 1200 --assert-flat 10
//! ```

use std::time::{Duration, Instant};

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, IncrementalBvSolver, Model, ReplayCheckedSatCachePolicy, SolverConfig,
};

const BAND: usize = 50;

struct Options {
    replay: Option<String>,
    synthetic: usize,
    assert_flat: Option<f64>,
    timeout: Duration,
    replay_cache: bool,
}

fn parse_args() -> Result<Options, String> {
    let mut opts = Options {
        replay: None,
        synthetic: 1_200,
        assert_flat: None,
        timeout: Duration::from_millis(2_000),
        replay_cache: true,
    };
    let mut args = std::env::args().skip(1);
    let mut mode_set = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--replay" => {
                opts.replay = Some(args.next().ok_or("--replay needs a stream prefix")?);
                mode_set = true;
            }
            "--synthetic" => {
                mode_set = true;
                if let Some(next) = args.next() {
                    opts.synthetic = next
                        .parse()
                        .map_err(|e| format!("--synthetic {next}: {e}"))?;
                }
            }
            "--assert-flat" => {
                let v = args.next().ok_or("--assert-flat needs a ratio")?;
                opts.assert_flat = Some(v.parse().map_err(|e| format!("--assert-flat {v}: {e}"))?);
            }
            "--timeout-ms" => {
                let v = args.next().ok_or("--timeout-ms needs a value")?;
                opts.timeout =
                    Duration::from_millis(v.parse().map_err(|e| format!("--timeout-ms {v}: {e}"))?);
            }
            "--no-replay-cache" => opts.replay_cache = false,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if !mode_set {
        return Err("choose --replay <stream> or --synthetic [checks]".to_string());
    }
    Ok(opts)
}

/// One check of the stream: the persistent stack, the temporaries, and the
/// verdict the stream recorded (`None` when unknown, e.g. synthetic).
struct Op {
    persistent: Vec<usize>,
    temporary: Vec<usize>,
    expected: Option<bool>,
}

struct Stream {
    arena: TermArena,
    assertions: Vec<TermId>,
    ops: Vec<Op>,
}

fn load_replay(prefix: &str) -> Result<Stream, String> {
    let script = std::fs::read_to_string(format!("{prefix}.smt2"))
        .map_err(|e| format!("{prefix}.smt2: {e}"))?;
    let parsed = axeyum_smtlib::parse_script(&script).map_err(|e| format!("parse: {e}"))?;
    let ops_text = std::fs::read_to_string(format!("{prefix}.ops"))
        .map_err(|e| format!("{prefix}.ops: {e}"))?;
    let mut ops = Vec::new();
    for (lineno, line) in ops_text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.split(';').collect();
        if fields.len() < 3 {
            return Err(format!("{prefix}.ops:{}: expected 3+ fields", lineno + 1));
        }
        let parse_list = |s: &str| -> Result<Vec<usize>, String> {
            s.split(',')
                .filter(|x| !x.is_empty())
                .map(|x| x.parse::<usize>().map_err(|e| format!("{x}: {e}")))
                .collect()
        };
        let expected = match fields[2] {
            "sat" => Some(true),
            "unsat" => Some(false),
            _ => None,
        };
        ops.push(Op {
            persistent: parse_list(fields[0])?,
            temporary: parse_list(fields[1])?,
            expected,
        });
    }
    let n = parsed.assertions.len();
    for (i, op) in ops.iter().enumerate() {
        if op.persistent.iter().chain(&op.temporary).any(|&k| k >= n) {
            return Err(format!("op {i} names an assertion index >= {n}"));
        }
    }
    Ok(Stream {
        arena: parsed.arena,
        assertions: parsed.assertions,
        ops,
    })
}

/// A driver-shaped path condition: `((zext32 (extract31:0 (x + k)) & mask) + c) op const`
/// over three 64-bit symbols, one constraint per branch step.
fn synthetic_constraint(
    arena: &mut TermArena,
    syms: &[TermId],
    step: u128,
    polarity: bool,
) -> TermId {
    let x = syms[(step % syms.len() as u128) as usize];
    let y = syms[((step / 3) % syms.len() as u128) as usize];
    let k = arena.bv_const(64, (step * 8) % 4096).unwrap();
    let sum = arena.bv_add(x, k).unwrap();
    let low = arena.extract(31, 0, sum).unwrap();
    let mask = arena.bv_const(32, 0xffff_ff00 | (step & 0x7f)).unwrap();
    let masked = arena.bv_and(low, mask).unwrap();
    let wide = arena.zero_ext(32, masked).unwrap();
    let ysh = arena.extract(15, 0, y).unwrap();
    let ywide = arena.zero_ext(48, ysh).unwrap();
    let mixed = arena.bv_add(wide, ywide).unwrap();
    let bound = arena.bv_const(64, 0x1000 + step * 40).unwrap();
    let cmp = match step % 3 {
        0 => arena.bv_ult(mixed, bound).unwrap(),
        1 => arena.bv_ule(bound, mixed).unwrap(),
        _ => {
            let bit = arena.extract(7, 0, mixed).unwrap();
            let c = arena.bv_const(8, (step * 37) & 0xff).unwrap();
            let eq = arena.eq(bit, c).unwrap();
            arena.not(eq).unwrap()
        }
    };
    if polarity {
        cmp
    } else {
        arena.not(cmp).unwrap()
    }
}

/// An overflow-probe assumption like the explorer's `integer-overflow` checks:
/// `(x + y) < x` restricted to a narrow slice so it is almost always unsat
/// under the prefix.
fn synthetic_probe(arena: &mut TermArena, syms: &[TermId], step: u128) -> TermId {
    let x = syms[(step % syms.len() as u128) as usize];
    let lo = arena.extract(7, 0, x).unwrap();
    let c = arena.bv_const(8, 0xf0 | (step & 0xf)).unwrap();
    let sum = arena.bv_add(lo, c).unwrap();
    let ovf = arena.bv_ult(sum, lo).unwrap();
    let hi = arena.extract(63, 8, x).unwrap();
    let z = arena.bv_const(56, 0).unwrap();
    let hz = arena.eq(hi, z).unwrap();
    arena.and(ovf, hz).unwrap()
}

fn build_synthetic(checks: usize) -> Stream {
    let mut arena = TermArena::new();
    let syms: Vec<TermId> = ["sym0_64", "sym1_64", "sym2_64"]
        .iter()
        .map(|n| {
            let id = arena.declare(n, Sort::BitVec(64)).unwrap();
            arena.var(id)
        })
        .collect();
    let mut assertions = Vec::new();
    let mut ops = Vec::new();
    // Depth-first walk: a path grows to `depth` constraints, then backtracks
    // `back` levels and takes the other polarity, so consecutive checks share
    // a long prefix (as sibling paths do in the explorer).
    let mut stack: Vec<usize> = Vec::new();
    let mut step: u128 = 0;
    let depth = 40;
    while ops.len() < checks {
        if stack.len() >= depth {
            let back = 1 + (step % 5) as usize;
            for _ in 0..back {
                stack.pop();
            }
        }
        let polarity = (step / 7) % 2 == 0;
        let t = synthetic_constraint(&mut arena, &syms, step, polarity);
        assertions.push(t);
        stack.push(assertions.len() - 1);
        ops.push(Op {
            persistent: stack.clone(),
            temporary: Vec::new(),
            expected: None,
        });
        if step % 3 == 0 && ops.len() < checks {
            let p = synthetic_probe(&mut arena, &syms, step);
            assertions.push(p);
            ops.push(Op {
                persistent: stack.clone(),
                temporary: vec![assertions.len() - 1],
                expected: None,
            });
        }
        step += 1;
    }
    Stream {
        arena,
        assertions,
        ops,
    }
}

fn replays(arena: &TermArena, model: &Model, terms: &[TermId]) -> bool {
    let assignment: Assignment = model.to_assignment();
    terms
        .iter()
        .all(|&t| matches!(eval(arena, t, &assignment), Ok(Value::Bool(true))))
}

fn percentile(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let idx = ((sorted.len() as f64 - 1.0) * p).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn main() {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("warm_session_age: {e}");
            std::process::exit(2);
        }
    };
    let (stream, source) = match &opts.replay {
        Some(prefix) => match load_replay(prefix) {
            Ok(s) => (s, format!("replay {prefix}")),
            Err(e) => {
                eprintln!("warm_session_age: {e}");
                std::process::exit(2);
            }
        },
        None => (
            build_synthetic(opts.synthetic),
            format!("synthetic {} checks", opts.synthetic),
        ),
    };
    let Stream {
        arena,
        assertions,
        ops,
    } = stream;
    println!(
        "source: {source}; distinct assertions {}; checks {}",
        assertions.len(),
        ops.len()
    );

    let config = SolverConfig::new()
        .with_timeout(opts.timeout)
        .with_preprocess(false);
    let mut solver = IncrementalBvSolver::with_config(config);
    if opts.replay_cache {
        // Glaurung's production bounds (axeyum_backend.rs DEFAULT_REPLAY_SAT_CACHE_*).
        solver
            .enable_replay_checked_sat_cache(ReplayCheckedSatCachePolicy::new(64, 4_096, 262_144))
            .expect("nonzero bounds");
    }

    let mut live: Vec<usize> = Vec::new();
    let mut times_us: Vec<f64> = Vec::with_capacity(ops.len());
    let mut sat = 0usize;
    let mut unsat = 0usize;
    let mut unknown = 0usize;
    let mut disagreements = 0usize;
    let mut replay_failures = 0usize;
    let mut errors = 0usize;
    let total_started = Instant::now();
    for (i, op) in ops.iter().enumerate() {
        let common = live
            .iter()
            .zip(&op.persistent)
            .take_while(|(a, b)| a == b)
            .count();
        while live.len() > common {
            assert!(solver.pop(), "pop underflow at check {i}");
            live.pop();
        }
        for &k in &op.persistent[common..] {
            solver.push().expect("push");
            if let Err(e) = solver.assert(&arena, assertions[k]) {
                eprintln!("check {i}: assert {k}: {e}");
                errors += 1;
            }
            live.push(k);
        }
        let temps: Vec<TermId> = op.temporary.iter().map(|&k| assertions[k]).collect();
        let started = Instant::now();
        let result = if temps.is_empty() {
            solver.check(&arena)
        } else {
            solver.check_assuming(&arena, &temps)
        };
        let elapsed = started.elapsed();
        times_us.push(elapsed.as_secs_f64() * 1e6);
        let verdict = match result {
            Ok(CheckResult::Sat(model)) => {
                sat += 1;
                let all: Vec<TermId> = op
                    .persistent
                    .iter()
                    .chain(&op.temporary)
                    .map(|&k| assertions[k])
                    .collect();
                if !replays(&arena, &model, &all) {
                    replay_failures += 1;
                    eprintln!("check {i}: sat model does not replay");
                }
                Some(true)
            }
            Ok(CheckResult::Unsat) => {
                unsat += 1;
                Some(false)
            }
            Ok(CheckResult::Unknown(reason)) => {
                unknown += 1;
                eprintln!("check {i}: unknown ({reason:?}) after {elapsed:?}");
                None
            }
            Err(e) => {
                errors += 1;
                eprintln!("check {i}: error {e}");
                None
            }
        };
        if let (Some(v), Some(e)) = (verdict, op.expected)
            && v != e
        {
            disagreements += 1;
            eprintln!("check {i}: verdict {v} disagrees with recorded {e}");
        }
    }
    let total = total_started.elapsed();

    println!(
        "verdicts: sat {sat} unsat {unsat} unknown {unknown} errors {errors}; disagreements {disagreements}; replay failures {replay_failures}; total {:.3} s",
        total.as_secs_f64()
    );
    println!(
        "retained: clauses {} vars {} aig {} depth {}",
        solver.encoded_clause_count(),
        solver.encoded_variable_count(),
        solver.lowered_aig_node_count(),
        solver.scope_depth()
    );
    println!("band  checks    p50_ms    p90_ms    max_ms    sum_ms");
    let mut first_p90 = None;
    let mut last_p90 = 0.0;
    for (b, chunk) in times_us.chunks(BAND).enumerate() {
        let mut sorted = chunk.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let p50 = percentile(&sorted, 0.5) / 1e3;
        let p90 = percentile(&sorted, 0.9) / 1e3;
        let max = sorted.last().copied().unwrap_or(0.0) / 1e3;
        let sum: f64 = chunk.iter().sum::<f64>() / 1e3;
        println!(
            "{:>4} {:>7} {:>9.3} {:>9.3} {:>9.3} {:>9.1}",
            b * BAND,
            chunk.len(),
            p50,
            p90,
            max,
            sum
        );
        if chunk.len() == BAND {
            if first_p90.is_none() {
                first_p90 = Some(p90);
            }
            last_p90 = p90;
        }
    }
    let first_p90 = first_p90.unwrap_or(0.0);
    let ratio = if first_p90 > 0.0 {
        last_p90 / first_p90
    } else {
        f64::INFINITY
    };
    println!("first_band_p90_ms={first_p90:.3} last_band_p90_ms={last_p90:.3} ratio={ratio:.2}");
    let mut failed = false;
    if replay_failures > 0 || disagreements > 0 || errors > 0 {
        eprintln!("SOUNDNESS: replay failures / disagreements / errors are nonzero");
        failed = true;
    }
    if let Some(limit) = opts.assert_flat
        && ratio > limit
    {
        eprintln!("GROWTH: last-band p90 is {ratio:.2}x the first band (limit {limit})");
        failed = true;
    }
    if failed {
        std::process::exit(1);
    }
}
