//! Frontier driver for `R_k(a(x-y) = bz)` at `k >= 4`: the `a^k` line.
//!
//! Chang-De Loera-Wesley (ISSAC 2022, arXiv:2210.03262) prove
//! `R_3(a(x-y)=bz) = a^3` for `gcd(a,b)=1`, `a >= b+2`, and their Lemma 4.1
//! gives `R_k >= a^k` for every `k` by the `a`-adic valuation colouring. This
//! driver tests the natural generalisation `R_k = a^k` at `k >= 4`, one
//! parameter point at a time, with both sides done separately:
//!
//! * `valuation` writes the `a`-adic colouring of `[n]` *from the
//!   construction* (no search) and checks it two ways: the encoder's own view
//!   ([`ColouringProblem::first_monochromatic`]) and the family's independent
//!   brute-force enumerator ([`ColouringFamily::first_violation`]), which
//!   shares no code with the encoder.
//! * `climb` warm-starts min-conflicts from a stored colouring, for the
//!   points where the valuation colouring is not extremal.
//! * `sat` runs the pure-Rust rustsat-batsat adapter (ADR-0007) as an
//!   *untrusted searcher* for the satisfiable side only; its model is worth
//!   nothing until the decoded colouring passes the same three checks, and an
//!   `unsat` from it is reported as `unsat-unchecked` and is not evidence.
//! * `solve` runs the native proof-producing CDCL monolithically, streams
//!   text DRAT to disk, reads it back through axeyum's own parser and checks
//!   it with `check_drat_backward` (ADR-0382).
//! * `cover` runs the cube-and-conquer harness when the monolithic solve is
//!   out of reach.
//! * `check` re-checks a DRAT proof this process did not produce, so a proof
//!   can be moved to a host that can afford to check it rather than being
//!   re-derived there.
//!
//! No external solver and no external checker anywhere in this binary
//! (ADR-0002).
//!
//! usage:
//! ```text
//! akb2_frontier valuation <a> <b> <k> <n> <out.txt>
//! akb2_frontier verify    <a> <b> <k> <in.txt>
//! akb2_frontier check     <a> <b> <k> <n> <in.drat>
//! akb2_frontier check-model <a> <b> <k> <n> <solver.out> <out.txt>
//! akb2_frontier climb     <a> <b> <k> <n> <start.txt|-> <out.txt> <seed> <moves>
//! akb2_frontier sat       <a> <b> <k> <n> <out-witness.txt> <hours>
//! akb2_frontier solve     <a> <b> <k> <n> <out.drat> <out-witness.txt> <hours>
//! akb2_frontier cover     <a> <b> <k> <n> <depth> <dir> <workers> <hours> <step-cap>
//! ```
//! exit: 0 the run established what it set out to; 10 the opposite verdict
//! (a `solve` that came back SAT, i.e. a refutation of `R_k <= n`); 3 a check
//! failed; 4 resource-out; 2 usage.

// `a`, `b`, `k`, `n` are the claim ledger's parameter names for this family.
// `single_match_else` is allowed because every verdict in this driver is
// reported as one `match` over the outcome enum: rewriting the two-armed ones
// as `if let` would make the happy path and the alarm path look different from
// each other, which is exactly the readability this file needs to keep.
#![allow(
    clippy::many_single_char_names,
    clippy::cast_possible_wrap,
    clippy::too_many_lines,
    clippy::cast_precision_loss,
    clippy::single_match_else
)]

use std::env;
use std::fs::{self, File};
use std::io::BufReader;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

#[cfg(unix)]
use axeyum_cnf::CacheDroppingWriter;
use axeyum_cnf::{
    SatResult, StreamingProofOutcome, TextProofSink, check_drat_backward,
    check_drat_backward_reader, parse_drat, solve_with_drat_proof_streaming,
    solve_with_native_core_timeout,
};
use axeyum_search::{
    ColouringFamily, MinConflictsOptions, Rado, Witness, cover, harness, min_conflicts,
};

/// The `a`-adic valuation colouring: point `j` takes colour `v_a(j) + 1`.
///
/// This is the colouring behind Lemma 4.1's lower bound `R_k >= a^k`. On
/// `[a^k - 1]` the valuation never reaches `k`, so it uses exactly `k`
/// colours, and no class contains a solution of `a(x-y) = bz` when
/// `gcd(a,b) = 1`: in class `m`, `a^m` divides `x` and `y` hence `x - y`, so
/// `v_a(b t) = v_a(t) >= m` where `x - y = b t`, while `z = a t` in the same
/// class forces `v_a(t) = m - 1` (and `m = 0` is impossible outright because
/// `v_a(a t) >= 1`).
fn valuation_colouring(a: usize, k: usize, n: usize) -> Vec<usize> {
    (1..=n)
        .map(|j| {
            let mut value = j;
            let mut v = 0usize;
            while value % a == 0 && v + 1 < k {
                value /= a;
                v += 1;
            }
            v + 1
        })
        .collect()
}

/// Checks a colouring three ways and reports which checks ran.
///
/// Returns `Err` with the message to print on the first failure.
fn check_colouring(family: &Rado, n: usize, colouring: &[usize]) -> Result<String, String> {
    if colouring.len() != n {
        return Err(format!(
            "colouring covers {} points, wanted {n}",
            colouring.len()
        ));
    }
    let problem = family
        .problem(n)
        .map_err(|e| format!("problem build failed: {e}"))?;
    let constraints = problem.forbidden().len();

    // (1) the encoder's own view.
    if let Some((set, colour)) = problem.first_monochromatic(colouring) {
        return Err(format!("encoder view: {set:?} all coloured {colour}"));
    }
    // (2) the family's independent brute-force enumerator.
    let witness =
        Witness::new(family.colours(), colouring.to_vec()).map_err(|e| format!("witness: {e}"))?;
    family
        .verify_witness(&witness)
        .map_err(|e| format!("independent enumerator: {e}"))?;
    // (3) the CNF itself, evaluated on the one-hot assignment.
    let formula = problem
        .encode()
        .map_err(|e| format!("encode failed: {e}"))?;
    let mut values = vec![false; problem.variable_count()];
    for (index, &colour) in colouring.iter().enumerate() {
        let var = problem
            .variable(index + 1, colour)
            .map_err(|e| format!("variable: {e}"))?;
        values[var.index()] = true;
    }
    match formula.evaluate(&values) {
        Ok(true) => {}
        Ok(false) => return Err("the encoded CNF is NOT satisfied by this colouring".to_string()),
        Err(e) => return Err(format!("evaluate failed: {e}")),
    }
    let used = {
        let mut seen = vec![false; family.colours() + 1];
        for &c in colouring {
            seen[c] = true;
        }
        seen.iter().skip(1).filter(|&&s| s).count()
    };
    Ok(format!(
        "checks=3 constraints={constraints} clauses={} colours_used={used}",
        formula.clauses().len()
    ))
}

fn read_colouring(path: &str) -> Vec<usize> {
    fs::read_to_string(path)
        .expect("read colouring")
        .split_whitespace()
        .map(|t| t.parse::<usize>().expect("colour token"))
        .collect()
}

fn write_colouring(path: &str, colouring: &[usize]) {
    let mut text = String::new();
    for (position, colour) in colouring.iter().enumerate() {
        if position > 0 {
            text.push(' ');
        }
        text.push_str(&colour.to_string());
    }
    text.push('\n');
    fs::write(path, text).expect("write colouring");
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!(
            "usage: akb2_frontier <valuation|verify|check|check-model|climb|sat|solve|cover> ..."
        );
        return ExitCode::from(2);
    }
    let mode = args[1].as_str();
    let num = |i: usize| -> usize { args[i].parse().unwrap_or_else(|_| panic!("arg {i}")) };

    match mode {
        "valuation" => {
            if args.len() < 7 {
                eprintln!("usage: akb2_frontier valuation <a> <b> <k> <n> <out.txt>");
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let family = Rado::new(a, b, k).expect("family");
            let colouring = valuation_colouring(a, k, n);
            match check_colouring(&family, n, &colouring) {
                Ok(note) => {
                    write_colouring(&args[6], &colouring);
                    println!(
                        "{{\"status\":\"witness-verified\",\"mode\":\"valuation\",\"a\":{a},\
                         \"b\":{b},\"k\":{k},\"n\":{n},\"note\":\"{note}\"}}"
                    );
                    ExitCode::SUCCESS
                }
                Err(why) => {
                    println!(
                        "{{\"status\":\"witness-rejected\",\"mode\":\"valuation\",\"a\":{a},\
                         \"b\":{b},\"k\":{k},\"n\":{n},\"why\":\"{why}\"}}"
                    );
                    ExitCode::from(3)
                }
            }
        }
        "check" => {
            // Check a DRAT proof this process did NOT produce. `solve` bundles
            // production and checking, and `recertify_rado` always re-solves;
            // neither can check a proof that already exists. That matters
            // because production and checking have very different memory
            // profiles: a proof that solves comfortably on a 61 GiB host can
            // need a 123 GiB host to check (measured 6.6x resident over the
            // text-DRAT file size). Separating them lets the proof move to the
            // machine that can afford it instead of being re-derived.
            if args.len() < 7 {
                eprintln!("usage: akb2_frontier check <a> <b> <k> <n> <in.drat>");
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let in_drat = args[6].clone();
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let formula = problem.encode().expect("encode");
            let bytes = fs::metadata(&in_drat).expect("stat drat").len();
            eprintln!(
                "instance a={a} b={b} k={k} n={n} vars={} clauses={} drat_bytes={bytes}",
                formula.variable_count(),
                formula.clauses().len()
            );
            // The backward checker must retain a reverse clause plan, but it
            // does not need a second, fully parsed step vector. This matters
            // for frontier proofs measured in gigabytes.
            let file = File::open(&in_drat).expect("open drat");
            let t0 = Instant::now();
            let verified =
                check_drat_backward_reader(&formula, BufReader::with_capacity(1 << 20, file))
                    .expect("check");
            let check_s = t0.elapsed().as_secs_f64();
            println!(
                "{{\"status\":\"{}\",\"mode\":\"check\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                 \"route\":\"file-backed-backward\",\"drat_bytes\":{bytes},\
                 \"check_s\":{check_s:.3}}}",
                if verified {
                    "verified-unsat"
                } else {
                    "check-failed"
                },
            );
            if verified {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(3)
            }
        }
        "check-model" => {
            if args.len() < 8 {
                eprintln!(
                    "usage: akb2_frontier check-model <a> <b> <k> <n> <solver.out> <out.txt>"
                );
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let formula = problem.encode().expect("encode");
            let output = fs::read_to_string(&args[6]).expect("read SAT competition output");
            let values =
                match harness::parse_sat_competition_model(&output, formula.variable_count()) {
                    Ok(values) => values,
                    Err(error) => {
                        println!("{{\"status\":\"model-rejected\",\"why\":\"{error}\"}}");
                        return ExitCode::from(3);
                    }
                };
            if formula.evaluate(&values) != Ok(true) {
                println!("{{\"status\":\"model-rejected\",\"why\":\"CNF replay failed\"}}");
                return ExitCode::from(3);
            }
            let witness = match problem.decode_model(&values) {
                Ok(witness) => witness,
                Err(error) => {
                    println!("{{\"status\":\"model-rejected\",\"why\":\"{error}\"}}");
                    return ExitCode::from(3);
                }
            };
            match check_colouring(&family, n, witness.colouring()) {
                Ok(note) => {
                    write_colouring(&args[7], witness.colouring());
                    println!(
                        "{{\"status\":\"witness-verified\",\"mode\":\"check-model\",\"a\":{a},\
                         \"b\":{b},\"k\":{k},\"n\":{n},\"note\":\"{note}\"}}"
                    );
                    ExitCode::SUCCESS
                }
                Err(why) => {
                    println!("{{\"status\":\"model-rejected\",\"why\":\"{why}\"}}");
                    ExitCode::from(3)
                }
            }
        }
        "verify" => {
            if args.len() < 6 {
                eprintln!("usage: akb2_frontier verify <a> <b> <k> <in.txt>");
                return ExitCode::from(2);
            }
            let (a, b, k) = (num(2), num(3), num(4));
            let colouring = read_colouring(&args[5]);
            let n = colouring.len();
            let family = Rado::new(a, b, k).expect("family");
            match check_colouring(&family, n, &colouring) {
                Ok(note) => {
                    println!(
                        "{{\"status\":\"witness-verified\",\"mode\":\"verify\",\"a\":{a},\
                         \"b\":{b},\"k\":{k},\"n\":{n},\"note\":\"{note}\"}}"
                    );
                    ExitCode::SUCCESS
                }
                Err(why) => {
                    println!(
                        "{{\"status\":\"witness-rejected\",\"mode\":\"verify\",\"a\":{a},\
                         \"b\":{b},\"k\":{k},\"n\":{n},\"why\":\"{why}\"}}"
                    );
                    ExitCode::from(3)
                }
            }
        }
        "climb" => {
            if args.len() < 10 {
                eprintln!(
                    "usage: akb2_frontier climb <a> <b> <k> <n> <start.txt|-> <out.txt> <seed> <moves>"
                );
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let out = args[7].clone();
            let seed: u64 = args[8].parse().expect("seed");
            let moves: u64 = args[9].parse().expect("moves");
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let start_vec = if args[6] == "-" {
                valuation_colouring(a, k, n)
            } else {
                let mut v = read_colouring(&args[6]);
                v.resize(n, 0);
                let filled = valuation_colouring(a, k, n);
                for (index, colour) in v.iter_mut().enumerate() {
                    if *colour == 0 {
                        *colour = filled[index];
                    }
                }
                v
            };
            let start = Witness::new(k, start_vec).expect("start witness");
            let options = MinConflictsOptions {
                seed,
                max_moves: moves,
                ..MinConflictsOptions::default()
            };
            let t0 = Instant::now();
            let found = min_conflicts(&problem, Some(&start), &options).expect("min_conflicts");
            let secs = t0.elapsed().as_secs_f64();
            match found {
                Some(witness) => match check_colouring(&family, n, witness.colouring()) {
                    Ok(note) => {
                        write_colouring(&out, witness.colouring());
                        println!(
                            "{{\"status\":\"witness-verified\",\"mode\":\"climb\",\"a\":{a},\
                             \"b\":{b},\"k\":{k},\"n\":{n},\"seed\":{seed},\
                             \"secs\":{secs:.3},\"note\":\"{note}\"}}"
                        );
                        ExitCode::SUCCESS
                    }
                    Err(why) => {
                        println!(
                            "{{\"status\":\"SEARCH-LIED\",\"mode\":\"climb\",\"a\":{a},\"b\":{b},\
                             \"k\":{k},\"n\":{n},\"why\":\"{why}\"}}"
                        );
                        ExitCode::from(3)
                    }
                },
                None => {
                    println!(
                        "{{\"status\":\"no-witness\",\"mode\":\"climb\",\"a\":{a},\"b\":{b},\
                         \"k\":{k},\"n\":{n},\"seed\":{seed},\"secs\":{secs:.3}}}"
                    );
                    ExitCode::from(4)
                }
            }
        }
        "sat" => {
            // Untrusted search for the SAT side only (ADR-0007): batsat is a
            // searcher, and its answer is worth nothing until the decoded
            // colouring passes the family's independent enumerator. An `unsat`
            // from here is reported as `unsat-unchecked` and is NOT evidence.
            if args.len() < 8 {
                eprintln!("usage: akb2_frontier sat <a> <b> <k> <n> <out-witness.txt> <hours>");
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let out_witness = args[6].clone();
            let hours: f64 = args[7].parse().expect("hours");
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let formula = problem.encode().expect("encode");
            eprintln!(
                "instance a={a} b={b} k={k} n={n} vars={} clauses={}",
                formula.variable_count(),
                formula.clauses().len()
            );
            let t0 = Instant::now();
            let result = solve_with_native_core_timeout(
                &formula,
                Some(Duration::from_secs_f64(hours * 3600.0)),
            )
            .expect("batsat");
            let secs = t0.elapsed().as_secs_f64();
            match result {
                SatResult::Sat(assignment) => {
                    let witness = problem
                        .decode_model(assignment.values())
                        .expect("decode model");
                    match check_colouring(&family, n, witness.colouring()) {
                        Ok(note) => {
                            write_colouring(&out_witness, witness.colouring());
                            println!(
                                "{{\"status\":\"sat-verified\",\"mode\":\"sat\",\"a\":{a},\
                                 \"b\":{b},\"k\":{k},\"n\":{n},\"secs\":{secs:.3},\
                                 \"note\":\"{note}\"}}"
                            );
                            ExitCode::from(10)
                        }
                        Err(why) => {
                            println!(
                                "{{\"status\":\"SEARCH-LIED\",\"mode\":\"sat\",\"a\":{a},\
                                 \"b\":{b},\"k\":{k},\"n\":{n},\"why\":\"{why}\"}}"
                            );
                            ExitCode::from(3)
                        }
                    }
                }
                SatResult::Unsat(_) => {
                    println!(
                        "{{\"status\":\"unsat-unchecked\",\"mode\":\"sat\",\"a\":{a},\"b\":{b},\
                         \"k\":{k},\"n\":{n},\"secs\":{secs:.3},\
                         \"note\":\"NOT EVIDENCE: no proof; rerun in solve or cover mode\"}}"
                    );
                    ExitCode::SUCCESS
                }
                SatResult::Unknown(reason) => {
                    println!(
                        "{{\"status\":\"unknown\",\"mode\":\"sat\",\"a\":{a},\"b\":{b},\
                         \"k\":{k},\"n\":{n},\"secs\":{secs:.3},\"reason\":\"{reason:?}\"}}"
                    );
                    ExitCode::from(4)
                }
            }
        }
        "solve" => {
            if args.len() < 9 {
                eprintln!(
                    "usage: akb2_frontier solve <a> <b> <k> <n> <out.drat> <out-witness.txt> <hours>"
                );
                return ExitCode::from(2);
            }
            let (a, b, k, n) = (num(2), num(3), num(4), num(5));
            let out_drat = args[6].clone();
            let out_witness = args[7].clone();
            let hours: f64 = args[8].parse().expect("hours");
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let formula = problem.encode().expect("encode");
            let vars = formula.variable_count();
            let clauses = formula.clauses().len();
            eprintln!("instance a={a} b={b} k={k} n={n} vars={vars} clauses={clauses}");

            let deadline = Instant::now() + Duration::from_secs_f64(hours * 3600.0);
            let t0 = Instant::now();
            let file = fs::File::create(&out_drat).expect("create drat");
            // This proof can run to gigabytes; drop written pages from the
            // page cache as they go rather than evicting everything else
            // resident on the box (refactor-2026-08 item 05.1).
            // TextProofSink already buffers internally, so no separate
            // BufWriter is needed here.
            #[cfg(unix)]
            let mut sink = TextProofSink::new(CacheDroppingWriter::new(file));
            #[cfg(not(unix))]
            let mut sink = TextProofSink::new(file);
            let outcome =
                solve_with_drat_proof_streaming(&formula, Some(deadline), usize::MAX, &mut sink);
            let solve_s = t0.elapsed().as_secs_f64();

            match outcome {
                StreamingProofOutcome::Unsat => {
                    sink.finish().expect("flush proof");
                    let bytes = fs::metadata(&out_drat).expect("stat").len();
                    let text = fs::read_to_string(&out_drat).expect("read back");
                    let proof = match parse_drat(&text) {
                        Ok(p) => p,
                        Err(e) => {
                            println!("{{\"status\":\"parse-failed\",\"error\":\"{e:?}\"}}");
                            return ExitCode::from(3);
                        }
                    };
                    drop(text);
                    let t2 = Instant::now();
                    let verified = check_drat_backward(&formula, &proof).expect("check");
                    let check_s = t2.elapsed().as_secs_f64();
                    println!(
                        "{{\"status\":\"{}\",\"mode\":\"solve\",\"a\":{a},\"b\":{b},\"k\":{k},\
                         \"n\":{n},\"vars\":{vars},\"clauses\":{clauses},\"steps\":{},\
                         \"drat_bytes\":{bytes},\"solve_s\":{solve_s:.3},\"check_s\":{check_s:.3}}}",
                        if verified {
                            "verified-unsat"
                        } else {
                            "check-failed"
                        },
                        proof.len(),
                    );
                    if verified {
                        ExitCode::SUCCESS
                    } else {
                        ExitCode::from(3)
                    }
                }
                StreamingProofOutcome::Sat(values) => {
                    let witness = problem.decode_model(values.values()).expect("decode model");
                    let note = match check_colouring(&family, n, witness.colouring()) {
                        Ok(note) => note,
                        Err(why) => {
                            println!(
                                "{{\"status\":\"SOLVER-LIED\",\"mode\":\"solve\",\"a\":{a},\
                                 \"b\":{b},\"k\":{k},\"n\":{n},\"why\":\"{why}\"}}"
                            );
                            return ExitCode::from(3);
                        }
                    };
                    write_colouring(&out_witness, witness.colouring());
                    let _ = fs::remove_file(&out_drat);
                    println!(
                        "{{\"status\":\"sat-verified\",\"mode\":\"solve\",\"a\":{a},\"b\":{b},\
                         \"k\":{k},\"n\":{n},\"solve_s\":{solve_s:.3},\"note\":\"{note}\"}}"
                    );
                    ExitCode::from(10)
                }
                StreamingProofOutcome::ResourceOut => {
                    println!(
                        "{{\"status\":\"resource-out\",\"mode\":\"solve\",\"a\":{a},\"b\":{b},\
                         \"k\":{k},\"n\":{n},\"solve_s\":{solve_s:.3}}}"
                    );
                    ExitCode::from(4)
                }
                StreamingProofOutcome::Interrupted => {
                    println!("{{\"status\":\"interrupted\",\"solve_s\":{solve_s:.3}}}");
                    ExitCode::from(5)
                }
                StreamingProofOutcome::SinkFailed(e) => {
                    println!("{{\"status\":\"sink-failed\",\"error\":\"{e:?}\"}}");
                    ExitCode::from(3)
                }
            }
        }
        "cover" => {
            if args.len() < 11 {
                eprintln!(
                    "usage: akb2_frontier cover <a> <b> <k> <n> <depth> <dir> <workers> <hours> <step-cap>"
                );
                return ExitCode::from(2);
            }
            let (a, b, k, n, depth) = (num(2), num(3), num(4), num(5), num(6));
            let dir = PathBuf::from(&args[7]);
            let workers = num(8);
            let hours: f64 = args[9].parse().expect("hours");
            let step_cap = num(10);
            let family = Rado::new(a, b, k).expect("family");
            let problem = family.problem(n).expect("problem");
            let formula = problem.encode().expect("encode");
            eprintln!(
                "instance a={a} b={b} k={k} n={n} vars={} clauses={} depth={depth}",
                formula.variable_count(),
                formula.clauses().len()
            );
            let points = family.branch_points(depth);
            eprintln!("branch points {points:?}");
            let plan = cover::colour_branch_plan(&problem, &points).expect("plan");
            fs::create_dir_all(&dir).expect("mkdir");
            let options = harness::CoverOptions {
                workers,
                total_time: Some(Duration::from_secs_f64(hours * 3600.0)),
                check: if step_cap == 0 {
                    harness::CheckMode::Deferred
                } else {
                    harness::CheckMode::Backward
                },
                check_step_cap: if step_cap == 0 { usize::MAX } else { step_cap },
                proof_dir: Some(dir.join("proofs")),
                proof_prefix: format!("akb2-a{a}-b{b}-k{k}-n{n}"),
                model_path: Some(dir.join("model.txt")),
                ledger_path: Some(dir.join("status.tsv")),
                ..harness::CoverOptions::default()
            };
            let t0 = Instant::now();
            let outcome = harness::run_cover(&formula, &plan, &options, &harness::PrintObserver)
                .expect("run_cover");
            let secs = t0.elapsed().as_secs_f64();
            match &outcome {
                harness::CoverOutcome::Refuted {
                    certificate,
                    certificate_gap,
                    records,
                    ..
                } => match certificate {
                    Some(certificate) => {
                        println!(
                            "{{\"status\":\"cover-refuted\",\"a\":{a},\"b\":{b},\"k\":{k},\
                             \"n\":{n},\"cells\":{},\"steps\":{},\"secs\":{secs:.3},\
                             \"summary\":\"{}\"}}",
                            certificate.cells,
                            certificate.steps,
                            certificate.summary().replace(['"', '\n'], "'")
                        );
                        ExitCode::SUCCESS
                    }
                    None => {
                        println!(
                            "{{\"status\":\"cover-uncertified\",\"a\":{a},\"b\":{b},\"k\":{k},\
                             \"n\":{n},\"records\":{},\"secs\":{secs:.3},\"gap\":\"{}\"}}",
                            records.len(),
                            certificate_gap
                                .as_deref()
                                .unwrap_or("none")
                                .replace(['"', '\n'], "'")
                        );
                        ExitCode::from(4)
                    }
                },
                harness::CoverOutcome::Satisfiable { .. } => {
                    println!(
                        "{{\"status\":\"cover-sat\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                         \"secs\":{secs:.3},\"model\":\"{}\"}}",
                        dir.join("model.txt").display()
                    );
                    ExitCode::from(10)
                }
                harness::CoverOutcome::Incomplete {
                    unfinished,
                    records,
                    ..
                } => {
                    println!(
                        "{{\"status\":\"cover-incomplete\",\"a\":{a},\"b\":{b},\"k\":{k},\
                         \"n\":{n},\"records\":{},\"unfinished\":{},\"secs\":{secs:.3}}}",
                        records.len(),
                        unfinished.len()
                    );
                    ExitCode::from(4)
                }
            }
        }
        other => {
            eprintln!("unknown mode {other:?}");
            ExitCode::from(2)
        }
    }
}
