//! Re-certify one Rado ledger claim entirely inside axeyum's own stack.
//!
//! Finding B8 of the 2026-08-12 campaign: the originally shipped `*.drat.gz`
//! certificates were BINARY DRAT (kissat's default output), and axeyum's
//! `parse_drat` reads TEXT DRAT — so the system that shipped those
//! certificates could not read them, and they were honestly downgraded to
//! `replay-only`. This driver produces the replacement (roadmap R3):
//!
//! ```text
//! regenerate CNF from (a, b, k, n)   [byte-compared against the stored .cnf]
//!   -> parse_dimacs
//!   -> solve_with_drat_proof_streaming + TextProofSink   (text DRAT to disk)
//!   -> read the file back, parse_drat        (the round trip B8 failed)
//!   -> check_drat_backward                   (ADR-0382)
//! ```
//!
//! No external solver and no external checker anywhere in this binary. The
//! byte-compare against the stored CNF makes generator drift fail closed: a
//! proof is only ever offered for the exact instance the claim recorded.
//!
//! Driven over the whole ledger by `scripts/recertify-claims.py`; the results
//! are installed by `scripts/apply-recertified-claims.py`.
//!
//! usage: `recertify_rado <a> <b> <k> <n> <stored-cnf> <out.drat> <hours>`
//! exit:  0 verified unsat; 3 check/compare failed; 4 resource; 5 deadline;
//!        10 SAT (would refute the claim!); 2 usage

// `a`, `b`, `k`, `n` are the claim ledger's own parameter names for this
// family (R_k of a(x-y)=bz on [1, n]); renaming them here would decouple the
// tool from the records it certifies. The usize->i64 literal casts cannot
// wrap: the largest variable id is n*k, and the generator's byte-compare
// against the stored CNF would fail closed long before 2^63 variables.
#![allow(clippy::many_single_char_names, clippy::cast_possible_wrap)]

use std::env;
use std::fs;
use std::io::BufWriter;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use axeyum_cnf::{
    StreamingProofOutcome, TextProofSink, check_drat_backward, parse_dimacs, parse_drat,
    solve_with_drat_proof_streaming,
};

/// Regenerates the deciding CNF exactly as `scripts/gen-rado-instance.py`
/// does: one-hot colour variables `var(j, i) = (j-1)k + i`, at-least-one and
/// at-most-one per point, one all-different-colours clause per solution of
/// `a(x-y) = bz` per colour, the first point pinned to colour 1, and the
/// staircase symmetry breaking (colour `i` first appears after colour `i-1`).
fn rado_cnf(a: usize, b: usize, k: usize, n: usize) -> String {
    let var = |j: usize, i: usize| (j - 1) * k + i;
    let mut cl: Vec<Vec<i64>> = Vec::new();
    for j in 1..=n {
        cl.push((1..=k).map(|i| var(j, i) as i64).collect());
    }
    let g = {
        let (mut x, mut y) = (a, b);
        while y != 0 {
            let t = x % y;
            x = y;
            y = t;
        }
        x
    };
    let (ap, bp) = (a / g, b / g);
    let mut t = 1usize;
    while ap * t <= n && bp * t < n {
        let (z, dx) = (ap * t, bp * t);
        for y in 1..=(n - dx) {
            let mut trip = vec![y + dx, y, z];
            trip.sort_unstable();
            trip.dedup();
            for i in 1..=k {
                cl.push(trip.iter().map(|&v| -(var(v, i) as i64)).collect());
            }
        }
        t += 1;
    }
    for j in 1..=n {
        for i1 in 1..=k {
            for i2 in (i1 + 1)..=k {
                cl.push(vec![-(var(j, i1) as i64), -(var(j, i2) as i64)]);
            }
        }
    }
    cl.push(vec![var(1, 1) as i64]);
    for j in 2..=n {
        for i in 2..=k {
            if j < i {
                cl.push(vec![-(var(j, i) as i64)]);
            } else {
                let mut c = vec![-(var(j, i) as i64)];
                c.extend((1..j).map(|jp| var(jp, i - 1) as i64));
                cl.push(c);
            }
        }
    }
    let mut s = format!("p cnf {} {}\n", n * k, cl.len());
    for c in &cl {
        for l in c {
            s.push_str(&l.to_string());
            s.push(' ');
        }
        s.push_str("0\n");
    }
    s
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() < 8 {
        eprintln!("usage: recertify_rado <a> <b> <k> <n> <stored-cnf> <out.drat> <hours>");
        return ExitCode::from(2);
    }
    let a: usize = args[1].parse().expect("a");
    let b: usize = args[2].parse().expect("b");
    let k: usize = args[3].parse().expect("k");
    let n: usize = args[4].parse().expect("n");
    let stored_cnf = &args[5];
    let out_drat = &args[6];
    let hours: f64 = args[7].parse().expect("hours");

    let regenerated = rado_cnf(a, b, k, n);
    let stored = fs::read_to_string(stored_cnf).expect("read stored cnf");
    if stored != regenerated {
        println!("{{\"status\":\"cnf-mismatch\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n}}}");
        return ExitCode::from(3);
    }
    let formula = parse_dimacs(&regenerated).expect("parse dimacs");

    let deadline = Instant::now() + Duration::from_secs_f64(hours * 3600.0);
    let t0 = Instant::now();
    let file = fs::File::create(out_drat).expect("create drat");
    let mut sink = TextProofSink::new(BufWriter::new(file));
    let outcome = solve_with_drat_proof_streaming(&formula, Some(deadline), usize::MAX, &mut sink);
    let solve_s = t0.elapsed().as_secs_f64();

    match outcome {
        StreamingProofOutcome::Unsat => {
            sink.finish().expect("flush proof");
            let bytes = fs::metadata(out_drat).expect("stat drat").len();
            // The round trip B8's certificates could not survive: read the
            // stored bytes back through axeyum's OWN text-DRAT parser.
            let t1 = Instant::now();
            let text = fs::read_to_string(out_drat).expect("read back drat");
            let proof = match parse_drat(&text) {
                Ok(p) => p,
                Err(e) => {
                    println!("{{\"status\":\"parse-failed\",\"error\":\"{e:?}\"}}");
                    return ExitCode::from(3);
                }
            };
            let parse_s = t1.elapsed().as_secs_f64();
            drop(text);
            let t2 = Instant::now();
            let verified = check_drat_backward(&formula, &proof).expect("check_drat_backward");
            let check_s = t2.elapsed().as_secs_f64();
            println!(
                "{{\"status\":\"{}\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                 \"vars\":{},\"clauses\":{},\"steps\":{},\"drat_bytes\":{bytes},\
                 \"solve_s\":{solve_s:.3},\"parse_s\":{parse_s:.3},\"check_s\":{check_s:.3}}}",
                if verified { "verified" } else { "check-failed" },
                formula.variable_count(),
                formula.clauses().len(),
                proof.len(),
            );
            if verified {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(3)
            }
        }
        StreamingProofOutcome::Sat(_) => {
            println!(
                "{{\"status\":\"sat\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\"solve_s\":{solve_s:.3}}}"
            );
            ExitCode::from(10)
        }
        StreamingProofOutcome::ResourceOut => {
            println!("{{\"status\":\"resource-out\",\"solve_s\":{solve_s:.3}}}");
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
