//! Bounded satisfiable-side probe for a Rado instance.
//!
//! The expected outcome at `n = 741, k = 4` is that nothing is found: the
//! shell construction is extremal at 740 and four independent 30M-move walks
//! already failed. But an undetected `sat` is the expensive mistake — it would
//! retire the tightness claim and make a day of refutation work pointless — so
//! this runs first and in parallel with the cover, not after it.
//!
//! Two start distributions, because they fail differently:
//!
//! * **warm** — the `[n-1]` witness with one extra point appended in each
//!   colour. The construction's own colouring is the best guess anyone has, and
//!   the walk starts one point away from it;
//! * **cold** — the deterministic round-robin start, which explores a part of
//!   the space the warm start never leaves.
//!
//! A found colouring is replayed through `ColouringFamily::verify_witness`, the
//! brute-force enumerator that shares no code with the encoder, before it is
//! reported or written. The search's own bookkeeping is never the last word.
//!
//! usage: `rado_sat_probe a=5 b=4 k=4 n=741 seeds=16 moves=50000000 \
//!         [warm=<witness.txt>] [out=<found.txt>] [threads=8]`
//!
//! exit: 0 nothing found (bound holds so far), 10 a colouring was FOUND and
//! verified, 3 a search lied (found a colouring the enumerator rejects).

// `main` is one long linear script by design: parse, probe, replay, report.
// Splitting it would hide the order of those steps, and the order is the
// point (the replay must sit between the find and the report).
#![allow(clippy::too_many_lines)]

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Instant;

use axeyum_search::{ColouringFamily, MinConflictsOptions, Rado, Witness, min_conflicts};

fn main() -> ExitCode {
    let args: BTreeMap<String, String> = std::env::args()
        .skip(1)
        .filter_map(|arg| {
            arg.split_once('=')
                .map(|(key, value)| (key.to_string(), value.to_string()))
        })
        .collect();
    let size = |key: &str, fallback: usize| -> usize {
        args.get(key)
            .map_or(fallback, |value| value.parse().expect("number"))
    };
    let count = |key: &str, fallback: u64| -> u64 {
        args.get(key)
            .map_or(fallback, |value| value.parse().expect("number"))
    };
    let (a, b, k, n) = (size("a", 5), size("b", 4), size("k", 4), size("n", 741));
    let seeds = count("seeds", 16);
    let moves = count("moves", 50_000_000);
    let threads = size("threads", 8).max(1);

    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");

    // Warm starts: the [n-1] witness with point n added in every colour.
    let mut starts: Vec<(String, Option<Witness>)> = Vec::new();
    if let Some(path) = args.get("warm") {
        let text = fs::read_to_string(path).expect("read warm start");
        let base = Witness::parse(k, &text).expect("parse warm start");
        assert_eq!(
            base.points() + 1,
            n,
            "warm start colours {} points, want {}",
            base.points(),
            n - 1
        );
        for colour in 1..=k {
            let mut colouring = base.colouring().to_vec();
            colouring.push(colour);
            starts.push((
                format!("warm+{colour}"),
                Some(Witness::new(k, colouring).expect("witness")),
            ));
        }
    }
    starts.push(("cold".to_string(), None));

    println!(
        "probe R_{k}({a}(x-y)={b}z) n={n}: {} starts x {seeds} seeds x {moves} moves, {threads} threads",
        starts.len()
    );
    let jobs: Vec<(usize, u64)> = (0..starts.len())
        .flat_map(|start| (0..seeds).map(move |seed| (start, seed)))
        .collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let found: Mutex<Option<(String, u64, Witness)>> = Mutex::new(None);
    let started = Instant::now();

    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if index >= jobs.len() {
                        return;
                    }
                    if found
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .is_some()
                    {
                        return;
                    }
                    let (start, seed) = jobs[index];
                    let options = MinConflictsOptions {
                        seed,
                        max_moves: moves,
                        ..MinConflictsOptions::default()
                    };
                    let outcome = min_conflicts(&problem, starts[start].1.as_ref(), &options)
                        .expect("min conflicts");
                    let label = &starts[start].0;
                    if let Some(witness) = outcome {
                        *found.lock().unwrap_or_else(PoisonError::into_inner) =
                            Some((label.clone(), seed, witness));
                        return;
                    }
                    println!(
                        "[{:7.1}s] {label} seed={seed}: no colouring in {moves} moves",
                        started.elapsed().as_secs_f64()
                    );
                }
            });
        }
    });

    let wall = started.elapsed().as_secs_f64();
    match found.into_inner().unwrap_or_else(PoisonError::into_inner) {
        None => {
            println!(
                "{{\"status\":\"not-found\",\"n\":{n},\"starts\":{},\"seeds\":{seeds},\
                 \"moves\":{moves},\"wall_s\":{wall:.1}}}",
                starts.len()
            );
            ExitCode::SUCCESS
        }
        Some((label, seed, witness)) => {
            // The search is untrusted: replay through the independent
            // enumerator before this is allowed to be called a colouring.
            if let Err(error) = family.verify_witness(&witness) {
                println!(
                    "{{\"status\":\"search-lied\",\"start\":{label:?},\"seed\":{seed},\"error\":\"{error}\"}}"
                );
                return ExitCode::from(3);
            }
            if let Some(path) = args.get("out") {
                fs::write(path, witness.render()).expect("write witness");
            }
            println!(
                "{{\"status\":\"FOUND\",\"n\":{n},\"start\":{label:?},\"seed\":{seed},\
                 \"verified\":true,\"wall_s\":{wall:.1}}}"
            );
            ExitCode::from(10)
        }
    }
}
