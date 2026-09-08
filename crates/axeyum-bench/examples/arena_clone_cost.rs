//! Prices one `TermArena::clone` on a real benchmark's arena.
//!
//! # Why this exists
//!
//! The online integer theory (`crate::lia_online::LiaTheory`) clones the whole
//! `TermArena` on every feasibility check, and `scripts/lia-counter-sweep.sh`
//! now counts those clones and the nodes they copy: 352 million nodes over the
//! committed 27-file `QF_LIA` loss list, measured 2026-09-08. A count is not a
//! cost, though, and the two candidate hot spots inside `theory_assert` — the
//! clone and the offline integer decider it feeds — cannot be separated by
//! counting alone. `perf` is unavailable on this host
//! (`perf_event_paranoid = 4`), so this prices the mechanism directly and the
//! attribution is `cost × counted frequency` rather than a sampled profile.
//!
//! A clone here is **not** a memcpy of a node vector. `TermArena` carries an
//! `intern: FastMap<TermNode, TermId>` with one entry per node, four
//! `FastMap<String, _>` name tables whose keys are individually-allocated
//! `String`s, and `TermNode::App` owns its argument list — so the per-clone
//! cost is dominated by allocator traffic, which is exactly the quantity a
//! back-of-the-envelope "20k nodes is nothing" argument gets wrong.
//!
//! Usage:
//! ```text
//! arena_clone_cost <file.smt2> [rounds]
//! ```
//!
//! Prints the arena's node count, the median clone time over `rounds` (default
//! 200), and the per-node cost.

use std::time::Instant;

fn main() -> std::process::ExitCode {
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: arena_clone_cost <file.smt2> [rounds]");
        return std::process::ExitCode::from(2);
    };
    let rounds: usize = args
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(200)
        .max(1);

    let source = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("cannot read {path}: {error}");
            return std::process::ExitCode::from(2);
        }
    };
    let script = match axeyum_smtlib::parse_script(&source) {
        Ok(script) => script,
        Err(error) => {
            eprintln!("cannot parse {path}: {error:?}");
            return std::process::ExitCode::from(2);
        }
    };
    let arena = script.arena;
    let nodes = arena.len();

    // Warm the allocator, then take the median of `rounds` clones. The median
    // rather than the mean because one clone landing on an allocator slow path
    // should not set the number a later attribution multiplies by.
    for _ in 0..8 {
        let clone = arena.clone();
        std::hint::black_box(&clone);
    }
    let mut samples = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let started = Instant::now();
        let clone = arena.clone();
        std::hint::black_box(&clone);
        samples.push(started.elapsed().as_nanos());
    }
    samples.sort_unstable();
    let median = samples[samples.len() / 2];
    let p90 = samples[(samples.len() * 9) / 10];

    #[allow(clippy::cast_precision_loss)]
    let per_node = median as f64 / nodes.max(1) as f64;
    println!("file={path}");
    println!("arena_nodes={nodes} assertions={}", script.assertions.len());
    println!("clone_median_ns={median} clone_p90_ns={p90} rounds={rounds}");
    println!("ns_per_node={per_node:.2}");
    std::process::ExitCode::SUCCESS
}
