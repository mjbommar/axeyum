//! Probes the open discrepancy `docs/research/12-performance/
//! bench-primitives-2026-09-07.md` (Finding 2) left unresolved: the in-tree
//! "58 MB takes ~54 s" figure (`SmtError::DeadlineExceeded`'s doc comment,
//! about 1.1 MB/s) is ~30x slower than that lane measured on four committed
//! files up to 10.5 MB (30.4–57.7 MB/s, roughly linear in bytes). The 58 MB
//! file itself is not in the tree, so that lane could not tell whether the
//! gap is the file's **shape** (deep nesting, a huge symbol table, heavy
//! sharing), a stale figure, or a wider definition of "reading".
//!
//! This does not have the file either, so it cannot settle *which* real
//! benchmark caused the figure. What it CAN do with the new
//! `axeyum_smtlib::ingest_stats` counters is bound the **shape** hypothesis:
//! build synthetic files of a fixed byte size in three shapes (flat
//! declarations, deep unary nesting, a huge symbol table) and check whether
//! any shape drives `parse_script` down anywhere near 1.1 MB/s. If none can,
//! "shape" is not a plausible explanation on its own and the other two
//! possibilities (stale figure / wider "reading") become more likely.
//!
//! Run with `cargo run -p axeyum-smtlib --example ingest_shape_probe
//! --release`.

use std::fmt::Write as _;
use std::time::Instant;

use axeyum_smtlib::{IngestStatsGuard, last_ingest_stats, parse_script};

/// Target size for each synthetic file. Large enough that per-call overhead
/// (arena setup, etc.) is negligible, small enough this runs in seconds.
const TARGET_BYTES: usize = 4 * 1024 * 1024;

/// A flat script: `TARGET_BYTES` worth of independent
/// `(declare-const x_i (_ BitVec 8)) (assert (= x_i #x2a))` pairs. This is
/// the committed-corpus shape (see `benches/smtlib_parse.rs`): no nesting,
/// no sharing, a linearly-growing but unremarkable symbol table.
fn flat_script(target_bytes: usize) -> String {
    let mut out = String::from("(set-logic QF_BV) ");
    let mut i: u64 = 0;
    while out.len() < target_bytes {
        let _ = write!(
            out,
            "(declare-const x{i} (_ BitVec 8)) (assert (= x{i} #x2a)) "
        );
        i += 1;
    }
    out.push_str("(check-sat)");
    out
}

/// One assertion, `depth` `bvnot`s deep, over a single declared variable —
/// the "deep nesting" shape candidate. Byte size is controlled by `depth`
/// alone (each level costs 7 bytes: `"(bvnot "` plus the matching `)`).
fn deep_nesting_script(depth: usize) -> String {
    let mut out = String::from("(set-logic QF_BV) (declare-const x (_ BitVec 8)) (assert (= ");
    for _ in 0..depth {
        out.push_str("(bvnot ");
    }
    out.push('x');
    for _ in 0..depth {
        out.push(')');
    }
    out.push_str(" x)) (check-sat)");
    out
}

/// A script whose byte budget goes almost entirely into DISTINCT top-level
/// declarations rather than assertions — the "huge symbol table" shape
/// candidate. Each symbol is declared but only cheaply referenced once, so
/// growth is concentrated in `TermArena`'s symbol table rather than in
/// term structure.
fn huge_symbol_table_script(target_bytes: usize) -> String {
    let mut out = String::from("(set-logic QF_BV) ");
    let mut names = Vec::new();
    let mut i: u64 = 0;
    while out.len() < target_bytes {
        let name = format!("sym_{i}_the_quick_brown_fox_jumps");
        let _ = write!(out, "(declare-const {name} (_ BitVec 8)) ");
        names.push(name);
        i += 1;
    }
    out.push_str("(assert (= ");
    out.push_str(names.first().expect("at least one symbol"));
    out.push(' ');
    out.push_str(names.last().expect("at least one symbol"));
    out.push_str(")) (check-sat)");
    out
}

fn probe(label: &str, script: &str) {
    let _guard = IngestStatsGuard::enable();
    let start = Instant::now();
    let result = parse_script(script);
    let elapsed = start.elapsed();
    let stats = last_ingest_stats();
    let bytes = script.len();
    #[allow(clippy::cast_precision_loss)] // display-only throughput estimate
    let mb = bytes as f64 / (1024.0 * 1024.0);
    let secs = elapsed.as_secs_f64().max(1e-9);
    let mb_per_s = mb / secs;
    match result {
        Ok(parsed) => {
            println!(
                "{label:24} bytes={bytes:>10} elapsed={elapsed:>10.3?} {mb_per_s:>8.1} MB/s \
                 atoms={:>9} lists={:>8} max_depth={:>6} assertions={:>6} symbols={:>7}",
                stats.atoms,
                stats.lists,
                stats.max_sexpr_depth,
                parsed.assertions.len(),
                stats.symbols_declared,
            );
        }
        Err(e) => println!("{label:24} FAILED: {e}"),
    }
}

fn main() {
    println!(
        "Bounding the shape hypothesis for the 58 MB / ~54 s (~1.1 MB/s) figure \
         — see docs/research/12-performance/foundation-counters-2026-09-07.md"
    );
    probe("flat_4mb", &flat_script(TARGET_BYTES));
    probe(
        "huge_symbol_table_4mb",
        &huge_symbol_table_script(TARGET_BYTES),
    );
    // Nesting depth is capped by what the crate's own resource limits admit
    // for a single term (not by this probe); depths are chosen to grow well
    // past anything the committed corpus exercises while staying under any
    // documented ceiling.
    probe("deep_nesting_1k", &deep_nesting_script(1_000));
    probe("deep_nesting_10k", &deep_nesting_script(10_000));
    probe("deep_nesting_100k", &deep_nesting_script(100_000));
    probe("deep_nesting_1m", &deep_nesting_script(1_000_000));
}
