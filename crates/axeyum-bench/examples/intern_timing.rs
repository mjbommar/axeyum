//! Timing probe: isolate parse + term-interning cost in isolation from any
//! rewrite/solve pass, for the axeyum-ir intern-table hasher measurement
//! (`docs/research/11-design-review/2026-09-05-intern-table-hasher-measured.md`).
//! Run with a single `.smt2` path argument:
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example intern_timing -- <file.smt2>
//! ```
//!
//! `parse_script` reads the whole file and interns every term through
//! `TermArena` as it builds each assertion (`axeyum-smtlib`'s parser calls
//! straight into the typed builders, which hash-cons through
//! `TermArena::intern`), so wall time here is dominated by the intern
//! table's hash/lookup/insert path on a large corpus file — not by any
//! later rewrite or solve stage. Prints elapsed ms and the final arena term
//! count (`script.arena.len()`) so a run can be sanity-checked against
//! another (same file must report the same node count regardless of
//! hasher). Diagnostic only — not part of the deterministic solve path.
#![allow(clippy::doc_markdown)]

use std::time::Instant;

use axeyum_smtlib::parse_script;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: intern_timing <file.smt2>");
    let text = std::fs::read_to_string(&path).expect("read smt2");

    let t = Instant::now();
    let script = parse_script(&text).expect("parse");
    let elapsed = t.elapsed();

    println!(
        "file={path} bytes={} elapsed_ms={:.3} assertions={} arena_nodes={}",
        text.len(),
        elapsed.as_secs_f64() * 1000.0,
        script.assertions.len(),
        script.arena.len(),
    );
}
