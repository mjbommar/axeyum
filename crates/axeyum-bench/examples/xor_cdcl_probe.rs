//! Diagnostic: run the in-tree competitive CDCL core (`solve_with_xor_cdcl`,
//! VSIDS/Luby/LBD/1-UIP) on a DIMACS CNF, to measure whether it converts the
//! small-CNF **Timeout** instances that batsat cannot crack but kissat can — i.e.
//! whether the existing P1.3 core is already the lever for the SAT-search-bound
//! band (ADR-0037). Usage:
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example xor_cdcl_probe -- <file.cnf>
//! ```
#![allow(clippy::doc_markdown)]

use std::time::Instant;

use axeyum_cnf::{XorCdclResult, parse_dimacs, solve_with_xor_cdcl};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: xor_cdcl_probe <file.cnf>");
    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    eprintln!(
        "{path}: {} vars, {} clauses",
        formula.variable_count(),
        formula.clauses().len()
    );
    let t = Instant::now();
    let result = solve_with_xor_cdcl(&formula);
    let verdict = match result {
        XorCdclResult::Sat(_) => "SAT",
        XorCdclResult::Unsat => "UNSAT",
        XorCdclResult::Unknown => "UNKNOWN (conflict budget exhausted)",
    };
    eprintln!("xor_cdcl: {verdict} in {:.2?}", t.elapsed());
}
