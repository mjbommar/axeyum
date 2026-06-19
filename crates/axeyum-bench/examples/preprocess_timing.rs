//! Timing probe: isolate which word-level preprocessing pass blows up on the
//! large public QF_BV ite-DAGs. Run with a single `.smt2` path argument:
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example preprocess_timing -- <file.smt2>
//! ```
//!
//! Prints wall-clock per pass (canonicalize → propagate_values → solve_eqs →
//! elim_unconstrained → post-canonicalize) plus the assertion/arena node counts,
//! so the unbounded-preprocessor hog is pinpointed before adding fuel. Diagnostic
//! only — not part of the deterministic solve path.
#![allow(clippy::doc_markdown)]

use std::time::Instant;

use axeyum_rewrite::{
    DEFAULT_SOLVE_EQS_FUEL, canonicalize_terms, elim_unconstrained, propagate_values,
    solve_eqs_bounded,
};
use axeyum_smtlib::parse_script;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: preprocess_timing <file.smt2>");
    let text = std::fs::read_to_string(&path).expect("read smt2");
    let mut script = parse_script(&text).expect("parse");
    eprintln!(
        "parsed {path}: {} assertions, {} arena nodes",
        script.assertions.len(),
        script.arena.len()
    );

    let t = Instant::now();
    let canonical = canonicalize_terms(&mut script.arena, &script.assertions)
        .expect("canonicalize")
        .terms;
    eprintln!(
        "canonicalize_terms: {:.2?} ({} arena nodes)",
        t.elapsed(),
        script.arena.len()
    );

    let t = Instant::now();
    let (after_values, _trail) = propagate_values(&mut script.arena, &canonical)
        .expect("propagate_values")
        .into_parts();
    eprintln!(
        "propagate_values:   {:.2?} ({} arena nodes)",
        t.elapsed(),
        script.arena.len()
    );

    let t = Instant::now();
    let eq = solve_eqs_bounded(&mut script.arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
        .expect("solve_eqs_bounded");
    let bailed = eq.bailed();
    let eliminated = eq.eliminated();
    let (reduced, _eq_trail) = eq.into_parts();
    eprintln!(
        "solve_eqs_bounded:  {:.2?} ({} arena nodes, eliminated={eliminated}, bailed={bailed})",
        t.elapsed(),
        script.arena.len()
    );

    let t = Instant::now();
    let (reduced, _u_trail) = elim_unconstrained(&mut script.arena, &reduced)
        .expect("elim_unconstrained")
        .into_parts();
    eprintln!(
        "elim_unconstrained: {:.2?} ({} arena nodes)",
        t.elapsed(),
        script.arena.len()
    );

    let t = Instant::now();
    let _final = canonicalize_terms(&mut script.arena, &reduced)
        .expect("post-canonicalize")
        .terms;
    eprintln!(
        "post-canonicalize:  {:.2?} ({} arena nodes)",
        t.elapsed(),
        script.arena.len()
    );
    eprintln!("DONE");
}
