//! Diagnostic: bit-blast a QF_BV `.smt2` query (after the same word-level
//! preprocessing the fair runs use) to a DIMACS CNF file, so a reference SAT
//! solver (kissat/cadical) can probe whether the public-slice **Timeout**
//! instances are SAT-search-bound (a stronger core would crack them) or genuinely
//! size-bound. Usage:
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example dump_dimacs -- <file.smt2> <out.cnf>
//! ```
//!
//! Not part of the solve path — a measurement tool for ADR-0037's open crux.
#![allow(clippy::doc_markdown)]

use axeyum_bv::lower_terms;
use axeyum_cnf::tseitin_encode;
use axeyum_rewrite::{
    DEFAULT_SOLVE_EQS_FUEL, canonicalize_terms, elim_unconstrained, propagate_values,
    solve_eqs_bounded,
};
use axeyum_smtlib::parse_script;

fn main() {
    let mut args = std::env::args().skip(1);
    let in_path = args
        .next()
        .expect("usage: dump_dimacs <file.smt2> <out.cnf>");
    let out_path = args
        .next()
        .expect("usage: dump_dimacs <file.smt2> <out.cnf>");

    let text = std::fs::read_to_string(&in_path).expect("read smt2");
    let mut script = parse_script(&text).expect("parse");

    // Mirror the fair `--preprocess` pipeline so the CNF matches what batsat timed
    // out on: canonicalize → propagate_values → fuel-bounded solve_eqs →
    // elim_unconstrained → re-canonicalize.
    let canonical = canonicalize_terms(&mut script.arena, &script.assertions)
        .expect("canonicalize")
        .terms;
    let (after_values, _t) = propagate_values(&mut script.arena, &canonical)
        .expect("propagate_values")
        .into_parts();
    let (reduced, _t) = solve_eqs_bounded(&mut script.arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
        .expect("solve_eqs")
        .into_parts();
    let (reduced, _t) = elim_unconstrained(&mut script.arena, &reduced)
        .expect("elim_unconstrained")
        .into_parts();
    let reduced = canonicalize_terms(&mut script.arena, &reduced)
        .expect("post-canonicalize")
        .terms;

    let lowering = lower_terms(&script.arena, &reduced).expect("lower_terms");
    let roots: Vec<_> = lowering.roots().iter().map(|r| r.bits()[0]).collect();
    let encoding = tseitin_encode(lowering.aig(), &roots).expect("tseitin_encode");
    let formula = encoding.formula();
    eprintln!(
        "{in_path}: {} vars, {} clauses → {out_path}",
        formula.variable_count(),
        formula.clauses().len()
    );
    std::fs::write(&out_path, formula.to_dimacs()).expect("write dimacs");
    eprintln!("DONE");
}
