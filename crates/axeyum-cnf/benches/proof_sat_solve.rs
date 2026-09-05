//! Micro-benchmark for the native proof-producing CDCL core
//! ([`solve_with_drat_proof`], `src/proof_sat.rs`) — see the 2026-09-05 design
//! review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`.
//!
//! Uses the same fixed, committed input as `axeyum-solver`'s
//! `benches/cdclt_propagate.rs`: `corpus/micro-cnf/unsat-pigeonhole-6-7.cnf` (pigeonhole
//! PHP(7,6), 7 pigeons into 6 holes, UNSAT, 42 vars / 133 clauses). Same
//! input, same host, same run — the two medians recorded in
//! `docs/research/08-planning/microbenchmarks-2026-09-05.md` are a direct
//! ratio between this engine (flat clause arena, blocking literals, VSIDS,
//! LBD/Luby restarts) and the CDCL(T) driver's own loop (`Vec<Vec<Lit>>`, no
//! blocking literals) — D1 in the design review, §3.2.
//!
//! `corpus/micro-cnf/{sat-forced,unsat-unit}.cnf` are 2-clause instances: not
//! enough search to isolate propagate/conflict-analysis/restart cost from
//! fixed per-call overhead. Pigeonhole is the standard small hard CNF.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;
use std::path::Path;

use axeyum_cnf::{ProofSolveOutcome, parse_dimacs, solve_with_drat_proof};
use criterion::{Criterion, criterion_group, criterion_main};

fn load_php_formula() -> axeyum_cnf::CnfFormula {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/micro-cnf/unsat-pigeonhole-6-7.cnf")
        .canonicalize()
        .expect("corpus/micro-cnf/unsat-pigeonhole-6-7.cnf must exist (committed fixed input)");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    parse_dimacs(&text).expect("unsat-pigeonhole-6-7.cnf must parse as DIMACS")
}

fn bench_proof_sat_solve(c: &mut Criterion) {
    let formula = load_php_formula();

    c.bench_function("proof_sat_solve_php_6_7", |b| {
        b.iter(|| {
            let outcome = solve_with_drat_proof(&formula);
            match &outcome {
                ProofSolveOutcome::Unsat(_) => {}
                other => panic!(
                    "unsat-pigeonhole-6-7.cnf is a fixed UNSAT instance; a different verdict \
                     ({other:?}) means the committed corpus file or the core changed"
                ),
            }
            black_box(outcome);
        });
    });
}

criterion_group!(benches, bench_proof_sat_solve);
criterion_main!(benches);
