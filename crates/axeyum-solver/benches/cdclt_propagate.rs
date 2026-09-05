//! Micro-benchmark for [`CdclT`]'s propagate/decide/solve loop — Boolean search
//! isolated from any real theory (see the 2026-09-05 design review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`).
//!
//! The theory is a trivial always-consistent [`TheorySolver`] (`assert` always
//! `Ok`, `propagate` always empty), so every conflict and decision comes from
//! the Boolean skeleton alone. The input is the same committed, fixed
//! pigeonhole-formula CNF (`corpus/micro-cnf/unsat-pigeonhole-6-7.cnf`, 7 pigeons into 6
//! holes, UNSAT, 42 vars / 133 clauses) as `proof_sat_solve`'s
//! `axeyum-cnf/benches/proof_sat_solve.rs`, so the two engines' medians in
//! `docs/research/08-planning/microbenchmarks-2026-09-05.md` are a direct
//! ratio, not an apples-to-oranges comparison.
//!
//! `corpus/micro-cnf/{sat-forced,unsat-unit}.cnf` are 2-clause instances —
//! any conflict-driven engine decides them in a handful of steps, which is not
//! enough search to isolate propagate/decide/backjump/restart cost from fixed
//! per-call overhead. The pigeonhole formula is the standard small hard CNF:
//! non-trivial resolution complexity while still solving in well under a
//! second, so a `criterion` sample loop stays fast.
//!
//! Requires the `bench-internals` feature (implies `full`); see
//! `crate::bench_internals` in `src/lib.rs` for why `CdclT` is reachable here
//! at all.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;
use std::path::Path;

use axeyum_cnf::parse_dimacs;
use axeyum_solver::bench_internals::{CdclT, Lit, Outcome};
use axeyum_solver::theories::combination::{TheoryLit, TheoryProp, TheorySolver};
use criterion::{Criterion, criterion_group, criterion_main};

/// Always-consistent theory: never conflicts, never propagates. Isolates the
/// Boolean CDCL loop from any theory-specific cost.
struct NoTheory;

impl TheorySolver for NoTheory {
    fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
        Ok(())
    }
    fn push(&mut self) {}
    fn pop(&mut self) {}
    fn propagate(&self) -> Vec<TheoryProp> {
        Vec::new()
    }
}

/// Loads the fixed pigeonhole CNF and converts it into `(var_count, clauses)`
/// for [`CdclT::new`].
fn load_php_clauses() -> (usize, Vec<Vec<Lit>>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/micro-cnf/unsat-pigeonhole-6-7.cnf")
        .canonicalize()
        .expect("corpus/micro-cnf/unsat-pigeonhole-6-7.cnf must exist (committed fixed input)");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    let formula = parse_dimacs(&text).expect("unsat-pigeonhole-6-7.cnf must parse as DIMACS");
    let var_count = formula.variable_count();
    let clauses = formula
        .clauses()
        .iter()
        .map(|clause| {
            clause
                .lits()
                .iter()
                .map(|lit| Lit {
                    var: lit.var().index(),
                    positive: !lit.is_negated(),
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    (var_count, clauses)
}

fn bench_cdclt_solve(c: &mut Criterion) {
    let (var_count, clauses) = load_php_clauses();

    c.bench_function("cdclt_solve_php_6_7", |b| {
        b.iter(|| {
            let mut solver = CdclT::new(var_count, 0, clauses.clone(), None);
            let mut theory = NoTheory;
            let outcome = solver.solve(&mut theory);
            assert_eq!(
                outcome,
                Outcome::Unsat,
                "unsat-pigeonhole-6-7.cnf is a fixed UNSAT instance; a different verdict means the \
                 committed corpus file or the driver changed"
            );
            black_box(outcome);
        });
    });
}

criterion_group!(benches, bench_cdclt_solve);
criterion_main!(benches);
