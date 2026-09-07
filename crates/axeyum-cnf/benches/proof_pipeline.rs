//! Micro-benchmarks for the **evidence path**: DRAT checking (forward and
//! backward), LRAT elaboration (forward and backward), and the two DRAT
//! serialisations.
//!
//! These four routines are what "every unsat carries a machine-checkable proof"
//! costs. Before this file none of them had a bench: `benches/proof_sat_solve.rs`
//! times the *search*, `benches/tseitin_encode.rs` times the *encoder*, and
//! nothing timed the step between a refutation and a certificate a referee can
//! check. `check_drat`, `check_drat_backward`, `elaborate_drat_to_lrat`,
//! `elaborate_drat_to_lrat_backward`, `write_drat`, `write_drat_binary` and
//! `parse_drat_binary` are all on that path.
//!
//! # What this proxies, and what it does not
//!
//! **The real workload** is: the native core refutes a `QF_BV` instance, and the
//! resulting DRAT proof is turned into an LRAT certificate and checked. On the
//! p4dfa slice those proofs run to hundreds of megabytes (the 2026-09-05
//! search-statistics table records 332 MB of DRAT from one 60 s run), so the
//! cost that matters is **per proof step over a proof with a real clause
//! database behind it**.
//!
//! The fixture here is the proof the core itself emits for
//! `corpus/micro-cnf/unsat-pigeonhole-6-7.cnf` — a real proof of a real
//! refutation, produced by the shipping entry point, not a synthetic step list.
//! It is however a **small** one (42 variables), and this file's own lane
//! measured the trap that makes small fixtures dangerous: on this very corpus
//! file the per-conflict cost that dominates a 473,949-variable instance is
//! 42 bytes and therefore invisible. So:
//!
//! - Treat these numbers as a **regression tripwire for the checker and
//!   elaborator implementations**, which is what they are good for: a change
//!   that makes RUP propagation quadratic, or that starts allocating per step,
//!   shows up here immediately and at a cost of seconds.
//! - Do **not** extrapolate them to certificate cost on a real corpus proof.
//!   Checking cost is superlinear in the clause database the RUP propagation
//!   runs against, and this database has 133 clauses. The corpus-scale number
//!   belongs to `examples/boolean_core_profile.rs` and the lane diary
//!   (`docs/research/12-performance/bench-boolean-core-2026-09-07.md`), which
//!   run against p4dfa DIMACS.
//!
//! Deterministic and seed-free: one committed input file, one solver, no RNG.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;
use std::path::Path;

use axeyum_cnf::{
    CnfFormula, DratStep, ProofSolveOutcome, check_drat, check_drat_backward,
    elaborate_drat_to_lrat, elaborate_drat_to_lrat_backward, parse_drat_binary,
    solve_with_drat_proof, write_drat, write_drat_binary,
};
use criterion::{Criterion, criterion_group, criterion_main};

/// The committed fixed input, shared with `benches/proof_sat_solve.rs`.
fn load_php_formula() -> CnfFormula {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/micro-cnf/unsat-pigeonhole-6-7.cnf")
        .canonicalize()
        .expect("corpus/micro-cnf/unsat-pigeonhole-6-7.cnf must exist (committed fixed input)");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    axeyum_cnf::parse_dimacs(&text).expect("unsat-pigeonhole-6-7.cnf must parse as DIMACS")
}

/// The formula and the proof the shipping core actually emits for it.
fn fixture() -> (CnfFormula, Vec<DratStep>) {
    let formula = load_php_formula();
    let proof = match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(steps) => steps,
        other => panic!(
            "unsat-pigeonhole-6-7.cnf is a fixed UNSAT instance; a different verdict \
             ({other:?}) means the committed corpus file or the core changed"
        ),
    };
    assert!(
        !proof.is_empty(),
        "an empty proof would make every benchmark below vacuous"
    );
    (formula, proof)
}

// The two byte counts in the closing `println!` are proof sizes in the tens of
// kilobytes; the ratio between them is exact as `f64`.
#[allow(clippy::cast_precision_loss)]
fn bench_proof_pipeline(c: &mut Criterion) {
    let (formula, proof) = fixture();
    let text = write_drat(&proof);
    let binary = write_drat_binary(&proof);

    // The two DRAT checkers, on the same proof. Forward is the RUP+RAT checker
    // of ADR-0011; backward re-derives only the clauses the refutation needs.
    c.bench_function("check_drat_forward_php_6_7", |b| {
        b.iter(|| {
            let ok = check_drat(&formula, &proof).expect("the core's own proof must check");
            assert!(ok, "check_drat rejected a proof the core just emitted");
            black_box(ok);
        });
    });
    c.bench_function("check_drat_backward_php_6_7", |b| {
        b.iter(|| {
            let ok =
                check_drat_backward(&formula, &proof).expect("the core's own proof must check");
            assert!(
                ok,
                "check_drat_backward rejected a proof the core just emitted"
            );
            black_box(ok);
        });
    });

    // The two LRAT elaborators. These are the ADR-0613 certification path and
    // had no bench at all: an LRAT step carries explicit antecedent hints, so
    // elaboration is strictly more work than checking, and it is the step that
    // turns an unsat into evidence a referee can check without trusting us.
    c.bench_function("elaborate_drat_to_lrat_forward_php_6_7", |b| {
        b.iter(|| {
            let lrat = elaborate_drat_to_lrat(&formula, &proof).expect("elaboration must succeed");
            assert!(!lrat.is_empty(), "elaboration produced no LRAT steps");
            black_box(lrat);
        });
    });
    c.bench_function("elaborate_drat_to_lrat_backward_php_6_7", |b| {
        b.iter(|| {
            let lrat = elaborate_drat_to_lrat_backward(&formula, &proof)
                .expect("elaboration must succeed");
            assert!(
                !lrat.is_empty(),
                "backward elaboration produced no LRAT steps"
            );
            black_box(lrat);
        });
    });

    // The two serialisations, so the "binary DRAT is ~3x smaller" claim has a
    // cost as well as a size. `parse_drat_binary` is the read side a checker
    // pays on every certificate it is handed.
    c.bench_function("write_drat_text_php_6_7", |b| {
        b.iter(|| black_box(write_drat(&proof)));
    });
    c.bench_function("write_drat_binary_php_6_7", |b| {
        b.iter(|| black_box(write_drat_binary(&proof)));
    });
    c.bench_function("parse_drat_binary_php_6_7", |b| {
        b.iter(|| {
            let steps = parse_drat_binary(&binary).expect("binary DRAT must round-trip");
            assert_eq!(
                steps.len(),
                proof.len(),
                "binary round-trip lost or invented steps"
            );
            black_box(steps);
        });
    });

    // Not a timing: the size ratio the binary format exists for. Printed once so
    // a reader of the criterion output can see what the two write benches are
    // producing, since a byte count is the whole point of the format.
    println!(
        "proof_pipeline fixture: {} DRAT steps, text {} bytes, binary {} bytes (text/binary = {:.2}x)",
        proof.len(),
        text.len(),
        binary.len(),
        text.len() as f64 / binary.len() as f64,
    );
}

criterion_group!(benches, bench_proof_pipeline);
criterion_main!(benches);
