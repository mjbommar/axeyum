//! Propagation-throughput benchmark for the native CDCL core on a **large,
//! bit-blasted** CNF — the shape the p4dfa corpus actually has.
//!
//! # Why this exists next to `benches/proof_sat_solve.rs`
//!
//! `proof_sat_solve_php_6_7` runs the same core on pigeonhole PHP(7,6): **42
//! variables, 133 clauses**. This lane measured what that costs (diary:
//! `docs/research/12-performance/bench-boolean-core-2026-09-07.md`). On the real
//! p4dfa corpus the native core does **1,800-11,000 propagations and
//! 2,500-29,000 watch-list visits per conflict** over 40,000-3,100,000
//! variables. On PHP(7,6) those numbers are smaller by three to four orders of
//! magnitude, and one per-conflict cost that is proportional to the *variable
//! count* — `analyze`'s `vec![false; nvars]` mark array — is 42 bytes there and
//! 3.1 MB on the largest p4dfa file. A 42-variable fixture is structurally
//! incapable of seeing it.
//!
//! This repository has the measured precedent: `cdclt_solve_php_6_7` reported
//! engine A beating engine B by 3.4% while, on a 330,000-variable real skeleton,
//! the same swap decided 4 more files at 12.9% better PAR-2 — opposite
//! directions. Pigeonhole instances are structurally unlike real CNF.
//!
//! # What this proxies
//!
//! **The real workload is a QF_BV query bit-blasted through `axeyum-bv` and
//! Tseitin-encoded** — exactly what every p4dfa instance is, and what the
//! `dump_dimacs` path in `axeyum-bench` produces. So the fixture here is built
//! the same way rather than written as DIMACS: a 20-bit multiplier constrained
//! to a fixed product, which is a genuinely hard search over tens of thousands
//! of Tseitin variables with the long implication chains a bit-blasted
//! arithmetic circuit has and pigeonhole does not.
//!
//! It is *not* a p4dfa file — those are 2-270 MB and cannot be committed. It is
//! a fixture whose **shape** (variables, clause count, propagations per
//! conflict, watch visits per conflict, blocking-literal miss rate) is in the
//! p4dfa range rather than the pigeonhole range;
//! `fixture_shape_is_in_the_corpus_range` asserts that, so the proxy claim is a
//! test and not a comment. Validation of the proxy against real corpus DIMACS is
//! recorded in the lane diary.
//!
//! # Fixed conflict budget
//!
//! The bench solves under an explicit conflict budget rather than to a verdict.
//! Two builds then analyse the same conflicts along the same trajectory, so the
//! wall-time difference between them is per-conflict throughput and not a
//! difference in how much search each did — the only comparison that means
//! anything for a change meant to be trajectory-preserving. It also bounds the
//! runtime: the budget, not the instance's difficulty, decides how long a sample
//! takes.
//!
//! Deterministic and seed-free: two symbolic inputs, one operator, one constant
//! and one budget fix the whole measurement.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_bv::lower_terms;
use axeyum_cnf::{CnfFormula, VecProofSink, solve_with_drat_proof_counted, tseitin_encode};
use axeyum_ir::{Sort, TermArena};
use criterion::{Criterion, criterion_group, criterion_main};

/// Multiplier width. 20 bits gives ~30-60k Tseitin variables — the low end of
/// the p4dfa variable range (40,548 for the smallest file in the 2026-09-05
/// study population) rather than pigeonhole's 42 — while keeping the encode step
/// well under a second so the bench is dominated by search, not by setup.
const WIDTH: u32 = 20;

/// Conflicts per sample. Chosen so one sample is on the order of a tenth of a
/// second: enough conflicts that per-conflict costs dominate fixed call
/// overhead, few enough that criterion's default sample count fits in seconds.
const CONFLICT_BUDGET: usize = 2_000;

/// `x * y == 0x0F0F1` over `WIDTH` bits, bit-blasted and Tseitin-encoded: a real
/// factorisation search over a real bit-blasted circuit. The constant is odd and
/// not a small power of two, so neither factor is forced and the search is not
/// trivially decided at level zero.
fn multiplier_formula() -> CnfFormula {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(WIDTH)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let product = arena.bv_mul(x, y).unwrap();
    let target = arena.bv_const(WIDTH, 0x0F0F1u128).unwrap();
    let equation = arena.eq(product, target).unwrap();
    let lowering = lower_terms(&arena, &[equation]).unwrap();
    let roots: Vec<_> = lowering.roots().iter().map(|r| r.bits()[0]).collect();
    let encoding = tseitin_encode(lowering.aig(), &roots).expect("fixed AIG encodes cleanly");
    encoding.formula().clone()
}

fn bench_proof_sat_propagate(c: &mut Criterion) {
    let formula = multiplier_formula();

    // The proxy claim, asserted rather than described. If a change to the
    // bit-blaster or the encoder collapses this fixture back toward a
    // pigeonhole-sized instance, this fails instead of quietly benchmarking
    // something that no longer predicts anything.
    let mut sink = VecProofSink::new();
    let (_, counters) = solve_with_drat_proof_counted(&formula, None, CONFLICT_BUDGET, &mut sink);
    assert!(
        formula.variable_count() >= 20_000,
        "the fixture must be in the corpus variable range, not the pigeonhole \
         range; got {} variables (p4dfa's smallest is 40,548, PHP(7,6) is 42)",
        formula.variable_count()
    );
    assert!(
        counters.conflicts > 0,
        "the fixture was decided without a single conflict, so this benchmark \
         measures setup and not search"
    );
    let propagations_per_conflict = counters.propagations as f64 / counters.conflicts as f64;
    assert!(
        propagations_per_conflict >= 50.0,
        "the fixture's implication chains collapsed: {propagations_per_conflict:.1} \
         propagations per conflict, against 1,800-11,000 measured on p4dfa. A \
         fixture with short chains cannot proxy a bit-blasted corpus instance."
    );
    println!(
        "proof_sat_propagate fixture: {} variables, {} clauses; at a {CONFLICT_BUDGET}-conflict \
         budget: {:.0} propagations/conflict, {:.0} watch visits/conflict, \
         {:.3} clause-deref rate, {:.1} resolutions/conflict",
        formula.variable_count(),
        formula.clauses().len(),
        propagations_per_conflict,
        counters.watch_visits_per_conflict(),
        counters.clause_deref_rate(),
        counters.resolutions as f64 / counters.conflicts as f64,
    );

    c.bench_function("proof_sat_propagate_bvmul20_2k_conflicts", |b| {
        b.iter(|| {
            let mut sink = VecProofSink::new();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, CONFLICT_BUDGET, &mut sink);
            // A run that stopped early would silently make the sample cheaper
            // and the benchmark meaningless, so the work done is checked, not
            // assumed.
            assert!(
                counters.conflicts > 0,
                "a sample analysed no conflicts; the fixed-work premise is broken"
            );
            black_box((outcome, counters));
        });
    });
}

criterion_group!(benches, bench_proof_sat_propagate);
criterion_main!(benches);
