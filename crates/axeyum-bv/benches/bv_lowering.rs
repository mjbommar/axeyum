//! Micro-benchmarks for term-to-AIG bit lowering — [`lower_terms`] and
//! [`IncrementalLowering`], the critical path for `QF_BV` and (through array
//! elimination) `QF_ABV`.
//!
//! `axeyum-bv` had **no benches at all** before 2026-09-07, despite ADR-0300
//! recording that "bit lowering plus CNF encoding account for about 84% of
//! Axeyum's cold pipeline while SAT search accounts for about 15%" on the
//! accepted Glaurung population. This file is the first instrument on that
//! 84%.
//!
//! # What real workload each group is a proxy for
//!
//! **`lower_terms_corpus` is not a proxy.** It lowers the assertions of a
//! committed `corpus/qfbv-curated` benchmark, parsed by `axeyum-smtlib` — the
//! same terms the `sat-bv` backend lowers on that file. Parsing happens once,
//! outside the timed loop, so the number is lowering alone.
//!
//! **`lower_terms_bvmul` is a proxy, and a deliberately narrow one.** A
//! symbolic `w`-bit multiplier is the standard nontrivial gate-count fixture
//! (`axeyum-cnf`'s `tseitin_encode` bench uses the same shape at `w = 16`, so
//! the two compose into a lowering-plus-encoding pair rather than two
//! unrelated numbers). It measures how lowering scales with a *quadratic*
//! circuit and nothing else. It has **not** been shown to predict the corpus:
//! a real `QF_BV` benchmark is mostly slices, concats, comparisons and adds
//! over a wide shared DAG, and the ADR-0300 family breakdown
//! (52 register-slice, 54 slice-partial, 36 arithmetic of 162) says the
//! arithmetic-heavy shape is a minority. Read the width sweep as a shape
//! study, not a forecast. `lower_terms_corpus` is the number to trust.
//!
//! **`lowering_incremental_vs_oneshot` is a proxy for the warm
//! `IncrementalBvSolver` push/assume path** (ADR-0009 st.2), where a caller
//! adds assertions one at a time over a growing arena and the memo must carry
//! shared subterms across calls. The two arms lower the *same* roots over the
//! *same* arena, so the ratio isolates per-call overhead plus memo reuse from
//! the circuit itself.
//!
//! # What this file deliberately does not do
//!
//! It does not compare memo representations. ADR-0300 preregistered exactly
//! that experiment (`BTreeMap<TermId, Vec<AigLit>>` versus a dense
//! `TermId`-indexed vector), ran it under a frozen protocol, and **rejected**
//! the dense candidate on a run-total variance gate despite a favourable
//! 0.922 paired bit-blast geometric mean. That ADR also names "select on
//! comparison counts or microbenchmarks" among its rejected alternatives. A
//! criterion median cannot reopen it and this bench does not pretend to.
//!
//! All fixtures are fixed: two symbolic inputs and one operator, or a
//! committed file. No RNG, no seed to pin.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;
use std::path::Path;

use axeyum_bv::{IncrementalLowering, lower_terms};
use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, WideUint};
use criterion::{Criterion, criterion_group, criterion_main};

/// Widths for the multiplier sweep. A multiplier's gate count is
/// ~quadratic in the width, so 8 → 64 spans roughly 64x of circuit.
const MUL_WIDTHS: &[u32] = &[8, 16, 32, 64];

/// A committed pure-`QF_BV` benchmark whose assertions lower end to end.
///
/// `crafted__bit-counting.smt2` is the largest file in `corpus/qfbv-curated`
/// (~2.7 K, 32-bit registers, `unsat`) and is the same file the
/// `axeyum-smtlib` parse bench uses as its small case, so lowering time and
/// ingest time on one real benchmark are directly comparable.
const CORPUS_QFBV: &str = "corpus/qfbv-curated/crafted__bit-counting.smt2";

/// Builds an arena holding a symbolic `width`-bit multiplier, and returns the
/// product's root.
fn multiplier(width: u32) -> (TermArena, TermId) {
    let mut arena = TermArena::new();
    let x_sym = arena
        .declare("x", Sort::BitVec(width))
        .expect("declaring a fresh symbol at a legal width cannot fail");
    let y_sym = arena
        .declare("y", Sort::BitVec(width))
        .expect("declaring a fresh symbol at a legal width cannot fail");
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let product = arena
        .bv_mul(x, y)
        .expect("bv_mul of two same-width bit-vectors is well sorted");
    (arena, product)
}

/// Parses the committed `QF_BV` benchmark into its arena and assertion roots.
fn corpus_qfbv() -> (TermArena, Vec<TermId>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(CORPUS_QFBV);
    let source = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "committed corpus file {} must be readable: {e}",
            path.display()
        )
    });
    let script = axeyum_smtlib::parse_script(&source).expect("a committed QF_BV file parses");
    assert!(
        !script.assertions.is_empty(),
        "the corpus fixture must carry assertions; zero means it stopped \
         exercising the lowerer"
    );
    (script.arena, script.assertions)
}

fn bench_lower_multiplier(c: &mut Criterion) {
    let mut group = c.benchmark_group("lower_terms_bvmul");
    for &width in MUL_WIDTHS {
        let (arena, product) = multiplier(width);
        // The 64-bit multiplier is ~64x the 8-bit one; cap its sample count so
        // the whole group stays well inside the lane's five-minute budget.
        group.sample_size(if width >= 64 { 30 } else { 100 });
        group.bench_function(format!("w{width}"), |b| {
            b.iter(|| {
                let lowering =
                    lower_terms(&arena, &[product]).expect("a multiplier is inside the BV subset");
                assert!(
                    lowering.aig().node_count() > 1,
                    "a symbolic multiplier must build real AIG nodes; a trivial \
                     node count means the fixture stopped exercising the lowerer"
                );
                black_box(lowering);
            });
        });
    }
    group.finish();
}

fn bench_lower_corpus(c: &mut Criterion) {
    let (arena, roots) = corpus_qfbv();
    c.bench_function("lower_terms_corpus_bit_counting", |b| {
        b.iter(|| {
            let lowering = lower_terms(&arena, &roots).expect("the committed QF_BV fixture lowers");
            assert!(
                lowering.aig().node_count() > 1,
                "the corpus fixture must build real AIG nodes"
            );
            black_box(lowering);
        });
    });
}

fn bench_incremental_vs_oneshot(c: &mut Criterion) {
    let (arena, roots) = corpus_qfbv();
    let mut group = c.benchmark_group("lowering_incremental_vs_oneshot");

    group.bench_function("oneshot", |b| {
        b.iter(|| {
            let lowering = lower_terms(&arena, &roots).expect("the committed fixture lowers");
            black_box(lowering);
        });
    });

    group.bench_function("incremental", |b| {
        b.iter(|| {
            let mut incremental = IncrementalLowering::new();
            for &root in &roots {
                incremental
                    .lower(&arena, root)
                    .expect("the committed fixture lowers incrementally too");
            }
            assert!(
                incremental.node_count() > 1,
                "incremental lowering must build real AIG nodes"
            );
            black_box(&incremental);
        });
    });

    group.finish();
}

/// Model replay: [`axeyum_bv::BitLowering::input_values`] at six symbol widths.
///
/// # What real workload this is a proxy for
///
/// **The mandatory one.** `CLAUDE.md`'s hard rules say "every `sat` result must
/// be checkable by evaluating the original term against the lifted model", and
/// `input_values` is the first step of that check on the BV route — it turns an
/// [`Assignment`](axeyum_ir::Assignment) back into the AIG's input vector. It
/// runs on every satisfiable query, and again on every differential-fuzz
/// iteration.
///
/// # The prediction this group exists to test
///
/// `input_values` iterates `symbol_inputs`, which holds **one entry per symbol
/// bit**, and for each entry calls `value_to_lsb_bits(value)` — which allocates
/// a fresh `Vec<bool>` of the symbol's **full width** — then reads exactly one
/// bit out of it and drops the vector. If that reading is right the routine is
/// O(width²) per symbol with O(width) allocations, where O(width) total is
/// available.
///
/// So: **doubling the width should roughly quadruple the time, not double it.**
/// The sweep runs 16 → 1024 over a single symbol precisely so that a quadratic
/// shows up as a shape and cannot be explained away as constant overhead. If
/// the ratios come out near 2x, the reading above is wrong and the diary says
/// so.
///
/// # Why the sweep goes past 128
///
/// At 128 bits the absolute cost is a few microseconds, which is nothing next
/// to a solve, and a reader could fairly dismiss the shape as academic.
/// [`Sort::BitVec`] admits widths to `MAX_BV_WIDTH` = 65,536, and this crate's
/// own tests lower 1024-bit symbols, so 512 and 1024 are added to say what the
/// shape actually costs where it is reachable. Those two also cross a code
/// boundary — above 128 bits a bit-vector value is a
/// [`Value::WideBv`](axeyum_ir::Value::WideBv) and the conversion goes through
/// `WideUint::to_lsb_bits` rather than `bv_value_to_lsb_bits` — so if the
/// quadratic survives the crossing it is a property of the *caller's loop*,
/// not of one conversion routine.
fn bench_model_replay_input_values(c: &mut Criterion) {
    let mut group = c.benchmark_group("model_replay_input_values");
    for &width in &[16u32, 32, 64, 128, 512, 1024] {
        let mut arena = TermArena::new();
        let x_sym = arena
            .declare("x", Sort::BitVec(width))
            .expect("declaring a fresh symbol at a legal width cannot fail");
        let x = arena.var(x_sym);
        // `bv_not` keeps the circuit linear in the width, so the lowering
        // itself contributes negligibly and every symbol bit becomes an AIG
        // input. The measurement is then about `input_values`, not the circuit.
        let root = arena.bv_not(x).expect("bv_not is well sorted");
        let lowering = lower_terms(&arena, &[root]).expect("bv_not is inside the BV subset");
        assert_eq!(
            lowering.symbol_inputs().len(),
            width as usize,
            "every symbol bit must become an AIG input; a different count means \
             the fixture stopped measuring the per-bit loop"
        );

        // `Value::Bv` is `u128`-backed, so anything wider must be a
        // `Value::WideBv`. Picking the right variant is not cosmetic: the
        // wrong one is an `AssignmentSortMismatch`, not a slow path.
        let value = if width <= 128 {
            Value::Bv { width, value: 1 }
        } else {
            Value::WideBv(WideUint::from_u128(1, width))
        };
        let mut assignment = Assignment::new();
        assignment.set(x_sym, value);

        // The 1024-bit case is ~500x the 16-bit one; cap its sample count so
        // the group stays well inside the lane's five-minute budget.
        group.sample_size(if width >= 512 { 30 } else { 100 });
        group.bench_function(format!("w{width}"), |b| {
            b.iter(|| {
                let inputs = lowering
                    .input_values(&assignment)
                    .expect("a complete assignment lifts");
                black_box(inputs);
            });
        });
    }
    // The counterweight to the width sweep, and the reason it is in the same
    // group rather than off in a note. The sweep above establishes a shape on
    // synthetic single-symbol fixtures; this case runs the *same* routine over
    // the *same* real benchmark `lower_terms_corpus_bit_counting` lowers, so a
    // reader can put "quadratic in the width" next to "and here is what it
    // costs on a file that exists" without leaving the output. If the corpus
    // number is a rounding error against that file's lowering time, the shape
    // is still real and still not a priority, and both halves have to be said.
    let (arena, roots) = corpus_qfbv();
    let lowering = lower_terms(&arena, &roots).expect("the committed QF_BV fixture lowers");
    let mut assignment = Assignment::new();
    for binding in lowering.symbol_inputs() {
        let value = match binding.sort {
            Sort::Bool => Value::Bool(true),
            Sort::BitVec(width) if width <= 128 => Value::Bv { width, value: 1 },
            Sort::BitVec(width) => Value::WideBv(WideUint::from_u128(1, width)),
            other => {
                panic!("the committed QF_BV fixture declares only Bool/BitVec, found {other:?}")
            }
        };
        assignment.set(binding.symbol, value);
    }
    let symbol_bits = lowering.symbol_inputs().len();
    assert!(
        symbol_bits > 0,
        "the corpus fixture must have symbol bits to lift; zero means it \
         stopped exercising the replay path"
    );
    group.sample_size(100);
    group.bench_function(
        format!("corpus_bit_counting_{symbol_bits}_symbol_bits"),
        |b| {
            b.iter(|| {
                let inputs = lowering
                    .input_values(&assignment)
                    .expect("a complete assignment lifts");
                black_box(inputs);
            });
        },
    );

    group.finish();
}

criterion_group!(
    benches,
    bench_lower_multiplier,
    bench_lower_corpus,
    bench_incremental_vs_oneshot,
    bench_model_replay_input_values
);
criterion_main!(benches);
