//! Micro-benchmarks for the ground evaluator — [`eval`] and
//! [`eval_with_memo`].
//!
//! # What real workload this is a proxy for
//!
//! The evaluator is the executable semantic reference every other layer checks
//! itself against, and `CLAUDE.md`'s hard rules make one of its uses
//! **mandatory**: "every `sat` result must be checkable by evaluating the
//! original term against the lifted model". So `eval` runs on every
//! satisfiable query, on every differential-fuzz iteration, and on every
//! self-checking scenario in `axeyum-scenarios`.
//!
//! # Honest limits of the fixture
//!
//! The DAG below is **synthetic and has not been shown to predict any corpus
//! file's evaluation time.** `axeyum-ir` cannot depend on `axeyum-smtlib`
//! (that is the dependency direction, and a dev-dependency cycle is not worth
//! it for a bench), so there is no committed benchmark to read here. The
//! fixture is shaped to look like a `QF_BV` skeleton rather than a chain —
//! a wide layered DAG over 32-bit registers where each layer combines earlier
//! layers, so subterms are genuinely *shared* and the memo is doing real work
//! — but "looks like" is the strongest claim available and the diary records
//! it as such. `axeyum-bv`'s `lower_terms_corpus` is the crate-level bench
//! that does read a real file.
//!
//! # The comparison that is the point
//!
//! [`eval`] builds a **fresh** `FastMap<TermId, Value>` on every call and
//! drops it on return; [`eval_with_memo`] takes the caller's map. A caller
//! evaluating one term under many assignments — a fuzz loop, a scenario
//! replay — therefore pays a full allocate-fill-drop cycle per assignment
//! that a reused map would not. The two arms evaluate the *same* term over
//! the *same* assignments, so the difference is exactly that cost, plus
//! whatever the memo's reuse is worth.
//!
//! Note what the `reused_memo` arm is **not**: it is not a correctness-
//! preserving drop-in. `eval_with_memo`'s doc is explicit that values left in
//! the memo are valid only for the assignment that produced them and "the
//! caller owns invalidation". The arm here clears the map between assignments
//! for exactly that reason, so it measures *allocation reuse only*, which is
//! the honest comparison. An arm that skipped the clear would be measuring a
//! wrong answer.
//!
//! Fixed sizes, no RNG, no seed to pin.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::{
    Assignment, FastMap, Sort, SymbolId, TermArena, TermId, Value, eval, eval_with_memo,
};
use criterion::{Criterion, criterion_group, criterion_main};

/// Register width, matching the `QF_BV` corpus files this is shaped after
/// (`corpus/qfbv-curated/crafted__bit-counting.smt2` declares 32-bit registers).
const WIDTH: u32 = 32;
/// Symbols in the bottom layer.
const LEAVES: usize = 32;
/// Combining layers stacked on top of the leaves.
const LAYERS: usize = 6;
/// Assignments replayed per iteration in the memo comparison.
const REPLAYS: usize = 16;

/// splitmix64's golden-ratio odd constant; multiplication by it is a bijection
/// on `u64`, so successive indices give distinct assignment values with no
/// collision to reason about.
const GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;

/// Builds a wide, genuinely shared DAG over `LEAVES` 32-bit symbols.
///
/// Each layer halves the node count by combining adjacent nodes with a mix of
/// `bvadd` / `bvxor` / `bvmul`, and every layer also folds in a leaf, so upper
/// nodes reference nodes from several layers down rather than forming a tree.
/// The root is a Boolean comparison, so the evaluator returns a
/// [`Value::Bool`] exactly as it would on a real assertion.
fn shared_dag() -> (TermArena, TermId, Vec<SymbolId>) {
    let mut arena = TermArena::new();
    let mut symbols = Vec::with_capacity(LEAVES);
    let mut layer: Vec<TermId> = Vec::with_capacity(LEAVES);
    for i in 0..LEAVES {
        let symbol = arena
            .declare(&format!("r{i}"), Sort::BitVec(WIDTH))
            .expect("distinct names at a legal width always declare");
        symbols.push(symbol);
        layer.push(arena.var(symbol));
    }

    let leaves = layer.clone();
    for depth in 0..LAYERS {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for (index, pair) in layer.chunks(2).enumerate() {
            let lhs = pair[0];
            let rhs = *pair.get(1).unwrap_or(&pair[0]);
            let combined = match (depth + index) % 3 {
                0 => arena.bv_add(lhs, rhs),
                1 => arena.bv_xor(lhs, rhs),
                _ => arena.bv_mul(lhs, rhs),
            }
            .expect("same-width bit-vector operators are well sorted");
            // Fold in a leaf so upper nodes reach back past the layer below,
            // which is what makes this a DAG rather than a balanced tree.
            let folded = arena
                .bv_add(combined, leaves[(depth * 7 + index) % LEAVES])
                .expect("same-width bv_add is well sorted");
            next.push(folded);
        }
        layer = next;
    }

    let top = layer[0];
    let zero = arena
        .bv_const(WIDTH, 0)
        .expect("zero fits any legal bv width");
    let root = arena
        .bv_ult(top, zero)
        .expect("bv_ult of two same-width bit-vectors is well sorted");
    (arena, root, symbols)
}

/// Assignment `index`: every symbol gets a distinct 32-bit value.
fn assignment_for(symbols: &[SymbolId], index: u64) -> Assignment {
    let mut assignment = Assignment::new();
    for (slot, &symbol) in symbols.iter().enumerate() {
        let raw = (index.wrapping_mul(GAMMA)).wrapping_add(slot as u64);
        assignment.set(
            symbol,
            Value::Bv {
                width: WIDTH,
                value: u128::from(raw & 0xFFFF_FFFF),
            },
        );
    }
    assignment
}

fn bench_eval_shared_dag(c: &mut Criterion) {
    let (arena, root, symbols) = shared_dag();
    let assignment = assignment_for(&symbols, 1);
    assert!(
        arena.len() > LEAVES,
        "the fixture must build interior nodes; an arena the size of the leaf \
         set means the DAG builder stopped working"
    );

    c.bench_function("eval_shared_dag", |b| {
        b.iter(|| {
            let value = eval(&arena, root, &assignment).expect("a total assignment evaluates");
            assert!(
                matches!(value, Value::Bool(_)),
                "the fixture's root is a comparison and must evaluate to Bool"
            );
            black_box(value);
        });
    });
}

fn bench_eval_memo_reuse(c: &mut Criterion) {
    let (arena, root, symbols) = shared_dag();
    let assignments: Vec<Assignment> = (0..REPLAYS as u64)
        .map(|i| assignment_for(&symbols, i))
        .collect();

    let mut group = c.benchmark_group("eval_replay_16_assignments");

    group.bench_function("fresh_map_per_call", |b| {
        b.iter(|| {
            for assignment in &assignments {
                black_box(eval(&arena, root, assignment).expect("a total assignment evaluates"));
            }
        });
    });

    group.bench_function("reused_map", |b| {
        // Allocated once, cleared between assignments. Clearing is required for
        // correctness (memo values are assignment-specific), so this arm
        // isolates allocation reuse and nothing else.
        let mut memo: FastMap<TermId, Value> = FastMap::default();
        b.iter(|| {
            for assignment in &assignments {
                memo.clear();
                black_box(
                    eval_with_memo(&arena, root, assignment, &mut memo)
                        .expect("a total assignment evaluates"),
                );
            }
        });
    });

    group.finish();
}

criterion_group!(benches, bench_eval_shared_dag, bench_eval_memo_reuse);
criterion_main!(benches);
