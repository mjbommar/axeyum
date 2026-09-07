//! Micro-benchmark for [`blast_integers`] — the per-rung transformation cost
//! of the `int-blast-ladder` route (`axeyum-solver`'s `auto.rs`
//! `dispatch_int_blast_width_ladder`), which tries a **dense range of widths
//! in sequence** (`INT_BLAST_MIN_WIDTH ..= INT_BLAST_DENSE_MAX_WIDTH`) on the
//! same assertions until one replay-checks. Neither the ladder nor
//! `blast_integers` itself had a bench before this file, and this route is
//! named in this lane's brief as the dominant path for `QF_NIA` and half the
//! `QF_SLIA` losses. See
//! `docs/research/12-performance/bench-theories-2026-09-07.md`.
//!
//! `blast_integers` is `O(assertions)` per call (a single memoized rewrite
//! pass, per its own doc comment), so the ladder's total cost is that
//! per-call cost times the number of rungs tried before one sticks — this
//! bench isolates the per-rung cost at a handful of representative widths
//! (8, 16, 32, 64) rather than re-implementing dispatch, which lives behind
//! `feature = "full"` in a different crate.
//!
//! What this proxies: a `QF_NIA` query with nonlinear terms (`int_mul`) that
//! the exact linearizer declines, falling through to the width ladder — each
//! `int_mul` also contributes one no-overflow side-constraint
//! (`mul_no_overflow_constraint`), so the fixture includes multiplication
//! explicitly rather than only linear terms.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::{TermArena, TermId};
use axeyum_rewrite::blast_integers;
use criterion::{Criterion, criterion_group, criterion_main};

const N_VARS: usize = 40;

/// `N_VARS` integer variables chained by alternating linear
/// (`x_i + x_{i+1} = c`) and nonlinear (`x_i * x_{i+1} < c`) constraints — a
/// mixed `QF_NIA`-shaped conjunction representative of what declines the exact
/// linearizer and falls to the width ladder.
fn build_nia_query(arena: &mut TermArena) -> Vec<TermId> {
    let vars: Vec<TermId> = (0..N_VARS)
        .map(|i| {
            arena
                .int_var(&format!("x_{i}"))
                .expect("distinct declared name per variable")
        })
        .collect();
    let mut assertions = Vec::with_capacity(N_VARS - 1);
    for i in 0..N_VARS - 1 {
        if i % 2 == 0 {
            let sum = arena
                .int_add(vars[i], vars[i + 1])
                .expect("int_add of two declared int vars");
            let target = arena.int_const(10);
            assertions.push(
                arena
                    .eq(sum, target)
                    .expect("eq of matching-sort int terms"),
            );
        } else {
            let product = arena
                .int_mul(vars[i], vars[i + 1])
                .expect("int_mul of two declared int vars");
            let bound = arena.int_const(100);
            assertions.push(
                arena
                    .int_lt(product, bound)
                    .expect("int_lt of matching-sort int terms"),
            );
        }
    }
    assertions
}

fn bench_blast_at_width(c: &mut Criterion, width: u32) {
    c.bench_function(&format!("int_blast_ladder_rung_width_{width}"), |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let assertions = build_nia_query(&mut arena);
            let blast = blast_integers(&mut arena, &assertions, width)
                .expect("every constant here fits every benched width");
            assert!(blast.had_integers());
            black_box(blast);
        });
    });
}

fn bench_width_8(c: &mut Criterion) {
    bench_blast_at_width(c, 8);
}
fn bench_width_16(c: &mut Criterion) {
    bench_blast_at_width(c, 16);
}
fn bench_width_32(c: &mut Criterion) {
    bench_blast_at_width(c, 32);
}
fn bench_width_64(c: &mut Criterion) {
    bench_blast_at_width(c, 64);
}

criterion_group!(
    benches,
    bench_width_8,
    bench_width_16,
    bench_width_32,
    bench_width_64
);
criterion_main!(benches);
