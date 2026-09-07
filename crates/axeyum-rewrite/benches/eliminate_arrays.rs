//! Micro-benchmark for [`eliminate_arrays`] — every `QF_A*` query pays this
//! preprocessing step before a theory solver sees the formula, and it had no
//! bench of any kind before this file. See
//! `docs/research/12-performance/bench-theories-2026-09-07.md`.
//!
//! Two fixtures, because `eliminate_arrays::tests::
//! abstraction_does_not_materialize_quadratic_select_pairs` already pins the
//! shape that matters here: N reads of one array under N distinct indices
//! elaborate to `N + N*(N-1)/2` assertions — the pairwise Ackermann
//! disequation obligation between every pair of reads is quadratic in read
//! count, and there is no way around it for an eager, non-lazy elimination.
//! `reads` isolates exactly that (no writes, so the only cost is the pairwise
//! blow-up); `read_over_write_chain` is the other shape every array query
//! pays — a single chain of `store`s under one final `select`, which walks the
//! write chain linearly with no pairwise term (see `read_over_write_eliminates_
//! arrays_and_preserves_denotation` in `arrays.rs`'s own test module).
//!
//! What this proxies: `reads` is a batch-verification-style workload (many
//! independent lookups into one table); `read_over_write_chain` is the
//! classic memcpy/array-update pattern (`array_memcpy`,
//! `array_write_chain` scenario families).

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::TermArena;
use axeyum_rewrite::eliminate_arrays;
use criterion::{Criterion, criterion_group, criterion_main};

/// Reads under a fixed 8-bit index (256 distinct indices is comfortably above
/// this), 8-bit elements.
const INDEX_WIDTH: u32 = 8;
const ELEMENT_WIDTH: u32 = 8;
const N_READS: usize = 60;
const CHAIN_LEN: usize = 200;

/// `N_READS` assertions `select(a, index_i) == value_i`, each `index_i` and
/// `value_i` a distinct fresh symbol — the quadratic-pairwise shape.
fn bench_many_reads(c: &mut Criterion) {
    c.bench_function("eliminate_arrays_many_reads_quadratic", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let array = arena
                .array_var("table", INDEX_WIDTH, ELEMENT_WIDTH)
                .expect("array declaration");
            let mut assertions = Vec::with_capacity(N_READS);
            for i in 0..N_READS {
                let index = arena
                    .bv_var(&format!("index_{i}"), INDEX_WIDTH)
                    .expect("distinct declared name per index");
                let value = arena
                    .bv_var(&format!("value_{i}"), ELEMENT_WIDTH)
                    .expect("distinct declared name per value");
                let read = arena
                    .select(array, index)
                    .expect("select over an array var");
                assertions.push(arena.eq(read, value).expect("eq of matching-sort bv terms"));
            }
            let elim = eliminate_arrays(&mut arena, &assertions).expect("supported QF_ABV shape");
            assert_eq!(
                elim.assertions().len(),
                N_READS + N_READS * (N_READS - 1) / 2,
                "N reads elaborate to N + N*(N-1)/2 assertions (pairwise Ackermann)"
            );
            black_box(elim);
        });
    });
}

/// A single chain: `store(store(...store(a, i_0, e_0)..., i_{k-1}, e_{k-1})`
/// then one `select` at a fresh index `j`, elaborated by read-over-write.
fn bench_read_over_write_chain(c: &mut Criterion) {
    c.bench_function("eliminate_arrays_read_over_write_chain", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let mut array = arena
                .array_var("a", INDEX_WIDTH, ELEMENT_WIDTH)
                .expect("array declaration");
            for i in 0..CHAIN_LEN {
                let index = arena
                    .bv_var(&format!("store_index_{i}"), INDEX_WIDTH)
                    .expect("distinct declared name per store index");
                let element = arena
                    .bv_var(&format!("store_elem_{i}"), ELEMENT_WIDTH)
                    .expect("distinct declared name per stored element");
                array = arena
                    .store(array, index, element)
                    .expect("store over a well-sorted array/index/element triple");
            }
            let read_index = arena
                .bv_var("read_index", INDEX_WIDTH)
                .expect("read index declaration");
            let read = arena
                .select(array, read_index)
                .expect("select over the final chained array");
            let result_sym = arena
                .bv_var("result", ELEMENT_WIDTH)
                .expect("result symbol declaration");
            let f = arena
                .eq(read, result_sym)
                .expect("eq of matching-sort bv terms");
            let elim = eliminate_arrays(&mut arena, &[f]).expect("supported QF_ABV shape");
            black_box(elim);
        });
    });
}

criterion_group!(benches, bench_many_reads, bench_read_over_write_chain);
criterion_main!(benches);
