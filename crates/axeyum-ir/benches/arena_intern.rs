//! Micro-benchmark for [`TermArena`] interning — `intern: HashMap<TermNode,
//! TermId>` (`src/arena.rs`), the default `std` `SipHash` table the
//! 2026-09-05 design review's D5 names as a hot-path cost paid for no
//! determinism gain (`docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`).
//! Named `arena_intern` deliberately: another lane is about to swap the
//! hasher, and this bench is its before/after instrument on this exact
//! table — do not rename it without checking that lane's status first.
//!
//! Interns `TERM_COUNT` distinct bit-vector constants (`TermArena::bv_const`,
//! width 64), each a distinct `TermNode::BvConst`, so every call is a genuine
//! insert rather than a hash hit on an already-seen node. Distinctness is
//! *guaranteed*, not merely seeded-and-likely: values are `i.wrapping_mul(GAMMA)`
//! for `i in 0..TERM_COUNT`, and multiplication by the odd constant `GAMMA` is a
//! bijection on `u64`, so `TERM_COUNT` distinct indices always produce
//! `TERM_COUNT` distinct values with no collision risk to reason about.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::TermArena;
use criterion::{Criterion, criterion_group, criterion_main};

const TERM_COUNT: u64 = 20_000;
const WIDTH: u32 = 64;
/// splitmix64's golden-ratio odd constant; multiplication by it is a
/// bijection on `u64`, which is what makes every one of `TERM_COUNT`
/// sequential indices map to a distinct value.
const GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;

fn bench_arena_intern(c: &mut Criterion) {
    c.bench_function("arena_intern_20000_bv_const", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            for i in 0..TERM_COUNT {
                let value = i.wrapping_mul(GAMMA);
                arena
                    .bv_const(WIDTH, u128::from(value))
                    .expect("a u64 value always fits a 64-bit bv_const");
            }
            black_box(&arena);
        });
    });
}

criterion_group!(benches, bench_arena_intern);
criterion_main!(benches);
