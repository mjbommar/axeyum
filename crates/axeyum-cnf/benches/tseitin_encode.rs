//! Micro-benchmark for [`tseitin_encode`] on a fixed AIG — see the 2026-09-05
//! design review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`.
//!
//! The AIG is bit-lowered (via `axeyum-bv`) from a fixed `QF_BV` term: a 16-bit
//! multiplier `x * y` of two symbolic bit-vectors (`TermArena::bv_mul`). A
//! multiplier is the standard "nontrivial gate count" fixture for a Tseitin
//! bench — 16x16 multiplication lowers to a few thousand AND nodes, unlike a
//! single `bv_add` chain, which is nearly linear in width. Fully
//! deterministic and seed-free: two symbolic inputs and one operator fix the
//! term completely, so there is no RNG to pin.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_bv::lower_terms;
use axeyum_cnf::tseitin_encode;
use axeyum_ir::{Sort, TermArena};
use criterion::{Criterion, criterion_group, criterion_main};

const WIDTH: u32 = 16;

/// Builds the fixed AIG: a 16-bit multiplier of two symbolic inputs, bit-lowered
/// through `axeyum-bv`. Returns the AIG together with the multiplier's root
/// literals (one per output bit) that `tseitin_encode` asserts.
fn build_multiplier_aig() -> (axeyum_aig::Aig, Vec<axeyum_aig::AigLit>) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(WIDTH)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let product = arena.bv_mul(x, y).unwrap();
    let lowering = lower_terms(&arena, &[product]).unwrap();
    let roots = lowering.roots()[0].bits().to_vec();
    (lowering.aig().clone(), roots)
}

fn bench_tseitin_encode(c: &mut Criterion) {
    let (aig, roots) = build_multiplier_aig();

    c.bench_function("tseitin_encode_bvmul16", |b| {
        b.iter(|| {
            let encoding = tseitin_encode(&aig, &roots).expect("fixed AIG encodes cleanly");
            assert!(
                encoding.formula().variable_count() > 0,
                "the multiplier AIG must encode a nonempty CNF; a zero-variable \
                 result means the fixture stopped exercising the encoder"
            );
            black_box(encoding);
        });
    });
}

criterion_group!(benches, bench_tseitin_encode);
criterion_main!(benches);
