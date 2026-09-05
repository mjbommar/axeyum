//! Micro-benchmark for AND-node construction, i.e. the deterministic
//! structural-hashing insert path (`AndUniqueTable`, private to the crate) that
//! [`Aig::and`] drives — see the 2026-09-05 design review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`.
//!
//! `AndUniqueTable` itself is a private struct (`src/lib.rs`, not `pub`);
//! `Aig::and` is its only entry point, so benchmarking `and` directly on a
//! seeded-but-fixed stream of AND nodes measures exactly the insert +
//! structural-hash-lookup cost the table exists for, with no internal
//! visibility change needed (unlike the `axeyum-solver` benches, which do
//! need one — see `crate::bench_internals` there).
//!
//! Builds 200 primary inputs, then 4,000 AND nodes whose two operands are
//! each a seeded pseudo-random choice among the inputs and previously built
//! AND nodes (with a seeded coin flip on inversion), so later nodes have
//! increasingly large fan-in trees and hash-table occupancy — closer to a
//! real bit-blast AIG's shape than a shallow, uniform-depth tree. Fixed seed,
//! no external `rand` dependency (see D4/D5 in the design review).

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_aig::{Aig, AigLit};
use criterion::{Criterion, criterion_group, criterion_main};

const SEED: u64 = 0xA16_A16_A16_A16;
const INPUT_COUNT: usize = 200;
const AND_NODE_COUNT: usize = 4_000;

/// splitmix64 (Vigna), a fixed-seed deterministic generator — no external
/// `rand` dependency.
struct SplitMix64(u64);

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound`. `bound` and the result are `usize` because
    /// every caller here uses this to index a slice.
    fn next_below(&mut self, bound: usize) -> usize {
        let bound = u64::try_from(bound).expect("pool sizes here are far below u64::MAX");
        usize::try_from(self.next_u64() % bound).expect("value below a usize bound fits usize")
    }

    fn next_bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

/// Builds the fixed AIG: `INPUT_COUNT` inputs, then `AND_NODE_COUNT` AND
/// nodes over a seeded pseudo-random pool of prior literals (inputs and
/// earlier AND outputs), each operand independently inverted by a seeded
/// coin flip.
fn build_aig() -> Aig {
    let mut rng = SplitMix64::new(SEED);
    let mut aig = Aig::new();
    let mut pool: Vec<AigLit> = Vec::with_capacity(INPUT_COUNT + AND_NODE_COUNT);
    for i in 0..INPUT_COUNT {
        pool.push(aig.input(format!("in{i}")));
    }
    for _ in 0..AND_NODE_COUNT {
        let pick = |rng: &mut SplitMix64, pool: &[AigLit]| -> AigLit {
            let lit = pool[rng.next_below(pool.len())];
            if rng.next_bool() { lit.negated() } else { lit }
        };
        let lhs = pick(&mut rng, &pool);
        let rhs = pick(&mut rng, &pool);
        pool.push(aig.and(lhs, rhs));
    }
    aig
}

fn bench_and_construction(c: &mut Criterion) {
    c.bench_function("aig_and_construction_4000_nodes", |b| {
        b.iter(|| {
            let aig = build_aig();
            let stats = aig.construction_stats();
            assert_eq!(
                stats.and_requests,
                u64::try_from(AND_NODE_COUNT).expect("AND_NODE_COUNT fits u64"),
                "every Aig::and call must be counted once, regardless of whether \
                 structural hashing, trivial simplification, or absorption \
                 resolved it — a different count means fewer AND nodes were \
                 actually requested than the fixture intends"
            );
            black_box(aig);
        });
    });
}

criterion_group!(benches, bench_and_construction);
criterion_main!(benches);
