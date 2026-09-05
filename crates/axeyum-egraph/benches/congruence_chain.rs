//! Micro-benchmark for [`EGraph::merge`] + [`EGraph::explain`] over a chain of
//! forced congruences — see the 2026-09-05 design review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`.
//!
//! Fixture (fully deterministic; a congruence chain has no free choices to
//! seed, unlike the AIG/simplex fixtures, which draw from a pool):
//! `CHAIN_LEN` distinct leaf e-nodes `a_0 .. a_N`, one application node
//! `f(a_i)` per leaf under a single function declaration, and `N` union
//! operations `merge(a_i, a_{i+1}, reason = i)` chaining every leaf into one
//! class. Congruence closure then forces every `f(a_i)` into that same class
//! too. `explain(f(a_0), f(a_N))` must walk the full N-step proof-forest path
//! plus one congruence step, exercising both the union-find merge path and
//! the explanation reconstruction the design review names.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_egraph::EGraph;
use criterion::{Criterion, criterion_group, criterion_main};

const CHAIN_LEN: usize = 500;
/// Declaration id for the chained application `f(a_i)`; leaf declarations use
/// `0..=CHAIN_LEN` so this must sit above them.
const F_DECL: u32 = 1_000_000;

fn bench_congruence_chain(c: &mut Criterion) {
    c.bench_function("egraph_congruence_chain_merge_explain", |b| {
        b.iter(|| {
            let mut g = EGraph::new();
            let leaves = (0..=CHAIN_LEN)
                .map(|i| g.add(u32::try_from(i).expect("CHAIN_LEN fits u32"), &[]))
                .collect::<Vec<_>>();
            let apps = leaves
                .iter()
                .map(|&leaf| g.add(F_DECL, &[leaf]))
                .collect::<Vec<_>>();
            for i in 0..CHAIN_LEN {
                g.merge(
                    leaves[i],
                    leaves[i + 1],
                    u32::try_from(i).expect("CHAIN_LEN fits u32"),
                );
            }
            assert!(
                g.equal(apps[0], apps[CHAIN_LEN]),
                "congruence closure must merge f(a_0) with f(a_N) once every \
                 leaf a_0..a_N is in one class"
            );
            let proof = g.explain(apps[0], apps[CHAIN_LEN]);
            assert!(
                !proof.is_empty(),
                "a chain of {CHAIN_LEN} forced unions must produce a nonempty \
                 explanation for the congruent pair"
            );
            black_box(proof);
        });
    });
}

criterion_group!(benches, bench_congruence_chain);
criterion_main!(benches);
