//! Micro-benchmark for [`Incremental`]'s pivot/feasibility loop (Dutertre–de
//! Moura §4) — the warm simplex a `DPLL(T)` arithmetic theory drives (see the
//! 2026-09-05 design review, §4 item 3:
//! `docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md`).
//!
//! The input is a seeded, fixed-size feasible LP: 12 problem variables, 18
//! rows, each row `Σ aⱼ·xⱼ ≥ rhs` over 3 seeded variables with small positive
//! seeded coefficients. Every row is a lower bound (`Rel::Ge`) with a positive
//! right-hand side and only nonnegative coefficients, so the system is
//! feasible **by construction** for any seed (every variable is unbounded
//! above, so making them all large enough always satisfies every row) — this
//! sidesteps the risk of a seeded-random instance turning out infeasible.
//! Starting every problem variable at its default value (0) violates every
//! row's `≥ rhs > 0` bound, so [`Incremental::check`] must actually pivot to
//! find a feasible point rather than accept the all-zero point immediately.
//!
//! The generator is a fixed-seed `splitmix64` (no external `rand` dependency;
//! the workspace intentionally has none — see D4/D5 in the design review),
//! so the LP is byte-identical across runs and hosts.
//!
//! Requires the `bench-internals` feature (implies `full`); see
//! `crate::bench_internals` in `src/lib.rs` for why `Incremental` is
//! reachable here at all.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::Rational;
use axeyum_solver::bench_internals::{Incremental, Rel, Status};
use criterion::{Criterion, criterion_group, criterion_main};

const SEED: u64 = 0x5EED_5A17_5A17_5EED;
const NVARS: usize = 12;
const ROWS: usize = 18;
const VARS_PER_ROW: usize = 3;

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

    /// A value in `0..bound`.
    fn next_below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }

    /// A value in `0..bound`, for indexing a slice of length `bound`.
    fn index_below(&mut self, bound: usize) -> usize {
        let bound = u64::try_from(bound).expect("row/variable counts here are tiny");
        usize::try_from(self.next_below(bound)).expect("value below a usize bound fits usize")
    }
}

/// Builds the fixed seeded feasible LP: sparse rows plus their `Rel::Ge`
/// bounds, ready for [`Incremental::new`] + repeated [`Incremental::assert_bound`].
fn build_lp() -> (Vec<Vec<(usize, Rational)>>, Vec<Rational>) {
    let mut rng = SplitMix64::new(SEED);
    let mut rows = Vec::with_capacity(ROWS);
    let mut rhs = Vec::with_capacity(ROWS);
    for _ in 0..ROWS {
        let mut row = Vec::with_capacity(VARS_PER_ROW);
        let mut used = [false; NVARS];
        while row.len() < VARS_PER_ROW {
            let j = rng.index_below(NVARS);
            if used[j] {
                continue;
            }
            used[j] = true;
            let coeff = 1 + rng.next_below(3); // in {1, 2, 3}, always positive
            row.push((j, Rational::integer(i128::from(coeff))));
        }
        row.sort_by_key(|(j, _)| *j);
        rows.push(row);
        let rhs_value = 3 + rng.next_below(7); // in [3, 9]
        rhs.push(Rational::integer(i128::from(rhs_value)));
    }
    (rows, rhs)
}

fn bench_simplex_check(c: &mut Criterion) {
    let (rows, rhs) = build_lp();

    c.bench_function("simplex_incremental_check_feasible_lp", |b| {
        b.iter(|| {
            let mut engine = Incremental::new(NVARS, rows.clone())
                .expect("fixed 12x18 LP is well under MAX_TABLEAU_CELLS");
            for (i, &r) in rhs.iter().enumerate() {
                engine.assert_bound(i, Rel::Ge, r);
            }
            let status = engine.check(None);
            assert_eq!(
                status,
                Status::Feasible,
                "the LP is feasible by construction (all-positive coefficients, \
                 lower bounds only, every variable unbounded above); a different \
                 verdict means the generator or the engine changed"
            );
            black_box(status);
        });
    });
}

criterion_group!(benches, bench_simplex_check);
criterion_main!(benches);
