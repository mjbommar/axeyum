//! Micro-benchmark for [`eliminate_int_divmod`] — every `QF_LIA`/`QF_NIA`
//! query with `div`/`mod`/`abs` pays this preprocessing step, and it had no
//! bench of any kind before this file. See
//! `docs/research/12-performance/bench-theories-2026-09-07.md`.
//!
//! Two fixtures, because the module's own doc comment names two structurally
//! different costs:
//!
//! - `many_constant_groups`: `N` distinct dividends, each `div`ed and `mod`ed
//!   by a nonzero constant — one fresh-variable group per dividend, each
//!   contributing a constant number of defining (Euclidean) constraints. This
//!   is the common case (`x div 3`, `y mod 5`, …) and should be linear in `N`.
//! - `zero_divisor_congruence`: `N` distinct dividends each `div`ed by the
//!   **constant zero** — the underspecified-total-function corner this
//!   repo's Hard Rules flag by name (`div`/`mod`-by-constant-zero). Every such
//!   group needs a congruence lemma against every *other* zero-divisor group
//!   (`emit_zero_divisor_congruence`, pairwise Ackermann, capped at
//!   `MAX_CONGRUENCE_GROUPS` = 48), so this path is quadratic in the number of
//!   zero-divisor groups where the constant-divisor path is linear — the same
//!   shape [`eliminate_arrays`]'s quadratic pairwise pass has, in a different
//!   module. `N` is pinned at `MAX_CONGRUENCE_GROUPS` (the worst case the
//!   route ever actually emits full congruence for; one more group and it
//!   relaxes instead, per `ZeroDivisorCongruence`).
//!
//! What this proxies: `many_constant_groups` is an ordinary arithmetic query
//! with several unrelated modular constraints (a checksum / hashing-style
//! encoding); `zero_divisor_congruence` is the worst case for a query with
//! many uses of `div`/`mod` by a literal `0` (transcribed from a template
//! that does not special-case the divisor, e.g. a generated bit-blast helper).

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::TermArena;
use axeyum_rewrite::{MAX_CONGRUENCE_GROUPS, eliminate_int_divmod};
use criterion::{Criterion, criterion_group, criterion_main};

const N_CONSTANT_GROUPS: usize = 200;

/// `N_CONSTANT_GROUPS` distinct dividends `x_i`, each asserted via
/// `x_i div 3 = q_i` and `x_i mod 3 = r_i` for fresh `q_i`/`r_i` — a linear
/// number of independent groups, none of them zero-divisor.
fn bench_many_constant_groups(c: &mut Criterion) {
    c.bench_function("eliminate_int_divmod_many_constant_groups", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let three = arena.int_const(3);
            let mut assertions = Vec::with_capacity(N_CONSTANT_GROUPS * 2);
            for i in 0..N_CONSTANT_GROUPS {
                let x = arena
                    .int_var(&format!("x_{i}"))
                    .expect("distinct declared name per dividend");
                let q = arena
                    .int_var(&format!("q_{i}"))
                    .expect("distinct declared name per quotient");
                let r = arena
                    .int_var(&format!("r_{i}"))
                    .expect("distinct declared name per remainder");
                let div = arena
                    .int_div(x, three)
                    .expect("int_div of int var by int const");
                let modt = arena
                    .int_mod(x, three)
                    .expect("int_mod of int var by int const");
                assertions.push(arena.eq(div, q).expect("eq of matching-sort int terms"));
                assertions.push(arena.eq(modt, r).expect("eq of matching-sort int terms"));
            }
            let elim =
                eliminate_int_divmod(&mut arena, &assertions).expect("IR builder cannot fail here");
            black_box(elim);
        });
    });
}

/// `MAX_CONGRUENCE_GROUPS` distinct dividends `y_i`, each `div`ed by the
/// literal `0` — the worst case the pairwise Ackermann congruence pass ever
/// emits in full (one more group and `ZeroDivisorCongruence` relaxes instead
/// of growing further).
fn bench_zero_divisor_congruence(c: &mut Criterion) {
    c.bench_function("eliminate_int_divmod_zero_divisor_congruence", |b| {
        b.iter(|| {
            let mut arena = TermArena::new();
            let zero = arena.int_const(0);
            let mut assertions = Vec::with_capacity(MAX_CONGRUENCE_GROUPS);
            for i in 0..MAX_CONGRUENCE_GROUPS {
                let y = arena
                    .int_var(&format!("y_{i}"))
                    .expect("distinct declared name per dividend");
                let q = arena
                    .int_var(&format!("zq_{i}"))
                    .expect("distinct declared name per quotient");
                let div = arena.int_div(y, zero).expect("int_div by the literal zero");
                assertions.push(arena.eq(div, q).expect("eq of matching-sort int terms"));
            }
            let elim =
                eliminate_int_divmod(&mut arena, &assertions).expect("IR builder cannot fail here");
            black_box(elim);
        });
    });
}

criterion_group!(
    benches,
    bench_many_constant_groups,
    bench_zero_divisor_congruence
);
criterion_main!(benches);
