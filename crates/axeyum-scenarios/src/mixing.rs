//! Crypto-style mixing-function inversion scenarios (satisfiable).
//!
//! These mirror the kind of query a symbolic-execution or CTF/reverse-
//! engineering consumer produces when inverting a keyed mixing function: given
//! an observed output, find an input that produces it. The function is built
//! from the supported lowering subset (`xor`, `add`, constant `rotate_left`),
//! and the output target is computed by concrete execution so the query is
//! satisfiable by construction with a known witness.

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64, mask};

/// Builds a satisfiable inversion of a `rounds`-round keyed mixing function
/// over `width`-bit values, seeded by `seed`.
///
/// The function is `f(x)`, where each round computes
/// `rotate_left(r, (acc xor k) + c)` for round constants `k`, `c` and rotation
/// amount `r` drawn from `seed`. The scenario asserts `f(x) == f(x*)` for a
/// concrete secret `x*`, so `x = x*` is a known satisfying witness.
///
/// # Panics
///
/// Panics if `width` exceeds 64 (constant generation is limited to 64-bit
/// draws) or on arena corruption.
pub fn mixing_inversion(width: u32, rounds: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "mixing_inversion supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", axeyum_ir::Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);

    let mut acc = x;
    for _ in 0..rounds {
        let k = bv_const(&mut arena, width, &mut rng);
        let c = bv_const(&mut arena, width, &mut rng);
        let rot = u32::try_from(rng.below(u64::from(width))).expect("amount < width fits u32");
        let xored = arena.bv_xor(acc, k).unwrap();
        let added = arena.bv_add(xored, c).unwrap();
        acc = arena.rotate_left(rot, added).unwrap();
    }

    // Concrete execution gives the ground-truth output for a secret input.
    let secret = rng.next_u128() & mask(width);
    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: secret,
        },
    );
    let target_value = eval(&arena, acc, &witness)
        .expect("mixing function evaluates under the witness")
        .as_bv()
        .expect("mixing function is bit-vector sorted")
        .1;
    let target = arena.bv_const(width, target_value).unwrap();
    let goal = arena.eq(acc, target).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("mixing/w{width}_r{rounds}_s{seed:#018x}"),
        family: Family::Mixing,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

fn bv_const(arena: &mut TermArena, width: u32, rng: &mut SplitMix64) -> TermId {
    let value = rng.next_u128() & mask(width);
    arena.bv_const(width, value).unwrap()
}
