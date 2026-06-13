//! Memory (`QF_ABV`) scenarios: self-checking store/load traces (ADR-0010).
//!
//! These mirror the memory a symbolic-execution consumer reasons about: a
//! symbolic base memory, a chain of symbolic `store`s, and a symbolic `load`.
//! The load's expected value is computed by concrete execution under a chosen
//! witness, so the query is satisfiable by construction and self-verifies
//! through the evaluator — exactly like the bit-vector families, now over
//! arrays.

use axeyum_ir::{ArrayValue, Assignment, Sort, TermArena, Value, eval};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64, mask};

/// Builds a satisfiable memory trace: a symbolic base memory, `stores` symbolic
/// writes, then a symbolic load asserted equal to its concretely-computed
/// value. Exercises read-over-write and Ackermann (selects over the base).
///
/// # Panics
///
/// Panics if a width exceeds 64 or on arena corruption.
pub fn memory_trace(addr_width: u32, elem_width: u32, stores: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&addr_width) && (1..=64).contains(&elem_width),
        "memory_trace supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let mem_sym = arena
        .declare(
            "mem",
            Sort::Array {
                index: addr_width,
                element: elem_width,
            },
        )
        .unwrap();
    let mem = arena.var(mem_sym);

    // A concrete base memory: a default plus a few entries.
    let mut base = ArrayValue::constant(addr_width, elem_width, rng.next_u128() & mask(elem_width));
    for _ in 0..3 {
        base = base.store(
            rng.next_u128() & mask(addr_width),
            rng.next_u128() & mask(elem_width),
        );
    }
    witness.set(mem_sym, Value::Array(base));

    // A chain of symbolic stores, each pinned by the witness.
    let mut current = mem;
    for index in 0..stores {
        let addr_sym = arena
            .declare(&format!("a{index}"), Sort::BitVec(addr_width))
            .unwrap();
        let val_sym = arena
            .declare(&format!("v{index}"), Sort::BitVec(elem_width))
            .unwrap();
        witness.set(addr_sym, bv(addr_width, rng.next_u128() & mask(addr_width)));
        witness.set(val_sym, bv(elem_width, rng.next_u128() & mask(elem_width)));
        let addr = arena.var(addr_sym);
        let val = arena.var(val_sym);
        current = arena.store(current, addr, val).unwrap();
    }

    // A symbolic load, asserted equal to its concrete value under the witness.
    let probe_sym = arena.declare("probe", Sort::BitVec(addr_width)).unwrap();
    witness.set(
        probe_sym,
        bv(addr_width, rng.next_u128() & mask(addr_width)),
    );
    let probe = arena.var(probe_sym);
    let loaded = arena.select(current, probe).unwrap();
    let expected_value = eval(&arena, loaded, &witness)
        .expect("load evaluates under the witness")
        .as_bv()
        .expect("load is bit-vector sorted")
        .1;
    let expected = arena.bv_const(elem_width, expected_value).unwrap();
    let goal = arena.eq(loaded, expected).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("memory/trace_a{addr_width}_e{elem_width}_s{stores}_{seed:#018x}"),
        family: Family::Memory,
        width: elem_width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A deterministic catalog of memory (`QF_ABV`) scenarios across sizes.
///
/// Kept separate from [`crate::catalog`] (which is pure bit-vector) because
/// these require array elimination to solve. Every entry is satisfiable by
/// construction and passes [`Scenario::self_check`].
pub fn memory_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for addr_width in [3u32, 4] {
        for (round, stores) in [1usize, 2, 4].into_iter().enumerate() {
            let seed = 0xBEEF_0000_u64 ^ ((u64::from(addr_width) << 8) | round as u64);
            scenarios.push(memory_trace(addr_width, 8, stores, seed));
        }
    }
    scenarios
}

fn bv(width: u32, value: u128) -> Value {
    Value::Bv { width, value }
}
