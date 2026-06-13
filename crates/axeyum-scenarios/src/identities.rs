//! Bit-twiddling identity scenarios (unsatisfiable).
//!
//! Each scenario asserts the *negation* of a well-known bit-vector theorem, so
//! it is unsatisfiable: no input violates the identity. These exercise the
//! supported lowering subset and, at small widths, are proven UNSAT
//! exhaustively by [`crate::Scenario::self_check`] without any solver — a clean
//! oracle-free UNSAT corpus.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Negation of the full-adder identity `x + y == (x ^ y) + ((x & y) << 1)`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn full_adder_identity(width: u32) -> Scenario {
    let mut arena = TermArena::new();
    let x = declare(&mut arena, "x", width);
    let y = declare(&mut arena, "y", width);

    let lhs = arena.bv_add(x, y).unwrap();
    let xor = arena.bv_xor(x, y).unwrap();
    let and = arena.bv_and(x, y).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let carry = arena.bv_shl(and, one).unwrap();
    let rhs = arena.bv_add(xor, carry).unwrap();

    finish(arena, "full_adder", width, 2)(lhs, rhs)
}

/// Negation of the xor-swap identity `((x ^ y) ^ y) == x`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn xor_swap_identity(width: u32) -> Scenario {
    let mut arena = TermArena::new();
    let x = declare(&mut arena, "x", width);
    let y = declare(&mut arena, "y", width);

    let first = arena.bv_xor(x, y).unwrap();
    let lhs = arena.bv_xor(first, y).unwrap();

    finish(arena, "xor_swap", width, 2)(lhs, x)
}

/// Negation of De Morgan's law `~(x & y) == (~x | ~y)`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn de_morgan_identity(width: u32) -> Scenario {
    let mut arena = TermArena::new();
    let x = declare(&mut arena, "x", width);
    let y = declare(&mut arena, "y", width);

    let and = arena.bv_and(x, y).unwrap();
    let lhs = arena.bv_not(and).unwrap();
    let not_x = arena.bv_not(x).unwrap();
    let not_y = arena.bv_not(y).unwrap();
    let rhs = arena.bv_or(not_x, not_y).unwrap();

    finish(arena, "de_morgan", width, 2)(lhs, rhs)
}

/// Negation of the two's-complement identity `-x == ~x + 1`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn twos_complement_identity(width: u32) -> Scenario {
    let mut arena = TermArena::new();
    let x = declare(&mut arena, "x", width);

    let lhs = arena.bv_neg(x).unwrap();
    let not_x = arena.bv_not(x).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let rhs = arena.bv_add(not_x, one).unwrap();

    finish(arena, "twos_complement", width, 1)(lhs, rhs)
}

fn declare(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    assert!(
        (1..=64).contains(&width),
        "identity scenarios support widths 1..=64"
    );
    let sym = arena.declare(name, Sort::BitVec(width)).unwrap();
    arena.var(sym)
}

/// Returns a closure that asserts `lhs != rhs` and packages the UNSAT scenario.
///
/// `symbols` is the number of `width`-bit input symbols, used to record the
/// exhaustive case count.
fn finish(
    arena: TermArena,
    label: &'static str,
    width: u32,
    symbols: u32,
) -> impl FnOnce(TermId, TermId) -> Scenario {
    move |lhs, rhs| {
        let mut arena = arena;
        let equal = arena.eq(lhs, rhs).unwrap();
        let distinct = arena.not(equal).unwrap();

        let mut builder = Query::builder(&arena);
        builder.assert(distinct).unwrap();
        let query = builder.build();

        let total_bits = symbols * width;
        let cases = if total_bits >= 64 {
            u64::MAX
        } else {
            1u64 << total_bits
        };

        Scenario {
            name: format!("identity/{label}_w{width}"),
            family: Family::Identity,
            width,
            seed: 0,
            arena,
            query,
            expectation: Expectation::Unsat {
                evidence: UnsatEvidence::Exhaustive { cases },
            },
        }
    }
}
