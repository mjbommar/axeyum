//! Multiplication and division scenarios (now that `bvmul`/`bvudiv`/`bvurem`
//! lower).
//!
//! [`factor_target`] is the classic "find factors of an observed product"
//! query a consumer hits when inverting a multiplication: satisfiable by
//! construction with the chosen factors as witness. [`distributivity_identity`]
//! asserts the negation of `x * (y + z) == x * y + x * z`, which is
//! unsatisfiable and, at small widths, proven so exhaustively by the evaluator.
//!
//! [`division_target`] pins an input through its quotient and remainder against
//! a fixed divisor (a satisfiable, uniquely-determined query).
//! [`division_roundtrip_identity`] asserts the negation of the Euclidean
//! identity `(x udiv k) * k + (x urem k) == x`, which is unsatisfiable.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64, UnsatEvidence, mask};

/// Builds a satisfiable factoring query `x * y == p` over `width`-bit values,
/// where `p` is the wrapping product of concrete factors drawn from `seed`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn factor_target(width: u32, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "factor_target supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let product = arena.bv_mul(x, y).unwrap();

    // Concrete factors give the ground-truth product (wrapping at `width`).
    let factor_x = rng.next_u128() & mask(width);
    let factor_y = rng.next_u128() & mask(width);
    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: factor_x,
        },
    );
    witness.set(
        y_sym,
        Value::Bv {
            width,
            value: factor_y,
        },
    );
    let product_value = eval(&arena, product, &witness)
        .expect("product evaluates under the witness")
        .as_bv()
        .expect("product is bit-vector sorted")
        .1;
    let target = arena.bv_const(width, product_value).unwrap();
    let goal = arena.eq(product, target).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("arith/factor_w{width}_s{seed:#018x}"),
        family: Family::Arithmetic,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Builds the unsatisfiable negation of left-distributivity
/// `x * (y + z) == x * y + x * z` over `width`-bit values.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn distributivity_identity(width: u32) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "distributivity_identity supports widths 1..=64"
    );
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
    let z_sym = arena.declare("z", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let z = arena.var(z_sym);

    let y_plus_z = arena.bv_add(y, z).unwrap();
    let lhs = arena.bv_mul(x, y_plus_z).unwrap();
    let x_times_y = arena.bv_mul(x, y).unwrap();
    let x_times_z = arena.bv_mul(x, z).unwrap();
    let rhs = arena.bv_add(x_times_y, x_times_z).unwrap();

    let equal = arena.eq(lhs, rhs).unwrap();
    let distinct = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(distinct).unwrap();
    let query = builder.build();

    let total_bits = 3 * width;
    let cases = if total_bits >= 64 {
        u64::MAX
    } else {
        1u64 << total_bits
    };

    Scenario {
        name: format!("arith/distributivity_w{width}"),
        family: Family::Arithmetic,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive { cases },
        },
    }
}

/// Builds a satisfiable query that pins `x` through its quotient and remainder
/// against a fixed nonzero divisor drawn from `seed`: `x udiv k == q` and
/// `x urem k == r`, which (for `k != 0`) determine `x` uniquely.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn division_target(width: u32, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "division_target supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    // A nonzero divisor, so the quotient/remainder pin `x` to a single value.
    let divisor_value = (rng.next_u128() % mask(width).max(1)) + 1;
    let divisor = arena.bv_const(width, divisor_value & mask(width)).unwrap();
    let quotient = arena.bv_udiv(x, divisor).unwrap();
    let remainder = arena.bv_urem(x, divisor).unwrap();

    let secret = rng.next_u128() & mask(width);
    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: secret,
        },
    );
    let quotient_value = eval_bv(&arena, quotient, &witness);
    let remainder_value = eval_bv(&arena, remainder, &witness);
    let quotient_const = arena.bv_const(width, quotient_value).unwrap();
    let remainder_const = arena.bv_const(width, remainder_value).unwrap();
    let quotient_goal = arena.eq(quotient, quotient_const).unwrap();
    let remainder_goal = arena.eq(remainder, remainder_const).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(quotient_goal).unwrap();
    builder.assert(remainder_goal).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("arith/divtarget_w{width}_s{seed:#018x}"),
        family: Family::Arithmetic,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Builds the unsatisfiable negation of the Euclidean roundtrip identity
/// `(x udiv k) * k + (x urem k) == x` for a fixed nonzero constant `k = 3`.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn division_roundtrip_identity(width: u32) -> Scenario {
    assert!(
        (2..=64).contains(&width),
        "division_roundtrip_identity supports widths 2..=64 (k = 3 must fit)"
    );
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let three = arena.bv_const(width, 3).unwrap();
    let quotient = arena.bv_udiv(x, three).unwrap();
    let remainder = arena.bv_urem(x, three).unwrap();
    let product = arena.bv_mul(quotient, three).unwrap();
    let reconstructed = arena.bv_add(product, remainder).unwrap();

    let equal = arena.eq(reconstructed, x).unwrap();
    let distinct = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(distinct).unwrap();
    let query = builder.build();

    let cases = if width >= 64 { u64::MAX } else { 1u64 << width };

    Scenario {
        name: format!("arith/divroundtrip_w{width}"),
        family: Family::Arithmetic,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive { cases },
        },
    }
}

fn eval_bv(arena: &TermArena, term: axeyum_ir::TermId, assignment: &Assignment) -> u128 {
    eval(arena, term, assignment)
        .expect("term evaluates under the witness")
        .as_bv()
        .expect("term is bit-vector sorted")
        .1
}
