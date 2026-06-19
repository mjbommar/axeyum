//! Linear-algebra scenarios over bit-vectors: a destination of the
//! [formal mathematics tour](../../../docs/curriculum/README.md).
//!
//! Fixed-size matrices with `BitVec` entries make the core linear-algebra
//! identities **exhaustively checkable**: matrix arithmetic is ring arithmetic
//! mod `2ʷ`, so the identities hold and their negations are unsatisfiable over
//! the (small) finite domain. Solving `A·x = b` is satisfiable with the chosen
//! `x` as witness. All oracle-free per ADR-0008, inside the BV lowering subset.
//!
//! Matrices are `2×2`, stored row-major as `[m00, m01, m10, m11]`.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Declares four fresh `width`-bit entries `name0..name3` of a `2×2` matrix.
fn matrix(arena: &mut TermArena, name: &str, width: u32) -> [TermId; 4] {
    let mut cell = |i: usize| {
        let sym = arena
            .declare(&format!("{name}{i}"), Sort::BitVec(width))
            .unwrap();
        arena.var(sym)
    };
    [cell(0), cell(1), cell(2), cell(3)]
}

/// `2×2` matrix product `A·B`, row-major.
fn mat_mul(arena: &mut TermArena, a: [TermId; 4], b: [TermId; 4]) -> [TermId; 4] {
    let [a00, a01, a10, a11] = a;
    let [b00, b01, b10, b11] = b;
    let entry = |arena: &mut TermArena, p, q, r, s| {
        let pr = arena.bv_mul(p, q).unwrap();
        let qs = arena.bv_mul(r, s).unwrap();
        arena.bv_add(pr, qs).unwrap()
    };
    [
        entry(arena, a00, b00, a01, b10),
        entry(arena, a00, b01, a01, b11),
        entry(arena, a10, b00, a11, b10),
        entry(arena, a10, b01, a11, b11),
    ]
}

/// Transpose of a `2×2` matrix (swap the off-diagonal).
fn transpose(m: [TermId; 4]) -> [TermId; 4] {
    [m[0], m[2], m[1], m[3]]
}

/// Determinant `m00·m11 − m01·m10` of a `2×2` matrix.
fn det(arena: &mut TermArena, m: [TermId; 4]) -> TermId {
    let ad = arena.bv_mul(m[0], m[3]).unwrap();
    let bc = arena.bv_mul(m[1], m[2]).unwrap();
    arena.bv_sub(ad, bc).unwrap()
}

/// Asserts that two `2×2` matrices are entrywise equal, as one conjunction.
fn matrices_equal(arena: &mut TermArena, x: [TermId; 4], y: [TermId; 4]) -> TermId {
    let mut acc: Option<TermId> = None;
    for i in 0..4 {
        let eq = arena.eq(x[i], y[i]).unwrap();
        acc = Some(match acc {
            None => eq,
            Some(prev) => arena.and(prev, eq).unwrap(),
        });
    }
    acc.expect("a 2x2 matrix has four entries")
}

/// Packages the negation of a matrix identity (`lhs == rhs` entrywise) as an
/// UNSAT scenario proven exhaustively over `symbol_count` `width`-bit entries.
fn unsat_identity(
    mut arena: TermArena,
    label: String,
    width: u32,
    symbol_count: u32,
    lhs: [TermId; 4],
    rhs: [TermId; 4],
) -> Scenario {
    let equal = matrices_equal(&mut arena, lhs, rhs);
    let differ = arena.not(equal).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::LinearAlgebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (symbol_count * width),
            },
        },
    }
}

/// Negation of the determinant–product law `det(A·B) = det(A)·det(B)` for `2×2`
/// matrices — unsatisfiable, proven exhaustively (8 entries).
///
/// # Panics
///
/// Panics if `8 * width` exceeds the enumeration budget or on arena corruption.
pub fn det_product_2x2(width: u32) -> Scenario {
    assert!(
        8 * width <= 20,
        "det_product stays inside the exhaustive budget"
    );
    let mut arena = TermArena::new();
    let a = matrix(&mut arena, "a", width);
    let b = matrix(&mut arena, "b", width);
    let ab = mat_mul(&mut arena, a, b);
    let lhs = det(&mut arena, ab);
    let da = det(&mut arena, a);
    let db = det(&mut arena, b);
    let rhs = arena.bv_mul(da, db).unwrap();
    // A scalar identity: reuse the matrix machinery by comparing 1×1 "matrices".
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();
    Scenario {
        name: format!("linear_algebra/det_product_2x2_w{width}"),
        family: Family::LinearAlgebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (8 * width),
            },
        },
    }
}

/// Negation of the transpose–product law `(A·B)ᵀ = Bᵀ·Aᵀ` for `2×2` matrices —
/// unsatisfiable, proven exhaustively (8 entries).
///
/// # Panics
///
/// Panics if `8 * width` exceeds the enumeration budget or on arena corruption.
pub fn transpose_product_2x2(width: u32) -> Scenario {
    assert!(8 * width <= 20, "transpose_product stays inside the budget");
    let mut arena = TermArena::new();
    let a = matrix(&mut arena, "a", width);
    let b = matrix(&mut arena, "b", width);
    let ab = mat_mul(&mut arena, a, b);
    let lhs = transpose(ab);
    let bt = transpose(b);
    let at = transpose(a);
    let rhs = mat_mul(&mut arena, bt, at);
    unsat_identity(
        arena,
        format!("linear_algebra/transpose_product_2x2_w{width}"),
        width,
        8,
        lhs,
        rhs,
    )
}

/// Negation of matrix-multiplication associativity `(A·B)·C = A·(B·C)` for `2×2`
/// matrices — unsatisfiable, proven exhaustively (12 entries; use `width = 1`,
/// i.e. matrices over 𝔽₂).
///
/// # Panics
///
/// Panics if `12 * width` exceeds the enumeration budget or on arena corruption.
pub fn mult_associative_2x2(width: u32) -> Scenario {
    assert!(
        12 * width <= 20,
        "associativity needs width 1 to stay in budget"
    );
    let mut arena = TermArena::new();
    let a = matrix(&mut arena, "a", width);
    let b = matrix(&mut arena, "b", width);
    let c = matrix(&mut arena, "c", width);
    let ab = mat_mul(&mut arena, a, b);
    let lhs = mat_mul(&mut arena, ab, c);
    let bc = mat_mul(&mut arena, b, c);
    let rhs = mat_mul(&mut arena, a, bc);
    unsat_identity(
        arena,
        format!("linear_algebra/mult_associative_2x2_w{width}"),
        width,
        12,
        lhs,
        rhs,
    )
}

/// A satisfiable `2×2` linear system `A·x = b` over `width`-bit arithmetic, with
/// a concrete solution `x` as witness (`A` and `b` are constants derived from
/// `seed`; `b` is computed as `A·x` so the system is consistent by construction).
///
/// # Panics
///
/// Panics if `width` is outside `1..=32` or on arena corruption.
pub fn linear_solve_2x2(width: u32, seed: u64) -> Scenario {
    use crate::SplitMix64;
    use crate::mask;
    assert!(
        (1..=32).contains(&width),
        "linear_solve supports widths 1..=32"
    );
    let m = mask(width);
    let mut rng = SplitMix64::new(seed);
    let a: [u128; 4] = [
        rng.next_u128() & m,
        rng.next_u128() & m,
        rng.next_u128() & m,
        rng.next_u128() & m,
    ];
    let x: [u128; 2] = [rng.next_u128() & m, rng.next_u128() & m];
    let mul = |p: u128, q: u128| p.wrapping_mul(q) & m;
    let b: [u128; 2] = [
        (mul(a[0], x[0]).wrapping_add(mul(a[1], x[1]))) & m,
        (mul(a[2], x[0]).wrapping_add(mul(a[3], x[1]))) & m,
    ];

    let mut arena = TermArena::new();
    let x0_sym = arena.declare("x0", Sort::BitVec(width)).unwrap();
    let x1_sym = arena.declare("x1", Sort::BitVec(width)).unwrap();
    let x0 = arena.var(x0_sym);
    let x1 = arena.var(x1_sym);
    let consts: Vec<TermId> = a
        .iter()
        .map(|&v| arena.bv_const(width, v).unwrap())
        .collect();
    let b0c = arena.bv_const(width, b[0]).unwrap();
    let b1c = arena.bv_const(width, b[1]).unwrap();

    let row0 = {
        let t0 = arena.bv_mul(consts[0], x0).unwrap();
        let t1 = arena.bv_mul(consts[1], x1).unwrap();
        let sum = arena.bv_add(t0, t1).unwrap();
        arena.eq(sum, b0c).unwrap()
    };
    let row1 = {
        let t0 = arena.bv_mul(consts[2], x0).unwrap();
        let t1 = arena.bv_mul(consts[3], x1).unwrap();
        let sum = arena.bv_add(t0, t1).unwrap();
        arena.eq(sum, b1c).unwrap()
    };
    let system = arena.and(row0, row1).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(system).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(x0_sym, Value::Bv { width, value: x[0] });
    witness.set(x1_sym, Value::Bv { width, value: x[1] });

    Scenario {
        name: format!("linear_algebra/linear_solve_2x2_w{width}_s{seed:#018x}"),
        family: Family::LinearAlgebra,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Declares nine fresh `width`-bit entries `name0..name8` of a `3×3` matrix
/// (row-major).
fn matrix3(arena: &mut TermArena, name: &str, width: u32) -> [TermId; 9] {
    let mut cell = |i: usize| {
        let sym = arena
            .declare(&format!("{name}{i}"), Sort::BitVec(width))
            .unwrap();
        arena.var(sym)
    };
    [
        cell(0),
        cell(1),
        cell(2),
        cell(3),
        cell(4),
        cell(5),
        cell(6),
        cell(7),
        cell(8),
    ]
}

/// `3×3` matrix product `A·B` (row-major).
fn mat_mul_3x3(arena: &mut TermArena, a: [TermId; 9], b: [TermId; 9]) -> [TermId; 9] {
    let mut out = a;
    for row in 0..3 {
        for col in 0..3 {
            let mut acc: Option<TermId> = None;
            for k in 0..3 {
                let term = arena.bv_mul(a[row * 3 + k], b[k * 3 + col]).unwrap();
                acc = Some(match acc {
                    None => term,
                    Some(prev) => arena.bv_add(prev, term).unwrap(),
                });
            }
            out[row * 3 + col] = acc.unwrap();
        }
    }
    out
}

/// Determinant of a `3×3` matrix (cofactor expansion along the first row).
fn det_3x3(arena: &mut TermArena, m: [TermId; 9]) -> TermId {
    let minor = |arena: &mut TermArena, p: TermId, q: TermId, r: TermId, s: TermId| {
        let ps = arena.bv_mul(p, s).unwrap();
        let qr = arena.bv_mul(q, r).unwrap();
        arena.bv_sub(ps, qr).unwrap()
    };
    let m0 = minor(arena, m[4], m[5], m[7], m[8]);
    let t0 = arena.bv_mul(m[0], m0).unwrap();
    let m1 = minor(arena, m[3], m[5], m[6], m[8]);
    let t1 = arena.bv_mul(m[1], m1).unwrap();
    let m2 = minor(arena, m[3], m[4], m[6], m[7]);
    let t2 = arena.bv_mul(m[2], m2).unwrap();
    let t0_minus_t1 = arena.bv_sub(t0, t1).unwrap();
    arena.bv_add(t0_minus_t1, t2).unwrap()
}

/// Negation of the `3×3` determinant–product law `det(A·B) = det(A)·det(B)` over
/// 𝔽₂ (entries `width = 1`) — unsatisfiable, proven exhaustively (18 entries =
/// 2¹⁸ cases).
///
/// # Panics
///
/// Panics if `width ≠ 1` (only 𝔽₂ keeps 18 entries inside the budget) or on
/// arena corruption.
pub fn det_product_3x3_f2() -> Scenario {
    let width = 1u32;
    let mut arena = TermArena::new();
    let a = matrix3(&mut arena, "a", width);
    let b = matrix3(&mut arena, "b", width);
    let ab = mat_mul_3x3(&mut arena, a, b);
    let lhs = det_3x3(&mut arena, ab);
    let da = det_3x3(&mut arena, a);
    let db = det_3x3(&mut arena, b);
    let rhs = arena.bv_mul(da, db).unwrap();
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    Scenario {
        name: "linear_algebra/det_product_3x3_f2".to_string(),
        family: Family::LinearAlgebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive { cases: 1u64 << 18 },
        },
    }
}

/// A deterministic catalog of linear-algebra scenarios.
pub fn linear_algebra_catalog() -> Vec<Scenario> {
    vec![
        det_product_2x2(2),
        transpose_product_2x2(2),
        mult_associative_2x2(1),
        linear_solve_2x2(8, 0x10A),
        linear_solve_2x2(16, 0x10B),
        det_product_3x3_f2(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_algebra_catalog_self_checks() {
        let scenarios = linear_algebra_catalog();
        assert!(!scenarios.is_empty());
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::LinearAlgebra);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "linear-algebra scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn det_product_is_exhaustively_unsat() {
        match det_product_2x2(2).self_check().unwrap() {
            UnsatEvidence::Exhaustive { cases } => assert_eq!(cases, 1 << 16),
            sampled @ UnsatEvidence::Sampled { .. } => {
                panic!("expected exhaustive, got {sampled:?}")
            }
        }
    }

    #[test]
    fn linear_solve_witness_is_valid() {
        let scenario = linear_solve_2x2(8, 0x10A);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
