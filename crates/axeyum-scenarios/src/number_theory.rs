//! Number-theory scenarios: the first destination of the
//! [formal mathematics tour](../../../docs/curriculum/README.md).
//!
//! Number theory's computational core (gcd, Bézout, modular inverses, parity) is
//! exactly the decidable/computable fragment axeyum already handles, so it is the
//! first destination with a self-checking exercise family. Two oracle-free
//! constructions (ADR-0008):
//!
//! - **SAT by computation + witness.** Compute the answer with a textbook
//!   algorithm (extended Euclid, Hensel-lifted inverse), carry it as the witness,
//!   and assert the identity it satisfies — self-checked by the evaluator.
//! - **UNSAT by bounded enumeration.** Assert the negation of a number-theoretic
//!   identity; `self_check` confirms no input over the width satisfies it.
//!
//! All scenarios stay inside the `BitVec` lowering subset (modular arithmetic mod
//! `2ʷ` *is* bit-vector arithmetic), so the pure-Rust backend decides them.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence, mask};

/// Extended Euclidean algorithm: returns `(g, x, y)` with `a*x + b*y = g` and
/// `g = gcd(a, b) ≥ 0`.
// `a, b, g, x, y` are the standard names of the Bézout/gcd identity.
#[allow(clippy::many_single_char_names)]
fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        let sign = if a < 0 { -1 } else { 1 };
        (a * sign, sign, 0)
    } else {
        let (g, x, y) = extended_gcd(b, a.rem_euclid(b));
        (g, y, x - (a.div_euclid(b)) * y)
    }
}

/// Multiplicative inverse of an odd `a` modulo `2^width`, by Hensel lifting
/// (`inv ← inv·(2 − a·inv)`), all arithmetic reduced mod `2^width`.
fn inverse_mod_pow2(a: u128, width: u32) -> u128 {
    let m = mask(width);
    // a is odd, so a ≡ 1 (mod 2) and inv = 1 is correct to one bit; each step
    // doubles the number of correct low bits.
    let mut inv = 1u128 & m;
    let steps = width.next_power_of_two().trailing_zeros() + 1;
    for _ in 0..=steps {
        let two = 2u128 & m;
        let a_inv = a.wrapping_mul(inv) & m;
        let correction = two.wrapping_sub(a_inv) & m;
        inv = inv.wrapping_mul(correction) & m;
    }
    inv & m
}

/// Bézout's identity `a·x + b·y = gcd(a, b)` over `width`-bit modular arithmetic,
/// satisfiable with the extended-Euclid coefficients as witness.
///
/// # Panics
///
/// Panics if `width` is outside `1..=63`, if `a == 0 && b == 0`, or on arena
/// corruption.
// `a, b, g, x, y` are standard Bézout names; the u128↔i128 casts are the
// deliberate two's-complement reduction of the (possibly negative) coefficients
// into the `width`-bit modular domain (`a, b < 2^63`, so no value is lost).
#[allow(
    clippy::many_single_char_names,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss
)]
pub fn bezout_identity(width: u32, a: u128, b: u128) -> Scenario {
    assert!((1..=63).contains(&width), "bezout supports widths 1..=63");
    let m = mask(width);
    let (a, b) = (a & m, b & m);
    assert!(a != 0 || b != 0, "bezout needs a nonzero (a, b)");

    let (g, x, y) = extended_gcd(a as i128, b as i128);
    // Reduce the (possibly negative) coefficients and gcd into the width.
    let x_val = (x as u128) & m;
    let y_val = (y as u128) & m;
    let g_val = (g as u128) & m;

    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
    let xt = arena.var(x_sym);
    let yt = arena.var(y_sym);
    let a_c = arena.bv_const(width, a).unwrap();
    let b_c = arena.bv_const(width, b).unwrap();
    let g_c = arena.bv_const(width, g_val).unwrap();
    let ax = arena.bv_mul(a_c, xt).unwrap();
    let by = arena.bv_mul(b_c, yt).unwrap();
    let sum = arena.bv_add(ax, by).unwrap();
    let goal = arena.eq(sum, g_c).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: x_val,
        },
    );
    witness.set(
        y_sym,
        Value::Bv {
            width,
            value: y_val,
        },
    );

    Scenario {
        name: format!("number_theory/bezout_w{width}_a{a}_b{b}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Modular inverse `a · a⁻¹ ≡ 1 (mod 2^width)` for odd `a`, satisfiable with the
/// computed inverse as witness.
///
/// # Panics
///
/// Panics if `width` is outside `1..=63` or on arena corruption.
pub fn modular_inverse(width: u32, a: u128) -> Scenario {
    assert!(
        (1..=63).contains(&width),
        "modular_inverse supports widths 1..=63"
    );
    let m = mask(width);
    // Force `a` odd so the inverse exists mod a power of two.
    let a = (a | 1) & m;
    let inv = inverse_mod_pow2(a, width);

    let mut arena = TermArena::new();
    let inv_sym = arena.declare("inv", Sort::BitVec(width)).unwrap();
    let inv_t = arena.var(inv_sym);
    let a_c = arena.bv_const(width, a).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let product = arena.bv_mul(a_c, inv_t).unwrap();
    let goal = arena.eq(product, one).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(inv_sym, Value::Bv { width, value: inv });

    Scenario {
        name: format!("number_theory/mod_inverse_w{width}_a{a}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Negation of "the product of consecutive integers is even":
/// `k·(k+1) ≡ 0 (mod 2)`. Unsatisfiable, proven exhaustively over the width.
///
/// # Panics
///
/// Panics if `width` is outside `1..=20` or on arena corruption.
pub fn consecutive_product_even(width: u32) -> Scenario {
    assert!(
        (1..=20).contains(&width),
        "consecutive_product_even stays inside the exhaustive budget"
    );
    let mut arena = TermArena::new();
    let k_sym = arena.declare("k", Sort::BitVec(width)).unwrap();
    let k = arena.var(k_sym);
    let one = arena.bv_const(width, 1).unwrap();
    let k1 = arena.bv_add(k, one).unwrap();
    let product = arena.bv_mul(k, k1).unwrap();
    let low_bit = arena.bv_and(product, one).unwrap();
    // Assert the product is ODD (low bit = 1): the negation of "even", so UNSAT.
    let odd = arena.eq(low_bit, one).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(odd).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("number_theory/consecutive_product_even_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// Negation of "squaring preserves parity": `x² ≡ x (mod 2)`. Unsatisfiable,
/// proven exhaustively over the width.
///
/// # Panics
///
/// Panics if `width` is outside `1..=20` or on arena corruption.
pub fn square_parity(width: u32) -> Scenario {
    assert!(
        (1..=20).contains(&width),
        "square_parity stays inside the exhaustive budget"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let one = arena.bv_const(width, 1).unwrap();
    let sq = arena.bv_mul(x, x).unwrap();
    let sq_parity = arena.bv_and(sq, one).unwrap();
    let x_parity = arena.bv_and(x, one).unwrap();
    let same = arena.eq(sq_parity, x_parity).unwrap();
    // Assert the parities DIFFER: the negation of the identity, so UNSAT.
    let differ = arena.not(same).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("number_theory/square_parity_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// A **Pythagorean triple** `a² + b² = c²` with `a, b ≠ 0`, satisfiable with the
/// classic `(3, 4, 5)` as witness — number theory meeting geometry, decidable
/// over bit-vectors.
///
/// # Panics
///
/// Panics if `width` is outside `5..=32` or on arena corruption.
pub fn pythagorean_triple(width: u32) -> Scenario {
    assert!(
        (5..=32).contains(&width),
        "pythagorean_triple needs width 5..=32"
    );
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let c_sym = arena.declare("c", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let c = arena.var(c_sym);
    let a2 = arena.bv_mul(a, a).unwrap();
    let b2 = arena.bv_mul(b, b).unwrap();
    let c2 = arena.bv_mul(c, c).unwrap();
    let sum = arena.bv_add(a2, b2).unwrap();
    let pyth = arena.eq(sum, c2).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let a_eq_zero = arena.eq(a, zero).unwrap();
    let a_nz = arena.not(a_eq_zero).unwrap();
    let b_eq_zero = arena.eq(b, zero).unwrap();
    let b_nz = arena.not(b_eq_zero).unwrap();
    let nontrivial = arena.and(a_nz, b_nz).unwrap();
    let goal = arena.and(pyth, nontrivial).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(a_sym, Value::Bv { width, value: 3 });
    witness.set(b_sym, Value::Bv { width, value: 4 });
    witness.set(c_sym, Value::Bv { width, value: 5 });

    Scenario {
        name: format!("number_theory/pythagorean_triple_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **Chinese Remainder Theorem**: `x ≡ 2 (mod 3) ∧ x ≡ 3 (mod 5)` has the
/// solution `x = 8` (mod 15). Satisfiable, witnessed by `x = 8`.
///
/// # Panics
///
/// Panics if `width` is outside `4..=32` or on arena corruption.
pub fn crt_witness(width: u32) -> Scenario {
    assert!((4..=32).contains(&width), "crt_witness needs width 4..=32");
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let three = arena.bv_const(width, 3).unwrap();
    let five = arena.bv_const(width, 5).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let r_three = arena.bv_const(width, 3).unwrap();
    let x_mod_3 = arena.bv_urem(x, three).unwrap();
    let x_mod_5 = arena.bv_urem(x, five).unwrap();
    let c1 = arena.eq(x_mod_3, two).unwrap();
    let c2 = arena.eq(x_mod_5, r_three).unwrap();
    let goal = arena.and(c1, c2).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(x_sym, Value::Bv { width, value: 8 });

    Scenario {
        name: format!("number_theory/crt_witness_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **Quadratic residue** mod a fixed prime `p = 7`: `2` is a residue
/// (`3² = 9 ≡ 2`), so `∃x<7. x² ≡ 2 (mod 7)` is satisfiable, witnessed by `x=3`.
///
/// # Panics
///
/// Panics if `width` is outside `6..=16` or on arena corruption.
pub fn quadratic_residue_sat(width: u32) -> Scenario {
    assert!(
        (6..=16).contains(&width),
        "quadratic_residue needs width 6..=16"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let seven = arena.bv_const(width, 7).unwrap();
    let lt = arena.bv_ult(x, seven).unwrap();
    let sq = arena.bv_mul(x, x).unwrap();
    let seven2 = arena.bv_const(width, 7).unwrap();
    let sq_mod = arena.bv_urem(sq, seven2).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let is_two = arena.eq(sq_mod, two).unwrap();
    let goal = arena.and(lt, is_two).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(x_sym, Value::Bv { width, value: 3 });

    Scenario {
        name: format!("number_theory/quadratic_residue_sat_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **Quadratic non-residue** mod a fixed prime `p = 7`: `3` is a non-residue, so
/// `∃x<7. x² ≡ 3 (mod 7)` is unsatisfiable — proven exhaustively over the width.
///
/// # Panics
///
/// Panics if `width` is outside `6..=10` or on arena corruption.
pub fn quadratic_nonresidue_unsat(width: u32) -> Scenario {
    assert!(
        (6..=10).contains(&width),
        "quadratic_nonresidue stays in budget"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let seven = arena.bv_const(width, 7).unwrap();
    let lt = arena.bv_ult(x, seven).unwrap();
    let sq = arena.bv_mul(x, x).unwrap();
    let seven2 = arena.bv_const(width, 7).unwrap();
    let sq_mod = arena.bv_urem(sq, seven2).unwrap();
    let three = arena.bv_const(width, 3).unwrap();
    let is_three = arena.eq(sq_mod, three).unwrap();
    let claim = arena.and(lt, is_three).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("number_theory/quadratic_nonresidue_unsat_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// **Sum of two squares (satisfiable)**: `25 = 3² + 4²`, witnessed by `(3, 4)`.
///
/// # Panics
///
/// Panics if `width` is outside `6..=32` or on arena corruption.
pub fn sum_of_two_squares_sat(width: u32) -> Scenario {
    assert!(
        (6..=32).contains(&width),
        "sum_of_two_squares_sat needs width 6..=32"
    );
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let a2 = arena.bv_mul(a, a).unwrap();
    let b2 = arena.bv_mul(b, b).unwrap();
    let sum = arena.bv_add(a2, b2).unwrap();
    let n = arena.bv_const(width, 25).unwrap();
    let goal = arena.eq(sum, n).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(a_sym, Value::Bv { width, value: 3 });
    witness.set(b_sym, Value::Bv { width, value: 4 });

    Scenario {
        name: format!("number_theory/sum_of_two_squares_sat_w{width}"),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **Sum of two squares (impossible)**: `11 ≡ 3 (mod 4)` is not a sum of two
/// squares. With `a, b < 4` (the only candidates, since `4² > 11`), `a² + b² = 11`
/// is unsatisfiable — proven exhaustively (the `width = 5` domain holds every
/// `a² + b²` exactly, so no wraparound).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn sum_of_two_squares_none() -> Scenario {
    let width = 5u32;
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let four = arena.bv_const(width, 4).unwrap();
    let a_lt = arena.bv_ult(a, four).unwrap();
    let b_lt = arena.bv_ult(b, four).unwrap();
    let bound = arena.and(a_lt, b_lt).unwrap();
    let a2 = arena.bv_mul(a, a).unwrap();
    let b2 = arena.bv_mul(b, b).unwrap();
    let sum = arena.bv_add(a2, b2).unwrap();
    let eleven = arena.bv_const(width, 11).unwrap();
    let is_eleven = arena.eq(sum, eleven).unwrap();
    let claim = arena.and(bound, is_eleven).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();

    Scenario {
        name: "number_theory/sum_of_two_squares_none_n11".to_string(),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (2 * width),
            },
        },
    }
}

/// **RSA round-trip**: with the toy key `n = 33 = 3·11`, `e = 3`, `d = 7`
/// (`e·d = 21 ≡ 1 mod φ(33)=20`), decryption inverts encryption —
/// `(mᵉ)ᵈ ≡ m (mod n)` for every `m < n` (true for all residues since `n` is
/// squarefree). Encoded with a modular reduction after each multiply (so values
/// stay below `n`), the negation is unsatisfiable, proven exhaustively.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn rsa_roundtrip() -> Scenario {
    let width = 11u32; // products a·b < 33·33 = 1089 < 2^11 fit before reduction
    let n = 33u128;
    let mut arena = TermArena::new();
    let m_sym = arena.declare("m", Sort::BitVec(width)).unwrap();
    let m = arena.var(m_sym);
    let n_c = arena.bv_const(width, n).unwrap();
    // mod-multiply helper: (x·y) mod n.
    let mod_mul = |arena: &mut TermArena, x: TermId, y: TermId| -> TermId {
        let prod = arena.bv_mul(x, y).unwrap();
        arena.bv_urem(prod, n_c).unwrap()
    };
    // m^21 mod n = ((m^3 mod n)^7 mod n), built as 20 modular multiplications.
    let mut power = m;
    for _ in 1..21 {
        power = mod_mul(&mut arena, power, m);
    }
    // m itself reduced mod n (m < n already, but keep it uniform).
    let m_mod = arena.bv_urem(m, n_c).unwrap();
    let m_lt_n = arena.bv_ult(m, n_c).unwrap();
    let roundtrips = arena.eq(power, m_mod).unwrap();
    let fails = arena.not(roundtrips).unwrap();
    let claim = arena.and(m_lt_n, fails).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();

    Scenario {
        name: "number_theory/rsa_roundtrip_n33".to_string(),
        family: Family::NumberTheory,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// A deterministic catalog of number-theory scenarios.
pub fn number_theory_catalog() -> Vec<Scenario> {
    vec![
        bezout_identity(16, 240, 46),
        bezout_identity(8, 12, 18),
        modular_inverse(16, 0x35),
        modular_inverse(8, 7),
        consecutive_product_even(8),
        consecutive_product_even(16),
        square_parity(8),
        square_parity(16),
        pythagorean_triple(8),
        pythagorean_triple(16),
        crt_witness(8),
        quadratic_residue_sat(6),
        quadratic_nonresidue_unsat(6),
        sum_of_two_squares_sat(8),
        sum_of_two_squares_none(),
        rsa_roundtrip(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_theory_catalog_self_checks() {
        let scenarios = number_theory_catalog();
        assert!(!scenarios.is_empty());
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::NumberTheory);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "number-theory scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn extended_gcd_satisfies_bezout() {
        for (a, b) in [(240i128, 46i128), (12, 18), (17, 5), (100, 0)] {
            let (g, x, y) = extended_gcd(a, b);
            assert_eq!(a * x + b * y, g, "bezout failed for ({a}, {b})");
            assert!(g >= 0);
        }
    }

    #[test]
    fn inverse_mod_pow2_is_a_genuine_inverse() {
        for width in [4u32, 8, 16, 32] {
            let m = mask(width);
            for a in [1u128, 3, 7, 0x35, 0xABCD & m] {
                let a = (a | 1) & m;
                let inv = inverse_mod_pow2(a, width);
                assert_eq!(a.wrapping_mul(inv) & m, 1, "a={a} width={width}");
            }
        }
    }

    #[test]
    fn bezout_witness_is_carried_and_valid() {
        let scenario = bezout_identity(16, 240, 46);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
