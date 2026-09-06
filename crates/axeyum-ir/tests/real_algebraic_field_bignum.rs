//! Arbitrary-precision algebraic-number field arithmetic (ADR-0045 storage
//! widening). `RealAlgebraic` now stores its defining polynomial (`Vec<BigInt>`)
//! and isolating interval (`BigRational`) in arbitrary precision, so field
//! arithmetic (`add`/`mul`/`neg`) computes entirely in bignum: there is no longer
//! an i128-storage ceiling, and combinations whose intermediate OR final
//! min-polynomial exceeds `i128` now DECIDE instead of declining.
//!
//! Soundness: every successful result is checked to replay
//! (`sign_at(min_poly) == Zero`), and the differential resultant determinant is
//! pinned by `sylvester_determinant_diff_bignum.rs` (isolation is
//! soundness-critical).

use std::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, Sign};
use axeyum_arith::big::BigInt;

/// `RealAlgebraic` from an LSB-first integer poly and an integer-endpoint bracket.
fn ra(poly: Vec<i128>, lo: i128, hi: i128) -> RealAlgebraic {
    RealAlgebraic::new(poly, Rational::integer(lo), Rational::integer(hi)).unwrap()
}

fn sqrt2() -> RealAlgebraic {
    ra(vec![-2, 0, 1], 1, 2) // x²−2 in (1,2) = +√2
}
fn sqrt3() -> RealAlgebraic {
    ra(vec![-3, 0, 1], 1, 2) // x²−3 in (1,2) = +√3
}
/// √2+√3 = the root of x⁴−10x²+1 in (3,4) ≈ 3.146.
fn sqrt2_plus_sqrt3() -> RealAlgebraic {
    ra(vec![1, 0, -10, 0, 1], 3, 4)
}
/// 2^(1/3) = the root of x³−2 in (1,2).
fn cbrt2() -> RealAlgebraic {
    ra(vec![-2, 0, 0, 1], 1, 2)
}

/// A `RealAlgebraic` replays iff its defining polynomial vanishes at the value it
/// denotes — the single-root invariant by construction, re-checked exactly.
fn replays(r: &RealAlgebraic) -> bool {
    r.sign_at_big(r.defining_poly()) == Some(Sign::Zero)
}

/// The defining poly as `i128` (for comparing against known small min-polys).
fn poly_i128(r: &RealAlgebraic) -> Vec<i128> {
    r.defining_poly_i128().expect("min-poly fits i128")
}

/// LSB-first `BigInt` poly literal from `i128` coefficients.
fn big(coeffs: &[i128]) -> Vec<BigInt> {
    coeffs.iter().map(|&c| BigInt::from(c)).collect()
}

// ---------------------------------------------------------------------------
// (1) Intermediate-overflow case: now decides in bignum, and replays.
// ---------------------------------------------------------------------------

/// `(√2+√3) + 2^(1/3)`: the degree-12 intermediate Sylvester determinant exceeds
/// `i128`, but the always-bignum path decides it; the result replays.
#[test]
fn intermediate_overflow_upgrades_to_some_and_replays() {
    let a = sqrt2_plus_sqrt3();
    let b = cbrt2();

    let sum = a
        .add(&b)
        .expect("bignum field arithmetic decides (√2+√3)+∛2");
    assert!(replays(&sum), "result must replay: {sum}");

    // The known min-poly (degree 12), pinned so a divergence in isolation/squarefree
    // is caught. Verified ≈ 1.414+1.732+1.260 = 4.406 is the unique root bracketed.
    assert_eq!(
        sum.defining_poly(),
        big(&[
            -3863, 696, 1290, 3488, 663, -1104, -1036, 0, 303, -8, -30, 0, 1
        ])
        .as_slice()
    );
    assert_eq!(
        sum.compare_rational(&Rational::integer(4)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        sum.compare_rational(&Rational::integer(5)),
        Some(Ordering::Less)
    );
}

/// Independent re-validation: `(√2+√3)+∛2` must equal `∛2+(√2+√3)` (addition is
/// commutative), and both must replay. The two evaluations build the resultant from
/// differently-ordered operands, so agreement is a non-trivial cross-check that the
/// bignum resultant + isolation is order-independent.
#[test]
fn intermediate_overflow_commutes() {
    let a = sqrt2_plus_sqrt3();
    let b = cbrt2();
    let sum1 = a.add(&b).expect("(√2+√3)+∛2 decides");
    let sum2 = b.add(&a).expect("∛2+(√2+√3) decides");
    assert_eq!(sum1, sum2, "α+β must equal β+α");
    assert!(replays(&sum1));
}

// ---------------------------------------------------------------------------
// (2) Regression: √2+√3 and √2·√3 still give the EXACT min-polys.
// ---------------------------------------------------------------------------

#[test]
fn sqrt2_plus_sqrt3_regression() {
    let s = sqrt2().add(&sqrt3()).expect("√2+√3 decides");
    // x⁴ − 10x² + 1, LSB-first.
    assert_eq!(poly_i128(&s), vec![1, 0, -10, 0, 1]);
    assert!(replays(&s));
}

#[test]
fn sqrt2_times_sqrt3_regression() {
    let p = sqrt2().mul(&sqrt3()).expect("√2·√3 decides");
    // x² − 6, LSB-first (= √6).
    assert_eq!(poly_i128(&p), vec![-6, 0, 1]);
    assert!(replays(&p));
    // √6 ≈ 2.449.
    assert_eq!(
        p.compare_rational(&Rational::integer(2)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        p.compare_rational(&Rational::integer(3)),
        Some(Ordering::Less)
    );
}

// ---------------------------------------------------------------------------
// (3) Large FINAL coefficients now DECIDE (arbitrary-precision storage) and
//     still replay — the former i128-storage decline is GONE (ADR-0045).
// ---------------------------------------------------------------------------

/// `√(10⁹) · ∛(10⁹) = (10⁹)^{5/6}`. The Sylvester dimension is small (deg 2 × deg
/// 3 ⇒ dim 5), but the resulting min-poly's constant term is `(10⁹)⁵ = 10⁴⁵`, far
/// beyond `i128::MAX`. Under the old i128 storage this DECLINED; now the
/// arbitrary-precision storage holds it, so the product decides and replays.
#[test]
fn huge_final_coefficient_decides_in_bignum() {
    let big_n = 1_000_000_000i128; // 10⁹
    // √(10⁹) ≈ 31622.7766, the positive root of x² − 10⁹ in (31622, 31623).
    let sqrt_big = ra(vec![-big_n, 0, 1], 31622, 31623);
    // ∛(10⁹) = 1000 exactly, the root of x³ − 10⁹ in (999, 1001).
    let cbrt_big = ra(vec![-big_n, 0, 0, 1], 999, 1001);

    let p = sqrt_big
        .mul(&cbrt_big)
        .expect("(10⁹)^{5/6} now decides in arbitrary precision");
    assert!(replays(&p), "huge-coefficient product must replay: {p}");
    // The min-poly's coefficients exceed i128 ⇒ defining_poly_i128 declines.
    assert!(
        p.defining_poly_i128().is_none(),
        "the 10⁴⁵-coefficient min-poly must not fit i128"
    );
    // (10⁹)^{5/6} = 10^{45/6} = 10^7.5 ≈ 31_622_776.6 — bracket it.
    assert_eq!(
        p.compare_rational(&Rational::integer(31_622_776)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        p.compare_rational(&Rational::integer(31_622_777)),
        Some(Ordering::Less)
    );
}

// ---------------------------------------------------------------------------
// (4) The headline coupled-NRA witness arithmetic: √(2+√3) · √(2−√3) = 1, and
//     √(2+√3)² + √(2−√3)² = 4. These are exactly the field operations the
//     2-variable grid lift needs for `x²+y²=4 ∧ x·y=1`.
// ---------------------------------------------------------------------------

/// `α = √(2+√3)`: 2+√3 is the root of (t−2)²=3 ⇒ t²−4t+1 in (3,4); its square root
/// α is the root of x⁴−4x²+1 in (1,2) ≈ 1.93185.
fn sqrt_2_plus_sqrt3() -> RealAlgebraic {
    ra(vec![1, 0, -4, 0, 1], 1, 2)
}
/// `β = √(2−√3)`: the root of x⁴−4x²+1 in (0,1) ≈ 0.51764.
fn sqrt_2_minus_sqrt3() -> RealAlgebraic {
    ra(vec![1, 0, -4, 0, 1], 0, 1)
}

#[test]
fn nested_radical_product_is_one() {
    let a = sqrt_2_plus_sqrt3();
    let b = sqrt_2_minus_sqrt3();
    // √(2+√3) · √(2−√3) = √((2+√3)(2−√3)) = √(4−3) = √1 = 1.
    let p = a.mul(&b).expect("nested-radical product decides");
    assert_eq!(
        p.compare_rational(&Rational::integer(1)),
        Some(Ordering::Equal),
        "√(2+√3)·√(2−√3) must equal exactly 1"
    );
}

#[test]
fn nested_radical_squares_sum_to_four() {
    let a = sqrt_2_plus_sqrt3();
    let b = sqrt_2_minus_sqrt3();
    // a² = 2+√3, b² = 2−√3, a²+b² = 4.
    let a2 = a.mul(&a).expect("a² decides");
    let b2 = b.mul(&b).expect("b² decides");
    let sum = a2.add(&b2).expect("a²+b² decides");
    assert_eq!(
        sum.compare_rational(&Rational::integer(4)),
        Some(Ordering::Equal),
        "√(2+√3)²+√(2−√3)² must equal exactly 4"
    );
}
