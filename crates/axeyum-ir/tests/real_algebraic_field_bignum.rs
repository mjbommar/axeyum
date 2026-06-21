//! Bignum-retry path for algebraic-number field arithmetic (nra-cad-nlsat-plan.md
//! step 2). These tests run ONLY with the `bignum` feature enabled.
//!
//! The slice keeps `RealAlgebraic`'s storage `i128` (poly `Vec<i128>` + i128
//! `Rational` interval). The bignum retry only removes the *intermediate*
//! resultant/Sturm overflow: when the i128 fast path declines but the FINAL
//! min-poly + isolating interval fit `i128`, the combination now SUCCEEDS; when
//! the final result genuinely exceeds `i128`, it still declines gracefully.
//!
//! Soundness: every successful result is checked to replay (`sign_at(min_poly) ==
//! Zero`), and a differential test pins the i128 and bignum paths to the SAME
//! min-poly on small inputs (isolation is soundness-critical).
#![cfg(feature = "bignum")]

use axeyum_ir::poly_big::{Combine, combine_retry};
use axeyum_ir::{Rational, RealAlgebraic, Sign};

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
    r.sign_at(r.defining_poly()) == Some(Sign::Zero)
}

// ---------------------------------------------------------------------------
// (1) Intermediate-overflow case: the i128 path declines, bignum decides.
// ---------------------------------------------------------------------------

/// `(√2+√3) + 2^(1/3)`: the degree-12 intermediate Sylvester determinant overflows
/// `i128` (the i128-only path returns `None`), but the FINAL squarefree min-poly
/// fits `i128`, so the bignum retry decides it and the result replays.
#[test]
fn intermediate_overflow_upgrades_to_some_and_replays() {
    let a = sqrt2_plus_sqrt3();
    let b = cbrt2();

    // At commit 2a54d51 (i128-only, no retry) this combination returned `None`
    // (the degree-12 intermediate Sylvester determinant overflows `i128`). With
    // the bignum retry the public `add` now decides it; the result must replay.
    let sum = a.add(&b).expect("bignum retry must decide (√2+√3)+∛2");
    assert!(replays(&sum), "result must replay: {sum}");

    // The known min-poly (degree 12), pinned so a divergence in isolation/squarefree
    // is caught. Verified ≈ 1.414+1.732+1.260 = 4.406 is the unique root bracketed.
    assert_eq!(
        sum.defining_poly(),
        &[
            -3863, 696, 1290, 3488, 663, -1104, -1036, 0, 303, -8, -30, 0, 1
        ]
    );
    // The bracket contains the true value 4.406…
    let (lo, hi) = sum.interval();
    assert_eq!(sum.compare_rational(&lo), Some(std::cmp::Ordering::Greater));
    assert_eq!(sum.compare_rational(&hi), Some(std::cmp::Ordering::Less));
    assert_eq!(
        sum.compare_rational(&Rational::integer(4)),
        Some(std::cmp::Ordering::Greater)
    );
    assert_eq!(
        sum.compare_rational(&Rational::integer(5)),
        Some(std::cmp::Ordering::Less)
    );
}

/// Independent re-validation of the intermediate-overflow result: `(√2+√3)+∛2`
/// must equal `∛2+(√2+√3)` (algebraic addition is commutative), and both must
/// replay. The two evaluations build the resultant from differently-ordered
/// operands, so agreement is a non-trivial cross-check that the bignum
/// resultant + isolation is order-independent (a soundness guard distinct from the
/// pinned-min-poly assertion above).
#[test]
fn intermediate_overflow_bignum_commutes() {
    let a = sqrt2_plus_sqrt3();
    let b = cbrt2();
    let sum1 = a.add(&b).expect("(√2+√3)+∛2 decides via bignum retry");
    let sum2 = b.add(&a).expect("∛2+(√2+√3) decides via bignum retry");
    assert_eq!(sum1, sum2, "α+β must equal β+α");
    assert!(replays(&sum1));
}

// ---------------------------------------------------------------------------
// (2) Regression: √2+√3 and √2·√3 still give the EXACT i128 min-polys.
// ---------------------------------------------------------------------------

#[test]
fn sqrt2_plus_sqrt3_regression() {
    let s = sqrt2()
        .add(&sqrt3())
        .expect("√2+√3 decides on the i128 fast path");
    // x⁴ − 10x² + 1, LSB-first.
    assert_eq!(s.defining_poly(), &[1, 0, -10, 0, 1]);
    assert!(replays(&s));
}

#[test]
fn sqrt2_times_sqrt3_regression() {
    let p = sqrt2()
        .mul(&sqrt3())
        .expect("√2·√3 decides on the i128 fast path");
    // x² − 6, LSB-first (= √6).
    assert_eq!(p.defining_poly(), &[-6, 0, 1]);
    assert!(replays(&p));
    // √6 ≈ 2.449.
    assert_eq!(
        p.compare_rational(&Rational::integer(2)),
        Some(std::cmp::Ordering::Greater)
    );
    assert_eq!(
        p.compare_rational(&Rational::integer(3)),
        Some(std::cmp::Ordering::Less)
    );
}

// ---------------------------------------------------------------------------
// (3) Genuine FINAL overflow still declines gracefully (no panic).
// ---------------------------------------------------------------------------

/// A LOW-dimension combination whose FINAL min-poly coefficients genuinely exceed
/// `i128`: `√(10⁹) · ∛(10⁹) = (10⁹)^{5/6}`. The Sylvester dimension is small
/// (deg 2 × deg 3 ⇒ dim 5, so no factorial-cost blowup — the bignum determinant
/// itself is cheap), but the resulting defining polynomial's constant term is
/// `(10⁹)⁵ = 10⁴⁵`, far beyond `i128::MAX ≈ 1.7·10³⁸`. So even the bignum retry,
/// after computing the exact answer, cannot fit it into the `i128`-backed
/// `RealAlgebraic` storage and must DECLINE gracefully (`None`) — never panic,
/// never a wrong value. (A bignum-backed `RealAlgebraic` is a deferred later
/// slice; until then this is the correct conservative behavior.)
#[test]
fn genuine_final_overflow_declines_gracefully() {
    let big = 1_000_000_000i128; // 10⁹
    // √(10⁹) ≈ 31622.7766, the positive root of x² − 10⁹ in (31622, 31623).
    let sqrt_big = ra(vec![-big, 0, 1], 31622, 31623);
    // ∛(10⁹) = 1000 exactly, the root of x³ − 10⁹ in (999, 1001).
    let cbrt_big = ra(vec![-big, 0, 0, 1], 999, 1001);

    // Product: (10⁹)^{5/6}. The exact min-poly has a 10⁴⁵ constant term ⇒ cannot
    // fit i128 ⇒ graceful decline. The test asserts it does NOT panic and returns
    // None (the i128 path declines on overflow; the bignum retry computes the
    // exact poly but `to_i128` rejects the oversized coefficient).
    let p = sqrt_big.mul(&cbrt_big);
    assert!(
        p.is_none(),
        "final-coefficient overflow must decline gracefully (None), got {p:?}"
    );

    // Defensive: even a deeper combination that exceeds the bignum Sylvester-
    // dimension cap declines fast (no factorial hang). ∛(10⁹) combined with the
    // degree-4 √2+√3 product has small dimension and a huge final poly ⇒ None too.
    let p2 = cbrt_big.mul(&sqrt2_plus_sqrt3());
    assert!(
        p2.is_none(),
        "huge-coefficient product must decline, got {p2:?}"
    );
}

// ---------------------------------------------------------------------------
// (4) Differential test: the i128 and bignum paths agree on small inputs where
//     BOTH succeed. Isolation is soundness-critical, so this pins them together.
// ---------------------------------------------------------------------------

#[test]
fn i128_and_bignum_paths_agree_on_small_inputs() {
    // Cases the i128 fast path handles (public add/mul succeed there without retry),
    // compared coefficient-for-coefficient against the bignum `combine_retry`.
    let cases: &[(RealAlgebraic, RealAlgebraic)] = &[
        (sqrt2(), sqrt3()),
        (sqrt3(), sqrt2()),
        (sqrt2(), sqrt2()),
        (cbrt2(), sqrt2()),
        (sqrt2(), cbrt2()),
    ];
    for (a, b) in cases {
        let (alo, ahi) = a.interval();
        let (blo, bhi) = b.interval();

        // Sum.
        let i128_sum = a.add(b).expect("i128 add");
        let big_sum = combine_retry(
            a.defining_poly(),
            alo,
            ahi,
            b.defining_poly(),
            blo,
            bhi,
            Combine::Sum,
        )
        .expect("bignum add")
        .to_i128()
        .expect("fits i128");
        assert_eq!(
            i128_sum.defining_poly(),
            big_sum.0.as_slice(),
            "sum min-poly must agree for {a} + {b}"
        );

        // Product.
        let i128_prod = a.mul(b).expect("i128 mul");
        let big_prod = combine_retry(
            a.defining_poly(),
            alo,
            ahi,
            b.defining_poly(),
            blo,
            bhi,
            Combine::Product,
        )
        .expect("bignum mul")
        .to_i128()
        .expect("fits i128");
        assert_eq!(
            i128_prod.defining_poly(),
            big_prod.0.as_slice(),
            "product min-poly must agree for {a} · {b}"
        );
    }
}
