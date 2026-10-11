//! The existing big fallback must accept already-promoted IR coefficients.
use axeyum_arith::big::{BigInt, BigRational};
use axeyum_cas::{CasExpr, ZeroTest, equal, recheck_zero_test};
use axeyum_ir::Rational;

fn wide() -> Rational {
    Rational::from_big_rational(&BigRational::new(BigInt::from(1) << 192, BigInt::from(3))).unwrap()
}

#[test]
fn promoted_coefficients_reach_exact_normalization_and_replay() {
    let coefficient = wide();
    let x = CasExpr::var("x");
    let left = CasExpr::Mul(vec![
        CasExpr::Const(coefficient),
        x.clone(),
        CasExpr::int(2),
    ]);
    let right = CasExpr::Mul(vec![
        CasExpr::Const(coefficient.wide_mul(Rational::integer(2)).unwrap()),
        x,
    ]);
    let certificate = equal(&left, &right);
    assert!(matches!(
        certificate,
        ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. }
    ));
    assert!(recheck_zero_test(&left, &right, &certificate));
    assert!(!recheck_zero_test(&left, &CasExpr::zero(), &certificate));
}

#[test]
fn a_promoted_constant_has_a_nonzero_checkable_witness() {
    let left = CasExpr::Const(wide());
    let right = CasExpr::zero();
    let certificate = equal(&left, &right);
    assert!(matches!(
        certificate,
        ZeroTest::CertifiedBig { equal: false, .. }
    ));
    assert!(recheck_zero_test(&left, &right, &certificate));
}

#[test]
fn thirty_year_payment_matches_an_independent_fraction_fixture() {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/amortization_30_year.json")).unwrap();
    let numerator: BigInt = fixture["payment_numerator"]
        .as_str()
        .unwrap()
        .parse()
        .unwrap();
    let denominator: BigInt = fixture["payment_denominator"]
        .as_str()
        .unwrap()
        .parse()
        .unwrap();
    let expected = CasExpr::Const(
        Rational::from_big_rational(&BigRational::new(numerator, denominator)).unwrap(),
    );
    let rate = CasExpr::Const(Rational::new(1, 240));
    let accumulation = CasExpr::Add(vec![CasExpr::int(1), rate.clone()]);
    // Explicit reciprocal lowering for this nonzero numeric base; this does
    // not claim a public signed-exponent API or unguarded symbolic cancellation.
    let reciprocal = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(accumulation));
    let denominator = CasExpr::Add(vec![
        CasExpr::int(1),
        CasExpr::Neg(Box::new(reciprocal.pow(360))),
    ]);
    let actual = CasExpr::Div(
        Box::new(CasExpr::Mul(vec![CasExpr::int(300_000), rate])),
        Box::new(denominator),
    );
    let certificate = equal(&actual, &expected);
    assert!(matches!(
        certificate,
        ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. }
    ));
    assert!(recheck_zero_test(&actual, &expected, &certificate));
}

#[test]
fn promoted_constants_render_with_sign_and_power_precedence() {
    let coefficient = wide();
    let positive = CasExpr::Const(coefficient);
    assert_eq!(positive.to_string(), coefficient.to_string());
    let negative = CasExpr::Const(coefficient.wide_neg().unwrap());
    assert_eq!(negative.to_string(), format!("-{coefficient}"));
    assert_eq!(
        CasExpr::Pow(Box::new(negative), 2).to_string(),
        format!("(-{coefficient})^2")
    );
}
