//! The existing big fallback must accept already-promoted IR coefficients.
use axeyum_cas::{CasExpr, ZeroTest, equal, recheck_zero_test};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;

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
