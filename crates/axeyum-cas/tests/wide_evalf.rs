//! Approximation accepts promoted constants without narrowing or infinity/infinity.
use axeyum_arith::big::{BigInt, BigRational};
use axeyum_cas::{CasExpr, evalf};
use axeyum_ir::Rational;

fn constant(numerator: BigInt, denominator: BigInt) -> CasExpr {
    CasExpr::Const(Rational::from_big_rational(&BigRational::new(numerator, denominator)).unwrap())
}

#[test]
fn balanced_promoted_ratio_is_finite_and_preserves_sign() {
    let magnitude: BigInt = BigInt::from(1) << 4096;
    let positive = constant(&magnitude + BigInt::from(1), &magnitude * 3 + 1);
    let negative = constant(-(&magnitude + BigInt::from(1)), &magnitude * 3 + 1);
    assert_eq!(evalf(&positive, &[]), Some(1.0 / 3.0));
    assert_eq!(evalf(&negative, &[]), Some(-1.0 / 3.0));
    assert_eq!(evalf(&positive.sin(), &[]), Some((1.0_f64 / 3.0).sin()));
}

#[test]
fn promoted_scales_and_small_path_keep_approximate_semantics() {
    let wide: BigInt = BigInt::from(1) << 192;
    assert_eq!(
        evalf(&constant(wide.clone(), BigInt::from(1)), &[]),
        Some(2.0_f64.powi(192))
    );
    assert_eq!(
        evalf(&constant(BigInt::from(1), wide), &[]),
        Some(2.0_f64.powi(-192))
    );
    assert_eq!(evalf(&CasExpr::rat(-7, 3), &[]), Some(-7.0 / 3.0));
    assert_eq!(evalf(&CasExpr::var("unbound"), &[]), None);
}
