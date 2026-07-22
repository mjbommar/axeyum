//! TL2.6 arbitrary-precision natural-literal representation gates.

use axeyum_lean_kernel::{ExprNode, Kernel, KernelError, Lit, NatLit};

const BELOW_2_128: &str = "340282366920938463463374607431768211455";
const AT_2_128: &str = "340282366920938463463374607431768211456";
const ABOVE_2_128: &str = "340282366920938463463374607431768211457";
const HUGE: &str = "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031";

#[test]
fn decimal_values_round_trip_below_at_and_above_u128_capacity() {
    for digits in [BELOW_2_128, AT_2_128, ABOVE_2_128, HUGE] {
        let value = NatLit::from_decimal(digits).expect("valid decimal natural");
        assert_eq!(value.to_string(), digits);
    }

    let canonical = NatLit::from_decimal("000000001").expect("leading zeroes are valid");
    assert_eq!(canonical.to_string(), "1");
}

#[test]
fn malformed_decimal_values_are_rejected() {
    for invalid in ["", "+1", "-1", " 1", "1 ", "1_0", "12a", "١"] {
        assert!(
            NatLit::from_decimal(invalid).is_none(),
            "accepted {invalid:?}"
        );
    }
}

#[test]
fn interning_and_structural_operations_preserve_the_exact_bignum() {
    let value = NatLit::from_decimal(HUGE).expect("valid decimal natural");
    let mut kernel = Kernel::new();
    let literal = kernel.lit(Lit::Nat(value.clone()));
    let duplicate = kernel.lit(Lit::Nat(value.clone()));
    let nearby = kernel.lit(Lit::Nat(
        NatLit::from_decimal(ABOVE_2_128).expect("valid decimal natural"),
    ));

    assert_eq!(literal, duplicate, "equal bignums must intern identically");
    assert_ne!(literal, nearby, "distinct bignums must not alias");
    assert_eq!(kernel.expr_node(literal), &ExprNode::Lit(Lit::Nat(value)));
    assert_eq!(kernel.lift_loose_bvars(literal, 0, u32::MAX), literal);
    let substitution = kernel.sort_zero();
    assert_eq!(kernel.instantiate(literal, &[substitution]), literal);
    assert_eq!(kernel.substitute_expr_levels(literal, &[]), literal);
    assert_eq!(kernel.render_lean(literal), HUGE);
}

#[test]
fn representation_does_not_self_authorize_the_nat_bootstrap() {
    let mut kernel = Kernel::new();
    let literal = kernel.lit(Lit::Nat(
        NatLit::from_decimal(AT_2_128).expect("valid decimal natural"),
    ));
    assert!(matches!(
        kernel.infer(literal),
        Err(KernelError::NatLiteralBootstrapMismatch { .. })
    ));
}
