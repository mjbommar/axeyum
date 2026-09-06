//! Tests for [`super::fermat_two_squares`] — Fermat's theorem on sums of two
//! squares and the four pieces of Euler's descent it assembles (ADR-1650).

use super::IntPrelude;
use super::build_int_prelude;
use crate::Kernel;
use crate::env::Declaration;

/// Every declaration this module makes, in registration order.
fn owned_names(p: &IntPrelude) -> [crate::NameId; 10] {
    [
        p.dvd_zero,
        p.dvd_of_mod_eq_zero,
        p.mul_mod_eq_zero,
        p.sq_add_sq_mod_eq_of_mod_eq,
        p.exists_next_multiplier,
        p.sq_mul_add_sq_mul,
        p.dvd_of_degenerate_descent,
        p.lt_of_nat_of_lt,
        p.le_two_of_nat_le_two,
        p.not_dvd_of_nat_of_prime_of_lt,
    ]
}

/// Each name is in the environment, is a `Theorem`, and rests on no axiom.
///
/// The `contains` assertion comes FIRST deliberately: `axiom_footprint` of a
/// name the environment does not hold is also empty, so an axiom-freedom
/// assertion alone would pass for a declaration that was never made.
#[test]
fn every_declaration_is_a_checked_axiom_free_theorem() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut checked = 0usize;
    for name in owned_names(&p) {
        assert!(
            k.environment().contains(name),
            "{} is not in the environment",
            k.display_name(name)
        );
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Theorem { .. }
            ),
            "{} should be a checked Theorem",
            k.display_name(name)
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{} should rest on no axiom",
            k.display_name(name)
        );
        checked += 1;
    }
    assert_eq!(checked, 10, "the sweep must inspect every owned name");
}
