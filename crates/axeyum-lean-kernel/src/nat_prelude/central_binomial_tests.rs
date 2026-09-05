//! Concrete-instance tests for `nat_prelude::central_binomial`.
//!
//! The bound is symbolic in `m`, so what these tests can add is (a) that it
//! INSTANTIATES at numerals with the arithmetic actually being what the module
//! doc claims, and (b) that the bound is the SHARP one — `choose (2m+1) m` is
//! at most `4^m`, not merely at most `2^(2m+1)`, which is what
//! `Nat.choose_le_two_pow` already gave. Test (b) is the whole reason the file
//! exists, so it is checked as a numeric fact about the two sides at `m = 3`:
//! `choose 7 3 = 35`, `4^3 = 64`, `2^7 = 128`.

use crate::env::Declaration;
use crate::{ExprId, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }
}

/// `Nat.mul_two_eq_add_self` states `a * 2 = a + a` at a FREE `a`.
///
/// At a numeral both sides reduce and the statement is vacuous, so the check
/// is at a free variable. The negative control is `a * 2 = a`, which is the
/// shape a dropped factor would produce and which is FALSE for every `a > 0`.
#[test]
fn mul_two_eq_add_self_states_the_doubling() {
    let mut f = Fixture::new();
    let p = f.p;
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let applied = f.const_app(p.mul_two_eq_add_self, &[a]);
    let ty = f.k.infer(applied).expect("mul_two_eq_add_self must apply");

    let expected = {
        let two = f.num(2);
        let lhs = f.mul(a, two);
        let rhs = f.add(a, a);
        f.eq(lhs, rhs)
    };
    assert!(
        f.k.def_eq(ty, expected),
        "mul_two_eq_add_self must state `a * 2 = a + a`, got {}",
        f.k.render_lean(ty)
    );
    let wrong = {
        let two = f.num(2);
        let lhs = f.mul(a, two);
        f.eq(lhs, a)
    };
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must not state `a * 2 = a`"
    );
}

/// The central binomial bound INSTANTIATES at `m = 0 … 3`, and the arithmetic
/// on both sides is what the module doc says.
///
/// `m = 3` is the discriminating row: `choose 7 3 = 35` and `4^3 = 64`, so a
/// bound that had accidentally been proved against `2^(2m+1) = 128` (the
/// weaker statement `Nat.choose_le_two_pow` already gives at this row) would
/// still be true and would still type-check — the check that separates them is
/// that the RIGHT-HAND SIDE reduces to 64.
#[test]
fn the_central_binomial_bound_instantiates() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, coefficient, bound) in [(0_u32, 1_u32, 1_u32), (1, 3, 4), (2, 10, 16), (3, 35, 64)] {
        let m_lit = f.num(m);
        let applied = f.const_app(p.choose_two_mul_succ_le_four_pow, &[m_lit]);
        let ty = f
            .k
            .infer(applied)
            .unwrap_or_else(|e| panic!("choose_two_mul_succ_le_four_pow must apply at {m}: {e:?}"));

        // The two sides, rebuilt and independently evaluated.
        let lhs = {
            let mm = f.add(m_lit, m_lit);
            let n = f.succ(mm);
            f.choose(n, m_lit)
        };
        let rhs = {
            let four = f.num(4);
            f.pow(four, m_lit)
        };
        let expected = f.le(lhs, rhs);
        assert!(
            f.k.def_eq(ty, expected),
            "the bound at m={m} must be `choose (2m+1) m <= 4^m`, got {}",
            f.k.render_lean(ty)
        );

        let coefficient_lit = f.num(coefficient);
        assert!(
            f.k.def_eq(lhs, coefficient_lit),
            "choose (2*{m}+1) {m} must reduce to {coefficient}"
        );
        let bound_lit = f.num(bound);
        assert!(f.k.def_eq(rhs, bound_lit), "4^{m} must reduce to {bound}");
    }
}

/// The `4^m` bound is STRICTLY better than what `Nat.choose_le_two_pow` gives
/// at the same row, which is the reason this file exists.
///
/// At `m = 3`: `choose_le_two_pow` bounds `choose 7 3` by `2^7 = 128`; this
/// file bounds it by `4^3 = 64`. The check is that the two right-hand sides
/// are DIFFERENT numerals — a "sharpening" that happened to prove the same
/// statement would fail here.
#[test]
fn the_bound_is_sharper_than_choose_le_two_pow() {
    let mut f = Fixture::new();
    let three = f.num(3);
    let four = f.num(4);
    let two = f.num(2);
    let seven = f.num(7);

    let sharp = f.pow(four, three);
    let blunt = f.pow(two, seven);
    assert!(
        !f.k.def_eq(sharp, blunt),
        "4^3 and 2^7 must be different numerals -- otherwise this file proves \
         nothing `choose_le_two_pow` did not already give"
    );
    let sixty_four = f.num(64);
    let one_twenty_eight = f.num(128);
    assert!(f.k.def_eq(sharp, sixty_four), "4^3 must reduce to 64");
    assert!(
        f.k.def_eq(blunt, one_twenty_eight),
        "2^7 must reduce to 128"
    );
}

/// Every name this module declares is admitted as a `Theorem` with an EMPTY
/// `Kernel::axiom_footprint`.
///
/// `Environment::contains` is asserted FIRST: `axiom_footprint` of a name that
/// is not in the environment is also empty.
#[test]
fn the_central_binomial_shelf_is_admitted_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names = [
        p.mul_two_eq_add_self,
        p.le_of_add_self_le_add_self,
        p.four_pow_eq_two_pow_add_self,
        p.choose_two_mul_succ_le_two_pow,
        p.choose_two_mul_succ_le_four_pow,
    ];
    assert_eq!(names.len(), 5, "the shelf has five theorems");
    for name in names {
        let shown = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{shown} must be admitted"))
                .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a Theorem, not {decl:?}"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must be axiom-free, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// `Nat.four_pow_eq_two_pow_add_self` states `4^m = 2^(m+m)` at a FREE `m`.
///
/// The negative control is `4^m = 2^m`, which is TRUE at `m = 0` and false
/// everywhere else — the exact shape a dropped exponent doubling produces.
#[test]
fn four_pow_bridge_states_the_exponent_doubling() {
    let mut f = Fixture::new();
    let p = f.p;
    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let applied = f.const_app(p.four_pow_eq_two_pow_add_self, &[m]);
    let ty =
        f.k.infer(applied)
            .expect("four_pow_eq_two_pow_add_self must apply");

    let build = |f: &mut Fixture, exponent: ExprId| -> ExprId {
        let four = f.num(4);
        let two = f.num(2);
        let lhs = f.pow(four, m);
        let rhs = f.pow(two, exponent);
        f.eq(lhs, rhs)
    };
    let doubled = f.add(m, m);
    let expected = build(&mut f, doubled);
    assert!(
        f.k.def_eq(ty, expected),
        "four_pow_eq_two_pow_add_self must state `4^m = 2^(m+m)`, got {}",
        f.k.render_lean(ty)
    );
    let wrong = build(&mut f, m);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must not state `4^m = 2^m`"
    );
}
