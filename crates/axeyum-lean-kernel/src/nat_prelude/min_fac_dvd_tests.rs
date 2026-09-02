//! Concrete-instance tests for `nat_prelude::min_fac_dvd`.
//!
//! These are theorems, so the kernel checked them; what a check here adds is
//! that they are not VACUOUS and that they say what the names claim.
//! `Nat.minFacAuxDvd`'s premise `add (succ cp) fuel = n` is exactly the kind of
//! hypothesis that could make a statement unusable, so each check below
//! instantiates the top-level form at a concrete `n` and reads off the inferred
//! type, which forces the premise to be dischargeable and pins the VALUE
//! `minFac n` reduces to.
//!
//! `12` and `15` discriminate: `minFac 12 = 2` exercises the very first
//! candidate, `minFac 15 = 3` exercises one failed candidate before the
//! successful one, and a `minFac` that returned the wrong candidate would give
//! `dvd 3 12` or `dvd 2 15` — both of which the negative controls rule out (the
//! second is not even true).

use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

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

/// `Nat.min_fac_dvd` INSTANTIATES, and at `12` and `15` it states the
/// divisibility by the value `minFac` actually computes.
#[test]
fn min_fac_dvd_instantiates_at_twelve_and_fifteen() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let twelve = f.num(12);
    let fifteen = f.num(15);

    // `2 ≤ 12` — `Nat.le` at literals closes by `le_refl` plus `le_step`s, so
    // build it from the prelude's own `le_of_ble_eq_true` bridge instead.
    let ble_true = {
        let cond = f.ble(two, twelve);
        f.bool_refl(cond)
    };
    let h12 = f.const_app(p.le_of_ble_eq_true, &[two, twelve, ble_true]);
    let applied = f.const_app(p.min_fac_dvd, &[twelve, h12]);
    let ty = f.k.infer(applied).expect("min_fac_dvd must apply at 12");
    let expected = f.dvd(two, twelve);
    assert!(
        f.k.def_eq(ty, expected),
        "min_fac_dvd 12 must state `2 ∣ 12`, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.dvd(three, twelve);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: min_fac_dvd 12 must NOT state `3 ∣ 12` -- 3 divides \
         12 but is not its LEAST factor"
    );

    let ble_true_15 = {
        let cond = f.ble(two, fifteen);
        f.bool_refl(cond)
    };
    let h15 = f.const_app(p.le_of_ble_eq_true, &[two, fifteen, ble_true_15]);
    let applied15 = f.const_app(p.min_fac_dvd, &[fifteen, h15]);
    let ty15 = f.k.infer(applied15).expect("min_fac_dvd must apply at 15");
    let expected15 = f.dvd(three, fifteen);
    assert!(
        f.k.def_eq(ty15, expected15),
        "min_fac_dvd 15 must state `3 ∣ 15` -- the search must skip the failed \
         candidate 2, got {}",
        f.k.render_lean(ty15)
    );
    let wrong15 = f.dvd(two, fifteen);
    assert!(
        !f.k.def_eq(ty15, wrong15),
        "negative control: min_fac_dvd 15 must NOT state `2 ∣ 15`"
    );
}

/// `Nat.min_fac_prime` INSTANTIATES, and its conclusion is primality of the
/// computed least factor.
///
/// The conclusion is an `And`, so the check compares against a hand-built
/// `prime_condition 3` and against the same shape at `5` -- which is prime, so
/// the negative control is testing that the theorem is about `minFac 15` and
/// not about "some prime".
#[test]
fn min_fac_prime_instantiates_at_fifteen() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let fifteen = f.num(15);

    let ble_true = {
        let cond = f.ble(two, fifteen);
        f.bool_refl(cond)
    };
    let h = f.const_app(p.le_of_ble_eq_true, &[two, fifteen, ble_true]);
    let applied = f.const_app(p.min_fac_prime, &[fifteen, h]);
    let ty = f.k.infer(applied).expect("min_fac_prime must apply at 15");

    let prime_at = |f: &mut Fixture, x: u32| {
        let nat = f.nat_ty();
        let lit = f.num(x);
        let two = f.num(2);
        let lower = f.le(two, lit);
        let c_fv = f.fresh_fvar();
        let c = f.k.fvar(c_fv);
        let divides = f.dvd(c, lit);
        let one = f.num(1);
        let trivial = f.eq(c, one);
        let whole = f.eq(c, lit);
        let or_name = f.p.logic.or;
        let disjunction = f.const_app(or_name, &[trivial, whole]);
        let body = f.arrow(divides, disjunction);
        let divisors = f.pi_fv(c_fv, nat, body);
        let and_name = f.p.logic.and;
        f.const_app(and_name, &[lower, divisors])
    };

    let expected = prime_at(&mut f, 3);
    assert!(
        f.k.def_eq(ty, expected),
        "min_fac_prime 15 must conclude primality of 3, got {}",
        f.k.render_lean(ty)
    );
    let wrong = prime_at(&mut f, 5);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT conclude primality of 5 -- 5 is prime and \
         divides 15, so this separates `minFac` from `some prime factor`"
    );
    let _ = five;
    let _ = three;
}
