//! Concrete-instance tests for `nat_prelude::size_extra`'s two theorems.
//! Separate file for the same merge-hazard reason as `bit_extra_tests.rs`;
//! `Fixture` here is the identical small local copy.

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

#[test]
fn size_one_reduces_and_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let applied = f.const_app(p.size_one, &[]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("size_one must type-check: {}", f.explain(&e)));
    let want = f.eq(one, one);
    assert!(
        f.k.def_eq(inferred, want),
        "size_one must state Eq (size 1) 1"
    );
    assert!(
        f.k.axiom_footprint(p.size_one).is_empty(),
        "size_one must rest on zero axioms"
    );
}

#[test]
fn size_eq_zero_applies_at_zero_and_at_a_positive_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();

    // The Iff itself, at a concrete n, must type-check and state exactly
    // `Iff (Eq (size n) 0) (Eq n 0)`.
    let five = f.num(5);
    let applied = f.const_app(p.size_eq_zero, &[five]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("size_eq_zero must type-check: {}", f.explain(&e)));
    let sz5 = f.const_app(p.size, &[five]);
    let lhs_ty = f.eq(sz5, zero);
    let rhs_ty = f.eq(five, zero);
    let want = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    assert!(
        f.k.def_eq(inferred, want),
        "size_eq_zero must state Iff (Eq (size 5) 0) (Eq 5 0)"
    );
    // Negative control: swapping which side is 0-tested is a different
    // (false at n=5, since size 5 = 3 != 0 while genuinely checking a
    // different pair) statement.
    let reversed = f.const_app(p.logic.iff, &[rhs_ty, lhs_ty]);
    assert!(
        !f.k.def_eq(inferred, reversed),
        "negative control: size_eq_zero must not also state Iff (Eq 5 0) (Eq (size 5) 0)"
    );
    assert!(
        f.k.axiom_footprint(p.size_eq_zero).is_empty(),
        "size_eq_zero must rest on zero axioms"
    );

    // Use the mpr direction concretely at n = 0: from `Eq 0 0` (refl) derive
    // `Eq (size 0) 0`, and check the produced proof really type-checks at
    // that instance (exercising the `reverse` branch, not just the `Iff`
    // shell).
    let iff_at_zero = f.const_app(p.size_eq_zero, &[zero]);
    let sz0 = f.const_app(p.size, &[zero]);
    let lhs0_ty = f.eq(sz0, zero);
    let rhs0_ty = f.eq(zero, zero);
    let mpr = f.const_app(p.logic.iff_mpr, &[lhs0_ty, rhs0_ty, iff_at_zero]);
    let refl0 = f.refl(zero);
    let derived = f.apply(mpr, &[refl0]);
    let derived_ty =
        f.k.infer(derived)
            .unwrap_or_else(|e| panic!("size_eq_zero mpr at 0 must type-check: {}", f.explain(&e)));
    assert!(
        f.k.def_eq(derived_ty, lhs0_ty),
        "size_eq_zero's mpr branch at n=0 must derive Eq (size 0) 0"
    );
}
