//! Concrete-instance tests for `nat_prelude::abundant_deficient`.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) for the merge hazard `avg_pair_tests.rs` records:
//! two lanes editing that one file at once have repeatedly produced a
//! conflict git cuts mid-item. `Fixture` here is a small local copy of
//! `nat_prelude_tests::Fixture` (that one is module-private).
//!
//! The kernel cannot tell a `Definition` is wrong — `Nat → Prop` is
//! `Nat → Prop` whatever proposition the body denotes, so `add_declaration`
//! accepts a reversed inequality or a missing factor of two as happily as the
//! intended predicate. Both definitions here are recursion-free, so the two
//! failure modes this kernel usually produces (a stuck recursor, a wrong
//! argument order) cannot occur; what CAN occur is a reversed `Lt` or a wrong
//! multiple of `n`. Every check below is a `def_eq` at concrete numerals
//! against an independently hand-computed value, paired with a negative
//! control naming the specific wrong formula it rules out.

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

/// The divisor sums both predicates are stated against, computed by the
/// kernel and compared to hand arithmetic. Everything below rests on these
/// three numbers, so they are checked first and separately: if
/// `sumDivisors 12` were not `28`, the discriminators further down would be
/// comparing the right definition against the wrong constant and would still
/// pass.
///
/// `sumDivisors 12 = 1+2+3+4+6+12 = 28`, `sumDivisors 8 = 1+2+4+8 = 15`,
/// `sumDivisors 6 = 1+2+3+6 = 12`. (`d = 0` contributes `0` on either branch
/// by construction — see `perfect.rs`'s module doc — so the `[0,n]` range and
/// the classical `[1,n]` one agree.)
#[test]
fn sum_divisors_evaluates_at_the_three_witnesses() {
    let mut f = Fixture::new();
    let p = f.p;

    for (n, expected) in [(12u32, 28u32), (8, 15), (6, 12)] {
        let arg = f.num(n);
        let sum = f.const_app(p.sum_divisors, &[arg]);
        let want = f.num(expected);
        assert!(
            f.k.def_eq(sum, want),
            "sumDivisors {n} must reduce to {expected}"
        );
        let off_by_one = f.num(expected - 1);
        assert!(
            !f.k.def_eq(sum, off_by_one),
            "negative control: sumDivisors {n} must NOT reduce to {}",
            expected - 1
        );
    }
}

/// `Nat.Abundant 12` must unfold to `Lt 24 28` — the TRUE direction, at
/// TWICE `n`.
///
/// The two negative controls are the two wrong definitions that type-check:
/// `Lt 28 24` is the reversed inequality (which is `Nat.Deficient`'s body,
/// i.e. exactly what a copy-paste between the two declarations produces), and
/// `Lt 12 28` is the missing factor of two (`n < sumDivisors n` — the shape a
/// reader gets by transcribing Mathlib's proper-divisor phrasing without
/// noticing that `sumDivisors` counts `n` itself).
#[test]
fn abundant_evaluates_at_twelve() {
    let mut f = Fixture::new();
    let p = f.p;

    let twelve = f.num(12);
    let abundant_12 = f.const_app(p.abundant, &[twelve]);

    let n24 = f.num(24);
    let n28 = f.num(28);
    let want = f.lt(n24, n28);
    assert!(
        f.k.def_eq(abundant_12, want),
        "Abundant 12 must unfold to Lt 24 28 (2*12 < sumDivisors 12 = 28)"
    );

    let reversed = f.lt(n28, n24);
    assert!(
        !f.k.def_eq(abundant_12, reversed),
        "negative control: Abundant 12 must NOT be Lt 28 24 (that is Deficient's body)"
    );

    let without_the_two = f.lt(twelve, n28);
    assert!(
        !f.k.def_eq(abundant_12, without_the_two),
        "negative control: Abundant 12 must NOT be Lt 12 28 (missing the factor of two)"
    );
}

/// `Nat.Deficient 8` must unfold to `Lt 15 16` — `sumDivisors 8 = 15` on the
/// LEFT, `2 * 8 = 16` on the right.
///
/// `8` rather than `12` is deliberate: it is deficient where `12` is
/// abundant, so a single definition copied to both names cannot satisfy this
/// test and `abundant_evaluates_at_twelve` at once. The reversed control
/// `Lt 16 15` is `Nat.Abundant`'s body at the same argument.
#[test]
fn deficient_evaluates_at_eight() {
    let mut f = Fixture::new();
    let p = f.p;

    let eight = f.num(8);
    let deficient_8 = f.const_app(p.deficient, &[eight]);

    let n15 = f.num(15);
    let n16 = f.num(16);
    let want = f.lt(n15, n16);
    assert!(
        f.k.def_eq(deficient_8, want),
        "Deficient 8 must unfold to Lt 15 16 (sumDivisors 8 = 15 < 2*8 = 16)"
    );

    let reversed = f.lt(n16, n15);
    assert!(
        !f.k.def_eq(deficient_8, reversed),
        "negative control: Deficient 8 must NOT be Lt 16 15 (that is Abundant's body)"
    );

    let without_the_two = f.lt(n15, eight);
    assert!(
        !f.k.def_eq(deficient_8, without_the_two),
        "negative control: Deficient 8 must NOT be Lt 15 8 (missing the factor of two)"
    );
}

/// The two predicates are DIFFERENT propositions at an argument where they
/// disagree, and they agree with `Nat.Perfect`'s own convention.
///
/// `12` is abundant and not deficient; `8` is deficient and not abundant. A
/// declaration that bound both names to one body would pass neither of the
/// first two `assert`s here. And at the perfect number `6` both bodies are
/// `Lt 12 12` — a real property of the definitions worth pinning (it is what
/// makes the module's trichotomy rows true), and precisely why `6` is NOT
/// used as a discriminator above: at `6` the two predicates ARE def-eq.
#[test]
fn abundant_and_deficient_are_distinct_and_meet_at_perfect() {
    let mut f = Fixture::new();
    let p = f.p;

    let twelve = f.num(12);
    let abundant_12 = f.const_app(p.abundant, &[twelve]);
    let deficient_12 = f.const_app(p.deficient, &[twelve]);
    assert!(
        !f.k.def_eq(abundant_12, deficient_12),
        "Abundant 12 and Deficient 12 must be different propositions"
    );

    let eight = f.num(8);
    let abundant_8 = f.const_app(p.abundant, &[eight]);
    let deficient_8 = f.const_app(p.deficient, &[eight]);
    assert!(
        !f.k.def_eq(abundant_8, deficient_8),
        "Abundant 8 and Deficient 8 must be different propositions"
    );

    let six = f.num(6);
    let abundant_6 = f.const_app(p.abundant, &[six]);
    let deficient_6 = f.const_app(p.deficient, &[six]);
    let n12 = f.num(12);
    let n12b = f.num(12);
    let both = f.lt(n12, n12b);
    assert!(
        f.k.def_eq(abundant_6, both),
        "Abundant 6 must unfold to Lt 12 12 (6 is perfect, so neither strict side holds)"
    );
    assert!(
        f.k.def_eq(deficient_6, both),
        "Deficient 6 must unfold to Lt 12 12"
    );
}

/// `Abundant 0` and `Deficient 0` are both `Lt 0 0`, matching Mathlib's own
/// `Nat.not_abundant_zero`: `properDivisors 0` is empty there, and
/// `sumDivisors 0` is `0` here (the `d = 0` term contributes `0` and the
/// range `[0,0]` has no other point), so `2 * 0 = 0` on both sides.
///
/// This is the boundary the truncating `Nat.sub` phrasing would have got
/// wrong, which is why `perfect.rs` avoids subtraction and this module
/// follows it.
#[test]
fn both_predicates_are_false_at_zero() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let sum_0 = f.const_app(p.sum_divisors, &[zero]);
    let zero2 = f.zero();
    assert!(f.k.def_eq(sum_0, zero2), "sumDivisors 0 must reduce to 0");

    let abundant_0 = f.const_app(p.abundant, &[zero]);
    let a = f.zero();
    let b = f.zero();
    let lt_0_0 = f.lt(a, b);
    assert!(
        f.k.def_eq(abundant_0, lt_0_0),
        "Abundant 0 must unfold to Lt 0 0"
    );

    let deficient_0 = f.const_app(p.deficient, &[zero]);
    assert!(
        f.k.def_eq(deficient_0, lt_0_0),
        "Deficient 0 must unfold to Lt 0 0"
    );

    let one = f.num(1);
    let zero3 = f.zero();
    let lt_0_1 = f.lt(zero3, one);
    assert!(
        !f.k.def_eq(abundant_0, lt_0_1),
        "negative control: Abundant 0 must NOT be Lt 0 1"
    );
}
