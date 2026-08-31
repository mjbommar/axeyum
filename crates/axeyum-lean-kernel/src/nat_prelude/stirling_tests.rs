//! Concrete-instance tests for `nat_prelude::stirling`'s two definitions.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) for the merge hazard `avg_pair_tests.rs` records.
//! `Fixture` here is a small local copy of `nat_prelude_tests::Fixture` (that
//! one is module-private).
//!
//! The kernel cannot tell a `Definition` is wrong: `Nat → Nat → Nat` is that
//! type whatever triangle the body computes, and the three ways to get this
//! one wrong (a `1` where the `succ` row's column zero must be `0`, the other
//! kind's coefficient, the coefficient on the wrong recursive call) all
//! type-check. Every value below is computed by hand from the recurrence and
//! checked against the kernel's own reduction, with a negative control naming
//! the specific wrong triangle it rules out.
//!
//! Hand computation, from `c(n+1,k+1) = n*c(n,k+1) + c(n,k)` (first kind) and
//! `S(n+1,k+1) = (k+1)*S(n,k+1) + S(n,k)` (second kind), both with
//! `c(0,0) = S(0,0) = 1` and zeros elsewhere on the boundary:
//!
//! ```text
//!   c: c(1,1)=1  c(2,1)=1  c(2,2)=1  c(3,1)=2  c(3,2)=3  c(3,3)=1
//!      c(4,1)=6  c(4,2)=11 c(4,3)=6  c(4,4)=1
//!   S: S(1,1)=1  S(2,1)=1  S(2,2)=1  S(3,1)=1  S(3,2)=3  S(3,3)=1
//!      S(4,1)=1  S(4,2)=7  S(4,3)=6  S(4,4)=1
//! ```
//!
//! Every magnitude formed here is at most `11`, deliberately: this prelude's
//! numerals are unary, so a check at a large argument would cost more than
//! the whole prelude build.

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

/// Both boundaries, which are where the two definitions differ from
/// `Nat.choose` — the `succ` row's column zero is `0`, not `1`.
///
/// `c(0,0) = S(0,0) = 1`; `c(0,k+1) = S(0,k+1) = 0`; and the one a
/// copy-of-`choose` gets wrong, `c(n+1,0) = S(n+1,0) = 0` where
/// `choose (n+1) 0 = 1`.
#[test]
fn both_triangles_have_the_right_boundary() {
    let mut f = Fixture::new();
    let p = f.p;

    for name in [p.stirling_first, p.stirling_second] {
        let zero = f.zero();
        let zero2 = f.zero();
        let at_0_0 = f.const_app(name, &[zero, zero2]);
        let one = f.num(1);
        assert!(f.k.def_eq(at_0_0, one), "stirling _ 0 0 must be 1");

        let z = f.zero();
        let one_col = f.num(1);
        let at_0_1 = f.const_app(name, &[z, one_col]);
        let zero3 = f.zero();
        assert!(f.k.def_eq(at_0_1, zero3), "stirling _ 0 1 must be 0");

        let one_row = f.num(1);
        let z2 = f.zero();
        let at_1_0 = f.const_app(name, &[one_row, z2]);
        let zero4 = f.zero();
        assert!(
            f.k.def_eq(at_1_0, zero4),
            "stirling _ 1 0 must be 0 -- this is where the triangle differs \
             from Nat.choose, whose (n+1) 0 is 1"
        );
        let one2 = f.num(1);
        assert!(
            !f.k.def_eq(at_1_0, one2),
            "negative control: stirling _ 1 0 must NOT be 1 (that is Nat.choose's \
             succ row, i.e. the body copied without changing its base case)"
        );

        let three = f.num(3);
        let z3 = f.zero();
        let at_3_0 = f.const_app(name, &[three, z3]);
        let zero5 = f.zero();
        assert!(f.k.def_eq(at_3_0, zero5), "stirling _ 3 0 must be 0");
    }
}

/// Unsigned Stirling numbers of the FIRST kind, at the instances that
/// separate them from the second kind and from `Nat.choose`.
///
/// `c(4,2) = 11` is the load-bearing one: the second kind is `7` there and
/// `choose 4 2` is `6`, so this single instance rules out both wrong bodies.
/// `c(3,1) = 2` and `c(4,1) = 6` are `2!` and `3!`, the row Mathlib's own
/// `stirlingFirst_one_right` describes, and separate the first kind from the
/// second (whose column 1 is all ones).
#[test]
fn stirling_first_evaluates() {
    let mut f = Fixture::new();
    let p = f.p;

    for (n, k, expected) in [
        (1u32, 1u32, 1u32),
        (2, 1, 1),
        (2, 2, 1),
        (3, 1, 2),
        (3, 2, 3),
        (3, 3, 1),
        (4, 1, 6),
        (4, 2, 11),
        (4, 3, 6),
    ] {
        let row = f.num(n);
        let col = f.num(k);
        let got = f.const_app(p.stirling_first, &[row, col]);
        let want = f.num(expected);
        assert!(
            f.k.def_eq(got, want),
            "stirlingFirst {n} {k} must reduce to {expected}"
        );
    }

    // The three discriminating negative controls, all at (4,2).
    let four = f.num(4);
    let two = f.num(2);
    let at_4_2 = f.const_app(p.stirling_first, &[four, two]);
    for (wrong, why) in [
        (
            7u32,
            "that is stirlingSecond 4 2 -- the second kind's coefficient",
        ),
        (6, "that is choose 4 2 -- no coefficient at all"),
        (
            0,
            "that is what n * c(n,k) + c(n,k+1) gives -- the coefficient on the \
             wrong recursive call, which collapses row 1 to all zeros and so \
             makes every later entry zero (the (1,1) case above catches it too, \
             independently)",
        ),
    ] {
        let bad = f.num(wrong);
        assert!(
            !f.k.def_eq(at_4_2, bad),
            "negative control: stirlingFirst 4 2 must NOT be {wrong} ({why})"
        );
    }
}

/// Stirling numbers of the SECOND kind. Column 1 is all ones (a set has one
/// partition into a single block), which is exactly where the first kind's
/// factorials distinguish it.
///
/// `S(4,2) = 7` against the first kind's `11` at the same argument is the
/// instance that makes a single body bound to both names impossible.
#[test]
fn stirling_second_evaluates() {
    let mut f = Fixture::new();
    let p = f.p;

    for (n, k, expected) in [
        (1u32, 1u32, 1u32),
        (2, 1, 1),
        (2, 2, 1),
        (3, 1, 1),
        (3, 2, 3),
        (3, 3, 1),
        (4, 1, 1),
        (4, 2, 7),
        (4, 3, 6),
    ] {
        let row = f.num(n);
        let col = f.num(k);
        let got = f.const_app(p.stirling_second, &[row, col]);
        let want = f.num(expected);
        assert!(
            f.k.def_eq(got, want),
            "stirlingSecond {n} {k} must reduce to {expected}"
        );
    }

    let four = f.num(4);
    let two = f.num(2);
    let at_4_2 = f.const_app(p.stirling_second, &[four, two]);
    let eleven = f.num(11);
    assert!(
        !f.k.def_eq(at_4_2, eleven),
        "negative control: stirlingSecond 4 2 must NOT be 11 (that is the FIRST kind)"
    );
    let six = f.num(6);
    assert!(
        !f.k.def_eq(at_4_2, six),
        "negative control: stirlingSecond 4 2 must NOT be 6 (that is choose 4 2)"
    );

    // Column 1 is the sharpest separator of the two kinds: all ones here,
    // factorials there. Checked as a DIFFERENCE so a single shared body fails.
    let three = f.num(3);
    let one = f.num(1);
    let second_3_1 = f.const_app(p.stirling_second, &[three, one]);
    let three2 = f.num(3);
    let one2 = f.num(1);
    let first_3_1 = f.const_app(p.stirling_first, &[three2, one2]);
    assert!(
        !f.k.def_eq(second_3_1, first_3_1),
        "stirlingSecond 3 1 (= 1) and stirlingFirst 3 1 (= 2) must differ"
    );
}
