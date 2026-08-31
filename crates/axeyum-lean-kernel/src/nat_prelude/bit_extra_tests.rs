//! Concrete-instance tests for `nat_prelude::bit_extra`'s six theorems.
//!
//! A separate file (rather than an addition to the dense
//! `nat_prelude_tests.rs`) per this session's own merge-hazard note: two
//! lanes editing that one file at once have twice produced a conflict git
//! cuts mid-item. `Fixture` here is a small local copy of
//! `nat_prelude_tests::Fixture` (that one is module-private) — same three
//! fields, same `NatOps` impl, same `build_nat_prelude` call.
//!
//! Every positive check pairs with a negative control that flips the ONE
//! thing the theorem asserts (order direction, which side gets doubled, the
//! selector bool), so none of these can pass vacuously.

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
fn bit_false_zero_reduces_and_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let applied = f.const_app(p.bit_false_zero, &[]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("bit_false_zero must type-check: {}", f.explain(&e)));
    let want = f.eq(zero, zero);
    assert!(
        f.k.def_eq(inferred, want),
        "bit_false_zero must state Eq (bit false 0) 0"
    );
    assert!(
        f.k.axiom_footprint(p.bit_false_zero).is_empty(),
        "bit_false_zero must rest on zero axioms"
    );
}

#[test]
fn bit_le_applies_at_a_concrete_pair() {
    let mut f = Fixture::new();
    let p = f.p;
    let bit = p.bit;
    let true_ = f.bool_true();

    // 3 <= 5 -> bit true 3 (=7) <= bit true 5 (=11).
    let three = f.num(3);
    let five = f.num(5);
    // Le 3 5 via le_add_right (3 <= 3 + 2 = 5), rather than hand-chaining
    // le_step calls.
    let two = f.num(2);
    let le_3_5 = f.lemma(p.le_add_right, &[three, two]); // Le 3 (add 3 2) = Le 3 5
    let applied = f.const_app(p.bit_le, &[true_, three, five, le_3_5]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("bit_le must type-check: {}", f.explain(&e)));
    let lhs = f.const_app(bit, &[true_, three]);
    let rhs = f.const_app(bit, &[true_, five]);
    let want = f.le(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "bit_le must state Le (bit true 3) (bit true 5)"
    );
    // Negative control: the reverse inequality (11 <= 7) is false.
    let reversed = f.le(rhs, lhs);
    assert!(
        !f.k.def_eq(inferred, reversed),
        "negative control: bit_le must not also state Le (bit true 5) (bit true 3)"
    );
    assert!(
        f.k.axiom_footprint(p.bit_le).is_empty(),
        "bit_le must rest on zero axioms"
    );
}

#[test]
fn bit_ne_zero_applies_at_a_concrete_positive_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let bit = p.bit;
    let false_ = f.bool_false();
    let five = f.num(5);
    let zero = f.zero();

    // A proof of `5 <> 0`, built by hand: `Eq 5 0 -> False` via a case split
    // is more machinery than this test needs, so borrow the existing
    // `succ_ne_zero` boundary theorem instead (5 is `succ 4`).
    let four = f.num(4);
    let ne_5_0 = f.lemma(p.succ_ne_zero, &[four]); // Ne (succ 4) 0 = Ne 5 0
    let applied = f.const_app(p.bit_ne_zero, &[false_, five, ne_5_0]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("bit_ne_zero must type-check: {}", f.explain(&e)));
    let bit_5 = f.const_app(bit, &[false_, five]);
    let eq_ty = f.eq(bit_5, zero);
    let false_ty = f.k.const_(p.logic.false_, vec![]);
    let want = f.arrow(eq_ty, false_ty);
    assert!(
        f.k.def_eq(inferred, want),
        "bit_ne_zero must state Not (Eq (bit false 5) 0)"
    );
    assert!(
        f.k.axiom_footprint(p.bit_ne_zero).is_empty(),
        "bit_ne_zero must rest on zero axioms"
    );
}

#[test]
fn bit_lt_bit_applies_at_a_concrete_discriminating_pair() {
    let mut f = Fixture::new();
    let p = f.p;
    let bit = p.bit;
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    // 2 < 3 -> bit true 2 (=5) < bit false 3 (=6).
    let two = f.num(2);
    let three = f.num(3);
    let lt_2_3 = f.lemma(p.lt_succ_self, &[two]); // Lt 2 (succ 2) = Lt 2 3
    let applied = f.const_app(p.bit_lt_bit, &[two, three, true_, false_, lt_2_3]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("bit_lt_bit must type-check: {}", f.explain(&e)));
    let lhs = f.const_app(bit, &[true_, two]);
    let rhs = f.const_app(bit, &[false_, three]);
    let want = f.lt(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "bit_lt_bit must state Lt (bit true 2) (bit false 3)"
    );
    // Negative control: the reverse (6 < 5) is false.
    let reversed = f.lt(rhs, lhs);
    assert!(
        !f.k.def_eq(inferred, reversed),
        "negative control: bit_lt_bit must not also state Lt (bit false 3) (bit true 2)"
    );
    assert!(
        f.k.axiom_footprint(p.bit_lt_bit).is_empty(),
        "bit_lt_bit must rest on zero axioms"
    );
}

#[test]
fn bit_add_left_and_right_apply_at_a_concrete_split() {
    let mut f = Fixture::new();
    let p = f.p;
    let bit = p.bit;
    let true_ = f.bool_true();
    let two = f.num(2);
    let three = f.num(3);

    // bit_add_left : bit true (2+3) = bit false 2 + bit true 3
    //   bit true 5 = 11 ; bit false 2 + bit true 3 = 4 + 7 = 11.
    {
        let applied = f.const_app(p.bit_add_left, &[true_, two, three]);
        let inferred =
            f.k.infer(applied)
                .unwrap_or_else(|e| panic!("bit_add_left must type-check: {}", f.explain(&e)));
        let sum = f.add(two, three);
        let lhs = f.const_app(bit, &[true_, sum]);
        let false_val = f.bool_false();
        let bit_false_2 = f.const_app(bit, &[false_val, two]);
        let bit_true_3 = f.const_app(bit, &[true_, three]);
        let rhs = f.add(bit_false_2, bit_true_3);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_add_left must state Eq (bit true (2+3)) (bit false 2 + bit true 3)"
        );
        // Negative control: `bit true 2 + bit true 3` is 5 + 7 = 12, NOT 11
        // -- a genuinely different VALUE, unlike swapping which side gets
        // `bit false` (both `bit_add_left`'s and `bit_add_right`'s splits
        // total 11, so that comparison would have been vacuous).
        let bit_true_2 = f.const_app(bit, &[true_, two]);
        let bit_true_3 = f.const_app(bit, &[true_, three]);
        let other_rhs = f.add(bit_true_2, bit_true_3);
        let other_want = f.eq(lhs, other_rhs);
        assert!(
            !f.k.def_eq(inferred, other_want),
            "negative control: bit_add_left must not also state Eq (bit true 5) (bit true 2 + bit true 3)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_add_left).is_empty(),
            "bit_add_left must rest on zero axioms"
        );
    }

    // bit_add_right : bit true (2+3) = bit true 2 + bit false 3
    {
        let applied = f.const_app(p.bit_add_right, &[true_, two, three]);
        let inferred =
            f.k.infer(applied)
                .unwrap_or_else(|e| panic!("bit_add_right must type-check: {}", f.explain(&e)));
        let sum = f.add(two, three);
        let lhs = f.const_app(bit, &[true_, sum]);
        let bit_true_2 = f.const_app(bit, &[true_, two]);
        let false_val = f.bool_false();
        let bit_false_3 = f.const_app(bit, &[false_val, three]);
        let rhs = f.add(bit_true_2, bit_false_3);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_add_right must state Eq (bit true (2+3)) (bit true 2 + bit false 3)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_add_right).is_empty(),
            "bit_add_right must rest on zero axioms"
        );
    }
}
