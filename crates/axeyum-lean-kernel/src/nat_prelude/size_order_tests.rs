//! Concrete-instance tests for `nat_prelude::size_order`'s two `ml430`
//! mirrors, `size_bit` and `size_le_size`. Separate file for the same
//! merge-hazard reason as `bit_extra_tests.rs`/`size_extra_tests.rs`;
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
fn size_le_size_applies_at_a_concrete_pair_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // 3 <= 6, size 3 = 2 (binary 11), size 6 = 3 (binary 110).
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let le_3_4 = f.lemma(p.le_succ, &[three]);
    let le_4_5 = f.lemma(p.le_succ, &[four]);
    let le_5_6 = f.lemma(p.le_succ, &[five]);
    let le_3_5 = f.lemma(p.le_trans, &[three, four, five, le_3_4, le_4_5]);
    let le_3_6 = f.lemma(p.le_trans, &[three, five, six, le_3_5, le_5_6]);

    let applied = f.const_app(p.size_le_size, &[three, six, le_3_6]);
    let inferred = f
        .k
        .infer(applied)
        .unwrap_or_else(|e| panic!("size_le_size must type-check at (3, 6): {}", f.explain(&e)));
    let size3 = f.const_app(p.size, &[three]);
    let size6 = f.const_app(p.size, &[six]);
    let want = f.le(size3, size6);
    assert!(
        f.k.def_eq(inferred, want),
        "size_le_size at (3, 6) must state Le (size 3) (size 6)"
    );
    // The two sizes must actually differ (2 vs 3), not merely both be
    // vacuously equal, or a swapped-direction bug would pass unnoticed.
    let size3_val = f.num(2);
    let size6_val = f.num(3);
    assert!(
        f.k.def_eq(size3, size3_val),
        "size 3 must compute to 2"
    );
    assert!(
        f.k.def_eq(size6, size6_val),
        "size 6 must compute to 3"
    );

    // Negative control: the reversed inequality is a different statement
    // (and false here, since size 6 = 3 > 2 = size 3).
    let reversed = f.le(size6, size3);
    assert!(
        !f.k.def_eq(inferred, reversed),
        "negative control: size_le_size must not also state Le (size 6) (size 3)"
    );

    assert!(
        f.k.axiom_footprint(p.size_le_size).is_empty(),
        "size_le_size must rest on zero axioms"
    );

    // Symbolic instance: the theorem must also type-check as a bare
    // universally-quantified statement (no concrete numerals at all),
    // matching the fact ledger's formal.statement over free m, n.
    let bare_const = f.k.const_(p.size_le_size, vec![]);
    let bare = f.k.infer(bare_const).unwrap_or_else(|e| {
        panic!(
            "size_le_size must type-check with no arguments applied: {}",
            f.explain(&e)
        )
    });
    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let hyp = f.le(m, n);
    let size_m = f.const_app(p.size, &[m]);
    let size_n = f.const_app(p.size, &[n]);
    let concl = f.le(size_m, size_n);
    let inner = f.arrow(hyp, concl);
    let nat = f.nat_ty();
    let want_bare = {
        let over_n = f.pi_fv(n_fv, nat, inner);
        f.pi_fv(m_fv, nat, over_n)
    };
    assert!(
        f.k.def_eq(bare, want_bare),
        "size_le_size must state Pi m n, Le m n -> Le (size m) (size n)"
    );
}

#[test]
fn size_bit_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let bit = p.bit;
    let true_ = f.bool_true();
    let two = f.num(2);

    // bit true 2 = 2*2 + 1 = 5, which reduces to a literal numeral, so
    // `Ne (bit true 2) 0` is exactly `Ne 5 0` up to defeq.
    let one = f.num(1);
    let ne_2_0 = f.lemma(p.succ_ne_zero, &[one]); // Ne (succ 1) 0 = Ne 2 0
    let ne_bit_0 = f.lemma(p.bit_ne_zero, &[true_, two, ne_2_0]); // Ne (bit true 2) 0

    let applied = f.const_app(p.size_bit, &[true_, two, ne_bit_0]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "size_bit must type-check at (true, 2): {}",
            f.explain(&e)
        )
    });

    let bit_val = f.const_app(bit, &[true_, two]);
    let size_bit_val = f.const_app(p.size, &[bit_val]);
    let size_two = f.const_app(p.size, &[two]);
    let succ_size_two = f.succ(size_two);
    let want = f.eq(size_bit_val, succ_size_two);
    assert!(
        f.k.def_eq(inferred, want),
        "size_bit at (true, 2) must state Eq (size (bit true 2)) (succ (size 2))"
    );

    // Both sides compute to a concrete numeral: size (bit true 2) = size 5 =
    // 3, and succ (size 2) = succ 2 = 3 -- a real, non-vacuous instance.
    let five = f.num(5);
    assert!(
        f.k.def_eq(bit_val, five),
        "bit true 2 must compute to 5"
    );
    let three = f.num(3);
    assert!(
        f.k.def_eq(size_bit_val, three),
        "size (bit true 2) must compute to 3"
    );
    assert!(
        f.k.def_eq(succ_size_two, three),
        "succ (size 2) must compute to 3"
    );

    // Negative control: `size (bit true 2)` must NOT equal `size 2` itself
    // (the "no increment" bug this theorem rules out -- 3 != 2).
    let no_increment = f.eq(size_bit_val, size_two);
    assert!(
        !f.k.def_eq(inferred, no_increment),
        "negative control: size_bit must not also state Eq (size (bit true 2)) (size 2)"
    );

    assert!(
        f.k.axiom_footprint(p.size_bit).is_empty(),
        "size_bit must rest on zero axioms"
    );
}
