//! Concrete-instance test for
//! `nat_prelude::add_choose_div::declare_add_choose`. Separate file for
//! the same merge-hazard reason as `bit_extra_tests.rs`/
//! `choose_factorial_add_tests.rs`.

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
fn add_choose_computes_at_i2_j3() {
    // i=2, j=3: (2+3).choose 3 = 5.choose 3 = 10 ; 2! = 2 ; 3! = 6 ;
    // 5! = 120 ; 120 / (2*6) = 120 / 12 = 10.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let applied = f.const_app(p.add_choose, &[two, three]);
    let inferred = f
        .k
        .infer(applied)
        .unwrap_or_else(|e| panic!("add_choose must type-check: {}", f.explain(&e)));

    let five = f.num(5);
    let ten = f.num(10);
    let sum = f.add(two, three);
    let choose_5_3 = f.const_app(p.choose, &[sum, three]);
    let fact_2 = f.const_app(p.factorial, &[two]);
    let fact_3 = f.const_app(p.factorial, &[three]);
    let fact_5 = f.const_app(p.factorial, &[five]);
    let denom = f.mul(fact_2, fact_3);
    let div_term = f.div(fact_5, denom);
    let want = f.eq(choose_5_3, div_term);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Eq (5.choose 3) (5! / (2! * 3!))"
    );

    // Sanity: every subterm reduces to the concrete numeral it should,
    // confirming this isn't a vacuous defeq between two stuck terms.
    let twelve = f.num(12);
    let hundred_twenty = f.num(120);
    assert!(f.k.def_eq(fact_5, hundred_twenty), "5! must reduce to 120");
    assert!(f.k.def_eq(denom, twelve), "2! * 3! must reduce to 12");
    assert!(f.k.def_eq(choose_5_3, ten), "choose 5 3 must reduce to 10");
    assert!(f.k.def_eq(div_term, ten), "120 / 12 must reduce to 10");

    // Negative control: 5.choose 1 = 5, discriminating from 5.choose 3 = 10.
    let one = f.num(1);
    let choose_5_1 = f.const_app(p.choose, &[sum, one]);
    let wrong_want = f.eq(choose_5_1, div_term);
    assert!(
        !f.k.def_eq(inferred, wrong_want),
        "negative control: must not also state Eq (5.choose 1) (5! / (2! * 3!))"
    );

    assert!(
        f.k.axiom_footprint(p.add_choose).is_empty(),
        "add_choose must rest on zero axioms"
    );
}
