//! Concrete-instance test for
//! `nat_prelude::choose_factorial_add::declare_add_choose_mul_factorial_mul_factorial`.
//! Separate file for the same merge-hazard reason as `bit_extra_tests.rs`.

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
fn add_choose_mul_factorial_mul_factorial_computes_at_i2_j3() {
    // i=2, j=3: (2+3).choose 3 = 5.choose 3 = 10 ; 2! = 2 ; 3! = 6 ;
    // 10 * 2 * 6 = 120 = 5!.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let applied = f.const_app(p.add_choose_mul_factorial_mul_factorial, &[two, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_choose_mul_factorial_mul_factorial must type-check: {}",
            f.explain(&e)
        )
    });

    let five = f.num(5);
    let ten = f.num(10);
    let sum = f.add(two, three);
    let choose_5_3 = f.const_app(p.choose, &[sum, three]);
    let fact_2 = f.const_app(p.factorial, &[two]);
    let fact_3 = f.const_app(p.factorial, &[three]);
    let choose_fact2 = f.mul(choose_5_3, fact_2);
    let lhs = f.mul(choose_fact2, fact_3);
    let fact_5 = f.const_app(p.factorial, &[five]);
    let want = f.eq(lhs, fact_5);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Eq ((5.choose 3) * 2! * 3!) 5!"
    );

    // Sanity: 5! reduces to the literal 120, and choose 5 3 to 10 -- confirms
    // this isn't a vacuous defeq between two stuck terms.
    let hundred_twenty = f.num(120);
    assert!(f.k.def_eq(fact_5, hundred_twenty), "5! must reduce to 120");
    assert!(f.k.def_eq(choose_5_3, ten), "choose 5 3 must reduce to 10");

    // Negative control: 5.choose 2 (=10, coincidentally the SAME value as
    // choose 5 3 -- Pascal symmetry) would be vacuous here, so use a
    // genuinely different value instead: 5.choose 1 = 5, giving
    // 5 * 2! * 3! = 60 != 120.
    let one = f.num(1);
    let choose_5_1 = f.const_app(p.choose, &[sum, one]);
    let choose1_fact2 = f.mul(choose_5_1, fact_2);
    let wrong_lhs = f.mul(choose1_fact2, fact_3);
    let wrong_want = f.eq(wrong_lhs, fact_5);
    assert!(
        !f.k.def_eq(inferred, wrong_want),
        "negative control: must not also state Eq ((5.choose 1) * 2! * 3!) 5!"
    );

    assert!(
        f.k.axiom_footprint(p.add_choose_mul_factorial_mul_factorial)
            .is_empty(),
        "add_choose_mul_factorial_mul_factorial must rest on zero axioms"
    );
}
