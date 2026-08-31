//! Concrete-instance test for
//! `nat_prelude::asc_factorial_div::declare_asc_factorial_eq_div`. Separate
//! file for the same merge-hazard reason as `bit_extra_tests.rs`/
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
fn asc_factorial_eq_div_computes_at_n2_k3() {
    // n=2, k=3: (2+1).ascFactorial 3 = 3.ascFactorial 3 = 3*4*5 = 60 ;
    // (2+3)! / 2! = 120 / 2 = 60.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let applied = f.const_app(p.asc_factorial_eq_div, &[two, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "asc_factorial_eq_div must type-check: {}",
            f.explain(&e)
        )
    });

    let sixty = f.num(60);
    let sn = f.succ(two);
    let af = f.const_app(p.asc_factorial, &[sn, three]);
    let sum = f.add(two, three);
    let fact_nk = f.const_app(p.factorial, &[sum]);
    let fact_n = f.const_app(p.factorial, &[two]);
    let div_term = f.div(fact_nk, fact_n);
    let want = f.eq(af, div_term);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Eq (3.ascFactorial 3) (5! / 2!)"
    );

    // Sanity: every subterm reduces to the concrete numeral it should.
    let hundred_twenty = f.num(120);
    let two_val = f.num(2);
    assert!(f.k.def_eq(fact_nk, hundred_twenty), "5! must reduce to 120");
    assert!(f.k.def_eq(fact_n, two_val), "2! must reduce to 2");
    assert!(f.k.def_eq(af, sixty), "3.ascFactorial 3 must reduce to 60");
    assert!(f.k.def_eq(div_term, sixty), "120 / 2 must reduce to 60");

    // Negative control: (2+1).ascFactorial 2 = 3*4 = 12, discriminating
    // from 120/2 = 60.
    let af2 = f.const_app(p.asc_factorial, &[sn, two]);
    let wrong_want = f.eq(af2, div_term);
    assert!(
        !f.k.def_eq(inferred, wrong_want),
        "negative control: must not also state Eq (3.ascFactorial 2) (5! / 2!)"
    );

    assert!(
        f.k.axiom_footprint(p.asc_factorial_eq_div).is_empty(),
        "asc_factorial_eq_div must rest on zero axioms"
    );
}
