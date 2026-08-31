//! Concrete-instance test for
//! `nat_prelude::add_desc_factorial_asc_factorial::declare_add_desc_factorial_eq_asc_factorial`.
//! Separate file for the same merge-hazard reason as `bit_extra_tests.rs`/
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
fn add_desc_factorial_eq_asc_factorial_computes_at_n2_k3() {
    // n=2, k=3: (2+3).descFactorial 3 = 5.descFactorial 3 = 5*4*3 = 60 ;
    // (2+1).ascFactorial 3 = 3.ascFactorial 3 = 3*4*5 = 60.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let applied = f.const_app(p.add_desc_factorial_eq_asc_factorial, &[two, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_desc_factorial_eq_asc_factorial must type-check: {}",
            f.explain(&e)
        )
    });

    let five = f.num(5);
    let sixty = f.num(60);
    let sum = f.add(two, three);
    let df = f.const_app(p.desc_factorial, &[sum, three]);
    let sn = f.succ(two);
    let af = f.const_app(p.asc_factorial, &[sn, three]);
    let want = f.eq(df, af);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Eq ((2+3).descFactorial 3) ((2+1).ascFactorial 3)"
    );

    // Sanity: both sides reduce to the same concrete numeral, confirming
    // this isn't a vacuous defeq between two stuck terms.
    assert!(f.k.def_eq(df, sixty), "(2+3).descFactorial 3 must reduce to 60");
    assert!(f.k.def_eq(af, sixty), "(2+1).ascFactorial 3 must reduce to 60");
    assert!(f.k.def_eq(sn, three), "succ 2 must reduce to 3");
    let _ = five;

    // Negative control: (2+3).descFactorial 2 = 5*4 = 20, discriminating
    // from (2+1).ascFactorial 3 = 60.
    let df2 = f.const_app(p.desc_factorial, &[sum, two]);
    let wrong_want = f.eq(df2, af);
    assert!(
        !f.k.def_eq(inferred, wrong_want),
        "negative control: must not also state Eq ((2+3).descFactorial 2) ((2+1).ascFactorial 3)"
    );

    assert!(
        f.k
            .axiom_footprint(p.add_desc_factorial_eq_asc_factorial)
            .is_empty(),
        "add_desc_factorial_eq_asc_factorial must rest on zero axioms"
    );
}
