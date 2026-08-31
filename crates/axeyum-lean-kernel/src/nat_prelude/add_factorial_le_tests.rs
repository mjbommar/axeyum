//! Concrete-instance tests for
//! `nat_prelude::add_factorial_le::{declare_add_factorial_le_factorial_add,
//! declare_add_factorial_succ_le_factorial_add_succ}`. Separate file for
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
fn add_factorial_le_factorial_add_computes_at_i2_n3() {
    // i=2, n=3: 2 + 3! = 2 + 6 = 8 <= (2+3)! = 5! = 120.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);

    // Le 1 3, built the same way `zero_lt_succ` builds `Le 1 (succ n)`:
    // here 3 is succ(2).
    let hyp_proof = f.zero_lt_succ(two);
    let applied = f.const_app(p.add_factorial_le_factorial_add, &[two, three]);
    let applied = f.apply(applied, &[hyp_proof]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_factorial_le_factorial_add must type-check: {}",
            f.explain(&e)
        )
    });

    let eight = f.num(8);
    let hundred_twenty = f.num(120);
    let fact3 = f.const_app(p.factorial, &[three]);
    let lhs = f.add(two, fact3);
    let sum = f.add(two, three);
    let rhs = f.const_app(p.factorial, &[sum]);
    let want = f.le(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Le (2 + 3!) ((2+3)!)"
    );
    assert!(f.k.def_eq(lhs, eight), "2 + 3! must reduce to 8");
    assert!(f.k.def_eq(rhs, hundred_twenty), "(2+3)! must reduce to 120");

    assert!(
        f.k
            .axiom_footprint(p.add_factorial_le_factorial_add)
            .is_empty(),
        "add_factorial_le_factorial_add must rest on zero axioms"
    );
}

#[test]
fn add_factorial_succ_le_factorial_add_succ_computes_at_i2_n2() {
    // i=2, n=2: 2 + (2+1)! = 2 + 3! = 8 <= (2+(2+1))! = 5! = 120.
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let applied = f.const_app(p.add_factorial_succ_le_factorial_add_succ, &[two, two]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_factorial_succ_le_factorial_add_succ must type-check: {}",
            f.explain(&e)
        )
    });

    let eight = f.num(8);
    let hundred_twenty = f.num(120);
    let sn = f.succ(two);
    let fact_sn = f.const_app(p.factorial, &[sn]);
    let lhs = f.add(two, fact_sn);
    let i_sn = f.add(two, sn);
    let rhs = f.const_app(p.factorial, &[i_sn]);
    let want = f.le(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "must state Le (2 + (2+1)!) ((2+(2+1))!)"
    );
    assert!(f.k.def_eq(lhs, eight), "2 + 3! must reduce to 8");
    assert!(
        f.k.def_eq(rhs, hundred_twenty),
        "(2+3)! must reduce to 120"
    );

    assert!(
        f.k
            .axiom_footprint(p.add_factorial_succ_le_factorial_add_succ)
            .is_empty(),
        "add_factorial_succ_le_factorial_add_succ must rest on zero axioms"
    );
}
