//! Concrete-instance tests for the `List`/`Nat` bridge: `List.sum`,
//! `List.toMultiset`, `List.count`, and a coverage check on the bridge
//! theorems' axiom footprints.

use crate::expr::ExprId;
use crate::level::LevelId;
use crate::{Kernel, ListNatBridge, ListPrelude, NatPrelude, build_list_nat_bridge};

struct Fixture {
    k: Kernel,
    p: ListPrelude,
    nat: NatPrelude,
    bridge: ListNatBridge,
    zero_lvl: LevelId,
    nat_ty: ExprId,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let (p, nat, bridge) = build_list_nat_bridge(&mut k).expect("bridge must build");
        let zero_lvl = k.level_zero();
        let nat_ty = k.const_(nat.nat, vec![]);
        Self {
            k,
            p,
            nat,
            bridge,
            zero_lvl,
            nat_ty,
        }
    }

    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.k.const_(self.nat.zero, vec![]);
        let succ = self.k.const_(self.nat.succ, vec![]);
        for _ in 0..n {
            e = self.k.app(succ, e);
        }
        e
    }

    fn nil_nat(&mut self) -> ExprId {
        let c = self.k.const_(self.p.nil, vec![self.zero_lvl]);
        self.k.app(c, self.nat_ty)
    }

    fn cons_nat(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let c = self.k.const_(self.p.cons, vec![self.zero_lvl]);
        let c = self.k.app(c, self.nat_ty);
        let c = self.k.app(c, head);
        self.k.app(c, tail)
    }

    fn list_of(&mut self, elements: &[u32]) -> ExprId {
        let mut acc = self.nil_nat();
        for &e in elements.iter().rev() {
            let lit = self.num(e);
            acc = self.cons_nat(lit, acc);
        }
        acc
    }

    fn sum(&mut self, l: ExprId) -> ExprId {
        let c = self.k.const_(self.bridge.sum, vec![]);
        self.k.app(c, l)
    }

    fn build_to_multiset(&mut self, l: ExprId) -> ExprId {
        let c = self.k.const_(self.bridge.to_multiset, vec![]);
        self.k.app(c, l)
    }

    fn count(&mut self, a: u32, l: ExprId) -> ExprId {
        let lit = self.num(a);
        let c = self.k.const_(self.bridge.count, vec![]);
        let c = self.k.app(c, lit);
        self.k.app(c, l)
    }

    fn multiset_count(&mut self, m: ExprId, a: u32) -> ExprId {
        let lit = self.num(a);
        let c = self.k.const_(self.nat.multiset_count, vec![]);
        let c = self.k.app(c, m);
        self.k.app(c, lit)
    }
}

#[test]
fn sum_adds_the_elements_not_counts_them() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 3]);
    let summed = f.sum(l);
    let six = f.num(6);
    let three = f.num(3);
    assert!(f.k.def_eq(summed, six), "sum [1,2,3] must be 6");
    assert!(
        !f.k.def_eq(summed, three),
        "negative control: sum [1,2,3] must NOT be 3 (the element count)"
    );

    let empty = f.nil_nat();
    let sum0 = f.sum(empty);
    let zero = f.num(0);
    assert!(f.k.def_eq(sum0, zero), "sum [] must be 0");
}

#[test]
fn to_multiset_agrees_with_count_at_several_points() {
    let mut f = Fixture::new();
    let l = f.list_of(&[2, 2, 3]);
    let m = f.build_to_multiset(l);
    let count0 = f.multiset_count(m, 0);
    let count2 = f.multiset_count(m, 2);
    let count3 = f.multiset_count(m, 3);
    let zero = f.num(0);
    let one = f.num(1);
    let two = f.num(2);
    assert!(
        f.k.def_eq(count0, zero),
        "Multiset.count (toMultiset [2,2,3]) 0 must be 0"
    );
    assert!(
        f.k.def_eq(count2, two),
        "Multiset.count (toMultiset [2,2,3]) 2 must be 2"
    );
    assert!(
        !f.k.def_eq(count2, one),
        "negative control: must NOT be 1 -- a set-flavoured toMultiset that \
         discards the repeat"
    );
    assert!(
        f.k.def_eq(count3, one),
        "Multiset.count (toMultiset [2,2,3]) 3 must be 1"
    );
}

#[test]
fn list_count_matches_the_multiplicity() {
    let mut f = Fixture::new();
    let l = f.list_of(&[2, 2, 3]);
    let c2 = f.count(2, l);
    let c3 = f.count(3, l);
    let c9 = f.count(9, l);
    let zero = f.num(0);
    let one = f.num(1);
    let two = f.num(2);
    assert!(f.k.def_eq(c2, two), "count 2 [2,2,3] must be 2");
    assert!(
        !f.k.def_eq(c2, one),
        "negative control: count 2 [2,2,3] must NOT be 1"
    );
    assert!(f.k.def_eq(c3, one), "count 3 [2,2,3] must be 1");
    assert!(f.k.def_eq(c9, zero), "count 9 [2,2,3] must be 0");
}

/// Coverage: `length_append`, `length_reverse` and `sum_append` are present
/// and axiom-free.
#[test]
fn the_bridge_theorems_declare_no_axioms() {
    let f = Fixture::new();
    for name in [
        f.bridge.length_append,
        f.bridge.length_reverse,
        f.bridge.sum_append,
    ] {
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "expected no axioms for {name:?}, found {footprint:?}"
        );
    }
}
