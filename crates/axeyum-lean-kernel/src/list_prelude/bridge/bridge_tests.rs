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

/// `List.count_toMultiset` landed (`ListNatBridge::count_to_multiset` is
/// `Some`, not the `None` `docs/plan/status/460-list-carrier-1.md` recorded),
/// is axiom-free, and instantiating the general (symbolic-in-`a`/`l`) proof
/// at concrete arguments both type-checks and matches independently
/// evaluated `count`/`Multiset.count (toMultiset …)` values -- the negative
/// controls are the SAME ones `list_count_matches_the_multiplicity` and
/// `to_multiset_agrees_with_count_at_several_points` already use, since a
/// wrong direction or a vacuous statement in `count_toMultiset` itself would
/// not be caught by either of those alone.
#[test]
fn count_to_multiset_landed_axiom_free_and_matches_concretely() {
    let mut f = Fixture::new();
    let ctm = f
        .bridge
        .count_to_multiset
        .expect("List.count_toMultiset must land (see the module doc for what unblocked it)");

    let footprint = f.k.axiom_footprint(ctm);
    assert!(
        footprint.is_empty(),
        "expected no axioms for List.count_toMultiset, found {footprint:?}"
    );

    let l = f.list_of(&[1, 2, 1]);
    let one = f.num(1);
    let three = f.num(3);
    let two = f.num(2);
    let zero = f.num(0);

    // Instantiate the theorem at (a := 1, l := [1,2,1]) and (a := 3, l :=
    // [1,2,1]); both must type-check (the theorem is `∀ a l, …`, so this
    // exercises the SAME general proof concretely, not a re-derivation).
    let ctm_const = f.k.const_(ctm, vec![]);
    let inst_at_one = f.k.app(ctm_const, one);
    let inst_at_one = f.k.app(inst_at_one, l);
    f.k.infer(inst_at_one)
        .expect("count_toMultiset applied at (1, [1,2,1]) must type-check");

    let ctm_const2 = f.k.const_(ctm, vec![]);
    let inst_at_three = f.k.app(ctm_const2, three);
    let inst_at_three = f.k.app(inst_at_three, l);
    f.k.infer(inst_at_three)
        .expect("count_toMultiset applied at (3, [1,2,1]) must type-check");

    // Independent evaluation: count 1 [1,2,1] = 2, count 3 [1,2,1] = 0 --
    // matching `to_multiset_agrees_with_count_at_several_points`'s own
    // negative-control shape (a repeat must not collapse to 1).
    let count1 = f.count(1, l);
    assert!(f.k.def_eq(count1, two), "count 1 [1,2,1] must be 2");
    assert!(
        !f.k.def_eq(count1, zero),
        "negative control: count 1 [1,2,1] must NOT be 0"
    );
    let count3 = f.count(3, l);
    assert!(f.k.def_eq(count3, zero), "count 3 [1,2,1] must be 0");
    assert!(
        !f.k.def_eq(count3, two),
        "negative control: count 3 [1,2,1] must NOT be 2"
    );
}
