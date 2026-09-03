//! Concrete-instance tests for `List.Perm` and its four theorems.

use crate::expr::ExprId;
use crate::level::LevelId;
use crate::{Kernel, ListPerm, ListPrelude, NatPrelude, build_list_nat_bridge};

/// Coverage: `List.count_append` builds standalone (independent of the rest
/// of `ListPerm`), the prerequisite `declare_perm_reverse`'s cons case
/// unfolds through.
#[test]
fn count_append_builds_standalone() {
    let mut k = Kernel::new();
    let (p, nat, bridge) = build_list_nat_bridge(&mut k).expect("bridge must build");
    let names = super::super::ListNames {
        list: p.list,
        nil: p.nil,
        cons: p.cons,
        rec: p.rec,
        u_param: p.u_param,
        length: p.length,
        append: p.append,
        map: p.map,
        foldr: p.foldr,
        reverse: p.reverse,
    };
    let logic = nat.logic;
    let zero_lvl = k.level_zero();
    let one_lvl = k.level_succ(zero_lvl);
    let _count_append = super::declare_count_append(
        &mut k,
        &logic,
        &nat,
        &names,
        bridge.count,
        zero_lvl,
        one_lvl,
    )
    .expect("count_append must build");
}

/// Coverage: `List.count_reverse` builds standalone, on top of `count_append`.
#[test]
fn count_reverse_builds_standalone() {
    let mut k = Kernel::new();
    let (p, nat, bridge) = build_list_nat_bridge(&mut k).expect("bridge must build");
    let names = super::super::ListNames {
        list: p.list,
        nil: p.nil,
        cons: p.cons,
        rec: p.rec,
        u_param: p.u_param,
        length: p.length,
        append: p.append,
        map: p.map,
        foldr: p.foldr,
        reverse: p.reverse,
    };
    let logic = nat.logic;
    let zero_lvl = k.level_zero();
    let one_lvl = k.level_succ(zero_lvl);
    let count_append = super::declare_count_append(
        &mut k,
        &logic,
        &nat,
        &names,
        bridge.count,
        zero_lvl,
        one_lvl,
    )
    .expect("count_append must build");
    let _count_reverse = super::declare_count_reverse(
        &mut k,
        &logic,
        &nat,
        &names,
        bridge.count,
        count_append,
        zero_lvl,
        one_lvl,
    )
    .expect("count_reverse must build");
}

struct Fixture {
    k: Kernel,
    p: ListPrelude,
    nat: NatPrelude,
    perm: ListPerm,
    zero_lvl: LevelId,
    nat_ty: ExprId,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let (p, nat, bridge) = build_list_nat_bridge(&mut k).expect("bridge must build");
        let perm = super::build_list_perm(&mut k, &p, &nat, &bridge).expect("perm must build");
        let zero_lvl = k.level_zero();
        let nat_ty = k.const_(nat.nat, vec![]);
        Self {
            k,
            p,
            nat,
            perm,
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

    fn perm(&mut self, l1: ExprId, l2: ExprId) -> ExprId {
        let c = self.k.const_(self.perm.perm, vec![]);
        let c = self.k.app(c, l1);
        self.k.app(c, l2)
    }
}

#[test]
fn perm_computes_true_and_false_by_evaluation() {
    let mut f = Fixture::new();
    let bool_true = f.k.const_(f.nat.logic.bool_true, vec![]);
    let bool_false = f.k.const_(f.nat.logic.bool_false, vec![]);

    let l12 = f.list_of(&[1, 2]);
    let l21 = f.list_of(&[2, 1]);
    let perm_12_21 = f.perm(l12, l21);
    assert!(
        f.k.def_eq(perm_12_21, bool_true),
        "Perm [1,2] [2,1] must be true"
    );

    let l122 = f.list_of(&[1, 2, 2]);
    let perm_12_122 = f.perm(l12, l122);
    assert!(
        f.k.def_eq(perm_12_122, bool_false),
        "negative control: Perm [1,2] [1,2,2] must be false"
    );
    assert!(
        !f.k.def_eq(perm_12_122, bool_true),
        "negative control (explicit): Perm [1,2] [1,2,2] must NOT be true"
    );

    // Perm l l = true by computation too, not only by `perm_refl`.
    let perm_12_12 = f.perm(l12, l12);
    assert!(
        f.k.def_eq(perm_12_12, bool_true),
        "Perm [1,2] [1,2] must be true"
    );
}

/// Coverage: the four theorems are all axiom-free.
#[test]
fn the_perm_theorems_declare_no_axioms() {
    let f = Fixture::new();
    for name in [
        f.perm.perm_refl,
        f.perm.perm_symm,
        f.perm.perm_reverse,
        f.perm.perm_append_comm,
    ] {
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "expected no axioms for {name:?}, found {footprint:?}"
        );
    }
}

#[test]
fn perm_refl_type_checks_at_a_concrete_list() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 1]);
    let c = f.k.const_(f.perm.perm_refl, vec![]);
    let inst = f.k.app(c, l);
    f.k.infer(inst)
        .expect("perm_refl applied at [1,2,1] must type-check");
}

#[test]
fn perm_symm_type_checks_and_matches_evaluation() {
    let mut f = Fixture::new();
    let bool_true = f.k.const_(f.nat.logic.bool_true, vec![]);
    let l12 = f.list_of(&[1, 2]);
    let l21 = f.list_of(&[2, 1]);

    // Build a proof of `Perm [1,2] [2,1] = true` from `perm_refl` is not
    // directly available (they are different lists), so instantiate
    // `perm_symm` at (l12, l21) with a hypothesis PROOF built by checking
    // the concrete equation reduces to `true` and using `Eq.refl` at that
    // reduced value (both sides `def_eq`, so `Eq.refl` at `true` type-checks
    // against `Perm l12 l21 = true` by defeq).
    let perm_12_21 = f.perm(l12, l21);
    assert!(f.k.def_eq(perm_12_21, bool_true));
    let hp = {
        let one_lvl = f.k.level_succ(f.zero_lvl);
        let eq_refl = f.k.const_(f.nat.logic.eq_refl, vec![one_lvl]);
        let bool_ty = f.k.const_(f.nat.logic.bool_, vec![]);
        let c = f.k.app(eq_refl, bool_ty);
        f.k.app(c, bool_true)
    };

    let c = f.k.const_(f.perm.perm_symm, vec![]);
    let c = f.k.app(c, l12);
    let c = f.k.app(c, l21);
    let inst = f.k.app(c, hp);
    f.k.infer(inst)
        .expect("perm_symm applied at (l12, l21, hp) must type-check");
}

#[test]
fn perm_reverse_type_checks_at_a_concrete_list() {
    let mut f = Fixture::new();
    let l = f.list_of(&[1, 2, 1]);
    let c = f.k.const_(f.perm.perm_reverse, vec![]);
    let inst = f.k.app(c, l);
    f.k.infer(inst)
        .expect("perm_reverse applied at [1,2,1] must type-check");
}

#[test]
fn perm_append_comm_type_checks_at_concrete_lists() {
    let mut f = Fixture::new();
    let l1 = f.list_of(&[1, 2]);
    let l2 = f.list_of(&[3]);
    let c = f.k.const_(f.perm.perm_append_comm, vec![]);
    let c = f.k.app(c, l1);
    let inst = f.k.app(c, l2);
    f.k.infer(inst)
        .expect("perm_append_comm applied at ([1,2], [3]) must type-check");
}
