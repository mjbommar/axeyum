//! Concrete-instance tests for `nat_prelude::hall`.
//!
//! `Nat.Hall.anyBelow`, `unionBound` and `unionOver` are admitted on their
//! TYPE, so a wrong one type-checks. Each is reduced here at tiny arguments and
//! paired with the wrong formula it rules out: an `anyBelow` that forgot one of
//! its two negations is the universal quantifier instead of the existential,
//! and a `unionOver` that intersected instead of uniting would give the same
//! type and a smaller card.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    counter: u32,
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
        Self {
            k,
            p,
            st,
            counter: 0,
        }
    }

    /// A fresh scratch name for an accept/reject control.
    fn scratch(&mut self) -> crate::NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "hallControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it -- nothing here reads a boolean out of a checker of its own.
    fn admits(&mut self, ty: ExprId, value: ExprId) -> bool {
        let name = self.scratch();
        self.k
            .add_declaration(crate::env::Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .is_ok()
    }

    fn dev(&mut self) -> super::ops::NatDev<'_> {
        let p = self.p;
        super::ops::NatDev::new(&mut self.k, p)
    }

    /// `Nat.Finset.singleton a`.
    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.finset_singleton;
        self.const_app(name, &[lit])
    }

    fn union(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_union;
        self.const_app(name, &[s, t])
    }

    /// The `Nat.Finset` with exactly these members.
    fn set_of(&mut self, elements: &[u32]) -> ExprId {
        let (first, rest) = elements.split_first().expect("at least one element");
        let mut acc = self.singleton(*first);
        for &e in rest {
            let s = self.singleton(e);
            acc = self.union(acc, s);
        }
        acc
    }

    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    /// `fun i => <table[i] as a Nat.Finset>`, with `Nat.Finset.range 0` (the
    /// empty set) outside the table.
    fn family(&mut self, table: &[&[u32]]) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let zero = self.zero();
        let range = self.p.finset_range;
        let mut body = self.const_app(range, &[zero]);
        for (index, members) in table.iter().enumerate().rev() {
            let set = self.set_of(members);
            let lit = self.num(u32::try_from(index).expect("small index"));
            let hit = self.beq(i, lit);
            let name = self.p.finset_rec;
            let _ = name;
            body = self.select_finset(hit, set, body);
        }
        self.lam_fv(i_fv, nat, body)
    }

    /// `Bool.rec (fun _ => Nat.Finset) on_false on_true condition`.
    fn select_finset(&mut self, condition: ExprId, on_true: ExprId, on_false: ExprId) -> ExprId {
        let bool_ty = self.bool_ty();
        let fs = {
            let name = self.p.finset;
            self.k.const_(name, vec![])
        };
        let anon = self.anon_name();
        let motive = self.k.lam(anon, bool_ty, fs, crate::BinderInfo::Default);
        let one = self.level_one();
        let rec = {
            let name = self.p.logic.bool_rec;
            self.k.const_(name, vec![one])
        };
        self.apply(rec, &[motive, on_false, on_true, condition])
    }

    fn any_below(&mut self, f: ExprId, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.hall_any_below;
        self.const_app(name, &[f, lit])
    }

    fn union_over(&mut self, nb: ExprId, t: ExprId) -> ExprId {
        let name = self.p.hall_union_over;
        self.const_app(name, &[nb, t])
    }

    fn mem(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }

    /// `fun k => beq k target`.
    fn hits(&mut self, target: u32) -> ExprId {
        let nat = self.nat_ty();
        let lit = self.num(target);
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.beq(k, lit);
        self.lam_fv(k_fv, nat, body)
    }

    fn assert_bool(&mut self, term: ExprId, expected: bool, message: &str) {
        let want = if expected {
            self.bool_true()
        } else {
            self.bool_false()
        };
        let other = if expected {
            self.bool_false()
        } else {
            self.bool_true()
        };
        assert!(self.k.def_eq(term, want), "{message}");
        assert!(
            !self.k.def_eq(term, other),
            "negative control: {message} -- must NOT reduce to the other Bool"
        );
    }

    fn assert_num(&mut self, term: ExprId, expected: u32, message: &str) {
        let want = self.num(expected);
        assert!(self.k.def_eq(term, want), "{message}");
    }

    fn assert_not_num(&mut self, term: ExprId, wrong: u32, message: &str) {
        let bad = self.num(wrong);
        assert!(!self.k.def_eq(term, bad), "negative control: {message}");
    }
}

/// `Nat.Hall.anyBelow` is the bounded EXISTENTIAL, not the universal.
///
/// `fun k => beq k 2` is true at exactly one index, so `anyBelow` over `[0,4)`
/// must be `true` while the `allBelow` of the same predicate is `false`. That
/// pair is the discriminating check: an `anyBelow` that dropped one of its two
/// negations would agree with `allBelow` and fail here.
#[test]
fn any_below_is_the_bounded_existential() {
    let mut f = Fixture::new();
    let pred = f.hits(2);
    let found = f.any_below(pred, 4);
    f.assert_bool(found, true, "2 is below 4, so anyBelow must be true");

    let pred2 = f.hits(2);
    let all = {
        let name = f.p.finset_all_below;
        let four = f.num(4);
        f.const_app(name, &[pred2, four])
    };
    f.assert_bool(
        all,
        false,
        "allBelow of the same predicate must be false -- anyBelow is not allBelow",
    );

    // Out of range: `2` is not below `2`.
    let pred3 = f.hits(2);
    let missed = f.any_below(pred3, 2);
    f.assert_bool(
        missed,
        false,
        "anyBelow must not look at or above its bound",
    );
}

/// `Nat.Hall.unionOver` collects every member of every indexed set, and only
/// over the indices in the index set.
///
/// The family is `nb 0 = {1,2}`, `nb 1 = {2,3}`, `nb 2 = {7}`. Over the index
/// set `{0,1}` the union is `{1,2,3}`, so its card is `3`. The negative
/// controls are `2` (what an INTERSECTION would give, `{2}` having card 1, or
/// what dropping one index would give) and `4` (what including index `2`, which
/// is not in the index set, would give).
#[test]
fn union_over_collects_the_indexed_sets() {
    let mut f = Fixture::new();
    let nb = f.family(&[&[1, 2], &[2, 3], &[7]]);
    let idx = f.set_of(&[0, 1]);
    let cover = f.union_over(nb, idx);

    for v in [1u32, 2, 3] {
        let inside = f.mem(cover, v);
        f.assert_bool(inside, true, "every member of an indexed set is covered");
    }
    let outside = f.mem(cover, 7);
    f.assert_bool(
        outside,
        false,
        "index 2 is not in the index set, so 7 is not covered",
    );
    let never = f.mem(cover, 0);
    f.assert_bool(never, false, "0 is in no indexed set");

    let c = f.card(cover);
    f.assert_num(c, 3, "the union over {0,1} is {1,2,3}");
    f.assert_not_num(c, 1, "negative control: the INTERSECTION {2} has card 1");
    f.assert_not_num(c, 4, "negative control: including index 2 would give 4");
}

/// The union over a one-element index set is that set, and the union over the
/// empty index set is empty — the two degenerate cases a bounded loop gets
/// wrong in opposite directions.
#[test]
fn union_over_handles_the_degenerate_index_sets() {
    let mut f = Fixture::new();

    let nb = f.family(&[&[1, 2], &[2, 3]]);
    let one = f.set_of(&[1]);
    let cover = f.union_over(nb, one);
    let c = f.card(cover);
    f.assert_num(c, 2, "the union over {1} is nb 1 = {2,3}");
    f.assert_not_num(c, 3, "negative control: the whole union would give 3");

    let nb2 = f.family(&[&[1, 2], &[2, 3]]);
    let empty = {
        let name = f.p.finset_range;
        let zero = f.zero();
        f.const_app(name, &[zero])
    };
    let none = f.union_over(nb2, empty);
    let c0 = f.card(none);
    f.assert_num(c0, 0, "the union over the empty index set is empty");
}

/// `Nat.Hall.hallCondition_of_isMatching` proves NECESSITY and not sufficiency.
///
/// This is the one place a reader could take more from the lane than landed, so
/// it is pinned in both directions with the SAME proof term: the implication
/// `IsMatching → HallCondition` is admitted, and the converse
/// `HallCondition → IsMatching` — which is Hall's marriage theorem proper, and
/// is NOT proved here — must be rejected.
#[test]
fn hall_necessity_is_admitted_and_sufficiency_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, forward: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let fam = d.arrow(nat, fs);
        let ch = d.arrow(nat, nat);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let fn_fv = d.fresh_fvar();
        let choice = d.kernel().fvar(fn_fv);
        let matching = d.const_app(p.hall_is_matching, &[s, nb, choice]);
        let condition = d.const_app(p.hall_condition, &[s, nb]);
        let step = if forward {
            d.arrow(matching, condition)
        } else {
            d.arrow(condition, matching)
        };
        let ty = {
            let s3 = d.pi_fv(fn_fv, ch, step);
            let s2 = d.pi_fv(nb_fv, fam, s3);
            d.pi_fv(s_fv, fs, s2)
        };
        let value = d.kernel().const_(p.hall_condition_of_is_matching, vec![]);
        (ty, value)
    };

    let (ty, value) = build(&mut f, true);
    assert!(
        f.admits(ty, value),
        "the necessity direction must be admitted"
    );

    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: the SUFFICIENCY direction -- Hall's marriage \
         theorem proper -- is not proved by this lane and must be rejected"
    );
}
