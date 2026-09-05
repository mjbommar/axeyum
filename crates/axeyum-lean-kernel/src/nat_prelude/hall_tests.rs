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
// ---------------------------------------------------------------------------
// The counting half (ADR-1623): `sdiff` under `card`, and `unionOver` under
// index-set congruence and family modification.
// ---------------------------------------------------------------------------

/// Concrete evaluation of the set difference the whole lane is about.
///
/// `{1,2,3} \ {2}` is `{1,3}`. The two negative controls are the two ways a
/// wrong `sdiff` reads: `3` is what NO deletion gives, and `1` is what
/// deleting everything BUT `2` (the arguments swapped) gives.
#[test]
fn sdiff_deletes_exactly_the_second_set() {
    let mut f = Fixture::new();
    let s = f.set_of(&[1, 2, 3]);
    let t = f.set_of(&[2]);
    let diff = {
        let name = f.p.finset_sdiff;
        f.const_app(name, &[s, t])
    };

    for v in [1u32, 3] {
        let inside = f.mem(diff, v);
        f.assert_bool(inside, true, "a member not deleted stays");
    }
    let gone = f.mem(diff, 2);
    f.assert_bool(gone, false, "the deleted member is gone");
    let never = f.mem(diff, 5);
    f.assert_bool(never, false, "a non-member is still a non-member");

    let c = f.card(diff);
    f.assert_num(c, 2, "{1,2,3} minus {2} is {1,3}");
    f.assert_not_num(c, 3, "negative control: no deletion would give 3");
    f.assert_not_num(c, 1, "negative control: the SWAPPED difference gives 1");
}

/// The three `sdiff` membership laws are admitted, and each is offered again
/// with ONE small term slid — the two sets exchanged, or one polarity flipped
/// — where the trusted gate must refuse the same proof term.
#[test]
fn the_sdiff_membership_laws_are_admitted_and_the_slid_statements_are_not() {
    let mut f = Fixture::new();

    // `memB_sdiff`, with the two sets exchanged on the right-hand side.
    let build_pointwise = |f: &mut Fixture, swapped: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sd = d.const_app(p.finset_sdiff, &[s, t]);
        let lhs = d.const_app(p.finset_mem_b, &[sd, i]);
        let ms = d.const_app(p.finset_mem_b, &[s]);
        let mt = d.const_app(p.finset_mem_b, &[t]);
        let dfn = if swapped {
            d.const_app(p.set_diff, &[mt, ms])
        } else {
            d.const_app(p.set_diff, &[ms, mt])
        };
        let rhs = d.apply(dfn, &[i]);
        let body = d.bool_eq(lhs, rhs);
        let ty = {
            let with_i = d.pi_fv(i_fv, nat, body);
            let with_t = d.pi_fv(t_fv, fs, with_i);
            d.pi_fv(s_fv, fs, with_t)
        };
        let value = d.kernel().const_(p.finset_mem_b_sdiff, vec![]);
        (ty, value)
    };
    let (ty, value) = build_pointwise(&mut f, false);
    assert!(f.admits(ty, value), "memB_sdiff must be admitted");
    let (ty, value) = build_pointwise(&mut f, true);
    assert!(
        !f.admits(ty, value),
        "negative control: `setDiff` with its two sets exchanged is a \
         DIFFERENT set and must be rejected"
    );

    // `memB_sdiff_intro`, with the deleted set's polarity flipped.
    let build_intro = |f: &mut Fixture, flipped: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tru = d.bool_true();
        let fal = d.bool_false();
        let mem_s = d.const_app(p.finset_mem_b, &[s, i]);
        let mem_t = d.const_app(p.finset_mem_b, &[t, i]);
        let h1 = d.bool_eq(mem_s, tru);
        let h2 = if flipped {
            d.bool_eq(mem_t, tru)
        } else {
            d.bool_eq(mem_t, fal)
        };
        let sd = d.const_app(p.finset_sdiff, &[s, t]);
        let lhs = d.const_app(p.finset_mem_b, &[sd, i]);
        let concl = d.bool_eq(lhs, tru);
        let ty = {
            let with_h2 = d.arrow(h2, concl);
            let with_h1 = d.arrow(h1, with_h2);
            let with_i = d.pi_fv(i_fv, nat, with_h1);
            let with_t = d.pi_fv(t_fv, fs, with_i);
            d.pi_fv(s_fv, fs, with_t)
        };
        let value = d.kernel().const_(p.finset_mem_b_sdiff_intro, vec![]);
        (ty, value)
    };
    let (ty, value) = build_intro(&mut f, false);
    assert!(f.admits(ty, value), "memB_sdiff_intro must be admitted");
    let (ty, value) = build_intro(&mut f, true);
    assert!(
        !f.admits(ty, value),
        "negative control: a member OF the deleted set is not in the \
         difference, so the flipped hypothesis must be rejected"
    );

    // `memB_sdiff_elim`, with the second conjunct's polarity flipped.
    let build_elim = |f: &mut Fixture, flipped: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tru = d.bool_true();
        let fal = d.bool_false();
        let sd = d.const_app(p.finset_sdiff, &[s, t]);
        let lhs = d.const_app(p.finset_mem_b, &[sd, i]);
        let hyp = d.bool_eq(lhs, tru);
        let mem_s = d.const_app(p.finset_mem_b, &[s, i]);
        let mem_t = d.const_app(p.finset_mem_b, &[t, i]);
        let left = d.bool_eq(mem_s, tru);
        let right = if flipped {
            d.bool_eq(mem_t, tru)
        } else {
            d.bool_eq(mem_t, fal)
        };
        let concl = d.const_app(p.logic.and, &[left, right]);
        let ty = {
            let with_h = d.arrow(hyp, concl);
            let with_i = d.pi_fv(i_fv, nat, with_h);
            let with_t = d.pi_fv(t_fv, fs, with_i);
            d.pi_fv(s_fv, fs, with_t)
        };
        let value = d.kernel().const_(p.finset_mem_b_sdiff_elim, vec![]);
        (ty, value)
    };
    let (ty, value) = build_elim(&mut f, false);
    assert!(f.admits(ty, value), "memB_sdiff_elim must be admitted");
    let (ty, value) = build_elim(&mut f, true);
    assert!(
        !f.admits(ty, value),
        "negative control: the elimination says the point is OFF the deleted \
         set, and the flipped conjunct must be rejected"
    );
}

/// `Nat.Finset.card_le_card_sdiff_add` — the counting core — is admitted, and
/// the same proof term is REFUSED at the statement with the deleted set's own
/// size dropped from the right.
///
/// The concrete half is a TIGHT instance, which is what makes the arithmetic
/// discriminating: `card {1,2,3} = 3` and `card ({1,2,3} \ {2}) + card {2}`
/// is `2 + 1 = 3`. An off-by-one in either direction breaks it, and the
/// dropped-term control `3 ≤ 2` is false.
#[test]
fn card_le_card_sdiff_add_is_admitted_and_dropping_the_deleted_size_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, dropped: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let fs = d.kernel().const_(p.finset, vec![]);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let sd = d.const_app(p.finset_sdiff, &[s, t]);
        let card_s = d.const_app(p.finset_card, &[s]);
        let card_sd = d.const_app(p.finset_card, &[sd]);
        let card_t = d.const_app(p.finset_card, &[t]);
        let rhs = if dropped {
            card_sd
        } else {
            d.add(card_sd, card_t)
        };
        let concl = d.le(card_s, rhs);
        let ty = {
            let with_t = d.pi_fv(t_fv, fs, concl);
            d.pi_fv(s_fv, fs, with_t)
        };
        let value = d.kernel().const_(p.finset_card_le_card_sdiff_add, vec![]);
        (ty, value)
    };
    let (ty, value) = build(&mut f, false);
    assert!(
        f.admits(ty, value),
        "the additive deletion bound must be admitted"
    );
    let (ty, value) = build(&mut f, true);
    assert!(
        !f.admits(ty, value),
        "negative control: without the deleted set's own size the bound is \
         false and must be rejected"
    );

    // The tight concrete instance the statement asserts.
    let s = f.set_of(&[1, 2, 3]);
    let t = f.set_of(&[2]);
    let diff = {
        let name = f.p.finset_sdiff;
        f.const_app(name, &[s, t])
    };
    let card_s = f.card(s);
    f.assert_num(card_s, 3, "card {1,2,3} = 3");
    let sum = {
        let a = f.card(diff);
        let b = f.card(t);
        f.add(a, b)
    };
    f.assert_num(sum, 3, "card ({1,2,3} \\ {2}) + card {2} = 2 + 1 = 3");
    f.assert_not_num(sum, 2, "negative control: dropping card {2} would give 2");
    f.assert_not_num(sum, 4, "negative control: no deletion would give 4");
}

/// `Nat.Hall.anyBelow_witness` is admitted at a `true` verdict and REFUSED at
/// a `false` one — the two are each other's control, exactly as
/// `subset_search.rs`'s two polarities are.
#[test]
fn any_below_witness_is_admitted_and_the_false_verdict_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, at_true: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let bool_ty = d.bool_ty();
        let pty = d.arrow(nat, bool_ty);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let tru = d.bool_true();
        let fal = d.bool_false();
        let search = d.const_app(p.hall_any_below, &[g, n]);
        let hyp = if at_true {
            d.bool_eq(search, tru)
        } else {
            d.bool_eq(search, fal)
        };
        let result_pred = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt = d.lt(i, n);
            let gi = d.apply(g, &[i]);
            let tru2 = d.bool_true();
            let is_true = d.bool_eq(gi, tru2);
            let body = d.const_app(p.logic.and, &[lt, is_true]);
            d.lam_fv(i_fv, nat, body)
        };
        let one = d.level_one();
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        let concl = d.apply(ex, &[nat, result_pred]);
        let ty = {
            let with_h = d.arrow(hyp, concl);
            let with_n = d.pi_fv(n_fv, nat, with_h);
            d.pi_fv(g_fv, pty, with_n)
        };
        let value = d.kernel().const_(p.hall_any_below_witness, vec![]);
        (ty, value)
    };
    let (ty, value) = build(&mut f, true);
    assert!(
        f.admits(ty, value),
        "a `true` bounded existential must yield a witness"
    );
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: an EXHAUSTED search yields no witness, so the \
         `false` verdict must be rejected"
    );
}

/// `Nat.Hall.memB_unionOver_elim` is admitted, and refused with its hypothesis
/// at `false` — the shape that would say a NON-member of the union has a
/// covering index.
#[test]
fn mem_union_over_elim_is_admitted_and_the_false_hypothesis_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, at_true: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let fam = d.arrow(nat, fs);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let tru = d.bool_true();
        let fal = d.bool_false();
        let cover = d.const_app(p.hall_union_over, &[nb, t]);
        let mem_here = d.const_app(p.finset_mem_b, &[cover, v]);
        let hyp = if at_true {
            d.bool_eq(mem_here, tru)
        } else {
            d.bool_eq(mem_here, fal)
        };
        let result_pred = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_t = d.const_app(p.finset_mem_b, &[t, i]);
            let tru2 = d.bool_true();
            let left = d.bool_eq(in_t, tru2);
            let member = d.apply(nb, &[i]);
            let holds = d.const_app(p.finset_mem_b, &[member, v]);
            let right = d.bool_eq(holds, tru2);
            let body = d.const_app(p.logic.and, &[left, right]);
            d.lam_fv(i_fv, nat, body)
        };
        let one = d.level_one();
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        let concl = d.apply(ex, &[nat, result_pred]);
        let ty = {
            let with_h = d.arrow(hyp, concl);
            let with_v = d.pi_fv(v_fv, nat, with_h);
            let with_t = d.pi_fv(t_fv, fs, with_v);
            d.pi_fv(nb_fv, fam, with_t)
        };
        let value = d.kernel().const_(p.hall_mem_union_over_elim, vec![]);
        (ty, value)
    };
    let (ty, value) = build(&mut f, true);
    assert!(
        f.admits(ty, value),
        "a member of the union must have a covering index"
    );
    let (ty, value) = build(&mut f, false);
    assert!(
        !f.admits(ty, value),
        "negative control: a NON-member has no covering index"
    );
}

/// The two index-set congruences are admitted WITH the membership hypothesis
/// and refused without it.
///
/// Dropping the hypothesis is the whole content of the statement: two
/// `Nat.Finset`s with different members give different unions, and the
/// hypothesis-free form would say every index set gives the same union. That
/// it is exactly one binder smaller is the point — a congruence that could be
/// stated without its congruence premise would not be worth proving.
#[test]
fn the_union_congruences_are_admitted_and_dropping_the_hypothesis_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, on_card: bool, with_hyp: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let fam = d.arrow(nat, fs);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let hc_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lhs = d.const_app(p.finset_mem_b, &[t, i]);
            let rhs = d.const_app(p.finset_mem_b, &[u, i]);
            let body = d.bool_eq(lhs, rhs);
            d.pi_fv(i_fv, nat, body)
        };
        let cover_t = d.const_app(p.hall_union_over, &[nb, t]);
        let cover_u = d.const_app(p.hall_union_over, &[nb, u]);
        let core = if on_card {
            let lhs = d.const_app(p.finset_card, &[cover_t]);
            let rhs = d.const_app(p.finset_card, &[cover_u]);
            d.eq(lhs, rhs)
        } else {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let lhs = d.const_app(p.finset_mem_b, &[cover_t, v]);
            let rhs = d.const_app(p.finset_mem_b, &[cover_u, v]);
            let body = d.bool_eq(lhs, rhs);
            d.pi_fv(v_fv, nat, body)
        };
        let inner = if with_hyp { d.arrow(hc_ty, core) } else { core };
        let ty = {
            let with_u = d.pi_fv(u_fv, fs, inner);
            let with_t = d.pi_fv(t_fv, fs, with_u);
            d.pi_fv(nb_fv, fam, with_t)
        };
        let name = if on_card {
            p.hall_card_union_over_congr
        } else {
            p.hall_mem_union_over_congr
        };
        let value = d.kernel().const_(name, vec![]);
        (ty, value)
    };

    for on_card in [false, true] {
        let (ty, value) = build(&mut f, on_card, true);
        assert!(
            f.admits(ty, value),
            "the union congruence must be admitted with its hypothesis \
             (on_card={on_card})"
        );
        let (ty, value) = build(&mut f, on_card, false);
        assert!(
            !f.admits(ty, value),
            "negative control: without the membership hypothesis the \
             congruence is false (on_card={on_card})"
        );
    }
}

/// Deleting commutes with the union, at a CONCRETE family, tightly.
///
/// `nb 0 = {1,2}`, `nb 1 = {2,3}`, index set `{0,1}`, deleted set `u = {2}`.
/// The union is `{1,2,3}` (card 3); the union of the deleted family is
/// `{1} ∪ {3} = {1,3}` (card 2), and so is the deletion of the union. The
/// negative control is `3`, which is what a family modification that did NOT
/// take effect would give — the exact failure the symbolic statement rules out.
#[test]
fn deleting_commutes_with_the_union_at_a_concrete_family() {
    let mut f = Fixture::new();
    let nb = f.family(&[&[1, 2], &[2, 3]]);
    let idx = f.set_of(&[0, 1]);
    let u = f.set_of(&[2]);

    let cover = f.union_over(nb, idx);
    let c_cover = f.card(cover);
    f.assert_num(c_cover, 3, "the undeleted union is {1,2,3}");

    let deleted_cover = {
        let name = f.p.finset_sdiff;
        f.const_app(name, &[cover, u])
    };
    let c_deleted_cover = f.card(deleted_cover);
    f.assert_num(
        c_deleted_cover,
        2,
        "deleting {2} from the union gives {1,3}",
    );

    let nb_del = {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let member = d.apply(nb, &[i]);
        let body = d.const_app(p.finset_sdiff, &[member, u]);
        d.lam_fv(i_fv, nat, body)
    };
    let cover_del = f.union_over(nb_del, idx);
    let c_cover_del = f.card(cover_del);
    f.assert_num(
        c_cover_del,
        2,
        "the union of the deleted family is {1} u {3} = {1,3}",
    );
    f.assert_not_num(
        c_cover_del,
        3,
        "negative control: a family modification that did not take effect \
         would leave the card at 3",
    );

    // The deficiency inequality is TIGHT here: 3 <= 2 + 1.
    let bound = {
        let a = f.card(cover_del);
        let b = f.card(u);
        f.add(a, b)
    };
    f.assert_num(bound, 3, "card (unionOver nb' t) + card u = 2 + 1 = 3");
    f.assert_not_num(bound, 4, "negative control: an undeleted family gives 4");
}

/// The two family-modification transports are admitted, and refused when the
/// family on the left is left UNDELETED — the one term the statement is about.
#[test]
fn the_family_modification_laws_are_admitted_and_the_undeleted_family_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, on_card: bool, deleted: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let fam = d.arrow(nat, fs);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);

        let nb_del = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let member = d.apply(nb, &[i]);
            let body = d.const_app(p.finset_sdiff, &[member, u]);
            d.lam_fv(i_fv, nat, body)
        };
        let left_family = if deleted { nb_del } else { nb };
        let left_cover = d.const_app(p.hall_union_over, &[left_family, t]);
        let cover = d.const_app(p.hall_union_over, &[nb, t]);
        let right = d.const_app(p.finset_sdiff, &[cover, u]);

        let core = if on_card {
            let lhs = d.const_app(p.finset_card, &[left_cover]);
            let rhs = d.const_app(p.finset_card, &[right]);
            d.eq(lhs, rhs)
        } else {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let lhs = d.const_app(p.finset_mem_b, &[left_cover, v]);
            let rhs = d.const_app(p.finset_mem_b, &[right, v]);
            let body = d.bool_eq(lhs, rhs);
            d.pi_fv(v_fv, nat, body)
        };
        let ty = {
            let with_t = d.pi_fv(t_fv, fs, core);
            let with_u = d.pi_fv(u_fv, fs, with_t);
            d.pi_fv(nb_fv, fam, with_u)
        };
        let name = if on_card {
            p.hall_card_union_over_sdiff
        } else {
            p.hall_mem_union_over_sdiff
        };
        let value = d.kernel().const_(name, vec![]);
        (ty, value)
    };

    for on_card in [false, true] {
        let (ty, value) = build(&mut f, on_card, true);
        assert!(
            f.admits(ty, value),
            "deleting commutes with the union (on_card={on_card})"
        );
        let (ty, value) = build(&mut f, on_card, false);
        assert!(
            !f.admits(ty, value),
            "negative control: with the family left UNDELETED the two sides \
             differ by exactly `u` (on_card={on_card})"
        );
    }
}

/// The deficiency inequality is admitted, and refused without the deleted
/// set's own size — the same slide `card_le_card_sdiff_add` is controlled by,
/// one level up.
#[test]
fn the_deficiency_inequality_is_admitted_and_dropping_the_deleted_size_is_not() {
    let mut f = Fixture::new();

    let build = |f: &mut Fixture, dropped: bool| -> (ExprId, ExprId) {
        let p = f.p;
        let mut d = f.dev();
        let nat = d.nat_ty();
        let fs = d.kernel().const_(p.finset, vec![]);
        let fam = d.arrow(nat, fs);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);

        let nb_del = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let member = d.apply(nb, &[i]);
            let body = d.const_app(p.finset_sdiff, &[member, u]);
            d.lam_fv(i_fv, nat, body)
        };
        let cover_del = d.const_app(p.hall_union_over, &[nb_del, t]);
        let cover = d.const_app(p.hall_union_over, &[nb, t]);
        let card_cover = d.const_app(p.finset_card, &[cover]);
        let card_cover_del = d.const_app(p.finset_card, &[cover_del]);
        let card_u = d.const_app(p.finset_card, &[u]);
        let rhs = if dropped {
            card_cover_del
        } else {
            d.add(card_cover_del, card_u)
        };
        let concl = d.le(card_cover, rhs);
        let ty = {
            let with_t = d.pi_fv(t_fv, fs, concl);
            let with_u = d.pi_fv(u_fv, fs, with_t);
            d.pi_fv(nb_fv, fam, with_u)
        };
        let value = d
            .kernel()
            .const_(p.hall_card_le_card_union_over_sdiff_add, vec![]);
        (ty, value)
    };
    let (ty, value) = build(&mut f, false);
    assert!(
        f.admits(ty, value),
        "the deficiency inequality must be admitted"
    );
    let (ty, value) = build(&mut f, true);
    assert!(
        !f.admits(ty, value),
        "negative control: the deleted family's union really is smaller, so \
         the bound without `card u` must be rejected"
    );
}

/// Every declaration this lane added is present AND axiom-free, both read from
/// the kernel. The presence check is not decoration: `axiom_footprint` returns
/// an empty vector for a name that was never declared, so the footprint
/// assertion alone would pass vacuously on a missing one.
#[test]
fn every_hall_counting_declaration_is_present_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names = [
        ("Nat.Finset.memB_sdiff", p.finset_mem_b_sdiff),
        ("Nat.Finset.memB_sdiff_intro", p.finset_mem_b_sdiff_intro),
        ("Nat.Finset.memB_sdiff_elim", p.finset_mem_b_sdiff_elim),
        (
            "Nat.Finset.card_le_card_sdiff_add",
            p.finset_card_le_card_sdiff_add,
        ),
        ("Nat.Hall.anyBelow_witness", p.hall_any_below_witness),
        ("Nat.Hall.memB_unionOver_elim", p.hall_mem_union_over_elim),
        ("Nat.Hall.memB_unionOver_congr", p.hall_mem_union_over_congr),
        (
            "Nat.Hall.card_unionOver_congr",
            p.hall_card_union_over_congr,
        ),
        ("Nat.Hall.memB_unionOver_sdiff", p.hall_mem_union_over_sdiff),
        (
            "Nat.Hall.card_unionOver_sdiff",
            p.hall_card_union_over_sdiff,
        ),
        (
            "Nat.Hall.card_le_card_unionOver_sdiff_add",
            p.hall_card_le_card_union_over_sdiff_add,
        ),
    ];
    for (label, name) in names {
        assert!(f.k.environment().contains(name), "{label} must be declared");
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, got {} names",
            footprint.len()
        );
    }
}
