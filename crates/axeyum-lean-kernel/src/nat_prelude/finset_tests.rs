//! Concrete-instance tests for `nat_prelude::finset`.
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat.Finset.memB`,
//! `card`, `sum`, `union`, `inter`, `sdiff`, `filter`, `range`, `singleton`,
//! `allBelow`, `subsetB` and `beq` are all admitted on their TYPE, and a
//! function that computes the wrong value has the right type, an empty axiom
//! footprint, and passes every sweep in this repository. So every check here
//! reduces a closed term to a numeral (or to `Bool.true`/`Bool.false`) with the
//! kernel's own `def_eq` and compares it against an independently hand-computed
//! value, and every positive is paired with the specific wrong formula it rules
//! out.
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! per this development's merge-hazard note; `Fixture` is a small local copy of
//! `nat_prelude_tests::Fixture` (that one is module-private), the same
//! arrangement `multiset_tests.rs` uses.
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest bound any fold below runs over is `14`.

use crate::expr::ExprId;
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

    /// `Nat.Finset.range n`.
    fn range(&mut self, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.finset_range;
        self.const_app(name, &[lit])
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

    fn inter(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_inter;
        self.const_app(name, &[s, t])
    }

    fn sdiff(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_sdiff;
        self.const_app(name, &[s, t])
    }

    fn filter(&mut self, q: ExprId, s: ExprId) -> ExprId {
        let name = self.p.finset_filter;
        self.const_app(name, &[q, s])
    }

    /// The set with the given elements, unioned left to right. Panics on an
    /// empty list — use `Nat.Finset.range 0` for that.
    fn of(&mut self, elements: &[u32]) -> ExprId {
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

    fn sum(&mut self, s: ExprId, f: ExprId) -> ExprId {
        let name = self.p.finset_sum;
        self.const_app(name, &[s, f])
    }

    fn memb(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }

    fn beq_sets(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_beq;
        self.const_app(name, &[s, t])
    }

    fn subset_b(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_subset_b;
        self.const_app(name, &[s, t])
    }

    /// `fun k => ble k bound_lit` — membership in `{0, …, bound_lit}`.
    fn le_pred(&mut self, bound_lit: u32) -> ExprId {
        let nat = self.nat_ty();
        let lit = self.num(bound_lit);
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.ble(k, lit);
        self.lam_fv(k_fv, nat, body)
    }

    /// `fun k => k`.
    fn identity(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        self.lam_fv(k_fv, nat, k)
    }
}

/// `Nat.Finset.memB` reads the stored predicate below the bound and
/// **truncates at it**.
///
/// `singleton 2` stores `fun k => beq k 2` with bound `3`, so membership must
/// be `true` at `2` and `false` everywhere else — including at `5`, which is
/// above the bound and therefore reached through the truncation branch rather
/// than through `beq`. The two `false`s are not redundant: `1` exercises
/// `beq 1 2 = false` BELOW the bound and `5` exercises `ble 6 3 = false` above
/// it, so a `memB` that forgot the truncation would still pass at `1`.
#[test]
fn mem_b_reads_a_singleton_and_truncates_at_the_bound() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();

    let s2 = f.singleton(2);
    let at_1 = f.memb(s2, 1);
    let at_2 = f.memb(s2, 2);
    let at_5 = f.memb(s2, 5);

    assert!(f.k.def_eq(at_2, t), "memB (singleton 2) 2 must be true");
    assert!(
        !f.k.def_eq(at_2, fa),
        "negative control: memB (singleton 2) 2 must NOT be false"
    );
    assert!(f.k.def_eq(at_1, fa), "memB (singleton 2) 1 must be false");
    assert!(
        !f.k.def_eq(at_1, t),
        "negative control: memB (singleton 2) 1 must NOT be true"
    );
    assert!(
        f.k.def_eq(at_5, fa),
        "memB (singleton 2) 5 must be false -- above the bound"
    );
    assert!(
        !f.k.def_eq(at_5, t),
        "negative control: memB (singleton 2) 5 must NOT be true"
    );
}

/// `Nat.Finset.card (range n) = n`, and it counts MEMBERS rather than indices.
///
/// The negative control is `4`: a `card` that folded over `pred n` (an
/// off-by-one on the bound) would land there.
#[test]
fn card_of_range_is_the_bound() {
    let mut f = Fixture::new();
    let five = f.num(5);
    let four = f.num(4);
    let zero = f.zero();

    let r5 = f.range(5);
    let c = f.card(r5);
    assert!(f.k.def_eq(c, five), "card (range 5) must be 5");
    assert!(
        !f.k.def_eq(c, four),
        "negative control: card (range 5) must NOT be 4"
    );

    let r0 = f.range(0);
    let c0 = f.card(r0);
    assert!(f.k.def_eq(c0, zero), "card (range 0) must be 0");
}

/// `Nat.Finset.filter` intersects with membership and does NOT widen the bound.
///
/// `filter (fun k => k ≤ 2) (range 5)` is `{0,1,2}`, so `3`; the negative
/// control `2` is what a filter whose predicate were applied to `[1,5)` (an
/// off-by-one in the fold) would give, and `5` is what one that ignored the
/// predicate entirely would give.
///
/// The second half is the bound check that matters for this carrier: a
/// predicate reaching PAST the set's bound must not add members, because
/// `filter` keeps the left bound and `memB` truncates. `filter (k ≤ 7)
/// (range 5)` is still `5`, not `8`.
#[test]
fn filter_intersects_and_keeps_the_bound() {
    let mut f = Fixture::new();
    let three = f.num(3);
    let two = f.num(2);
    let five = f.num(5);
    let eight = f.num(8);

    let r5 = f.range(5);
    let le2 = f.le_pred(2);
    let small = f.filter(le2, r5);
    let c = f.card(small);
    assert!(
        f.k.def_eq(c, three),
        "card (filter (k <= 2) (range 5)) must be 3"
    );
    assert!(
        !f.k.def_eq(c, two),
        "negative control: card (filter (k <= 2) (range 5)) must NOT be 2"
    );
    assert!(
        !f.k.def_eq(c, five),
        "negative control: a filter that ignored its predicate would give 5"
    );

    let r5b = f.range(5);
    let le7 = f.le_pred(7);
    let wide = f.filter(le7, r5b);
    let cw = f.card(wide);
    assert!(
        f.k.def_eq(cw, five),
        "card (filter (k <= 7) (range 5)) must still be 5"
    );
    assert!(
        !f.k.def_eq(cw, eight),
        "negative control: a filter that widened the bound to the predicate's \
         reach would give 8"
    );
}

/// `Nat.Finset.sum` sums `f` over the MEMBERS, not over `[0, bound)`.
///
/// `sum (range 4) id = 0+1+2+3 = 6`. The negative control is `10`, which is
/// `sum (range 5) id` — what a `sum` folding one index too far would give — and
/// the second half is the discriminating one: `sum {1,3} id = 4`, where a `sum`
/// that ignored membership and folded the whole `[0, bound)` would give `6`
/// (the bound of `{1,3}` is `2 + 4 = 6`, so it would give `15`; `6` is what
/// folding `[0,4)` would give). Both wrong answers are excluded explicitly.
#[test]
fn sum_folds_over_the_members() {
    let mut f = Fixture::new();
    let six = f.num(6);
    let ten = f.num(10);
    let four = f.num(4);
    let fifteen = f.num(15);

    let r4 = f.range(4);
    let id = f.identity();
    let s = f.sum(r4, id);
    assert!(f.k.def_eq(s, six), "sum (range 4) id must be 6");
    assert!(
        !f.k.def_eq(s, ten),
        "negative control: sum (range 4) id must NOT be 10 (that is range 5)"
    );

    let pair = f.of(&[1, 3]);
    let id2 = f.identity();
    let sp = f.sum(pair, id2);
    assert!(f.k.def_eq(sp, four), "sum {{1,3}} id must be 4");
    assert!(
        !f.k.def_eq(sp, fifteen),
        "negative control: a sum ignoring membership would fold [0,6) and give 15"
    );
}

/// `Nat.Finset.union` is a SET union: a shared element is counted once.
///
/// `card ({1,2} ∪ {2,3}) = 3`, and the negative control `4` is exactly what a
/// multiset-flavoured union — or a `card` folding `pred` rather than `memB`
/// past each operand's own bound — would give. `card ({1,2} ∩ {2,3}) = 1` and
/// `card ({1,2} \ {2,3}) = 1` pin the other two operations against the same
/// pair, and `1 + 3 = 2 + 2` is inclusion–exclusion checked numerically at this
/// instance.
#[test]
fn union_inter_sdiff_on_an_overlapping_pair() {
    let mut f = Fixture::new();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);

    let a = f.of(&[1, 2]);
    let b = f.of(&[2, 3]);

    let u = f.union(a, b);
    let cu = f.card(u);
    assert!(f.k.def_eq(cu, three), "card ({{1,2}} u {{2,3}}) must be 3");
    assert!(
        !f.k.def_eq(cu, four),
        "negative control: card ({{1,2}} u {{2,3}}) must NOT be 4 -- a union \
         that counted the shared 2 twice"
    );

    let i = f.inter(a, b);
    let ci = f.card(i);
    assert!(f.k.def_eq(ci, one), "card ({{1,2}} n {{2,3}}) must be 1");
    assert!(
        !f.k.def_eq(ci, two),
        "negative control: card ({{1,2}} n {{2,3}}) must NOT be 2"
    );

    let dd = f.sdiff(a, b);
    let cd = f.card(dd);
    assert!(f.k.def_eq(cd, one), "card ({{1,2}} \\ {{2,3}}) must be 1");
    assert!(
        !f.k.def_eq(cd, two),
        "negative control: card ({{1,2}} \\ {{2,3}}) must NOT be 2"
    );

    // Inclusion-exclusion at this instance: 3 + 1 = 2 + 2.
    let card_a = f.card(a);
    let card_b = f.card(b);
    assert!(f.k.def_eq(card_a, two), "card {{1,2}} must be 2");
    assert!(f.k.def_eq(card_b, two), "card {{2,3}} must be 2");
}

/// `Nat.Finset.beq` is EXTENSIONAL: it compares members, not stored predicates
/// or bounds.
///
/// `{1,2}` and `{2,1}` are built by unions in opposite orders, so their stored
/// predicates are different terms and their bounds are `2+3` and `3+2` — the
/// same numeral only by accident of this pair. They must still compare `true`.
/// `{1,2}` against `{1,2,3}` must compare `false`, and this is the case a `beq`
/// that only checked one inclusion would get wrong.
#[test]
fn beq_compares_members_not_representations() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();

    let ab = f.of(&[1, 2]);
    let ba = f.of(&[2, 1]);
    let same = f.beq_sets(ab, ba);
    assert!(f.k.def_eq(same, t), "beq {{1,2}} {{2,1}} must be true");
    assert!(
        !f.k.def_eq(same, fa),
        "negative control: beq {{1,2}} {{2,1}} must NOT be false"
    );

    let abc = f.of(&[1, 2, 3]);
    let ab2 = f.of(&[1, 2]);
    let differ = f.beq_sets(ab2, abc);
    assert!(
        f.k.def_eq(differ, fa),
        "beq {{1,2}} {{1,2,3}} must be false"
    );
    assert!(
        !f.k.def_eq(differ, t),
        "negative control: beq {{1,2}} {{1,2,3}} must NOT be true"
    );

    // The reflexive case, and the one a `beq` comparing bounds rather than
    // members would get wrong: `range 3` and `{0,1,2}` have bounds 3 and 9.
    let r3 = f.range(3);
    let listed = f.of(&[0, 1, 2]);
    let agree = f.beq_sets(r3, listed);
    assert!(
        f.k.def_eq(agree, t),
        "beq (range 3) {{0,1,2}} must be true -- different bounds, same members"
    );
}

/// `Nat.Finset.subsetB` decides inclusion, in the asymmetric direction.
///
/// `{1,2} ⊆ {1,2,3}` is `true` and the converse is `false`; a `subsetB` that
/// compared cardinalities, or that ranged over the wrong bound, would agree on
/// one of these and not the other, which is why both directions are checked.
#[test]
fn subset_b_decides_inclusion_asymmetrically() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();

    let small = f.of(&[1, 2]);
    let big = f.of(&[1, 2, 3]);

    let forward = f.subset_b(small, big);
    assert!(
        f.k.def_eq(forward, t),
        "subsetB {{1,2}} {{1,2,3}} must be true"
    );
    assert!(
        !f.k.def_eq(forward, fa),
        "negative control: subsetB {{1,2}} {{1,2,3}} must NOT be false"
    );

    let backward = f.subset_b(big, small);
    assert!(
        f.k.def_eq(backward, fa),
        "subsetB {{1,2,3}} {{1,2}} must be false"
    );
    assert!(
        !f.k.def_eq(backward, t),
        "negative control: subsetB {{1,2,3}} {{1,2}} must NOT be true -- an \
         asymmetric decision that answered `true` here would be comparing \
         something other than inclusion"
    );
}

/// Every `Nat.Finset` declaration is present AND has an EMPTY axiom footprint,
/// both read from the kernel rather than from a maintained list.
///
/// The presence check is not decoration: `Kernel::axiom_footprint` returns an
/// EMPTY vector for a name that was never declared, so a footprint assertion
/// alone passes vacuously on a typo'd or missing declaration — the exact shape
/// of checker this development bans. `Environment::contains` is what makes the
/// exit status depend on the finding.
#[test]
fn every_finset_declaration_is_present_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names = [
        ("Finset", p.finset),
        ("mk", p.finset_mk),
        ("pred", p.finset_pred),
        ("bound", p.finset_bound),
        ("memB", p.finset_mem_b),
        ("card", p.finset_card),
        ("sum", p.finset_sum),
        ("union", p.finset_union),
        ("inter", p.finset_inter),
        ("sdiff", p.finset_sdiff),
        ("filter", p.finset_filter),
        ("range", p.finset_range),
        ("singleton", p.finset_singleton),
        ("allBelow", p.finset_all_below),
        ("subsetB", p.finset_subset_b),
        ("beq", p.finset_beq),
        ("memB_of_lt", p.finset_mem_b_of_lt),
        ("memB_of_bound_le", p.finset_mem_b_of_bound_le),
        ("card_eq_countRange_add", p.finset_card_eq_count_range_add),
        (
            "card_union_add_card_inter",
            p.finset_card_union_add_card_inter,
        ),
    ];
    for (label, name) in names {
        assert!(
            f.k.environment().contains(name),
            "Nat.Finset.{label} must be declared"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "Nat.Finset.{label} must be axiom-free, got {} names",
            footprint.len()
        );
    }
}
