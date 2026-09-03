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
        ("allBelow_of_all_true", p.finset_all_below_of_all_true),
        ("allBelow_true_at", p.finset_all_below_true_at),
        ("card_le_of_subsetB", p.finset_card_le_of_subset_b),
        ("sum_eq_sumRangeIf_add", p.finset_sum_eq_sum_range_if_add),
        ("sum_union_disjoint", p.finset_sum_union_disjoint),
        ("sum_congr_of_beq", p.finset_sum_congr_of_beq),
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

/// `Nat.Finset.card_union_add_card_inter` instantiates at a CONCRETE
/// overlapping pair and states the arithmetic identity that pair satisfies.
///
/// Instantiating concretely is not redundant with the declaration: the theorem
/// was admitted against free `s`/`t`, which is the symbolic half, and a
/// concrete instance is what catches a statement whose two sides are the same
/// term for a reason other than the one intended. The negative control is the
/// SUBTRACTIVE form's numerals — `3` against `4` — which this additive
/// statement deliberately does not claim.
#[test]
fn inclusion_exclusion_instantiates_concretely_and_symbolically() {
    let mut f = Fixture::new();
    let name = f.p.finset_card_union_add_card_inter;

    let a = f.of(&[1, 2]);
    let b = f.of(&[2, 3]);
    let at_pair = f.const_app(name, &[a, b]);
    let ty =
        f.k.infer(at_pair)
            .expect("card_union_add_card_inter must instantiate at {1,2}, {2,3}");

    // Both sides are `4` at this pair: 3 + 1 on the left, 2 + 2 on the right.
    let four = f.num(4);
    let three = f.num(3);
    let expected = f.eq(four, four);
    assert!(
        f.k.def_eq(ty, expected),
        "at ({{1,2}}, {{2,3}}) the identity must reduce to 4 = 4, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.eq(three, four);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: the statement must NOT reduce to 3 = 4"
    );

    // The symbolic half: the same constant applied to two genuinely free
    // set-valued variables, closed back into a lambda so `infer` sees it.
    // Nothing here reduces to a numeral, which is the point -- a concrete
    // instance can hide a defeq-shaped gap that full evaluation papers over.
    let fs = f.k.const_(f.p.finset, vec![]);
    let s_fv = f.fresh_fvar();
    let s = f.k.fvar(s_fv);
    let t_fv = f.fresh_fvar();
    let t = f.k.fvar(t_fv);
    let at_free = f.const_app(name, &[s, t]);
    let closed = {
        let inner = f.lam_fv(t_fv, fs, at_free);
        f.lam_fv(s_fv, fs, inner)
    };
    assert!(
        f.k.infer(closed).is_ok(),
        "card_union_add_card_inter must infer at free set variables"
    );
}

/// `Nat.Finset.card_le_of_subsetB` instantiates at a CONCRETE inclusion whose
/// `subsetB` witness is `Eq.refl true` — the decision computes, so the
/// hypothesis costs nothing at a closed instance — and states `2 ≤ 3`.
///
/// The negative control is the reversed inequality: a `card_le_of_subsetB`
/// stated with its two `card`s swapped would type-check identically against
/// free variables, and only a concrete instance separates them.
#[test]
fn card_le_of_subset_b_instantiates_concretely_and_symbolically() {
    let mut f = Fixture::new();
    let name = f.p.finset_card_le_of_subset_b;

    let small = f.of(&[1, 2]);
    let big = f.of(&[1, 2, 3]);
    let witness = {
        let t = f.bool_true();
        f.bool_refl(t)
    };
    let applied = f.const_app(name, &[small, big, witness]);
    let ty =
        f.k.infer(applied)
            .expect("card_le_of_subsetB must instantiate where subsetB computes to true");

    let two = f.num(2);
    let three = f.num(3);
    let expected = f.le(two, three);
    assert!(
        f.k.def_eq(ty, expected),
        "at ({{1,2}} <= {{1,2,3}}) the conclusion must be 2 <= 3, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.le(three, two);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: the conclusion must NOT be 3 <= 2 -- a statement \
         with the two cards swapped is indistinguishable symbolically"
    );

    // Symbolic: two free sets, closed back into a lambda. The residual type is
    // the implication `subsetB s t = true -> card s <= card t` at genuinely
    // free arguments, where no `subsetB` decision computes.
    let fs = f.k.const_(f.p.finset, vec![]);
    let s_fv = f.fresh_fvar();
    let s = f.k.fvar(s_fv);
    let t_fv = f.fresh_fvar();
    let t = f.k.fvar(t_fv);
    let at_free = f.const_app(name, &[s, t]);
    let closed = {
        let inner = f.lam_fv(t_fv, fs, at_free);
        f.lam_fv(s_fv, fs, inner)
    };
    assert!(
        f.k.infer(closed).is_ok(),
        "card_le_of_subsetB must infer at free set variables"
    );
}

/// The two `allBelow` directions are genuinely different theorems, and the
/// REFLECTION one is the direction `Nat.Multiset.eqBelow` does not carry.
///
/// `allBelow (fun k => ble k 4) 3` computes to `true` and
/// `allBelow (fun k => ble k 1) 3` to `false` — the second is the case a loop
/// that ignored its predicate, or that stopped one index early, would get
/// wrong (`ble 2 1 = false` is the only index that separates them).
#[test]
fn all_below_computes_and_stops_at_the_bound() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();
    let name = f.p.finset_all_below;

    let three = f.num(3);
    let wide = f.le_pred(4);
    let all = f.const_app(name, &[wide, three]);
    assert!(
        f.k.def_eq(all, t),
        "allBelow (k <= 4) 3 must be true -- every index below 3 satisfies it"
    );
    assert!(
        !f.k.def_eq(all, fa),
        "negative control: allBelow (k <= 4) 3 must NOT be false"
    );

    let three_b = f.num(3);
    let narrow = f.le_pred(1);
    let some = f.const_app(name, &[narrow, three_b]);
    assert!(
        f.k.def_eq(some, fa),
        "allBelow (k <= 1) 3 must be false -- index 2 fails"
    );
    assert!(
        !f.k.def_eq(some, t),
        "negative control: allBelow (k <= 1) 3 must NOT be true; a loop that \
         stopped at index 1 would answer true here"
    );

    // And it does not read past its bound: at bound 2 the failing index 2 is
    // out of range, so the same narrow predicate answers `true`.
    let two = f.num(2);
    let narrow2 = f.le_pred(1);
    let stopped = f.const_app(name, &[narrow2, two]);
    assert!(
        f.k.def_eq(stopped, t),
        "allBelow (k <= 1) 2 must be true -- the failing index is out of range"
    );
}

/// `Nat.Finset.sum_union_disjoint`, instantiated, and its hypothesis shown to
/// be LOAD-BEARING.
///
/// The hypothesis `∀ i, setInter (memB s) (memB t) i = false` is `Eq.refl
/// false` exactly when one side's bound is `0` — at a symbolic index the guard
/// `ble (succ i) (bound s)` is stuck for any positive bound, so a non-degenerate
/// witness is a real case analysis and not something a test can spell in one
/// line. So this checks three things rather than one:
///
/// 1. the theorem INSTANTIATED at `s = range 0`, where the witness does reduce,
///    and its conclusion inferred and compared against `5 = 0 + 5`;
/// 2. the statement's CONTENT at a non-degenerate disjoint pair, evaluated
///    directly: `sum ({1} u {2}) id` and `sum {1} id + sum {2} id` are both `3`;
/// 3. the same two quantities at an OVERLAPPING pair, where they are `6` and
///    `8` — so the disjointness hypothesis is not decoration, and a
///    `sum_union_disjoint` stated without it would be false.
#[test]
fn sum_union_disjoint_instantiates_and_its_hypothesis_is_load_bearing() {
    let mut f = Fixture::new();
    let name = f.p.finset_sum_union_disjoint;

    // (1) the instantiation whose witness reduces.
    let empty = f.range(0);
    let t = f.of(&[2, 3]);
    let id = f.identity();
    let witness = {
        let nat = f.nat_ty();
        let i_fv = f.fresh_fvar();
        let fa = f.bool_false();
        let body = f.bool_refl(fa);
        f.lam_fv(i_fv, nat, body)
    };
    let applied = f.const_app(name, &[empty, t, id, witness]);
    let ty =
        f.k.infer(applied)
            .expect("sum_union_disjoint must instantiate at an empty left set");
    let five = f.num(5);
    let zero = f.zero();
    let expected = {
        let rhs = f.add(zero, five);
        f.eq(five, rhs)
    };
    assert!(
        f.k.def_eq(ty, expected),
        "at (range 0, {{2,3}}) the identity must state 5 = 0 + 5, got {}",
        f.k.render_lean(ty)
    );
    let six = f.num(6);
    let wrong = {
        let rhs = f.add(zero, five);
        f.eq(six, rhs)
    };
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: it must NOT state 6 = 0 + 5"
    );

    // (2) the content at a non-degenerate DISJOINT pair.
    let a = f.of(&[1]);
    let b = f.of(&[2]);
    let joined = f.union(a, b);
    let id2 = f.identity();
    let lhs = f.sum(joined, id2);
    let id3 = f.identity();
    let sa = f.sum(a, id3);
    let id4 = f.identity();
    let sb = f.sum(b, id4);
    let rhs = f.add(sa, sb);
    let three = f.num(3);
    assert!(f.k.def_eq(lhs, three), "sum ({{1}} u {{2}}) id must be 3");
    assert!(
        f.k.def_eq(rhs, three),
        "sum {{1}} id + sum {{2}} id must be 3"
    );

    // (3) the same two quantities at an OVERLAPPING pair, where they DIFFER.
    let c = f.of(&[1, 2]);
    let dset = f.of(&[2, 3]);
    let overlapped = f.union(c, dset);
    let id5 = f.identity();
    let lhs2 = f.sum(overlapped, id5);
    let id6 = f.identity();
    let sc = f.sum(c, id6);
    let id7 = f.identity();
    let sd = f.sum(dset, id7);
    let rhs2 = f.add(sc, sd);
    let six2 = f.num(6);
    let eight = f.num(8);
    assert!(
        f.k.def_eq(lhs2, six2),
        "sum ({{1,2}} u {{2,3}}) id must be 6 -- the shared 2 counted once"
    );
    assert!(
        f.k.def_eq(rhs2, eight),
        "sum {{1,2}} id + sum {{2,3}} id must be 8 -- the shared 2 counted twice"
    );
    assert!(
        !f.k.def_eq(lhs2, rhs2),
        "the disjointness hypothesis is LOAD-BEARING: 6 != 8 at an overlapping \
         pair, so `sum_union_disjoint` without it would be false"
    );

    // Symbolic: free sets and a free summand, closed back into lambdas.
    let fs = f.k.const_(f.p.finset, vec![]);
    let nat = f.nat_ty();
    let fn_ty = f.arrow(nat, nat);
    let s_fv = f.fresh_fvar();
    let s = f.k.fvar(s_fv);
    let t_fv = f.fresh_fvar();
    let tv = f.k.fvar(t_fv);
    let g_fv = f.fresh_fvar();
    let g = f.k.fvar(g_fv);
    let at_free = f.const_app(name, &[s, tv, g]);
    let closed = {
        let inner = f.lam_fv(g_fv, fn_ty, at_free);
        let mid = f.lam_fv(t_fv, fs, inner);
        f.lam_fv(s_fv, fs, mid)
    };
    assert!(
        f.k.infer(closed).is_ok(),
        "sum_union_disjoint must infer at free set and summand variables"
    );
}

/// `Nat.Finset.sum_congr_of_beq`, instantiated where the `beq` decision
/// computes, and its hypothesis shown to be LOAD-BEARING.
///
/// `range 3` and `{0,1,2}` are the same set with different REPRESENTATIONS: the
/// bounds are `3` and `6` and the stored predicates are unrelated terms, so
/// `sum` folds over ranges of different lengths on the two sides and the two
/// sums are equal for a reason, not by being the same term. `beq` decides them
/// equal, so the witness is `Eq.refl true`.
///
/// The load-bearing check is `range 3` against `range 4`, where `beq` is `false`
/// and the two sums are `3` and `6`: a `sum_congr` stated without the hypothesis
/// would be false there.
#[test]
fn sum_congr_of_beq_instantiates_and_its_hypothesis_is_load_bearing() {
    let mut f = Fixture::new();
    let name = f.p.finset_sum_congr_of_beq;

    // The two representations really are different: bounds 3 and 9.
    let r3 = f.range(3);
    let listed = f.of(&[0, 1, 2]);
    let bound_name = f.p.finset_bound;
    let b1 = f.const_app(bound_name, &[r3]);
    let b2 = f.const_app(bound_name, &[listed]);
    let three = f.num(3);
    // `{0,1,2}` is `union (union (singleton 0) (singleton 1)) (singleton 2)`,
    // and `union` takes the SUM of its operands' bounds: (1 + 2) + 3 = 6.
    let six_bound = f.num(6);
    assert!(f.k.def_eq(b1, three), "bound (range 3) must be 3");
    assert!(f.k.def_eq(b2, six_bound), "bound {{0,1,2}} must be 6");
    assert!(
        !f.k.def_eq(b1, b2),
        "the two representations must have DIFFERENT bounds, or this instance \
         checks nothing"
    );

    let id = f.identity();
    let witness = {
        let t = f.bool_true();
        f.bool_refl(t)
    };
    let applied = f.const_app(name, &[r3, listed, id, witness]);
    let ty =
        f.k.infer(applied)
            .expect("sum_congr_of_beq must instantiate where beq computes to true");
    let three_a = f.num(3);
    let three_b = f.num(3);
    let expected = f.eq(three_a, three_b);
    assert!(
        f.k.def_eq(ty, expected),
        "at (range 3, {{0,1,2}}) with id the conclusion must be 3 = 3, got {}",
        f.k.render_lean(ty)
    );
    let six = f.num(6);
    let wrong = {
        let a = f.num(3);
        f.eq(a, six)
    };
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: the conclusion must NOT be 3 = 6"
    );

    // The hypothesis is load-bearing: at a pair `beq` rejects, the sums differ.
    let r3b = f.range(3);
    let r4 = f.range(4);
    let beq_name = f.p.finset_beq;
    let decided = f.const_app(beq_name, &[r3b, r4]);
    let fa = f.bool_false();
    assert!(
        f.k.def_eq(decided, fa),
        "beq (range 3) (range 4) must be false"
    );
    let id2 = f.identity();
    let s3 = f.sum(r3b, id2);
    let id3 = f.identity();
    let s4 = f.sum(r4, id3);
    let three_c = f.num(3);
    let six_b = f.num(6);
    assert!(f.k.def_eq(s3, three_c), "sum (range 3) id must be 3");
    assert!(f.k.def_eq(s4, six_b), "sum (range 4) id must be 6");
    assert!(
        !f.k.def_eq(s3, s4),
        "the `beq` hypothesis is LOAD-BEARING: 3 != 6 at a rejected pair"
    );

    // Symbolic: free sets and a free summand.
    let fs = f.k.const_(f.p.finset, vec![]);
    let nat = f.nat_ty();
    let fn_ty = f.arrow(nat, nat);
    let s_fv = f.fresh_fvar();
    let s = f.k.fvar(s_fv);
    let t_fv = f.fresh_fvar();
    let tv = f.k.fvar(t_fv);
    let g_fv = f.fresh_fvar();
    let g = f.k.fvar(g_fv);
    let at_free = f.const_app(name, &[s, tv, g]);
    let closed = {
        let inner = f.lam_fv(g_fv, fn_ty, at_free);
        let mid = f.lam_fv(t_fv, fs, inner);
        f.lam_fv(s_fv, fs, mid)
    };
    assert!(
        f.k.infer(closed).is_ok(),
        "sum_congr_of_beq must infer at free set and summand variables"
    );
}
