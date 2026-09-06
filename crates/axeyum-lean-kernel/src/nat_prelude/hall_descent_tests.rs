//! Concrete-instance tests for `nat_prelude::hall_descent` (ADR-1645).
//!
//! An empty axiom footprint is ALSO what a missing name returns, so every
//! footprint assertion below is preceded by an `Environment::contains`
//! assertion on the same name and a check of the declaration's KIND.
//!
//! The tests that matter are not the footprints, though. A descent measure is
//! the one place in Hall's induction where a `≤` would type-check everywhere
//! it is built and only fail where it is USED, so two of the tests below
//! APPLY each inequality at a closed instance, infer the resulting type with
//! the kernel's own `infer`, and assert it is the STRICT relation and is not
//! def-eq to the weak one. A rendered-string check would not separate them:
//! `Nat.lt a b` prints as itself and unfolds to `Nat.le (succ a) b`, so the
//! discrimination has to be done on types the kernel compares.
//!
//! Magnitudes are tiny on purpose (largest numeral formed: `3`); this prelude's
//! numerals are unary `Nat.succ` towers.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude};

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

    /// `Nat.Finset.range n` — every index below `n`.
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

    /// `Nat.Finset.empty`.
    fn empty(&mut self) -> ExprId {
        let name = self.p.finset_empty;
        self.k.const_(name, vec![])
    }

    /// `Nat.Finset.card s`.
    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    /// `Nat.Finset.bound s`.
    fn bound(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_bound;
        self.const_app(name, &[s])
    }

    /// `Nat.Finset.sdiff s t`.
    fn sdiff(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_sdiff;
        self.const_app(name, &[s, t])
    }

    /// `Nat.Finset.memB s i` at a numeral index.
    fn memb_of(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }

    /// `Nat.Finset.subsetFixed s t`.
    fn subset_fixed(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_subset_fixed;
        self.const_app(name, &[s, t])
    }

    /// `Eq.refl Bool Bool.true`, the proof every closed `= true` premise takes
    /// once its subject reduces.
    fn true_by_reduction(&mut self) -> ExprId {
        let tr = self.bool_true();
        self.bool_refl(tr)
    }

    /// `Nat.le_of_ble_eq_true a b (Eq.refl Bool true) : Le a b`, valid whenever
    /// `Nat.ble a b` reduces to `true`.
    fn le_by_reduction(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let proof = self.true_by_reduction();
        let name = self.p.le_of_ble_eq_true;
        self.const_app(name, &[a, b, proof])
    }
}

/// The four descent declarations are present, are checked `Theorem`s, and rest
/// on zero axioms.
#[test]
fn the_descent_shelf_is_admitted_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let theorems: [NameId; 4] = [
        p.finset_mem_b_of_subset_fixed_of_bound_le,
        p.finset_card_add_card_sdiff,
        p.finset_card_lt_card_of_subset_fixed,
        p.finset_card_sdiff_lt_card_of_subset_fixed,
    ];

    for name in theorems {
        let shown = k.display_name(name).to_string();
        assert!(
            k.environment().contains(name),
            "{shown} must be declared before its footprint means anything"
        );
        let decl = k.environment().get(name).expect("just checked");
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a checked Theorem"
        );
        println!("theorem {shown} : {}", k.render_lean(decl.ty()));
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{shown} must rest on zero axioms"
        );
    }
}

/// The counting identity is a real arithmetic fact at a concrete pair, and the
/// obvious wrong right-hand sides are ruled out.
///
/// `range 3 = {0, 1, 2}` and `singleton 1 = {1}`, so the split is `3 = 1 + 2`.
/// The negative controls are the two ways the summands could be confused —
/// counting the subset twice (`1 + 1`) and counting the whole set on the right
/// (`3 + 2`) — because `card_add_card_sdiff`'s statement is symmetric enough in
/// shape that an argument slip would still type-check.
#[test]
fn the_split_identity_is_three_equals_one_plus_two() {
    let mut f = Fixture::new();

    let s = f.range(3);
    let t = f.singleton(1);
    let rest = f.sdiff(s, t);

    let card_s = f.card(s);
    let card_t = f.card(t);
    let card_rest = f.card(rest);

    let three = f.num(3);
    let two = f.num(2);
    let one = f.num(1);
    assert!(f.k.def_eq(card_s, three), "`card (range 3)` must be 3");
    assert!(f.k.def_eq(card_t, one), "`card (singleton 1)` must be 1");
    assert!(
        f.k.def_eq(card_rest, two),
        "`card (range 3 \\ singleton 1)` must be 2"
    );

    let split = f.add(card_t, card_rest);
    assert!(f.k.def_eq(card_s, split), "the split identity must compute");

    let double_subset = f.add(card_t, card_t);
    assert!(
        !f.k.def_eq(card_s, double_subset),
        "negative control: `card t + card t` is 2, not 3 -- the second summand \
         must be the COMPLEMENT's count"
    );
    let whole_on_right = f.add(card_s, card_rest);
    assert!(
        !f.k.def_eq(card_s, whole_on_right),
        "negative control: `card s + card (s \\ t)` is 5, not 3 -- the first \
         summand must be the SUBSET's count"
    );
}

/// `card_lt_card_of_subsetFixed` applied at a closed instance has the STRICT
/// type, and that type is not the weak one.
///
/// This is the test that dies when `<` is weakened to `≤`. It cannot be done on
/// the rendered string: `Nat.lt a b` unfolds to `Nat.le (succ a) b`, so the
/// separation has to be a `def_eq` between two types the kernel builds itself.
/// At `s = range 3`, `t = singleton 1`: `card t = 1`, `card s = 3`, so the
/// strict conclusion is `Lt 1 3` and the weak one would be `Le 1 3` — both true
/// statements, and NOT definitionally the same proposition.
#[test]
fn the_subset_measure_conclusion_is_strict() {
    let mut f = Fixture::new();

    let s = f.range(3);
    let t = f.singleton(1);
    let rest = f.sdiff(s, t);

    let bt = f.bound(t);
    let bs = f.bound(s);
    let hb = f.le_by_reduction(bt, bs);
    let hsf = f.true_by_reduction();

    let zero = f.zero();
    let card_rest = f.card(rest);
    let one = f.num(1);
    let hpos = f.le_by_reduction(one, card_rest);

    let name = f.p.finset_card_lt_card_of_subset_fixed;
    let applied = f.const_app(name, &[s, t, hb, hsf, hpos]);
    let inferred =
        f.k.infer(applied)
            .expect("the descent measure must apply at this instance");

    let three = f.num(3);
    let strict = f.lt(one, three);
    let weak = f.le(one, three);
    assert!(
        f.k.def_eq(inferred, strict),
        "the conclusion must be `Lt (card t) (card s)` = `Lt 1 3`; got {}",
        f.k.render_lean(inferred)
    );
    assert!(
        !f.k.def_eq(strict, weak),
        "control: `Lt 1 3` and `Le 1 3` must be distinguishable propositions, \
         or this test could not detect a weakened measure"
    );
    assert!(
        !f.k.def_eq(inferred, weak),
        "the conclusion must NOT be the weak `Le 1 3` -- a `≤` measure makes \
         the strong induction unfoundable; got {}",
        f.k.render_lean(inferred)
    );

    // The positivity premise is not decoration: at `t = s` it fails, and that
    // is precisely the instance where the strict conclusion is false.
    let self_rest = f.sdiff(s, s);
    let card_self_rest = f.card(self_rest);
    assert!(
        f.k.def_eq(card_self_rest, zero),
        "`card (s \\ s)` must be 0, so the positivity premise is unavailable \
         exactly when `card t < card s` is false"
    );
}

/// `card_sdiff_lt_card_of_subsetFixed` applied at a closed instance has the
/// STRICT type, and that type is not the weak one.
///
/// The same discrimination on the other inequality. At `s = range 3`,
/// `t = singleton 1`: `card (s \ t) = 2`, `card s = 3`, so the strict
/// conclusion is `Lt 2 3` and the weak one would be `Le 2 3`.
#[test]
fn the_complement_measure_conclusion_is_strict() {
    let mut f = Fixture::new();

    let s = f.range(3);
    let t = f.singleton(1);

    let bt = f.bound(t);
    let bs = f.bound(s);
    let hb = f.le_by_reduction(bt, bs);
    let hsf = f.true_by_reduction();

    let card_t = f.card(t);
    let one = f.num(1);
    let hpos = f.le_by_reduction(one, card_t);

    let name = f.p.finset_card_sdiff_lt_card_of_subset_fixed;
    let applied = f.const_app(name, &[s, t, hb, hsf, hpos]);
    let inferred =
        f.k.infer(applied)
            .expect("the complement measure must apply at this instance");

    let two = f.num(2);
    let three = f.num(3);
    let strict = f.lt(two, three);
    let weak = f.le(two, three);
    assert!(
        f.k.def_eq(inferred, strict),
        "the conclusion must be `Lt (card (s \\ t)) (card s)` = `Lt 2 3`; got {}",
        f.k.render_lean(inferred)
    );
    assert!(
        !f.k.def_eq(strict, weak),
        "control: `Lt 2 3` and `Le 2 3` must be distinguishable propositions"
    );
    assert!(
        !f.k.def_eq(inferred, weak),
        "the conclusion must NOT be the weak `Le 2 3`; got {}",
        f.k.render_lean(inferred)
    );

    // The positivity premise is not decoration here either: at `t = empty` it
    // fails, and `card (s \ empty) = card s` is exactly the non-decrease.
    let e = f.empty();
    let card_e = f.card(e);
    let zero = f.zero();
    assert!(f.k.def_eq(card_e, zero), "`card empty` must be 0");
    let untouched = f.sdiff(s, e);
    let card_untouched = f.card(untouched);
    let card_s = f.card(s);
    assert!(
        f.k.def_eq(card_untouched, card_s),
        "`card (s \\ empty)` must equal `card s`, so a measure without the \
         positivity premise would be false"
    );
}

/// `Le (bound t) (bound s)` on the bridge lemma is load-bearing, and ADR-1644's
/// own counterexample is what shows it.
///
/// `subsetFixed empty (singleton 0)` is `true` — `bound empty` is `0`, so the
/// loop answers no index at all — while `0` IS a member of `singleton 0` and is
/// NOT a member of `empty`. So `memB_of_subsetFixed_of_bound_le` would be FALSE
/// without the bound hypothesis, and here `bound (singleton 0)` is not `≤`
/// `bound empty`. This test asserts all three facts, so a lane that drops the
/// hypothesis as "bookkeeping" gets a failure rather than a rejection it has to
/// interpret.
#[test]
fn the_bound_hypothesis_is_what_makes_the_bridge_true() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let e = f.empty();
    let t = f.singleton(0);

    let decided = f.subset_fixed(e, t);
    assert!(
        f.k.def_eq(decided, tr),
        "`subsetFixed empty (singleton 0)` must be `true` -- the loop runs to \
         `bound empty` = 0 and answers no index"
    );

    let in_t = f.memb_of(t, 0);
    assert!(f.k.def_eq(in_t, tr), "0 must be a member of `singleton 0`");
    let in_e = f.memb_of(e, 0);
    assert!(f.k.def_eq(in_e, fa), "0 must NOT be a member of `empty`");

    // ...and the bound hypothesis is exactly what this pair violates.
    let bt = f.bound(t);
    let be = f.bound(e);
    let one = f.num(1);
    let zero = f.zero();
    assert!(
        f.k.def_eq(bt, one),
        "`bound (singleton 0)` must be 1, not 0"
    );
    assert!(f.k.def_eq(be, zero), "`bound empty` must be 0");
    let ble = f.ble(bt, be);
    assert!(
        f.k.def_eq(ble, fa),
        "`ble (bound (singleton 0)) (bound empty)` must be `false` -- the \
         hypothesis that fails is the one that keeps the bridge true"
    );
}
