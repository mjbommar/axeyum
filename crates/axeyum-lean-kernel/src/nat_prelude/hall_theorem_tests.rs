//! Concrete-instance tests for `nat_prelude::hall_theorem` (ADR-1644).
//!
//! **The kernel cannot tell a `Definition` is wrong.**
//! `Nat.Finset.subsetFixed` is admitted on its type, `Finset → Finset → Bool`,
//! and so is `Nat.Finset.subsetB`, and so is `fun _ _ => true`. So the checks
//! below reduce closed terms with the kernel's own `def_eq` and compare against
//! independently hand-computed values, and every positive is paired with the
//! specific wrong definition it rules out — including the two the shape invites:
//! the ARGUMENT ORDER (`subsetFixed s t` decides `t ⊆ s`, not `s ⊆ t`) and the
//! LOOP BOUND (`bound s`, not `bound t`).
//!
//! The theorems get a different treatment: an empty axiom footprint is ALSO
//! what a missing name returns, so each footprint assertion is preceded by an
//! `Environment::contains` assertion on the same name.
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

    /// `Nat.Finset.singleton a`.
    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.finset_singleton;
        self.const_app(name, &[lit])
    }

    /// `Nat.Finset.range n` — every index below `n`.
    fn range(&mut self, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.finset_range;
        self.const_app(name, &[lit])
    }

    /// `Nat.Finset.empty`.
    fn empty(&mut self) -> ExprId {
        let name = self.p.finset_empty;
        self.k.const_(name, vec![])
    }

    /// `Nat.Finset.subsetFixed s t`.
    fn subset_fixed(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_subset_fixed;
        self.const_app(name, &[s, t])
    }

    /// `Nat.Finset.subsetB s t` — the EXISTING decision, kept as the control.
    fn subset_b(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_subset_b;
        self.const_app(name, &[s, t])
    }

    /// `Nat.Finset.allBelow f n`.
    fn all_below(&mut self, f: ExprId, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.finset_all_below;
        self.const_app(name, &[f, lit])
    }

    /// `Nat.Finset.union s t`.
    fn union(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_union;
        self.const_app(name, &[s, t])
    }

    /// `Nat.Finset.card s`.
    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    /// `Nat.Hall.unionOver nb t`.
    fn union_over(&mut self, nb: ExprId, t: ExprId) -> ExprId {
        let name = self.p.hall_union_over;
        self.const_app(name, &[nb, t])
    }

    /// `Nat.Finset.memB s i` at a numeral index.
    fn memb_of(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }
}

/// `subsetFixed` computes the inclusion it claims to, at four hand-checked
/// pairs, and is NOT its own argument-swap.
///
/// The four instances are chosen so no single wrong definition survives them:
///
/// | `s`             | `t`           | verdict | why it discriminates                    |
/// |-----------------|---------------|---------|-----------------------------------------|
/// | `range 3`       | `singleton 1` | true    | a proper nonempty inclusion             |
/// | `singleton 1`   | `range 3`     | false   | the SWAP of the row above                |
/// | `range 3`       | `empty`       | true    | the empty set is included in everything |
/// | `singleton 2`   | `singleton 0` | false   | two sets neither of which includes the  |
/// |                 |               |         | other, with the witness inside the loop |
///
/// Rows 1 and 2 together are what rules out `fun s t => subsetFixed t s`. The
/// four together rule out both constant functions, which no two of them do on
/// their own (a constant `true` passes rows 1 and 3, a constant `false` passes
/// 2 and 4).
///
/// Row 4 is `singleton 2` and not `empty` on purpose. `subsetFixed empty
/// (singleton 0)` is **true**, not false: `bound empty` is `0`, so the loop
/// answers no index at all. That is the correct value for this definition and
/// [`the_loop_bound_comes_from_the_first_argument`] is where it is asserted and
/// used; putting it here as a `false` row would have been a wrong hand
/// computation dressed as a control.
#[test]
fn subset_fixed_decides_inclusion_and_is_not_its_own_swap() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let r3 = f.range(3);
    let s1 = f.singleton(1);
    let e = f.empty();
    let s0 = f.singleton(0);

    // `singleton 1 ⊆ range 3` -- true.
    let a = f.subset_fixed(r3, s1);
    assert!(
        f.k.def_eq(a, tr),
        "subsetFixed (range 3) (singleton 1) must be true: 1 < 3"
    );
    assert!(
        !f.k.def_eq(a, fa),
        "negative control: subsetFixed (range 3) (singleton 1) must NOT be false"
    );

    // `range 3 ⊆ singleton 1` -- false (0 and 2 are missing). This is the
    // SWAP of the line above and it must disagree, or the argument order is
    // not being tested at all.
    let b = f.subset_fixed(s1, r3);
    assert!(
        f.k.def_eq(b, fa),
        "subsetFixed (singleton 1) (range 3) must be false: 0 is in range 3 \
         and not in singleton 1"
    );
    assert!(
        !f.k.def_eq(b, tr),
        "negative control: the swapped pair must NOT also be true -- if it \
         were, `subsetFixed` would be symmetric and could not be an inclusion"
    );

    // `empty ⊆ range 3` -- true.
    let c = f.subset_fixed(r3, e);
    assert!(
        f.k.def_eq(c, tr),
        "subsetFixed (range 3) empty must be true"
    );

    // `singleton 0 ⊆ singleton 2` -- false: index 0 is in `singleton 0`, is
    // below `bound (singleton 2) = 3`, and is not in `singleton 2`.
    let s2 = f.singleton(2);
    let d = f.subset_fixed(s2, s0);
    assert!(
        f.k.def_eq(d, fa),
        "subsetFixed (singleton 2) (singleton 0) must be false"
    );
    assert!(
        !f.k.def_eq(d, tr),
        "negative control: `singleton 0` is not included in `singleton 2`, and \
         the loop over `bound (singleton 2) = 3` reaches the witness"
    );
}

/// The loop bound really is `bound s`, and this is the pair that shows it.
///
/// `subsetFixed` is a BOUNDED decision, so it is not extensional inclusion and
/// this test is where the difference is recorded rather than papered over:
///
/// ```text
/// subsetFixed empty         (singleton 0) = true   -- bound empty = 0: the loop
///                                                     answers no index at all
/// subsetFixed (singleton 2) (singleton 0) = false  -- bound (singleton 2) = 3:
///                                                     the loop reaches index 0
/// ```
///
/// Extensionally `singleton 0` is a subset of neither, so a definition that
/// decided extensional inclusion would return `false` for both. This one does
/// not, and that is correct for what it is: the first line is vacuous because
/// the loop is empty.
///
/// The pair is the DISCRIMINATOR for the loop bound because the two share their
/// `t`. `bound (singleton 0)` is `1` in both, so a `subsetFixed` that looped to
/// `bound t` would give them the same verdict; only a loop over `bound s`
/// separates them. Every caller in the Hall induction supplies `Lt i (bound s)`
/// through `mem_of_subsetFixed`, which is where the boundedness is paid for.
#[test]
fn the_loop_bound_comes_from_the_first_argument() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let e = f.empty();
    let s0 = f.singleton(0);
    let s2 = f.singleton(2);

    // `bound empty = 0`: the loop is empty, so the verdict is vacuously
    // `true` even though `singleton 0` is not a subset of `empty` in the
    // extensional sense.
    let vacuous = f.subset_fixed(e, s0);

    // `bound (singleton 2) = 3`: the loop reaches index 0, where
    // `memB (singleton 0) 0 = true` and `memB (singleton 2) 0 = false`, so the
    // verdict is `false`.
    let answered = f.subset_fixed(s2, s0);
    assert!(
        f.k.def_eq(answered, fa),
        "subsetFixed (singleton 2) (singleton 0) must be false: index 0 is in \
         `singleton 0`, is below `bound (singleton 2) = 3`, and is not in \
         `singleton 2`"
    );

    // THE DISCRIMINATOR. Same `t` in both, so `bound t` is `1` in both; the
    // verdicts differ, so the loop bound cannot be `bound t`.
    assert!(
        !f.k.def_eq(vacuous, answered),
        "negative control: the two verdicts must DIFFER. They share `t`, so a \
         `subsetFixed` that looped to `bound t` would answer both the same \
         way; only a loop over `bound s` separates them"
    );

    // ...and the vacuous one is the `true` side, which is what "loop to
    // `bound s`" predicts and "loop to `bound t`" does not.
    assert!(
        f.k.def_eq(vacuous, tr),
        "subsetFixed empty (singleton 0) must be true: `bound empty` is 0, so \
         the loop answers no index"
    );
}

/// `subsetFixed` is NOT `subsetB`, and is not `subsetB` with its arguments
/// swapped either.
///
/// Both are `Finset → Finset → Bool` and both loop `allBelow` over an
/// inclusion guard, so nothing in the type or the shape separates them; only a
/// value does. `subsetB s t` decides `s ⊆ t` over `bound s`, and
/// `subsetFixed s t` decides `t ⊆ s` over `bound s` — the guard is transposed
/// but the loop bound is not, which is precisely the combination neither
/// `subsetB s t` nor `subsetB t s` has.
#[test]
fn subset_fixed_is_neither_orientation_of_subset_b() {
    let mut f = Fixture::new();

    let r3 = f.range(3);
    let s1 = f.singleton(1);

    let fixed = f.subset_fixed(s1, r3);
    let plain = f.subset_b(s1, r3);
    let swapped = f.subset_b(r3, s1);

    // `subsetFixed (singleton 1) (range 3)` is `false` (0 ∈ range 3, 0 ∉ s1,
    // and 0 < bound (singleton 1) = 2).
    // `subsetB (singleton 1) (range 3)` is `true` (1 ∈ range 3).
    assert!(
        !f.k.def_eq(fixed, plain),
        "`subsetFixed s t` must not be `subsetB s t`: the guard is transposed"
    );
    // `subsetB (range 3) (singleton 1)` loops to `bound (range 3) = 3` and is
    // `false`; it agrees with `subsetFixed` here by VALUE, so the separating
    // instance is a different pair -- see below.
    let _ = swapped;

    // The pair that separates `subsetFixed s t` from `subsetB t s`: they use
    // different loop bounds, so a `t` wider than `s` is answered by one and
    // not the other.
    let e = f.empty();
    let s0 = f.singleton(0);
    let fixed_e = f.subset_fixed(e, s0); // loops to bound empty = 0  -> true
    let swapped_e = f.subset_b(s0, e); // loops to bound (singleton 0) = 1 -> false
    assert!(
        !f.k.def_eq(fixed_e, swapped_e),
        "`subsetFixed s t` must not be `subsetB t s`: they loop over `bound s` \
         and `bound t` respectively, and at (s, t) = (empty, singleton 0) \
         those bounds are 0 and 1"
    );
}

/// `allBelow_congr`'s statement is not vacuous: the loop really does depend on
/// its predicate, so an `allBelow` that ignored `f` would make the theorem
/// content-free.
///
/// Two closed predicates over the same bound with different verdicts. Without
/// this, `allBelow_congr` would be satisfied by `fun _ n => true`.
#[test]
fn all_below_depends_on_its_predicate() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let anon = f.anon_name();

    // `fun _ => true` and `fun _ => false`.
    let always_true = {
        let t = f.bool_true();
        f.k.lam(anon, nat, t, crate::BinderInfo::Default)
    };
    let always_false = {
        let fa_inner = f.bool_false();
        f.k.lam(anon, nat, fa_inner, crate::BinderInfo::Default)
    };
    let _ = bool_ty;

    let yes = f.all_below(always_true, 3);
    let no = f.all_below(always_false, 3);
    assert!(
        f.k.def_eq(yes, tr),
        "allBelow (fun _ => true) 3 must be true"
    );
    assert!(
        f.k.def_eq(no, fa),
        "allBelow (fun _ => false) 3 must be false"
    );
    assert!(
        !f.k.def_eq(yes, no),
        "negative control: the two loops must differ, or `allBelow_congr` is \
         a statement about a constant"
    );

    // ...and at bound `0` they agree, which is the base case `allBelow_congr`
    // discharges by `rfl`.
    let yes0 = f.all_below(always_true, 0);
    let no0 = f.all_below(always_false, 0);
    assert!(
        f.k.def_eq(yes0, no0),
        "at bound 0 both loops are `true`, which is why the congruence's base \
         case needs no hypothesis"
    );
}

/// Every declaration this module lands is present, is the kind it claims to
/// be, and rests on zero axioms.
///
/// `Environment::contains` comes FIRST on every name: `Kernel::axiom_footprint`
/// of a name that was never declared is also empty, so the footprint assertion
/// alone would pass for a typo.
#[test]
fn the_fixed_bound_inclusion_shelf_is_admitted_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let definitions: [NameId; 1] = [p.finset_subset_fixed];
    let theorems: [NameId; 4] = [
        p.finset_all_below_congr,
        p.finset_subset_fixed_of_mem,
        p.finset_mem_of_subset_fixed,
        p.finset_subset_fixed_congr,
    ];

    for name in definitions {
        let shown = k.display_name(name).to_string();
        assert!(
            k.environment().contains(name),
            "{shown} must be declared before its footprint means anything"
        );
        let decl = k.environment().get(name).expect("just checked");
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "{shown} must be a Definition"
        );
        println!("def {shown} : {}", k.render_lean(decl.ty()));
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{shown} must rest on zero axioms"
        );
    }

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

/// The congruence lemma is stated over the loop bound `subsetFixed` actually
/// uses, so it can discharge `forallSubset_of_search`'s premise.
///
/// This is a statement-shape check, not a proof check: `subsetFixed_congr`
/// quantifies `s` once and both `t` arguments after it, which is what makes
/// `fun t => subsetFixed s t` a congruent predicate at a FIXED `s`. A version
/// that varied `s` instead would be admitted just as happily by the footprint
/// test above and would be useless to the search.
#[test]
fn subset_fixed_congr_fixes_the_first_argument() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let congr = k
        .environment()
        .get(p.finset_subset_fixed_congr)
        .expect("subsetFixed_congr must be admitted")
        .ty();
    let shown = k.render_lean(congr);

    assert!(
        shown.contains("Nat.Finset.subsetFixed"),
        "the congruence must be about `subsetFixed`; got {shown}"
    );
    assert!(
        shown.contains("Nat.Finset.memB"),
        "its hypothesis must be POINTWISE membership, not `subsetB`; got {shown}"
    );
    // The control: the hypothesis must not be an equation between the two
    // sets, which would make the lemma a triviality.
    assert!(
        !shown.contains("Nat.Finset.beq"),
        "the hypothesis must not be a decidable set equality; got {shown}"
    );

    // The premise `Nat.Finset.forallSubset_of_search` asks for is stated over
    // the same vocabulary, which is what makes this a discharge rather than a
    // near miss.
    let search = k
        .environment()
        .get(p.finset_forall_subset_of_search)
        .expect("forallSubset_of_search must be admitted")
        .ty();
    let search_shown = k.render_lean(search);
    assert!(
        search_shown.contains("Nat.Finset.memB"),
        "the search's congruence premise must be pointwise membership too; \
         got {search_shown}"
    );
}

// ---------------------------------------------------------------------------
// The critical-subset split (deliverable 2).
// ---------------------------------------------------------------------------

/// The five split declarations are present, are checked `Theorem`s, and rest on
/// zero axioms.
///
/// `Environment::contains` comes FIRST on every name, because
/// `Kernel::axiom_footprint` of a name that was never declared is also empty
/// and the footprint assertion alone would pass for a typo.
#[test]
fn the_critical_split_is_admitted_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let theorems: [NameId; 5] = [
        p.finset_card_union_of_disjoint,
        p.hall_condition_subset,
        p.hall_mem_union_over_union_of_vanishing,
        p.hall_condition_sdiff_of_critical,
        p.hall_condition_sdiff_singleton_of_strict,
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

/// The disjoint-union count is a real identity at concrete sets, and it FAILS
/// when the two sets meet — so the hypothesis of
/// `Nat.Finset.card_union_of_disjoint` is load-bearing rather than decoration.
///
/// A theorem's footprint says nothing about whether its hypothesis is needed.
/// These are the two hand-computed instances that say so:
///
/// ```text
/// card (union (singleton 0) (singleton 1)) = 2 = 1 + 1   disjoint: the identity
/// card (union (singleton 0) (singleton 0)) = 1 ≠ 1 + 1   overlapping: it fails
/// ```
#[test]
fn the_disjointness_hypothesis_is_load_bearing() {
    let mut f = Fixture::new();

    let s0 = f.singleton(0);
    let s1 = f.singleton(1);

    let disjoint = {
        let u = f.union(s0, s1);
        f.card(u)
    };
    let two = f.num(2);
    assert!(
        f.k.def_eq(disjoint, two),
        "card (singleton 0 ∪ singleton 1) must be 2"
    );

    let overlapping = {
        let u = f.union(s0, s0);
        f.card(u)
    };
    let one = f.num(1);
    assert!(
        f.k.def_eq(overlapping, one),
        "card (singleton 0 ∪ singleton 0) must be 1"
    );
    assert!(
        !f.k.def_eq(overlapping, two),
        "negative control: without disjointness the sum is WRONG, so \
         `card_union_of_disjoint` cannot be stated without its hypothesis"
    );
}

/// Dropping indices from a union is NOT free in general — the vanishing
/// hypothesis of `Nat.Hall.memB_unionOver_union_of_vanishing` is what buys it.
///
/// At `mb := Nat.Finset.singleton` (so `mb i` is `{i}`), `w := {0}`,
/// `t := {1}` and `v := 1`:
///
/// ```text
/// memB (unionOver mb ({0} ∪ {1})) 1 = true    -- index 1 contributes 1
/// memB (unionOver mb {0})         1 = false   -- index 0 contributes only 0
/// ```
///
/// The two sides DISAGREE, and they must: this `mb` does not vanish on `t`
/// (`memB (mb 1) 1` is `true`, not `false`), so the lemma does not apply here.
/// Without this instance the lemma could have been the trivial one that holds
/// for every family.
#[test]
fn dropping_indices_from_a_union_needs_the_vanishing_hypothesis() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    // `mb := Nat.Finset.singleton`, as a bare function `Nat → Nat.Finset`.
    let mb = {
        let name = f.p.finset_singleton;
        f.k.const_(name, vec![])
    };
    let w = f.singleton(0);
    let t = f.singleton(1);
    let big = f.union(w, t);

    let cover_big = f.union_over(mb, big);
    let cover_w = f.union_over(mb, w);

    let at_big = f.memb_of(cover_big, 1);
    let at_w = f.memb_of(cover_w, 1);

    assert!(
        f.k.def_eq(at_big, tr),
        "1 is covered by the union over {{0}} ∪ {{1}}: index 1 contributes it"
    );
    assert!(
        f.k.def_eq(at_w, fa),
        "1 is NOT covered by the union over {{0}} alone"
    );
    assert!(
        !f.k.def_eq(at_big, at_w),
        "negative control: the two unions must DISAGREE here. This family does \
         not vanish on `t`, so `memB_unionOver_union_of_vanishing` does not \
         apply -- which is what makes its hypothesis content rather than \
         decoration"
    );

    // ...and the hypothesis really is false for this family at this value.
    let mb_at_one = f.singleton(1);
    let inside = f.memb_of(mb_at_one, 1);
    assert!(
        f.k.def_eq(inside, tr),
        "`memB (mb 1) 1` is true, so the vanishing hypothesis fails here"
    );
}

/// The two split lemmas are stated over the vocabulary the induction will
/// compose them in, and the deleted family is spelled the way
/// `Nat.Hall.card_le_card_unionOver_sdiff_add` spells it.
///
/// This is a statement-shape check and it is the one the footprint test cannot
/// do. A version of the critical branch that deleted the WRONG set — `t` itself
/// rather than `unionOver nb t` — would be admitted just as happily and would
/// be useless: the values a matching on `t` consumes live in the
/// neighbourhood, not in the index set.
#[test]
fn the_split_lemmas_delete_the_neighbourhood_not_the_index_set() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let critical = k
        .environment()
        .get(p.hall_condition_sdiff_of_critical)
        .expect("the critical branch must be admitted")
        .ty();
    let shown = k.render_lean(critical);

    for needle in [
        "Nat.Hall.HallCondition",
        "Nat.Hall.unionOver",
        "Nat.Finset.sdiff",
        "Nat.Finset.card",
    ] {
        assert!(
            shown.contains(needle),
            "the critical branch must mention {needle}; got {shown}"
        );
    }
    // The deleted set is `unionOver nb t`, so `sdiff` and `unionOver` must
    // both appear -- and the conclusion's family must delete a `unionOver`,
    // not a bare index set. `Nat.Finset.singleton` must NOT appear: that is
    // the other branch's shape.
    assert!(
        !shown.contains("Nat.Finset.singleton"),
        "the critical branch deletes a whole neighbourhood, never a singleton; \
         got {shown}"
    );

    let strict = k
        .environment()
        .get(p.hall_condition_sdiff_singleton_of_strict)
        .expect("the non-critical branch must be admitted")
        .ty();
    let strict_shown = k.render_lean(strict);
    assert!(
        strict_shown.contains("Nat.Finset.singleton"),
        "the non-critical branch deletes ONE value; got {strict_shown}"
    );
    assert!(
        strict_shown.contains("Nat.lt"),
        "the non-critical branch's hypothesis must be STRICT; got {strict_shown}"
    );
    // The control: the critical branch's hypothesis is NOT strict -- it is a
    // `Le` on the neighbourhood count, which is what lets the caller decide it
    // with a `Le` test. If both were strict, one of the two branches would be
    // unreachable.
    assert!(
        shown.contains("Nat.le"),
        "the critical branch's criticality hypothesis must be a `Le`; got {shown}"
    );
}

/// `Nat.Hall.hallCondition_subset` really restricts, and its direction is
/// pinned: the hypothesis says the SECOND index set is inside the first.
///
/// Both `HallCondition s nb → … → HallCondition t nb` and its converse have
/// the same constants in the same order, so a rendered-name check cannot tell
/// them apart. What can is the ARITY at which each `HallCondition` sits, which
/// the render shows as the argument order. This test reads the rendered type
/// and asserts the two mentions are not identical strings — a lemma whose
/// hypothesis and conclusion were the same instance would be a tautology.
#[test]
fn hall_condition_subset_is_not_a_tautology() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let decl = k
        .environment()
        .get(p.hall_condition_subset)
        .expect("hallCondition_subset must be admitted")
        .ty();
    let shown = k.render_lean(decl);

    let mentions = shown.matches("Nat.Hall.HallCondition").count();
    assert!(
        mentions == 2,
        "the restriction lemma must mention `HallCondition` exactly twice \
         (hypothesis and conclusion); got {mentions} in {shown}"
    );
    assert!(
        shown.contains("Nat.Finset.memB"),
        "the inclusion premise must be POINTWISE membership; got {shown}"
    );
    // The control: it must not be stated over `subsetB` or `subsetFixed`,
    // neither of which carries the reflection this proof composes.
    assert!(
        !shown.contains("Nat.Finset.subsetB"),
        "the inclusion premise must not be the bounded decision; got {shown}"
    );
}
