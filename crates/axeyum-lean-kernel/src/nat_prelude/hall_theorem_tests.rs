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
