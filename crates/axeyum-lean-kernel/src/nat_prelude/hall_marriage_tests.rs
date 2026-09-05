//! Concrete-instance tests for `nat_prelude::hall_marriage` (ADR-1645).
//!
//! An empty axiom footprint is ALSO what a missing name returns, so every
//! footprint assertion is preceded by `Environment::contains` and a check of the
//! declaration's KIND.
//!
//! `Nat.Hall.criticalB` is a `Definition`, and the kernel cannot tell a
//! definition is wrong — it type-checks at `Finset → (Nat → Finset) → Finset →
//! Bool` and so does `fun _ _ _ => true`. So it is evaluated at closed
//! arguments against hand-computed verdicts, with one instance per conjunct
//! chosen so that dropping THAT conjunct flips exactly that row.
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

    /// `Nat.Finset.empty`.
    fn empty(&mut self) -> ExprId {
        let name = self.p.finset_empty;
        self.k.const_(name, vec![])
    }

    /// `Nat.Hall.criticalB s nb t`.
    fn critical(&mut self, s: ExprId, nb: ExprId, t: ExprId) -> ExprId {
        let name = self.p.hall_critical_b;
        self.const_app(name, &[s, nb, t])
    }

    /// The constant family `fun _ => m`.
    fn const_family(&mut self, m: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        self.lam_fv(i_fv, nat, m)
    }
}

/// Every declaration this file adds is present, is the kind it claims to be,
/// and rests on zero axioms — including the two headline statements.
#[test]
fn halls_marriage_theorem_is_admitted_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let definitions: [NameId; 1] = [p.hall_critical_b];
    let theorems: [NameId; 6] = [
        p.finset_mem_b_sdiff_congr,
        p.hall_is_matching_of_family_sdiff,
        p.hall_mem_b_false_of_family_sdiff,
        p.hall_critical_b_congr,
        p.hall_sufficient,
        p.hall_marriage_iff,
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

/// `Nat.Hall.marriage_iff` is a BICONDITIONAL between Hall's condition and the
/// existence of a matching, and not something weaker that would also type-check
/// under the name.
///
/// The statement-shape check is what a footprint test cannot do: an `Iff` whose
/// two sides were the same proposition, or whose right side quantified the
/// wrong thing, would be admitted and axiom-free just as happily.
#[test]
fn the_theorem_relates_halls_condition_to_a_matching() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let decl = k
        .environment()
        .get(p.hall_marriage_iff)
        .expect("marriage_iff must be admitted");
    let shown = k.render_lean(decl.ty());

    assert!(
        shown.contains("Iff"),
        "must be a biconditional; got {shown}"
    );
    assert!(
        shown.contains("Nat.Hall.HallCondition"),
        "one side must be Hall's condition; got {shown}"
    );
    assert!(
        shown.contains("Nat.Hall.IsMatching"),
        "the other side must be a matching; got {shown}"
    );
    assert!(
        shown.contains("Exists"),
        "the matching side must be an EXISTENTIAL over the choice function, not \
         a fixed one; got {shown}"
    );

    // The sufficiency direction on its own must not be the trivial implication:
    // its hypothesis is Hall's condition and its conclusion the existential.
    let suff = k
        .environment()
        .get(p.hall_sufficient)
        .expect("sufficient must be admitted");
    let shown_suff = k.render_lean(suff.ty());
    let hall_at = shown_suff
        .find("Nat.Hall.HallCondition")
        .expect("sufficient must mention Hall's condition");
    let exists_at = shown_suff
        .find("Exists")
        .expect("sufficient must conclude an existential");
    assert!(
        hall_at < exists_at,
        "Hall's condition must be the HYPOTHESIS and the existential the \
         conclusion, not the other way round; got {shown_suff}"
    );
}

/// `criticalB` decides what it claims to, at four closed instances chosen so
/// that each conjunct is the one that decides exactly one row.
///
/// The family is the constant `fun _ => range 1 = {0}`, so `unionOver nb t` is
/// `{0}` for every nonempty `t` and empty for `t = empty`.
///
/// | `s`         | `t`           | verdict | the conjunct that decides it              |
/// |-------------|---------------|---------|-------------------------------------------|
/// | `range 3`   | `singleton 1` | true    | all four hold                              |
/// | `range 3`   | `empty`       | false   | `ble 1 (card t)` — the FIRST positivity test |
/// | `range 3`   | `range 3`     | false   | `ble 1 (card (sdiff s t))` — the SECOND one |
/// | `{0, 2}`    | `singleton 1` | false   | `subsetFixed s t` — `1 ∉ s`, and `1 < bound s` |
///
/// Rows two and three are the pair the module header calls out: each is
/// rejected by one positivity conjunct and accepted by the other, so a version
/// carrying only one of them passes exactly one of these rows.
///
/// The last row uses `{0, 2}` rather than a member ABOVE `bound s`, and the
/// separate test below records why.
#[test]
fn critical_b_decides_the_four_conjuncts_separately() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let s = f.range(3);
    let nbhd = f.range(1);
    let nb = f.const_family(nbhd);

    let good = f.singleton(1);
    let verdict = f.critical(s, nb, good);
    assert!(
        f.k.def_eq(verdict, tr),
        "`singleton 1` is a nonempty proper critical subset of `range 3`"
    );

    let e = f.empty();
    let verdict = f.critical(s, nb, e);
    assert!(
        f.k.def_eq(verdict, fa),
        "the EMPTY subset must be rejected -- otherwise the critical branch \
         recurses on `sdiff s empty`, whose count is `card s`, and the \
         induction does not descend"
    );

    let whole = f.range(3);
    let verdict = f.critical(s, nb, whole);
    assert!(
        f.k.def_eq(verdict, fa),
        "the WHOLE set must be rejected -- otherwise the critical branch \
         recurses on `t` at the same count"
    );

    // `{0, 2}`: a hole INSIDE the loop's range, which is what `subsetFixed`
    // can see.
    let gapped = f.sdiff_of(s, good);
    let verdict = f.critical(gapped, nb, good);
    assert!(
        f.k.def_eq(verdict, fa),
        "`singleton 1` is not included in `{{0, 2}}`, and 1 is below its bound, \
         so the inclusion conjunct must reject it"
    );
}

/// `criticalB` accepts a set whose members lie ABOVE `bound s`, and the
/// induction is unaffected because the SEARCH never offers it one.
///
/// This is ADR-1644's truncation hazard, asserted rather than avoided.
/// `subsetFixed s t` loops to `bound s`, so it answers nothing about indices at
/// or above that bound: `subsetFixed (range 3) (singleton 5)` is `true` even
/// though `5 ∉ range 3`. A reader who assumed `criticalB s nb t = true` implies
/// `t ⊆ s` would be wrong, and the proof does not assume it —
/// `Nat.Finset.existsSubset_of_search` returns `bound t = bound s` alongside
/// the verdict, and it is that equation, fed to
/// `memB_of_subsetFixed_of_bound_le`, which upgrades the decision to a real
/// inclusion.
///
/// The assertions below pin both halves: the predicate DOES accept
/// `singleton 5`, and `singleton 5` does NOT have the bound the search
/// guarantees.
#[test]
fn the_predicate_alone_does_not_imply_inclusion_and_the_search_bound_is_why() {
    let mut f = Fixture::new();
    let tr = f.bool_true();
    let fa = f.bool_false();

    let s = f.range(3);
    let nbhd = f.range(1);
    let nb = f.const_family(nbhd);
    let outside = f.singleton(5);

    let verdict = f.critical(s, nb, outside);
    assert!(
        f.k.def_eq(verdict, tr),
        "the predicate accepts `singleton 5` -- `subsetFixed` runs to \
         `bound s` = 3 and never looks at index 5"
    );
    let member = f.memb_of(s, 5);
    assert!(
        f.k.def_eq(member, fa),
        "...while 5 is genuinely NOT a member of `range 3`"
    );

    // The search's bound equation is what the proof uses instead, and this
    // instance does not satisfy it.
    let bound_t = f.bound_of(outside);
    let bound_s = f.bound_of(s);
    let six = f.num(6);
    let three = f.num(3);
    assert!(f.k.def_eq(bound_t, six), "`bound (singleton 5)` must be 6");
    assert!(f.k.def_eq(bound_s, three), "`bound (range 3)` must be 3");
    assert!(
        !f.k.def_eq(bound_t, bound_s),
        "so `existsSubset_of_search` at `bound s` cannot return this set, and \
         the inductive step never sees it"
    );
}

/// The two positivity conjuncts are genuinely independent: neither instance
/// that one rejects is rejected by the other.
///
/// This is the control for the table above. Dropping `ble 1 (card t)` would
/// leave `t = empty` accepted, because its complement IS nonempty; dropping
/// `ble 1 (card (sdiff s t))` would leave `t = s` accepted, because `s` IS
/// nonempty. So the pair cannot be collapsed into one test, and this asserts
/// the two counts that make that so rather than asserting it in prose.
#[test]
fn neither_positivity_conjunct_subsumes_the_other() {
    let mut f = Fixture::new();

    let s = f.range(3);
    let e = f.empty();
    let whole = f.range(3);

    let card_e = f.card_of(e);
    let zero = f.zero();
    assert!(
        f.k.def_eq(card_e, zero),
        "`card empty` is 0, so `t = empty` is rejected by the FIRST test"
    );
    let rest_of_empty = f.sdiff_of(s, e);
    let card_rest_of_empty = f.card_of(rest_of_empty);
    let three = f.num(3);
    assert!(
        f.k.def_eq(card_rest_of_empty, three),
        "...and its complement has count 3, so the SECOND test accepts it"
    );

    let card_whole = f.card_of(whole);
    assert!(
        f.k.def_eq(card_whole, three),
        "`card (range 3)` is 3, so `t = s` is accepted by the FIRST test"
    );
    let rest_of_whole = f.sdiff_of(s, whole);
    let card_rest_of_whole = f.card_of(rest_of_whole);
    assert!(
        f.k.def_eq(card_rest_of_whole, zero),
        "...and its complement is empty, so only the SECOND test rejects it"
    );
}

impl Fixture {
    /// `Nat.Finset.card s`.
    fn card_of(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    /// `Nat.Finset.sdiff s t`.
    fn sdiff_of(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_sdiff;
        self.const_app(name, &[s, t])
    }

    /// `Nat.Finset.bound s`.
    fn bound_of(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_bound;
        self.const_app(name, &[s])
    }

    /// `Nat.Finset.memB s i` at a numeral index.
    fn memb_of(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }
}
