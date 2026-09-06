//! Concrete-instance tests for `nat_prelude::multiset_select`.
//!
//! `Nat.Multiset.restrict` and `Nat.Multiset.prodSel` are `Definition`s, and
//! **the trusted gate cannot tell a `Definition` is wrong** — it type-checks, and
//! a fold that reads the wrong position has exactly the right type. So the
//! theorems in `multiset_select.rs` prove nothing about whether `prodSel` is the
//! product over the selected values; only the evaluations below do.
//!
//! Every check is paired with the specific wrong value it rules out:
//!
//! - `prodSel {2,2,3} (· = 2) = 4` rules out `2` (a `prodSel` that ignored the
//!   multiplicity) and `12` (one that ignored the selection).
//! - `prodSel {2,2,3} (· = 3) = 3` rules out `4` — the two selections have to
//!   give DIFFERENT answers, or a `prodSel` reading a constant would pass.
//! - `prodSel {2,2,3} (· = 2)` must not be `1`, which is what an OFF-BY-ONE
//!   read (`s (succ q)` in place of `s q`) gives: `succ q = 2` at `q = 1`, where
//!   `count m 1 = 0` and the factor is `1`. This is the mutant the lane brief
//!   names, and this assertion is what kills it.
//! - `count (restrict {2,2,3} (· = 2)) 2 = 2` and `… 3 = 0` pin the restriction
//!   in both directions: kept with multiplicity, and dropped.
//!
//! The last test is not a wrong-value control but a **necessity** control:
//! `Nat.Multiset.prodSel_injective` concludes only at the values the multiset
//! actually contains, and `{3}` with the two selections `(· = 3)` and
//! `insertAt 2 (· = 3)` shows why — they have the same `prodSel` (`3`) and
//! disagree at `2`, INSIDE the bound, because `count {3} 2 = 0` makes the factor
//! `2 ^ 0 = 1` either way. Dropping the hypothesis would make the theorem false,
//! not merely weaker.
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest value any check below builds is `12`.

use crate::expr::ExprId;
use crate::name::NameId;
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

    /// `Nat.Multiset.singleton a`.
    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.multiset_singleton;
        self.const_app(name, &[lit])
    }

    /// The multiset with the given elements, added left to right.
    fn of(&mut self, elements: &[u32]) -> ExprId {
        let (first, rest) = elements.split_first().expect("at least one element");
        let mut acc = self.singleton(*first);
        for &e in rest {
            let s = self.singleton(e);
            let name = self.p.multiset_add;
            acc = self.const_app(name, &[acc, s]);
        }
        acc
    }

    /// `fun q => Nat.beq q k` — the selection of the single value `k`.
    fn only(&mut self, k: u32) -> ExprId {
        let nat = self.nat_ty();
        let q_fv = self.fresh_fvar();
        let q = self.k.fvar(q_fv);
        let lit = self.num(k);
        let body = self.beq(q, lit);
        self.lam_fv(q_fv, nat, body)
    }

    /// `Nat.Subsets.insertAt k s` — `s` with the value `k` added.
    fn insert_at(&mut self, k: u32, s: ExprId) -> ExprId {
        let lit = self.num(k);
        let name = self.p.subsets_insert_at;
        self.const_app(name, &[lit, s])
    }

    /// `Nat.Multiset.prodSel m s`.
    fn prod_sel(&mut self, m: ExprId, s: ExprId) -> ExprId {
        let name = self.p.multiset_prod_sel;
        self.const_app(name, &[m, s])
    }

    /// `Nat.Multiset.restrict m s`.
    fn restrict(&mut self, m: ExprId, s: ExprId) -> ExprId {
        let name = self.p.multiset_restrict;
        self.const_app(name, &[m, s])
    }

    /// `Nat.Multiset.count m x`.
    fn count(&mut self, m: ExprId, x: u32) -> ExprId {
        let lit = self.num(x);
        let name = self.p.multiset_count;
        self.const_app(name, &[m, lit])
    }

    /// `Nat.Multiset.bound m`.
    fn bound(&mut self, m: ExprId) -> ExprId {
        let name = self.p.multiset_bound;
        self.const_app(name, &[m])
    }

    /// `Nat.Multiset.prod m`.
    fn prod(&mut self, m: ExprId) -> ExprId {
        let name = self.p.multiset_prod;
        self.const_app(name, &[m])
    }
}

/// `Nat.Multiset.prodSel` computes the product over the SELECTED values, with
/// multiplicity, and the two single-value selections of `{2,2,3}` disagree.
///
/// The `1` control is the one that matters: it is the value an off-by-one read
/// of the selection gives, and no theorem in `multiset_select.rs` would notice.
#[test]
fn prod_sel_evaluates_the_two_single_value_selections() {
    let mut f = Fixture::new();
    let m = f.of(&[2, 2, 3]);

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let twelve = f.num(12);

    let pick_two = f.only(2);
    let sel_two = f.prod_sel(m, pick_two);
    assert!(
        f.k.def_eq(sel_two, four),
        "prodSel {{2,2,3}} (· = 2) must be 4 (the repeated 2, kept with \
         multiplicity), got {}",
        f.k.render_lean(sel_two)
    );
    assert!(
        !f.k.def_eq(sel_two, two),
        "negative control: it must NOT be 2 -- that is what a `prodSel` \
         discarding the multiplicity would give"
    );
    assert!(
        !f.k.def_eq(sel_two, one),
        "negative control: it must NOT be 1 -- that is what a `prodSel` reading \
         the selection at the WRONG position (`s (succ q)` for `s q`) gives, \
         since `count {{2,2,3}} 1 = 0`"
    );
    assert!(
        !f.k.def_eq(sel_two, twelve),
        "negative control: it must NOT be 12 -- that is `prod`, i.e. a \
         `prodSel` that ignored the selection"
    );

    let pick_three = f.only(3);
    let sel_three = f.prod_sel(m, pick_three);
    assert!(
        f.k.def_eq(sel_three, three),
        "prodSel {{2,2,3}} (· = 3) must be 3, got {}",
        f.k.render_lean(sel_three)
    );
    assert!(
        !f.k.def_eq(sel_three, four),
        "negative control: the two single-value selections must DISAGREE, or a \
         `prodSel` reading a constant selection would pass both checks"
    );
}

/// The two boundary selections evaluate, and `prodSel_all`/`prodSel_empty` say
/// the same thing at the same numbers.
#[test]
fn prod_sel_at_the_empty_and_full_selections() {
    let mut f = Fixture::new();
    let p = f.p;
    let m = f.of(&[2, 2, 3]);

    let one = f.num(1);
    let twelve = f.num(12);

    let empty = f.k.const_(p.subsets_empty, vec![]);
    let sel_empty = f.prod_sel(m, empty);
    assert!(
        f.k.def_eq(sel_empty, one),
        "prodSel {{2,2,3}} ∅ must be 1, got {}",
        f.k.render_lean(sel_empty)
    );

    let all = {
        let nat = f.nat_ty();
        let q_fv = f.fresh_fvar();
        let t = f.bool_true();
        f.lam_fv(q_fv, nat, t)
    };
    let sel_all = f.prod_sel(m, all);
    assert!(
        f.k.def_eq(sel_all, twelve),
        "prodSel {{2,2,3}} (fun _ => true) must be 12, got {}",
        f.k.render_lean(sel_all)
    );
    assert!(
        !f.k.def_eq(sel_all, one),
        "negative control: the full selection must NOT collapse to the empty \
         one's value"
    );

    // The two theorems, instantiated at this multiset, state exactly that.
    let empty_thm = f.const_app(p.multiset_prod_sel_empty, &[m]);
    let empty_ty =
        f.k.infer(empty_thm)
            .expect("prodSel_empty must instantiate at {2,2,3}");
    let expected_empty = f.eq(one, one);
    assert!(
        f.k.def_eq(empty_ty, expected_empty),
        "prodSel_empty {{2,2,3}} must state `1 = 1`, got {}",
        f.k.render_lean(empty_ty)
    );

    let all_thm = f.const_app(p.multiset_prod_sel_all, &[m]);
    let all_ty =
        f.k.infer(all_thm)
            .expect("prodSel_all must instantiate at {2,2,3}");
    let expected_all = f.eq(twelve, twelve);
    assert!(
        f.k.def_eq(all_ty, expected_all),
        "prodSel_all {{2,2,3}} must state `12 = 12`, got {}",
        f.k.render_lean(all_ty)
    );
    let wrong_all = f.eq(twelve, one);
    assert!(
        !f.k.def_eq(all_ty, wrong_all),
        "negative control: prodSel_all must NOT state `12 = 1`"
    );
}

/// `Nat.Multiset.restrict` keeps the selected values with their multiplicity,
/// drops the rest, and keeps the BOUND — which is the property
/// `count_restrict`'s lack of a side condition rests on.
#[test]
fn restrict_keeps_multiplicity_and_bound_and_drops_the_rest() {
    let mut f = Fixture::new();
    let m = f.of(&[2, 2, 3]);
    let pick_two = f.only(2);
    let r = f.restrict(m, pick_two);

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let four = f.num(4);

    let kept = f.count(r, 2);
    assert!(
        f.k.def_eq(kept, two),
        "count (restrict {{2,2,3}} (· = 2)) 2 must be 2, got {}",
        f.k.render_lean(kept)
    );
    assert!(
        !f.k.def_eq(kept, one),
        "negative control: it must NOT be 1 -- a `restrict` that kept mere \
         MEMBERSHIP rather than the multiplicity would give that"
    );

    let dropped = f.count(r, 3);
    assert!(
        f.k.def_eq(dropped, zero),
        "count (restrict {{2,2,3}} (· = 2)) 3 must be 0, got {}",
        f.k.render_lean(dropped)
    );
    assert!(
        !f.k.def_eq(dropped, one),
        "negative control: the unselected value must NOT survive"
    );

    let bound_r = f.bound(r);
    let bound_m = f.bound(m);
    assert!(
        f.k.def_eq(bound_r, bound_m),
        "restrict must keep the bound: `count_restrict` has no `q < bound` side \
         condition precisely because it does"
    );

    let prod_r = f.prod(r);
    assert!(
        f.k.def_eq(prod_r, four),
        "prod (restrict {{2,2,3}} (· = 2)) must be 4, got {}",
        f.k.render_lean(prod_r)
    );
}

/// `prodSel_eq_prod_restrict` and `prodSel_dvd_prod` INSTANTIATE at the worked
/// multiset, and what they state there is about these numbers.
#[test]
fn the_two_bridge_theorems_instantiate_at_the_worked_multiset() {
    let mut f = Fixture::new();
    let p = f.p;
    let m = f.of(&[2, 2, 3]);
    let pick_two = f.only(2);

    let four = f.num(4);
    let twelve = f.num(12);

    let bridge = f.const_app(p.multiset_prod_sel_eq_prod_restrict, &[m, pick_two]);
    let bridge_ty =
        f.k.infer(bridge)
            .expect("prodSel_eq_prod_restrict must instantiate");
    let expected = f.eq(four, four);
    assert!(
        f.k.def_eq(bridge_ty, expected),
        "prodSel_eq_prod_restrict must state `4 = 4` here, got {}",
        f.k.render_lean(bridge_ty)
    );
    let wrong = f.eq(four, twelve);
    assert!(
        !f.k.def_eq(bridge_ty, wrong),
        "negative control: it must NOT state `4 = 12`"
    );

    let divides = f.const_app(p.multiset_prod_sel_dvd_prod, &[m, pick_two]);
    let divides_ty =
        f.k.infer(divides)
            .expect("prodSel_dvd_prod must instantiate");
    let expected_dvd = f.dvd(four, twelve);
    assert!(
        f.k.def_eq(divides_ty, expected_dvd),
        "prodSel_dvd_prod must state `4 ∣ 12` here, got {}",
        f.k.render_lean(divides_ty)
    );
    let wrong_dvd = f.dvd(twelve, four);
    assert!(
        !f.k.def_eq(divides_ty, wrong_dvd),
        "negative control: it must NOT state `12 ∣ 4`"
    );
}

/// NECESSITY control for `prodSel_injective`'s `Lt 0 (count m q)` hypothesis.
///
/// The theorem concludes `s q = t q` only where the multiset actually has an
/// element. That is not slack: `{3}` (bound `4`) with `s := (· = 3)` and
/// `t := insertAt 2 s` have the SAME `prodSel` — `3` — and disagree at `2`,
/// which is INSIDE the bound. Dropping the hypothesis would make the theorem
/// false, so no strengthening of it is available at this carrier.
#[test]
fn prod_sel_injectivity_cannot_reach_outside_the_support() {
    let mut f = Fixture::new();
    let m = f.of(&[3]);
    let s = f.only(3);
    let t = f.insert_at(2, s);

    let three = f.num(3);
    let zero = f.zero();

    let sel_s = f.prod_sel(m, s);
    let sel_t = f.prod_sel(m, t);
    assert!(
        f.k.def_eq(sel_s, three),
        "prodSel {{3}} (· = 3) must be 3, got {}",
        f.k.render_lean(sel_s)
    );
    assert!(
        f.k.def_eq(sel_t, three),
        "prodSel {{3}} (insertAt 2 (· = 3)) must ALSO be 3, got {}",
        f.k.render_lean(sel_t)
    );

    // ... and yet the two selections differ at 2, which is below the bound.
    let two = f.num(2);
    let s_at_two = f.apply(s, &[two]);
    let t_at_two = f.apply(t, &[two]);
    let false_ = f.bool_false();
    let true_ = f.bool_true();
    assert!(
        f.k.def_eq(s_at_two, false_),
        "the first selection must not contain 2"
    );
    assert!(
        f.k.def_eq(t_at_two, true_),
        "the second selection must contain 2"
    );

    // The reason they may differ there is that the multiset has no 2.
    let count_two = f.count(m, 2);
    assert!(
        f.k.def_eq(count_two, zero),
        "count {{3}} 2 must be 0 -- that is exactly the hypothesis \
         `prodSel_injective` requires and cannot have"
    );
    let bound_m = f.bound(m);
    let four = f.num(4);
    assert!(
        f.k.def_eq(bound_m, four),
        "and 2 is INSIDE the bound (4), so this is not an out-of-range artefact"
    );
}

/// Every name this module declares is present, is derived rather than asserted,
/// and rests on ZERO axioms.
///
/// `Kernel::axiom_footprint` returns an empty set for a name that does not
/// exist, so `Environment::contains` is asserted FIRST for each — otherwise a
/// renamed or never-declared theorem would pass this test silently.
#[test]
fn every_multiset_select_declaration_is_present_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names: [NameId; 14] = [
        p.mul_dvd_mul,
        p.prod_range_dvd_prod_range,
        p.bool_select_nat_inj_of_pos,
        p.multiset_restrict,
        p.multiset_prod_sel,
        p.multiset_bound_restrict,
        p.multiset_count_restrict,
        p.multiset_count_restrict_pos,
        p.multiset_prod_sel_eq_prod_restrict,
        p.multiset_prod_sel_all,
        p.multiset_prod_sel_empty,
        p.multiset_prod_sel_congr,
        p.multiset_prod_sel_dvd_prod,
        p.multiset_prod_sel_injective,
    ];
    for name in names {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{shown} must be declared -- an absent name has an EMPTY axiom \
             footprint, so the check below would pass without it"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must rest on zero axioms, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}
