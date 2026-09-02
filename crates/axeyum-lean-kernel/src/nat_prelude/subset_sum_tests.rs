//! Tests for [`nat_prelude::subset_sum`](super::subset_sum).
//!
//! The order here is deliberate and matches the contributor guide's rule for
//! a new `Definition`: **the trusted gate cannot tell you a definition is
//! wrong** — `Nat.sumRangeIf` would type-check just as well with the
//! product convention (`1` for an unselected index) or with the predicate
//! read the other way round. So the evaluation tests come first, at tiny
//! arguments, each with a negative control that a wrong-but-well-typed
//! variant would fail:
//!
//! 1. **Evaluation at numerals** against a reference recomputed in Rust,
//!    with the `prodRangeIf` convention (`1` when unselected) and the
//!    negated predicate both shown to give DIFFERENT numbers.
//! 2. The two defining equations, instantiated.
//! 3. The bounded congruence, at a pair of predicates that agree below the
//!    bound and DISAGREE at it — so the boundedness is exercised, not
//!    incidental.
//! 4. The complement split, evaluated on both sides, with the control that
//!    `sumRangeIf p f n` alone is not the full sum.
//! 5. Footprints and the four declared types, pinned character for
//!    character.

use crate::expr::{BinderInfo, ExprId};
use crate::tc::{LocalContext, LocalDecl};
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

/// Which concrete predicate/function pair a test is using. Both are built
/// from `Nat.ble`, `Nat.succ` and `Nat.mul` only, so they reduce at numerals
/// with no extra prelude machinery.
#[derive(Clone, Copy)]
enum Case {
    /// `p i := ble 3 i` ("`3 ≤ i`"), `f i := succ i`.
    GeThreeSucc,
    /// `p i := ble i 1` ("`i ≤ 1`"), `f i := mul i i`.
    LeOneSquare,
}

impl Case {
    fn holds(self, i: u32) -> bool {
        match self {
            Self::GeThreeSucc => 3 <= i,
            Self::LeOneSquare => i <= 1,
        }
    }

    fn value(self, i: u32) -> u32 {
        match self {
            Self::GeThreeSucc => i + 1,
            Self::LeOneSquare => i * i,
        }
    }

    /// `Σ_{i<n, p i} f i` — the intended reading.
    fn selected_sum(self, n: u32) -> u32 {
        (0..n)
            .filter(|&i| self.holds(i))
            .map(|i| self.value(i))
            .sum()
    }

    /// `Σ_{i<n, ¬ p i} f i` — what `setCompl p` must select.
    fn unselected_sum(self, n: u32) -> u32 {
        (0..n)
            .filter(|&i| !self.holds(i))
            .map(|i| self.value(i))
            .sum()
    }

    /// `Σ_{i<n} f i` — the full range.
    fn full_sum(self, n: u32) -> u32 {
        (0..n).map(|i| self.value(i)).sum()
    }

    /// What the `prodRangeIf` convention would give if the unselected value
    /// were `1` instead of `0`: the wrong-but-well-typed definition.
    fn one_padded_sum(self, n: u32) -> u32 {
        (0..n)
            .map(|i| if self.holds(i) { self.value(i) } else { 1 })
            .sum()
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// Open a local context holding one free variable per supplied type. The
    /// congruence's two hypotheses are propositions no numeral discharges, so
    /// this is how that instance is inferred at all -- and it is a WEAKER
    /// check than a discharged one, which is why the evaluation tests above
    /// carry the discriminating work.
    fn open(&mut self, tys: &[ExprId]) -> (Vec<ExprId>, LocalContext) {
        let anon = self.anon_name();
        let mut ctx = LocalContext::new();
        let mut vars = Vec::with_capacity(tys.len());
        for ty in tys {
            let fv = self.fresh_fvar();
            vars.push(self.k.fvar(fv));
            ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty: *ty,
                info: BinderInfo::Default,
            });
        }
        (vars, ctx)
    }

    /// The case's predicate as a `Nat → Bool` lambda.
    fn predicate(&mut self, case: Case) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let body = match case {
            Case::GeThreeSucc => {
                let three = self.num(3);
                self.ble(three, i)
            }
            Case::LeOneSquare => {
                let one = self.num(1);
                self.ble(i, one)
            }
        };
        self.lam_fv(i_fv, nat, body)
    }

    /// The case's summand as a `Nat → Nat` lambda.
    fn summand(&mut self, case: Case) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let body = match case {
            Case::GeThreeSucc => self.succ(i),
            Case::LeOneSquare => self.mul(i, i),
        };
        self.lam_fv(i_fv, nat, body)
    }

    /// `Nat.sumRangeIf p f n` at a concrete `n`.
    fn sum_range_if(&mut self, case: Case, n_v: u32) -> ExprId {
        let p = self.p;
        let pred = self.predicate(case);
        let f = self.summand(case);
        let n = self.num(n_v);
        self.const_app(p.sum_range_if, &[pred, f, n])
    }

    /// `Nat.sumRangeIf (setCompl p) f n` at a concrete `n`.
    fn sum_range_if_compl(&mut self, case: Case, n_v: u32) -> ExprId {
        let p = self.p;
        let pred = self.predicate(case);
        let compl = self.const_app(p.set_compl, &[pred]);
        let f = self.summand(case);
        let n = self.num(n_v);
        self.const_app(p.sum_range_if, &[compl, f, n])
    }

    /// `Nat.sumRange f n` at a concrete `n`.
    fn sum_range_at(&mut self, case: Case, n_v: u32) -> ExprId {
        let f = self.summand(case);
        let n = self.num(n_v);
        self.sum_range(f, n)
    }

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }
}

/// The Rust reference itself, before anything is asked of the kernel: the
/// four readings really are different numbers at the instances used below,
/// so the `def_eq` controls that follow are not vacuous.
#[test]
fn the_reference_readings_are_distinct() {
    // `p i := 3 ≤ i`, `f i := i+1`, `n = 6`: selected `{3,4,5}` -> 4+5+6.
    assert_eq!(Case::GeThreeSucc.selected_sum(6), 15);
    assert_eq!(Case::GeThreeSucc.unselected_sum(6), 6);
    assert_eq!(Case::GeThreeSucc.full_sum(6), 21);
    // The product convention pads the three unselected indices with `1`.
    assert_eq!(Case::GeThreeSucc.one_padded_sum(6), 18);

    // `p i := i ≤ 1`, `f i := i*i`, `n = 4`: selected `{0,1}` -> 0+1.
    assert_eq!(Case::LeOneSquare.selected_sum(4), 1);
    assert_eq!(Case::LeOneSquare.unselected_sum(4), 13);
    assert_eq!(Case::LeOneSquare.full_sum(4), 14);
    assert_eq!(Case::LeOneSquare.one_padded_sum(4), 3);
}

/// **`Nat.sumRangeIf` computes the intended value**, and does NOT compute
/// either of the two wrong-but-well-typed readings: the `prodRangeIf`
/// convention (unselected index contributes `1`) or the negated predicate
/// (which is what `setCompl` selects).
#[test]
fn sum_range_if_computes_on_small_numerals() {
    let mut f = Fixture::new();

    for (case, n) in [(Case::GeThreeSucc, 6u32), (Case::LeOneSquare, 4)] {
        let term = f.sum_range_if(case, n);
        let want = case.selected_sum(n);
        assert!(
            f.reduces_to(term, want),
            "sumRangeIf must reduce to {want} at n = {n}"
        );

        // Negative control 1: the numeral one above -- so the `def_eq` above
        // is discriminating and not an "everything is equal" artefact.
        assert!(
            !f.reduces_to(term, want + 1),
            "sumRangeIf must NOT reduce to {}",
            want + 1
        );
        // Negative control 2: the product convention's value.
        let padded = case.one_padded_sum(n);
        assert_ne!(padded, want, "the two conventions must differ here");
        assert!(
            !f.reduces_to(term, padded),
            "sumRangeIf must not pad unselected indices with 1 ({padded})"
        );
        // Negative control 3: the complement's value -- the predicate is not
        // read the wrong way round.
        let flipped = case.unselected_sum(n);
        assert_ne!(flipped, want, "the two readings must differ here");
        assert!(
            !f.reduces_to(term, flipped),
            "sumRangeIf must select `p`, not its complement ({flipped})"
        );
    }
}

/// `Nat.sumRangeIf (setCompl p) f n` computes the complementary sum. This is
/// what makes the split's statement mean what it says.
#[test]
fn sum_range_if_at_the_complement_computes() {
    let mut f = Fixture::new();

    for (case, n) in [(Case::GeThreeSucc, 6u32), (Case::LeOneSquare, 4)] {
        let term = f.sum_range_if_compl(case, n);
        let want = case.unselected_sum(n);
        assert!(
            f.reduces_to(term, want),
            "sumRangeIf at setCompl must reduce to {want} at n = {n}"
        );
        let selected = case.selected_sum(n);
        assert_ne!(selected, want);
        assert!(
            !f.reduces_to(term, selected),
            "the complement must not compute the selected sum"
        );
    }
}

/// The two defining equations, instantiated: each conclusion is inferred
/// from the kernel and matched against the statement built independently
/// here, and the `succ` equation is checked at a numeral where the new term
/// is genuinely selected (`n = 3` for `3 ≤ i`) so a `succ` equation that
/// dropped the new term would be caught.
#[test]
fn the_defining_equations_hold_at_concrete_arguments() {
    let mut f = Fixture::new();
    let p = f.p;

    let case = Case::GeThreeSucc;
    let pred = f.predicate(case);
    let fun = f.summand(case);

    // `sumRangeIf p f 0 = 0`.
    {
        let inst = f.lemma(p.sum_range_if_zero, &[pred, fun]);
        let inferred = f.k.infer(inst).expect("zero equation must type-check");
        let zero = f.zero();
        let lhs = f.const_app(p.sum_range_if, &[pred, fun, zero]);
        let zero_r = f.zero();
        let expected = f.eq(lhs, zero_r);
        assert!(
            f.k.def_eq(inferred, expected),
            "the zero equation states something else"
        );
        assert!(f.reduces_to(lhs, 0), "the empty conditional sum is 0");
    }

    // `sumRangeIf p f (succ 3) = sumRangeIf p f 3 + sel (p 3) (f 3)`, where
    // `p 3` is TRUE and `f 3 = 4`: `0 + 4 = 4`.
    {
        let three = f.num(3);
        let inst = f.lemma(p.sum_range_if_succ, &[pred, fun, three]);
        let inferred = f.k.infer(inst).expect("succ equation must type-check");

        let sthree = f.succ(three);
        let lhs = f.const_app(p.sum_range_if, &[pred, fun, sthree]);
        let prior = f.const_app(p.sum_range_if, &[pred, fun, three]);
        let p3 = f.apply(pred, &[three]);
        let f3 = f.apply(fun, &[three]);
        let zero = f.zero();
        let sel = f.bool_select_nat(p3, f3, zero);
        let rhs = f.add(prior, sel);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "the succ equation states something else"
        );

        assert_eq!(case.selected_sum(3), 0);
        assert_eq!(case.selected_sum(4), 4);
        assert!(f.reduces_to(prior, 0), "nothing below 3 is selected");
        assert!(f.reduces_to(lhs, 4), "index 3 contributes f 3 = 4");
        assert!(
            !f.reduces_to(lhs, 0),
            "a succ equation that dropped the new term would give 0"
        );
    }
}

/// **The bounded congruence, at predicates that DISAGREE at the bound.**
/// `p i := ble 3 i` and `q i := ble 4 i` agree on `{0,1,2,3}`… they do not:
/// they differ at `i = 3`. The pair used here agrees strictly below `n = 3`
/// and differs at `3`, which is what makes the `Lt i n` bound load-bearing:
/// an unconditional congruence could not be applied at all.
#[test]
fn the_bounded_congruence_applies_where_the_predicates_agree_below_the_bound() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // `pp i := ble 3 i`, `qq i := ble 4 i`. They agree on `i < 3` (both
    // false) and differ at `i = 3` (true vs false).
    let pp = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let three = f.num(3);
        let body = f.ble(three, i);
        f.lam_fv(i_fv, nat, body)
    };
    let qq = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let four = f.num(4);
        let body = f.ble(four, i);
        f.lam_fv(i_fv, nat, body)
    };
    // `fun i => succ i` on both sides -- the function halves agree
    // everywhere, so only the predicate halves are under test.
    let fun = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let body = f.succ(i);
        f.lam_fv(i_fv, nat, body)
    };

    // The two sums at `n = 3` are both empty; at `n = 4` they differ, which
    // is the point of the bound.
    let n3 = f.num(3);
    let lhs3 = f.const_app(p.sum_range_if, &[pp, fun, n3]);
    let rhs3 = f.const_app(p.sum_range_if, &[qq, fun, n3]);
    assert!(f.reduces_to(lhs3, 0));
    assert!(f.reduces_to(rhs3, 0));

    let n4 = f.num(4);
    let lhs4 = f.const_app(p.sum_range_if, &[pp, fun, n4]);
    let rhs4 = f.const_app(p.sum_range_if, &[qq, fun, n4]);
    assert!(f.reduces_to(lhs4, 4), "`3 ≤ i` picks up f 3 = 4 at n = 4");
    assert!(f.reduces_to(rhs4, 0), "`4 ≤ i` picks up nothing at n = 4");
    assert!(
        !f.k.def_eq(lhs4, rhs4),
        "so the congruence must NOT be applicable at n = 4"
    );

    // Apply the congruence at `n = 3`, discharging both hypotheses. The
    // predicate hypothesis holds because `ble 3 i` and `ble 4 i` are both
    // `false` for `i < 3` -- but proving that pointwise needs the order
    // bridges, so instead the hypotheses are supplied as opaque assumptions
    // and the inferred CONCLUSION is what is checked.
    let hyp_bool = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let hyp = f.lt(i, n3);
        let pi = f.apply(pp, &[i]);
        let qi = f.apply(qq, &[i]);
        let eqn = f.bool_eq(pi, qi);
        let body = f.arrow(hyp, eqn);
        f.pi_fv(i_fv, nat, body)
    };
    let hyp_nat = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let hyp = f.lt(i, n3);
        let fi = f.apply(fun, &[i]);
        let gi = f.apply(fun, &[i]);
        let eqn = f.eq(fi, gi);
        let body = f.arrow(hyp, eqn);
        f.pi_fv(i_fv, nat, body)
    };
    let (vars, mut ctx) = f.open(&[hyp_bool, hyp_nat]);
    let inst = f.lemma(
        p.sum_range_if_congr_lt,
        &[pp, qq, fun, fun, n3, vars[0], vars[1]],
    );
    let inferred =
        f.k.infer_in(inst, &mut ctx)
            .expect("the congruence instance must type-check");
    let expected = f.eq(lhs3, rhs3);
    assert!(
        f.k.def_eq(inferred, expected),
        "the congruence's conclusion is not the equality of the two sums"
    );
}

/// **The split**, instantiated at both cases with every term evaluated:
/// `selected + unselected = full`, and the selected part alone is NOT the
/// full sum (so the theorem is not true for the trivial reason that the
/// complement contributes nothing).
#[test]
fn the_complement_split_holds_and_both_parts_are_nonempty() {
    let mut f = Fixture::new();
    let p = f.p;

    for (case, n) in [(Case::GeThreeSucc, 6u32), (Case::LeOneSquare, 4)] {
        let pred = f.predicate(case);
        let fun = f.summand(case);
        let n_e = f.num(n);
        let inst = f.lemma(p.sum_range_if_compl, &[pred, fun, n_e]);
        let inferred = f.k.infer(inst).expect("the split must type-check");

        let sel = f.sum_range_if(case, n);
        let com = f.sum_range_if_compl(case, n);
        let lhs = f.add(sel, com);
        let rhs = f.sum_range_at(case, n);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "the split states something else at n = {n}"
        );

        // Every one of the three terms reduces, so the identity is not two
        // stuck aggregates agreeing.
        assert!(f.reduces_to(sel, case.selected_sum(n)));
        assert!(f.reduces_to(com, case.unselected_sum(n)));
        assert!(f.reduces_to(rhs, case.full_sum(n)));

        // Neither part is the whole: a split whose complement contributed
        // nothing would be uninformative.
        assert_ne!(case.selected_sum(n), case.full_sum(n));
        assert_ne!(case.unselected_sum(n), case.full_sum(n));
        assert!(
            !f.k.def_eq(sel, rhs),
            "the selected part alone must not be the full sum"
        );
    }
}

/// All five declarations rest on zero axioms.
#[test]
fn the_subset_sum_declarations_rest_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;

    for name in [
        p.sum_range_if,
        p.sum_range_if_zero,
        p.sum_range_if_succ,
        p.sum_range_if_congr_lt,
        p.sum_range_if_compl,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character.
///
/// Three distinctions no numeric instance can see, which is why these pins
/// exist:
///
/// - the unselected value is `AxNat.zero`, not `AxNat.succ AxNat.zero`;
/// - the `succ` equation's new term is on the RIGHT of the `add`;
/// - the congruence's hypotheses are bounded by `AxNat.lt x4 …`, not
///   unconditional.
#[test]
fn the_subset_sum_declarations_state_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let render = |k: &mut Kernel, name| match k
        .environment()
        .get(name)
        .expect("the declaration must exist")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is neither a theorem nor a definition"),
    };

    assert_eq!(render(&mut k, p.sum_range_if), EXPECTED_SUM_RANGE_IF);
    assert_eq!(render(&mut k, p.sum_range_if_zero), EXPECTED_ZERO);
    assert_eq!(render(&mut k, p.sum_range_if_succ), EXPECTED_SUCC);
    assert_eq!(render(&mut k, p.sum_range_if_congr_lt), EXPECTED_CONGR_LT);
    assert_eq!(render(&mut k, p.sum_range_if_compl), EXPECTED_COMPL);
}

/// The definition's VALUE, pinned: the type alone cannot see the selection
/// convention at all (`(Nat → Bool) → (Nat → Nat) → Nat → Nat` is the type
/// of every wrong variant too).
#[test]
fn the_definition_selects_f_when_true_and_zero_when_false() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let value = match k
        .environment()
        .get(p.sum_range_if)
        .expect("the definition must exist")
    {
        Declaration::Definition { value, .. } => {
            let value = *value;
            k.render_lean(value)
        }
        other => panic!("{other:?} is not a definition"),
    };
    assert_eq!(value, EXPECTED_SUM_RANGE_IF_VALUE);
    // The `Bool.rec` false-branch is `AxNat.zero`; a `succ AxNat.zero` there
    // would be `prodRangeIf`'s convention.
    // `Bool.rec motive on_false on_true condition`: the FALSE branch is
    // `AxNat.zero`, the TRUE branch is `f i` (`x1 x3`), the condition `p i`.
    assert!(
        value.contains("AxNat) AxNat.zero (x1 x3) (x0 x3)"),
        "the false branch must be `zero`, the true branch `f i`, the condition `p i`"
    );
    // Negative controls on that `contains`: the product convention would put
    // `succ zero` where `zero` is, and reading the predicate the other way
    // round would swap the two branches.
    assert!(
        !value.contains("AxNat) (AxNat.succ AxNat.zero) (x1 x3) (x0 x3)"),
        "the false branch must NOT be `1` (that is `prodRangeIf`)"
    );
    assert!(
        !value.contains("AxNat) (x1 x3) AxNat.zero (x0 x3)"),
        "the branches must NOT be swapped"
    );
}

const EXPECTED_SUM_RANGE_IF: &str = "((x0 : ((x0 : AxNat) -> Bool)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> AxNat)))";
const EXPECTED_SUM_RANGE_IF_VALUE: &str = "fun (x0 : ((x0 : AxNat) -> Bool)) => fun (x1 : ((x1 : AxNat) -> AxNat)) => fun (x2 : AxNat) => AxNat.sumRange (fun (x3 : AxNat) => Bool.rec.{1} (fun (x4 : Bool) => AxNat) AxNat.zero (x1 x3) (x0 x3)) x2";
const EXPECTED_ZERO: &str = "((x0 : ((x0 : AxNat) -> Bool)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> Eq.{1} AxNat (AxNat.sumRange (fun (x2 : AxNat) => Bool.rec.{1} (fun (x3 : Bool) => AxNat) AxNat.zero (x1 x2) (x0 x2)) AxNat.zero) AxNat.zero))";
const EXPECTED_SUCC: &str = "((x0 : ((x0 : AxNat) -> Bool)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.sumRange (fun (x3 : AxNat) => Bool.rec.{1} (fun (x4 : Bool) => AxNat) AxNat.zero (x1 x3) (x0 x3)) (AxNat.succ x2)) (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => Bool.rec.{1} (fun (x4 : Bool) => AxNat) AxNat.zero (x1 x3) (x0 x3)) x2) (Bool.rec.{1} (fun (x3 : Bool) => AxNat) AxNat.zero (x1 x2) (x0 x2))))))";
const EXPECTED_CONGR_LT: &str = "((x0 : ((x0 : AxNat) -> Bool)) -> ((x1 : ((x1 : AxNat) -> Bool)) -> ((x2 : ((x2 : AxNat) -> AxNat)) -> ((x3 : ((x3 : AxNat) -> AxNat)) -> ((x4 : AxNat) -> ((x5 : ((x5 : AxNat) -> ((x6 : AxNat.lt x5 x4) -> Eq.{1} Bool (x0 x5) (x1 x5)))) -> ((x6 : ((x6 : AxNat) -> ((x7 : AxNat.lt x6 x4) -> Eq.{1} AxNat (x2 x6) (x3 x6)))) -> Eq.{1} AxNat (AxNat.sumRange (fun (x7 : AxNat) => Bool.rec.{1} (fun (x8 : Bool) => AxNat) AxNat.zero (x2 x7) (x0 x7)) x4) (AxNat.sumRange (fun (x7 : AxNat) => Bool.rec.{1} (fun (x8 : Bool) => AxNat) AxNat.zero (x3 x7) (x1 x7)) x4))))))))";
const EXPECTED_COMPL: &str = "((x0 : ((x0 : AxNat) -> Bool)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => Bool.rec.{1} (fun (x4 : Bool) => AxNat) AxNat.zero (x1 x3) (x0 x3)) x2) (AxNat.sumRange (fun (x3 : AxNat) => Bool.rec.{1} (fun (x4 : Bool) => AxNat) AxNat.zero (x1 x3) (AxNat.setCompl x0 x3)) x2)) (AxNat.sumRange x1 x2))))";
