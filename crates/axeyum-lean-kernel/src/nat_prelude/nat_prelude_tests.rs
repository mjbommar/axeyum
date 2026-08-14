//! Tests for the natural-number prelude.
//!
//! Three things are checked here, in order of importance:
//!
//! 1. **The trusted base is empty of axioms.** `build_nat_prelude` declares
//!    only inductives, definitions, and theorems; every algebraic law is a
//!    proof term the kernel re-checked at admission.
//! 2. **The kernel rejects broken proofs.** A checker that has never rejected
//!    anything is untested, so a battery of negative controls feeds the kernel
//!    swapped lemma arguments, the wrong lemma, an omitted induction step, a
//!    wrong base case, a transposed conclusion, a false identity, and a bogus
//!    order fact — and requires an `Err` plus an environment that never learned
//!    the name.
//! 3. **A downstream development can use it.** [`Fixture`] implements
//!    [`NatOps`] with the two required methods (the pattern a consumer follows)
//!    and proves a new theorem out of the prelude's lemmas.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::env::Declaration;
use crate::{ExprId, Kernel, KernelError, NameId, NatOps, NatPrelude, NatState, build_nat_prelude};

/// A downstream development: a kernel carrying the prelude, plus a name root of
/// its own. Implementing [`NatOps`] takes exactly the two required methods.
struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    root: NameId,
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
        let anon = k.anon();
        let root = k.name_str(anon, "consumer");
        Self { k, p, st, root }
    }

    /// A name in this development's own namespace.
    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

/// Every name [`build_nat_prelude`] promises, with the declaration kind it must
/// have. `Nat`/`Nat.zero`/`Nat.succ`/`Nat.rec`/`Nat.le`/… are inductive
/// machinery, so they are checked separately by `environment().contains`.
fn definition_names(p: &NatPrelude) -> Vec<NameId> {
    vec![
        p.add,
        p.mul,
        p.pow,
        p.sum_range,
        p.pred,
        p.sub,
        p.lt,
        p.in_closed_interval,
        p.dvd,
        p.valuation_at,
    ]
}

fn theorem_names(p: &NatPrelude) -> Vec<NameId> {
    vec![
        p.add_zero,
        p.add_succ,
        p.mul_zero,
        p.mul_succ,
        p.pow_zero,
        p.pow_succ,
        p.pred_zero,
        p.pred_succ,
        p.sub_zero,
        p.sub_succ,
        p.succ_sub_succ,
        p.sub_self,
        p.sum_range_zero,
        p.sum_range_succ,
        p.sum_range_congr,
        p.mul_sum_range,
        p.mul_sum_range_pow,
        p.zero_add,
        p.succ_add,
        p.add_comm,
        p.add_assoc,
        p.add_right_comm,
        p.succ_injective,
        p.add_right_cancel,
        p.add_left_cancel,
        p.zero_mul,
        p.succ_mul,
        p.mul_comm,
        p.left_distrib,
        p.mul_assoc,
        p.one_mul,
        p.mul_one,
        p.zero_le,
        p.le_succ_succ,
        p.le_of_succ_le_succ,
        p.le_trans,
        p.lt_or_eq_of_le,
        p.le_total,
        p.not_succ_le_zero,
        p.le_antisymm,
        p.le_intro,
        p.le_dest,
        p.le_add_right,
        p.add_le_add_left,
        p.add_le_add_right,
        p.le_of_add_le_add_left,
        p.le_of_add_le_add_right,
        p.mul_le_mul_left,
        p.le_of_mul_le_mul_left_succ,
        p.le_of_mul_le_mul_left,
        p.mul_left_cancel_of_pos,
        p.sub_add_cancel,
        p.sub_eq_zero_of_le,
        p.sub_le_iff_le_add,
        p.mul_sub_left_distrib,
        p.dvd_mul,
        p.dvd_add,
        p.dvd_add_right_cancel_of_pos,
        p.not_dvd_one_of_two_le,
        p.not_dvd_one_add_mul_of_two_le,
        p.valuation_at_two_mul_sq,
    ]
}

/// The honesty control: the prelude rests on **zero axioms**. Its trusted base
/// is the kernel plus the inductive declarations of the logic prelude.
#[test]
fn the_nat_prelude_declares_no_axioms() {
    let mut k = Kernel::new();
    let _p = build_nat_prelude(&mut k).expect("Nat prelude must build");
    let axioms: Vec<String> = k
        .environment()
        .iter()
        .filter_map(|(_, decl)| match decl {
            Declaration::Axiom { name, .. } => Some(k.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    println!("axiom population: {axioms:?}");
    assert!(
        axioms.is_empty(),
        "the nat prelude must rest on zero axioms, found: {axioms:?}"
    );
}

/// Every promised name is present with the promised declaration kind, and every
/// theorem statement is rendered for the record.
#[test]
fn every_promised_name_is_admitted_with_the_expected_kind() {
    let f = Fixture::new();
    let p = f.p;

    for name in definition_names(&p) {
        let display = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{display} must be admitted"));
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "{display} must be a Definition"
        );
        let ty = decl.ty();
        println!("def {display} : {}", f.k.render_lean(ty));
    }

    for name in theorem_names(&p) {
        let display = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{display} must be admitted"));
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{display} must be a checked Theorem"
        );
        let ty = decl.ty();
        println!("theorem {display} : {}", f.k.render_lean(ty));
    }

    // The inductive machinery the definitions and proofs ride on.
    for name in [
        p.nat, p.zero, p.succ, p.rec, p.le, p.le_refl, p.le_step, p.le_rec,
    ] {
        let display = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{display} must be in the environment"
        );
    }
    let le_rec_ty = f.k.environment().get(p.le_rec).expect("Nat.le.rec").ty();
    println!("Nat.le.rec : {}", f.k.render_lean(le_rec_ty));
}

/// The definitions **compute**: the kernel's own `def_eq` (δ/β/ι) reduces closed
/// arithmetic to numerals. The negative half matters as much as the positive
/// one — `def_eq` must not be vacuously true.
#[test]
fn arithmetic_reduces_on_numerals() {
    let mut f = Fixture::new();

    let two = f.num(2);
    let three = f.num(3);
    let sum = f.add(two, three);
    let five = f.num(5);
    assert!(f.k.def_eq(sum, five), "add 2 3 must reduce to 5");

    let four = f.num(4);
    let prod = f.mul(three, four);
    let twelve = f.num(12);
    assert!(f.k.def_eq(prod, twelve), "mul 3 4 must reduce to 12");

    let five_again = f.num(5);
    let power = f.pow(two, five_again);
    let thirty_two = f.num(32);
    assert!(f.k.def_eq(power, thirty_two), "pow 2 5 must reduce to 32");

    let cube = f.pow(three, three);
    let twenty_seven = f.num(27);
    assert!(f.k.def_eq(cube, twenty_seven), "pow 3 3 must reduce to 27");

    let subtraction_zero = f.zero();
    let zero_pred = f.pred(subtraction_zero);
    assert!(
        f.k.def_eq(zero_pred, subtraction_zero),
        "pred 0 must reduce to 0"
    );
    let pred_four = f.pred(four);
    assert!(f.k.def_eq(pred_four, three), "pred 4 must reduce to 3");
    let seven = f.num(7);
    let seven_sub_three = f.sub(seven, three);
    assert!(f.k.def_eq(seven_sub_three, four), "7 - 3 must reduce to 4");
    let two_sub_five = f.sub(two, five);
    assert!(
        f.k.def_eq(two_sub_five, subtraction_zero),
        "2 - 5 must truncate to 0"
    );

    let six = f.num(6);
    let i_fv = f.fresh_fvar();
    let i = f.k.fvar(i_fv);
    let nat = f.nat_ty();
    let identity = f.lam_fv(i_fv, nat, i);
    let zero = f.zero();
    let empty = f.sum_range(identity, zero);
    assert!(
        f.k.def_eq(empty, zero),
        "the empty range sum must reduce to 0"
    );
    let first_four = f.sum_range(identity, four);
    assert!(
        f.k.def_eq(first_four, six),
        "sumRange identity 4 must reduce to 0+1+2+3 = 6"
    );

    // NEGATIVE reduction controls.
    assert!(!f.k.def_eq(sum, six), "add 2 3 must NOT be def-eq to 6");
    let twenty_six = f.num(26);
    assert!(
        !f.k.def_eq(cube, twenty_six),
        "pow 3 3 must NOT be def-eq to 26"
    );
    assert!(
        !f.k.def_eq(first_four, five),
        "sumRange identity 4 must NOT be def-eq to 5"
    );
    assert!(
        !f.k.def_eq(seven_sub_three, five),
        "7 - 3 must NOT be def-eq to 5"
    );
}

/// Checked predecessor elimination supports successor injectivity and both
/// orientations of additive cancellation in downstream proof terms.
#[test]
fn additive_cancellation_is_checked_and_reusable() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let zero = f.zero();
    let zero_plus_two = f.add(zero, two);
    let zero_add_two = f.lemma(p.zero_add, &[two]);

    let succ_eq = f.congr(zero_plus_two, two, zero_add_two, &|d, n| d.succ(n));
    let injective = f.lemma(p.succ_injective, &[zero_plus_two, two, succ_eq]);
    let injective_name = f.name("succ_two_injective");
    let zero_plus_two_eq_two = f.eq(zero_plus_two, two);
    f.declare_theorem(injective_name, zero_plus_two_eq_two, injective)
        .unwrap_or_else(|e| panic!("successor injectivity should admit: {}", f.explain(&e)));

    let right_h = f.congr(zero_plus_two, two, zero_add_two, &|d, n| d.add(n, five));
    let right = f.lemma(p.add_right_cancel, &[zero_plus_two, two, five, right_h]);
    let right_name = f.name("cancel_right_five");
    f.declare_theorem(right_name, zero_plus_two_eq_two, right)
        .unwrap_or_else(|e| panic!("right cancellation should admit: {}", f.explain(&e)));

    let left_h = f.congr(zero_plus_two, two, zero_add_two, &|d, n| d.add(three, n));
    let left = f.lemma(p.add_left_cancel, &[three, zero_plus_two, two, left_h]);
    let left_name = f.name("cancel_left_three");
    f.declare_theorem(left_name, zero_plus_two_eq_two, left)
        .unwrap_or_else(|e| panic!("left cancellation should admit: {}", f.explain(&e)));
}

/// Order evidence discharges the side condition under which truncated
/// subtraction restores the original minuend.
#[test]
fn conditional_subtraction_restores_bounded_minuends() {
    let mut f = Fixture::new();
    let p = f.p;
    let three = f.num(3);
    let four = f.num(4);
    let seven = f.num(7);

    let three_le_seven = f.lemma(p.le_add_right, &[three, four]);
    let restored = f.lemma(p.sub_add_cancel, &[three, seven, three_le_seven]);
    let difference = f.sub(seven, three);
    let lhs = f.add(difference, three);
    let stmt = f.eq(lhs, seven);
    let name = f.name("seven_sub_three_add_three");
    f.declare_theorem(name, stmt, restored)
        .unwrap_or_else(|e| panic!("bounded subtraction should restore: {}", f.explain(&e)));

    let self_le = f.const_app(p.le_refl, &[three]);
    let self_restored = f.lemma(p.sub_add_cancel, &[three, three, self_le]);
    let self_difference = f.sub(three, three);
    let self_lhs = f.add(self_difference, three);
    let self_stmt = f.eq(self_lhs, three);
    let self_name = f.name("three_sub_three_add_three");
    f.declare_theorem(self_name, self_stmt, self_restored)
        .unwrap_or_else(|e| panic!("equal-bound subtraction should restore: {}", f.explain(&e)));
}

/// Scaling a bounded truncated difference agrees with subtracting the scaled
/// endpoints; this is the generic algebra needed by the paper witness.
#[test]
fn bounded_subtraction_distributes_under_left_multiplication() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let seven = f.num(7);
    let bound = f.lemma(p.le_add_right, &[two, five]);
    let proof = f.lemma(p.mul_sub_left_distrib, &[three, seven, two, bound]);
    let difference = f.sub(seven, two);
    let lhs = f.mul(three, difference);
    let scaled_q = f.mul(three, seven);
    let scaled_a = f.mul(three, two);
    let rhs = f.sub(scaled_q, scaled_a);
    let stmt = f.eq(lhs, rhs);
    let name = f.name("three_times_seven_sub_two");
    f.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("scaled bounded subtraction should admit: {}", f.explain(&e)));
    let fifteen = f.num(15);
    assert!(f.k.def_eq(lhs, fifteen));
    assert!(f.k.def_eq(rhs, fifteen));
}

/// The generic checked reindexing theorem covers both the empty `k = 3`
/// corner and a nonempty geometric sum used by the Rado sharpness proof.
#[test]
fn geometric_sum_reindexing_is_checked() {
    let mut f = Fixture::new();
    let p = f.p;
    let three = f.num(3);
    let zero = f.zero();
    let empty_proof = f.lemma(p.mul_sum_range_pow, &[three, zero]);
    let empty_name = f.name("empty_geometric_reindex");
    let empty_ty = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let power = f.pow(three, i);
        let nat = f.nat_ty();
        let powers = f.lam_fv(i_fv, nat, power);
        let sum = f.sum_range(powers, zero);
        let lhs = f.mul(three, sum);
        f.eq(lhs, zero)
    };
    f.declare_theorem(empty_name, empty_ty, empty_proof)
        .unwrap_or_else(|e| panic!("empty reindexing should admit: {}", f.explain(&e)));

    let four = f.num(4);
    let proof = f.lemma(p.mul_sum_range_pow, &[three, four]);
    let name = f.name("three_power_reindex_four");
    let declared =
        f.k.environment()
            .get(p.mul_sum_range_pow)
            .expect("reindexing theorem is present")
            .ty();
    println!("Nat.mul_sumRange_pow : {}", f.k.render_lean(declared));
    let applied_ty = f.k.infer(proof).expect("applied reindexing proof infers");
    let theorem = f.k.const_(p.mul_sum_range_pow, vec![]);
    let expected = {
        let at_a = f.k.app(theorem, three);
        f.k.app(at_a, four)
    };
    let expected_ty = f.k.infer(expected).expect("application infers");
    assert!(f.k.def_eq(applied_ty, expected_ty));
    f.declare_theorem(name, applied_ty, proof)
        .unwrap_or_else(|e| panic!("nonempty reindexing should admit: {}", f.explain(&e)));
}

/// Scalar distribution is generic in the summand, so downstream mathematics
/// can reuse it without introducing a Rado-specific recurrence.
#[test]
fn scalar_multiplication_distributes_over_finite_ranges() {
    let mut f = Fixture::new();
    let p = f.p;
    let three = f.num(3);
    let four = f.num(4);
    let i_fv = f.fresh_fvar();
    let i = f.k.fvar(i_fv);
    let nat = f.nat_ty();
    let identity = f.lam_fv(i_fv, nat, i);
    let proof = f.lemma(p.mul_sum_range, &[three, identity, four]);
    let ty = f.k.infer(proof).expect("distribution proof infers");
    let name = f.name("three_distributes_over_first_four");
    f.declare_theorem(name, ty, proof)
        .unwrap_or_else(|e| panic!("finite-sum distribution should admit: {}", f.explain(&e)));

    let sum = f.sum_range(identity, four);
    let lhs = f.mul(three, sum);
    let eighteen = f.num(18);
    assert!(f.k.def_eq(lhs, eighteen), "3 * (0+1+2+3) must reduce to 18");
}

/// Pointwise equality lifts through a finite range without assuming function
/// extensionality.
#[test]
fn pointwise_equality_lifts_through_finite_ranges() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let i_fv = f.fresh_fvar();
    let i = f.k.fvar(i_fv);
    let nat = f.nat_ty();
    let zero_plus_i = f.add(zero, i);
    let lhs_fn = f.lam_fv(i_fv, nat, zero_plus_i);
    let j_fv = f.fresh_fvar();
    let j = f.k.fvar(j_fv);
    let rhs_fn = f.lam_fv(j_fv, nat, j);
    let h_fv = f.fresh_fvar();
    let h_i = f.k.fvar(h_fv);
    let h_body = f.lemma(p.zero_add, &[h_i]);
    let pointwise = f.lam_fv(h_fv, nat, h_body);
    let four = f.num(4);
    let proof = f.lemma(p.sum_range_congr, &[lhs_fn, rhs_fn, four, pointwise]);
    let ty = f.k.infer(proof).expect("sum congruence proof infers");
    let name = f.name("sum_zero_add_congr");
    f.declare_theorem(name, ty, proof)
        .unwrap_or_else(|e| panic!("sum congruence should admit: {}", f.explain(&e)));
}

/// A downstream development proves something new out of the prelude's lemmas:
/// `∀ n, 2 * n = n + n`, by `succ_mul` and `one_mul`.
#[test]
fn a_downstream_development_proves_a_new_theorem() {
    let mut f = Fixture::new();
    let p = f.p;
    let name = f.name("two_mul");
    let ty = f
        .theorem(name, 1, &|d, v| {
            let n = v[0];
            let two = d.num(2);
            let one = d.num(1);
            let start = d.mul(two, n);
            // mul (succ 1) n = add (mul 1 n) n
            let one_n = d.mul(one, n);
            let s1 = d.add(one_n, n);
            let h1 = d.lemma(p.succ_mul, &[one, n]);
            // ... = add n n
            let s2 = d.add(n, n);
            let h_om = d.lemma(p.one_mul, &[n]);
            let h2 = d.congr(one_n, n, h_om, &|d, t| d.add(t, n));
            let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
            assert_eq!(end, s2, "the chain must land on `add n n`");
            let stmt = d.eq(start, end);
            (stmt, proof)
        })
        .expect("derived Nat theorem must check");
    println!("two_mul : {}", f.k.render_lean(ty));
    assert!(matches!(
        f.k.environment().get(name),
        Some(Declaration::Theorem { .. })
    ));
}

/// The order fragment is usable on concrete bounds: `le_add_right 1 2` has type
/// `Le 1 (add 1 2)`, and `add 1 2 ≡ 3`, so the kernel accepts it as a proof of
/// `Le 1 3`. `le_trans` then chains it to `Le 1 4`; strict order reduces to
/// successor `le`, and successor monotonicity can be inverted again.
#[test]
fn the_order_fragment_bounds_concrete_numerals() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);

    let stmt = f.le(one, three);
    let proof = f.lemma(p.le_add_right, &[one, two]);
    let name = f.name("one_le_three");
    f.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("one_le_three should admit: {}", f.explain(&e)));
    println!("one_le_three : {}", f.k.render_lean(stmt));

    // Le 3 4 from the step constructor, then Le 1 4 by transitivity.
    let three_le_four = {
        let refl3 = f.const_app(p.le_refl, &[three]);
        f.const_app(p.le_step, &[three, three, refl3])
    };
    let one_le_three = f.const_app(name, &[]);
    let stmt2 = f.le(one, four);
    let proof2 = f.lemma(p.le_trans, &[one, three, four, one_le_three, three_le_four]);
    let name2 = f.name("one_le_four");
    f.declare_theorem(name2, stmt2, proof2)
        .unwrap_or_else(|e| panic!("one_le_four should admit: {}", f.explain(&e)));
    println!("one_le_four : {}", f.k.render_lean(stmt2));

    let two_lt_four = f.lt(two, four);
    let three_le_four_ty = f.le(three, four);
    assert!(
        f.k.def_eq(two_lt_four, three_le_four_ty),
        "2 < 4 must reduce to 3 ≤ 4"
    );

    let lifted = f.lemma(p.le_succ_succ, &[one, three, one_le_three]);
    let inverted = f.lemma(p.le_of_succ_le_succ, &[one, three, lifted]);
    let inversion_name = f.name("one_le_three_by_inversion");
    f.declare_theorem(inversion_name, stmt, inverted)
        .unwrap_or_else(|e| panic!("successor inversion should admit: {}", f.explain(&e)));
}

/// Addition and multiplication preserve checked order evidence under a fixed
/// left operand, providing reusable range arithmetic for later developments.
#[test]
fn order_is_monotone_under_left_addition_and_multiplication() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let h = f.lemma(p.le_add_right, &[two, three]);

    let add_proof = f.lemma(p.add_le_add_left, &[four, two, five, h]);
    let six = f.num(6);
    let nine = f.num(9);
    let add_stmt = f.le(six, nine);
    let add_name = f.name("four_plus_two_le_four_plus_five");
    f.declare_theorem(add_name, add_stmt, add_proof)
        .unwrap_or_else(|e| panic!("addition monotonicity should admit: {}", f.explain(&e)));

    let mul_proof = f.lemma(p.mul_le_mul_left, &[three, two, five, h]);
    let fifteen = f.num(15);
    let mul_stmt = f.le(six, fifteen);
    let mul_name = f.name("three_times_two_le_three_times_five");
    f.declare_theorem(mul_name, mul_stmt, mul_proof)
        .unwrap_or_else(|e| {
            panic!(
                "multiplication monotonicity should admit: {}",
                f.explain(&e)
            )
        });
}

#[test]
fn order_is_total() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let five = f.num(5);
    let proof = f.lemma(p.le_total, &[five, two]);
    f.k.infer(proof)
        .unwrap_or_else(|e| panic!("totality application should infer: {}", f.explain(&e)));

    let three = f.num(3);
    let two_plus_three = f.add(two, three);
    let forward = f.lemma(p.le_refl, &[two_plus_three]);
    let reverse = f.lemma(p.le_refl, &[five]);
    let equality = f.lemma(p.le_antisymm, &[two_plus_three, five, forward, reverse]);
    f.k.infer(equality)
        .unwrap_or_else(|e| panic!("antisymmetry application should infer: {}", f.explain(&e)));

    let one = f.num(1);
    let lower = f.lemma(p.le_add_right, &[two, one]);
    let two_more = f.num(2);
    let upper = f.lemma(p.le_add_right, &[three, two_more]);
    let interval = f.in_closed_interval(two, five, three);
    let lower_ty = f.le(two, three);
    let upper_ty = f.le(three, five);
    let interval_proof = f.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper]);
    let interval_name = f.name("three_mem_two_five");
    f.declare_theorem(interval_name, interval, interval_proof)
        .unwrap_or_else(|e| panic!("closed interval membership should admit: {}", f.explain(&e)));

    let two_le_five = f.lemma(p.le_add_right, &[two, three]);
    let split = f.lemma(p.lt_or_eq_of_le, &[two, five, two_le_five]);
    f.k.infer(split).unwrap_or_else(|e| {
        panic!(
            "strict-or-equal decomposition should infer: {}",
            f.explain(&e)
        )
    });
}

#[test]
fn order_bounds_round_trip_through_additive_witnesses() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let nine = f.num(9);
    let h = f.lemma(p.le_add_right, &[two, three]);
    let represented = f.lemma(p.le_dest, &[two, five, h]);
    f.k.infer(represented)
        .unwrap_or_else(|e| panic!("order witness should infer: {}", f.explain(&e)));

    let six = f.num(6);
    let sum_eq = f.refl(five);
    let rebuilt = f.lemma(p.le_intro, &[two, five, three, sum_eq]);
    let reflected = {
        let shifted = f.lemma(p.add_le_add_left, &[four, two, five, rebuilt]);
        f.lemma(p.le_of_add_le_add_left, &[four, two, five, shifted])
    };
    let stmt = f.le(two, five);
    let name = f.name("reflected_two_le_five");
    f.declare_theorem(name, stmt, reflected)
        .unwrap_or_else(|e| panic!("additive order reflection should admit: {}", f.explain(&e)));
    let four_plus_two = f.add(four, two);
    let four_plus_five = f.add(four, five);
    assert!(f.k.def_eq(six, four_plus_two));
    assert!(f.k.def_eq(nine, four_plus_five));

    let shifted_right = f.lemma(p.add_le_add_right, &[four, two, five, rebuilt]);
    let reflected_right = f.lemma(p.le_of_add_le_add_right, &[four, two, five, shifted_right]);
    f.k.infer(reflected_right)
        .unwrap_or_else(|e| panic!("right-additive reflection should infer: {}", f.explain(&e)));

    let sub_zero = f.lemma(p.sub_eq_zero_of_le, &[two, five, rebuilt]);
    f.k.infer(sub_zero).unwrap_or_else(|e| {
        panic!(
            "bounded reverse subtraction should infer: {}",
            f.explain(&e)
        )
    });
    let adjunction = f.lemma(p.sub_le_iff_le_add, &[five, two, four]);
    f.k.infer(adjunction)
        .unwrap_or_else(|e| panic!("subtraction adjunction should infer: {}", f.explain(&e)));
}

#[test]
fn positive_successor_multiplication_reflects_order() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let six = f.num(6);
    let nine = f.num(9);
    let fifteen = f.num(15);
    let exclusion = f.lemma(p.not_succ_le_zero, &[two]);
    f.k.infer(exclusion)
        .unwrap_or_else(|e| panic!("successor exclusion should infer: {}", f.explain(&e)));
    let scaled = f.lemma(p.le_add_right, &[six, nine]);
    let reflected = f.lemma(p.le_of_mul_le_mul_left_succ, &[two, two, five, scaled]);
    let stmt = f.le(two, five);
    let name = f.name("cancel_three_from_six_le_fifteen");
    f.declare_theorem(name, stmt, reflected)
        .unwrap_or_else(|e| panic!("positive multiplication should reflect: {}", f.explain(&e)));
    let three_times_two = f.mul(three, two);
    let three_times_five = f.mul(three, five);
    assert!(f.k.def_eq(six, three_times_two));
    assert!(f.k.def_eq(fifteen, three_times_five));

    let one = f.num(1);
    let positive = f.lemma(p.le_add_right, &[one, two]);
    let reflected_from_bound = f.lemma(
        p.le_of_mul_le_mul_left,
        &[three, two, five, positive, scaled],
    );
    let bounded_name = f.name("cancel_positive_bounded_factor");
    f.declare_theorem(bounded_name, stmt, reflected_from_bound)
        .unwrap_or_else(|e| panic!("bounded positive factor should reflect: {}", f.explain(&e)));

    let product_equality = f.refl(six);
    let cancelled_equality = f.lemma(
        p.mul_left_cancel_of_pos,
        &[three, two, two, positive, product_equality],
    );
    f.k.infer(cancelled_equality).unwrap_or_else(|e| {
        panic!(
            "positive multiplication equality should cancel: {}",
            f.explain(&e)
        )
    });
}

/// Divisibility is a real prelude definition, not a test-only proposition:
/// witness introduction proves `2 ∣ 6`, and `dvd_add` composes proofs of
/// `2 ∣ 4` and `2 ∣ 6` into a checked proof of `2 ∣ 10`.
#[test]
fn divisibility_introduction_and_addition_are_checked() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let ten = f.num(10);

    let two_dvd_six = f.dvd(two, six);
    let proof = f.lemma(p.dvd_mul, &[two, three]);
    let six_name = f.name("two_dvd_six");
    f.declare_theorem(six_name, two_dvd_six, proof)
        .unwrap_or_else(|e| panic!("2 ∣ 6 should admit: {}", f.explain(&e)));

    let two_again = f.num(2);
    let h4 = f.lemma(p.dvd_mul, &[two, two_again]);
    let h6 = f.const_app(six_name, &[]);
    let two_dvd_ten = f.dvd(two, ten);
    let proof_add = f.lemma(p.dvd_add, &[two, four, six, h4, h6]);
    let ten_name = f.name("two_dvd_ten");
    f.declare_theorem(ten_name, two_dvd_ten, proof_add)
        .unwrap_or_else(|e| panic!("2 ∣ 10 should admit: {}", f.explain(&e)));

    let one = f.num(1);
    let positive = f.lemma(p.le_add_right, &[one, one]);
    let h10 = f.const_app(ten_name, &[]);
    let cancelled = f.lemma(
        p.dvd_add_right_cancel_of_pos,
        &[two, four, six, positive, h4, h10],
    );
    f.k.infer(cancelled).unwrap_or_else(|e| {
        panic!(
            "positive divisibility cancellation should infer: {}",
            f.explain(&e)
        )
    });

    let two_le_two = f.lemma(p.le_refl, &[two]);
    let not_dvd_one = f.lemma(p.not_dvd_one_of_two_le, &[two, two_le_two]);
    f.k.infer(not_dvd_one)
        .unwrap_or_else(|e| panic!("2 ∤ 1 should infer: {}", f.explain(&e)));
    let not_dvd_one_plus_six = f.lemma(p.not_dvd_one_add_mul_of_two_le, &[two, three, two_le_two]);
    f.k.infer(not_dvd_one_plus_six)
        .unwrap_or_else(|e| panic!("2 ∤ 1+2*3 should infer: {}", f.explain(&e)));
    let two_times_three = f.mul(two, three);
    let u = f.add(one, two_times_three);
    let exact_two = f.lemma(
        p.valuation_at_two_mul_sq,
        &[two, u, two_le_two, not_dvd_one_plus_six],
    );
    f.k.infer(exact_two).unwrap_or_else(|e| {
        panic!(
            "the square multiple should have valuation two: {}",
            f.explain(&e)
        )
    });
}

/// NEGATIVE CONTROLS. Each feeds the kernel a deliberately broken proof and
/// requires a rejection; the verbatim rejection is printed so the failure mode
/// is on the record, and the rejected name must never reach the environment.
#[test]
fn kernel_rejects_broken_proof_terms() {
    let mut rejections = 0usize;
    let mut f = Fixture::new();
    let p = f.p;

    // NC1 — SWAPPED LEMMA ARGUMENTS. The goal `(a*b)*b = a*(b*b)` is
    // `mul_assoc a b b`; feed it `mul_assoc b a b : (b*a)*b = b*(a*b)`.
    {
        let name = f.name("nc1_swapped_lemma_arguments");
        let err = f
            .try_theorem(name, 2, &|d, v| {
                let (a, b) = (v[0], v[1]);
                let ab = d.mul(a, b);
                let lhs = d.mul(ab, b);
                let bb = d.mul(b, b);
                let rhs = d.mul(a, bb);
                let stmt = d.eq(lhs, rhs);
                let proof = d.lemma(p.mul_assoc, &[b, a, b]); // WRONG order
                (stmt, proof)
            })
            .expect_err("NC1: swapped lemma arguments must be rejected");
        println!(
            "NC1 (swapped lemma arguments) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(matches!(err, KernelError::DeclarationValueMismatch { .. }));
        assert!(
            !f.k.environment().contains(name),
            "a rejected declaration must never reach the environment"
        );
        rejections += 1;
    }

    // NC2 — THE WRONG LEMMA. `mul n m = mul m n` proved with `add_comm n m`.
    {
        let name = f.name("nc2_wrong_lemma");
        let err = f
            .try_theorem(name, 2, &|d, v| {
                let (n, m) = (v[0], v[1]);
                let lhs = d.mul(n, m);
                let rhs = d.mul(m, n);
                let stmt = d.eq(lhs, rhs);
                let proof = d.lemma(p.add_comm, &[n, m]); // WRONG lemma
                (stmt, proof)
            })
            .expect_err("NC2: the wrong lemma must be rejected");
        println!("NC2 (wrong lemma) rejected:\n  {}", f.explain(&err));
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC3 — OMITTED INDUCTION STEP. `zero_add`'s successor case needs the
    // induction hypothesis transported under `succ`; hand back the hypothesis.
    {
        let name = f.name("nc3_omitted_induction_step");
        let err = f
            .try_theorem(name, 1, &|d, v| {
                let n = v[0];
                let motive = |d: &mut Fixture, x: ExprId| {
                    let z = d.zero();
                    let lhs = d.add(z, x);
                    d.eq(lhs, x)
                };
                let stmt = motive(d, n);
                let proof = d.induct(
                    &motive,
                    &|d| {
                        let z = d.zero();
                        d.refl(z)
                    },
                    &|_d, _j, ih| ih, // missing the `congr succ` transport
                    n,
                );
                (stmt, proof)
            })
            .expect_err("NC3: an omitted induction step must be rejected");
        println!(
            "NC3 (omitted induction step) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC4 — WRONG BASE CASE. The same induction with `refl 1` where the zero
    // case demands `add zero zero = zero`.
    {
        let name = f.name("nc4_wrong_base_case");
        let err = f
            .try_theorem(name, 1, &|d, v| {
                let n = v[0];
                let motive = |d: &mut Fixture, x: ExprId| {
                    let z = d.zero();
                    let lhs = d.add(z, x);
                    d.eq(lhs, x)
                };
                let stmt = motive(d, n);
                let proof = d.induct(
                    &motive,
                    &|d| {
                        let one = d.num(1); // WRONG: the zero case is about `zero`
                        d.refl(one)
                    },
                    &|d, j, ih| {
                        let z = d.zero();
                        let lhs = d.add(z, j);
                        d.congr(lhs, j, ih, &|d, x| d.succ(x))
                    },
                    n,
                );
                (stmt, proof)
            })
            .expect_err("NC4: a wrong base case must be rejected");
        println!("NC4 (wrong base case) rejected:\n  {}", f.explain(&err));
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC5 — TRANSPOSED CONCLUSION. `succ_mul` proves `= add (mul n m) m`; claim
    // the transposed `= add m (mul n m)` with the unmodified proof term. (The
    // claim is *true* — by `add_comm` — but this proof does not establish it,
    // and the two sides are not definitionally equal.)
    {
        let name = f.name("nc5_transposed_conclusion");
        let err = f
            .try_theorem(name, 2, &|d, v| {
                let (n, m) = (v[0], v[1]);
                let sn = d.succ(n);
                let lhs = d.mul(sn, m);
                let nm = d.mul(n, m);
                let rhs = d.add(m, nm); // transposed
                let stmt = d.eq(lhs, rhs);
                let proof = d.lemma(p.succ_mul, &[n, m]);
                (stmt, proof)
            })
            .expect_err("NC5: a transposed conclusion must be rejected");
        println!(
            "NC5 (transposed conclusion) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC6 — FALSE IDENTITY WITH A `refl` PROOF: `mul a b = add a b`.
    {
        let name = f.name("nc6_mul_is_add");
        let err = f
            .try_theorem(name, 2, &|d, v| {
                let (a, b) = (v[0], v[1]);
                let lhs = d.mul(a, b);
                let rhs = d.add(a, b);
                let stmt = d.eq(lhs, rhs);
                let proof = d.refl(lhs);
                (stmt, proof)
            })
            .expect_err("NC6: `mul = add` must be rejected");
        println!(
            "NC6 (false identity, refl proof) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC7 — BOGUS ORDER FACT. `Le (succ n) n` from `Le.refl n`; the constructor
    // produces `Le n n`, and no derivation of `succ n ≤ n` exists.
    {
        let name = f.name("nc7_succ_le_self");
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let sn = f.succ(n);
        let bad = f.le(sn, n);
        let bogus = f.const_app(p.le_refl, &[n]);
        let nat = f.nat_ty();
        let ty = f.pi_fv(n_fv, nat, bad);
        let value = f.lam_fv(n_fv, nat, bogus);
        let err = f
            .declare_theorem(name, ty, value)
            .expect_err("NC7: `Le (succ n) n` must be rejected");
        println!("NC7 (bogus order fact) rejected:\n  {}", f.explain(&err));
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC8 — A TRUE-BUT-UNPROVED BOUND: `le_add_right 1 2 : Le 1 (add 1 2)`
    // cannot pass as `Le 3 1` (the reduct `Le 1 3` is the other way round).
    {
        let name = f.name("nc8_reversed_bound");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let bad = f.le(three, one);
        let proof = f.lemma(p.le_add_right, &[one, two]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC8: a reversed bound must be rejected");
        println!("NC8 (reversed bound) rejected:\n  {}", f.explain(&err));
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC9 — `dvd_add` proves closure under addition, not multiplication. Feed
    // its proof of `2 ∣ 4 + 6` to the false goal `2 ∣ 4 * 6 + 1`.
    {
        let name = f.name("nc9_dvd_add_wrong_target");
        let two = f.num(2);
        let two_again = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let six = f.num(6);
        let h4 = f.lemma(p.dvd_mul, &[two, two_again]);
        let h6 = f.lemma(p.dvd_mul, &[two, three]);
        let proof = f.lemma(p.dvd_add, &[two, four, six, h4, h6]);
        let product = f.mul(four, six);
        let one = f.num(1);
        let bad_target = f.add(product, one);
        let bad = f.dvd(two, bad_target);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC9: dvd_add must not prove divisibility of a wrong target");
        println!(
            "NC9 (wrong divisibility target) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC10 — successor inversion recovers exactly the predecessor bound. A
    // proof of `1 ≤ 3` obtained by lifting and inversion cannot prove `4 ≤ 2`.
    {
        let name = f.name("nc10_inversion_wrong_target");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let h13 = f.lemma(p.le_add_right, &[one, two]);
        let lifted = f.lemma(p.le_succ_succ, &[one, three, h13]);
        let proof = f.lemma(p.le_of_succ_le_succ, &[one, three, lifted]);
        let bad = f.le(four, two);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC10: inversion must not change the predecessor target");
        println!(
            "NC10 (wrong inversion target) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC11 — the successor equation identifies the newly appended summand; it
    // cannot prove the unrelated claim that the same sum equals zero.
    {
        let name = f.name("nc11_sum_range_wrong_target");
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let nat = f.nat_ty();
        let identity = f.lam_fv(i_fv, nat, i);
        let two = f.num(2);
        let proof = f.lemma(p.sum_range_succ, &[identity, two]);
        let three = f.num(3);
        let sum_three = f.sum_range(identity, three);
        let zero = f.zero();
        let bad = f.eq(sum_three, zero);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC11: the sum successor equation must retain its target");
        println!(
            "NC11 (wrong finite-sum target) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC12 — the checked power-sum shift preserves the exact range length; it
    // cannot establish the corresponding statement with one extra summand.
    {
        let name = f.name("nc12_power_sum_shift_wrong_range");
        let two = f.num(2);
        let three = f.num(3);
        let proof = f.lemma(p.mul_sum_range_pow, &[two, two]);
        let theorem = f.k.const_(p.mul_sum_range_pow, vec![]);
        let at_a = f.k.app(theorem, two);
        let wrong = f.k.app(at_a, three);
        let bad = f.k.infer(wrong).expect("wrong-range target still infers");
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC12: reindexing must retain the exact range length");
        println!(
            "NC12 (wrong reindexing range) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC13 — scalar distribution retains the scalar. A proof for multiplication
    // by two cannot be assigned the proposition for multiplication by three.
    {
        let name = f.name("nc13_sum_distribution_wrong_scalar");
        let two = f.num(2);
        let three = f.num(3);
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let nat = f.nat_ty();
        let identity = f.lam_fv(i_fv, nat, i);
        let proof = f.lemma(p.mul_sum_range, &[two, identity, three]);
        let theorem = f.k.const_(p.mul_sum_range, vec![]);
        let at_scalar = f.k.app(theorem, three);
        let at_function = f.k.app(at_scalar, identity);
        let wrong = f.k.app(at_function, three);
        let bad = f.k.infer(wrong).expect("wrong-scalar target infers");
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC13: distribution must retain the exact scalar");
        println!(
            "NC13 (wrong distribution scalar) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC14 — sum congruence retains the exact range. A proof over two terms
    // cannot be assigned the inferred proposition over three terms.
    {
        let name = f.name("nc14_sum_congruence_wrong_range");
        let zero = f.zero();
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let nat = f.nat_ty();
        let zero_plus_i = f.add(zero, i);
        let lhs_fn = f.lam_fv(i_fv, nat, zero_plus_i);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let rhs_fn = f.lam_fv(j_fv, nat, j);
        let h_fv = f.fresh_fvar();
        let h_i = f.k.fvar(h_fv);
        let h_body = f.lemma(p.zero_add, &[h_i]);
        let pointwise = f.lam_fv(h_fv, nat, h_body);
        let two = f.num(2);
        let three = f.num(3);
        let proof = f.lemma(p.sum_range_congr, &[lhs_fn, rhs_fn, two, pointwise]);
        let theorem = f.k.const_(p.sum_range_congr, vec![]);
        let at_lhs = f.k.app(theorem, lhs_fn);
        let at_rhs = f.k.app(at_lhs, rhs_fn);
        let at_range = f.k.app(at_rhs, three);
        let wrong = f.k.app(at_range, pointwise);
        let bad = f.k.infer(wrong).expect("wrong-range target infers");
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC14: sum congruence must retain the exact range");
        println!(
            "NC14 (wrong congruence range) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC15 — cancellation preserves equality orientation. The checked proof
    // returns `b = c`; it cannot be assigned the untransported target `c = b`.
    {
        let name = f.name("nc15_add_left_cancel_wrong_orientation");
        let err = f
            .try_theorem(name, 3, &|d, v| {
                let (a, b, c) = (v[0], v[1], v[2]);
                let ab = d.add(a, b);
                let ac = d.add(a, c);
                let hyp_ty = d.eq(ab, ac);
                let h_fv = d.fresh_fvar();
                let h = d.k.fvar(h_fv);
                let body = d.lemma(p.add_left_cancel, &[a, b, c, h]);
                let proof = d.lam_fv(h_fv, hyp_ty, body);
                let wrong = d.eq(c, b);
                let stmt = d.arrow(hyp_ty, wrong);
                (stmt, proof)
            })
            .expect_err("NC15: cancellation result orientation must be checked");
        println!(
            "NC15 (wrong cancellation orientation) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC16 — the order-conditioned restoration proof retains its exact
    // minuend. A valid proof restoring seven cannot establish a target of six.
    {
        let name = f.name("nc16_sub_add_cancel_wrong_minuend");
        let three = f.num(3);
        let four = f.num(4);
        let six = f.num(6);
        let seven = f.num(7);
        let bound = f.lemma(p.le_add_right, &[three, four]);
        let proof = f.lemma(p.sub_add_cancel, &[three, seven, bound]);
        let difference = f.sub(seven, three);
        let lhs = f.add(difference, three);
        let bad = f.eq(lhs, six);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC16: subtraction restoration must retain the exact minuend");
        println!(
            "NC16 (wrong restored minuend) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC17 — scaled subtraction retains the exact subtrahend. Replacing
    // `3*2` by `3*3` changes the concrete result from 15 to 12.
    {
        let name = f.name("nc17_mul_sub_wrong_scaled_subtrahend");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let bound = f.lemma(p.le_add_right, &[two, five]);
        let proof = f.lemma(p.mul_sub_left_distrib, &[three, seven, two, bound]);
        let difference = f.sub(seven, two);
        let lhs = f.mul(three, difference);
        let scaled_q = f.mul(three, seven);
        let wrong_scaled_a = f.mul(three, three);
        let wrong_rhs = f.sub(scaled_q, wrong_scaled_a);
        let bad = f.eq(lhs, wrong_rhs);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC17: scaled subtraction must retain the exact subtrahend");
        println!(
            "NC17 (wrong scaled subtrahend) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC18 — addition monotonicity retains its common left operand.
    {
        let name = f.name("nc18_add_monotonicity_wrong_left_operand");
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let h = f.lemma(p.le_add_right, &[two, three]);
        let proof = f.lemma(p.add_le_add_left, &[four, two, five, h]);
        let wrong_lhs = f.add(three, two);
        let rhs = f.add(four, five);
        let bad = f.le(wrong_lhs, rhs);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC18: addition monotonicity must retain the common operand");
        println!(
            "NC18 (wrong addition operand) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC19 — multiplication monotonicity retains its common left factor.
    {
        let name = f.name("nc19_mul_monotonicity_wrong_left_factor");
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let h = f.lemma(p.le_add_right, &[two, three]);
        let proof = f.lemma(p.mul_le_mul_left, &[three, two, five, h]);
        let wrong_lhs = f.mul(four, two);
        let rhs = f.mul(three, five);
        let bad = f.le(wrong_lhs, rhs);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC19: multiplication monotonicity must retain the factor");
        println!(
            "NC19 (wrong multiplication factor) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC20 — totality retains both compared endpoints.
    {
        let name = f.name("nc20_totality_wrong_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let proof = f.lemma(p.le_total, &[five, two]);
        let wrong_left = f.le(five, three);
        let right = f.le(two, five);
        let bad = f.const_app(p.logic.or, &[wrong_left, right]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC20: totality must retain both compared endpoints");
        println!(
            "NC20 (wrong totality endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC21 — witness-based order introduction retains the reconstructed upper endpoint.
    {
        let name = f.name("nc21_le_intro_wrong_upper_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let sum_eq = f.refl(five);
        let proof = f.lemma(p.le_intro, &[two, five, three, sum_eq]);
        let bad = f.le(two, four);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC21: order introduction must retain the reconstructed endpoint");
        println!(
            "NC21 (wrong introduced endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC22 — additive order reflection retains the unshifted lower endpoint.
    {
        let name = f.name("nc22_add_order_reflection_wrong_lower_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let h = f.lemma(p.le_add_right, &[two, three]);
        let shifted = f.lemma(p.add_le_add_left, &[four, two, five, h]);
        let proof = f.lemma(p.le_of_add_le_add_left, &[four, two, five, shifted]);
        let bad = f.le(three, five);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC22: reflected order must retain the unshifted endpoints");
        println!(
            "NC22 (wrong reflected endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC23 — positive multiplication cancellation retains the reflected endpoints.
    {
        let name = f.name("nc23_mul_order_reflection_wrong_lower_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let nine = f.num(9);
        let scaled = f.lemma(p.le_add_right, &[six, nine]);
        let proof = f.lemma(p.le_of_mul_le_mul_left_succ, &[two, two, five, scaled]);
        let bad = f.le(three, five);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC23: multiplication reflection must retain both endpoints");
        println!(
            "NC23 (wrong multiplied endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC24 — bounded reverse subtraction retains minuend and subtrahend.
    {
        let name = f.name("nc24_sub_zero_wrong_orientation");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let zero = f.zero();
        let h = f.lemma(p.le_add_right, &[two, three]);
        let proof = f.lemma(p.sub_eq_zero_of_le, &[two, five, h]);
        let wrong_difference = f.sub(five, two);
        let bad = f.eq(wrong_difference, zero);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC24: subtraction-to-zero must retain operand orientation");
        println!(
            "NC24 (wrong subtraction orientation) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC25 — the subtraction adjunction retains its exact additive upper bound.
    {
        let name = f.name("nc25_sub_adjunction_wrong_upper_bound");
        let two = f.num(2);
        let four = f.num(4);
        let five = f.num(5);
        let proof = f.lemma(p.sub_le_iff_le_add, &[five, two, four]);
        let difference = f.sub(five, two);
        let lhs = f.le(difference, four);
        let wrong_rhs = f.le(five, five);
        let bad = f.const_app(p.logic.iff, &[lhs, wrong_rhs]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC25: subtraction adjunction must retain the exact upper bound");
        println!(
            "NC25 (wrong adjunction bound) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC26 — proof-directed positive cancellation retains both endpoints.
    {
        let name = f.name("nc26_bounded_mul_reflection_wrong_lower_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let nine = f.num(9);
        let positive = f.lemma(p.le_add_right, &[one, two]);
        let scaled = f.lemma(p.le_add_right, &[six, nine]);
        let proof = f.lemma(
            p.le_of_mul_le_mul_left,
            &[three, two, five, positive, scaled],
        );
        let bad = f.le(three, five);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC26: bounded multiplication reflection must retain both endpoints");
        println!(
            "NC26 (wrong proof-directed multiplied endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC27 — antisymmetry retains the equality endpoints.
    {
        let name = f.name("nc27_antisymmetry_wrong_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let bound = f.lemma(p.le_refl, &[two]);
        let proof = f.lemma(p.le_antisymm, &[two, two, bound, bound]);
        let bad = f.eq(two, three);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC27: antisymmetry must retain both endpoints");
        println!(
            "NC27 (wrong antisymmetry endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC28 — positive multiplication equality cancellation retains endpoints.
    {
        let name = f.name("nc28_mul_equality_cancel_wrong_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let six = f.num(6);
        let positive = f.lemma(p.le_add_right, &[one, two]);
        let equality = f.refl(six);
        let proof = f.lemma(
            p.mul_left_cancel_of_pos,
            &[three, two, two, positive, equality],
        );
        let bad = f.eq(two, three);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC28: multiplication equality cancellation must retain endpoints");
        println!(
            "NC28 (wrong cancelled equality endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC29 — divisibility cancellation retains the uncancelled summand.
    {
        let name = f.name("nc29_dvd_add_cancel_wrong_summand");
        let one = f.num(1);
        let two = f.num(2);
        let four = f.num(4);
        let five = f.num(5);
        let six = f.num(6);
        let positive = f.lemma(p.le_add_right, &[one, one]);
        let h4 = f.lemma(p.dvd_mul, &[two, two]);
        let three = f.num(3);
        let h6 = f.lemma(p.dvd_mul, &[two, three]);
        let h10 = f.lemma(p.dvd_add, &[two, four, six, h4, h6]);
        let proof = f.lemma(
            p.dvd_add_right_cancel_of_pos,
            &[two, four, six, positive, h4, h10],
        );
        let bad = f.dvd(two, five);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC29: divisibility cancellation must retain the second summand");
        println!(
            "NC29 (wrong cancelled divisibility summand) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC30 — primitive nondivisibility retains the divisor.
    {
        let name = f.name("nc30_not_dvd_one_wrong_divisor");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let bound = f.lemma(p.le_refl, &[two]);
        let proof = f.lemma(p.not_dvd_one_of_two_le, &[two, bound]);
        let three_dvd_one = f.dvd(three, one);
        let bad = f.const_app(p.logic.not, &[three_dvd_one]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC30: nondivisibility of one must retain the divisor");
        println!(
            "NC30 (wrong primitive nondivisor) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC31 — the one-plus-multiple theorem retains its exact multiplier.
    {
        let name = f.name("nc31_not_dvd_one_plus_mul_wrong_multiplier");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let bound = f.lemma(p.le_refl, &[two]);
        let proof = f.lemma(p.not_dvd_one_add_mul_of_two_le, &[two, three, bound]);
        let two_times_two = f.mul(two, two);
        let wrong_sum = f.add(one, two_times_two);
        let wrong_dvd = f.dvd(two, wrong_sum);
        let bad = f.const_app(p.logic.not, &[wrong_dvd]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC31: one-plus-multiple nondivisibility must retain the multiplier");
        println!(
            "NC31 (wrong one-plus-multiple endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC32 — the exact-valuation theorem retains exponent two.
    {
        let name = f.name("nc32_valuation_wrong_exponent");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let bound = f.lemma(p.le_refl, &[two]);
        let not_dvd = f.lemma(p.not_dvd_one_add_mul_of_two_le, &[two, three, bound]);
        let multiple = f.mul(two, three);
        let u = f.add(one, multiple);
        let proof = f.lemma(p.valuation_at_two_mul_sq, &[two, u, bound, not_dvd]);
        let square = f.mul(two, two);
        let z = f.mul(square, u);
        let bad = f.valuation_at(two, z, one);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC32: exact valuation must retain exponent two");
        println!(
            "NC32 (wrong valuation exponent) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC33 — closed-interval membership retains both endpoints.
    {
        let name = f.name("nc33_closed_interval_wrong_upper_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let lower = f.lemma(p.le_add_right, &[two, one]);
        let two_more = f.num(2);
        let upper = f.lemma(p.le_add_right, &[three, two_more]);
        let lower_ty = f.le(two, three);
        let upper_ty = f.le(three, five);
        let proof = f.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper]);
        let bad = f.in_closed_interval(two, four, three);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC33: interval membership must retain both endpoints");
        println!(
            "NC33 (wrong closed-interval endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC34 — order decomposition retains its lower endpoint.
    {
        let name = f.name("nc34_lt_or_eq_wrong_lower_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let bound = f.lemma(p.le_add_right, &[two, three]);
        let proof = f.lemma(p.lt_or_eq_of_le, &[two, five, bound]);
        let wrong_lt = f.lt(three, five);
        let wrong_eq = f.eq(three, five);
        let bad = f.const_app(p.logic.or, &[wrong_lt, wrong_eq]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC34: order decomposition must retain both endpoints");
        println!(
            "NC34 (wrong strict-or-equal endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    assert_eq!(rejections, 34, "every negative control must be rejected");
}

/// The build is deterministic: two independent kernels render every promised
/// statement identically.
#[test]
fn the_build_is_deterministic() {
    let render_all = || {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut out: Vec<String> = Vec::new();
        for name in definition_names(&p).into_iter().chain(theorem_names(&p)) {
            let display = k.display_name(name).to_string();
            let ty = k.environment().get(name).expect("admitted").ty();
            out.push(format!("{display} : {}", k.render_lean(ty)));
        }
        out
    };
    let first = render_all();
    let second = render_all();
    assert_eq!(first, second, "the prelude build must be deterministic");
    assert_eq!(
        first.len(),
        10 + 61,
        "every promised definition and theorem must be rendered"
    );
}
