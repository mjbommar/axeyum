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

    /// Build a concrete balanced-witness congruence proof when both sides
    /// reduce to the same unary numeral.
    fn concrete_mod_eq(
        &mut self,
        modulus: ExprId,
        left: ExprId,
        right: ExprId,
        left_witness: ExprId,
        right_witness: ExprId,
    ) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        let outer = self.mod_eq_outer_predicate(modulus, left, right);
        let inner = self.mod_eq_inner_predicate(modulus, left, right, left_witness);
        let lhs = self.mod_eq_sum(modulus, left, left_witness);
        let equation = self.refl(lhs);
        let intro = self.k.const_(self.p.logic.exists_intro, vec![one]);
        let inner_proof = self.apply(intro, &[nat, inner, right_witness, equation]);
        self.apply(intro, &[nat, outer, left_witness, inner_proof])
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
        p.beq,
        p.div_mod_state,
        p.div,
        p.mod_,
        p.gcd,
        p.sum_range,
        p.pred,
        p.sub,
        p.lt,
        p.in_closed_interval,
        p.div_mod,
        p.dvd,
        p.bezout,
        p.mod_eq,
        p.valuation_at,
        p.lt_well_founded,
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
        p.add_sub_cancel_left,
        p.sum_range_zero,
        p.sum_range_succ,
        p.sum_range_congr,
        p.mul_sum_range,
        p.mul_sum_range_pow,
        p.beq_refl,
        p.eq_of_beq_eq_true,
        p.beq_eq_true_of_eq,
        p.beq_eq_true_iff,
        p.div_zero,
        p.mod_zero,
        p.zero_div,
        p.zero_mod,
        p.div_succ,
        p.mod_succ,
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
        p.right_distrib,
        p.mul_assoc,
        p.one_mul,
        p.mul_one,
        p.zero_le,
        p.le_succ_succ,
        p.le_of_succ_le_succ,
        p.le_trans,
        p.lt_or_eq_of_le,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_total,
        p.not_succ_le_zero,
        p.lt_irrefl,
        p.le_antisymm,
        p.le_intro,
        p.le_dest,
        p.le_add_right,
        p.add_le_add_left,
        p.add_lt_add_left,
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
        p.mul_sub_left_distrib_total,
        p.div_mod_exists,
        p.div_mod_unique,
        p.div_mod_bounds,
        p.div_mod_mul_le_iff,
        p.div_mod_lt_mul_iff,
        p.div_mod_add_multiple,
        p.div_mod_remainder_eq_zero_iff_dvd,
        p.div_mod_exact_exists,
        p.div_mod_exec,
        p.mod_lt,
        p.gcd_zero_left,
        p.gcd_succ,
        p.gcd_dvd,
        p.gcd_dvd_left,
        p.gcd_dvd_right,
        p.dvd_gcd,
        p.dvd_gcd_iff,
        p.gcd_bezout,
        p.mod_eq_refl,
        p.mod_eq_symm,
        p.mod_eq_trans,
        p.mod_eq_add_left,
        p.mod_eq_add_right,
        p.mod_eq_add,
        p.mod_eq_mul_left,
        p.mod_eq_mul_right,
        p.mod_eq_mul,
        p.div_mod_same_remainder_mod_eq,
        p.div_mod_remainder_eq_of_mod_eq,
        p.mod_eq_iff_div_mod_remainder_eq,
        p.mod_eq_zero_of_dvd,
        p.dvd_of_mod_eq_zero_of_pos,
        p.mod_eq_zero_iff_dvd,
        p.dvd_mul,
        p.dvd_refl,
        p.dvd_zero,
        p.dvd_trans,
        p.dvd_mul_right_of_dvd,
        p.dvd_add_iff_right,
        p.dvd_mod_iff,
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

    let four = f.num(4);
    let two_lt_three = f.lemma(p.le_refl, &[three]);
    let three_lt_five = f.lemma(p.le_add_right, &[four, one]);
    for proof in [
        f.lemma(p.lt_of_lt_of_le, &[two, three, five, two_lt_three, upper]),
        f.lemma(p.lt_of_le_of_lt, &[two, three, five, lower, three_lt_five]),
        f.lemma(p.add_lt_add_left, &[one, two, three, two_lt_three]),
        f.lemma(p.lt_irrefl, &[three]),
    ] {
        f.k.infer(proof).unwrap_or_else(|e| {
            panic!(
                "strict-order library application should infer: {}",
                f.explain(&e)
            )
        });
    }
}

#[test]
fn boolean_equality_computes_and_reflects_propositional_equality() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let two = f.num(2);
    let three = f.num(3);
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    for (left, right, expected) in [
        (zero, zero, true_),
        (two, two, true_),
        (two, three, false_),
        (three, two, false_),
    ] {
        let result = f.beq(left, right);
        assert!(
            f.k.def_eq(result, expected),
            "Nat.beq must compute on closed inputs"
        );
    }

    let two_is_two = f.lemma(p.beq_refl, &[two]);
    let reflected = f.lemma(p.eq_of_beq_eq_true, &[two, two, two_is_two]);
    let reflected_ty = f.eq(two, two);
    let inferred = f.k.infer(reflected).expect("reflection should infer");
    assert!(f.k.def_eq(inferred, reflected_ty));

    let iff = f.lemma(p.beq_eq_true_iff, &[two, three]);
    f.k.infer(iff)
        .expect("the exact equality specification should infer");

    let false_result = f.beq(two, three);
    let wrong_ty = f.bool_eq(false_result, true_);
    let wrong_proof = f.bool_refl(false_result);
    let wrong_name = f.name("beq_two_three_is_true");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, wrong_proof)
        .expect_err("the kernel must reject a false equality-test result");
    assert!(
        matches!(error, KernelError::DeclarationValueMismatch { .. }),
        "unexpected rejection: {error:?}"
    );
}

#[test]
fn executable_division_computes_both_shared_state_projections() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let six = f.num(6);
    let eleven = f.num(11);

    for (dividend, divisor, quotient, remainder) in [
        (zero, zero, zero, zero),
        (five, zero, zero, five),
        (zero, three, zero, zero),
        (two, five, zero, two),
        (five, two, two, one),
        (six, two, three, zero),
        (eleven, two, five, one),
    ] {
        let computed_quotient = f.div(dividend, divisor);
        let computed_remainder = f.modulo(dividend, divisor);
        let true_selector = f.bool_true();
        let false_selector = f.bool_false();
        let state_quotient = f.div_mod_state(divisor, dividend, true_selector);
        let state_remainder = f.div_mod_state(divisor, dividend, false_selector);
        assert!(
            f.k.def_eq(computed_quotient, quotient),
            "quotient projection must compute"
        );
        assert!(
            f.k.def_eq(computed_remainder, remainder),
            "remainder projection must compute"
        );
        assert!(
            f.k.def_eq(state_quotient, quotient),
            "shared state true projection"
        );
        assert!(
            f.k.def_eq(state_remainder, remainder),
            "shared state false projection"
        );
    }

    let div_succ_proof = f.lemma(p.div_succ, &[five, one]);
    let mod_succ_proof = f.lemma(p.mod_succ, &[five, one]);
    for proof in [
        f.lemma(p.div_zero, &[five]),
        f.lemma(p.mod_zero, &[five]),
        f.lemma(p.zero_div, &[three]),
        f.lemma(p.zero_mod, &[three]),
        div_succ_proof,
        mod_succ_proof,
    ] {
        f.k.infer(proof).expect("division equation should infer");
    }

    let computed_quotient = f.div(five, two);
    let wrong_quotient_ty = f.eq(computed_quotient, three);
    let wrong_quotient_proof = f.refl(computed_quotient);
    let wrong_quotient_name = f.name("five_div_two_is_three");
    let quotient_error = f
        .declare_theorem(wrong_quotient_name, wrong_quotient_ty, wrong_quotient_proof)
        .expect_err("a wrong quotient must be rejected");
    assert!(matches!(
        quotient_error,
        KernelError::DeclarationValueMismatch { .. }
    ));

    let computed_remainder = f.modulo(five, two);
    let wrong_remainder_ty = f.eq(computed_remainder, zero);
    let wrong_remainder_proof = f.refl(computed_remainder);
    let wrong_remainder_name = f.name("five_mod_two_is_zero");
    let remainder_error = f
        .declare_theorem(
            wrong_remainder_name,
            wrong_remainder_ty,
            wrong_remainder_proof,
        )
        .expect_err("a wrong remainder must be rejected");
    assert!(matches!(
        remainder_error,
        KernelError::DeclarationValueMismatch { .. }
    ));
}

#[test]
fn executable_division_is_checked_against_the_relational_specification() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);
    let six = f.num(6);

    let five_spec = f.lemma(p.div_mod_exec, &[one, five]);
    let five_quotient = f.div(five, two);
    let five_remainder = f.modulo(five, two);
    let five_spec_ty = f.div_mod(two, five, five_quotient, five_remainder);
    let inferred =
        f.k.infer(five_spec)
            .expect("the executable division specification should infer");
    assert!(f.k.def_eq(inferred, five_spec_ty));

    let floor_bounds = f.lemma(
        p.div_mod_bounds,
        &[two, five, five_quotient, five_remainder, five_spec],
    );
    f.k.infer(floor_bounds)
        .expect("relational floor laws should apply to executable division");

    let six_spec = f.lemma(p.div_mod_exec, &[one, six]);
    let six_quotient = f.div(six, two);
    let six_remainder = f.modulo(six, two);
    let zero_remainder_dvd = f.lemma(
        p.div_mod_remainder_eq_zero_iff_dvd,
        &[two, six, six_quotient, six_remainder, six_spec],
    );
    f.k.infer(zero_remainder_dvd)
        .expect("divisibility laws should apply to executable remainders");

    let swapped_ty = f.div_mod(two, five, five_remainder, five_quotient);
    let swapped_name = f.name("five_div_mod_projections_are_swapped");
    let error = f
        .declare_theorem(swapped_name, swapped_ty, five_spec)
        .expect_err("the relational bridge must reject swapped projections");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));

    let zero_spec = f.lemma(p.div_mod_exec, &[zero, five]);
    f.k.infer(zero_spec)
        .expect("the successor-divisor theorem must include divisor one");
}

#[test]
fn executable_gcd_uses_checked_remainder_descent_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let seven = f.num(7);
    let ten = f.num(10);
    let fifteen = f.num(15);

    let remainder_bound = f.lemma(p.mod_lt, &[three, six]);
    let remainder = f.modulo(six, four);
    let bound_ty = f.lt(remainder, four);
    let inferred =
        f.k.infer(remainder_bound)
            .expect("mod_lt should expose the checked Euclidean decrease");
    assert!(f.k.def_eq(inferred, bound_ty));

    let gcd_zero_five = f.gcd(zero, five);
    assert!(f.k.def_eq(gcd_zero_five, five), "gcd 0 5 must reduce to 5");
    let gcd_ten_fifteen = f.gcd(ten, fifteen);
    assert!(
        f.k.def_eq(gcd_ten_fifteen, five),
        "gcd 10 15 must reduce to 5"
    );
    let gcd_seven_zero = f.gcd(seven, zero);
    assert!(
        f.k.def_eq(gcd_seven_zero, seven),
        "gcd 7 0 must reduce to 7"
    );

    let equation = f.lemma(p.gcd_succ, &[three, six]);
    let left = f.gcd(four, six);
    let quotient = f.div(six, four);
    let changed_right = f.gcd(quotient, four);
    let changed_ty = f.eq(left, changed_right);
    let changed_name = f.name("gcd_succ_with_quotient_instead_of_remainder");
    let error = f
        .declare_theorem(changed_name, changed_ty, equation)
        .expect_err("the gcd equation must reject quotient/remainder mutation");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));
}

#[test]
fn executable_gcd_has_the_checked_common_divisor_characterization() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let ten = f.num(10);
    let fourteen = f.num(14);
    let fifteen = f.num(15);

    let common = f.gcd(ten, fifteen);
    let common_divides_ten_ty = f.dvd(common, ten);
    let common_divides_fifteen_ty = f.dvd(common, fifteen);
    let pair_ty = f.const_app(
        p.logic.and,
        &[common_divides_ten_ty, common_divides_fifteen_ty],
    );
    let gcd_dvd = f.lemma(p.gcd_dvd, &[ten, fifteen]);
    let inferred =
        f.k.infer(gcd_dvd)
            .expect("computed gcd should divide both inputs");
    assert!(f.k.def_eq(inferred, pair_ty));

    let five_divides_ten = f.lemma(p.dvd_mul, &[five, two]);
    let five_divides_fifteen = f.lemma(p.dvd_mul, &[five, three]);
    let five_divides_gcd = f.lemma(
        p.dvd_gcd,
        &[five, ten, fifteen, five_divides_ten, five_divides_fifteen],
    );
    f.k.infer(five_divides_gcd)
        .expect("every common divisor should divide computed gcd");

    let characterization = f.lemma(p.dvd_gcd_iff, &[five, ten, fifteen]);
    f.k.infer(characterization)
        .expect("dvd_gcd_iff should package both semantic directions");
    let zero_characterization = f.lemma(p.dvd_gcd_iff, &[zero, zero, zero]);
    f.k.infer(zero_characterization)
        .expect("the gcd characterization should include the all-zero corner");

    let changed_right_ty = f.dvd(common, fourteen);
    let changed_pair_ty = f.const_app(p.logic.and, &[common_divides_ten_ty, changed_right_ty]);
    let changed_name = f.name("gcd_dvd_with_changed_right_input");
    let error = f
        .declare_theorem(changed_name, changed_pair_ty, gcd_dvd)
        .expect_err("gcd divisibility must reject a changed input");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));
}

#[test]
fn executable_gcd_has_a_checked_balanced_bezout_certificate() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);
    let ten = f.num(10);
    let fourteen = f.num(14);
    let fifteen = f.num(15);

    let common = f.gcd(ten, fifteen);
    let target = f.bezout(ten, fifteen, common);
    let general = f.lemma(p.gcd_bezout, &[ten, fifteen]);
    let inferred =
        f.k.infer(general)
            .expect("the general Euclidean construction should yield a certificate");
    assert!(f.k.def_eq(inferred, target));

    // 5 + 10*0 + 15*1 = 10*2 + 15*0 is a concrete balanced encoding of
    // 5 = 2*10 - 1*15, independent of the recursive theorem's chosen witness.
    let twenty = f.num(20);
    let equation = f.refl(twenty);
    let explicit = f.bezout_intro(ten, fifteen, five, two, zero, zero, one, equation);
    let explicit_ty =
        f.k.infer(explicit)
            .expect("an explicit nontrivial balanced certificate should check");
    let expected_explicit_ty = f.bezout(ten, fifteen, five);
    assert!(f.k.def_eq(explicit_ty, expected_explicit_ty));

    let all_zero = f.lemma(p.gcd_bezout, &[zero, zero]);
    f.k.infer(all_zero)
        .expect("the constructive theorem should include gcd 0 0");

    let changed_target = f.bezout(ten, fourteen, common);
    let changed_name = f.name("gcd_bezout_with_changed_right_input");
    let error = f
        .declare_theorem(changed_name, changed_target, general)
        .expect_err("a Bézout certificate must reject a changed generator");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));
}

/// The Nat accessibility proof is deliberately reducible: a closed function
/// built with the generic `WellFounded.fix` must compute through it. This
/// countdown identity uses the recursive value at the immediate predecessor,
/// so it exercises more than a step function that ignores strong recursion.
#[test]
fn nat_strict_well_foundedness_drives_generic_strong_recursion() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_level = f.level_one();
    let relation = f.k.const_(p.lt, vec![]);
    let recursive_ty = |f: &mut Fixture, upper: ExprId| {
        let predecessor_fv = f.fresh_fvar();
        let related_fv = f.fresh_fvar();
        let predecessor = f.k.fvar(predecessor_fv);
        let related_ty = f.lt(predecessor, upper);
        let at_relation = f.pi_fv(related_fv, related_ty, nat);
        f.pi_fv(predecessor_fv, nat, at_relation)
    };

    let motive_fv = f.fresh_fvar();
    let family = f.lam_fv(motive_fv, nat, nat);
    let step_motive = {
        let upper_fv = f.fresh_fvar();
        let upper = f.k.fvar(upper_fv);
        let recursive = recursive_ty(&mut f, upper);
        let result = f.arrow(recursive, nat);
        f.lam_fv(upper_fv, nat, result)
    };
    let step_zero = {
        let recursive_fv = f.fresh_fvar();
        let zero = f.zero();
        let recursive = recursive_ty(&mut f, zero);
        f.lam_fv(recursive_fv, recursive, zero)
    };
    let step_succ = {
        let prior_fv = f.fresh_fvar();
        let ih_fv = f.fresh_fvar();
        let recursive_fv = f.fresh_fvar();
        let prior = f.k.fvar(prior_fv);
        let sprior = f.succ(prior);
        let prior_case = recursive_ty(&mut f, prior);
        let ih_ty = f.arrow(prior_case, nat);
        let recursive = f.k.fvar(recursive_fv);
        let recursive_succ_ty = recursive_ty(&mut f, sprior);
        let related = f.lemma(p.le_refl, &[sprior]);
        let prior_value = f.apply(recursive, &[prior, related]);
        let body = f.succ(prior_value);
        let with_recursive = f.lam_fv(recursive_fv, recursive_succ_ty, body);
        let with_ih = f.lam_fv(ih_fv, ih_ty, with_recursive);
        f.lam_fv(prior_fv, nat, with_ih)
    };
    let step = {
        let upper_fv = f.fresh_fvar();
        let recursive_fv = f.fresh_fvar();
        let upper = f.k.fvar(upper_fv);
        let recursive = f.k.fvar(recursive_fv);
        let recursive_type = recursive_ty(&mut f, upper);
        let rec = f.k.const_(p.rec, vec![one_level]);
        let selected = f.apply(rec, &[step_motive, step_zero, step_succ, upper]);
        let body = f.apply(selected, &[recursive]);
        let with_recursive = f.lam_fv(recursive_fv, recursive_type, body);
        f.lam_fv(upper_fv, nat, with_recursive)
    };

    let well_founded = f.k.const_(p.lt_well_founded, vec![]);
    let fix =
        f.k.const_(p.logic.well_founded_fix, vec![one_level, one_level]);
    let two = f.num(2);
    let computed = f.apply(fix, &[nat, relation, family, well_founded, step, two]);
    let inferred = f.k.infer(computed).expect("strong recursion should infer");
    assert!(f.k.def_eq(inferred, nat));
    assert!(f.k.def_eq(computed, two), "countdown identity at two");

    let one = f.num(1);
    let wrong_ty = f.eq(computed, one);
    let proof = f.refl(computed);
    let wrong_name = f.name("lt_well_founded_wrong_result");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, proof)
        .expect_err("strong recursion must not compute to the wrong numeral");
    assert!(
        matches!(error, KernelError::DeclarationValueMismatch { .. }),
        "unexpected rejection: {error:?}"
    );
}

#[test]
fn euclidean_division_exists_constructively() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);
    let positive = f.lemma(p.le_add_right, &[one, one]);
    let exists = f.lemma(p.div_mod_exists, &[two, five, positive]);
    f.k.infer(exists)
        .unwrap_or_else(|e| panic!("Euclidean decomposition should infer: {}", f.explain(&e)));

    // Concrete anti-vacuity: 5 = 2*2+1 and 1<2.
    let relation = f.div_mod(two, five, two, one);
    let product = f.mul(two, two);
    let reconstructed = f.add(product, one);
    let equation_ty = f.eq(five, reconstructed);
    let bound_ty = f.lt(one, two);
    let equation = f.refl(five);
    let bound = f.lemma(p.le_refl, &[two]);
    let proof = f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
    let name = f.name("five_div_two");
    f.declare_theorem(name, relation, proof)
        .unwrap_or_else(|e| panic!("concrete divMod witness should admit: {}", f.explain(&e)));

    let unique = f.lemma(
        p.div_mod_unique,
        &[two, five, two, one, two, one, proof, proof],
    );
    f.k.infer(unique).unwrap_or_else(|e| {
        panic!(
            "Euclidean decomposition uniqueness should infer: {}",
            f.explain(&e)
        )
    });

    let bounds = f.lemma(p.div_mod_bounds, &[two, five, two, one, proof]);
    f.k.infer(bounds)
        .unwrap_or_else(|e| panic!("Euclidean floor bounds should infer: {}", f.explain(&e)));

    let floor_order = f.lemma(p.div_mod_mul_le_iff, &[two, five, two, one, two, proof]);
    f.k.infer(floor_order).unwrap_or_else(|e| {
        panic!(
            "Euclidean quotient/multiplication order equivalence should infer: {}",
            f.explain(&e)
        )
    });

    let three = f.num(3);
    let ceiling_order = f.lemma(p.div_mod_lt_mul_iff, &[two, five, two, one, three, proof]);
    f.k.infer(ceiling_order).unwrap_or_else(|e| {
        panic!(
            "Euclidean quotient/strict-multiplication equivalence should infer: {}",
            f.explain(&e)
        )
    });

    // Adding 2*3 to 5 = 2*2+1 preserves the remainder and shifts the
    // quotient: 11 = 2*5+1.
    let shifted_relation = f.lemma(p.div_mod_add_multiple, &[two, five, two, one, three, proof]);
    let eleven = f.num(11);
    let shifted_quotient = f.num(5);
    let shifted_relation_ty = f.div_mod(two, eleven, shifted_quotient, one);
    let shifted_name = f.name("eleven_div_two_from_shift");
    f.declare_theorem(shifted_name, shifted_relation_ty, shifted_relation)
        .unwrap_or_else(|e| {
            panic!(
                "adding a divisor multiple should preserve divMod: {}",
                f.explain(&e)
            )
        });

    // Exact division connects zero remainder to the existing existential
    // divisibility relation: 6 = 2*3+0 iff 2 divides 6.
    let zero = f.num(0);
    let six = f.num(6);
    let exact_product = f.mul(two, three);
    let exact_reconstructed = f.add(exact_product, zero);
    let exact_equation_ty = f.eq(six, exact_reconstructed);
    let exact_bound_ty = f.lt(zero, two);
    let exact_equation = f.refl(six);
    let exact_relation = f.const_app(
        p.logic.and_intro,
        &[exact_equation_ty, exact_bound_ty, exact_equation, positive],
    );
    let exact_division = f.lemma(
        p.div_mod_remainder_eq_zero_iff_dvd,
        &[two, six, three, zero, exact_relation],
    );
    f.k.infer(exact_division).unwrap_or_else(|e| {
        panic!(
            "zero remainder/exact divisibility equivalence should infer: {}",
            f.explain(&e)
        )
    });

    let divides_six = f.lemma(p.dvd_mul, &[two, three]);
    let exact_exists = f.lemma(p.div_mod_exact_exists, &[two, six, positive, divides_six]);
    f.k.infer(exact_exists).unwrap_or_else(|e| {
        panic!(
            "exact zero-remainder decomposition should infer: {}",
            f.explain(&e)
        )
    });
}

#[test]
fn modular_congruence_is_a_checked_equivalence_relation() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.num(0);
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);
    let twelve = f.num(12);

    let two_to_seven = f.concrete_mod_eq(five, two, seven, one, zero);
    let relation = f.mod_eq(five, two, seven);
    let name = f.name("two_mod_five_seven");
    f.declare_theorem(name, relation, two_to_seven)
        .unwrap_or_else(|e| panic!("2 ≡ 7 (mod 5) should admit: {}", f.explain(&e)));

    let reflexive = f.lemma(p.mod_eq_refl, &[five, two]);
    f.k.infer(reflexive)
        .unwrap_or_else(|e| panic!("modular reflexivity should infer: {}", f.explain(&e)));
    let symmetric = f.lemma(p.mod_eq_symm, &[five, two, seven, two_to_seven]);
    f.k.infer(symmetric)
        .unwrap_or_else(|e| panic!("modular symmetry should infer: {}", f.explain(&e)));

    let seven_to_twelve = f.concrete_mod_eq(five, seven, twelve, one, zero);
    let transitive = f.lemma(
        p.mod_eq_trans,
        &[five, two, seven, twelve, two_to_seven, seven_to_twelve],
    );
    let transitive_ty = f.mod_eq(five, two, twelve);
    let transitive_name = f.name("two_mod_five_twelve");
    f.declare_theorem(transitive_name, transitive_ty, transitive)
        .unwrap_or_else(|e| panic!("modular transitivity should admit: {}", f.explain(&e)));

    let three = f.num(3);
    let shifted = f.lemma(p.mod_eq_add_left, &[five, two, seven, three, two_to_seven]);
    let five_value = f.add(three, two);
    let ten = f.add(three, seven);
    let shifted_ty = f.mod_eq(five, five_value, ten);
    let shifted_name = f.name("five_mod_five_ten");
    f.declare_theorem(shifted_name, shifted_ty, shifted)
        .unwrap_or_else(|e| panic!("left-shifted congruence should admit: {}", f.explain(&e)));

    let shifted_right = f.lemma(p.mod_eq_add_right, &[five, two, seven, three, two_to_seven]);
    let right_shifted_left = f.add(two, three);
    let right_shifted_right = f.add(seven, three);
    let shifted_right_ty = f.mod_eq(five, right_shifted_left, right_shifted_right);
    let shifted_right_name = f.name("two_plus_three_mod_five_seven_plus_three");
    f.declare_theorem(shifted_right_name, shifted_right_ty, shifted_right)
        .unwrap_or_else(|e| panic!("right-shifted congruence should admit: {}", f.explain(&e)));

    let eight = f.num(8);
    let three_to_eight = f.concrete_mod_eq(five, three, eight, one, zero);
    let pairwise = f.lemma(
        p.mod_eq_add,
        &[five, two, seven, three, eight, two_to_seven, three_to_eight],
    );
    let pairwise_left = f.add(two, three);
    let pairwise_right = f.add(seven, eight);
    let pairwise_ty = f.mod_eq(five, pairwise_left, pairwise_right);
    let pairwise_name = f.name("two_plus_three_mod_five_seven_plus_eight");
    f.declare_theorem(pairwise_name, pairwise_ty, pairwise)
        .unwrap_or_else(|e| {
            panic!(
                "pairwise additive congruence should admit: {}",
                f.explain(&e)
            )
        });

    let factor = f.num(4);
    let scaled = f.lemma(p.mod_eq_mul_left, &[five, two, seven, factor, two_to_seven]);
    let scaled_left = f.mul(factor, two);
    let scaled_right = f.mul(factor, seven);
    let scaled_ty = f.mod_eq(five, scaled_left, scaled_right);
    let scaled_name = f.name("four_times_two_mod_five_four_times_seven");
    f.declare_theorem(scaled_name, scaled_ty, scaled)
        .unwrap_or_else(|e| panic!("left-scaled congruence should admit: {}", f.explain(&e)));

    let scaled_right_proof = f.lemma(
        p.mod_eq_mul_right,
        &[five, two, seven, factor, two_to_seven],
    );
    let right_scaled_left = f.mul(two, factor);
    let right_scaled_right = f.mul(seven, factor);
    let right_scaled_ty = f.mod_eq(five, right_scaled_left, right_scaled_right);
    let right_scaled_name = f.name("two_times_four_mod_five_seven_times_four");
    f.declare_theorem(right_scaled_name, right_scaled_ty, scaled_right_proof)
        .unwrap_or_else(|e| panic!("right-scaled congruence should admit: {}", f.explain(&e)));

    let pairwise_product = f.lemma(
        p.mod_eq_mul,
        &[five, two, seven, three, eight, two_to_seven, three_to_eight],
    );
    let product_left = f.mul(two, three);
    let product_right = f.mul(seven, eight);
    let product_ty = f.mod_eq(five, product_left, product_right);
    let product_name = f.name("two_times_three_mod_five_seven_times_eight");
    f.declare_theorem(product_name, product_ty, pairwise_product)
        .unwrap_or_else(|e| {
            panic!(
                "pairwise multiplicative congruence should admit: {}",
                f.explain(&e)
            )
        });

    // Equal relational Euclidean remainders imply congruence, independently
    // of any executable quotient/remainder operation: 7 = 5*1+2 and
    // 12 = 5*2+2, hence 7 ≡ 12 (mod 5).
    let three = f.num(3);
    let left_product = f.mul(five, one);
    let left_reconstructed = f.add(left_product, two);
    let left_equation_ty = f.eq(seven, left_reconstructed);
    let bound_ty = f.lt(two, five);
    let left_equation = f.refl(seven);
    let bound = f.lemma(p.le_add_right, &[three, two]);
    let left_relation = f.const_app(
        p.logic.and_intro,
        &[left_equation_ty, bound_ty, left_equation, bound],
    );
    let right_product = f.mul(five, two);
    let right_reconstructed = f.add(right_product, two);
    let right_equation_ty = f.eq(twelve, right_reconstructed);
    let right_equation = f.refl(twelve);
    let right_relation = f.const_app(
        p.logic.and_intro,
        &[right_equation_ty, bound_ty, right_equation, bound],
    );
    let same_remainder = f.lemma(
        p.div_mod_same_remainder_mod_eq,
        &[
            five,
            seven,
            twelve,
            one,
            two,
            two,
            left_relation,
            right_relation,
        ],
    );
    let same_remainder_ty = f.mod_eq(five, seven, twelve);
    let same_remainder_name = f.name("seven_mod_five_twelve_from_remainders");
    f.declare_theorem(same_remainder_name, same_remainder_ty, same_remainder)
        .unwrap_or_else(|e| {
            panic!(
                "same Euclidean remainder should imply congruence: {}",
                f.explain(&e)
            )
        });

    let seven_to_twelve_again = f.concrete_mod_eq(five, seven, twelve, one, zero);
    let remainder_eq = f.lemma(
        p.div_mod_remainder_eq_of_mod_eq,
        &[
            five,
            seven,
            twelve,
            one,
            two,
            two,
            two,
            seven_to_twelve_again,
            left_relation,
            right_relation,
        ],
    );
    let remainder_eq_ty = f.eq(two, two);
    let remainder_eq_name = f.name("congruent_dividends_have_equal_remainders");
    f.declare_theorem(remainder_eq_name, remainder_eq_ty, remainder_eq)
        .unwrap_or_else(|e| {
            panic!(
                "congruent relational divisions should have equal remainders: {}",
                f.explain(&e)
            )
        });

    let remainder_characterization = f.lemma(
        p.mod_eq_iff_div_mod_remainder_eq,
        &[
            five,
            seven,
            twelve,
            one,
            two,
            two,
            two,
            left_relation,
            right_relation,
        ],
    );
    let congruence_ty = f.mod_eq(five, seven, twelve);
    let remainder_characterization_ty = f.const_app(p.logic.iff, &[congruence_ty, remainder_eq_ty]);
    let characterization_name = f.name("mod_eq_iff_equal_relational_remainders");
    f.declare_theorem(
        characterization_name,
        remainder_characterization_ty,
        remainder_characterization,
    )
    .unwrap_or_else(|e| {
        panic!(
            "modular congruence/remainder characterization should admit: {}",
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

    let zero = f.num(0);
    let ten_mod_two_zero = f.lemma(p.mod_eq_zero_of_dvd, &[two, ten, proof_add]);
    let ten_mod_two_zero_ty = f.mod_eq(two, ten, zero);
    let ten_mod_two_zero_name = f.name("ten_mod_two_zero");
    f.declare_theorem(ten_mod_two_zero_name, ten_mod_two_zero_ty, ten_mod_two_zero)
        .unwrap_or_else(|e| {
            panic!(
                "divisibility should imply congruence to zero: {}",
                f.explain(&e)
            )
        });

    let one = f.num(1);
    let positive = f.lemma(p.le_add_right, &[one, one]);
    let recovered_divisibility = f.lemma(
        p.dvd_of_mod_eq_zero_of_pos,
        &[two, ten, positive, ten_mod_two_zero],
    );
    f.k.infer(recovered_divisibility).unwrap_or_else(|e| {
        panic!(
            "positive congruence to zero should imply divisibility: {}",
            f.explain(&e)
        )
    });
    let complete_characterization = f.lemma(p.mod_eq_zero_iff_dvd, &[two, ten]);
    let congruence_ty = f.mod_eq(two, ten, zero);
    let divisibility_ty = f.dvd(two, ten);
    let characterization_ty = f.const_app(p.logic.iff, &[congruence_ty, divisibility_ty]);
    let characterization_name = f.name("ten_mod_two_zero_iff_two_divides_ten");
    f.declare_theorem(
        characterization_name,
        characterization_ty,
        complete_characterization,
    )
    .unwrap_or_else(|e| {
        panic!(
            "congruence to zero should characterize divisibility: {}",
            f.explain(&e)
        )
    });
    let zero_characterization = f.lemma(p.mod_eq_zero_iff_dvd, &[zero, zero]);
    let zero_congruence_ty = f.mod_eq(zero, zero, zero);
    let zero_divisibility_ty = f.dvd(zero, zero);
    let zero_characterization_ty =
        f.const_app(p.logic.iff, &[zero_congruence_ty, zero_divisibility_ty]);
    let zero_characterization_name = f.name("zero_mod_zero_zero_iff_zero_divides_zero");
    f.declare_theorem(
        zero_characterization_name,
        zero_characterization_ty,
        zero_characterization,
    )
    .unwrap_or_else(|e| {
        panic!(
            "the all-Nat characterization should include modulus zero: {}",
            f.explain(&e)
        )
    });
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

#[test]
fn all_nat_divisibility_algebra_reaches_executable_remainders() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let eighteen = f.num(18);

    let total_distrib = f.lemma(p.mul_sub_left_distrib_total, &[three, two, five]);
    f.k.infer(total_distrib)
        .expect("reverse-order truncated distribution should infer");

    let two_divides_six = f.lemma(p.dvd_mul, &[two, three]);
    let six_divides_eighteen = f.lemma(p.dvd_mul, &[six, three]);
    let two_divides_eighteen = f.lemma(
        p.dvd_trans,
        &[two, six, eighteen, two_divides_six, six_divides_eighteen],
    );
    f.k.infer(two_divides_eighteen)
        .expect("divisibility witnesses should compose");

    let zero_divides_zero = f.lemma(p.dvd_zero, &[zero]);
    let zero_add_iff = f.lemma(p.dvd_add_iff_right, &[zero, zero, zero, zero_divides_zero]);
    f.k.infer(zero_add_iff)
        .expect("additive cancellation should cover divisor zero");

    let two_divides_four = f.lemma(p.dvd_mul, &[two, two]);
    let remainder_iff = f.lemma(p.dvd_mod_iff, &[two, three, six, two_divides_four]);
    let remainder = f.modulo(six, four);
    let correct_ty = {
        let left = f.dvd(two, remainder);
        let right = f.dvd(two, six);
        f.const_app(p.logic.iff, &[left, right])
    };
    let inferred =
        f.k.infer(remainder_iff)
            .expect("dvd_mod_iff should reach executable remainder");
    assert!(f.k.def_eq(inferred, correct_ty));

    let quotient = f.div(six, four);
    assert!(f.k.def_eq(quotient, one));
    let changed_ty = {
        let left = f.dvd(two, quotient);
        let right = f.dvd(two, six);
        f.const_app(p.logic.iff, &[left, right])
    };
    let changed_name = f.name("dvd_mod_iff_with_quotient_instead_of_remainder");
    let error = f
        .declare_theorem(changed_name, changed_ty, remainder_iff)
        .expect_err("the remainder bridge must reject a quotient substitution");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));
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

    // NC35 — Euclidean existence retains the dividend.
    {
        let name = f.name("nc35_div_mod_exists_wrong_dividend");
        let two = f.num(2);
        let four = f.num(4);
        let five = f.num(5);
        let one = f.num(1);
        let positive = f.lemma(p.le_add_right, &[one, one]);
        let proof = f.lemma(p.div_mod_exists, &[two, five, positive]);
        let nat = f.nat_ty();
        let one_level = f.level_one();
        let quotient_fv = f.fresh_fvar();
        let quotient = f.k.fvar(quotient_fv);
        let remainder_fv = f.fresh_fvar();
        let remainder = f.k.fvar(remainder_fv);
        let relation = f.div_mod(two, four, quotient, remainder);
        let remainder_predicate = f.lam_fv(remainder_fv, nat, relation);
        let exists_const = f.k.const_(p.logic.exists_, vec![one_level]);
        let remainder_exists = f.apply(exists_const, &[nat, remainder_predicate]);
        let quotient_predicate = f.lam_fv(quotient_fv, nat, remainder_exists);
        let bad = f.apply(exists_const, &[nat, quotient_predicate]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC35: Euclidean existence must retain the dividend");
        println!(
            "NC35 (wrong Euclidean dividend) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC36 — strict/weak transitivity retains its upper endpoint.
    {
        let name = f.name("nc36_lt_of_lt_of_le_wrong_upper_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let strict = f.lemma(p.le_refl, &[three]);
        let two_more = f.num(2);
        let bound = f.lemma(p.le_add_right, &[three, two_more]);
        let proof = f.lemma(p.lt_of_lt_of_le, &[two, three, five, strict, bound]);
        let bad = f.lt(two, four);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC36: strict/weak transitivity must retain its upper endpoint");
        println!(
            "NC36 (wrong strict upper endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC37 — weak/strict transitivity retains its lower endpoint.
    {
        let name = f.name("nc37_lt_of_le_of_lt_wrong_lower_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let weak = f.lemma(p.le_add_right, &[two, one]);
        let strict = f.lemma(p.le_add_right, &[four, one]);
        let proof = f.lemma(p.lt_of_le_of_lt, &[two, three, five, weak, strict]);
        let bad = f.lt(one, five);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC37: weak/strict transitivity must retain its lower endpoint");
        println!(
            "NC37 (wrong strict lower endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC38 — irreflexivity retains the compared endpoint.
    {
        let name = f.name("nc38_lt_irrefl_wrong_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let proof = f.lemma(p.lt_irrefl, &[two]);
        let wrong_lt = f.lt(three, three);
        let bad = f.const_app(p.logic.not, &[wrong_lt]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC38: irreflexivity must retain its endpoint");
        println!(
            "NC38 (wrong irreflexive endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC39 — strict addition monotonicity retains the added term.
    {
        let name = f.name("nc39_add_lt_add_left_wrong_shift");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let strict = f.lemma(p.le_refl, &[three]);
        let proof = f.lemma(p.add_lt_add_left, &[one, two, three, strict]);
        let wrong_left = f.add(two, two);
        let wrong_right = f.add(two, three);
        let bad = f.lt(wrong_left, wrong_right);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC39: strict addition monotonicity must retain the shift");
        println!(
            "NC39 (wrong strict addition shift) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC40 — division uniqueness retains the proved remainder.
    {
        let name = f.name("nc40_div_mod_unique_wrong_remainder");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let five = f.num(5);
        let relation = f.div_mod(two, five, two, one);
        let product = f.mul(two, two);
        let reconstructed = f.add(product, one);
        let equation_ty = f.eq(five, reconstructed);
        let bound_ty = f.lt(one, two);
        let equation = f.refl(five);
        let bound = f.lemma(p.le_refl, &[two]);
        let relation_proof =
            f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let inferred_relation = f
            .k
            .infer(relation_proof)
            .unwrap_or_else(|e| panic!("NC40 relation witness should infer: {}", f.explain(&e)));
        assert!(f.k.def_eq(relation, inferred_relation));
        let proof = f.lemma(
            p.div_mod_unique,
            &[
                two,
                five,
                two,
                one,
                two,
                one,
                relation_proof,
                relation_proof,
            ],
        );
        let quotient_eq = f.eq(two, two);
        let wrong_remainder_eq = f.eq(one, zero);
        let bad = f.const_app(p.logic.and, &[quotient_eq, wrong_remainder_eq]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC40: division uniqueness must retain the proved remainder");
        println!(
            "NC40 (wrong unique remainder) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC41 — division bounds retain their strict upper endpoint.
    {
        let name = f.name("nc41_div_mod_bounds_wrong_upper_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let five = f.num(5);
        let product = f.mul(two, two);
        let reconstructed = f.add(product, one);
        let equation_ty = f.eq(five, reconstructed);
        let bound_ty = f.lt(one, two);
        let equation = f.refl(five);
        let bound = f.lemma(p.le_refl, &[two]);
        let relation_proof =
            f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let proof = f.lemma(p.div_mod_bounds, &[two, five, two, one, relation_proof]);
        let lower = f.le(product, five);
        let wrong_upper = f.lt(five, five);
        let bad = f.const_app(p.logic.and, &[lower, wrong_upper]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC41: division bounds must retain the strict upper endpoint");
        println!(
            "NC41 (wrong division upper endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC42 — the floor equivalence retains the quotient endpoint.
    {
        let name = f.name("nc42_div_mod_floor_iff_wrong_quotient");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let product = f.mul(two, two);
        let reconstructed = f.add(product, one);
        let equation_ty = f.eq(five, reconstructed);
        let bound_ty = f.lt(one, two);
        let equation = f.refl(five);
        let bound = f.lemma(p.le_refl, &[two]);
        let relation_proof =
            f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let proof = f.lemma(
            p.div_mod_mul_le_iff,
            &[two, five, two, one, two, relation_proof],
        );
        let product_bound = f.le(product, five);
        let wrong_quotient_bound = f.le(three, two);
        let bad = f.const_app(p.logic.iff, &[product_bound, wrong_quotient_bound]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC42: floor equivalence must retain the quotient endpoint");
        println!(
            "NC42 (wrong floor quotient endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC43 — the strict dual retains the quotient lower endpoint.
    {
        let name = f.name("nc43_div_mod_strict_iff_wrong_quotient");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let product = f.mul(two, two);
        let reconstructed = f.add(product, one);
        let equation_ty = f.eq(five, reconstructed);
        let bound_ty = f.lt(one, two);
        let equation = f.refl(five);
        let bound = f.lemma(p.le_refl, &[two]);
        let relation_proof =
            f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let proof = f.lemma(
            p.div_mod_lt_mul_iff,
            &[two, five, two, one, three, relation_proof],
        );
        let candidate_product = f.mul(two, three);
        let product_bound = f.lt(five, candidate_product);
        let wrong_quotient_bound = f.lt(one, three);
        let bad = f.const_app(p.logic.iff, &[product_bound, wrong_quotient_bound]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC43: strict division equivalence must retain the quotient");
        println!(
            "NC43 (wrong strict quotient endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC44 — exact division retains the divisor in the divisibility result.
    {
        let name = f.name("nc44_zero_remainder_iff_wrong_divisor");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let six = f.num(6);
        let product = f.mul(two, three);
        let reconstructed = f.add(product, zero);
        let equation_ty = f.eq(six, reconstructed);
        let bound_ty = f.lt(zero, two);
        let equation = f.refl(six);
        let bound = f.lemma(p.le_add_right, &[one, one]);
        let relation_proof =
            f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let proof = f.lemma(
            p.div_mod_remainder_eq_zero_iff_dvd,
            &[two, six, three, zero, relation_proof],
        );
        let zero_remainder = f.eq(zero, zero);
        let wrong_divides = f.dvd(three, six);
        let bad = f.const_app(p.logic.iff, &[zero_remainder, wrong_divides]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC44: exact division must retain the divisor");
        println!(
            "NC44 (wrong exact-division divisor) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC45 — exact decomposition existence retains the dividend.
    {
        let name = f.name("nc45_exact_decomposition_wrong_dividend");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let positive = f.lemma(p.le_add_right, &[one, one]);
        let divides = f.lemma(p.dvd_mul, &[two, three]);
        let proof = f.lemma(p.div_mod_exact_exists, &[two, six, positive, divides]);
        let nat = f.nat_ty();
        let level_one = f.level_one();
        let quotient_fv = f.fresh_fvar();
        let quotient = f.k.fvar(quotient_fv);
        let wrong_relation = f.div_mod(two, five, quotient, zero);
        let wrong_predicate = f.lam_fv(quotient_fv, nat, wrong_relation);
        let exists = f.k.const_(p.logic.exists_, vec![level_one]);
        let bad = f.apply(exists, &[nat, wrong_predicate]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC45: exact decomposition must retain the dividend");
        println!(
            "NC45 (wrong exact-decomposition dividend) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC46 — modular reflexivity retains its endpoint.
    {
        let name = f.name("nc46_mod_eq_refl_wrong_endpoint");
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let proof = f.lemma(p.mod_eq_refl, &[five, two]);
        let bad = f.mod_eq(five, two, three);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC46: modular reflexivity must retain its endpoint");
        println!(
            "NC46 (wrong modular reflexive endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC47 — modular symmetry retains the reversed right endpoint.
    {
        let name = f.name("nc47_mod_eq_symm_wrong_endpoint");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let relation = f.concrete_mod_eq(five, two, seven, one, zero);
        let proof = f.lemma(p.mod_eq_symm, &[five, two, seven, relation]);
        let bad = f.mod_eq(five, seven, three);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC47: modular symmetry must retain both endpoints");
        println!(
            "NC47 (wrong modular symmetric endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC48 — modular transitivity retains its final endpoint.
    {
        let name = f.name("nc48_mod_eq_trans_wrong_endpoint");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let five = f.num(5);
        let seven = f.num(7);
        let eleven = f.num(11);
        let twelve = f.num(12);
        let first = f.concrete_mod_eq(five, two, seven, one, zero);
        let second = f.concrete_mod_eq(five, seven, twelve, one, zero);
        let proof = f.lemma(p.mod_eq_trans, &[five, two, seven, twelve, first, second]);
        let bad = f.mod_eq(five, two, eleven);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC48: modular transitivity must retain its final endpoint");
        println!(
            "NC48 (wrong modular transitive endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC49 — additive congruence retains the common left shift.
    {
        let name = f.name("nc49_mod_eq_add_left_wrong_shift");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let seven = f.num(7);
        let relation = f.concrete_mod_eq(five, two, seven, one, zero);
        let proof = f.lemma(p.mod_eq_add_left, &[five, two, seven, three, relation]);
        let wrong_left = f.add(four, two);
        let shifted_right = f.add(three, seven);
        let bad = f.mod_eq(five, wrong_left, shifted_right);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC49: additive congruence must retain its common shift");
        println!(
            "NC49 (wrong modular addition shift) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC50 — right-addition compatibility retains its common shift.
    {
        let name = f.name("nc50_mod_eq_add_right_wrong_shift");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let seven = f.num(7);
        let relation = f.concrete_mod_eq(five, two, seven, one, zero);
        let proof = f.lemma(p.mod_eq_add_right, &[five, two, seven, three, relation]);
        let shifted_left = f.add(two, three);
        let wrong_right = f.add(seven, four);
        let bad = f.mod_eq(five, shifted_left, wrong_right);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC50: right-additive congruence must retain its common shift");
        println!(
            "NC50 (wrong right-addition shift) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC51 — pairwise additive congruence retains its second right endpoint.
    {
        let name = f.name("nc51_mod_eq_add_wrong_endpoint");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let eight = f.num(8);
        let nine = f.num(9);
        let first = f.concrete_mod_eq(five, two, seven, one, zero);
        let second = f.concrete_mod_eq(five, three, eight, one, zero);
        let proof = f.lemma(
            p.mod_eq_add,
            &[five, two, seven, three, eight, first, second],
        );
        let left_sum = f.add(two, three);
        let wrong_right_sum = f.add(seven, nine);
        let bad = f.mod_eq(five, left_sum, wrong_right_sum);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC51: pairwise additive congruence must retain every endpoint");
        println!(
            "NC51 (wrong pairwise-addition endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC52 — multiplicative congruence retains the common left factor.
    {
        let name = f.name("nc52_mod_eq_mul_left_wrong_factor");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let seven = f.num(7);
        let relation = f.concrete_mod_eq(five, two, seven, one, zero);
        let proof = f.lemma(p.mod_eq_mul_left, &[five, two, seven, three, relation]);
        let wrong_left = f.mul(four, two);
        let scaled_right = f.mul(three, seven);
        let bad = f.mod_eq(five, wrong_left, scaled_right);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC52: multiplicative congruence must retain its common factor");
        println!(
            "NC52 (wrong modular multiplication factor) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC53 — right-factor compatibility retains its common factor.
    {
        let name = f.name("nc53_mod_eq_mul_right_wrong_factor");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let seven = f.num(7);
        let relation = f.concrete_mod_eq(five, two, seven, one, zero);
        let proof = f.lemma(p.mod_eq_mul_right, &[five, two, seven, three, relation]);
        let scaled_left = f.mul(two, three);
        let wrong_right = f.mul(seven, four);
        let bad = f.mod_eq(five, scaled_left, wrong_right);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC53: right multiplicative congruence must retain its factor");
        println!(
            "NC53 (wrong right multiplication factor) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC54 — pairwise multiplicative congruence retains every endpoint.
    {
        let name = f.name("nc54_mod_eq_mul_wrong_endpoint");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let eight = f.num(8);
        let nine = f.num(9);
        let first = f.concrete_mod_eq(five, two, seven, one, zero);
        let second = f.concrete_mod_eq(five, three, eight, one, zero);
        let proof = f.lemma(
            p.mod_eq_mul,
            &[five, two, seven, three, eight, first, second],
        );
        let left_product = f.mul(two, three);
        let wrong_right_product = f.mul(seven, nine);
        let bad = f.mod_eq(five, left_product, wrong_right_product);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC54: pairwise multiplicative congruence must retain every endpoint");
        println!(
            "NC54 (wrong pairwise multiplication endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC55 — the shared-remainder bridge retains both dividends.
    {
        let name = f.name("nc55_div_mod_same_remainder_wrong_dividend");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let twelve = f.num(12);
        let thirteen = f.num(13);
        let bound_ty = f.lt(two, five);
        let bound = f.lemma(p.le_add_right, &[three, two]);

        let left_product = f.mul(five, one);
        let left_reconstructed = f.add(left_product, two);
        let left_equation_ty = f.eq(seven, left_reconstructed);
        let left_equation = f.refl(seven);
        let left_relation = f.const_app(
            p.logic.and_intro,
            &[left_equation_ty, bound_ty, left_equation, bound],
        );

        let right_product = f.mul(five, two);
        let right_reconstructed = f.add(right_product, two);
        let right_equation_ty = f.eq(twelve, right_reconstructed);
        let right_equation = f.refl(twelve);
        let right_relation = f.const_app(
            p.logic.and_intro,
            &[right_equation_ty, bound_ty, right_equation, bound],
        );
        let proof = f.lemma(
            p.div_mod_same_remainder_mod_eq,
            &[
                five,
                seven,
                twelve,
                one,
                two,
                two,
                left_relation,
                right_relation,
            ],
        );
        let bad = f.mod_eq(five, seven, thirteen);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC55: shared-remainder congruence must retain both dividends");
        println!(
            "NC55 (wrong shared-remainder dividend) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC56 — adding a multiple shifts the quotient by the same amount.
    {
        let name = f.name("nc56_div_mod_add_multiple_wrong_quotient");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let four = f.num(4);
        let five = f.num(5);
        let eleven = f.num(11);
        let product = f.mul(two, two);
        let reconstructed = f.add(product, one);
        let equation_ty = f.eq(five, reconstructed);
        let bound_ty = f.lt(one, two);
        let equation = f.refl(five);
        let bound = f.lemma(p.le_refl, &[two]);
        let relation = f.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound]);
        let proof = f.lemma(
            p.div_mod_add_multiple,
            &[two, five, two, one, three, relation],
        );
        let bad = f.div_mod(two, eleven, four, one);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC56: adding a multiple must shift the quotient exactly");
        println!(
            "NC56 (wrong shifted divMod quotient) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC57 — the converse bridge retains both relational remainders.
    {
        let name = f.name("nc57_mod_eq_div_mod_wrong_remainder");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let twelve = f.num(12);
        let congruence = f.concrete_mod_eq(five, seven, twelve, one, zero);
        let bound_ty = f.lt(two, five);
        let bound = f.lemma(p.le_add_right, &[three, two]);
        let left_product = f.mul(five, one);
        let left_reconstructed = f.add(left_product, two);
        let left_equation_ty = f.eq(seven, left_reconstructed);
        let left_equation = f.refl(seven);
        let left_relation = f.const_app(
            p.logic.and_intro,
            &[left_equation_ty, bound_ty, left_equation, bound],
        );
        let right_product = f.mul(five, two);
        let right_reconstructed = f.add(right_product, two);
        let right_equation_ty = f.eq(twelve, right_reconstructed);
        let right_equation = f.refl(twelve);
        let right_relation = f.const_app(
            p.logic.and_intro,
            &[right_equation_ty, bound_ty, right_equation, bound],
        );
        let proof = f.lemma(
            p.div_mod_remainder_eq_of_mod_eq,
            &[
                five,
                seven,
                twelve,
                one,
                two,
                two,
                two,
                congruence,
                left_relation,
                right_relation,
            ],
        );
        let bad = f.eq(two, one);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC57: converse bridge must retain both remainders");
        println!(
            "NC57 (wrong modular remainder equality) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC58 — the packaged characterization retains the remainder endpoints.
    {
        let name = f.name("nc58_mod_eq_iff_wrong_remainder");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let five = f.num(5);
        let seven = f.num(7);
        let twelve = f.num(12);
        let bound_ty = f.lt(two, five);
        let bound = f.lemma(p.le_add_right, &[three, two]);
        let left_product = f.mul(five, one);
        let left_reconstructed = f.add(left_product, two);
        let left_equation_ty = f.eq(seven, left_reconstructed);
        let left_equation = f.refl(seven);
        let left_relation = f.const_app(
            p.logic.and_intro,
            &[left_equation_ty, bound_ty, left_equation, bound],
        );
        let right_product = f.mul(five, two);
        let right_reconstructed = f.add(right_product, two);
        let right_equation_ty = f.eq(twelve, right_reconstructed);
        let right_equation = f.refl(twelve);
        let right_relation = f.const_app(
            p.logic.and_intro,
            &[right_equation_ty, bound_ty, right_equation, bound],
        );
        let proof = f.lemma(
            p.mod_eq_iff_div_mod_remainder_eq,
            &[
                five,
                seven,
                twelve,
                one,
                two,
                two,
                two,
                left_relation,
                right_relation,
            ],
        );
        let congruence_ty = f.mod_eq(five, seven, twelve);
        let wrong_remainder_eq = f.eq(two, one);
        let bad = f.const_app(p.logic.iff, &[congruence_ty, wrong_remainder_eq]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC58: remainder characterization must retain both endpoints");
        println!(
            "NC58 (wrong packaged remainder endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC59 — divisibility-to-congruence retains the zero endpoint.
    {
        let name = f.name("nc59_mod_eq_zero_of_dvd_wrong_endpoint");
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let six = f.num(6);
        let divides = f.lemma(p.dvd_mul, &[two, three]);
        let proof = f.lemma(p.mod_eq_zero_of_dvd, &[two, six, divides]);
        let bad = f.mod_eq(two, six, one);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC59: divisibility must imply congruence specifically to zero");
        println!(
            "NC59 (wrong divisible congruence endpoint) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC60 — the positive converse retains the divisible value.
    {
        let name = f.name("nc60_dvd_of_mod_eq_zero_wrong_value");
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let four = f.num(4);
        let five = f.num(5);
        let ten = f.num(10);
        let eleven = f.num(11);
        let positive = f.lemma(p.le_add_right, &[one, four]);
        let congruence = f.concrete_mod_eq(five, ten, zero, zero, two);
        let proof = f.lemma(
            p.dvd_of_mod_eq_zero_of_pos,
            &[five, ten, positive, congruence],
        );
        let bad = f.dvd(five, eleven);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC60: positive congruence-to-zero converse must retain its value");
        println!(
            "NC60 (wrong positive-converse divisible value) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    // NC61 — the all-Nat characterization retains the same dividend on both sides.
    {
        let name = f.name("nc61_mod_eq_zero_iff_dvd_wrong_value");
        let zero = f.num(0);
        let five = f.num(5);
        let ten = f.num(10);
        let eleven = f.num(11);
        let proof = f.lemma(p.mod_eq_zero_iff_dvd, &[five, ten]);
        let congruence_ty = f.mod_eq(five, ten, zero);
        let wrong_divides_ty = f.dvd(five, eleven);
        let bad = f.const_app(p.logic.iff, &[congruence_ty, wrong_divides_ty]);
        let err = f
            .declare_theorem(name, bad, proof)
            .expect_err("NC61: the all-Nat characterization must retain its dividend");
        println!(
            "NC61 (wrong all-Nat characterization value) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    assert_eq!(rejections, 61, "every negative control must be rejected");
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
        19 + 117,
        "every promised definition and theorem must be rendered"
    );
}
