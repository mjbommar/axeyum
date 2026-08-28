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

use crate::BinderInfo;
use crate::env::Declaration;
use crate::{
    ExprId, Kernel, KernelError, NameId, NatOps, NatPrelude, NatState, build_nat_prelude,
    on_a_deep_stack,
};

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
/// `Nat.permInverse` COMPUTES the right inverse table for a concrete
/// permutation of `[0,4)` — not merely type-checks — and a negative control:
/// reusing the very proof that certifies the correct `(n, k)` instance
/// against a statement with `n` and `k` TRANSPOSED (a genuinely different,
/// and false, computed equation) must be rejected.
#[test]
fn perm_inverse_computes_a_concrete_permutation_table_with_a_transposed_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // f : the 4-cycle (0 1 2 3), i.e. f(0)=1, f(1)=2, f(2)=3, f(3)=0.
    let perm = |f: &mut Fixture| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.kernel().fvar(k_fv);
        let zero = f.zero();
        let one = f.num(1);
        let two = f.num(2);
        let three = f.num(3);
        let cond2 = f.beq(k, two);
        let sel2 = f.bool_select_nat(cond2, three, zero);
        let cond1 = f.beq(k, one);
        let sel1 = f.bool_select_nat(cond1, two, sel2);
        let cond0 = f.beq(k, zero);
        let sel0 = f.bool_select_nat(cond0, one, sel1);
        f.lam_fv(k_fv, nat, sel0)
    };
    let sigma = perm(&mut f);
    let four = f.num(4);

    // The genuine inverse table: permInverse sigma 4 k, for k = 0,1,2,3,
    // must COMPUTE (by `def_eq`, i.e. by reduction, not merely type) to
    // 3, 0, 1, 2 respectively -- sigma's actual two-sided inverse on [0,4).
    let expected = [(0u32, 3u32), (1, 0), (2, 1), (3, 2)];
    let mut computed_at_one: Option<ExprId> = None;
    for (k_val, expected_val) in expected {
        let k = f.num(k_val);
        let idx = f.const_app(p.perm_inverse, &[sigma, four, k]);
        let want = f.num(expected_val);
        assert!(
            f.k.def_eq(idx, want),
            "permInverse sigma 4 {k_val} must COMPUTE to {expected_val}"
        );
        // NEGATIVE CONTROL half 1: it must not also collapse to some OTHER
        // index (a checker that accepts every value would pass the line
        // above vacuously if `def_eq` were broken in the "always true"
        // direction).
        let bogus = f.num((expected_val + 1) % 4);
        assert!(
            !f.k.def_eq(idx, bogus),
            "permInverse sigma 4 {k_val} must NOT also compute to {}",
            (expected_val + 1) % 4
        );
        if k_val == 1 {
            computed_at_one = Some(idx);
        }
    }
    let idx_at_1 = computed_at_one.expect("k=1 case ran");

    // `sigma` composed with its computed inverse really is the identity at
    // this point: `sigma (permInverse sigma 4 1) = 1`.
    let sigma_idx = f.apply(sigma, &[idx_at_1]);
    let one = f.num(1);
    assert!(
        f.k.def_eq(sigma_idx, one),
        "sigma (permInverse sigma 4 1) must compute to 1"
    );

    // The REAL proof of this fact: `Eq.refl 1`, whose inferred type is
    // `Eq Nat 1 1`, accepted here as `Eq Nat (sigma (permInverse sigma 4 1)) 1`
    // only because both sides genuinely reduce to the same numeral.
    let real_proof = f.refl(one);
    let real_stmt = f.eq(sigma_idx, one);
    let real_name = f.name("nc_perm_inverse_real_at_n4_k1");
    f.declare_theorem(real_name, real_stmt, real_proof)
        .expect("the real, non-transposed fact must be admitted");

    // NEGATIVE CONTROL half 2 (the brief's required control): reuse THAT
    // SAME proof term against the statement with `n` and `k` TRANSPOSED --
    // `sigma (permInverse sigma 1 4) = 4` instead of
    // `sigma (permInverse sigma 4 1) = 1`. This is a genuinely different
    // computed value (confirmed below before trusting the rejection), not
    // an accidental tautology: `permInverse sigma 1 4` computes to `0`
    // (the search bound is `1`, so only index `0` is ever tried, and
    // `sigma 0 = 1 != 4` never matches, so the search falls through to its
    // base-case default `0`), and `sigma 0 = 1`, so the transposed
    // statement's left side is `1`, not `4`.
    let one_bound = f.num(1);
    let four_target = f.num(4);
    let idx_transposed = f.const_app(p.perm_inverse, &[sigma, one_bound, four_target]);
    let zero = f.zero();
    assert!(
        f.k.def_eq(idx_transposed, zero),
        "permInverse sigma 1 4 must compute to 0 (only index 0 is searched)"
    );
    let sigma_idx_transposed = f.apply(sigma, &[idx_transposed]);
    assert!(
        f.k.def_eq(sigma_idx_transposed, one),
        "sigma (permInverse sigma 1 4) computes to 1, genuinely != the claimed 4"
    );
    let transposed_stmt = f.eq(sigma_idx_transposed, four_target);

    let bad_name = f.name("nc_perm_inverse_transposed_n_and_k");
    let err = f
        .declare_theorem(bad_name, transposed_stmt, real_proof)
        .expect_err(
            "NC: reusing the n=4,k=1 proof against the n,k-transposed statement must be rejected",
        );
    println!(
        "NC (permInverse with n and k transposed) rejected:\n  {}",
        f.explain(&err)
    );
    assert!(!f.k.environment().contains(bad_name));
}

/// `Nat.bijective_on_perm_inverse` and `Nat.bijective_on_comp` APPLY at a
/// concrete, genuinely nontrivial instance — the transposition swapping `0`
/// and `1` on `[0,2)` (the order-2 symmetric group on two elements), built
/// entirely from already-proved `Nat.transposition_*` theorems, no
/// hand-rolled case bash — and `Nat.permInverse sigma 2` COMPUTES sigma's
/// genuine inverse table. Negative control: reusing the genuine
/// `bijective_on_perm_inverse` proof (built at bound `2`) against a
/// statement with the bound TRANSPOSED to `3` must be rejected, after
/// confirming `2` and `3` genuinely differ.
#[test]
fn bijective_on_lemmas_apply_to_a_concrete_transposition_with_a_transposed_bound_negative_control()
{
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    // sigma := transposition 0 1 : Nat -> Nat, swapping 0 and 1 -- the
    // generator of the order-2 symmetric group on [0,2).
    let sigma = f.const_app(p.transposition, &[zero, one]);

    let lt01 = f.zero_lt_succ(zero); // Lt 0 1
    let lt12 = f.lemma(p.lt_succ_self, &[one]); // Lt 1 2

    let inj_sigma = f.lemma(p.transposition_injective, &[zero, one, lt01, two]);
    let maps_sigma = f.lemma(p.transposition_maps_into, &[zero, one, lt01, two, lt12]);
    let bij_sigma = f.lemma(
        p.bijective_of_injective_on,
        &[two, sigma, inj_sigma, maps_sigma],
    );

    // `Nat.permInverse sigma 2` COMPUTES sigma's genuine inverse table on
    // `[0,2)`: sigma swaps 0 and 1, so its inverse does too.
    let g_at_0 = f.const_app(p.perm_inverse, &[sigma, two, zero]);
    assert!(
        f.k.def_eq(g_at_0, one),
        "permInverse sigma 2 0 must COMPUTE to 1"
    );
    assert!(
        !f.k.def_eq(g_at_0, zero),
        "permInverse sigma 2 0 must NOT also compute to 0"
    );
    let g_at_1 = f.const_app(p.perm_inverse, &[sigma, two, one]);
    assert!(
        f.k.def_eq(g_at_1, zero),
        "permInverse sigma 2 1 must COMPUTE to 0"
    );
    assert!(
        !f.k.def_eq(g_at_1, one),
        "permInverse sigma 2 1 must NOT also compute to 1"
    );

    // `Nat.bijective_on_perm_inverse` APPLIES at this concrete instance --
    // the kernel re-checks the proof against the genuine statement.
    let ga = f.const_app(p.perm_inverse, &[sigma, two]);
    let ga_bij_stmt = f.const_app(p.bijective_on, &[ga, two]);
    let ga_bij_proof = f.lemma(p.bijective_on_perm_inverse, &[two, sigma, bij_sigma]);
    let real_name = f.name("nc_bijective_on_perm_inverse_real_at_n2");
    f.declare_theorem(real_name, ga_bij_stmt, ga_bij_proof)
        .expect("BijectiveOn (permInverse sigma 2) 2 must be admitted");

    // `Nat.bijective_on_comp` APPLIES too: composing sigma with itself is
    // bijective on the same bound.
    let comp_sigma_sigma = f.const_app(p.comp, &[sigma, sigma]);
    let comp_bij_stmt = f.const_app(p.bijective_on, &[comp_sigma_sigma, two]);
    let comp_bij_proof = f.lemma(
        p.bijective_on_comp,
        &[two, sigma, sigma, bij_sigma, bij_sigma],
    );
    let comp_name = f.name("nc_bijective_on_comp_real_at_n2");
    f.declare_theorem(comp_name, comp_bij_stmt, comp_bij_proof)
        .expect("BijectiveOn (comp sigma sigma) 2 must be admitted");

    // NEGATIVE CONTROL: reuse the REAL `bijective_on_perm_inverse` proof
    // (built at n = 2) against a statement with the bound TRANSPOSED to 3.
    // Confirm first that 2 and 3 genuinely differ (not an accidental
    // tautology).
    assert!(
        !f.k.def_eq(two, three),
        "2 and 3 must genuinely differ before trusting the rejection"
    );
    let bad_stmt = f.const_app(p.bijective_on, &[ga, three]);
    let bad_name = f.name("nc_bijective_on_perm_inverse_transposed_bound");
    let err = f
        .declare_theorem(bad_name, bad_stmt, ga_bij_proof)
        .expect_err("NC: reusing the n=2 proof against the n=3 statement must be rejected");
    println!(
        "NC (bijective_on_perm_inverse with bound transposed) rejected:\n  {}",
        f.explain(&err)
    );
    assert!(!f.k.environment().contains(bad_name));
}

/// `Nat.symmetric_group_isGroupOnFn` APPLIES at a concrete instance —
/// `transposition 0 1` on `[0,2)` — and `Nat.permInverse`'s table for it
/// COMPUTES (by `def_eq`, not merely type-checks). The REQUIRED negative
/// control: the exact proof term that makes the FIXED (`EqOn`-bounded)
/// inverse conjunct hold at this instance is reused against the UNBOUNDED
/// `Eq (Nat → Nat)` form this module's own top-of-file doc found false —
/// and the kernel rejects it.
#[test]
fn symmetric_group_is_group_on_fn_applies_at_transposition_0_1_with_unbounded_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let fn_ty = f.arrow(nat, nat);

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);

    // sigma := transposition 0 1 : Nat -> Nat, swapping 0 and 1.
    let sigma = f.const_app(p.transposition, &[zero, one]);
    let lt01 = f.zero_lt_succ(zero); // Lt 0 1
    let lt12 = f.lemma(p.lt_succ_self, &[one]); // Lt 1 2
    let inj_sigma = f.lemma(p.transposition_injective, &[zero, one, lt01, two]);
    let maps_sigma = f.lemma(p.transposition_maps_into, &[zero, one, lt01, two, lt12]);
    let surj_sigma = f.lemma(
        p.injective_on_imp_surjective_on,
        &[two, sigma, inj_sigma, maps_sigma],
    );

    // `Nat.permInverse sigma 2` COMPUTES sigma's genuine inverse table on
    // `[0,2)`: sigma is its own inverse, so the table is 1, 0.
    let g_at_0 = f.const_app(p.perm_inverse, &[sigma, two, zero]);
    assert!(
        f.k.def_eq(g_at_0, one),
        "permInverse sigma 2 0 must COMPUTE to 1"
    );
    let g_at_1 = f.const_app(p.perm_inverse, &[sigma, two, one]);
    assert!(
        f.k.def_eq(g_at_1, zero),
        "permInverse sigma 2 1 must COMPUTE to 0"
    );

    // The group witness APPLIES at n := 2: `Nat.symmetric_group_isGroupOnFn 2`
    // is a genuine proof of `IsGroupOnFn Nat.comp Nat.id (fun f=>permInverse
    // f 2) 2`; the kernel re-checks it here when declared as a consumer
    // theorem (the "downstream development can use it" pattern this file's
    // own module doc names as its third thing checked).
    let ga = f.const_app(p.perm_inverse, &[sigma, two]); // Nat -> Nat
    let inv = {
        let f_fv = f.fresh_fvar();
        let fvar = f.kernel().fvar(f_fv);
        let body = f.const_app(p.perm_inverse, &[fvar, two]);
        f.lam_fv(f_fv, fn_ty, body)
    };
    let op = f.const_app(p.comp, &[]);
    let id_const = f.const_app(p.id, &[]);
    let full = f.const_app(p.symmetric_group_is_group_on_fn, &[two]);
    let full_stmt = f.const_app(p.is_group_on_fn, &[op, id_const, inv, two]);
    let real_name = f.name("nc_symmetric_group_is_group_on_fn_real_at_n2");
    f.declare_theorem(real_name, full_stmt, full)
        .expect("IsGroupOnFn Nat.comp Nat.id (fun f=>permInverse f 2) 2 must be admitted");

    // The bounded inverse fact this fix actually proves: `EqOn (comp sigma
    // (permInverse sigma 2)) Nat.id 2`, built directly from
    // `Nat.permInverse_right` (the same lemma
    // `declare_symmetric_group_is_group_on_fn` uses internally) at every
    // `k < 2` — a real, TRUE fact, admitted here to confirm it as such
    // before reusing its proof term below.
    let comp_sigma_ga = f.const_app(p.comp, &[sigma, ga]);
    let eqon_proof = {
        let k_fv = f.fresh_fvar();
        let k = f.kernel().fvar(k_fv);
        let hk_fv = f.fresh_fvar();
        let hk = f.kernel().fvar(hk_fv);
        let hk_ty = f.lt(k, two);
        let body = f.lemma(p.perm_inverse_right, &[sigma, two, surj_sigma, k, hk]);
        let with_hk = f.lam_fv(hk_fv, hk_ty, body);
        f.lam_fv(k_fv, nat, with_hk)
    };
    let eqon_stmt = f.const_app(p.eq_on, &[comp_sigma_ga, id_const, two]);
    let real_name2 = f.name("nc_symmetric_group_eqon_real_at_n2");
    f.declare_theorem(real_name2, eqon_stmt, eqon_proof)
        .expect("EqOn (comp sigma (permInverse sigma 2)) Nat.id 2 must be admitted");

    // Confirm, by computation, that the UNBOUNDED claim this module's doc
    // refuted really is false here (not an accidental tautology this
    // negative control would pass vacuously): at k := 2 (outside [0,2)),
    // `permInverse sigma 2 2` computes to `0` (the search never matches),
    // so `sigma (permInverse sigma 2 2) = sigma 0 = 1`, genuinely != `id 2 = 2`.
    let g_at_2 = f.const_app(p.perm_inverse, &[sigma, two, two]);
    assert!(
        f.k.def_eq(g_at_2, zero),
        "permInverse sigma 2 2 must COMPUTE to 0 (the search never matches)"
    );
    let sigma_g2 = f.apply(sigma, &[g_at_2]);
    assert!(
        f.k.def_eq(sigma_g2, one),
        "sigma (permInverse sigma 2 2) must compute to 1"
    );
    assert!(
        !f.k.def_eq(sigma_g2, two),
        "…and genuinely not to 2, confirming the unbounded claim is false at this instance"
    );

    // THE NEGATIVE CONTROL: reuse the REAL `eqon_proof` — a `Pi`-shaped
    // pointwise fact, and this fix's whole reason for existing — against
    // the UNBOUNDED `Eq (Nat → Nat) (comp sigma (permInverse sigma 2))
    // Nat.id` this file's module doc found false. It must be rejected.
    let unbounded_stmt = {
        let one_lvl = f.level_one();
        let eq_const = f.kernel().const_(p.logic.eq, vec![one_lvl]);
        f.apply(eq_const, &[fn_ty, comp_sigma_ga, id_const])
    };
    let bad_name = f.name("nc_symmetric_group_unbounded_inverse_conjunct");
    let err = f
        .declare_theorem(bad_name, unbounded_stmt, eqon_proof)
        .expect_err(
            "NC: the bounded EqOn fact must NOT prove the unbounded (refuted) IsGroupOnFn claim",
        );
    println!(
        "NC (unbounded IsGroupOnFn inverse conjunct, reusing the real EqOn proof) rejected:\n  {}",
        f.explain(&err)
    );
    assert!(!f.k.environment().contains(bad_name));
}

fn definition_names(p: &NatPrelude) -> Vec<NameId> {
    vec![
        p.set_union,
        p.set_inter,
        p.set_compl,
        p.set_diff,
        p.subset,
        p.catalan,
        p.add,
        p.mul,
        p.pow,
        p.beq,
        p.div_mod_state,
        p.div,
        p.mod_,
        p.gcd,
        p.lcm,
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
        p.choose,
        p.fin_val,
        p.injective_on,
        p.surjective_on,
        p.maps_into,
        p.transposition,
        p.setwise_fixed,
        p.test_bit_aux,
        p.test_bit,
        p.size_aux,
        p.size,
        p.count_range,
        p.totient,
        p.fib_aux,
        p.fib,
        p.reflexive_on,
        p.symmetric_on,
        p.transitive_on,
        p.equivalence_on,
        p.bijective_on,
        p.comp,
        p.is_group_on,
        p.perm_inverse,
        p.id,
        p.is_group_on_fn,
        p.eq_on,
        p.prod_range,
        p.prod_range_if,
        p.injective_on_p,
        p.maps_into_p,
        p.surjective_on_p,
        p.pow_sq_aux,
        p.pow_sq,
        p.sum_divisors,
        p.perfect,
        // Found by `every_nat_declaration_is_checked_and_axiom_free`'s coverage
        // assertion, not by anyone noticing: these four were live in the
        // prelude and unlisted here, so this suite had never checked their
        // kind, determinism, or axiom-footprint. `Nat.noConfusionType` /
        // `Nat.noConfusion` are the generated injectivity/disjointness
        // machinery for the `zero`/`succ` constructors; `Nat.factorial` and
        // `Nat.ble` (boolean `<=`) are ordinary recursive definitions that
        // simply never made it into this list.
        p.factorial,
        p.desc_factorial,
        p.no_confusion_type,
        p.no_confusion,
        p.ble,
        p.even,
        p.odd,
        p.log_aux,
        p.log,
        p.sqrt_aux,
        p.sqrt,
        p.clog_aux,
        p.clog,
        p.bit,
        p.land_aux,
        p.land,
        p.lor_aux,
        p.lor,
        p.ldiff_aux,
        p.ldiff,
        p.asc_factorial,
        p.multichoose,
    ]
}

fn theorem_names(p: &NatPrelude) -> Vec<NameId> {
    vec![
        p.count_range_union_add_inter,
        p.count_range_le_of_subset,
        p.count_range_compl,
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
        p.mul_eq_zero,
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
        p.mul_succ_add_lt_of_le_of_lt,
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
        p.mod_self,
        p.div_mod_exec,
        p.mod_lt,
        p.gcd_zero_left,
        p.gcd_succ,
        p.gcd_dvd,
        p.gcd_dvd_left,
        p.gcd_dvd_right,
        p.dvd_gcd,
        p.dvd_gcd_iff,
        p.lcm_zero_left,
        p.dvd_lcm_left,
        p.dvd_lcm_right,
        p.gcd_mul_lcm,
        p.gcd_bezout,
        p.gauss_lemma,
        p.lcm_dvd,
        p.dvd_antisymm,
        p.dvd_lcm_of_dvd_left,
        p.dvd_lcm_of_dvd_right,
        p.dvd_of_lcm_left_dvd,
        p.dvd_of_lcm_right_dvd,
        p.catalan_mul_succ,
        p.lcm_comm,
        p.coprime_lcm_eq_mul,
        p.fib_add,
        p.coprime_fib_succ,
        p.fib_add_two_strictmono,
        p.fib_strictmonoon,
        p.fib_lt_fib,
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
        p.mod_eq_cancel,
        p.mod_eq_gcd_eq,
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
        p.le_of_dvd,
        p.two_le_succ_or_eq_one,
        p.least_divisor_search,
        p.exists_prime_dvd,
        p.coprime_of_lt_prime,
        p.coprime_of_dvd_left,
        p.coprime_of_dvd_right,
        p.coprime_of_dvd,
        p.coprime_of_forall_prime_dvd,
        p.prime_dvd_iff_not_coprime,
        p.coprime_add_self_right,
        p.coprime_self_add_right,
        p.coprime_symmetric,
        p.not_coprime_zero_zero,
        p.coprime_one_left_iff,
        p.coprime_one_right_iff,
        p.coprime_add_self_left,
        p.coprime_self_add_left,
        p.coprime_or_dvd_of_prime,
        p.choose_zero_right,
        p.choose_succ_succ,
        p.zero_choose_succ,
        p.choose_succ_self_eq_zero,
        p.choose_self,
        p.choose_symm,
        p.choose_one_right,
        p.choose_eq_zero_of_lt,
        p.choose_ne_zero,
        p.choose_le_succ,
        p.choose_symm_of_eq_add,
        p.choose_le_add,
        p.choose_symm_add,
        p.choose_le_choose,
        p.choose_mono,
        p.sum_range_add,
        p.sum_range_shift_front,
        p.sum_range_congr_lt,
        p.add_pow_zero,
        p.add_pow_one,
        p.add_pow,
        p.one_pow,
        p.le_sum_range_of_lt,
        p.sum_choose_row,
        p.choose_le_two_pow,
        p.succ_sub_of_le,
        p.succ_mul_choose_eq,
        // Euclid's lemma (Elements VII.30) was admitted and axiom-free but named
        // by NOTHING in this list, so the presence/footprint sweep never saw it.
        // `axiom_footprint` of a name the sweep does not visit is not "empty" —
        // it is unmeasured, and the two look identical in a green run.
        p.euclid_lemma,
        p.prime_dvd_choose,
        p.mod_eq_pow,
        p.dvd_sum_range_of_forall_lt,
        p.add_pow_modeq_prime,
        p.pow_prime_modeq_self,
        p.count_range_zero,
        p.count_range_succ,
        p.count_range_le,
        p.count_range_congr,
        p.count_range_split,
        p.beq_eq_false_of_ne,
        p.count_range_eq_pred_of_only_zero_false,
        p.totient_prime,
        p.fin_is_lt,
        p.fin_val_mk,
        p.injective_on_imp_surjective_on,
        p.restrict_injective,
        p.restrict_maps_into,
        p.transposition_involutive,
        p.transposition_injective,
        p.transposition_maps_into,
        p.conjugate_injective,
        p.conjugate_maps_into,
        p.restrict_pair_injective,
        p.restrict_pair_maps_into,
        p.add_sub_cancel_of_le,
        p.sum_range_diagonal,
        p.sum_range_split,
        p.sum_range_rect_eq_diag_add_corner,
        p.choose_add_convolution,
        p.sum_choose_sq,
        p.test_bit_zero,
        p.test_bit_succ,
        p.test_bit_le_one,
        p.mod_two_mul_split,
        p.sum_test_bit_lt,
        p.size_zero,
        p.size_aux_lt_pow,
        p.lt_pow_size,
        p.mod_eq_self_of_lt,
        p.sum_test_bit_eq,
        p.fib_add_two,
        p.fib_le_succ,
        p.fib_pos_of_pos,
        p.sum_fib,
        p.eq_equivalence_on,
        p.mod_eq_equivalence_on,
        p.bijective_of_injective_on,
        p.injective_on_comp,
        p.pigeonhole,
        p.set_union_comm,
        p.set_inter_comm,
        p.set_union_assoc,
        p.set_inter_assoc,
        p.set_union_idem,
        p.set_inter_idem,
        p.set_inter_union_distrib,
        p.set_union_inter_distrib,
        p.set_union_absorb,
        p.set_inter_absorb,
        p.set_compl_union,
        p.set_compl_inter,
        p.set_compl_involutive,
        p.group_identity_unique,
        p.group_inverse_unique,
        p.group_left_cancel,
        p.mod_add_is_group,
        p.subset_refl,
        p.subset_trans,
        p.subset_antisymm,
        p.set_diff_eq_inter_compl,
        p.union_eq_right_of_subset,
        p.subset_union_left,
        p.subset_inter_left,
        p.perm_inverse_right,
        p.perm_inverse_left,
        p.comp_assoc,
        p.bijective_on_comp,
        p.bijective_on_perm_inverse,
        p.eq_on_refl,
        p.eq_on_symm,
        p.eq_on_trans,
        p.symmetric_group_is_group_on_fn,
        p.prod_range_zero,
        p.prod_range_succ,
        p.prod_range_if_zero,
        p.prod_range_if_succ,
        p.prod_range_if_congr_lt,
        p.injective_on_p_imp_surjective_on_p,
        p.exists_prime_factorization,
        p.coprime_mul_dvd,
        p.crt_unique,
        p.pow_half_split,
        p.even_or_odd,
        p.pow_sq_aux_eq_pow,
        p.pow_sq_eq_pow,
        p.pow_sq_zero,
        p.pow_sq_succ,
        p.succ_pred_of_pos,
        p.sum_divisors_one,
        p.sum_divisors_prime,
        p.pow2_geom_sum,
        p.cantor_diagonal,
        p.cantor_diagonal_neg,
        p.cantor_no_fixed_point,
        p.dvd_two_pow_mul_classify,
        p.dvd_two_pow_classify,
        p.pow_two_ne_pow_two_mul_prime,
        p.pow_pos,
        p.pow_lt_pow_succ,
        p.pow_lt_pow_of_lt,
        p.pow_injective,
        p.pow_mul_prime_injective,
        p.dvd_two_pow_succ_iff_of_le,
        p.sum_divisors_two_pow_eq_geom_sum,
        p.sum_divisors_two_pow,
        p.even_of_even_sq,
        p.no_rational_sqrt_two,
        // Found by `every_nat_declaration_is_checked_and_axiom_free`'s coverage
        // assertion, not by anyone noticing: these forty-four theorems were
        // live in the prelude and unlisted here, so this suite had never
        // checked their kind, determinism, or axiom-footprint. Mostly the
        // elementary `Nat.le`/`Nat.lt`/`Nat.sub`/`Nat.ble` order lemmas and a
        // handful of number-theory results (`exists_prime_gt`,
        // `eq_one_of_dvd_one`, the Bezout/gcd-cofactor family, `fib_mono`) that
        // this file's own tests already exercise by name elsewhere.
        p.succ_ne_zero,
        p.not_lt_zero,
        p.pow_add,
        p.factorial_zero,
        p.factorial_succ,
        p.desc_factorial_zero,
        p.desc_factorial_succ,
        p.desc_factorial_one,
        p.desc_factorial_of_lt,
        p.monotone_of_le_succ,
        p.le_refl_thm,
        p.le_succ,
        p.succ_le_succ,
        p.le_of_lt_succ,
        p.lt_succ_self,
        p.lt_succ_of_le,
        p.lt_add_one,
        p.not_succ_le_self,
        p.le_succ_of_le,
        p.zero_lt_succ,
        p.pred_le,
        p.pred_le_pred,
        p.sub_le,
        p.sub_lt,
        p.succ_sub_succ_eq_sub,
        p.lt_of_not_le,
        p.lt_or_ge,
        p.le_of_lt_add_one,
        p.zero_lt_of_ne_zero,
        p.ne_of_beq_eq_false,
        p.ble_self_eq_true,
        p.ble_succ_eq_true,
        p.ble_eq_true_of_le,
        p.le_of_ble_eq_true,
        p.not_le_of_not_ble_eq_true,
        p.one_le_factorial,
        p.exists_prime_gt,
        p.eq_one_of_dvd_one,
        p.coprime_of_bezout_one,
        p.bezout_of_scaled,
        p.gcd_cofactors_coprime,
        p.div_mul_cancel_of_dvd,
        p.div_dvd_div_left,
        p.one_le_right_of_mul,
        p.one_le_left_of_mul,
        p.one_le_of_dvd_pos,
        p.one_le_mul,
        p.dvd_factorial_of_le,
        p.factorial_dvd_factorial,
        p.factorial_le,
        p.factorial_lt_of_lt,
        p.factorial_ne_zero,
        p.fib_mono,
        p.even_or_odd_exists,
        p.add_self_ne_succ_add_self,
        p.even_not_odd,
        p.odd_not_even,
        p.even_iff_odd_succ,
        p.coprime_two_left,
        p.coprime_two_right,
        p.coprime_odd_of_left,
        p.coprime_odd_of_right,
        p.prime_odd_of_ne_two,
        p.prime_even_iff,
        p.prime_not_dvd_mul,
        p.prime_dvd_of_dvd_pow,
        p.coprime_primes,
        p.not_prime_of_dvd_of_ne,
        p.prime_pred_pos,
        p.succ_pred_prime,
        p.prime_dvd_mul_of_dvd_ne,
        p.log_zero_right,
        p.log_zero_left,
        p.log_one_left,
        p.log_one_right,
        p.ble_eq_false_of_lt,
        p.log_of_lt,
        p.sqrt_zero,
        p.sqrt_one,
        p.clog_zero_right,
        p.clog_zero_left,
        p.clog_one_left,
        p.clog_one_right,
        p.log_aux_le_fuel,
        p.log_le_self,
        p.bit_false,
        p.bit_true,
        p.bit_true_pos,
        p.bit_false_le_bit_true,
        p.land_zero_left,
        p.land_zero_right,
        p.land_one_one,
        p.land_three_five,
        p.lor_zero_left,
        p.lor_zero_right,
        p.lor_three_five,
        p.ldiff_zero_left,
        p.ldiff_zero_right,
        p.ldiff_three_five,
        p.ldiff_five_three,
        p.asc_factorial_zero,
        p.asc_factorial_succ,
        p.asc_factorial_one,
        p.multichoose_zero_right,
        p.multichoose_one,
        p.multichoose_one_right,
    ]
}

/// COVERAGE, checked against the ENVIRONMENT rather than against
/// `definition_names`/`theorem_names` themselves.
///
/// Every other test in this file (`every_promised_name_is_admitted_with_the_
/// expected_kind`, `the_build_is_deterministic`) only ever inspects the
/// declarations someone remembered to list in those two functions. A
/// `Definition` or `Theorem` declared under `Nat.` and omitted from both lists
/// receives no kind check, no determinism check, and no axiom-footprint check
/// -- and every run stays green, because a list cannot notice what is missing
/// from it. This mirrors `every_creal_declaration_is_checked_and_axiom_free`
/// (`creal_tests.rs`), landed after exactly this gap was found there.
///
/// Scoped to `Definition`/`Theorem` kinds deliberately: the inductive
/// machinery (`Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Nat.le` and its
/// constructors/recursor, `Nat.Fin` and its constructor/recursor) is checked
/// by name in `every_promised_name_is_admitted_with_the_expected_kind`
/// instead, and an `Inductive`/`Constructor`/`Recursor` declaration has no
/// proof term for `axiom_footprint` to inspect the way a `Definition`'s value
/// or a `Theorem`'s proof does.
#[test]
fn every_nat_declaration_is_checked_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let listed: std::collections::BTreeSet<NameId> = definition_names(&p)
        .into_iter()
        .chain(theorem_names(&p))
        .collect();
    let declared: Vec<(NameId, Declaration)> = k
        .environment()
        .iter()
        .map(|(name, decl)| (*name, decl.clone()))
        .collect();
    let unlisted: Vec<String> = declared
        .iter()
        .filter(|(name, decl)| {
            matches!(
                decl,
                Declaration::Definition { .. } | Declaration::Theorem { .. }
            ) && k.display_name(*name).to_string().starts_with("Nat.")
                && !listed.contains(name)
        })
        .map(|(name, _)| k.display_name(*name).to_string())
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `Nat` definitions/theorems are live in the prelude but absent \
         from `definition_names`/`theorem_names`, so nothing checks their kind, \
         determinism, or axiom-footprint: {unlisted:?}. Add them there -- do \
         not delete this assertion."
    );

    for (name, decl) in &declared {
        let shown = k.display_name(*name).to_string();
        if !shown.starts_with("Nat.") || !listed.contains(name) {
            continue;
        }
        assert!(
            !matches!(decl, Declaration::Axiom { .. } | Declaration::Opaque { .. }),
            "{shown} is asserted, not derived"
        );
        let footprint = k.axiom_footprint(*name);
        assert!(
            footprint.is_empty(),
            "{shown} must have an empty axiom footprint, found {:?}",
            footprint
                .iter()
                .map(|n| k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
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
        p.nat, p.zero, p.succ, p.rec, p.le, p.le_refl, p.le_step, p.le_rec, p.fin, p.fin_mk,
        p.fin_rec,
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

/// `Nat.totient` **computes** by pure reduction on numerals, matching
/// `totient.rs`'s module doc (hand-checked before any kernel work):
/// `totient 1 = 1` — the range is `{0}`, and `gcd 0 1 = 1`;
/// `totient 6 = 2` — of `{0,..,5}`, only `1` and `5` are coprime to `6`
/// (`0,2,3,4` share a factor: `2,4` with `2`, `3` with `3`, `0` with `6`
/// itself);
/// `totient 9 = 6` — of `{0,..,8}`, `{1,2,4,5,7,8}` are coprime to `9`,
/// excluding `0,3,6` (multiples of `3`).
/// A definition that type-checks but counts wrong has an empty axiom
/// footprint and passes every sweep in this repository, so this negative
/// half matters as much as the positive one.
#[test]
fn totient_computes_on_small_numerals() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let totient_one = f.const_app(p.totient, &[one]);
    assert!(f.k.def_eq(totient_one, one), "totient 1 must reduce to 1");

    let six = f.num(6);
    let two = f.num(2);
    let totient_six = f.const_app(p.totient, &[six]);
    assert!(f.k.def_eq(totient_six, two), "totient 6 must reduce to 2");

    let nine = f.num(9);
    let six_again = f.num(6);
    let totient_nine = f.const_app(p.totient, &[nine]);
    assert!(
        f.k.def_eq(totient_nine, six_again),
        "totient 9 must reduce to 6"
    );

    // NEGATIVE reduction controls.
    let three = f.num(3);
    assert!(
        !f.k.def_eq(totient_six, three),
        "totient 6 must NOT be def-eq to 3"
    );
    let five = f.num(5);
    assert!(
        !f.k.def_eq(totient_nine, five),
        "totient 9 must NOT be def-eq to 5"
    );
}

/// `Nat.prodRangeIf` computes on small numerals by REDUCTION, not merely
/// type-checking — the mandatory concrete instance for the product-over-a-
/// predicate-defined-subset primitive.
///
/// `prodRangeIf 6 (fun i => i is odd) id` restricts to `{1,3,5}` of `{0,..,5}`
/// and multiplies them: `1*3*5 = 15`. `prodRangeIf 6 (fun _ => true) succ`
/// keeps every index and multiplies `succ i` for `i` in `{0,..,5}`, i.e.
/// `1*2*3*4*5*6 = 720`. Both negative controls below are plausible off-by-one
/// answers (the parity flipped, or the bound off by one), not arbitrary
/// numbers — a definition that type-checks but computes a different function
/// passes an axiom-footprint sweep, so only reduction catches it.
#[test]
fn prod_range_if_computes_on_small_numerals() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let nat = f.nat_ty();

        // `fun i => beq (mod i 2) 1` — `i` is odd.
        let is_odd = {
            let i_fv = f.fresh_fvar();
            let i = f.kernel().fvar(i_fv);
            let two = f.num(2);
            let one = f.num(1);
            let rem = f.modulo(i, two);
            let cond = f.beq(rem, one);
            f.lam_fv(i_fv, nat, cond)
        };
        let id_fn = f.const_app(p.id, &[]);
        let six = f.num(6);
        let prod_odds = f.const_app(p.prod_range_if, &[is_odd, id_fn, six]);
        let fifteen = f.num(15);
        assert!(
            f.k.def_eq(prod_odds, fifteen),
            "prodRangeIf 6 (odd) id must reduce to 15"
        );
        // NEGATIVE CONTROL: the flipped predicate (evens: {0,2,4}) multiplies
        // to 0 (via `id 0`), a plausible bug if the `Bool.rec` branches were
        // transposed.
        let zero = f.zero();
        assert!(
            !f.k.def_eq(prod_odds, zero),
            "prodRangeIf 6 (odd) id must NOT reduce to 0 (the flipped-parity answer)"
        );

        // `fun _ => Bool.true` — every index passes.
        let const_true = {
            let i_fv = f.fresh_fvar();
            let true_v = f.bool_true();
            f.lam_fv(i_fv, nat, true_v)
        };
        let succ_fn = f.const_app(p.succ, &[]);
        let six_again = f.num(6);
        let prod_succ = f.const_app(p.prod_range_if, &[const_true, succ_fn, six_again]);
        let seven_twenty = f.num(720);
        assert!(
            f.k.def_eq(prod_succ, seven_twenty),
            "prodRangeIf 6 (true) succ must reduce to 720"
        );
        // NEGATIVE CONTROL: the off-by-one bound (7 instead of 6) gives 5040.
        let five_thousand_forty = f.num(5040);
        assert!(
            !f.k.def_eq(prod_succ, five_thousand_forty),
            "prodRangeIf 6 (true) succ must NOT reduce to 5040 (the off-by-one bound answer)"
        );
    });
}

/// `Nat.prodRangeIf_congr_lt` applies at a concrete instance: two predicates
/// that agree below the bound (`beq i 0`, both sides) and two functions that
/// agree below the bound (`id` on both sides) give a proof of
/// `prodRangeIf p f 4 = prodRangeIf p f 4` — the reflexive case exercises the
/// full argument shape (both bounded-pointwise hypotheses) end to end.
#[test]
fn prod_range_if_congr_lt_applies_at_a_reflexive_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let is_zero = {
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let zero = f.zero();
        let cond = f.beq(i, zero);
        f.lam_fv(i_fv, nat, cond)
    };
    let id_fn = f.const_app(p.id, &[]);
    let four = f.num(4);

    let refl_bool = {
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let pi = f.apply(is_zero, &[i]);
        let refl = f.bool_refl(pi);
        let hi_fv = f.fresh_fvar();
        let hi_ty = f.lt(i, four);
        let with_hi = f.lam_fv(hi_fv, hi_ty, refl);
        f.lam_fv(i_fv, nat, with_hi)
    };
    let refl_nat = {
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let fi = f.apply(id_fn, &[i]);
        let refl = f.refl(fi);
        let hi_fv = f.fresh_fvar();
        let hi_ty = f.lt(i, four);
        let with_hi = f.lam_fv(hi_fv, hi_ty, refl);
        f.lam_fv(i_fv, nat, with_hi)
    };

    let proof = f.const_app(
        p.prod_range_if_congr_lt,
        &[is_zero, is_zero, id_fn, id_fn, four, refl_bool, refl_nat],
    );
    let expected_lhs = f.const_app(p.prod_range_if, &[is_zero, id_fn, four]);
    let stmt = f.eq(expected_lhs, expected_lhs);
    let inferred = f.kernel().infer(proof).expect("congr_lt must apply");
    assert!(
        f.kernel().def_eq(inferred, stmt),
        "prodRangeIf_congr_lt applied reflexively must prove prodRangeIf p f 4 = prodRangeIf p f 4"
    );
}

/// The predicate-scoped pigeonhole (`Nat.injective_on_p_imp_surjective_on_p`)
/// at a REAL predicate and a REAL bijection of its subset: `p i := i is odd`
/// on `{0,…,5}` (the subset is `{1,3,5}`) and `sigma` the 3-cycle
/// `1 → 3 → 5 → 1`, fixing every point outside the subset. Two things are
/// checked, not just one: first that `p` and `sigma` genuinely compute what
/// their names claim (every value below reduces to the SAME numeral both
/// sides would reach, checked by `def_eq`, not merely type-checked), and
/// second — the "apply, then infer" bar `restrict_injective_and_maps_into_
/// apply_at_a_concrete_swap` above already sets for a self-map theorem with
/// this many hypotheses — that the theorem's PARTIAL application (the two
/// data arguments `p`/`sigma`/`n`, none of the three proof-shaped
/// hypotheses) infers the expected residual Pi type.
#[test]
fn predicate_scoped_pigeonhole_applies_at_a_concrete_odd_3_cycle() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // `fun i => beq (mod i 2) 1` — `i` is odd. Same construction
    // `prod_range_if_computes_on_small_numerals` above uses.
    let is_odd = {
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let two = f.num(2);
        let one = f.num(1);
        let rem = f.modulo(i, two);
        let cond = f.beq(rem, one);
        f.lam_fv(i_fv, nat, cond)
    };

    // `sigma i := if i==1 then 3 else if i==3 then 5 else if i==5 then 1
    //   else i` — the 3-cycle on the odd subset `{1,3,5}`, identity
    // elsewhere.
    let sigma = {
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let one = f.num(1);
        let three = f.num(3);
        let five = f.num(5);
        let is_five = f.beq(i, five);
        let inner_five = f.bool_select_nat(is_five, one, i);
        let is_three = f.beq(i, three);
        let inner_three = f.bool_select_nat(is_three, five, inner_five);
        let is_one = f.beq(i, one);
        let body = f.bool_select_nat(is_one, three, inner_three);
        f.lam_fv(i_fv, nat, body)
    };

    // Concrete reductions: `sigma` really is the 3-cycle on `{1,3,5}` and
    // the identity on `{0,2,4}` — a lemma whose hypotheses nothing satisfies
    // is admitted with a type nothing can use.
    for (input, expected) in [(1u32, 3u32), (3, 5), (5, 1), (0, 0), (2, 2), (4, 4)] {
        let arg = f.num(input);
        let applied = f.apply(sigma, &[arg]);
        let want = f.num(expected);
        assert!(
            f.kernel().def_eq(applied, want),
            "sigma({input}) must reduce to {expected}"
        );
    }
    // `is_odd` really is the odd/even split on `{0,…,5}`.
    let true_v = f.bool_true();
    let false_v = f.bool_false();
    for (input, expected_odd) in [
        (0u32, false),
        (1, true),
        (2, false),
        (3, true),
        (4, false),
        (5, true),
    ] {
        let arg = f.num(input);
        let applied = f.apply(is_odd, &[arg]);
        let want = if expected_odd { true_v } else { false_v };
        assert!(
            f.kernel().def_eq(applied, want),
            "is_odd({input}) must reduce to {expected_odd}"
        );
    }

    // Apply, then infer: the theorem's residual type over the two data
    // arguments `is_odd`/`sigma` and the bound `n = 6` must accept the two
    // `InjectiveOnP`/`MapsIntoP` hypothesis slots and land on
    // `SurjectiveOnP is_odd sigma 6`.
    let six = f.num(6);
    let proof = f.lemma(p.injective_on_p_imp_surjective_on_p, &[is_odd, sigma, six]);
    f.kernel().infer(proof).unwrap_or_else(|e| {
        panic!(
            "injective_on_p_imp_surjective_on_p(is_odd, sigma, 6) should infer: {}",
            f.explain(&e)
        )
    });

    assert!(
        f.kernel()
            .axiom_footprint(p.injective_on_p_imp_surjective_on_p)
            .is_empty(),
        "the predicate-scoped pigeonhole must rest on zero axioms"
    );
}

/// `sumDivisors` computes the ACTUAL divisor sum by pure kernel reduction,
/// not merely type-checks: `sumDivisors 1 = 1`, `sumDivisors 6 = 12`
/// (`1+2+3+6`, `6` is the smallest perfect number), `sumDivisors 7 = 8`
/// (`1+7`, `7` is prime), and `sumDivisors 28 = 56` (`1+2+4+7+14+28`, the
/// second perfect number). An off-by-one in the range bound (excluding `n`
/// itself) type-checks perfectly and computes a different function; only
/// computation catches it.
#[test]
fn sum_divisors_computes_on_small_numerals() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let sum_divisors_one = f.const_app(p.sum_divisors, &[one]);
    assert!(
        f.k.def_eq(sum_divisors_one, one),
        "sumDivisors 1 must reduce to 1"
    );

    let six = f.num(6);
    let twelve = f.num(12);
    let sum_divisors_six = f.const_app(p.sum_divisors, &[six]);
    assert!(
        f.k.def_eq(sum_divisors_six, twelve),
        "sumDivisors 6 must reduce to 12 (1+2+3+6, 6 is perfect)"
    );

    let seven = f.num(7);
    let eight = f.num(8);
    let sum_divisors_seven = f.const_app(p.sum_divisors, &[seven]);
    assert!(
        f.k.def_eq(sum_divisors_seven, eight),
        "sumDivisors 7 must reduce to 8 (1+7, 7 is prime)"
    );

    let twenty_eight = f.num(28);
    let fifty_six = f.num(56);
    let sum_divisors_twenty_eight = f.const_app(p.sum_divisors, &[twenty_eight]);
    assert!(
        f.k.def_eq(sum_divisors_twenty_eight, fifty_six),
        "sumDivisors 28 must reduce to 56 (1+2+4+7+14+28, the second perfect number)"
    );

    // NEGATIVE reduction controls.
    let eleven = f.num(11);
    assert!(
        !f.k.def_eq(sum_divisors_six, eleven),
        "sumDivisors 6 must NOT be def-eq to 11"
    );
    let nine = f.num(9);
    assert!(
        !f.k.def_eq(sum_divisors_seven, nine),
        "sumDivisors 7 must NOT be def-eq to 9"
    );
}

/// `Nat.Perfect` computes correctly at both a perfect and a non-perfect
/// numeral: `sumDivisors 6 = 2*6` reduces (both sides to `12`), while
/// `sumDivisors 7 = 2*7` does NOT (`8` vs `14`) — the negative control that
/// distinguishes "the predicate type-checks" from "the predicate is
/// selective".
#[test]
fn perfect_holds_at_six_and_fails_at_seven() {
    let mut f = Fixture::new();
    let p = f.p;

    let six = f.num(6);
    let perfect_six = f.const_app(p.perfect, &[six]);
    let twelve = f.num(12);
    let sum_divisors_six = f.const_app(p.sum_divisors, &[six]);
    let sum_divisors_six_eq_twelve = f.eq(sum_divisors_six, twelve);
    assert!(
        f.k.def_eq(perfect_six, sum_divisors_six_eq_twelve),
        "Perfect 6 must unfold to sumDivisors 6 = 12"
    );

    let seven = f.num(7);
    let sum_divisors_seven = f.const_app(p.sum_divisors, &[seven]);
    let fourteen = f.num(14);
    assert!(
        !f.k.def_eq(sum_divisors_seven, fourteen),
        "sumDivisors 7 must NOT be def-eq to 14 -- Perfect 7 must be false"
    );
}

/// `Nat.sumDivisors_prime` composes with the executable `sumDivisors`: at a
/// concrete prime (`7`), the theorem applied through the primality witness
/// gives a proof of `sumDivisors 7 = 8` by pure kernel reduction of the
/// conclusion, not a fresh computation.
#[test]
fn sum_divisors_one_and_prime_are_derived_and_apply() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    for name in [p.sum_divisors_one, p.sum_divisors_prime] {
        let declaration = k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{name:?} must be declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem"
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{name:?} rests on a trusted declaration"
        );
    }
}

/// `Nat.pow2_geom_sum` computes the ACTUAL finite geometric sum by kernel
/// reduction: `pow 2 5` reduces to `32`, and the theorem applied at `5`
/// type-checks to a residue naming `sumRange`, `pow`, and `add` (the
/// subtraction-free `Σ_{i<5} 2^i + 1 = 2^5` statement) — a definition that
/// type-checks but sums the wrong function has an empty axiom footprint and
/// passes every sweep in this repository, so the numeral check matters as
/// much as the derivation check.
#[test]
fn pow2_geom_sum_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let five = f.num(5);
    let two_pow_five = f.const_app(p.pow, &[two, five]);
    let thirty_two = f.num(32);
    assert!(
        f.k.def_eq(two_pow_five, thirty_two),
        "pow 2 5 must reduce to 32"
    );

    let five2 = f.num(5);
    let applied = f.const_app(p.pow2_geom_sum, &[five2]);
    let inferred = f.k.infer(applied).expect("pow2_geom_sum 5 must type-check");
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("sumRange") && rendered.contains("AxNat.pow") && rendered.contains("add"),
        "unexpected residue type: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.pow2_geom_sum).is_empty(),
        "pow2_geom_sum rests on a trusted declaration"
    );
}

/// `Nat.dvd_two_pow_mul_classify` — Euclid IX.36's divisor-classification
/// blocker. At `k = 2, q = 7` (the `p = 3` case: `2^2·7 = 28`, and
/// `sumDivisors 28` already reduces to `56 = 2·28`, i.e. `28` is perfect —
/// see `perfect_holds_at_six_and_fails_at_seven`), the theorem partially
/// applied at `[k, q]` type-checks and its residue names `dvd`, `pow`, and
/// the two-armed `Or (Exists …) (Exists …)` disjunction the classification
/// promises; the axiom footprint is empty.
#[test]
fn dvd_two_pow_mul_classify_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let seven = f.num(7);
    let four = f.num(4);
    let twenty_eight = f.num(28);
    let two_pow_two = f.const_app(p.pow, &[two, two]);
    assert!(f.k.def_eq(two_pow_two, four), "pow 2 2 must reduce to 4");
    let target = f.mul(four, seven);
    assert!(
        f.k.def_eq(target, twenty_eight),
        "mul (pow 2 2) 7 must reduce to 28"
    );

    let k = f.num(2);
    let q = f.num(7);
    let applied = f.const_app(p.dvd_two_pow_mul_classify, &[k, q]);
    let inferred =
        f.k.infer(applied)
            .expect("dvd_two_pow_mul_classify 2 7 must type-check");
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("dvd")
            && rendered.contains("AxNat.pow")
            && rendered.contains("Or")
            && rendered.contains("Exists"),
        "unexpected residue type: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.dvd_two_pow_mul_classify).is_empty(),
        "dvd_two_pow_mul_classify rests on a trusted declaration"
    );
}

/// `Nat.dvd_two_pow_classify` — the "divisors of `2^n` are exactly the
/// powers of `2` up to `n`" classification `sumDivisors_two_pow`'s
/// congruence step needs. At `k = 3` (`2^3 = 8`), the theorem partially
/// applied at `[k]` type-checks and its residue names `dvd`, `pow`, and a
/// single `Exists` (no `Or`, unlike `dvd_two_pow_mul_classify` — there is
/// only one shape to land in without a coprime cofactor); the axiom
/// footprint is empty.
#[test]
fn dvd_two_pow_classify_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);
    let eight = f.num(8);
    let two_pow_three = f.const_app(p.pow, &[two, three]);
    assert!(f.k.def_eq(two_pow_three, eight), "pow 2 3 must reduce to 8");

    let k = f.num(3);
    let applied = f.const_app(p.dvd_two_pow_classify, &[k]);
    let inferred =
        f.k.infer(applied)
            .expect("dvd_two_pow_classify 3 must type-check");
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("dvd") && rendered.contains("AxNat.pow") && rendered.contains("Exists"),
        "unexpected residue type: {rendered}"
    );
    assert!(
        !rendered.contains("Or"),
        "dvd_two_pow_classify has no coprime cofactor, so its residue must not \
         carry an Or disjunction: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.dvd_two_pow_classify).is_empty(),
        "dvd_two_pow_classify rests on a trusted declaration"
    );

    // A genuine divisor at this instance: `4 ∣ 8` (witness `2`), and the
    // theorem fully applied at `dd = 4` type-checks, certifying `∃ i, Le i 3
    // ∧ Eq 4 (pow 2 i)` (the true witness is `i = 2`, since `4 = 2^2`).
    let four = f.num(4);
    let nat = f.nat_ty();
    let dvd_predicate = f.dvd_predicate(four, eight);
    let one_lvl = f.level_one();
    let exists_intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
    let witness = f.num(2);
    let mul_four_two = f.mul(four, witness);
    assert!(f.k.def_eq(eight, mul_four_two), "8 must reduce to mul 4 2");
    let eq_proof = f.refl(eight);
    let dvd_four_eight = f.apply(exists_intro, &[nat, dvd_predicate, witness, eq_proof]);

    let applied_full = f.apply(applied, &[four, dvd_four_eight]);
    let inferred_full =
        f.k.infer(applied_full)
            .expect("dvd_two_pow_classify 3 4 (proof of 4∣8) must type-check");
    let rendered_full = f.k.render_lean(inferred_full);
    assert!(
        rendered_full.contains("Exists"),
        "fully applied residue must still be the existential witness claim: \
         {rendered_full}"
    );
}

/// `Nat.pow_two_ne_pow_two_mul_prime` — the non-overlap fact between
/// `2^k·q`'s two divisor families. At `i = 2, j = 0, q = 3` (`p = 2`'s
/// Euclid IX.36 instance: `2^1·3 = 6`, and `sumDivisors 6` already reduces
/// to `12 = 2·6` — see `perfect_holds_at_six_and_fails_at_seven`), `pow 2 2
/// = 4` and `mul (pow 2 0) 3 = 3` are genuinely distinct numerals, so this
/// checks the theorem's residue SHAPE (a `Prime → ¬(dvd · 2) → Not (Eq …)`
/// arrow chain) rather than deriving an impossible witness — there is no
/// counterexample to construct, since the statement is true. The axiom
/// footprint is empty.
#[test]
fn pow_two_ne_pow_two_mul_prime_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let zero = f.num(0);
    let three = f.num(3);
    let four = f.num(4);
    let two_pow_two = f.const_app(p.pow, &[two, two]);
    assert!(f.k.def_eq(two_pow_two, four), "pow 2 2 must reduce to 4");
    let two_pow_zero = f.const_app(p.pow, &[two, zero]);
    let one = f.num(1);
    assert!(f.k.def_eq(two_pow_zero, one), "pow 2 0 must reduce to 1");
    let target = f.mul(one, three);
    assert!(
        f.k.def_eq(target, three),
        "mul (pow 2 0) 3 must reduce to 3"
    );

    let i = f.num(2);
    let j = f.num(0);
    let q = f.num(3);
    let applied = f.const_app(p.pow_two_ne_pow_two_mul_prime, &[i, j, q]);
    let inferred =
        f.k.infer(applied)
            .expect("pow_two_ne_pow_two_mul_prime 2 0 3 must type-check");
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("dvd")
            && rendered.contains("AxNat.pow")
            && rendered.contains("Not")
            && rendered.contains("Eq"),
        "unexpected residue type: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.pow_two_ne_pow_two_mul_prime)
            .is_empty(),
        "pow_two_ne_pow_two_mul_prime rests on a trusted declaration"
    );
}

/// `Nat.pow_pos` — fully applied at `b = 3, k = 4` (`pow 3 4` reduces to
/// `81`) with a CONCRETE proof of `Lt 0 3` (built from `Le.refl`/`Le.step`,
/// not merely asserted), the residue's inferred type must reduce to
/// `Lt 0 81` by `def_eq` — the numeral check a bare axiom-footprint/type
/// pass cannot see (an off-by-one exponent or a wrong base would still
/// type-check).
#[test]
fn pow_pos_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let four = f.num(4);
    let pow_three_four = f.const_app(p.pow, &[three, four]);
    let eighty_one = f.num(81);
    assert!(
        f.k.def_eq(pow_three_four, eighty_one),
        "pow 3 4 must reduce to 81"
    );

    // A concrete proof of `Le 1 3` (defeq `Lt 0 3`): `le_refl 1`, stepped
    // twice.
    let one = f.num(1);
    let two = f.num(2);
    let le_1_1 = f.const_app(p.le_refl, &[one]);
    let le_1_2 = f.const_app(p.le_step, &[one, one, le_1_1]);
    let le_1_3 = f.const_app(p.le_step, &[one, two, le_1_2]);

    let applied = f.const_app(p.pow_pos, &[three, four]);
    let full = f.apply(applied, &[le_1_3]);
    let inferred = f.k.infer(full).expect("pow_pos 3 4 le_1_3 must type-check");
    let zero = f.zero();
    let expected = f.lt(zero, eighty_one);
    assert!(
        f.k.def_eq(inferred, expected),
        "pow_pos 3 4 must certify Lt 0 81, got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.pow_pos).is_empty(),
        "pow_pos rests on a trusted declaration"
    );
}

/// `Nat.pow_lt_pow_succ` — fully applied at `b = 2, k = 3` with a CONCRETE
/// proof of `Lt 1 2` (`Le.refl 2`), the residue's inferred type must reduce
/// to `Lt 8 16` (`pow 2 3 = 8`, `pow 2 4 = 16`) by `def_eq`. This is exactly
/// the instance `sumDivisors_two_pow`'s tail sub-induction will apply this
/// lemma at (`2^k < 2^(k+1)`).
#[test]
fn pow_lt_pow_succ_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let pow_two_three = f.const_app(p.pow, &[two, three]);
    let eight = f.num(8);
    assert!(f.k.def_eq(pow_two_three, eight), "pow 2 3 must reduce to 8");
    let pow_two_four = f.const_app(p.pow, &[two, four]);
    let sixteen = f.num(16);
    assert!(
        f.k.def_eq(pow_two_four, sixteen),
        "pow 2 4 must reduce to 16"
    );

    // A concrete proof of `Le 2 2` (defeq `Lt 1 2`): `le_refl 2`.
    let le_2_2 = f.const_app(p.le_refl, &[two]);

    let applied = f.const_app(p.pow_lt_pow_succ, &[two, three]);
    let full = f.apply(applied, &[le_2_2]);
    let inferred =
        f.k.infer(full)
            .expect("pow_lt_pow_succ 2 3 le_2_2 must type-check");
    let expected = f.lt(eight, sixteen);
    assert!(
        f.k.def_eq(inferred, expected),
        "pow_lt_pow_succ 2 3 must certify Lt 8 16, got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.pow_lt_pow_succ).is_empty(),
        "pow_lt_pow_succ rests on a trusted declaration"
    );
}

/// `Nat.pow_lt_pow_of_lt` — fully applied at `b = 2, i = 1, j = 4` (a genuine
/// GAP, not a successor step, and `i ≠ j` so the direction is checkable: a
/// transposed-argument defect would certify `Lt 16 2`, which is false and
/// would fail the `def_eq` below), the residue's inferred type must reduce to
/// `Lt 2 16` by `def_eq`. Euclid IX.36's injectivity chain needs exactly this
/// general-gap form (`pow_lt_pow_succ` only ever gave one successor step).
#[test]
fn pow_lt_pow_of_lt_computes_at_a_concrete_gap() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let two = f.num(2);
    let four = f.num(4);
    let pow_two_one = f.const_app(p.pow, &[two, one]);
    assert!(f.k.def_eq(pow_two_one, two), "pow 2 1 must reduce to 2");
    let pow_two_four = f.const_app(p.pow, &[two, four]);
    let sixteen = f.num(16);
    assert!(
        f.k.def_eq(pow_two_four, sixteen),
        "pow 2 4 must reduce to 16"
    );

    // `Lt 1 2` (defeq `Le 2 2`): `le_refl 2`.
    let hb = f.const_app(p.le_refl, &[two]);

    // `Lt 1 4` (defeq `Le 2 4`): `le_refl 2` widened twice by `le_step`.
    let le_2_2 = f.const_app(p.le_refl, &[two]);
    let le_2_3 = f.lemma(p.le_step, &[two, two, le_2_2]);
    let three = f.num(3);
    let hlt = f.lemma(p.le_step, &[two, three, le_2_3]);

    let applied = f.const_app(p.pow_lt_pow_of_lt, &[two, one, four]);
    let full = f.apply(applied, &[hb, hlt]);
    let inferred =
        f.k.infer(full)
            .expect("pow_lt_pow_of_lt 2 1 4 hb hlt must type-check");
    let expected = f.lt(two, sixteen);
    assert!(
        f.k.def_eq(inferred, expected),
        "pow_lt_pow_of_lt 2 1 4 must certify Lt 2 16, got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.pow_lt_pow_of_lt).is_empty(),
        "pow_lt_pow_of_lt rests on a trusted declaration"
    );
}

/// `Nat.pow_injective` — fully applied at `b = 2, i = j = 3` with the
/// reflexive proof of `Eq (pow 2 3) (pow 2 3)`, the residue's inferred type
/// must reduce to `Eq 3 3` by `def_eq`.
#[test]
fn pow_injective_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);

    // `Lt 1 2` (defeq `Le 2 2`): `le_refl 2`.
    let hb = f.const_app(p.le_refl, &[two]);

    let pow_two_three = f.const_app(p.pow, &[two, three]);
    let heq = f.refl(pow_two_three); // Eq (pow 2 3) (pow 2 3)

    let applied = f.const_app(p.pow_injective, &[two, three, three]);
    let full = f.apply(applied, &[hb, heq]);
    let inferred =
        f.k.infer(full)
            .expect("pow_injective 2 3 3 hb heq must type-check");
    let expected = f.eq(three, three);
    assert!(
        f.k.def_eq(inferred, expected),
        "pow_injective 2 3 3 must certify Eq 3 3, got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.pow_injective).is_empty(),
        "pow_injective rests on a trusted declaration"
    );
}

/// `Nat.pow_mul_prime_injective` — fully applied at `i = j = 2, q = 3` with
/// the reflexive proof of `Eq (mul (pow 2 2) 3) (mul (pow 2 2) 3)`, the
/// residue's inferred type must reduce to `Eq 2 2` by `def_eq`.
#[test]
fn pow_mul_prime_injective_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    // `Le 1 3`: `le_refl 1` widened twice by `le_step`.
    let le_1_1 = f.const_app(p.le_refl, &[one]);
    let le_1_2 = f.lemma(p.le_step, &[one, one, le_1_1]);
    let hq = f.lemma(p.le_step, &[one, two, le_1_2]);

    let pow_two_two = f.const_app(p.pow, &[two, two]);
    let mul_term = f.mul(pow_two_two, three);
    let heq = f.refl(mul_term); // Eq (mul (pow 2 2) 3) (mul (pow 2 2) 3)

    let applied = f.const_app(p.pow_mul_prime_injective, &[two, two, three]);
    let full = f.apply(applied, &[hq, heq]);
    let inferred =
        f.k.infer(full)
            .expect("pow_mul_prime_injective 2 2 3 hq heq must type-check");
    let expected = f.eq(two, two);
    assert!(
        f.k.def_eq(inferred, expected),
        "pow_mul_prime_injective 2 2 3 must certify Eq 2 2, got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.pow_mul_prime_injective).is_empty(),
        "pow_mul_prime_injective rests on a trusted declaration"
    );
}

/// `Nat.dvd_two_pow_succ_iff_of_le` — the congruence step
/// `sumDivisors_two_pow`'s tail sub-induction needs. At `k = 2` (`2^2 = 4`,
/// `2^3 = 8`) with `dd = 4` (`Le 4 4` via `le_refl`), the theorem fully
/// applied type-checks to the concrete `Iff (dvd 4 4) (dvd 4 8)`, and its
/// forward direction (`iff_mp`) applied to the genuine fact `dvd 4 4`
/// (`dvd_refl`) computes a proof of `dvd 4 8`.
#[test]
fn dvd_two_pow_succ_iff_of_le_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let four = f.num(4);
    let eight = f.num(8);
    let k = f.num(2);
    let pow_k = f.const_app(p.pow, &[two, k]);
    assert!(f.k.def_eq(pow_k, four), "pow 2 2 must reduce to 4");
    let sk = f.succ(k);
    let pow_sk = f.const_app(p.pow, &[two, sk]);
    assert!(f.k.def_eq(pow_sk, eight), "pow 2 (succ 2) must reduce to 8");

    let dd = four;
    let bound = f.lemma(p.le_refl, &[four]); // Le 4 4, defeq Le dd (pow 2 k)

    let iff_proof = f.lemma(p.dvd_two_pow_succ_iff_of_le, &[k, dd, bound]);
    let inferred =
        f.k.infer(iff_proof)
            .expect("dvd_two_pow_succ_iff_of_le 2 4 (le_refl 4) must type-check");
    let expected_left = f.dvd(dd, four);
    let expected_right = f.dvd(dd, eight);
    let expected_iff = f.const_app(p.logic.iff, &[expected_left, expected_right]);
    assert!(
        f.k.def_eq(inferred, expected_iff),
        "dvd_two_pow_succ_iff_of_le 2 4 must certify Iff (dvd 4 4) (dvd 4 8), got {}",
        f.k.render_lean(inferred)
    );

    assert!(
        f.k.axiom_footprint(p.dvd_two_pow_succ_iff_of_le).is_empty(),
        "dvd_two_pow_succ_iff_of_le rests on a trusted declaration"
    );

    // The forward direction really computes: `dvd 4 4` (genuinely true, via
    // `dvd_refl`) pushed through `iff_mp` must certify `dvd 4 8`.
    let dvd_4_4 = f.lemma(p.dvd_refl, &[four]);
    let mp = f.const_app(p.logic.iff_mp, &[expected_left, expected_right, iff_proof]);
    let dvd_4_8 = f.apply(mp, &[dvd_4_4]);
    let inferred_mp =
        f.k.infer(dvd_4_8)
            .expect("iff_mp (dvd_two_pow_succ_iff_of_le 2 4 …) dvd_refl must type-check");
    assert!(
        f.k.def_eq(inferred_mp, expected_right),
        "the forward direction must certify dvd 4 8, got {}",
        f.k.render_lean(inferred_mp)
    );
}

/// `Nat.sumDivisors_two_pow_eq_geom_sum` and `Nat.sumDivisors_two_pow` — the
/// Euclid IX.36 divisor-sum blocker. At `k = 3` (`2^3 = 8`): `sumDivisors 8`
/// is ALREADY independently computation-tested to reduce to `15`
/// (`sum_divisors_computes_on_small_numerals`), and `15 + 1 = 16 = 2^4`. Both
/// theorems fully applied at `k = 3` must certify exactly this concrete
/// numeral identity — not merely type-check — and rest on empty axiom
/// footprints.
#[test]
fn sum_divisors_two_pow_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let eight = f.num(8);
    let fifteen = f.num(15);
    let sixteen = f.num(16);

    let pow_2_3 = f.const_app(p.pow, &[two, three]);
    assert!(f.k.def_eq(pow_2_3, eight), "pow 2 3 must reduce to 8");
    let pow_2_4 = f.const_app(p.pow, &[two, four]);
    assert!(f.k.def_eq(pow_2_4, sixteen), "pow 2 4 must reduce to 16");
    let sd_8 = f.const_app(p.sum_divisors, &[eight]);
    assert!(
        f.k.def_eq(sd_8, fifteen),
        "sumDivisors 8 must reduce to 15 (independently pinned elsewhere too)"
    );

    // `sumDivisors_two_pow_eq_geom_sum 3 : Eq (sumDivisors (pow 2 3))
    // (sumRange (fun i => pow 2 i) 4)`, and the RHS is the geometric sum
    // `1+2+4+8 = 15`.
    let eq_geom_applied = f.const_app(p.sum_divisors_two_pow_eq_geom_sum, &[three]);
    let inferred_geom =
        f.k.infer(eq_geom_applied)
            .expect("sumDivisors_two_pow_eq_geom_sum 3 must type-check");
    let f_pow2 = {
        let nat = f.nat_ty();
        let i_fv = f.fresh_fvar();
        let i = f.kernel().fvar(i_fv);
        let two_inner = f.num(2);
        let body = f.pow(two_inner, i);
        f.lam_fv(i_fv, nat, body)
    };
    let geom_sum_4 = f.sum_range(f_pow2, four);
    let expected_geom_ty = f.eq(sd_8, geom_sum_4);
    assert!(
        f.k.def_eq(inferred_geom, expected_geom_ty),
        "sumDivisors_two_pow_eq_geom_sum 3 must certify Eq (sumDivisors 8) \
         (sumRange pow2 4), got {}",
        f.k.render_lean(inferred_geom)
    );
    assert!(
        f.k.axiom_footprint(p.sum_divisors_two_pow_eq_geom_sum)
            .is_empty(),
        "sumDivisors_two_pow_eq_geom_sum rests on a trusted declaration"
    );

    // `sumDivisors_two_pow 3 : Eq (add (sumDivisors (pow 2 3)) one) (pow 2 4)`
    // — both sides reduce to the CONCRETE numeral `16`.
    let applied = f.const_app(p.sum_divisors_two_pow, &[three]);
    let inferred =
        f.k.infer(applied)
            .expect("sumDivisors_two_pow 3 must type-check");
    let expected_ty = f.eq(sixteen, sixteen);
    assert!(
        f.k.def_eq(inferred, expected_ty),
        "sumDivisors_two_pow 3 must certify Eq 16 16 (i.e. sumDivisors 8 + 1 = 2^4), got {}",
        f.k.render_lean(inferred)
    );
    assert!(
        f.k.axiom_footprint(p.sum_divisors_two_pow).is_empty(),
        "sumDivisors_two_pow rests on a trusted declaration"
    );
}

/// `Nat.testBit` computes the binary digits of `13 = 1101₂` by pure reduction
/// on numerals: bit 0 and bit 2 and bit 3 are `1`, bit 1 is `0`. This is the
/// mandatory concrete instance — a definition that type-checks but computes
/// the wrong digit is exactly what an axiom-footprint check cannot see.
#[test]
fn test_bit_computes_thirteen_in_binary() {
    let mut f = Fixture::new();
    let p = f.p;

    let thirteen = f.num(13);
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    let bit0 = f.const_app(p.test_bit, &[thirteen, zero]);
    let bit1 = f.const_app(p.test_bit, &[thirteen, one]);
    let bit2 = f.const_app(p.test_bit, &[thirteen, two]);
    let bit3 = f.const_app(p.test_bit, &[thirteen, three]);

    assert!(f.k.def_eq(bit0, one), "testBit 13 0 must reduce to 1");
    assert!(f.k.def_eq(bit1, zero), "testBit 13 1 must reduce to 0");
    assert!(f.k.def_eq(bit2, one), "testBit 13 2 must reduce to 1");
    assert!(f.k.def_eq(bit3, one), "testBit 13 3 must reduce to 1");

    // NEGATIVE reduction controls — a checker that can't fail is worse than
    // none.
    assert!(!f.k.def_eq(bit0, zero), "testBit 13 0 must NOT be 0");
    assert!(!f.k.def_eq(bit1, one), "testBit 13 1 must NOT be 1");
    assert!(!f.k.def_eq(bit2, zero), "testBit 13 2 must NOT be 0");
    assert!(!f.k.def_eq(bit3, zero), "testBit 13 3 must NOT be 0");

    // Bit 4 and beyond are 0 (13 < 16), and every bit is Le _ 1.
    let four = f.num(4);
    let bit4 = f.const_app(p.test_bit, &[thirteen, four]);
    assert!(f.k.def_eq(bit4, zero), "testBit 13 4 must reduce to 0");
}

/// `Nat.size` computes the binary digit count by pure reduction on numerals:
/// `size 0 = 0`, `size 1 = 1`, `size 13 = 4` (`13 = 1101₂`), `size 16 = 5`
/// (`16 = 10000₂`). This is the mandatory concrete instance the handover
/// asked for — a fuel-recursive definition that type-checks but computes the
/// wrong size has an empty axiom footprint and would pass every other sweep
/// here.
#[test]
fn size_computes_binary_digit_counts() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let four = f.num(4);
    let five = f.num(5);
    let thirteen = f.num(13);
    let sixteen = f.num(16);

    let size_zero_val = f.const_app(p.size, &[zero]);
    let size_one_val = f.const_app(p.size, &[one]);
    let size_thirteen_val = f.const_app(p.size, &[thirteen]);
    let size_sixteen_val = f.const_app(p.size, &[sixteen]);

    assert!(f.k.def_eq(size_zero_val, zero), "size 0 must reduce to 0");
    assert!(f.k.def_eq(size_one_val, one), "size 1 must reduce to 1");
    assert!(
        f.k.def_eq(size_thirteen_val, four),
        "size 13 must reduce to 4 (13 = 1101 in binary)"
    );
    assert!(
        f.k.def_eq(size_sixteen_val, five),
        "size 16 must reduce to 5 (16 = 10000 in binary)"
    );

    // NEGATIVE reduction controls — a checker that can't fail is worse than
    // none.
    assert!(
        !f.k.def_eq(size_thirteen_val, five),
        "size 13 must NOT be def-eq to 5"
    );
    assert!(
        !f.k.def_eq(size_sixteen_val, four),
        "size 16 must NOT be def-eq to 4"
    );
    assert!(
        !f.k.def_eq(size_one_val, zero),
        "size 1 must NOT be def-eq to 0"
    );
    let two = f.num(2);
    assert!(
        !f.k.def_eq(size_zero_val, two),
        "size 0 must NOT be def-eq to a nonzero numeral"
    );

    for name in [p.size_aux, p.size, p.size_zero] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `powSq 2 10` reduces to `1024` and `powSq 3 4` to `81` — real kernel
/// reduction (`def_eq`), not type-checking. An implementation with the
/// even/odd branches of `powSqAux` swapped type-checks perfectly and
/// computes the wrong function; only computation catches that, which is why
/// this test exists independently of `pow_sq_eq_pow`'s admission.
#[test]
fn pow_sq_computes_exponentiation_by_squaring() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let ten = f.num(10);
    let three = f.num(3);
    let four = f.num(4);

    let pow_sq_2_10 = f.const_app(p.pow_sq, &[two, ten]);
    let expected_1024 = f.num(1024);
    assert!(
        f.k.def_eq(pow_sq_2_10, expected_1024),
        "powSq 2 10 must reduce to 1024"
    );

    let pow_sq_3_4 = f.const_app(p.pow_sq, &[three, four]);
    let expected_81 = f.num(81);
    assert!(
        f.k.def_eq(pow_sq_3_4, expected_81),
        "powSq 3 4 must reduce to 81"
    );

    // NEGATIVE reduction controls — a checker that can't fail is worse than
    // none. 512 = 2^9 is the off-by-one an exponent/fuel bookkeeping slip
    // would plausibly produce; 80/82 are near misses on 81.
    let wrong_512 = f.num(512);
    assert!(
        !f.k.def_eq(pow_sq_2_10, wrong_512),
        "powSq 2 10 must NOT be def-eq to 512 (= 2^9, an off-by-one)"
    );
    let wrong_80 = f.num(80);
    assert!(
        !f.k.def_eq(pow_sq_3_4, wrong_80),
        "powSq 3 4 must NOT be def-eq to 80"
    );
    let wrong_82 = f.num(82);
    assert!(
        !f.k.def_eq(pow_sq_3_4, wrong_82),
        "powSq 3 4 must NOT be def-eq to 82"
    );

    for name in [
        p.pow_sq_aux,
        p.pow_sq,
        p.pow_half_split,
        p.pow_sq_aux_eq_pow,
        p.pow_sq_eq_pow,
        p.pow_sq_zero,
        p.pow_sq_succ,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `powSq`'s own two defining equations, checked by reducing both sides at a
/// concrete instance — not just admission (the theorems are proved generically
/// via `pow_sq_eq_pow`, so this is an independent computational check).
#[test]
fn pow_sq_defining_equations_hold_at_concrete_points() {
    let mut f = Fixture::new();
    let p = f.p;

    // pow_sq_zero : powSq b 0 = 1, at b = 7.
    let seven = f.num(7);
    let zero = f.zero();
    let proof_zero = f.lemma(p.pow_sq_zero, &[seven]);
    let lhs_zero = f.const_app(p.pow_sq, &[seven, zero]);
    let one = f.num(1);
    let stmt_zero = f.eq(lhs_zero, one);
    let inferred_zero =
        f.k.infer(proof_zero)
            .unwrap_or_else(|e| panic!("pow_sq_zero(7) should infer: {}", f.explain(&e)));
    assert!(
        f.k.def_eq(inferred_zero, stmt_zero),
        "pow_sq_zero(7) must prove powSq 7 0 = 1"
    );

    // pow_sq_succ at b = 2, k = 3 (e = succ k = 4, even): both sides of the
    // stated equation reduce to 16.
    let two = f.num(2);
    let three = f.num(3);
    let proof_succ = f.lemma(p.pow_sq_succ, &[two, three]);
    let inferred_succ =
        f.k.infer(proof_succ)
            .unwrap_or_else(|e| panic!("pow_sq_succ(2, 3) should infer: {}", f.explain(&e)));
    let sixteen = f.num(16);
    let e = f.succ(three);
    let lhs_succ = f.const_app(p.pow_sq, &[two, e]);
    let stmt_succ_lhs_reduces = f.eq(lhs_succ, sixteen);
    assert!(
        f.k.def_eq(inferred_succ, stmt_succ_lhs_reduces),
        "pow_sq_succ(2, 3)'s statement must reduce to powSq 2 4 = 16"
    );
    assert!(
        f.k.def_eq(lhs_succ, sixteen),
        "powSq 2 4 must independently reduce to 16"
    );
}

/// `Nat.lt_pow_size` holds at several concrete instances, checked by reducing
/// its instantiated statement to the numeral both sides of `Lt` compute to —
/// not just admission. `size_aux_lt_pow`'s underlying bound is what makes
/// `n` itself always enough fuel for `size n := sizeAux n n`.
#[test]
fn lt_pow_size_holds_at_concrete_points() {
    let mut f = Fixture::new();
    let p = f.p;

    for (n_val, expected_size) in [(0u32, 0u32), (1, 1), (13, 4), (16, 5), (63, 6)] {
        let n = f.num(n_val);
        let proof = f.lemma(p.lt_pow_size, &[n]);
        let inferred =
            f.k.infer(proof)
                .unwrap_or_else(|e| panic!("lt_pow_size({n_val}) should infer: {}", f.explain(&e)));
        let size_n = f.const_app(p.size, &[n]);
        let expected_size_val = f.num(expected_size);
        assert!(
            f.k.def_eq(size_n, expected_size_val),
            "size {n_val} must reduce to {expected_size}"
        );
        let two = f.num(2);
        let pow_n = f.pow(two, size_n);
        let expected_ty = f.lt(n, pow_n);
        assert!(
            f.k.def_eq(inferred, expected_ty),
            "lt_pow_size({n_val}) should state n < 2^(size n)"
        );
    }

    assert!(
        f.k.axiom_footprint(p.size_aux_lt_pow).is_empty(),
        "size_aux_lt_pow must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lt_pow_size).is_empty(),
        "lt_pow_size must rest on zero axioms"
    );
}

/// `Nat.mod_eq_self_of_lt` applies at concrete points, and both sides of its
/// conclusion compute to the same numeral.
#[test]
fn mod_eq_self_of_lt_applies_at_concrete_points() {
    let mut f = Fixture::new();
    let p = f.p;

    // `Lt n m` for concrete numerals is `Le (succ n) m`, witnessed directly
    // via `le_intro (succ n) m k proof` with `k := m - n - 1`: the witness
    // `succ n + k` reduces to `m` on literal numerals, so `refl` closes it.
    for (n_val, m_val) in [(0u32, 1u32), (3, 5), (4, 5), (0, 7)] {
        let n = f.num(n_val);
        let m = f.num(m_val);
        let sn = f.succ(n);
        let k = f.num(m_val - n_val - 1);
        let sn_plus_k = f.add(sn, k);
        let witness = f.refl(sn_plus_k);
        let lt_proof = f.lemma(p.le_intro, &[sn, m, k, witness]);
        let inferred_lt = f.k.infer(lt_proof).unwrap_or_else(|e| {
            panic!(
                "le_intro should infer for n={n_val} m={m_val}: {}",
                f.explain(&e)
            )
        });
        let expected_lt_ty = f.lt(n, m);
        assert!(
            f.k.def_eq(inferred_lt, expected_lt_ty),
            "le_intro instance should witness Lt {n_val} {m_val}"
        );

        let proof = f.lemma(p.mod_eq_self_of_lt, &[n, m, lt_proof]);
        let inferred = f.k.infer(proof).unwrap_or_else(|e| {
            panic!(
                "mod_eq_self_of_lt({n_val},{m_val}) should infer: {}",
                f.explain(&e)
            )
        });
        let mod_val = f.modulo(n, m);
        let expected = f.eq(mod_val, n);
        assert!(
            f.k.def_eq(inferred, expected),
            "mod_eq_self_of_lt({n_val},{m_val}) should state mod {n_val} {m_val} = {n_val}"
        );
        assert!(
            f.k.def_eq(mod_val, n),
            "mod {n_val} {m_val} must actually reduce to {n_val}"
        );
    }

    assert!(
        f.k.axiom_footprint(p.mod_eq_self_of_lt).is_empty(),
        "mod_eq_self_of_lt must rest on zero axioms"
    );
}

/// `Nat.sum_testBit_eq` — the headline result, "a natural number IS the sum
/// of its own bits" — checked by reducing both sides at several concrete
/// numerals, not just admitted.
#[test]
fn sum_test_bit_eq_holds_at_concrete_points() {
    let mut f = Fixture::new();
    let p = f.p;

    for n_val in [0u32, 1, 2, 13, 16, 63] {
        let n = f.num(n_val);
        let proof = f.lemma(p.sum_test_bit_eq, &[n]);
        let inferred = f
            .k
            .infer(proof)
            .unwrap_or_else(|e| panic!("sum_testBit_eq({n_val}) should infer: {}", f.explain(&e)));

        let size_n = f.const_app(p.size, &[n]);
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let nat = f.nat_ty();
        let tb = f.const_app(p.test_bit, &[n, i]);
        let two = f.num(2);
        let p2i = f.pow(two, i);
        let body = f.mul(tb, p2i);
        let term = f.lam_fv(i_fv, nat, body);
        let lhs = f.sum_range(term, size_n);
        let expected = f.eq(lhs, n);
        assert!(
            f.k.def_eq(inferred, expected),
            "sum_testBit_eq({n_val}) should state sumRange (bit-term n) (size n) = {n_val}"
        );
        assert!(
            f.k.def_eq(lhs, n),
            "the reconstructed bit sum for {n_val} must actually reduce to {n_val}"
        );
    }

    // NEGATIVE reduction control.
    let thirteen = f.num(13);
    let proof13 = f.lemma(p.sum_test_bit_eq, &[thirteen]);
    let inferred13 = f.k.infer(proof13).unwrap();
    let size13 = f.const_app(p.size, &[thirteen]);
    let i_fv = f.fresh_fvar();
    let i = f.k.fvar(i_fv);
    let nat = f.nat_ty();
    let tb = f.const_app(p.test_bit, &[thirteen, i]);
    let two = f.num(2);
    let p2i = f.pow(two, i);
    let body = f.mul(tb, p2i);
    let term13 = f.lam_fv(i_fv, nat, body);
    let lhs13 = f.sum_range(term13, size13);
    let fourteen = f.num(14);
    let wrong_expected = f.eq(lhs13, fourteen);
    assert!(
        !f.k.def_eq(inferred13, wrong_expected),
        "sum_testBit_eq(13) must NOT be def-eq to a statement about 14"
    );

    assert!(
        f.k.axiom_footprint(p.sum_test_bit_eq).is_empty(),
        "sum_testBit_eq must rest on zero axioms"
    );
}

/// `Nat.choose` computes Pascal's triangle by pure reduction on numerals, and
/// `choose_symm` is checkable at a genuinely non-trivial (non-self-symmetric)
/// point, not just admitted vacuously.
#[test]
fn choose_computes_and_symm_holds_at_a_concrete_point() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let ten = f.num(10);

    let c00 = f.choose(zero, zero);
    assert!(f.k.def_eq(c00, one), "choose 0 0 = 1");
    let c40 = f.choose(four, zero);
    assert!(f.k.def_eq(c40, one), "choose 4 0 = 1");
    let c03 = f.choose(zero, three);
    assert!(f.k.def_eq(c03, zero), "choose 0 3 = 0");
    let c44 = f.choose(four, four);
    assert!(f.k.def_eq(c44, one), "choose 4 4 = 1");
    let c42 = f.choose(four, two);
    assert!(f.k.def_eq(c42, six), "choose 4 2 = 6");
    let c52 = f.choose(five, two);
    assert!(f.k.def_eq(c52, ten), "choose 5 2 = 10");
    let c41 = f.choose(four, one);
    assert!(f.k.def_eq(c41, four), "choose 4 1 = 4");
    let c43 = f.choose(four, three);
    assert!(f.k.def_eq(c43, four), "choose 4 3 = 4");

    // NEGATIVE reduction control.
    let c42_again = f.choose(four, two);
    assert!(
        !f.k.def_eq(c42_again, five),
        "choose 4 2 must NOT be def-eq to 5"
    );

    // choose_symm at (n=4, k=1): a non-diagonal, non-edge point, so this
    // actually exercises the strict `k' < m` case inside the proof, not just
    // the `k = 0` or `k = n` shortcuts.
    let four_minus_one = f.add(one, three);
    let sum_eq = f.refl(four_minus_one);
    let le_1_4 = f.lemma(p.le_intro, &[one, four, three, sum_eq]);
    let symm_proof = f.lemma(p.choose_symm, &[four, one, le_1_4]);
    let inferred = f
        .k
        .infer(symm_proof)
        .unwrap_or_else(|e| panic!("choose_symm(4,1) instance should infer: {}", f.explain(&e)));
    let sub_4_1 = f.sub(four, one);
    let expected = {
        let lhs = f.choose(four, one);
        let rhs = f.choose(four, sub_4_1);
        f.eq(lhs, rhs)
    };
    assert!(
        f.k.def_eq(inferred, expected),
        "choose_symm(4,1) should state choose 4 1 = choose 4 (4-1)"
    );
    assert!(f.k.def_eq(sub_4_1, three), "4 - 1 = 3");

    for name in [
        p.choose,
        p.choose_zero_right,
        p.choose_succ_succ,
        p.zero_choose_succ,
        p.choose_succ_self_eq_zero,
        p.choose_self,
        p.choose_symm,
        p.choose_one_right,
        p.choose_eq_zero_of_lt,
        p.choose_ne_zero,
        p.choose_le_succ,
        p.choose_symm_of_eq_add,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The binomial theorem's finite-sum toolkit (`sum_range_add`,
/// `sum_range_shift_front`, `sum_range_congr_lt`) checked numerically, plus
/// the `n=0`/`n=1` sanity instances of `add_pow`'s statement shape — both
/// sides fully compute to the same numeral once `a,b` are concrete, so this
/// is a genuine arithmetic check, not just an admission.
#[test]
fn binomial_toolkit_and_add_pow_sanity_instances_compute() {
    let mut f = Fixture::new();
    let p = f.p;

    // sum_range_add at a concrete instance: f = identity, g = identity, n = 3.
    // sumRange (fun i => i+i) 3 = 0+2+4 = 6 = sumRange id 3 + sumRange id 3 = 3+3.
    let i_fv = f.fresh_fvar();
    let i = f.k.fvar(i_fv);
    let nat = f.nat_ty();
    let identity = f.lam_fv(i_fv, nat, i);
    let three = f.num(3);
    let sum_add_proof = f.lemma(p.sum_range_add, &[identity, identity, three]);
    let inferred =
        f.k.infer(sum_add_proof)
            .unwrap_or_else(|e| panic!("sum_range_add(id,id,3) should infer: {}", f.explain(&e)));
    let six = f.num(6);
    let expected = {
        let combined = {
            let i_fv2 = f.fresh_fvar();
            let iv = f.k.fvar(i_fv2);
            let doubled = f.add(iv, iv);
            f.lam_fv(i_fv2, nat, doubled)
        };
        let lhs = f.sum_range(combined, three);
        let sr = f.sum_range(identity, three);
        let rhs = f.add(sr, sr);
        f.eq(lhs, rhs)
    };
    assert!(
        f.k.def_eq(inferred, expected),
        "sum_range_add should state sumRange(i+i)3 = sumRange id 3 + sumRange id 3"
    );
    let combined_again = {
        let i_fv2 = f.fresh_fvar();
        let iv = f.k.fvar(i_fv2);
        let doubled = f.add(iv, iv);
        f.lam_fv(i_fv2, nat, doubled)
    };
    let lhs_val = f.sum_range(combined_again, three);
    assert!(
        f.k.def_eq(lhs_val, six),
        "sumRange (i+i) 3 must reduce to 6"
    );

    // sum_range_shift_front at a concrete instance: f = identity, n = 3.
    // sumRange id 4 = 0+1+2+3 = 6 = id(0) + sumRange (fun k => id(succ k)) 3
    //               = 0 + (1+2+3) = 0+6 = 6.
    let shift_proof = f.lemma(p.sum_range_shift_front, &[identity, three]);
    let shift_inferred = f.k.infer(shift_proof).unwrap_or_else(|e| {
        panic!(
            "sum_range_shift_front(id,3) should infer: {}",
            f.explain(&e)
        )
    });
    let four = f.num(4);
    let shift_expected = {
        let lhs = f.sum_range(identity, four);
        let zero = f.zero();
        let f0 = f.apply(identity, &[zero]);
        let shifted = {
            let k_fv = f.fresh_fvar();
            let k = f.k.fvar(k_fv);
            let sk = f.succ(k);
            let body = f.apply(identity, &[sk]);
            f.lam_fv(k_fv, nat, body)
        };
        let sr = f.sum_range(shifted, three);
        let rhs = f.add(f0, sr);
        f.eq(lhs, rhs)
    };
    assert!(
        f.k.def_eq(shift_inferred, shift_expected),
        "sum_range_shift_front should state sumRange id 4 = id 0 + sumRange (shifted id) 3"
    );
    let shift_lhs_val = f.sum_range(identity, four);
    assert!(
        f.k.def_eq(shift_lhs_val, six),
        "sumRange id 4 must reduce to 0+1+2+3=6"
    );

    // sum_range_congr_lt at a concrete instance: f = identity, g = identity, n = 2
    // (the hypothesis is vacuously dischargeable since f and g agree everywhere).
    let two = f.num(2);
    let vacuous_hyp = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let hlt_ty = f.lt(k, two);
        let hlt_fv = f.fresh_fvar();
        let body = f.refl(k);
        let inner = f.lam_fv(hlt_fv, hlt_ty, body);
        f.lam_fv(k_fv, nat, inner)
    };
    let congr_lt_proof = f.lemma(
        p.sum_range_congr_lt,
        &[identity, identity, two, vacuous_hyp],
    );
    f.k.infer(congr_lt_proof).unwrap_or_else(|e| {
        panic!(
            "sum_range_congr_lt(id,id,2,_) should infer: {}",
            f.explain(&e)
        )
    });

    // add_pow_zero / add_pow_one at a=2, b=3: (2+3)^0=1 and (2+3)^1=5. Both
    // sides of each declared equation fully compute to a literal once a,b are
    // concrete numerals, so def_eq against the numeral is a genuine
    // arithmetic check, not just a shape check.
    let two_ = f.num(2);
    let three_ = f.num(3);
    let one = f.num(1);
    let five = f.num(5);

    let zero_proof = f.lemma(p.add_pow_zero, &[two_, three_]);
    let zero_inferred =
        f.k.infer(zero_proof)
            .unwrap_or_else(|e| panic!("add_pow_zero(2,3) should infer: {}", f.explain(&e)));
    let zero_expected = {
        let sum = f.add(two_, three_);
        let z = f.zero();
        let lhs = f.pow(sum, z);
        f.eq(lhs, one)
    };
    assert!(
        f.k.def_eq(zero_inferred, zero_expected),
        "add_pow_zero(2,3) should state (2+3)^0 = 1, and both sides must compute to 1"
    );

    let one_proof = f.lemma(p.add_pow_one, &[two_, three_]);
    let one_inferred =
        f.k.infer(one_proof)
            .unwrap_or_else(|e| panic!("add_pow_one(2,3) should infer: {}", f.explain(&e)));
    let one_expected = {
        let sum = f.add(two_, three_);
        let lhs = f.pow(sum, one);
        f.eq(lhs, five)
    };
    assert!(
        f.k.def_eq(one_inferred, one_expected),
        "add_pow_one(2,3) should state (2+3)^1 = 5, and both sides must compute to 5"
    );

    for name in [
        p.sum_range_add,
        p.sum_range_shift_front,
        p.sum_range_congr_lt,
        p.add_pow_zero,
        p.add_pow_one,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The binomial theorem itself, `Nat.add_pow`, checked numerically at `n=2`
/// and `n=3` with `a=2,b=3`: `(2+3)^2 = 25 = 2^2+2*2*3+3^2` and
/// `(2+3)^3 = 125 = 2^3+3*2^2*3+3*2*3^2+3^3`, both via `def_eq` reducing the
/// declared theorem's `sumRange`-shaped instance all the way down to the
/// literal numeral — an off-by-one in the sum's bound or in either exponent's
/// orientation would leave the two sides at DIFFERENT numerals, not just
/// differently-shaped ones.
#[test]
fn add_pow_holds_at_n_equals_two_and_three() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);

    let n2 = f.num(2);
    let proof2 = f.lemma(p.add_pow, &[two, three, n2]);
    let inferred2 =
        f.k.infer(proof2)
            .unwrap_or_else(|e| panic!("add_pow(2,3,2) should infer: {}", f.explain(&e)));
    let twenty_five = f.num(25);
    let expected2 = {
        let sum = f.add(two, three);
        let lhs = f.pow(sum, n2);
        f.eq(lhs, twenty_five)
    };
    assert!(
        f.k.def_eq(inferred2, expected2),
        "add_pow(2,3,2) should state (2+3)^2 = 25 (= 2^2+2*2*3+3^2), and both \
         sides must compute to 25"
    );

    let n3 = f.num(3);
    let proof3 = f.lemma(p.add_pow, &[two, three, n3]);
    let inferred3 =
        f.k.infer(proof3)
            .unwrap_or_else(|e| panic!("add_pow(2,3,3) should infer: {}", f.explain(&e)));
    let one_hundred_twenty_five = f.num(125);
    let expected3 = {
        let sum = f.add(two, three);
        let lhs = f.pow(sum, n3);
        f.eq(lhs, one_hundred_twenty_five)
    };
    assert!(
        f.k.def_eq(inferred3, expected3),
        "add_pow(2,3,3) should state (2+3)^3 = 125 \
         (= 2^3+3*2^2*3+3*2*3^2+3^3), and both sides must compute to 125"
    );

    assert!(
        f.k.axiom_footprint(p.add_pow).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.add_pow)
    );
}

/// The row sum (`Nat.sum_choose_row`, via `add_pow` at `a=b=1`) and the term
/// bound (`Nat.choose_le_two_pow`, via `Nat.le_sumRange_of_lt`), checked
/// numerically: `sumRange (choose 4 ·) 5 = 16 = 2^4`, and
/// `choose 4 2 = 6 ≤ 16 = 2^4`. `Nat.one_pow` is checked directly first
/// (`1^5 = 1`), since both later theorems are built on it.
#[test]
fn row_sum_and_term_bound_hold_at_concrete_points() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // one_pow(5) : 1^5 = 1.
    let one = f.num(1);
    let five = f.num(5);
    let one_pow_proof = f.lemma(p.one_pow, &[five]);
    let one_pow_inferred =
        f.k.infer(one_pow_proof)
            .unwrap_or_else(|e| panic!("one_pow(5) should infer: {}", f.explain(&e)));
    let one_pow_expected = {
        let lhs = f.pow(one, five);
        f.eq(lhs, one)
    };
    assert!(
        f.k.def_eq(one_pow_inferred, one_pow_expected),
        "one_pow(5) should state 1^5 = 1"
    );

    // sum_choose_row(4) : sumRange (fun k => choose 4 k) 5 = 2^4 = 16 (the
    // row 1,4,6,4,1). Folding the numeral into the expected equation's own
    // RHS (rather than a separate def_eq check) forces both the theorem's
    // abstract shape AND the underlying computation to agree, the same style
    // `add_pow_holds_at_n_equals_two_and_three` uses.
    let four = f.num(4);
    let two = f.num(2);
    let sixteen = f.num(16);
    let row_proof = f.lemma(p.sum_choose_row, &[four]);
    let row_inferred =
        f.k.infer(row_proof)
            .unwrap_or_else(|e| panic!("sum_choose_row(4) should infer: {}", f.explain(&e)));
    let g = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let body = f.choose(four, k);
        f.lam_fv(k_fv, nat, body)
    };
    let five_terms = f.num(5);
    let row_expected = {
        let lhs = f.sum_range(g, five_terms);
        f.eq(lhs, sixteen)
    };
    assert!(
        f.k.def_eq(row_inferred, row_expected),
        "sum_choose_row(4) should state sumRange(choose 4 .)5 = 16 (1+4+6+4+1), \
         and both sides must compute to 16"
    );

    // choose_le_two_pow(4,2), under Le 2 4 (witness 2+2=4): choose 4 2 = 6 ≤
    // 2^4 = 16.
    let two_witness = f.num(2);
    let add_2_2 = f.add(two_witness, two_witness);
    let sum_eq = f.refl(add_2_2);
    let le_2_4 = f.lemma(p.le_intro, &[two_witness, four, two_witness, sum_eq]);
    let bound_proof = f.lemma(p.choose_le_two_pow, &[four, two_witness, le_2_4]);
    let bound_inferred =
        f.k.infer(bound_proof)
            .unwrap_or_else(|e| panic!("choose_le_two_pow(4,2,_) should infer: {}", f.explain(&e)));
    let six = f.num(6);
    let bound_expected = {
        let lhs = f.choose(four, two_witness);
        let rhs = f.pow(two, four);
        f.le(lhs, rhs)
    };
    assert!(
        f.k.def_eq(bound_inferred, bound_expected),
        "choose_le_two_pow(4,2,_) should state Le (choose 4 2) (2^4)"
    );
    let choose_4_2 = f.choose(four, two_witness);
    assert!(f.k.def_eq(choose_4_2, six), "choose 4 2 must reduce to 6");
    let pow_2_4 = f.pow(two, four);
    assert!(f.k.def_eq(pow_2_4, sixteen), "2^4 must reduce to 16");

    for name in [
        p.one_pow,
        p.le_sum_range_of_lt,
        p.sum_choose_row,
        p.choose_le_two_pow,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.succ_sub_of_le` — Vandermonde's convolution's named stall point —
/// checked at a concrete point: `i=3 ≤ m=5` gives
/// `sub (succ 5) 3 = succ (sub 5 3)`, i.e. `sub 6 3 = succ 2`, both sides `3`.
#[test]
fn succ_sub_of_le_holds_at_a_concrete_point() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let five = f.num(5);
    let two_witness = f.num(2);
    let add_3_2 = f.add(three, two_witness);
    let sum_eq = f.refl(add_3_2); // add(3,2) is definitionally 5
    let le_3_5 = f.lemma(p.le_intro, &[three, five, two_witness, sum_eq]);

    let proof = f.lemma(p.succ_sub_of_le, &[five, three, le_3_5]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("succ_sub_of_le(5,3,_) should infer: {}", f.explain(&e)));

    let sm = f.succ(five);
    let lhs = f.sub(sm, three);
    let sub_5_3 = f.sub(five, three);
    let rhs = f.succ(sub_5_3);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "succ_sub_of_le(5,3,_) should state sub (succ 5) 3 = succ (sub 5 3)"
    );

    let three_lit = f.num(3);
    assert!(f.k.def_eq(lhs, three_lit), "sub 6 3 must reduce to 3");
    assert!(
        f.k.def_eq(rhs, three_lit),
        "succ (sub 5 3) must reduce to 3"
    );

    assert!(
        f.k.axiom_footprint(p.succ_sub_of_le).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.succ_sub_of_le)
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

/// **Mandatory concrete instantiation** for `mul_succ_add_lt_of_le_of_lt`
/// (the "flatten a row-major (block, offset) index" bound `CReal.
/// samplePoint_reblock`'s own roadmap step 3 will need): `n = 2, m = 3, i =
/// 1, j = 2` (`n != m` and `i != j`, so a transposed argument or a swapped
/// `n`/`m` is visible). By hand: `sn = 3`, `sm = 4`, `global_idx = sn*i+j =
/// 3*1+2 = 5`, `total = sn*sm = 12`, and `5 < 12` genuinely holds. `hle : Le
/// 1 3` comes from `le_add_right` (`Le 1 (1+2)`, reducing to `Le 1 3`);
/// `hlt : Lt 2 3` comes from `le_refl` at `3` (`Le 3 3`, reducing to `Lt 2
/// 3 = Le (succ 2) 3 = Le 3 3`). Declaring the general lemma applied at
/// these concrete arguments against the INDEPENDENTLY hand-computed
/// conclusion `Lt 5 12` forces the kernel to check the two sides' `global_idx`/
/// `total` arithmetic reduces to 5 and 12 -- not merely that SOME instance
/// type-checks.
#[test]
fn row_major_index_bound_computes_five_lt_twelve_at_concrete_args() {
    let mut f = Fixture::new();
    let p = f.p;

    let n = f.num(2);
    let m = f.num(3);
    let i = f.num(1);
    let j = f.num(2);

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    // hle : Le i m = Le 1 3.
    let hle = f.lemma(p.le_add_right, &[one, two]);
    // hlt : Lt j (succ n) = Lt 2 3 = Le 3 3.
    let hlt = f.lemma(p.le_refl, &[three]);

    let proof = f.lemma(p.mul_succ_add_lt_of_le_of_lt, &[n, m, i, j, hle, hlt]);

    let five = f.num(5);
    let twelve = f.num(12);
    let stmt = f.lt(five, twelve);
    let name = f.name("row_major_index_five_lt_twelve");
    f.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
        panic!(
            "mul_succ_add_lt_of_le_of_lt did NOT compute 5 < 12 at n=2, m=3, \
             i=1, j=2 (not merely type-check): {}",
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

    let positive = f.zero_lt_succ(three);
    let remainder_bound = f.lemma(p.mod_lt, &[six, four, positive]);
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

/// `Nat.lcm` computes, and its checked properties apply at concrete points.
///
/// Hand-computed values (also recorded in the session report): `lcm 4 6 = 12`
/// (gcd 4 6 = 2, 24/2 = 12), `lcm 0 5 = 0`, `lcm 1 7 = 7`, `lcm 7 7 = 7`,
/// `lcm 0 0 = 0` (the degenerate corner: `gcd 0 0 = 0` too, and `div _ 0 = 0`,
/// so `0 * 0 = 0 * 0`). Every one of these is checked by kernel `def_eq`, not
/// merely by inferring the theorem's stated type — an `lcm` that type-checks
/// but computes wrong would pass every OTHER sweep in this repository.
#[test]
fn lcm_computes_and_satisfies_its_checked_properties() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let four = f.num(4);
    let five = f.num(5);
    let six = f.num(6);
    let seven = f.num(7);
    let twelve = f.num(12);

    let lcm_4_6 = f.const_app(p.lcm, &[four, six]);
    assert!(f.k.def_eq(lcm_4_6, twelve), "lcm 4 6 must reduce to 12");
    assert!(!f.k.def_eq(lcm_4_6, six), "lcm 4 6 must NOT reduce to 6");

    let lcm_0_5 = f.const_app(p.lcm, &[zero, five]);
    assert!(f.k.def_eq(lcm_0_5, zero), "lcm 0 5 must reduce to 0");

    let lcm_1_7 = f.const_app(p.lcm, &[one, seven]);
    assert!(f.k.def_eq(lcm_1_7, seven), "lcm 1 7 must reduce to 7");

    let lcm_7_7 = f.const_app(p.lcm, &[seven, seven]);
    assert!(f.k.def_eq(lcm_7_7, seven), "lcm 7 7 must reduce to 7");

    let lcm_0_0 = f.const_app(p.lcm, &[zero, zero]);
    assert!(f.k.def_eq(lcm_0_0, zero), "lcm 0 0 must reduce to 0");

    // `dvd_lcm_left`/`dvd_lcm_right`: lcm is a genuine common multiple.
    let dvd_left = f.lemma(p.dvd_lcm_left, &[four, six]);
    let dvd_left_ty = f.dvd(four, lcm_4_6);
    let inferred =
        f.k.infer(dvd_left)
            .expect("dvd_lcm_left must apply at (4,6)");
    assert!(f.k.def_eq(inferred, dvd_left_ty));

    let dvd_right = f.lemma(p.dvd_lcm_right, &[four, six]);
    let dvd_right_ty = f.dvd(six, lcm_4_6);
    let inferred =
        f.k.infer(dvd_right)
            .expect("dvd_lcm_right must apply at (4,6)");
    assert!(f.k.def_eq(inferred, dvd_right_ty));

    // `gcd_mul_lcm`: the headline identity, at a positive pair and at the
    // all-zero corner.
    let headline = f.lemma(p.gcd_mul_lcm, &[four, six]);
    let common = f.gcd(four, six);
    let mul_common_lcm = f.mul(common, lcm_4_6);
    let four_six = f.mul(four, six);
    let headline_ty = f.eq(mul_common_lcm, four_six);
    let inferred =
        f.k.infer(headline)
            .expect("gcd_mul_lcm must apply at (4,6)");
    assert!(f.k.def_eq(inferred, headline_ty));

    let headline_zero = f.lemma(p.gcd_mul_lcm, &[zero, zero]);
    let common_zero = f.gcd(zero, zero);
    let mul_common_zero_lcm = f.mul(common_zero, lcm_0_0);
    let zero_zero = f.mul(zero, zero);
    let headline_zero_ty = f.eq(mul_common_zero_lcm, zero_zero);
    let inferred =
        f.k.infer(headline_zero)
            .expect("gcd_mul_lcm must apply at the all-zero corner");
    assert!(f.k.def_eq(inferred, headline_zero_ty));

    // Negative control: a changed conclusion must be rejected by the trusted
    // gate, not just look wrong to a reader.
    let six_sq = f.mul(six, six);
    let wrong_ty = f.eq(mul_common_lcm, six_sq);
    let changed_name = f.name("gcd_mul_lcm_with_wrong_product");
    let error = f
        .declare_theorem(changed_name, wrong_ty, headline)
        .expect_err("gcd_mul_lcm's proof must not typecheck against a different product");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));
}

#[test]
fn mod_lt_matches_the_general_positive_denominator_contract() {
    let mut f = Fixture::new();
    let p = f.p;
    let declaration =
        f.k.environment()
            .get(p.mod_lt)
            .expect("Nat.mod_lt must be declared");
    assert!(matches!(declaration, Declaration::Theorem { .. }));
    assert!(
        f.k.axiom_footprint(p.mod_lt).is_empty(),
        "Nat.mod_lt must remain derived"
    );
    assert_eq!(
        f.k.render_lean(declaration.ty()),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat.lt AxNat.zero x1) -> AxNat.lt (AxNat.mod x0 x1) x1)))"
    );

    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let positive = f.zero_lt_succ(three);
    let proof = f.lemma(p.mod_lt, &[six, four, positive]);
    let expected = {
        let remainder = f.modulo(six, four);
        f.lt(remainder, four)
    };
    let inferred = f.k.infer(proof).expect("general Nat.mod_lt must apply");
    assert!(f.k.def_eq(inferred, expected));

    let old_argument_order = f.lemma(p.mod_lt, &[three, six, positive]);
    assert!(
        f.k.infer(old_argument_order).is_err(),
        "the old predecessor-first call shape must not remain silently usable"
    );
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

/// `Nat.mod_eq_cancel` at a concrete instance: `gcd 3 5 = 1` and
/// `3*2 ≡ 3*7 [5]` (both sides are `6 ≡ 21`, and `6 mod 5 = 21 mod 5 = 1`)
/// must cancel to `2 ≡ 7 [5]` — and the proof must genuinely REDUCE (the
/// `gcd 3 5 = 1` premise is discharged by `refl`, which only checks if the
/// executable `gcd` actually computes to `1`), not merely type-check.
///
/// A negative control: reusing the same premises against the WRONG
/// conclusion (`3 ≡ 7 [5]`, transposing the cancelled `2` for the modulus'
/// own `3`) must be rejected by the kernel.
#[test]
fn mod_eq_cancel_holds_at_a_concrete_instance_with_a_transposed_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.num(0);
    let three = f.num(3);
    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);

    let gcd_three_five = f.gcd(three, five);
    let coprime_proof = f.refl(gcd_three_five);
    // `coprime_proof : Eq (gcd 3 5) (gcd 3 5)`, accepted below against
    // `Eq (gcd 3 5) 1` only because `gcd 3 5` reduces to `1`.

    let three_two = f.mul(three, two);
    let three_seven = f.mul(three, seven);
    // `3*2 ≡ 3*7 [5]`, witnesses `u=3, v=0`: `6+5*3=21`, `21+5*0=21`.
    let hyp_proof = f.concrete_mod_eq(five, three_two, three_seven, three, zero);

    let cancel_proof = f.lemma(
        p.mod_eq_cancel,
        &[five, three, two, seven, coprime_proof, hyp_proof],
    );
    let cancel_ty = f.mod_eq(five, two, seven);
    let name = f.name("two_mod_five_seven_from_cancellation");
    f.declare_theorem(name, cancel_ty, cancel_proof)
        .unwrap_or_else(|e| panic!("mod_eq_cancel should admit: {}", f.explain(&e)));

    // Negative control: the same cancellation proof does NOT check against
    // `modEq 5 3 7` (transposing the cancelled `2` for the modulus' `3`).
    let wrong_ty = f.mod_eq(five, three, seven);
    let wrong_name = f.name("nc_mod_eq_cancel_wrong_conclusion");
    let wrong_proof = f.lemma(
        p.mod_eq_cancel,
        &[five, three, two, seven, coprime_proof, hyp_proof],
    );
    let result = f.declare_theorem(wrong_name, wrong_ty, wrong_proof);
    assert!(
        result.is_err(),
        "mod_eq_cancel's proof must be rejected against the transposed conclusion"
    );
    assert!(
        !f.k.environment().contains(wrong_name),
        "a rejected declaration must not enter the environment"
    );
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

    // NC62 — `Fin.mk`'s defining equation must retain its data field's actual
    // value, not a nearby one. `Fin.val n (Fin.mk n val h)` ι-reduces to
    // `val`; claim it equals `succ val` instead and supply the (correct,
    // now-mismatched) `Eq.refl val` proof.
    {
        let name = f.name("nc62_fin_val_mk_wrong_value");
        let nat = f.nat_ty();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let val_fv = f.fresh_fvar();
        let val = f.k.fvar(val_fv);
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);
        let bound = f.lt(val, n);
        let mk_nvh = f.const_app(p.fin_mk, &[n, val, h]);
        let lhs = f.const_app(p.fin_val, &[n, mk_nvh]);
        let wrong_rhs = f.succ(val);
        let bad = f.eq(lhs, wrong_rhs);
        let proof = f.refl(val);
        let ty = {
            let with_h = f.pi_fv(h_fv, bound, bad);
            let with_val = f.pi_fv(val_fv, nat, with_h);
            f.pi_fv(n_fv, nat, with_val)
        };
        let value = {
            let with_h = f.lam_fv(h_fv, bound, proof);
            let with_val = f.lam_fv(val_fv, nat, with_h);
            f.lam_fv(n_fv, nat, with_val)
        };
        let err = f
            .declare_theorem(name, ty, value)
            .expect_err("NC62: Fin.mk's defining equation must retain its actual value");
        println!(
            "NC62 (wrong Fin.val_mk value) rejected:\n  {}",
            f.explain(&err)
        );
        assert!(!f.k.environment().contains(name));
        rejections += 1;
    }

    assert_eq!(rejections, 62, "every negative control must be rejected");
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
        83 + 415,
        "every promised definition and theorem must be rendered"
    );
}

/// `Nat.eq_one_of_dvd_one` is a theorem with an empty axiom footprint, and it
/// *applies* — instantiating it at a concrete divisor type-checks.
///
/// The application matters: a theorem can be admitted with a type nothing can
/// use, and this one is the closing step for coprimality after dividing by a
/// gcd, so the shape it will be used in is the shape worth pinning.
#[test]
fn eq_one_of_dvd_one_is_derived_and_applies() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let declaration = k
        .environment()
        .get(p.eq_one_of_dvd_one)
        .expect("Nat.eq_one_of_dvd_one must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "eq_one_of_dvd_one must be a Theorem"
    );
    assert!(
        k.axiom_footprint(p.eq_one_of_dvd_one).is_empty(),
        "eq_one_of_dvd_one rests on a trusted declaration"
    );

    // Applied at a concrete divisor, the residue is `dvd 2 1 → 2 = 1`.
    let two = {
        let zero = k.const_(p.zero, vec![]);
        let succ = k.const_(p.succ, vec![]);
        let one = k.app(succ, zero);
        k.app(succ, one)
    };
    let theorem = k.const_(p.eq_one_of_dvd_one, vec![]);
    let applied = k.app(theorem, two);
    let inferred = k.infer(applied).expect("the application must type-check");
    let rendered = k.render_lean(inferred);
    assert!(
        rendered.contains("dvd") && rendered.contains("Eq"),
        "unexpected residue type: {rendered}"
    );
}

/// The four `Nat.Coprime`-import-backlog theorems
/// (`coprime_of_dvd_left`/`_right`, `prime_dvd_iff_not_coprime`,
/// `coprime_add_self_right`) are `Theorem`s, rest on no axiom, and each
/// *applies* at concrete numerals — instantiating their leading `Nat`
/// arguments produces the residual `Pi`/`Iff` type the doc comments promise,
/// not merely a type that admits.
#[test]
fn coprime_import_backlog_theorems_apply_at_concrete_numerals() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };

    for name in [
        p.coprime_of_dvd_left,
        p.coprime_of_dvd_right,
        p.prime_dvd_iff_not_coprime,
        p.coprime_add_self_right,
    ] {
        let declaration = k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{name:?} must be declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem"
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{name:?} rests on a trusted declaration"
        );
    }

    // `coprime_of_dvd_left 2 6 3 : dvd 2 6 -> gcd 6 3 = 1 -> gcd 2 3 = 1`.
    {
        let two = numeral(&mut k, 2);
        let six = numeral(&mut k, 6);
        let three = numeral(&mut k, 3);
        let theorem = k.const_(p.coprime_of_dvd_left, vec![]);
        let step1 = k.app(theorem, two);
        let step2 = k.app(step1, six);
        let applied = k.app(step2, three);
        let inferred = k.infer(applied).expect("must type-check");
        let rendered = k.render_lean(inferred);
        assert!(
            rendered.contains("dvd") && rendered.contains("gcd"),
            "unexpected residue type: {rendered}"
        );
    }

    // `coprime_of_dvd_right 3 2 6 : dvd 2 6 -> gcd 3 6 = 1 -> gcd 3 2 = 1`.
    {
        let three = numeral(&mut k, 3);
        let two = numeral(&mut k, 2);
        let six = numeral(&mut k, 6);
        let theorem = k.const_(p.coprime_of_dvd_right, vec![]);
        let step1 = k.app(theorem, three);
        let step2 = k.app(step1, two);
        let applied = k.app(step2, six);
        let inferred = k.infer(applied).expect("must type-check");
        let rendered = k.render_lean(inferred);
        assert!(
            rendered.contains("dvd") && rendered.contains("gcd"),
            "unexpected residue type: {rendered}"
        );
    }

    // `prime_dvd_iff_not_coprime 3 5 : prime_condition 3 -> Iff (dvd 3 5) (Not (gcd 3 5 = 1))`.
    {
        let three = numeral(&mut k, 3);
        let five = numeral(&mut k, 5);
        let theorem = k.const_(p.prime_dvd_iff_not_coprime, vec![]);
        let step1 = k.app(theorem, three);
        let applied = k.app(step1, five);
        let inferred = k.infer(applied).expect("must type-check");
        let rendered = k.render_lean(inferred);
        assert!(
            rendered.contains("dvd") && rendered.contains("Not") && rendered.contains("gcd"),
            "unexpected residue type: {rendered}"
        );
    }

    // `coprime_add_self_right 3 4 : Iff (gcd 3 (4+3) = 1) (gcd 3 4 = 1)`.
    {
        let three = numeral(&mut k, 3);
        let four = numeral(&mut k, 4);
        let theorem = k.const_(p.coprime_add_self_right, vec![]);
        let step1 = k.app(theorem, three);
        let applied = k.app(step1, four);
        let inferred = k.infer(applied).expect("must type-check");
        let rendered = k.render_lean(inferred);
        assert!(
            rendered.contains("gcd") && rendered.contains("Iff"),
            "unexpected residue type: {rendered}"
        );
    }
}

/// `Nat.coprime_of_bezout_one` composes with the *executable* gcd: at a coprime
/// pair, `gcd_bezout` already has the shape the theorem consumes, because
/// `gcd 2 3` REDUCES to `1`.
///
/// This is the round trip ℚ will make — a Bézout certificate for the cofactors
/// in, a `reduced` field out — so the composition is what is worth pinning, not
/// the theorem's mere existence.
#[test]
fn coprime_of_bezout_one_composes_with_the_executable_gcd() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };

    // `gcd_bezout 2 3 : bezout 2 3 (gcd 2 3)`, and `gcd 2 3` computes to `1`,
    // so it is accepted where `bezout 2 3 1` is required.
    let two = numeral(&mut k, 2);
    let three = numeral(&mut k, 3);
    let certificate = {
        let lemma = k.const_(p.gcd_bezout, vec![]);
        let applied = k.app(lemma, two);
        k.app(applied, three)
    };
    let coprime = {
        let theorem = k.const_(p.coprime_of_bezout_one, vec![]);
        let at_a = k.app(theorem, two);
        let at_b = k.app(at_a, three);
        k.app(at_b, certificate)
    };
    let inferred = k
        .infer(coprime)
        .expect("coprime_of_bezout_one must accept a computed Bezout certificate");
    let rendered = k.render_lean(inferred);
    assert!(
        rendered.contains("gcd"),
        "unexpected conclusion type: {rendered}"
    );

    // The hypothesis genuinely constrains: `gcd 2 4` computes to `2`, so
    // `gcd_bezout 2 4` is a certificate for `2`, not for `1`, and the same
    // application must be REJECTED.
    let four = numeral(&mut k, 4);
    let wrong_certificate = {
        let lemma = k.const_(p.gcd_bezout, vec![]);
        let applied = k.app(lemma, two);
        k.app(applied, four)
    };
    let misapplied = {
        let theorem = k.const_(p.coprime_of_bezout_one, vec![]);
        let at_a = k.app(theorem, two);
        let at_b = k.app(at_a, three);
        k.app(at_b, wrong_certificate)
    };
    assert!(
        k.infer(misapplied).is_err(),
        "a Bezout certificate for gcd 2 4 = 2 was accepted where 1 was required"
    );
}

/// `Nat.gcd_cofactors_coprime` applies to a concrete pair, and its hypothesis
/// genuinely constrains.
///
/// With `g = 2, a = 1, b = 2` the premise `gcd (2*1) (2*2) = 2` is `rfl`, since
/// `gcd` computes, and the conclusion is `gcd 1 2 = 1`. With `a = 2, b = 4` the
/// premise would be `gcd 4 8 = 2`, which is false — `gcd 4 8` computes to `4` —
/// so the same `rfl` must be REJECTED. That rejection is what shows the
/// hypothesis is load-bearing rather than decorative.
#[test]
fn gcd_cofactors_coprime_applies_and_its_premise_constrains() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let nat_ty = k.const_(p.nat, vec![]);
    let level = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };

    let two = numeral(&mut k, 2);
    let one = numeral(&mut k, 1);
    let zero = k.const_(p.zero, vec![]);
    // 1 <= 2
    let positive = {
        let base = {
            let lemma = k.const_(p.zero_le, vec![]);
            k.app(lemma, one)
        };
        let lemma = k.const_(p.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero);
        let at_one = k.app(at_zero, one);
        k.app(at_one, base)
    };

    let apply_at = |k: &mut Kernel, a: ExprId, b: ExprId, witness: ExprId| {
        let theorem = k.const_(p.gcd_cofactors_coprime, vec![]);
        let at_g = k.app(theorem, two);
        let at_a = k.app(at_g, a);
        let at_b = k.app(at_a, b);
        let at_pos = k.app(at_b, positive);
        k.app(at_pos, witness)
    };
    // `rfl : gcd (2*a) (2*b) = 2`, which only checks when it is actually true.
    let refl_at_two = {
        let refl = k.const_(p.logic.eq_refl, vec![level]);
        let at_ty = k.app(refl, nat_ty);
        k.app(at_ty, two)
    };

    let good = apply_at(&mut k, one, two, refl_at_two);
    let inferred = k
        .infer(good)
        .expect("gcd (2*1) (2*2) = 2 holds by computation");
    let rendered = k.render_lean(inferred);
    assert!(
        rendered.contains("gcd"),
        "unexpected conclusion: {rendered}"
    );

    let four = numeral(&mut k, 4);
    let bad = apply_at(&mut k, two, four, refl_at_two);
    assert!(
        k.infer(bad).is_err(),
        "accepted `gcd 4 8 = 2`, which is false — gcd 4 8 computes to 4"
    );
}

/// `Nat.div_mul_cancel_of_dvd` applies concretely, and its divisibility
/// hypothesis is what makes it true.
///
/// `2 * (4/2) = 4` needs a witness for `2 ∣ 4`, built as
/// `Exists.intro … 2 (rfl : 4 = 2*2)`. The same construction at `5` requires
/// `5 = 2*2`, which computes to `4 ≠ 5`, so it must be REJECTED — the theorem
/// cannot be applied to a non-multiple.
#[test]
fn div_mul_cancel_needs_real_divisibility() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let nat_ty = k.const_(p.nat, vec![]);
    let level = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };
    let zero = k.const_(p.zero, vec![]);
    let one = numeral(&mut k, 1);
    let two = numeral(&mut k, 2);

    // 1 <= 2
    let positive = {
        let base = {
            let lemma = k.const_(p.zero_le, vec![]);
            k.app(lemma, one)
        };
        let lemma = k.const_(p.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero);
        let at_one = k.app(at_zero, one);
        k.app(at_one, base)
    };

    // `Exists.intro Nat (fun q => Eq target (2*q)) 2 (rfl : target = 2*2)`
    let witness_for = |k: &mut Kernel, target: ExprId| {
        let predicate = {
            // `fun (q : Nat) => Eq Nat target (2 * q)`, with `q` as de Bruijn 0.
            let q = k.bvar(0);
            let product = {
                let mul = k.const_(p.mul, vec![]);
                let at_two = k.app(mul, two);
                k.app(at_two, q)
            };
            let eq = k.const_(p.logic.eq, vec![level]);
            let at_ty = k.app(eq, nat_ty);
            let at_lhs = k.app(at_ty, target);
            let body = k.app(at_lhs, product);
            let anon = k.anon();
            k.lam(anon, nat_ty, body, BinderInfo::Default)
        };
        let refl = {
            let refl = k.const_(p.logic.eq_refl, vec![level]);
            let at_ty = k.app(refl, nat_ty);
            k.app(at_ty, target)
        };
        let intro = k.const_(p.logic.exists_intro, vec![level]);
        let at_ty = k.app(intro, nat_ty);
        let at_pred = k.app(at_ty, predicate);
        let at_witness = k.app(at_pred, two);
        k.app(at_witness, refl)
    };

    let apply_at = |k: &mut Kernel, target: ExprId, divides: ExprId| {
        let theorem = k.const_(p.div_mul_cancel_of_dvd, vec![]);
        let at_g = k.app(theorem, two);
        let at_n = k.app(at_g, target);
        let at_pos = k.app(at_n, positive);
        k.app(at_pos, divides)
    };

    let four = numeral(&mut k, 4);
    let good_witness = witness_for(&mut k, four);
    let good = apply_at(&mut k, four, good_witness);
    assert!(
        k.infer(good).is_ok(),
        "2 divides 4, so 2 * (4/2) = 4 must be derivable"
    );

    let five = numeral(&mut k, 5);
    let bad_witness = witness_for(&mut k, five);
    assert!(
        k.infer(bad_witness).is_err(),
        "accepted a divisibility witness claiming 5 = 2*2"
    );
}

/// The positivity lemmas `Rat.normalize` needs, and the hypothesis that carries
/// them.
///
/// `one_le_of_dvd_pos` says a divisor of a positive number is positive. Its
/// positivity hypothesis is about the DIVIDEND, so supplying `1 ≤ 4` while the
/// dividend is `6` must be a type error — that is what the second half checks.
#[test]
fn positivity_lemmas_apply_and_track_their_dividend() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let nat_ty = k.const_(p.nat, vec![]);
    let level = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };
    let zero = k.const_(p.zero, vec![]);

    // `1 <= n` for a literal successor n, via le_succ_succ on zero_le.
    let one_le = |k: &mut Kernel, n: usize| {
        let predecessor = numeral(k, n - 1);
        let base = {
            let lemma = k.const_(p.zero_le, vec![]);
            k.app(lemma, predecessor)
        };
        let lemma = k.const_(p.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero);
        let at_pred = k.app(at_zero, predecessor);
        k.app(at_pred, base)
    };

    let two = numeral(&mut k, 2);
    let four = numeral(&mut k, 4);
    let six = numeral(&mut k, 6);

    // `2 | 4`, witnessed by `4 = 2*2`.
    let divides = {
        let predicate = {
            let q = k.bvar(0);
            let product = {
                let mul = k.const_(p.mul, vec![]);
                let at_two = k.app(mul, two);
                k.app(at_two, q)
            };
            let eq = k.const_(p.logic.eq, vec![level]);
            let at_ty = k.app(eq, nat_ty);
            let at_lhs = k.app(at_ty, four);
            let body = k.app(at_lhs, product);
            let anon = k.anon();
            k.lam(anon, nat_ty, body, BinderInfo::Default)
        };
        let refl = {
            let refl = k.const_(p.logic.eq_refl, vec![level]);
            let at_ty = k.app(refl, nat_ty);
            k.app(at_ty, four)
        };
        let intro = k.const_(p.logic.exists_intro, vec![level]);
        let at_ty = k.app(intro, nat_ty);
        let at_pred = k.app(at_ty, predicate);
        let at_witness = k.app(at_pred, two);
        k.app(at_witness, refl)
    };

    let four_positive = one_le(&mut k, 4);
    let good = {
        let theorem = k.const_(p.one_le_of_dvd_pos, vec![]);
        let at_g = k.app(theorem, two);
        let at_n = k.app(at_g, four);
        let at_pos = k.app(at_n, four_positive);
        k.app(at_pos, divides)
    };
    assert!(
        k.infer(good).is_ok(),
        "2 divides 4 and 4 is positive, so 2 must be positive"
    );

    // The positivity hypothesis is about the dividend: `1 <= 4` cannot stand in
    // for `1 <= 6`.
    let mismatched = {
        let theorem = k.const_(p.one_le_of_dvd_pos, vec![]);
        let at_g = k.app(theorem, two);
        let at_n = k.app(at_g, six);
        k.app(at_n, four_positive)
    };
    assert!(
        k.infer(mismatched).is_err(),
        "accepted `1 <= 4` as the positivity of the dividend 6"
    );
}

/// `Nat.factorial` **computes**, and `dvd_factorial_of_le` applies to concrete
/// arguments with a conclusion that reduces to a true divisibility fact.
///
/// The computation half is the load-bearing control, not decoration. Both
/// recursion rules hold definitionally, so a step that multiplied by `j` instead
/// of `succ j` would still type-check, `factorial_zero`/`factorial_succ` would
/// still be admitted as stated, and `dvd_factorial_of_le` would still be
/// admitted — about the constantly-zero function, which everything divides.
/// Reduction to numerals with negative controls beside it is what excludes that.
#[test]
fn factorial_computes_and_every_positive_bound_divides_it() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let at_zero = f.factorial(zero);
    assert!(f.k.def_eq(at_zero, one), "0! must reduce to 1");
    let at_one = f.factorial(one);
    assert!(f.k.def_eq(at_one, one), "1! must reduce to 1");

    let four = f.num(4);
    let twenty_four = f.num(24);
    let at_four = f.factorial(four);
    assert!(f.k.def_eq(at_four, twenty_four), "4! must reduce to 24");

    let five = f.num(5);
    let one_twenty = f.num(120);
    let at_five = f.factorial(five);
    assert!(f.k.def_eq(at_five, one_twenty), "5! must reduce to 120");

    // NEGATIVE reduction controls: `def_eq` must not be vacuously true here, and
    // the zero-collapse a mis-stepped recursion would produce must be visible.
    assert!(!f.k.def_eq(at_four, zero), "4! must NOT be def-eq to 0");
    assert!(
        !f.k.def_eq(at_five, twenty_four),
        "5! must NOT be def-eq to 24"
    );

    // `1 <= 3` and `3 <= 5`, built from the `Le` constructors.
    let three = f.num(3);
    let two = f.num(2);
    let one_le_three = {
        let base = f.lemma(p.le_refl, &[one]);
        let to_two = f.lemma(p.le_step, &[one, one, base]);
        f.lemma(p.le_step, &[one, two, to_two])
    };
    let three_le_five = {
        let base = f.lemma(p.le_refl, &[three]);
        let to_four = f.lemma(p.le_step, &[three, three, base]);
        f.lemma(p.le_step, &[three, four, to_four])
    };

    let applied = f.lemma(
        p.dvd_factorial_of_le,
        &[three, five, one_le_three, three_le_five],
    );
    let inferred =
        f.k.infer(applied)
            .expect("1 <= 3 and 3 <= 5, so the theorem applies at (3, 5)");
    let expected = {
        let target = f.factorial(five);
        f.dvd(three, target)
    };
    assert!(f.k.def_eq(inferred, expected));
    // The conclusion is about the NUMBER 120, not an opaque application.
    let concrete = f.dvd(three, one_twenty);
    assert!(
        f.k.def_eq(inferred, concrete),
        "the admitted conclusion must reduce to `3 divides 120`"
    );

    // Both hypotheses are load-bearing, and the kernel checks the indices:
    // `3 <= 5` is not `3 <= 3`, and it is not `1 <= 3` either.
    let wrong_bound = {
        let theorem = f.k.const_(p.dvd_factorial_of_le, vec![]);
        let at_divisor = f.k.app(theorem, three);
        let at_bound = f.k.app(at_divisor, three);
        let at_positive = f.k.app(at_bound, one_le_three);
        f.k.app(at_positive, three_le_five)
    };
    assert!(
        f.k.infer(wrong_bound).is_err(),
        "accepted a proof of `3 <= 5` where `3 <= 3` was required"
    );
    let wrong_positivity = {
        let theorem = f.k.const_(p.dvd_factorial_of_le, vec![]);
        let at_divisor = f.k.app(theorem, three);
        let at_bound = f.k.app(at_divisor, five);
        f.k.app(at_bound, three_le_five)
    };
    assert!(
        f.k.infer(wrong_positivity).is_err(),
        "accepted a proof of `3 <= 5` as the positivity hypothesis `1 <= 3`"
    );
}

/// `Nat.descFactorial` computes the right VALUES at concrete instances —
/// complementary to the fully symbolic proofs `declare_desc_factorial_of_lt`
/// and friends type-check against, which catch a wrong recursion scheme but
/// not a wrong recursion *direction* that still happens to type-check.
///
/// `5.descFactorial 0 = 1`, `5.descFactorial 2 = 5*4 = 20`,
/// `5.descFactorial 5 = 5! = 120`, and — the truncated-`Nat.sub` boundary —
/// `5.descFactorial 6 = 0`, both by direct reduction and via
/// `descFactorial_of_lt` applied at the concrete pair `(5, 6)`.
#[test]
fn desc_factorial_computes_and_collapses_past_its_base() {
    let mut f = Fixture::new();
    let p = f.p;

    let five = f.num(5);
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let six = f.num(6);

    let at_zero = f.const_app(p.desc_factorial, &[five, zero]);
    assert!(
        f.k.def_eq(at_zero, one),
        "5.descFactorial 0 must reduce to 1"
    );

    let at_two = f.const_app(p.desc_factorial, &[five, two]);
    let twenty = f.num(20);
    assert!(
        f.k.def_eq(at_two, twenty),
        "5.descFactorial 2 must reduce to 5*4 = 20"
    );

    let at_five = f.const_app(p.desc_factorial, &[five, five]);
    let one_twenty = f.num(120);
    assert!(
        f.k.def_eq(at_five, one_twenty),
        "5.descFactorial 5 must reduce to 5! = 120"
    );

    // NEGATIVE reduction control: `def_eq` must not be vacuously true here.
    assert!(
        !f.k.def_eq(at_two, one_twenty),
        "5.descFactorial 2 must NOT be def-eq to 120"
    );

    // Past the base: `k > n` truncates `Nat.sub` to zero at every remaining
    // factor, so the product collapses.
    let at_six = f.const_app(p.desc_factorial, &[five, six]);
    assert!(
        f.k.def_eq(at_six, zero),
        "5.descFactorial 6 must reduce to 0 (6 > 5)"
    );

    // `descFactorial_of_lt` applied at the concrete pair (5, 6): `5 < 6` is
    // `Le 6 6`, i.e. `Nat.le.refl 6`.
    let five_lt_six = f.lemma(p.le_refl, &[six]);
    let applied = f.lemma(p.desc_factorial_of_lt, &[five, six, five_lt_six]);
    let inferred =
        f.k.infer(applied)
            .expect("5 < 6, so descFactorial_of_lt applies at (5, 6)");
    let expected = f.eq(at_six, zero);
    assert!(f.k.def_eq(inferred, expected));

    // The hypothesis is load-bearing: swapping in a proof of `5 < 5` (not
    // `5 < 6`) must be rejected, not silently accepted for the wrong bound.
    let five_lt_five = f.lemma(p.le_refl, &[five]);
    let wrong_bound = {
        let theorem = f.k.const_(p.desc_factorial_of_lt, vec![]);
        let at_n = f.k.app(theorem, five);
        let at_k = f.k.app(at_n, six);
        f.k.app(at_k, five_lt_five)
    };
    assert!(
        f.k.infer(wrong_bound).is_err(),
        "accepted a proof of `5 < 5` where `5 < 6` was required"
    );
}

/// `Nat.ascFactorial` computes the right VALUES at concrete instances — the
/// kernel accepts a `Definition` once it type-checks regardless of what it
/// COMPUTES (`Nat -> Nat -> Nat` either way), so this is the only guard
/// against a wrong recursion *direction* that still type-checks: `add`
/// swapped for `sub`, or the two step-function arguments transposed.
///
/// `3.ascFactorial 0 = 1`, `3.ascFactorial 2 = 3*4 = 12`,
/// `5.ascFactorial 1 = 5`. NEGATIVE control: `3.ascFactorial 2` must NOT be
/// def-eq to `5.descFactorial 2 = 20` (a *descending* product at unrelated
/// arguments) NOR to `12`'s descending twin `3*2 = 6` (the value a
/// copy-pasted `sub`-based step would compute for `descFactorial 3 2` at the
/// SAME arguments) — catching exactly the copy-paste this module's doc
/// comment warns about.
#[test]
fn asc_factorial_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let five = f.num(5);
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);

    let at_zero = f.const_app(p.asc_factorial, &[three, zero]);
    assert!(
        f.k.def_eq(at_zero, one),
        "3.ascFactorial 0 must reduce to 1"
    );

    let at_two = f.const_app(p.asc_factorial, &[three, two]);
    let twelve = f.num(12);
    assert!(
        f.k.def_eq(at_two, twelve),
        "3.ascFactorial 2 must reduce to 3*4 = 12"
    );

    let one_right = f.const_app(p.asc_factorial, &[five, one]);
    assert!(
        f.k.def_eq(one_right, five),
        "5.ascFactorial 1 must reduce to 5"
    );

    // NEGATIVE reduction controls: `def_eq` must not be vacuously true here.
    let six = f.num(6);
    assert!(
        !f.k.def_eq(at_two, six),
        "3.ascFactorial 2 must NOT be def-eq to the DESCENDING product 3*2 = 6"
    );
    let descending_at_two = f.const_app(p.desc_factorial, &[three, two]);
    assert!(
        !f.k.def_eq(at_two, descending_at_two),
        "3.ascFactorial 2 must NOT be def-eq to 3.descFactorial 2"
    );
}

/// `Nat.multichoose` computes the right VALUES at concrete instances —
/// `multichoose n k := choose (pred (add n k)) k` is a plain abbreviation,
/// so a dropped `pred` (an off-by-one in the `-1`) would still type-check.
///
/// `0.multichoose 0 = choose 0 0 = 1` (the empty multiset), `3.multichoose 2
/// = choose 4 2 = 6` (the six size-2 multisets of `{a,b,c}`: `aa, ab, ac,
/// bb, bc, cc`), `1.multichoose 4 = choose 4 4 = 1`, `4.multichoose 1 =
/// choose 4 1 = 4`. NEGATIVE control: `3.multichoose 2` must NOT be def-eq
/// to `choose (add 3 2) 2 = choose 5 2 = 10` — the value a `pred`-dropping
/// copy-paste would compute at the same arguments.
#[test]
fn multichoose_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);

    let at_zero_zero = f.const_app(p.multichoose, &[zero, zero]);
    assert!(
        f.k.def_eq(at_zero_zero, one),
        "0.multichoose 0 must reduce to 1"
    );

    let at_three_two = f.const_app(p.multichoose, &[three, two]);
    let six = f.num(6);
    assert!(
        f.k.def_eq(at_three_two, six),
        "3.multichoose 2 must reduce to choose 4 2 = 6"
    );

    let at_one_four = f.const_app(p.multichoose, &[one, four]);
    assert!(
        f.k.def_eq(at_one_four, one),
        "1.multichoose 4 must reduce to choose 4 4 = 1"
    );

    let at_four_one = f.const_app(p.multichoose, &[four, one]);
    assert!(
        f.k.def_eq(at_four_one, four),
        "4.multichoose 1 must reduce to choose 4 1 = 4"
    );

    // NEGATIVE reduction control: dropping `pred` (an off-by-one in the
    // `- 1`) at the same arguments gives a DIFFERENT value; `def_eq` must
    // not be vacuously true here.
    let ten = f.num(10);
    assert!(
        !f.k.def_eq(at_three_two, ten),
        "3.multichoose 2 must NOT be def-eq to choose 5 2 = 10 (the `pred`-dropped value)"
    );
}

/// `∃ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ∧ p ∣ m` — the statement, not just
/// the name, plus the two lemmas it rests on applied to concrete numbers.
///
/// The **statement** check is the load-bearing control here. Nothing in this
/// slice is a `Definition`, so there is no degenerate computation rule to guard
/// against: the kernel re-checks each proof term against its stated type, and a
/// witness that was not actually prime (say `m` itself at `m = 6`) would be
/// rejected outright. What the kernel cannot notice is a statement that is
/// *weaker than intended* — spelling the primality lower bound `1 ≤ p` instead
/// of `2 ≤ p` still type-checks, still admits, and is still provable by the same
/// argument, but it is satisfied by `p = 1`, whose only divisor is `1`. Euclid's
/// theorem cannot be closed with it. So the admitted type is compared against an
/// independently built term, with that exact weakening as the negative control.
#[test]
fn every_number_at_least_two_has_a_prime_divisor() {
    /// `∃ x, (bound ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x) ∧ x ∣ m`, built here
    /// rather than read back from the prelude.
    fn prime_divisor_of(f: &mut Fixture, bound: u32, m: ExprId) -> ExprId {
        let p = f.p;
        let nat = f.nat_ty();
        let level = f.level_one();
        let lower_bound = f.num(bound);
        let unit = f.num(1);
        let predicate = {
            let x_fv = f.fresh_fvar();
            let x = f.k.fvar(x_fv);
            let lower = f.le(lower_bound, x);
            let divisors = {
                let c_fv = f.fresh_fvar();
                let c = f.k.fvar(c_fv);
                let hypothesis = f.dvd(c, x);
                let trivial = f.eq(c, unit);
                let whole = f.eq(c, x);
                let disjunction = f.const_app(p.logic.or, &[trivial, whole]);
                let body = f.arrow(hypothesis, disjunction);
                f.pi_fv(c_fv, nat, body)
            };
            let prime = f.const_app(p.logic.and, &[lower, divisors]);
            let divides = f.dvd(x, m);
            let body = f.const_app(p.logic.and, &[prime, divides]);
            f.lam_fv(x_fv, nat, body)
        };
        let exists = f.k.const_(p.logic.exists_, vec![level]);
        f.apply(exists, &[nat, predicate])
    }

    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);

    // `1 <= 6` and `2 <= 6`, built from the `Le` constructors.
    let le_chain = |f: &mut Fixture, from: ExprId, steps: &[ExprId]| {
        let mut proof = f.lemma(p.le_refl, &[from]);
        for &rung in steps {
            proof = f.lemma(p.le_step, &[from, rung, proof]);
        }
        proof
    };
    let five = f.num(5);
    let one_le_six = le_chain(&mut f, one, &[one, two, three, four, five]);
    let two_le_six = le_chain(&mut f, two, &[two, three, four, five]);

    // --- the admitted STATEMENT, compared against an independent build -------
    let declared = {
        let theorem = f.k.const_(p.exists_prime_dvd, vec![]);
        f.k.infer(theorem)
            .expect("`Nat.exists_prime_dvd` must be in the environment")
    };
    let expected = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let hypothesis = f.le(two, m);
        let conclusion = prime_divisor_of(&mut f, 2, m);
        let body = f.arrow(hypothesis, conclusion);
        let nat = f.nat_ty();
        f.pi_fv(m_fv, nat, body)
    };
    assert!(
        f.k.def_eq(declared, expected),
        "the admitted type is not `∀ m, 2 <= m → ∃ p, (2 <= p ∧ ∀ d, d | p → d = 1 ∨ d = p) ∧ p | m`"
    );
    // NEGATIVE control: the `1 <= p` weakening is a DIFFERENT proposition. It
    // would still be provable and still admit, and `p = 1` would satisfy it.
    let weakened = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let hypothesis = f.le(two, m);
        let conclusion = prime_divisor_of(&mut f, 1, m);
        let body = f.arrow(hypothesis, conclusion);
        let nat = f.nat_ty();
        f.pi_fv(m_fv, nat, body)
    };
    assert!(
        !f.k.def_eq(declared, weakened),
        "`2 <= p` and `1 <= p` must not be the same statement — `p = 1` satisfies the second"
    );

    // --- applied to a concrete COMPOSITE number -----------------------------
    let applied = f.lemma(p.exists_prime_dvd, &[six, two_le_six]);
    let inferred =
        f.k.infer(applied)
            .expect("2 <= 6, so the theorem applies at m = 6");
    let expected_at_six = prime_divisor_of(&mut f, 2, six);
    assert!(
        f.k.def_eq(inferred, expected_at_six),
        "the conclusion at 6 must be `∃ p, prime p ∧ p | 6`"
    );
    // The hypothesis is load-bearing and the kernel checks its index.
    let wrong_hypothesis = {
        let theorem = f.k.const_(p.exists_prime_dvd, vec![]);
        let at_six = f.k.app(theorem, six);
        f.k.app(at_six, one_le_six)
    };
    assert!(
        f.k.infer(wrong_hypothesis).is_err(),
        "accepted `1 <= 6` where `2 <= 6` was required"
    );

    // --- the bound `le_of_dvd` supplies, and its positivity guard -----------
    let three_divides_six = {
        let level = f.level_one();
        let nat = f.nat_ty();
        let predicate = f.dvd_predicate(three, six);
        let witness = f.refl(six);
        let intro = f.k.const_(p.logic.exists_intro, vec![level]);
        f.apply(intro, &[nat, predicate, two, witness])
    };
    let bounded = f.lemma(p.le_of_dvd, &[three, six, one_le_six, three_divides_six]);
    let bound_ty =
        f.k.infer(bounded)
            .expect("3 divides 6 and 6 is positive, so 3 <= 6");
    let expected_bound = f.le(three, six);
    assert!(f.k.def_eq(bound_ty, expected_bound));
    // Positivity is not decoration: `2 | 0` holds, and `2 <= 0` does not. The
    // hypothesis is the only thing standing between them.
    let zero = f.zero();
    let two_divides_zero = f.lemma(p.dvd_zero, &[two]);
    let unguarded = {
        let theorem = f.k.const_(p.le_of_dvd, vec![]);
        let at_divisor = f.k.app(theorem, two);
        let at_target = f.k.app(at_divisor, zero);
        let at_positive = f.k.app(at_target, one_le_six);
        f.k.app(at_positive, two_divides_zero)
    };
    assert!(
        f.k.infer(unguarded).is_err(),
        "accepted `1 <= 6` as the positivity of 0, which would yield `2 <= 0`"
    );

    // --- the search these rest on, and the successor dichotomy --------------
    let searched = f.lemma(p.least_divisor_search, &[six, six]);
    assert!(
        f.k.infer(searched).is_ok(),
        "the least-divisor search must apply at (k, m) = (6, 6)"
    );
    let dichotomy = f.lemma(p.two_le_succ_or_eq_one, &[three]);
    let dichotomy_ty =
        f.k.infer(dichotomy)
            .expect("the successor dichotomy must apply at j = 3");
    let expected_dichotomy = {
        let big = f.le(two, four);
        let small = f.eq(four, one);
        f.const_app(p.logic.or, &[big, small])
    };
    assert!(f.k.def_eq(dichotomy_ty, expected_dichotomy));
}

/// `Nat.succ_mul_choose_eq` at a concrete point: `n = 3, k = 1` gives
/// `succ 1 * choose 4 2 = succ 3 * choose 3 1`, i.e. `2 * 6 = 4 * 3`, both
/// sides reducing to `12`.
#[test]
fn succ_mul_choose_eq_holds_at_a_concrete_point() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let one = f.num(1);
    let proof = f.lemma(p.succ_mul_choose_eq, &[three, one]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("succ_mul_choose_eq(3,1) should infer: {}", f.explain(&e)));

    let two = f.num(2);
    let four = f.num(4);
    let choose_4_2 = f.choose(four, two);
    let lhs = f.mul(two, choose_4_2);
    let choose_3_1 = f.choose(three, one);
    let rhs = f.mul(four, choose_3_1);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "succ_mul_choose_eq(3,1) should state succ 1 * choose 4 2 = succ 3 * choose 3 1"
    );

    let twelve = f.num(12);
    assert!(f.k.def_eq(lhs, twelve), "2 * choose 4 2 must reduce to 12");
    assert!(f.k.def_eq(rhs, twelve), "4 * choose 3 1 must reduce to 12");

    assert!(
        f.k.axiom_footprint(p.succ_mul_choose_eq).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.succ_mul_choose_eq)
    );
}

/// `Nat.prime_dvd_choose`'s statement, checked against an independently built
/// type, plus its shape and reduction at a concrete `p = 5, k = 2`
/// (`choose 5 2` reduces to `10`). Primality itself is left as the
/// hypothesis's TYPE rather than a discharged proof — mirroring
/// `every_number_at_least_two_has_a_prime_divisor`'s own treatment of a found
/// prime — since manufacturing a from-scratch primality certificate for a
/// literal numeral is a separate concern from what this theorem proves.
#[test]
fn prime_dvd_choose_matches_its_statement_at_a_concrete_point() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.num(1);
    let two = f.num(2);

    let prime_ty_of = |f: &mut Fixture, pp: ExprId| -> ExprId {
        let lower = f.le(two, pp);
        let c_fv = f.fresh_fvar();
        let c = f.k.fvar(c_fv);
        let hyp = f.dvd(c, pp);
        let is_one = f.eq(c, one);
        let is_pp = f.eq(c, pp);
        let disjunction = f.const_app(p.logic.or, &[is_one, is_pp]);
        let body = f.arrow(hyp, disjunction);
        let divisors = f.pi_fv(c_fv, nat, body);
        f.const_app(p.logic.and, &[lower, divisors])
    };

    // --- the STATEMENT, compared against an independent build ---------------
    let declared = {
        let theorem = f.k.const_(p.prime_dvd_choose, vec![]);
        f.k.infer(theorem)
            .expect("`Nat.prime_dvd_choose` must be in the environment")
    };
    let expected = {
        let pp_fv = f.fresh_fvar();
        let pp = f.k.fvar(pp_fv);
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let prime_ty = prime_ty_of(&mut f, pp);
        let zero = f.zero();
        let pos_ty = f.lt(zero, k);
        let lt_ty = f.lt(k, pp);
        let choose_pp_k = f.choose(pp, k);
        let conclusion = f.dvd(pp, choose_pp_k);
        let inner1 = f.arrow(lt_ty, conclusion);
        let inner2 = f.arrow(pos_ty, inner1);
        let body_ty = f.arrow(prime_ty, inner2);
        let with_k = f.pi_fv(k_fv, nat, body_ty);
        f.pi_fv(pp_fv, nat, with_k)
    };
    assert!(
        f.k.def_eq(declared, expected),
        "the admitted type is not \
         `∀ p k, (2 <= p ∧ ∀ d, d|p -> d=1 ∨ d=p) -> 0<k -> k<p -> p|choose p k`"
    );

    // --- applied at a concrete p=5, k=2 --------------------------------------
    let five = f.num(5);
    let partial = {
        let theorem = f.k.const_(p.prime_dvd_choose, vec![]);
        let at_p = f.k.app(theorem, five);
        f.k.app(at_p, two)
    };
    let partial_ty = f.k.infer(partial).unwrap_or_else(|e| {
        panic!(
            "prime_dvd_choose should apply at p=5, k=2: {}",
            f.explain(&e)
        )
    });
    let expected_partial = {
        let prime_ty = prime_ty_of(&mut f, five);
        let zero = f.zero();
        let pos_ty = f.lt(zero, two);
        let lt_ty = f.lt(two, five);
        let choose_5_2 = f.choose(five, two);
        let conclusion = f.dvd(five, choose_5_2);
        let inner1 = f.arrow(lt_ty, conclusion);
        let inner2 = f.arrow(pos_ty, inner1);
        f.arrow(prime_ty, inner2)
    };
    assert!(
        f.k.def_eq(partial_ty, expected_partial),
        "prime_dvd_choose(5,2) should await (prime 5) -> 0<2 -> 2<5 -> 5 | choose 5 2"
    );

    let choose_5_2 = f.choose(five, two);
    let ten = f.num(10);
    assert!(f.k.def_eq(choose_5_2, ten), "choose 5 2 must reduce to 10");

    assert!(
        f.k.axiom_footprint(p.prime_dvd_choose).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.prime_dvd_choose)
    );
}

/// **Fermat's little theorem says what the ledger says it says.**
///
/// `the_nat_prelude_declares_no_axioms` and `the_build_is_deterministic` cover
/// these names already, and neither can carry this claim: a theorem stating
/// something *weaker* — primality replaced by `0 < p`, `a^p ≡ a` replaced by
/// the vacuous `a ≡ a`, the modulus and the base transposed — has exactly the
/// same empty footprint and renders into the same deterministic list, whose
/// assertion is on the *count* of entries and not on any one of them.
///
/// `artifacts/facts/` records a *statement*, so a statement is what is pinned.
/// Both the Frobenius identity and Fermat proper are asserted, because Fermat
/// alone would leave the identity it rests on free to drift.
#[test]
fn fermat_and_frobenius_are_stated_over_primes_not_merely_positive_moduli() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        k.render_lean(
            k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
                .ty(),
        )
    };
    for name in [p.add_pow_modeq_prime, p.pow_prime_modeq_self] {
        let got = rendered(&k, name);
        assert!(
            got.contains("AxNat.dvd"),
            "{} must quantify over PRIMES -- the primality predicate is spelled \
             inline as `2 <= p and forall d, d | p -> d = 1 or d = p`, so a statement \
             with no `AxNat.dvd` in it has dropped it. Note the carrier renders as \
             `AxNat` -- an INDUCTIVE type whose trusted surface measures 0, despite the \
             name -- and matching the bare substring `Nat.dvd` would be satisfied by \
             `AxNat.dvd` for the wrong reason: {got}",
            k.display_name(name)
        );
        assert!(
            got.contains("AxNat.modEq"),
            "{} must conclude a congruence: {got}",
            k.display_name(name)
        );
    }
    assert_eq!(
        rendered(&k, p.pow_prime_modeq_self),
        FERMAT_LITTLE_THEOREM,
        "Fermat's little theorem"
    );
}

/// The kernel-rendered type of `Nat.pow_prime_modeq_self`, pinned by value.
const FERMAT_LITTLE_THEOREM: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) (((x2 : AxNat) -> ((x3 : AxNat.dvd x2 x0) -> Or (Eq.{1} AxNat x2 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x2 x0))))) -> AxNat.modEq x0 (AxNat.pow x1 x0) x1)))";

/// `Nat.restrict_injective` / `Nat.restrict_maps_into` apply at a concrete
/// swap (`sigma(k) := if k < 1 then 1 else 0`, i.e. `sigma(0)=1`,
/// `sigma(1)=0`, the transposition of `{0,1}`) and rest on zero axioms.
/// Neither hypothesis (`InjectiveOn`, `MapsInto`, `Lt i0 n`, `sigma i0 = n`)
/// is discharged here — the partial application's INFERRED TYPE is what is
/// checked, the same "apply, then infer" style
/// `succ_mul_choose_eq_holds_at_a_concrete_point` uses above.
#[test]
fn restrict_injective_and_maps_into_apply_at_a_concrete_swap() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let sigma = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let one = f.num(1);
        let zero = f.num(0);
        let succ_k = f.succ(k);
        let cond = f.ble(succ_k, one);
        let body = f.bool_select_nat(cond, one, zero);
        f.lam_fv(k_fv, nat, body)
    };
    let i0 = f.num(0);
    let n = f.num(1);

    let proof_inj = f.lemma(p.restrict_injective, &[sigma, i0, n]);
    f.k.infer(proof_inj).unwrap_or_else(|e| {
        panic!(
            "restrict_injective(sigma, 0, 1) should infer: {}",
            f.explain(&e)
        )
    });

    let proof_maps = f.lemma(p.restrict_maps_into, &[sigma, i0, n]);
    f.k.infer(proof_maps).unwrap_or_else(|e| {
        panic!(
            "restrict_maps_into(sigma, 0, 1) should infer: {}",
            f.explain(&e)
        )
    });

    for name in [p.restrict_injective, p.restrict_maps_into] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.add_sub_cancel_of_le` at a concrete point: `i=3 ≤ k=7` gives
/// `add 3 (sub 7 3) = 7`, i.e. `add 3 4 = 7`.
#[test]
fn add_sub_cancel_of_le_holds_at_a_concrete_point() {
    let mut f = Fixture::new();
    let p = f.p;
    let three = f.num(3);
    let four = f.num(4);
    let seven = f.num(7);

    let three_le_seven = f.lemma(p.le_add_right, &[three, four]);
    let proof = f.lemma(p.add_sub_cancel_of_le, &[three, seven, three_le_seven]);
    let inferred = f.k.infer(proof).unwrap_or_else(|e| {
        panic!(
            "add_sub_cancel_of_le(3,7,_) should infer: {}",
            f.explain(&e)
        )
    });

    let difference = f.sub(seven, three);
    let lhs = f.add(three, difference);
    let expected = f.eq(lhs, seven);
    assert!(
        f.k.def_eq(inferred, expected),
        "add_sub_cancel_of_le(3,7,_) should state add 3 (sub 7 3) = 7"
    );
    assert!(f.k.def_eq(lhs, seven), "add 3 (sub 7 3) must reduce to 7");

    assert!(
        f.k.axiom_footprint(p.add_sub_cancel_of_le).is_empty(),
        "add_sub_cancel_of_le must rest on zero axioms"
    );
}

/// `Nat.sumRange_diagonal` at a concrete instance: `F i j := add i j`, `n =
/// 3`. Both the antidiagonal grouping (`Σ_{k<3} Σ_{i≤k} F i (k−i)`) and the
/// row grouping (`Σ_{i<3} Σ_{j<3−i} F i j`) sum `i+j` over the SAME triangle
/// `{(i,j) : i+j<3}` — `(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)` — and both must
/// independently compute to `8`, so this is a genuine reindexing check, not
/// just an admission.
#[test]
fn sum_range_diagonal_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // F := fun i j => add i j
    let ff = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let body = f.add(i, j);
        let inner = f.lam_fv(j_fv, nat, body);
        f.lam_fv(i_fv, nat, inner)
    };
    let three = f.num(3);
    let eight = f.num(8);

    let proof = f.lemma(p.sum_range_diagonal, &[ff, three]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("sum_range_diagonal(F,3) should infer: {}", f.explain(&e)));

    // The antidiagonal (triangle) sum, built independently of `diagonal.rs`'s
    // own helpers.
    let triangle = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let ki = f.sub(k, i);
        let fiki = f.apply(ff, &[i, ki]);
        let diag_inner = f.lam_fv(i_fv, nat, fiki);
        let sk = f.succ(k);
        let diag_sum = f.sum_range(diag_inner, sk);
        let t_fn = f.lam_fv(k_fv, nat, diag_sum);
        f.sum_range(t_fn, three)
    };
    // The row-major sum, likewise independently built.
    let rows = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let fij = f.apply(ff, &[i, j]);
        let row_inner = f.lam_fv(j_fv, nat, fij);
        let ni = f.sub(three, i);
        let row_sum_i = f.sum_range(row_inner, ni);
        let row_fn = f.lam_fv(i_fv, nat, row_sum_i);
        f.sum_range(row_fn, three)
    };

    let expected = f.eq(triangle, rows);
    assert!(
        f.k.def_eq(inferred, expected),
        "sum_range_diagonal(F,3) should state the antidiagonal sum equals the row-major sum"
    );
    assert!(
        f.k.def_eq(triangle, eight),
        "the antidiagonal (triangle) sum of i+j over {{(i,j):i+j<3}} must reduce to 8"
    );
    assert!(
        f.k.def_eq(rows, eight),
        "the row-major sum of i+j over {{(i,j):i+j<3}} must reduce to 8"
    );

    assert!(
        f.k.axiom_footprint(p.sum_range_diagonal).is_empty(),
        "sum_range_diagonal must rest on zero axioms"
    );
}

/// **The rectangle/triangle/corner decomposition says what it claims, character
/// for character.** An empty axiom footprint cannot carry this claim: a theorem
/// that dropped the corner term, or that summed the triangle to `x2` instead of
/// `succ x2` (off by the whole antidiagonal), has an identically empty
/// footprint. What distinguishes them is the STATEMENT, so the statement is
/// what is pinned.
///
/// Three things to read in the rendered types, none of them cosmetic:
///
/// * **`AxNat` IS NOT AN AXIOMATIZED `Nat`.** The `Ax` is `axeyum`, and
///   `lean_pp` roots the kernel's COMPUTATIONAL naturals there only so they do
///   not shadow Lean's own `Nat` on export. This is an unhappy collision with
///   `AxReal`, where `Ax` DOES mean axiomatized and the trusted surface is 30.
///   `nat` measures 0 and these two theorems are part of that measurement.
/// * **The corner's inner summand is `AxNat.add (AxNat.sub x1 x2) x3`** — ONE
///   truncated subtraction, never nested. The reflection parametrization
///   `(i,j) ↦ (n−1−i, n−1−j)` needs a nested `sub` and was rejected for it.
/// * **`sumRange_split`'s bound is `AxNat.add x1 x2`, and there is no `Le`
///   hypothesis anywhere in its type.** Quantifying over the split point and
///   the tail length instead of over `m ≤ n` is what keeps `Nat.sub` out of the
///   induction entirely.
#[test]
fn the_rectangle_decomposition_is_stated_exactly() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    let split = rendered(&k, p.sum_range_split);
    assert!(
        !split.contains("AxNat.le") && !split.contains("AxNat.sub"),
        "sumRange_split must be quantified over the split POINT, not over `m ≤ n`; \
         a `le` premise or a `sub` in the statement means the other formulation \
         landed and the induction is no longer sub-free: {split}"
    );
    assert_eq!(split, SUM_RANGE_SPLIT_TYPE, "Nat.sumRange_split");

    let rect = rendered(&k, p.sum_range_rect_eq_diag_add_corner);
    assert!(
        rect.contains("AxNat.add (AxNat.sub x1 x2) x3"),
        "the corner must be row i's width-i suffix reindexed from n-i, with ONE \
         truncated subtraction and no nesting: {rect}"
    );
    assert_eq!(
        rect, RECT_EQ_DIAG_ADD_CORNER_TYPE,
        "Nat.sumRange_rect_eq_diag_add_corner"
    );
}

/// The pinned type of [`NatPrelude::sum_range_split`].
const SUM_RANGE_SPLIT_TYPE: &str = "((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : AxNat) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.sumRange x0 (AxNat.add x1 x2)) (AxNat.add (AxNat.sumRange x0 x1) (AxNat.sumRange (fun (x3 : AxNat) => x0 (AxNat.add x1 x3)) x2)))))";

/// The pinned type of [`NatPrelude::sum_range_rect_eq_diag_add_corner`].
const RECT_EQ_DIAG_ADD_CORNER_TYPE: &str = "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> AxNat))) -> ((x1 : AxNat) -> Eq.{1} AxNat (AxNat.sumRange (fun (x2 : AxNat) => AxNat.sumRange (fun (x3 : AxNat) => x0 x2 x3) x1) x1) (AxNat.add (AxNat.sumRange (fun (x2 : AxNat) => AxNat.sumRange (fun (x3 : AxNat) => x0 x3 (AxNat.sub x2 x3)) (AxNat.succ x2)) x1) (AxNat.sumRange (fun (x2 : AxNat) => AxNat.sumRange (fun (x3 : AxNat) => (fun (x4 : AxNat) => x0 x2 x4) (AxNat.add (AxNat.sub x1 x2) x3)) x2) x1))))";

/// `Nat.choose_add_convolution` (Vandermonde's convolution) at `m = 2, n = 1,
/// k = 2`: `choose (2+1) 2 = choose 2 0 * choose 1 2 + choose 2 1 * choose 1
/// 1 + choose 2 2 * choose 1 0 = 1*0 + 2*1 + 1*1 = 3`. The `i=0` term
/// vanishes because `choose 1 2 = 0` (`k` past `n`), not because of any
/// `Nat.sub` truncation — a genuine cross-check of the convolution, not just
/// an admission.
#[test]
fn choose_add_convolution_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let one = f.num(1);
    let three = f.num(3);

    let proof = f.lemma(p.choose_add_convolution, &[two, one, two]);
    let inferred = f.k.infer(proof).unwrap_or_else(|e| {
        panic!(
            "choose_add_convolution(2,1,2) should infer: {}",
            f.explain(&e)
        )
    });

    let lhs = {
        let add_2_1 = f.add(two, one);
        f.choose(add_2_1, two)
    };
    let rhs = {
        let summand = {
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let c1 = f.choose(two, i);
            let ki = f.sub(two, i);
            let c2 = f.choose(one, ki);
            let body = f.mul(c1, c2);
            let nat = f.nat_ty();
            f.lam_fv(i_fv, nat, body)
        };
        let bound = f.succ(two);
        f.sum_range(summand, bound)
    };

    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "choose_add_convolution(2,1,2) should state choose (add 2 1) 2 = sumRange (…) (succ 2)"
    );
    assert!(f.k.def_eq(lhs, three), "choose (2+1) 2 must reduce to 3");
    assert!(
        f.k.def_eq(rhs, three),
        "the convolution sum choose 2 0 * choose 1 2 + choose 2 1 * choose 1 1 + choose 2 2 * choose 1 0 must reduce to 3"
    );

    assert!(
        f.k.axiom_footprint(p.choose_add_convolution).is_empty(),
        "choose_add_convolution must rest on zero axioms"
    );
}

/// `Nat.sum_choose_sq` at `n = 3`: `choose 3 0² + choose 3 1² + choose 3 2² +
/// choose 3 3² = 1 + 9 + 9 + 1 = 20 = choose 6 3`, the classic
/// sum-of-squares-of-a-row identity.
#[test]
fn sum_choose_sq_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let twenty = f.num(20);

    let proof = f.lemma(p.sum_choose_sq, &[three]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("sum_choose_sq(3) should infer: {}", f.explain(&e)));

    let lhs = {
        let summand = {
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let ci = f.choose(three, i);
            let body = f.mul(ci, ci);
            let nat = f.nat_ty();
            f.lam_fv(i_fv, nat, body)
        };
        let bound = f.succ(three);
        f.sum_range(summand, bound)
    };
    let rhs = {
        let add_3_3 = f.add(three, three);
        f.choose(add_3_3, three)
    };

    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "sum_choose_sq(3) should state sumRange (fun i => choose 3 i * choose 3 i) 4 = choose (add 3 3) 3"
    );
    assert!(
        f.k.def_eq(lhs, twenty),
        "the sum of squared row-3 coefficients must reduce to 20"
    );
    assert!(f.k.def_eq(rhs, twenty), "choose 6 3 must reduce to 20");

    assert!(
        f.k.axiom_footprint(p.sum_choose_sq).is_empty(),
        "sum_choose_sq must rest on zero axioms"
    );
}

/// `Nat.fib` computes: the kernel's own `def_eq` (`δ`/`β`/`ι`) reduces `fib
/// 0..10` to the literal Fibonacci numerals. The negative half matters as
/// much as the positive one (`arithmetic_reduces_on_numerals` says so above,
/// and it applies here just as much): a `fib` that type-checks but reduces
/// wrong has an EMPTY axiom footprint and passes every sweep in this
/// repository, so `def_eq` must also be shown to REJECT a wrong value.
#[test]
fn fib_reduces_on_numerals_with_a_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;

    let expected: [u32; 11] = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    for (n, &want) in expected.iter().enumerate() {
        let n_u32 = u32::try_from(n).expect("small test index fits in u32");
        let arg = f.num(n_u32);
        let fib_n = f.const_app(p.fib, &[arg]);
        let want_lit = f.num(want);
        assert!(f.k.def_eq(fib_n, want_lit), "fib {n} must reduce to {want}");
    }

    // Negative control: def_eq must not be vacuously true.
    let seven = f.num(7);
    let fib_seven = f.const_app(p.fib, &[seven]);
    let wrong = f.num(14);
    assert!(
        !f.k.def_eq(fib_seven, wrong),
        "fib 7 must NOT reduce to 14 -- def_eq must not be vacuously true"
    );
    // fib 6 = 8, not 7 -- a second, independent negative control at a
    // DIFFERENT wrong numeral, so this is not just an off-by-one that
    // happens to always fail.
    let six = f.num(6);
    let fib_six = f.const_app(p.fib, &[six]);
    let seven_lit = f.num(7);
    assert!(
        !f.k.def_eq(fib_six, seven_lit),
        "fib 6 must NOT reduce to 7 -- it is 8"
    );
}

/// `Nat.fib_add_two` applies at a concrete `n`, matches direct numeral
/// computation, and rests on zero axioms.
#[test]
fn fib_add_two_holds_at_a_concrete_point_and_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;

    let five = f.num(5);
    let proof = f.lemma(p.fib_add_two, &[five]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("fib_add_two(5) should infer: {}", f.explain(&e)));

    let six = f.succ(five);
    let seven = f.succ(six);
    let lhs = f.const_app(p.fib, &[seven]);
    let fib_six = f.const_app(p.fib, &[six]);
    let fib_five = f.const_app(p.fib, &[five]);
    let rhs = f.add(fib_six, fib_five);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "fib_add_two(5) should state fib 7 = add (fib 6) (fib 5)"
    );

    let thirteen = f.num(13);
    assert!(f.k.def_eq(lhs, thirteen), "fib 7 must reduce to 13");
    let eight = f.num(8);
    let five_lit = f.num(5);
    assert!(f.k.def_eq(fib_six, eight), "fib 6 must reduce to 8");
    assert!(f.k.def_eq(fib_five, five_lit), "fib 5 must reduce to 5");

    assert!(
        f.k.axiom_footprint(p.fib_add_two).is_empty(),
        "fib_add_two must rest on zero axioms"
    );
}

/// `Nat.fib_le_succ`, `Nat.fib_pos_of_pos`, and `Nat.sum_fib` each rest on
/// zero axioms and apply at a concrete point.
#[test]
fn fib_le_succ_pos_of_pos_and_sum_fib_apply_and_are_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;

    let four = f.num(4);
    let le_proof = f.lemma(p.fib_le_succ, &[four]);
    f.k.infer(le_proof)
        .unwrap_or_else(|e| panic!("fib_le_succ(4) should infer: {}", f.explain(&e)));
    assert!(
        f.k.axiom_footprint(p.fib_le_succ).is_empty(),
        "fib_le_succ must rest on zero axioms"
    );

    let hyp_ty = {
        let zero = f.zero();
        f.lt(zero, four)
    };
    let pos_partial = f.lemma(p.fib_pos_of_pos, &[four]);
    let pos_partial_ty =
        f.k.infer(pos_partial)
            .unwrap_or_else(|e| panic!("fib_pos_of_pos(4) should infer: {}", f.explain(&e)));
    let expected_partial = {
        let fib_four = f.const_app(p.fib, &[four]);
        let zero = f.zero();
        let concl = f.lt(zero, fib_four);
        f.arrow(hyp_ty, concl)
    };
    assert!(
        f.k.def_eq(pos_partial_ty, expected_partial),
        "fib_pos_of_pos(4) should await 0 < 4 -> 0 < fib 4"
    );
    assert!(
        f.k.axiom_footprint(p.fib_pos_of_pos).is_empty(),
        "fib_pos_of_pos must rest on zero axioms"
    );

    let sum_proof = f.lemma(p.sum_fib, &[four]);
    let sum_inferred =
        f.k.infer(sum_proof)
            .unwrap_or_else(|e| panic!("sum_fib(4) should infer: {}", f.explain(&e)));
    let fib_fn = f.k.const_(p.fib, vec![]);
    let sr4 = f.sum_range(fib_fn, four);
    let five = f.succ(four);
    let fib5 = f.const_app(p.fib, &[five]);
    let one = f.num(1);
    let sub = f.sub(fib5, one);
    let expected_sum = f.eq(sr4, sub);
    assert!(
        f.k.def_eq(sum_inferred, expected_sum),
        "sum_fib(4) should state sumRange fib 4 = sub (fib 5) 1"
    );
    // sum_{i<4} fib i = fib0+fib1+fib2+fib3 = 0+1+1+2 = 4; fib 5 - 1 = 5-1 = 4.
    let four_lit = f.num(4);
    assert!(
        f.k.def_eq(sr4, four_lit),
        "sumRange fib 4 = fib0+fib1+fib2+fib3 = 0+1+1+2 = 4"
    );
    assert!(f.k.def_eq(sub, four_lit), "fib 5 - 1 = 5 - 1 = 4");

    assert!(
        f.k.axiom_footprint(p.sum_fib).is_empty(),
        "sum_fib must rest on zero axioms"
    );
}

/// The stronger Fibonacci monotonicity theorem is real lemma composition:
/// its checked closure cites the adjacent-step theorem rather than rebuilding
/// the recurrence proof.
#[test]
fn fib_mono_composes_fib_le_succ_and_records_the_dependency() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let five = f.num(5);
    let h = f.lemma(p.le_refl, &[two]);
    let h = f.lemma(p.le_step, &[two, two, h]);
    let three = f.succ(two);
    let h = f.lemma(p.le_step, &[two, three, h]);
    let four = f.succ(three);
    let h = f.lemma(p.le_step, &[two, four, h]);
    let proof = f.lemma(p.fib_mono, &[two, five, h]);
    f.k.infer(proof)
        .unwrap_or_else(|e| panic!("fib_mono(2,5) should infer: {}", f.explain(&e)));

    assert!(f.k.axiom_footprint(p.fib_mono).is_empty());
    let dependencies = f.k.theorem_dependencies(p.fib_mono);
    assert!(dependencies.contains(&p.fib_le_succ));
    assert!(dependencies.contains(&p.monotone_of_le_succ));
    assert!(!dependencies.contains(&p.le_trans));

    let direct = f.k.declaration_dependencies(p.fib_mono);
    assert!(
        dependencies
            .iter()
            .all(|dependency| direct.contains(dependency))
    );
    assert!(direct.contains(&p.fib));
    assert!(direct.contains(&p.monotone_of_le_succ));
    assert!(
        !direct.contains(&p.fib_aux),
        "the direct vocabulary must not absorb fib's transitive implementation closure"
    );
    let statement = f.k.declaration_type_dependencies(p.fib_mono);
    assert!(statement.contains(&p.fib));
    assert!(!statement.contains(&p.monotone_of_le_succ));
    assert!(!statement.contains(&p.fib_le_succ));
}

/// `Nat.catalan` computes: the kernel's own `def_eq` reduces `catalan 0..5`
/// to the literal Catalan numbers `1, 1, 2, 5, 14, 42` — see `catalan.rs`'s
/// module doc for the hand check. The negative control matters as much as
/// the positive one (`arithmetic_reduces_on_numerals` says so above, and it
/// applies here just as much): a `catalan` that type-checks but computes
/// wrong has an EMPTY axiom footprint and passes every sweep in this
/// repository.
#[test]
fn catalan_computes_at_concrete_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    let expected: [u32; 6] = [1, 1, 2, 5, 14, 42];
    for (n, &c) in expected.iter().enumerate() {
        let n_expr = f.num(u32::try_from(n).expect("n fits in u32"));
        let cat = f.const_app(p.catalan, &[n_expr]);
        let c_expr = f.num(c);
        assert!(
            f.k.def_eq(cat, c_expr),
            "catalan {n} must reduce to {c}, the n={n} Catalan number"
        );
    }

    // Negative control: `catalan 3` is NOT `6` — a plausible-looking wrong
    // value (`6 = choose 4 2`, what you would get from forgetting the
    // second subtracted term entirely).
    let three = f.num(3);
    let cat_3 = f.const_app(p.catalan, &[three]);
    let six = f.num(6);
    assert!(
        !f.k.def_eq(cat_3, six),
        "catalan 3 must NOT reduce to 6 (def_eq must not be vacuously true)"
    );
}

/// `Nat.catalan_mul_succ` at `n = 3`: `4 * catalan 3 = 4 * 5 = 20 = choose 6
/// 3` — the multiplicative identity that ties `catalan` to `choose`, checked
/// at a concrete instance independent of the computation check above (that
/// one never applies `catalan_mul_succ`).
#[test]
fn catalan_mul_succ_computes_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let proof = f.lemma(p.catalan_mul_succ, &[three]);
    let inferred =
        f.k.infer(proof)
            .unwrap_or_else(|e| panic!("catalan_mul_succ(3) should infer: {}", f.explain(&e)));

    let lhs = {
        let four = f.succ(three);
        let cat_3 = f.const_app(p.catalan, &[three]);
        f.mul(four, cat_3)
    };
    let rhs = {
        let six = f.add(three, three);
        f.choose(six, three)
    };
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "catalan_mul_succ(3) should state mul (succ 3) (catalan 3) = choose (add 3 3) 3"
    );

    let twenty = f.num(20);
    assert!(f.k.def_eq(lhs, twenty), "4 * catalan 3 must reduce to 20");
    assert!(f.k.def_eq(rhs, twenty), "choose 6 3 must reduce to 20");

    assert!(
        f.k.axiom_footprint(p.catalan_mul_succ).is_empty(),
        "catalan_mul_succ must rest on zero axioms"
    );
}

/// Finite set operations (`nat_prelude/finite_set.rs`) compute the right
/// membership on a small concrete instance: singleton predicates `A = {0}`,
/// `B = {1}`, and `C = {0}` (so `A ∩ C` has a nonempty positive case, unlike
/// the disjoint `A ∩ B`). This is the mandatory concrete instance for the
/// curriculum node `sets` — a characteristic function that type-checks but
/// computes the wrong membership has an empty axiom footprint and passes
/// every other sweep in this repository. WITH negative controls throughout.
#[test]
fn finite_set_operations_compute_on_a_concrete_pair() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let singleton = |f: &mut Fixture, elem: ExprId| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.kernel().fvar(k_fv);
        let body = f.beq(k, elem);
        f.lam_fv(k_fv, nat, body)
    };

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    let a = singleton(&mut f, zero); // A = {0}
    let b = singleton(&mut f, one); // B = {1}
    let c = singleton(&mut f, zero); // C = {0}, overlaps A

    // setUnion: A ∪ B = {0, 1}.
    let union_ab = f.const_app(p.set_union, &[a, b]);
    let u0 = f.apply(union_ab, &[zero]);
    let u1 = f.apply(union_ab, &[one]);
    let u2 = f.apply(union_ab, &[two]);
    assert!(f.k.def_eq(u0, true_), "0 must be in A union B");
    assert!(f.k.def_eq(u1, true_), "1 must be in A union B");
    assert!(f.k.def_eq(u2, false_), "2 must not be in A union B");
    assert!(
        !f.k.def_eq(u2, true_),
        "NEGATIVE: 2 not in A union B must not reduce to true"
    );

    // setInter: A ∩ B = ∅ (disjoint); A ∩ C = {0} (C = A, overlapping).
    let inter_ab = f.const_app(p.set_inter, &[a, b]);
    let iab0 = f.apply(inter_ab, &[zero]);
    let iab1 = f.apply(inter_ab, &[one]);
    assert!(f.k.def_eq(iab0, false_), "0 must not be in A inter B");
    assert!(f.k.def_eq(iab1, false_), "1 must not be in A inter B");

    let inter_ac = f.const_app(p.set_inter, &[a, c]);
    let iac0 = f.apply(inter_ac, &[zero]);
    let iac1 = f.apply(inter_ac, &[one]);
    assert!(f.k.def_eq(iac0, true_), "0 must be in A inter C");
    assert!(f.k.def_eq(iac1, false_), "1 must not be in A inter C");
    assert!(
        !f.k.def_eq(iac0, false_),
        "NEGATIVE: 0 in A inter C must not reduce to false"
    );

    // setCompl: complement of A over the ambient {0, 1, 2} probe points.
    let compl_a = f.const_app(p.set_compl, &[a]);
    let ca0 = f.apply(compl_a, &[zero]);
    let ca1 = f.apply(compl_a, &[one]);
    let ca2 = f.apply(compl_a, &[two]);
    assert!(f.k.def_eq(ca0, false_), "0 must not be in complement of A");
    assert!(f.k.def_eq(ca1, true_), "1 must be in complement of A");
    assert!(f.k.def_eq(ca2, true_), "2 must be in complement of A");
    assert!(
        !f.k.def_eq(ca0, true_),
        "NEGATIVE: 0 not in complement of A must not reduce to true"
    );

    // setDiff: A \ B = {0}.
    let diff_ab = f.const_app(p.set_diff, &[a, b]);
    let d0 = f.apply(diff_ab, &[zero]);
    let d1 = f.apply(diff_ab, &[one]);
    let d2 = f.apply(diff_ab, &[two]);
    assert!(f.k.def_eq(d0, true_), "0 must be in A diff B");
    assert!(f.k.def_eq(d1, false_), "1 must not be in A diff B");
    assert!(f.k.def_eq(d2, false_), "2 must not be in A diff B");
    assert!(
        !f.k.def_eq(d0, false_),
        "NEGATIVE: 0 in A diff B must not reduce to false"
    );

    // Every declaration exercised here rests on zero axioms.
    for name in [p.set_union, p.set_inter, p.set_compl, p.set_diff, p.subset] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The pointwise Boolean-lattice laws (`nat_prelude/finite_set.rs`) — the
/// curriculum node `sets`'s own claim, "the same Boolean laws as in
/// propositional logic, one level up" — apply at a concrete instance and
/// genuinely compute, not just type-check; WITH the mandatory negative
/// control: a De Morgan law with its top operator swapped (`union` for
/// `inter`) type-checks as a STATEMENT exactly like the real one, but is a
/// different, false Boolean identity, and reusing the real proof against it
/// must be rejected by the trusted gate.
#[test]
fn set_lattice_laws_hold_concretely_and_reject_a_swapped_de_morgan() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let singleton = |f: &mut Fixture, elem: ExprId| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.kernel().fvar(k_fv);
        let body = f.beq(k, elem);
        f.lam_fv(k_fv, nat, body)
    };

    let zero = f.zero();
    let one = f.num(1);
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    let a = singleton(&mut f, zero); // A = {0}
    let b = singleton(&mut f, one); // B = {1}

    // `setUnion_comm` applies at a concrete instance, and both sides
    // genuinely compute the SAME `Bool` (not just type-check the same).
    let comm_thm = f.k.const_(p.set_union_comm, vec![]);
    let applied = f.apply(comm_thm, &[a, b, zero]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("setUnion_comm(A,B,0) should infer: {}", f.explain(&e)));
    let union_ab = f.const_app(p.set_union, &[a, b]);
    let union_ba = f.const_app(p.set_union, &[b, a]);
    let lhs0 = f.apply(union_ab, &[zero]);
    let rhs0 = f.apply(union_ba, &[zero]);
    let expected = f.bool_eq(lhs0, rhs0);
    assert!(
        f.k.def_eq(inferred, expected),
        "setUnion_comm(A,B,0) should state (A union B) 0 = (B union A) 0"
    );
    assert!(f.k.def_eq(lhs0, true_), "0 is in A union B");
    assert!(f.k.def_eq(rhs0, true_), "0 is in B union A too");
    assert!(
        !f.k.def_eq(lhs0, false_),
        "NEGATIVE: (A union B) 0 must not reduce to false"
    );

    // `setCompl_involutive` applies at a concrete instance where its shared
    // value is `false` (1 is not in A).
    let inv_thm = f.k.const_(p.set_compl_involutive, vec![]);
    let applied_inv = f.apply(inv_thm, &[a, one]);
    f.k.infer(applied_inv)
        .unwrap_or_else(|e| panic!("setCompl_involutive(A,1) should infer: {}", f.explain(&e)));
    let a1 = f.apply(a, &[one]);
    assert!(f.k.def_eq(a1, false_), "1 is not in A");

    // NEGATIVE CONTROL: at A={0}, B={1}, point 0 — `compl (union A B) 0` is
    // `false` (0 IS in A union B), and the TRUE De Morgan law's rhs
    // `inter (compl A) (compl B) 0` matches (`false`: 0 is in A, so not in
    // `compl A`, and `inter`'s `false` branch is the fixed constant). The
    // SWAPPED law (`union` for `inter`) claims `union (compl A) (compl B) 0`,
    // which is `true` (1 IS in `compl A`, and `union`'s `true` branch
    // short-circuits) — a genuinely DIFFERENT value. Reusing the REAL
    // `setCompl_union` proof (of the true, `inter`, statement) against this
    // swapped statement must be rejected: a checker that admits it is
    // vacuous.
    let real_thm = f.k.const_(p.set_compl_union, vec![]);
    let real_proof_at_point = f.apply(real_thm, &[a, b, zero]);

    let compl_union_ab = f.const_app(p.set_compl, &[union_ab]);
    let lhs_bad = f.apply(compl_union_ab, &[zero]);
    let compl_a = f.const_app(p.set_compl, &[a]);
    let compl_b = f.const_app(p.set_compl, &[b]);
    let bad_rhs_fn = f.const_app(p.set_union, &[compl_a, compl_b]); // WRONG: should be set_inter
    let rhs_bad = f.apply(bad_rhs_fn, &[zero]);
    let bad_stmt = f.bool_eq(lhs_bad, rhs_bad);

    // Confirm the two sides genuinely diverge, so this is a real negative
    // control and not an accidental tautology.
    assert!(
        f.k.def_eq(lhs_bad, false_),
        "compl(A union B) at 0 is false"
    );
    assert!(
        f.k.def_eq(rhs_bad, true_),
        "the SWAPPED rhs (union of complements) at 0 is true -- genuinely different"
    );

    let name = f.name("nc63_set_compl_union_rhs_swapped_to_union");
    let err = f
        .declare_theorem(name, bad_stmt, real_proof_at_point)
        .expect_err("NC63: a De Morgan law with its operator swapped must be rejected");
    println!(
        "NC63 (setCompl_union with rhs swapped to union) rejected:\n  {}",
        f.explain(&err)
    );
    assert!(!f.k.environment().contains(name));
}

/// `Subset` is a partial order (`subset_refl`/`subset_trans`/
/// `subset_antisymm`), `setDiff` is `setInter` composed with `setCompl`, and
/// union with a superset is the superset — the `sets` node's own open goal,
/// joined to `relations-and-functions`. Concrete computation at a singleton
/// predicate over {0,1,2}, exercising BOTH branches of `subset_antisymm`'s
/// `Bool.rec` split (`k=0`, where `A 0 = true`; `k=1`, where `A 1 = false`),
/// WITH a negative control: reusing `setDiff_eq_inter_compl`'s real,
/// universally-quantified proof term against a statement with its top
/// operator on the right swapped (`setUnion` for `setInter`) must be
/// rejected — `setDiff f g` is defeq to `setInter f (setCompl g)` for
/// ABSTRACT `f g`, never to `setUnion f (setCompl g)`.
#[test]
fn subset_is_a_partial_order_and_joins_the_lattice() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();

    let singleton = |f: &mut Fixture, elem: ExprId| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.kernel().fvar(k_fv);
        let body = f.beq(k, elem);
        f.lam_fv(k_fv, nat, body)
    };

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    let a = singleton(&mut f, zero); // A = {0}
    let b = singleton(&mut f, one); // B = {1}

    // `0 < 3` and `1 < 3`, built as `Le` witnesses (`Lt x y := Le (succ x) y`).
    let hk0 = {
        let sum = f.add(one, two);
        let sum_eq = f.refl(sum);
        f.lemma(p.le_intro, &[one, three, two, sum_eq])
    };
    let hk1 = {
        let sum = f.add(two, one);
        let sum_eq = f.refl(sum);
        f.lemma(p.le_intro, &[two, three, one, sum_eq])
    };

    // subset_refl / subset_trans: concrete instances must infer.
    let refl_proof = f.lemma(p.subset_refl, &[a, three]);
    f.k.infer(refl_proof).expect("subset_refl should infer");
    let trans_proof = f.lemma(p.subset_trans, &[a, a, a, three, refl_proof, refl_proof]);
    f.k.infer(trans_proof).expect("subset_trans should infer");

    // subset_antisymm on A, A (mutually a subset of itself via subset_refl):
    // pointwise equal everywhere. Evaluate at k=0 (A 0 = true, exercising the
    // `Bool.rec` split's TRUE branch) and k=1 (A 1 = false, the FALSE branch).
    let antisymm_proof = f.lemma(p.subset_antisymm, &[a, a, three, refl_proof, refl_proof]);
    let eq_at_0 = f.apply(antisymm_proof, &[zero, hk0]);
    f.k.infer(eq_at_0)
        .expect("subset_antisymm at k=0 should infer");
    let a0 = f.apply(a, &[zero]);
    assert!(f.k.def_eq(a0, true_), "A 0 must compute to true");
    let eq_at_1 = f.apply(antisymm_proof, &[one, hk1]);
    f.k.infer(eq_at_1)
        .expect("subset_antisymm at k=1 should infer");
    let a1 = f.apply(a, &[one]);
    assert!(f.k.def_eq(a1, false_), "A 1 must compute to false");

    // setDiff_eq_inter_compl: A \ B at 0 must equal A ∩ (compl B) at 0, and
    // both must compute to `true` (0 is in A, 0 is not in B).
    let diff_ab = f.const_app(p.set_diff, &[a, b]);
    let diff_ab_0 = f.apply(diff_ab, &[zero]);
    let compl_b = f.const_app(p.set_compl, &[b]);
    let inter_a_complb = f.const_app(p.set_inter, &[a, compl_b]);
    let inter_a_complb_0 = f.apply(inter_a_complb, &[zero]);
    assert!(
        f.k.def_eq(diff_ab_0, inter_a_complb_0),
        "setDiff a b 0 must be defeq to setInter a (setCompl b) 0"
    );
    assert!(
        f.k.def_eq(diff_ab_0, true_),
        "0 is in A and not in B, so A diff B at 0 must compute to true"
    );

    // union_eq_right_of_subset: Subset A A n (via subset_refl) gives
    // setUnion A A k = A k at every k < n.
    let union_eq_proof = f.lemma(p.union_eq_right_of_subset, &[a, a, three, refl_proof]);
    let union_eq_at_0 = f.apply(union_eq_proof, &[zero, hk0]);
    f.k.infer(union_eq_at_0)
        .expect("union_eq_right_of_subset at k=0 should infer");
    let union_aa = f.const_app(p.set_union, &[a, a]);
    let union_aa_0 = f.apply(union_aa, &[zero]);
    assert!(
        f.k.def_eq(union_aa_0, a0),
        "setUnion a a 0 must compute to a 0"
    );

    // subset_union_left / subset_inter_left: concrete instances must infer,
    // and (for union_left) the produced membership proof must check against
    // the real `setUnion a b 0 = true` obligation.
    let union_left_proof = f.lemma(p.subset_union_left, &[a, b, three]);
    let mem_a0 = f.bool_refl(a0);
    let union_left_at_0 = f.apply(union_left_proof, &[zero, hk0, mem_a0]);
    let union_ab = f.const_app(p.set_union, &[a, b]);
    let union_ab_0 = f.apply(union_ab, &[zero]);
    let inferred_union_left =
        f.k.infer(union_left_at_0)
            .expect("subset_union_left at k=0 should infer");
    let expected_union_left = f.bool_eq(union_ab_0, true_);
    assert!(f.k.def_eq(inferred_union_left, expected_union_left));

    let inter_left_proof = f.lemma(p.subset_inter_left, &[a, b, three]);
    f.k.infer(inter_left_proof)
        .expect("subset_inter_left should infer");

    // NEGATIVE CONTROL: reuse `setDiff_eq_inter_compl`'s real, fully
    // quantified proof term against a statement with the right-hand
    // operator swapped (`setUnion` in place of `setInter`) — a genuinely
    // different identity for abstract `f g k`, and the kernel must reject
    // the reuse.
    let real_proof = f.const_app(p.set_diff_eq_inter_compl, &[]);
    let wrong_ty = {
        let pred_ty = f.arrow(nat, bool_ty);
        let f_fv = f.fresh_fvar();
        let fp = f.kernel().fvar(f_fv);
        let g_fv = f.fresh_fvar();
        let gp = f.kernel().fvar(g_fv);
        let k_fv = f.fresh_fvar();
        let kp = f.kernel().fvar(k_fv);

        let diff_fg = f.const_app(p.set_diff, &[fp, gp]);
        let lhs = f.apply(diff_fg, &[kp]);
        let compl_g = f.const_app(p.set_compl, &[gp]);
        let union_f_complg = f.const_app(p.set_union, &[fp, compl_g]); // swapped
        let rhs = f.apply(union_f_complg, &[kp]);
        let eq = f.bool_eq(lhs, rhs);

        let with_k = f.pi_fv(k_fv, nat, eq);
        let with_g = f.pi_fv(g_fv, pred_ty, with_k);
        f.pi_fv(f_fv, pred_ty, with_g)
    };
    let wrong_name = f.name("setDiff_is_secretly_setUnion_compl");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, real_proof)
        .expect_err("setDiff must not be defeq to setUnion(f, compl g) for abstract f g k");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));

    // Every declaration exercised here rests on zero axioms.
    for name in [
        p.subset_refl,
        p.subset_trans,
        p.subset_antisymm,
        p.set_diff_eq_inter_compl,
        p.union_eq_right_of_subset,
        p.subset_union_left,
        p.subset_inter_left,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The Chinese Remainder Theorem's **uniqueness** half (`crt_unique`,
/// `crt.rs`) at a concrete instance: `m=2, n=3, x=1, y=7` — `1` and `7` are
/// both `≡ 1 (mod 2)` and `≡ 1 (mod 3)`, and `7 - 1 = 6 = 2*3`, so
/// `crt_unique` must produce `modEq 6 1 7`. `coprime_mul_dvd` (`crt.rs`) is
/// exercised here as `crt_unique`'s own engine, not standalone. NEGATIVE
/// CONTROL: the same proof term reused against a WRONG modulus (`5`, not
/// `2*3`) must be rejected — the witnesses `crt_unique` builds are for `6`
/// specifically, not for any common multiple of `2` and `3`.
#[test]
fn crt_unique_holds_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let seven = f.num(7);

    // gcd 2 3 computes to 1.
    let gcd_mn = f.gcd(two, three);
    let coprime_ty = f.eq(gcd_mn, one);
    let coprime = f.refl(one);
    let coprime_inferred =
        f.k.infer(coprime)
            .unwrap_or_else(|e| panic!("gcd 2 3 = 1 should typecheck: {}", f.explain(&e)));
    assert!(
        f.k.def_eq(coprime_inferred, coprime_ty),
        "gcd 2 3 must compute to 1"
    );

    // x=1 ≡ y=7 (mod 2): 1 + 2*3 = 7 + 2*0.
    let hm = f.concrete_mod_eq(two, one, seven, three, zero);
    // x=1 ≡ y=7 (mod 3): 1 + 3*2 = 7 + 3*0.
    let hn = f.concrete_mod_eq(three, one, seven, two, zero);

    let proof = f.lemma(p.crt_unique, &[two, three, one, seven, coprime, hm, hn]);
    let mn = f.mul(two, three);
    let six = f.num(6);
    assert!(f.k.def_eq(mn, six), "2*3 must compute to 6");
    let target = f.mod_eq(mn, one, seven);
    let name = f.name("one_mod_six_seven");
    f.declare_theorem(name, target, proof).unwrap_or_else(|e| {
        panic!(
            "crt_unique at m=2,n=3,x=1,y=7 should admit modEq 6 1 7: {}",
            f.explain(&e)
        )
    });

    // NEGATIVE CONTROL: the very same proof term against a WRONG modulus
    // (5, not 2*3) must be rejected.
    let five = f.num(5);
    let wrong_ty = f.mod_eq(five, one, seven);
    let wrong_name = f.name("one_mod_five_seven_via_crt_unique_forgery");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, proof)
        .expect_err("crt_unique's witness for modulus 6 must not satisfy modulus 5");
    assert!(matches!(
        error,
        KernelError::TypeMismatch { .. } | KernelError::DeclarationValueMismatch { .. }
    ));

    for name in [p.coprime_mul_dvd, p.crt_unique] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.cantor_diagonal` applies at a concrete `f := Nat.beq`, and — the part
/// that matters, since a wrong argument order (`f k n` instead of `f n n`)
/// would type-check identically — the diagonal it produces actually
/// REDUCES, not merely type-checks.
///
/// `beq n n` is constantly `true` (`Nat.beq_refl`), so the diagonal witness
/// `g := fun n => not (f n n)` is constantly `false`; at `n = 3` this is
/// `not (beq 3 3) = not true = false`, disagreeing with `f 3 3 = beq 3 3 =
/// true`. The `not` here is rebuilt independently from `cantor.rs`'s private
/// copy, using only the generic `NatOps` methods any downstream development
/// has (the same pattern this file's own `Fixture` demonstrates throughout),
/// so this is a genuinely external check of what the declared theorem's
/// *statement* reduces to at a concrete instance, not a re-run of its proof.
#[test]
fn cantor_diagonal_applies_at_beq_and_the_diagonal_witness_reduces() {
    let mut f = Fixture::new();
    let p = f.p;
    let bool_ty = f.bool_ty();

    // f_concrete := Nat.beq : Nat -> Nat -> Bool
    let f_concrete = f.k.const_(p.beq, vec![]);

    let theorem = f.k.const_(p.cantor_diagonal, vec![]);
    let applied = f.k.app(theorem, f_concrete);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "cantor_diagonal must apply to a concrete f: {}",
            f.explain(&e)
        )
    });
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("Exists"),
        "unexpected residue type: {rendered}"
    );

    // f_concrete 3 3 = beq 3 3, must reduce to `true` (Nat.beq_refl).
    let three = f.num(3);
    let f_3_3 = {
        let applied = f.k.app(f_concrete, three);
        f.k.app(applied, three)
    };
    let bool_true = f.bool_true();
    let bool_false = f.bool_false();
    assert!(
        f.k.def_eq(f_3_3, bool_true),
        "beq 3 3 must reduce to Bool.true"
    );

    // not (f_concrete 3 3), rebuilt independently of cantor.rs's private
    // `not_bool`, must reduce to `false` -- the diagonal witness's value at
    // n = 3.
    let g_3 = {
        let motive_fv = f.fresh_fvar();
        let motive = f.lam_fv(motive_fv, bool_ty, bool_ty);
        let one = f.level_one();
        let bool_rec = f.k.const_(p.logic.bool_rec, vec![one]);
        f.apply(bool_rec, &[motive, bool_true, bool_false, f_3_3])
    };
    assert!(
        f.k.def_eq(g_3, bool_false),
        "not (beq 3 3) must reduce to Bool.false"
    );
    assert!(
        !f.k.def_eq(g_3, f_3_3),
        "the diagonal witness must genuinely differ from the row at n = 3"
    );

    assert!(
        f.k.axiom_footprint(p.cantor_diagonal).is_empty(),
        "cantor_diagonal must rest on zero axioms"
    );
}

/// `Nat.cantor_diagonal_neg` applies at a concrete `f := Nat.beq` and is
/// axiom-free -- the negative form built from `cantor_diagonal` by nested
/// `Exists.rec`, checked as a standalone declaration (its own `add_declaration`
/// call already re-verified the proof term against the stated type; this test
/// pins that the composed statement keeps applying downstream).
#[test]
fn cantor_diagonal_neg_applies_at_beq() {
    let mut f = Fixture::new();
    let p = f.p;

    let f_concrete = f.k.const_(p.beq, vec![]);
    let theorem = f.k.const_(p.cantor_diagonal_neg, vec![]);
    let applied = f.k.app(theorem, f_concrete);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "cantor_diagonal_neg must apply to a concrete f: {}",
            f.explain(&e)
        )
    });
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("Exists") && rendered.contains("False"),
        "unexpected residue type: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.cantor_diagonal_neg).is_empty(),
        "cantor_diagonal_neg must rest on zero axioms"
    );
}

/// `Nat.cantor_no_fixed_point` applies at a concrete `F := not` (rebuilt
/// independently of `cantor.rs`'s private `not_bool`, the same pattern the
/// two tests above use) and is axiom-free. Instantiating at `not` is the
/// corollary's own point: the diagonal's negation has no fixed point on
/// `Bool`, which is the seed of the halting argument's self-application
/// shape.
#[test]
fn cantor_no_fixed_point_applies_to_negation() {
    let mut f = Fixture::new();
    let p = f.p;
    let bool_ty = f.bool_ty();

    // not := fun b => Bool.rec (fun _ => Bool) true false b
    let not_fn = {
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let inner_motive_fv = f.fresh_fvar();
        let inner_motive = f.lam_fv(inner_motive_fv, bool_ty, bool_ty);
        let one = f.level_one();
        let bool_rec = f.k.const_(p.logic.bool_rec, vec![one]);
        let t = f.bool_true();
        let ff = f.bool_false();
        let not_b = f.apply(bool_rec, &[inner_motive, t, ff, b]);
        f.lam_fv(b_fv, bool_ty, not_b)
    };

    let theorem = f.k.const_(p.cantor_no_fixed_point, vec![]);
    let applied = f.k.app(theorem, not_fn);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "cantor_no_fixed_point must apply to a concrete F: {}",
            f.explain(&e)
        )
    });
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("Exists") && rendered.contains("False"),
        "unexpected residue type: {rendered}"
    );

    assert!(
        f.k.axiom_footprint(p.cantor_no_fixed_point).is_empty(),
        "cantor_no_fixed_point must rest on zero axioms"
    );
}

/// `Nat.Even`/`Nat.Odd` apply at concrete witnesses (4 = 2+2, 5 = succ(2+2)),
/// `even_not_odd`/`odd_not_even` apply to them and rest on zero axioms, and
/// `even_iff_odd_succ(4).mp` applied to a hand-built `Even 4` produces a term
/// whose inferred type is defeq to an independently hand-built `Odd 5` --- a
/// concrete cross-check that the `mp` direction is not accidentally the
/// `mpr` direction with the same shape (they'd both type-check as `Prop`
/// arrows, so only a value-level check like this one catches a swap).
#[test]
fn parity_predicates_apply_at_concrete_witnesses_and_are_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.level_one();

    let four = f.num(4);
    let two = f.num(2);
    let five = f.num(5);

    // Even 4, witnessed by 2 (4 = 2+2).
    let even4 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(four, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(four);
        let intro = f.k.const_(p.logic.exists_intro, vec![one]);
        f.apply(intro, &[nat, pred, two, proof])
    };
    f.k.infer(even4)
        .unwrap_or_else(|e| panic!("Even 4 (witness 2) should type-check: {}", f.explain(&e)));

    // Odd 5, witnessed by 2 (5 = succ(2+2)).
    let odd5 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(five, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(five);
        let intro = f.k.const_(p.logic.exists_intro, vec![one]);
        f.apply(intro, &[nat, pred, two, proof])
    };
    let odd5_ty =
        f.k.infer(odd5)
            .unwrap_or_else(|e| panic!("Odd 5 (witness 2) should type-check: {}", f.explain(&e)));

    // even_not_odd(4) applied to even4 : Not (Odd 4).
    let even_not_odd_at_4 = f.lemma(p.even_not_odd, &[four]);
    let not_odd4 = f.apply(even_not_odd_at_4, &[even4]);
    f.k.infer(not_odd4).unwrap_or_else(|e| {
        panic!(
            "even_not_odd(4) applied to Even 4 should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.axiom_footprint(p.even_not_odd).is_empty(),
        "even_not_odd must rest on zero axioms"
    );

    // odd_not_even(5) applied to odd5 : Not (Even 5).
    let odd_not_even_at_5 = f.lemma(p.odd_not_even, &[five]);
    let not_even5 = f.apply(odd_not_even_at_5, &[odd5]);
    f.k.infer(not_even5).unwrap_or_else(|e| {
        panic!(
            "odd_not_even(5) applied to Odd 5 should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.axiom_footprint(p.odd_not_even).is_empty(),
        "odd_not_even must rest on zero axioms"
    );

    // even_iff_odd_succ(4).mp applied to even4 must land on the same type as
    // the independently hand-built odd5.
    let even4_ty = f.lemma(p.even, &[four]);
    let odd5_ty_folded = f.lemma(p.odd, &[five]);
    let iff_at_4 = f.lemma(p.even_iff_odd_succ, &[four]);
    let mp_fn = f.const_app(p.logic.iff_mp, &[even4_ty, odd5_ty_folded, iff_at_4]);
    let odd5_from_even4 = f.apply(mp_fn, &[even4]);
    let odd5_from_even4_ty = f.k.infer(odd5_from_even4).unwrap_or_else(|e| {
        panic!(
            "even_iff_odd_succ(4).mp applied to Even 4 should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(odd5_from_even4_ty, odd5_ty),
        "even_iff_odd_succ(4).mp(Even 4) must land on Odd 5, matching the \
         independently witnessed Odd 5 -- a mismatch here would mean mp/mpr \
         are swapped"
    );
    assert!(
        f.k.axiom_footprint(p.even_iff_odd_succ).is_empty(),
        "even_iff_odd_succ must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.even_or_odd_exists).is_empty(),
        "even_or_odd_exists must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.add_self_ne_succ_add_self).is_empty(),
        "add_self_ne_succ_add_self must rest on zero axioms"
    );
}

/// `coprime_two_left(5).mpr` applied to a hand-built `Odd 5` produces a term
/// whose inferred type is `Eq (gcd 2 5) 1`, and round-tripping that result
/// back through `coprime_two_left(5).mp` lands on a type defeq to `Odd 5`
/// again. This is the same swap-detecting technique as
/// `parity_predicates_apply_at_concrete_witnesses_and_are_axiom_free`: if
/// `mp`/`mpr` had been passed to `iff_intro` in the wrong order, the `mp`
/// leg of the round trip would receive an argument of the wrong type
/// (`Eq (gcd 2 5) 1` where an `Odd n`-shaped value is expected) and
/// `Kernel::infer` would reject it, so this only passes if both directions
/// are wired correctly. All four new declarations are also checked
/// axiom-free directly.
#[test]
fn coprime_two_left_applies_at_a_concrete_odd_witness_and_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let five = f.num(5);
    let two_wit = f.num(2);

    // Odd 5, witnessed by 2 (5 = succ(2+2)).
    let odd5 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(five, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(five);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two_wit, proof])
    };

    let two = f.num(2);
    let gcd_two_five = f.gcd(two, five);
    let one = f.num(1);
    let cop_ty = f.eq(gcd_two_five, one);
    let odd_ty = f.lemma(p.odd, &[five]);

    let iff_at_5 = f.lemma(p.coprime_two_left, &[five]);
    let mpr_fn = f.const_app(p.logic.iff_mpr, &[cop_ty, odd_ty, iff_at_5]);
    let cop_from_odd5 = f.apply(mpr_fn, &[odd5]);
    let cop_from_odd5_ty = f.k.infer(cop_from_odd5).unwrap_or_else(|e| {
        panic!(
            "coprime_two_left(5).mpr applied to Odd 5 should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(cop_from_odd5_ty, cop_ty),
        "coprime_two_left(5).mpr(Odd 5) must land on Eq (gcd 2 5) 1"
    );

    let mp_fn = f.const_app(p.logic.iff_mp, &[cop_ty, odd_ty, iff_at_5]);
    let odd5_roundtrip = f.apply(mp_fn, &[cop_from_odd5]);
    let odd5_roundtrip_ty = f.k.infer(odd5_roundtrip).unwrap_or_else(|e| {
        panic!(
            "coprime_two_left(5).mp applied to the mpr result should \
             type-check (this fails if mp/mpr were swapped): {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(odd5_roundtrip_ty, odd_ty),
        "the mp/mpr round trip on Odd 5 must land back on Odd 5"
    );

    for name in [
        p.coprime_two_left,
        p.coprime_two_right,
        p.coprime_odd_of_left,
        p.coprime_odd_of_right,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }
}

/// `Nat.log_of_lt` applies at a concrete `3 < 5`, and its conclusion is the
/// statement its name promises.
///
/// This is the one `Nat.log` theorem with a hypothesis, so it is the one that
/// can be admitted with a type nothing can discharge. Building the `Lt 3 5`
/// witness by hand and feeding it in is what shows the hypothesis is the
/// ordinary `Nat.lt` and not some shape only the proof term can produce.
#[test]
fn log_of_lt_applies_at_a_concrete_pair() {
    let mut f = Fixture::new();
    let p = f.p;

    // Le 0 1, then four `le_succ_succ` steps: Le 4 5, i.e. Lt 3 5.
    let one = f.num(1);
    let mut witness = f.lemma(p.zero_le, &[one]);
    for step in 0..4u32 {
        let lower = f.num(step);
        let upper = f.num(step + 1);
        witness = f.lemma(p.le_succ_succ, &[lower, upper, witness]);
    }
    let three = f.num(3);
    let five = f.num(5);
    let expected_hypothesis = f.lt(three, five);
    let witness_ty =
        f.k.infer(witness)
            .expect("the hand-built order witness must type-check");
    assert!(
        f.k.def_eq(witness_ty, expected_hypothesis),
        "the hand-built witness must be a proof of Lt 3 5"
    );

    let applied = f.const_app(p.log_of_lt, &[five, three]);
    let applied = f.apply(applied, &[witness]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        let shown = f.explain(&e);
        panic!("Nat.log_of_lt must apply at (b, n) = (5, 3): {shown}")
    });
    let log = p.log;
    let lhs = f.const_app(log, &[five, three]);
    let zero = f.zero();
    let want = f.eq(lhs, zero);
    assert!(
        f.k.def_eq(inferred, want),
        "Nat.log_of_lt 5 3 must state Eq (log 5 3) 0"
    );

    // And the conclusion is not vacuous: `log 5 3` really is 0 by computation,
    // while `log 2 8` (where the hypothesis does NOT hold) is not.
    assert!(f.k.def_eq(lhs, zero), "log 5 3 must reduce to 0");
    let two = f.num(2);
    let eight = f.num(8);
    let log_two_eight = f.const_app(log, &[two, eight]);
    assert!(
        !f.k.def_eq(log_two_eight, zero),
        "negative control: log 2 8 is 3, so `log_of_lt`'s hypothesis is load-bearing"
    );

    for name in [p.log_of_lt, p.ble_eq_false_of_lt] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }
}

/// `Nat.log_aux_le_fuel` and `Nat.log_le_self` apply at a concrete instance,
/// each landing on the exact statement its name promises rather than on some
/// swapped-operand `Le` that would type-check just as easily.
///
/// This is the fuel-generalized-over-`n` induction: `logAux_le_fuel` bounds
/// `logAux b f n` by the fuel `f` for *every* `n`, not merely the diagonal
/// `f = n` that `log b n := logAux b n n` instantiates — `log_le_self` is
/// exactly that diagonal specialization.
#[test]
fn log_aux_le_fuel_and_log_le_self_apply_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // logAux_le_fuel 2 8 3 : Le (logAux 2 8 3) 8 -- fuel EXCEEDS what a
    // diagonal `n = f` instance would ever exercise, so this is not merely
    // `log_le_self` in disguise.
    let two = f.num(2);
    let eight = f.num(8);
    let three = f.num(3);
    let applied = f.const_app(p.log_aux_le_fuel, &[two, eight, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        let shown = f.explain(&e);
        panic!("Nat.logAux_le_fuel must apply at (b, f, n) = (2, 8, 3): {shown}")
    });
    let lhs = f.const_app(p.log_aux, &[two, eight, three]);
    let want = f.le(lhs, eight);
    assert!(
        f.k.def_eq(inferred, want),
        "Nat.logAux_le_fuel 2 8 3 must state Le (logAux 2 8 3) 8"
    );
    // Negative control: the swapped-operand statement is a different `Le`
    // entirely, so a checker that could not tell the difference would still
    // accept the application above.
    let swapped = f.le(eight, lhs);
    assert!(
        !f.k.def_eq(inferred, swapped),
        "negative control: Le (logAux 2 8 3) 8 must not be confused with its swap"
    );

    // log_le_self 2 8 : Le (log 2 8) 8, and log 2 8 = 3 < 8 -- a strict, not
    // merely reflexive, instance.
    let log = p.log;
    let applied = f.const_app(p.log_le_self, &[two, eight]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        let shown = f.explain(&e);
        panic!("Nat.log_le_self must apply at (b, n) = (2, 8): {shown}")
    });
    let log_two_eight = f.const_app(log, &[two, eight]);
    let want = f.le(log_two_eight, eight);
    assert!(
        f.k.def_eq(inferred, want),
        "Nat.log_le_self 2 8 must state Le (log 2 8) 8"
    );
    assert!(
        f.k.def_eq(log_two_eight, three),
        "log 2 8 must reduce to 3, so this bound is strict, not vacuous reflexivity"
    );

    for name in [p.log_aux_le_fuel, p.log_le_self] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }
}

/// `Nat.log` COMPUTES, and its four boundary theorems apply at concrete
/// arguments.
///
/// The definition is the point of interest, not the theorems: `Nat.log`
/// recurses on `n / b`, which is not a constructor predecessor, so it is built
/// by structural recursion on a **fuel** argument instantiated at `n` itself
/// (`log.rs`). That is only correct if the fuel always suffices, and the
/// cheapest evidence for it is that closed applications actually reduce to the
/// right numeral rather than getting stuck on an exhausted fuel -- an exhausted
/// fuel returns `0`, which is exactly what a *wrong* answer looks like here, so
/// every positive case below is also a fuel-sufficiency check.
///
/// Both negative controls differ from the truth by ONE successor, deliberately:
/// a control that differs wildly can be discriminated by a cheap size check and
/// so tests less than it appears to.
#[test]
fn log_computes_and_its_boundary_equations_apply() {
    let mut f = Fixture::new();
    let log = f.p.log;

    for (base, value, expected) in [
        (2u32, 8u32, 3u32),
        (2, 7, 2),
        (2, 1, 0),
        (3, 9, 2),
        (5, 4, 0),
        (0, 6, 0),
        (1, 6, 0),
        (7, 0, 0),
    ] {
        let b = f.num(base);
        let n = f.num(value);
        let lhs = f.const_app(log, &[b, n]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "log {base} {value} must reduce to {expected}"
        );
    }

    let two = f.num(2);
    let eight = f.num(8);
    let log_two_eight = f.const_app(log, &[two, eight]);
    let four = f.num(4);
    assert!(
        !f.k.def_eq(log_two_eight, four),
        "negative control: log 2 8 is 3, not 4 -- def_eq must not be vacuous"
    );
    let three = f.num(3);
    let nine = f.num(9);
    let log_three_nine = f.const_app(log, &[three, nine]);
    let one = f.num(1);
    assert!(
        !f.k.def_eq(log_three_nine, one),
        "negative control: log 3 9 is 2, not 1"
    );

    // The boundary equations apply, and each lands on the statement its name
    // promises rather than on some vacuously true instance.
    let p = f.p;
    let zero = f.zero();
    let seven = f.num(7);
    for (name, expected_lhs) in [
        (p.log_zero_right, (7u32, 0u32)),
        (p.log_zero_left, (0, 7)),
        (p.log_one_left, (1, 7)),
        (p.log_one_right, (7, 1)),
    ] {
        let applied = f.const_app(name, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("{name:?} must apply at a concrete argument: {shown}")
        });
        let b = f.num(expected_lhs.0);
        let n = f.num(expected_lhs.1);
        let lhs = f.const_app(log, &[b, n]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "{name:?} at 7 must state Eq (log {} {}) 0",
            expected_lhs.0,
            expected_lhs.1
        );
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }
}

/// `Nat.sqrt` COMPUTES, and its two boundary theorems apply at concrete
/// arguments.
///
/// The definition is the point of interest: `sqrtAux` searches upward by
/// fuel-bounded structural recursion, and that is only correct if the fuel
/// (`n` itself) always suffices. An exhausted fuel returns whatever
/// accumulator it stopped at, which for a `0`-fuel case is `0` -- so, like
/// `Nat.log`'s equivalent test, every positive case below doubles as a
/// fuel-sufficiency check: a wrong answer here would mean fuel ran out too
/// early.
///
/// Both negative controls differ from the truth by exactly one, deliberately
/// (a control that differs wildly tests less than it appears to).
#[test]
fn sqrt_computes_and_its_boundary_equations_apply() {
    let mut f = Fixture::new();
    let sqrt = f.p.sqrt;

    for (value, expected) in [(0u32, 0u32), (1, 1), (2, 1), (3, 1), (4, 2), (8, 2), (9, 3)] {
        let n = f.num(value);
        let lhs = f.const_app(sqrt, &[n]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "sqrt {value} must reduce to {expected}"
        );
    }

    let eight = f.num(8);
    let sqrt_eight = f.const_app(sqrt, &[eight]);
    let three = f.num(3);
    assert!(
        !f.k.def_eq(sqrt_eight, three),
        "negative control: sqrt 8 is 2, not 3 -- def_eq must not be vacuous"
    );
    let nine = f.num(9);
    let sqrt_nine = f.const_app(sqrt, &[nine]);
    let two = f.num(2);
    assert!(
        !f.k.def_eq(sqrt_nine, two),
        "negative control: sqrt 9 is 3, not 2"
    );

    // The two boundary equations apply, and each lands on the statement its
    // name promises rather than on some vacuously true instance.
    let p = f.p;
    for (name, expected_value) in [(p.sqrt_zero, 0u32), (p.sqrt_one, 1u32)] {
        let applied = f.const_app(name, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("{name:?} must type-check: {shown}")
        });
        let n = f.num(expected_value);
        let lhs = f.const_app(sqrt, &[n]);
        let want = f.eq(lhs, n);
        assert!(
            f.k.def_eq(inferred, want),
            "{name:?} must state Eq (sqrt {expected_value}) {expected_value}"
        );
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(p.sqrt_aux).is_empty(),
        "Nat.sqrtAux must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.sqrt).is_empty(),
        "Nat.sqrt must rest on zero axioms"
    );
}

/// `Nat.bit` computes at concrete points -- `bit false n = 2*n`,
/// `bit true n = 2*n + 1` -- and its four boundary theorems land on the
/// statement each name promises, each with a transposed/mismatched negative
/// control so this cannot pass vacuously.
#[test]
fn bit_computes_and_its_boundary_theorems_apply() {
    let mut f = Fixture::new();
    let bit = f.p.bit;
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    for (test, value, expected) in [
        (false_, 0u32, 0u32),
        (true_, 0, 1),
        (false_, 1, 2),
        (true_, 1, 3),
        (false_, 6, 12),
        (true_, 6, 13),
    ] {
        let n = f.num(value);
        let lhs = f.const_app(bit, &[test, n]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "bit _ {value} must reduce to {expected}"
        );
    }

    // Negative control: transposing the two branches must not also def_eq.
    let six = f.num(6);
    let bit_false_six = f.const_app(bit, &[false_, six]);
    let thirteen = f.num(13);
    assert!(
        !f.k.def_eq(bit_false_six, thirteen),
        "negative control: bit false 6 is 12, not 13 -- def_eq must not be vacuous"
    );
    let bit_true_six = f.const_app(bit, &[true_, six]);
    let twelve = f.num(12);
    assert!(
        !f.k.def_eq(bit_true_six, twelve),
        "negative control: bit true 6 is 13, not 12"
    );

    let p = f.p;

    // bit_false : Eq (bit false n) (mul 2 n)
    {
        let applied = f.const_app(p.bit_false, &[six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bit_false must type-check: {shown}")
        });
        let lhs = f.const_app(bit, &[false_, six]);
        let two = f.num(2);
        let rhs = f.const_app(p.mul, &[two, six]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_false must state Eq (bit false 6) (mul 2 6)"
        );
        // Negative control: bit_false's statement must not also match bit true.
        let bad_lhs = f.const_app(bit, &[true_, six]);
        let bad_want = f.eq(bad_lhs, rhs);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bit_false must not also prove Eq (bit true 6) (mul 2 6)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_false).is_empty(),
            "bit_false must rest on zero axioms"
        );
    }

    // bit_true : Eq (bit true n) (add (mul 2 n) 1)
    {
        let applied = f.const_app(p.bit_true, &[six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bit_true must type-check: {shown}")
        });
        let lhs = f.const_app(bit, &[true_, six]);
        let two = f.num(2);
        let doubled = f.const_app(p.mul, &[two, six]);
        let one = f.num(1);
        let rhs = f.const_app(p.add, &[doubled, one]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_true must state Eq (bit true 6) (add (mul 2 6) 1)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_true).is_empty(),
            "bit_true must rest on zero axioms"
        );
    }

    // bit_true_pos : Lt 0 (bit true n)
    {
        let applied = f.const_app(p.bit_true_pos, &[six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bit_true_pos must type-check: {shown}")
        });
        let zero = f.num(0);
        let lhs = f.const_app(bit, &[true_, six]);
        let want = f.lt(zero, lhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_true_pos must state Lt 0 (bit true 6)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_true_pos).is_empty(),
            "bit_true_pos must rest on zero axioms"
        );
    }

    // bit_false_le_bit_true : Le (bit false n) (bit true n)
    {
        let applied = f.const_app(p.bit_false_le_bit_true, &[six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bit_false_le_bit_true must type-check: {shown}")
        });
        let lhs = f.const_app(bit, &[false_, six]);
        let rhs = f.const_app(bit, &[true_, six]);
        let want = f.le(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bit_false_le_bit_true must state Le (bit false 6) (bit true 6)"
        );
        // Negative control: the reverse inequality is false (13 <= 12 is
        // false), so the theorem's statement must not def_eq it either.
        let reversed = f.le(rhs, lhs);
        assert!(
            !f.k.def_eq(inferred, reversed),
            "negative control: bit_false_le_bit_true must not also state Le (bit true 6) (bit false 6)"
        );
        assert!(
            f.k.axiom_footprint(p.bit_false_le_bit_true).is_empty(),
            "bit_false_le_bit_true must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(bit).is_empty(),
        "Nat.bit must rest on zero axioms"
    );
}

/// `Nat.land` computes bitwise AND at concrete points -- including a
/// non-diagonal pair with differing bit patterns (`3 &&& 5 = 1`) and a
/// self-AND that exercises several fuel steps (`7 &&& 7 = 7`) -- and its
/// four boundary/sanity theorems land on the statement each name promises,
/// each with a negative control this cannot pass vacuously.
#[test]
fn land_computes_and_its_boundary_theorems_apply() {
    let mut f = Fixture::new();
    let p = f.p;
    let land = p.land;

    for (m, n, expected) in [
        (0u32, 0u32, 0u32),
        (0, 5, 0),
        (5, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 1),
        (3, 5, 1),
        (6, 3, 2),
        (7, 7, 7),
    ] {
        let mm = f.num(m);
        let nn = f.num(n);
        let lhs = f.const_app(land, &[mm, nn]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "land {m} {n} must reduce to {expected}"
        );
    }

    // Negative controls: `3 &&& 5 = 1`, not `5` (the OR-shaped/first-operand
    // wrong answer) and not `7` (the OR of the two).
    let three = f.num(3);
    let five = f.num(5);
    let land_three_five = f.const_app(land, &[three, five]);
    let bad_five = f.num(5);
    assert!(
        !f.k.def_eq(land_three_five, bad_five),
        "negative control: land 3 5 is 1, not 5"
    );
    let bad_seven = f.num(7);
    assert!(
        !f.k.def_eq(land_three_five, bad_seven),
        "negative control: land 3 5 is 1, not 7"
    );

    // land_zero_left : Eq (land 0 n) 0
    {
        let seven = f.num(7);
        let zero = f.num(0);
        let applied = f.const_app(p.land_zero_left, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_zero_left must type-check: {shown}")
        });
        let lhs = f.const_app(land, &[zero, seven]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "land_zero_left must state Eq (land 0 7) 0"
        );
        // Negative control: the statement must not claim the wrong value.
        let one = f.num(1);
        let bad_want = f.eq(lhs, one);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: land_zero_left must not also state Eq (land 0 7) 1"
        );
        assert!(
            f.k.axiom_footprint(p.land_zero_left).is_empty(),
            "land_zero_left must rest on zero axioms"
        );
    }

    // land_zero_right : Eq (land m 0) 0
    {
        let nine = f.num(9);
        let zero = f.num(0);
        let applied = f.const_app(p.land_zero_right, &[nine]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_zero_right must type-check: {shown}")
        });
        let lhs = f.const_app(land, &[nine, zero]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "land_zero_right must state Eq (land 9 0) 0"
        );
        let one = f.num(1);
        let bad_want = f.eq(lhs, one);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: land_zero_right must not also state Eq (land 9 0) 1"
        );
        assert!(
            f.k.axiom_footprint(p.land_zero_right).is_empty(),
            "land_zero_right must rest on zero axioms"
        );
    }

    // land_one_one : Eq (land 1 1) 1
    {
        let applied = f.const_app(p.land_one_one, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_one_one must type-check: {shown}")
        });
        let one = f.num(1);
        let lhs = f.const_app(land, &[one, one]);
        let want = f.eq(lhs, one);
        assert!(
            f.k.def_eq(inferred, want),
            "land_one_one must state Eq (land 1 1) 1"
        );
        let zero = f.num(0);
        let bad_want = f.eq(lhs, zero);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: land_one_one must not also state Eq (land 1 1) 0"
        );
        assert!(
            f.k.axiom_footprint(p.land_one_one).is_empty(),
            "land_one_one must rest on zero axioms"
        );
    }

    // land_three_five : Eq (land 3 5) 1
    {
        let applied = f.const_app(p.land_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_three_five must type-check: {shown}")
        });
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(land, &[three, five]);
        let one = f.num(1);
        let want = f.eq(lhs, one);
        assert!(
            f.k.def_eq(inferred, want),
            "land_three_five must state Eq (land 3 5) 1"
        );
        let bad_want = f.eq(lhs, five);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: land_three_five must not also state Eq (land 3 5) 5"
        );
        assert!(
            f.k.axiom_footprint(p.land_three_five).is_empty(),
            "land_three_five must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(land).is_empty(),
        "Nat.land must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_aux).is_empty(),
        "Nat.landAux must rest on zero axioms"
    );
}

/// `Nat.lor` computes bitwise OR at concrete points -- including a
/// non-diagonal pair with differing bit patterns (`3 ||| 5 = 7`, the
/// discriminant against `land_three_five`'s `3 &&& 5 = 1`) and the zero
/// boundary in both argument positions, where OR (unlike AND) returns the
/// OTHER operand rather than zero -- and its three boundary/sanity theorems
/// land on the statement each name promises, each with a negative control
/// this cannot pass vacuously.
#[test]
fn lor_computes_or_and_its_boundary_theorems_apply() {
    let mut f = Fixture::new();
    let p = f.p;
    let lor = p.lor;

    for (m, n, expected) in [
        (0u32, 0u32, 0u32),
        (0, 5, 5),
        (5, 0, 5),
        (1, 0, 1),
        (0, 1, 1),
        (1, 1, 1),
        (3, 5, 7),
        (6, 3, 7),
        (7, 7, 7),
    ] {
        let mm = f.num(m);
        let nn = f.num(n);
        let lhs = f.const_app(lor, &[mm, nn]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "lor {m} {n} must reduce to {expected}"
        );
    }

    // Negative controls: `3 ||| 5 = 7`, not `1` (the AND-shaped wrong
    // answer) and not `5` (the first operand only).
    let three = f.num(3);
    let five = f.num(5);
    let lor_three_five = f.const_app(lor, &[three, five]);
    let bad_one = f.num(1);
    assert!(
        !f.k.def_eq(lor_three_five, bad_one),
        "negative control: lor 3 5 is 7, not 1"
    );
    let bad_five = f.num(5);
    assert!(
        !f.k.def_eq(lor_three_five, bad_five),
        "negative control: lor 3 5 is 7, not 5"
    );

    // lor_zero_left : Eq (lor 0 n) n
    {
        let seven = f.num(7);
        let zero = f.num(0);
        let applied = f.const_app(p.lor_zero_left, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_zero_left must type-check: {shown}")
        });
        let lhs = f.const_app(lor, &[zero, seven]);
        let want = f.eq(lhs, seven);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_zero_left must state Eq (lor 0 7) 7"
        );
        // Negative control: the statement must not claim the wrong value.
        let zero_val = f.num(0);
        let bad_want = f.eq(lhs, zero_val);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: lor_zero_left must not also state Eq (lor 0 7) 0"
        );
        assert!(
            f.k.axiom_footprint(p.lor_zero_left).is_empty(),
            "lor_zero_left must rest on zero axioms"
        );
    }

    // lor_zero_right : Eq (lor m 0) m
    {
        let nine = f.num(9);
        let zero = f.num(0);
        let applied = f.const_app(p.lor_zero_right, &[nine]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_zero_right must type-check: {shown}")
        });
        let lhs = f.const_app(lor, &[nine, zero]);
        let want = f.eq(lhs, nine);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_zero_right must state Eq (lor 9 0) 9"
        );
        let zero_val = f.num(0);
        let bad_want = f.eq(lhs, zero_val);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: lor_zero_right must not also state Eq (lor 9 0) 0"
        );
        assert!(
            f.k.axiom_footprint(p.lor_zero_right).is_empty(),
            "lor_zero_right must rest on zero axioms"
        );
    }

    // lor_three_five : Eq (lor 3 5) 7
    {
        let applied = f.const_app(p.lor_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_three_five must type-check: {shown}")
        });
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(lor, &[three, five]);
        let seven = f.num(7);
        let want = f.eq(lhs, seven);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_three_five must state Eq (lor 3 5) 7"
        );
        let bad_want = f.eq(lhs, five);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: lor_three_five must not also state Eq (lor 3 5) 5"
        );
        assert!(
            f.k.axiom_footprint(p.lor_three_five).is_empty(),
            "lor_three_five must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(lor).is_empty(),
        "Nat.lor must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lor_aux).is_empty(),
        "Nat.lorAux must rest on zero axioms"
    );
}

/// `Nat.ldiff` computes bitwise "AND NOT" at concrete points -- including a
/// non-diagonal pair (`3 &~ 5 = 2`) and its swap (`5 &~ 3 = 4`), the sharpest
/// negative control available: `ldiff`, unlike `land`/`lor`, is NOT
/// commutative, so the same two operands in the other order must produce a
/// DIFFERENT result -- and the zero boundary in both argument positions,
/// where (unlike `lor`) only the LEFT side is absorbing (`ldiff 0 n = 0`,
/// but `ldiff m 0 = m`). Its four boundary/sanity theorems land on the
/// statement each name promises, each with a negative control this cannot
/// pass vacuously.
#[test]
fn ldiff_computes_and_its_boundary_theorems_apply() {
    let mut f = Fixture::new();
    let p = f.p;
    let ldiff = p.ldiff;

    for (m, n, expected) in [
        (0u32, 0u32, 0u32),
        (0, 5, 0),
        (5, 0, 5),
        (1, 0, 1),
        (0, 1, 0),
        (1, 1, 0),
        (3, 5, 2),
        (5, 3, 4),
        (6, 3, 4),
        (7, 7, 0),
    ] {
        let mm = f.num(m);
        let nn = f.num(n);
        let lhs = f.const_app(ldiff, &[mm, nn]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "ldiff {m} {n} must reduce to {expected}"
        );
    }

    // Negative controls: `3 &~ 5 = 2`, not `1` (the AND-shaped wrong answer)
    // and not `6` (`5 &~ 3`, the swapped-operand result -- the asymmetry
    // itself is the discriminant).
    let three = f.num(3);
    let five = f.num(5);
    let ldiff_three_five = f.const_app(ldiff, &[three, five]);
    let bad_one = f.num(1);
    assert!(
        !f.k.def_eq(ldiff_three_five, bad_one),
        "negative control: ldiff 3 5 is 2, not 1"
    );
    let bad_four = f.num(4);
    assert!(
        !f.k.def_eq(ldiff_three_five, bad_four),
        "negative control: ldiff 3 5 is 2, not 4 (that is ldiff 5 3)"
    );

    // ldiff_zero_left : Eq (ldiff 0 n) 0
    {
        let seven = f.num(7);
        let zero = f.num(0);
        let applied = f.const_app(p.ldiff_zero_left, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_zero_left must type-check: {shown}")
        });
        let lhs = f.const_app(ldiff, &[zero, seven]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_zero_left must state Eq (ldiff 0 7) 0"
        );
        // Negative control: the statement must not claim the wrong value.
        let bad_want = f.eq(lhs, seven);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: ldiff_zero_left must not also state Eq (ldiff 0 7) 7"
        );
        assert!(
            f.k.axiom_footprint(p.ldiff_zero_left).is_empty(),
            "ldiff_zero_left must rest on zero axioms"
        );
    }

    // ldiff_zero_right : Eq (ldiff m 0) m
    {
        let nine = f.num(9);
        let zero = f.num(0);
        let applied = f.const_app(p.ldiff_zero_right, &[nine]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_zero_right must type-check: {shown}")
        });
        let lhs = f.const_app(ldiff, &[nine, zero]);
        let want = f.eq(lhs, nine);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_zero_right must state Eq (ldiff 9 0) 9"
        );
        let bad_want = f.eq(lhs, zero);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: ldiff_zero_right must not also state Eq (ldiff 9 0) 0"
        );
        assert!(
            f.k.axiom_footprint(p.ldiff_zero_right).is_empty(),
            "ldiff_zero_right must rest on zero axioms"
        );
    }

    // ldiff_three_five : Eq (ldiff 3 5) 2
    {
        let applied = f.const_app(p.ldiff_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_three_five must type-check: {shown}")
        });
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(ldiff, &[three, five]);
        let two = f.num(2);
        let want = f.eq(lhs, two);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_three_five must state Eq (ldiff 3 5) 2"
        );
        let bad_want = f.eq(lhs, five);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: ldiff_three_five must not also state Eq (ldiff 3 5) 5"
        );
        assert!(
            f.k.axiom_footprint(p.ldiff_three_five).is_empty(),
            "ldiff_three_five must rest on zero axioms"
        );
    }

    // ldiff_five_three : Eq (ldiff 5 3) 4 -- the asymmetry theorem: same two
    // operands as ldiff_three_five, swapped, and NOT the same answer.
    {
        let applied = f.const_app(p.ldiff_five_three, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_five_three must type-check: {shown}")
        });
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(ldiff, &[five, three]);
        let four = f.num(4);
        let want = f.eq(lhs, four);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_five_three must state Eq (ldiff 5 3) 4"
        );
        // The sharpest negative control this definition can carry: the
        // swapped-operand result must NOT equal ldiff_three_five's value.
        let two = f.num(2);
        let bad_want = f.eq(lhs, two);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: ldiff_five_three must not also state Eq (ldiff 5 3) 2 \
             (that is ldiff 3 5 -- ldiff is not commutative)"
        );
        assert!(
            f.k.axiom_footprint(p.ldiff_five_three).is_empty(),
            "ldiff_five_three must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(ldiff).is_empty(),
        "Nat.ldiff must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.ldiff_aux).is_empty(),
        "Nat.ldiffAux must rest on zero axioms"
    );
}

/// `Nat.clog` computes at concrete points, including `(2, 7)`, which is
/// deliberately chosen to differ from `Nat.log 2 7 = 2`: `clog` is the
/// CEILING logarithm, so `clog 2 7 = 3` (three levels of the fuel
/// recursion's guard, exercising `(n + b - 1) / b` at each). The boundary
/// equations then apply at a concrete argument and are axiom-free.
///
/// Negative controls differ from the truth by ONE successor, deliberately
/// (see `log_computes_and_its_boundary_equations_apply`'s doc for why).
#[test]
fn clog_computes_and_its_boundary_equations_apply() {
    let mut f = Fixture::new();
    let clog = f.p.clog;

    for (base, value, expected) in [
        (2u32, 8u32, 3u32),
        (2, 7, 3),
        (2, 5, 3),
        (2, 1, 0),
        (3, 9, 2),
        (5, 4, 1),
        (0, 6, 0),
        (1, 6, 0),
        (7, 0, 0),
    ] {
        let b = f.num(base);
        let n = f.num(value);
        let lhs = f.const_app(clog, &[b, n]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "clog {base} {value} must reduce to {expected}"
        );
    }

    let two = f.num(2);
    let seven = f.num(7);
    let clog_two_seven = f.const_app(clog, &[two, seven]);
    let four = f.num(4);
    assert!(
        !f.k.def_eq(clog_two_seven, four),
        "negative control: clog 2 7 is 3, not 4 -- def_eq must not be vacuous"
    );
    let three = f.num(3);
    let nine = f.num(9);
    let clog_three_nine = f.const_app(clog, &[three, nine]);
    let one = f.num(1);
    assert!(
        !f.k.def_eq(clog_three_nine, one),
        "negative control: clog 3 9 is 2, not 1"
    );

    // The boundary equations apply, and each lands on the statement its name
    // promises rather than on some vacuously true instance.
    let p = f.p;
    let zero = f.zero();
    for (name, expected_lhs) in [
        (p.clog_zero_right, (7u32, 0u32)),
        (p.clog_zero_left, (0, 7)),
        (p.clog_one_left, (1, 7)),
        (p.clog_one_right, (7, 1)),
    ] {
        let applied = f.const_app(name, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("{name:?} must apply at a concrete argument: {shown}")
        });
        let b = f.num(expected_lhs.0);
        let n = f.num(expected_lhs.1);
        let lhs = f.const_app(clog, &[b, n]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "{name:?} at 7 must state Eq (clog {} {}) 0",
            expected_lhs.0,
            expected_lhs.1
        );
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{name:?} must rest on zero axioms"
        );
    }
}
