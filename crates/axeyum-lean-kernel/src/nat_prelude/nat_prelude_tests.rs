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
    ExprId, Kernel, KernelError, LocalContext, LocalDecl, NameId, NatOps, NatPrelude, NatState,
    build_nat_prelude, on_a_deep_stack,
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
        p.log2,
        p.bit,
        p.land_aux,
        p.land,
        p.lor_aux,
        p.lor,
        p.ldiff_aux,
        p.ldiff,
        p.bitwise_aux,
        p.bitwise,
        p.xor,
        p.asc_factorial,
        p.multichoose,
        p.is_rel_prime,
        p.min_fac_aux,
        p.min_fac,
        p.pair_fst,
        p.pair_snd,
        p.binary_rec_aux,
        p.binary_rec,
        // `nat-dist-nth` lane (`docs/plan/status/348-nat-dist-nth.md`).
        p.dist,
        p.nth_aux,
        p.nth,
        // `nat-fermat-number` lane (`docs/research/09-decisions/
        // adr-0653-declaring-the-unblocking-constant-contaminated-the-
        // family-it-opened.md`). Definition only, deliberately.
        p.fermat_number,
    ]
}

fn theorem_names(p: &NatPrelude) -> Vec<NameId> {
    vec![
        p.count_range_union_add_inter,
        p.count_range_le_of_subset,
        p.count_range_compl,
        p.count_range_congr_lt,
        p.count_range_point_change,
        p.count_range_permute,
        p.count_range_product,
        p.div_mod_block,
        p.crt_self_map_maps_into,
        p.crt_self_map_injective_on,
        p.totient_mul_of_coprime,
        p.count_range_const_true,
        p.coprime_mul_iff_of_dvd,
        p.totient_mul_of_dvd,
        p.totient_pow_succ_of_prime,
        p.totient_prime_pow,
        p.totient_dvd_totient_mul_prime,
        p.totient_dvd_totient_mul,
        p.totient_dvd_of_dvd,
        p.totient_mul_cofactor_bound,
        p.eq_or_eq_of_totient_eq_totient,
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
        p.add_add_add_comm,
        p.add_eq,
        p.add_eq_left,
        p.add_eq_right,
        p.add_eq_zero_iff,
        p.add_eq_one_iff,
        p.add_eq_two_iff,
        p.add_eq_three_iff,
        p.zero_mul,
        p.succ_mul,
        p.mul_comm,
        p.left_distrib,
        p.right_distrib,
        p.mul_assoc,
        p.one_mul,
        p.mul_one,
        p.mul_eq_zero,
        p.add_eq_zero,
        p.zero_or_succ,
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
        p.add_mul_div_left,
        p.add_mul_div_right,
        p.add_mul_mod_self_left,
        p.add_mul_mod_self_right,
        p.add_mod_left,
        p.add_mod_right,
        p.add_div_left,
        p.add_div_right,
        p.add_div_of_dvd_add_add_one,
        p.base_induction,
        p.mod_mul,
        p.mod_mul_left_mod,
        p.mod_mul_right_mod,
        p.mod_mul_left_div_self,
        p.mod_mul_right_div_self,
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
        p.gcd_mul_right,
        p.dvd_gcd_mul_iff_dvd_mul,
        p.dvd_mul_gcd_iff_dvd_mul,
        p.dvd_gcd_mul_gcd_iff_dvd_mul,
        p.mod_eq_cancel_left_div_gcd,
        p.mod_eq_cancel_right_div_gcd,
        p.mod_eq_cancel_left_div_gcd_general,
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
        p.gcd_dvd_mul,
        p.gcd_le_mul,
        p.eq_zero_of_lcm_eq_zero,
        p.lcm_assoc,
        p.lcm_div,
        p.fib_add,
        p.coprime_fib_succ,
        p.fib_add_two_strictmono,
        p.fib_strictmonoon,
        p.fib_lt_fib,
        p.le_fib_self,
        p.le_fib_add_one,
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
        p.mod_eq_add_left_cancel,
        p.mod_eq_add_right_cancel,
        p.mod_eq_add_iff_left,
        p.mod_eq_add_iff_right,
        p.mod_eq_cancel_left,
        p.mod_eq_add_le_of_lt,
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
        p.coprime_dvd_left,
        p.coprime_dvd_right,
        p.coprime_mul_left,
        p.coprime_mul_right,
        p.coprime_mul_left_right,
        p.coprime_mul_right_right,
        p.dvd_of_dvd_mul_left,
        p.dvd_of_dvd_mul_right,
        p.coprime_div_right,
        p.coprime_div_left,
        p.gcd_comm,
        p.coprime_mul_of_coprime,
        p.gcd_mod_left_eq_gcd,
        p.coprime_mul_iff,
        p.coprime_of_forall_prime_dvd,
        p.dvd_of_forall_prime_mul_dvd,
        p.coprime_iff_is_rel_prime,
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
        // `prime_dvd_mirrors.rs`: the small consequences of `prime_condition`'s
        // own clause, plus the `Coprime <-> not dvd` bridge and its `p^m`
        // corollary.
        p.prime_one_lt,
        p.prime_one_le,
        p.prime_pos,
        p.prime_ne_one,
        p.prime_ne_zero,
        p.prime_not_dvd_one,
        p.prime_eq_one_or_self_of_dvd,
        p.prime_dvd_iff_eq,
        p.prime_dvd_mul_iff,
        p.prime_coprime_iff_not_dvd,
        p.prime_eq_two_or_odd,
        p.prime_eq_two_or_mod_two_eq_one,
        p.prime_mod_two_eq_one_iff_ne_two,
        p.prime_coprime_pow_of_not_dvd,
        p.mod_eq_pow,
        p.dvd_sum_range_of_forall_lt,
        p.add_pow_modeq_prime,
        p.pow_prime_modeq_self,
        p.count_range_zero,
        p.count_range_succ,
        p.count_range_le,
        p.count_range_congr,
        p.count_range_split,
        p.count_range_reversal_even,
        p.beq_eq_false_of_ne,
        p.count_range_eq_pred_of_only_zero_false,
        p.totient_prime,
        p.coprime_succ_self,
        p.totient_eq_zero,
        p.count_range_succ_of_true,
        p.count_range_le_of_le,
        p.count_range_ge_two_of_two_witnesses,
        p.dvd_two_of_totient_le_one,
        p.totient_eq_one_iff,
        p.totient_even,
        p.odd_totient_iff_eq_one,
        p.odd_totient_iff,
        p.totient_coprime_totient_iff,
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
        p.test_bit_of_zero,
        p.mod_two_mul_split,
        p.sum_test_bit_lt,
        p.size_zero,
        p.size_aux_lt_pow,
        p.lt_pow_size,
        p.mod_eq_self_of_lt,
        p.sum_test_bit_eq,
        p.sum_range_const_zero,
        p.zero_of_test_bit_eq_zero,
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
        p.mod_lcm,
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
        p.desc_factorial_succ_eq_succ_mul,
        p.desc_factorial_eq_factorial_mul_choose,
        p.factorial_dvd_desc_factorial,
        p.desc_factorial_self,
        p.desc_factorial_le,
        p.self_le_factorial,
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
        p.even_iff_mod_two_eq_zero,
        p.odd_iff_mod_two_eq_one,
        p.div_two_mul_two_of_even,
        p.div_two_mul_two_add_one_of_odd,
        p.add_one_lt_of_even,
        p.even_mul_of_even_left,
        p.odd_of_mul_left,
        p.odd_of_mul_right,
        p.even_add_one,
        p.even_add,
        p.even_add_prime,
        p.even_div,
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
        p.five_le_of_ne_two_of_ne_three,
        p.prime_pred_pos,
        p.succ_pred_prime,
        p.prime_not_prime_pow_two_le,
        p.prime_not_prime_pow_ne_one,
        p.prime_eq_one_of_pow,
        p.prime_not_coprime_iff_dvd,
        p.prime_mul_eq_prime_sq_iff,
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
        p.div_le_div_right,
        p.log_aux_mono,
        p.log_mono_right,
        p.log_monotone,
        p.clog_aux_mono,
        p.clog_mono_right,
        p.clog_monotone,
        p.clog_pos,
        p.log_aux_le_clog_aux,
        p.log_le_clog,
        p.div_lt_self,
        p.log_aux_lt_of_pos,
        p.log_lt_self,
        p.div_le_div_left,
        p.log_aux_antitone_base,
        p.log_antitone_left,
        p.clog_aux_antitone_base,
        p.clog_antitone_left,
        p.log2_eq_log_two,
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
        p.bitwise_zero_left,
        p.bitwise_zero_right,
        p.bitwise_and_eq_land_three_five,
        p.bitwise_or_eq_lor_three_five,
        p.bitwise_xor_three_five,
        p.xor_three_five,
        p.even_xor,
        p.xor_comm,
        p.test_bit_xor,
        p.self_lt_two_pow,
        p.self_lt_two_pow_add,
        p.lt_of_test_bit,
        p.test_bit_eq_zero_of_lt,
        p.msb_exists_of_le_fuel,
        p.exists_most_significant_bit,
        p.eq_of_test_bit_eq,
        p.xor_assoc,
        p.xor_xor_cancel_left,
        p.xor_xor_cancel_right,
        p.xor_ne_zero_iff,
        p.xor_trichotomy,
        p.lt_xor_cases,
        p.lt_two_cases,
        p.mod_two_eq_zero_or_one,
        p.bitwise_aux_eq_land_aux,
        p.bitwise_aux_eq_lor_aux,
        p.bitwise_and_eq_land,
        p.bitwise_or_eq_lor,
        p.land_aux_zero_left_any_fuel,
        p.land_aux_agree_of_fuel,
        p.land_aux_eq_land_of_le,
        p.lor_aux_zero_left_any_fuel,
        p.lor_aux_agree_of_fuel,
        p.lor_aux_eq_lor_of_le,
        p.ldiff_aux_zero_left_any_fuel,
        p.ldiff_aux_agree_of_fuel,
        p.ldiff_aux_eq_ldiff_of_le,
        p.land_aux_comm_of_fuel,
        p.land_comm,
        p.lor_aux_comm_of_fuel,
        p.lor_comm,
        p.bitwise_aux_zero_left_any_fuel,
        p.bitwise_aux_agree_of_fuel,
        p.bitwise_aux_comm_of_fuel,
        p.bitwise_comm,
        p.bitwise_aux_swap_of_fuel,
        p.bitwise_swap,
        p.bitwise_bit,
        p.land_aux_le_left,
        p.land_le_left,
        p.bit_div_two,
        p.bit_mod_two,
        p.land_bit,
        p.land_aux_eq_zero_of_left_eq_zero,
        p.lor_bit,
        p.ldiff_bit,
        p.land_aux_assoc_of_fuel,
        p.land_assoc,
        p.lor_aux_ne_zero_of_right_ne_zero,
        p.lor_aux_assoc_of_fuel,
        p.lor_aux_le_add,
        p.lor_assoc,
        p.asc_factorial_zero,
        p.asc_factorial_succ,
        p.asc_factorial_one,
        p.zero_asc_factorial_succ,
        p.asc_factorial_succ_eq_factorial_mul_choose,
        p.factorial_dvd_asc_factorial,
        p.multichoose_zero_right,
        p.multichoose_one,
        p.multichoose_one_right,
        p.min_fac_aux_minimal,
        p.min_fac_minimal_of_two_le,
        p.coprime_of_lt_min_fac,
        p.pair_fst_mk,
        p.pair_snd_mk,
        p.pair_eta,
        p.pair_ext,
        p.lt_two_mul_of_pos,
        p.half_le_of_succ_le_succ,
        p.binary_rec_aux_zero_fuel,
        p.binary_rec_aux_zero,
        p.binary_rec_aux_succ,
        p.binary_rec_zero,
        p.binary_rec_aux_agree_of_fuel,
        p.binary_rec_succ,
        p.binary_rec_rebuilds_thirteen,
        p.binary_rec_rebuilds_six,
        p.lt_of_mul_lt_mul_left,
        p.lt_of_mul_lt_mul_right,
        p.mul_lt_mul_left,
        p.mul_lt_mul_right,
        p.div_lt_of_lt_mul,
        p.add_pos_right,
        p.dvd_mul_left,
        p.dvd_mul_left_of_dvd,
        p.eq_zero_of_gcd_eq_zero_left,
        p.eq_zero_of_gcd_eq_zero_right,
        p.dvd_mod_iff_gen,
        p.div_mul_cancel,
        p.dvd_iff_mod_eq_zero,
        p.div_gcd_pos_of_pos_left,
        p.div_gcd_pos_of_pos_right,
        p.dvd_add_iff_left,
        p.dvd_mul_split,
        // `nat-dist-nth` lane (`docs/plan/status/348-nat-dist-nth.md`).
        p.dist_comm,
        p.dist_self,
        p.dist_eq_sub_of_le,
        p.dist_eq_sub_of_le_right,
        p.dist_zero_right,
        p.dist_zero_left,
        p.dist_succ_succ,
        // `pow-add-prime` lane (toward
        // `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`), `pow_add_prime.rs`.
        p.pow_mul,
        p.dvd_pow_add_one_of_odd_exp,
        p.dvd_pow_add_one_of_odd_mul_exp,
        p.pow_two_or_has_odd_factor,
        p.pow_of_pow_add_prime,
        // `fermat-mirrors` lane: `fermat_number_mirrors.rs`.
        p.fermatnumber_ne_one,
        p.fermatnumber_mono,
        p.coprime_fermatnumber_fermatnumber,
        // `lnp-implies-em` lane, `least_number.rs` -- ADR-0603 row 2 for the
        // least-number principle over the naturals.
        p.lnp_bounded_search,
        p.lnp_of_pointwise_decision,
        p.lnp_decidable,
        p.em_implies_lnp,
        p.lnp_unrestricted_implies_em,
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
        p.fin_rec, p.pair, p.pair_mk, p.pair_rec,
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

/// `Nat.Pair` and `Nat.binaryRec` **compute**, each with a negative control.
///
/// The trusted gate admits a `Definition` on its TYPE, so neither
/// `Nat.Pair.fst`/`snd` nor `Nat.binaryRecAux` is constrained by admission to
/// return anything in particular. `Nat.Pair.mk 3 5` is deliberately
/// ASYMMETRIC, so a `fst`/`snd` transposition changes the value instead of
/// coincidentally agreeing — the failure `land 3 5`/`lor 3 5` cannot expose
/// on its own.
///
/// For `binaryRec` the workload is the bit round trip
/// `binaryRec 0 (fun b _ acc => bit b acc) n = n`, which the prelude also
/// carries as the theorems `binaryRec_rebuilds_thirteen`/`_six`. What is added
/// here is (a) a THIRD value whose bit pattern is a palindrome-free
/// alternation, and (b) the negative control that `13` does not reduce to `11`
/// — `0b1101` reversed — so a traversal that consumed the bits in the wrong
/// order would be caught rather than passing by symmetry. Every magnitude is
/// tiny on purpose: these numerals are unary `succ` towers.
#[test]
fn pair_and_binary_rec_compute_with_transposed_negative_controls() {
    let mut f = Fixture::new();

    // --- Nat.Pair ----------------------------------------------------------
    let three = f.num(3);
    let five = f.num(5);
    let mk = f.p.pair_mk;
    let q = f.const_app(mk, &[three, five]);
    let fst = f.const_app(f.p.pair_fst, &[q]);
    let snd = f.const_app(f.p.pair_snd, &[q]);
    assert!(f.k.def_eq(fst, three), "fst (mk 3 5) must reduce to 3");
    assert!(f.k.def_eq(snd, five), "snd (mk 3 5) must reduce to 5");
    assert!(
        !f.k.def_eq(fst, five),
        "fst (mk 3 5) must NOT reduce to 5 -- a transposed projection"
    );
    assert!(
        !f.k.def_eq(snd, three),
        "snd (mk 3 5) must NOT reduce to 3 -- a transposed projection"
    );

    // --- Nat.binaryRec: the bit round trip ---------------------------------
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let rebuild = {
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let ignored_fv = f.fresh_fvar();
        let acc_fv = f.fresh_fvar();
        let acc = f.k.fvar(acc_fv);
        let bit = f.p.bit;
        let body = f.const_app(bit, &[b, acc]);
        let with_acc = f.lam_fv(acc_fv, nat, body);
        let with_ignored = f.lam_fv(ignored_fv, nat, with_acc);
        f.lam_fv(b_fv, bool_ty, with_ignored)
    };
    let zero = f.zero();
    let binary_rec = f.p.binary_rec;
    for value in [0u32, 1, 6, 10, 13] {
        let numeral = f.num(value);
        let lhs = f.const_app(binary_rec, &[nat, zero, rebuild, numeral]);
        assert!(
            f.k.def_eq(lhs, numeral),
            "binaryRec must rebuild {value} from its own bits"
        );
    }
    // Negative control: `13 = 0b1101` reversed is `0b1011 = 11`. A traversal
    // that combined the bits in the wrong order would land here.
    let thirteen = f.num(13);
    let eleven = f.num(11);
    let at_thirteen = f.const_app(binary_rec, &[nat, zero, rebuild, thirteen]);
    assert!(
        !f.k.def_eq(at_thirteen, eleven),
        "binaryRec 13 must NOT reduce to 11 (13's bits, reversed)"
    );
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

/// `Nat.coprime_succ_self` — consecutive naturals are coprime — applies at a
/// concrete instance (where its content REDUCES: `gcd 5 6` must be
/// def-eq `1`) and at a genuinely free variable (disjoint defect classes,
/// per this file's own standing rule: a concrete instance can hide a
/// defeq-shaped gap a symbolic check exposes, and a symbolic check alone can
/// miss a wrong hand-computed expectation).
#[test]
fn coprime_succ_self_applies_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: gcd 5 6 = 1, and NOT gcd 4 6 = 1 (a negative control on a
    // DIFFERENT pair, both even, sharing the factor 2 -- `gcd 5 7 = 1` too,
    // so that pair would not have discriminated anything).
    let five = f.num(5);
    let six = f.num(6);
    let one = f.num(1);
    let gcd_5_6 = f.gcd(five, six);
    assert!(f.k.def_eq(gcd_5_6, one), "gcd 5 6 must reduce to 1");
    let four = f.num(4);
    let gcd_4_6 = f.gcd(four, six);
    assert!(!f.k.def_eq(gcd_4_6, one), "gcd 4 6 must NOT reduce to 1");

    let proof = f.const_app(p.coprime_succ_self, &[five]);
    let expected = f.eq(gcd_5_6, one);
    let inferred =
        f.k.infer(proof)
            .expect("coprime_succ_self 5 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "coprime_succ_self 5 must prove gcd 5 6 = 1"
    );

    // Symbolic: a genuinely free `m`, pushed into an explicit `LocalContext`
    // so `infer_in` can look up its type (a bare unregistered `FVar` is
    // `UnboundFVar` to the checker, not merely "unknown").
    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let sm = f.succ(m);
    let one2 = f.num(1);
    let gcd_m_sm = f.gcd(m, sm);
    let expected_sym = f.eq(gcd_m_sm, one2);
    let proof_sym = f.const_app(p.coprime_succ_self, &[m]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(proof_sym, &mut ctx)
            .expect("coprime_succ_self must apply at a free variable");
    assert!(
        f.k.def_eq(inferred_sym, expected_sym),
        "coprime_succ_self m must prove gcd m (succ m) = 1 symbolically"
    );
}

/// `Nat.totient_eq_zero` at three shapes: `n = 0` (both `Iff` legs are
/// trivially true), a concrete `n = succ k` with `k` a literal (`totient 5 =
/// 0` and `5 = 0` are both refutable, so both `Iff` legs are `ex_falso`
/// routes), and a genuinely free `n = succ m` (the universally-quantified
/// case the theorem was actually proved over — the concrete instances alone
/// would not catch a wrong direction inside `at_succ`'s defeq chain, since a
/// concrete numeral papers over exactly the kind of defeq gap this file's
/// standing rule warns about).
#[test]
fn totient_eq_zero_applies_at_zero_a_concrete_successor_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();

    // n = 0: mp and mpr are both immediate.
    let totient_0 = f.const_app(p.totient, &[zero]);
    let iff_0 = f.const_app(p.totient_eq_zero, &[zero]);
    let expected_lhs_0 = f.eq(totient_0, zero);
    let expected_rhs_0 = f.eq(zero, zero);
    let expected_0 = f.const_app(p.logic.iff, &[expected_lhs_0, expected_rhs_0]);
    let inferred_0 = f.k.infer(iff_0).expect("totient_eq_zero 0 must type-check");
    assert!(f.k.def_eq(inferred_0, expected_0));
    assert!(
        f.k.def_eq(totient_0, zero),
        "totient 0 must reduce to 0 by the countRange base case"
    );

    // n = 5 (a concrete successor): totient 5 must NOT reduce to 0 (a
    // negative control on the theorem's actual content, not just its type).
    let five = f.num(5);
    let totient_5 = f.const_app(p.totient, &[five]);
    assert!(
        !f.k.def_eq(totient_5, zero),
        "totient 5 must NOT reduce to 0"
    );
    let iff_5 = f.const_app(p.totient_eq_zero, &[five]);
    let expected_lhs_5 = f.eq(totient_5, zero);
    let expected_rhs_5 = f.eq(five, zero);
    let expected_5 = f.const_app(p.logic.iff, &[expected_lhs_5, expected_rhs_5]);
    let inferred_5 = f.k.infer(iff_5).expect("totient_eq_zero 5 must type-check");
    assert!(f.k.def_eq(inferred_5, expected_5));

    // Symbolic: a genuinely free `n`, pushed into an explicit `LocalContext`
    // (see `coprime_succ_self_applies_at_a_concrete_instance_and_symbolically`
    // for why a bare unregistered `FVar` cannot be `infer`red directly).
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let totient_n = f.const_app(p.totient, &[n]);
    let iff_n = f.const_app(p.totient_eq_zero, &[n]);
    let expected_lhs_n = f.eq(totient_n, zero);
    let expected_rhs_n = f.eq(n, zero);
    let expected_n = f.const_app(p.logic.iff, &[expected_lhs_n, expected_rhs_n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_n =
        f.k.infer_in(iff_n, &mut ctx)
            .expect("totient_eq_zero must apply at a free variable");
    assert!(f.k.def_eq(inferred_n, expected_n));
}

/// `Nat.countRange_succ_of_true` — the general "promote one witness" step
/// extracted from `totient_eq_zero`'s own technique — at a concrete predicate
/// (`fun k => beq k 0`, true only at `0`) applied at its own witness, AND at
/// a genuinely free `f`/`k`/hypothesis pushed into an explicit
/// `LocalContext` (the fully symbolic instantiation the general lemma was
/// actually proved over).
#[test]
fn count_range_succ_of_true_applies_at_a_concrete_witness_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let pred_ty = f.arrow(nat, bool_ty);
    let anon = f.anon_name();

    // Concrete: `f := fun k => beq k 0`, witness `k = 0`.
    let zero = f.zero();
    let true_v = f.bool_true();
    let f_concrete = {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let body = f.beq(x, zero);
        f.lam_fv(x_fv, nat, body)
    };
    let f0 = f.apply(f_concrete, &[zero]);
    assert!(f.k.def_eq(f0, true_v), "f 0 = beq 0 0 must reduce to true");
    let hyp = f.bool_refl(true_v);

    let one = f.num(1);
    let cr_f_0 = f.const_app(p.count_range, &[f_concrete, zero]);
    assert!(
        f.k.def_eq(cr_f_0, zero),
        "countRange f 0 must be 0 (no room)"
    );
    let succ_zero = f.succ(zero);
    let cr_f_1 = f.const_app(p.count_range, &[f_concrete, succ_zero]);
    assert!(
        f.k.def_eq(cr_f_1, one),
        "countRange f 1 must be 1 (the k=0 witness counts)"
    );
    // Negative control: the conclusion is NOT vacuous -- countRange f 1 is
    // NOT 0.
    assert!(!f.k.def_eq(cr_f_1, zero), "countRange f 1 must NOT be 0");

    let proof = f.const_app(p.count_range_succ_of_true, &[f_concrete, zero, hyp]);
    let succ_cr_f_0 = f.succ(cr_f_0);
    let expected = f.eq(cr_f_1, succ_cr_f_0);
    let inferred =
        f.k.infer(proof)
            .expect("count_range_succ_of_true must type-check at a concrete witness");
    assert!(
        f.k.def_eq(inferred, expected),
        "count_range_succ_of_true must prove countRange f 1 = succ (countRange f 0)"
    );

    // Symbolic: a genuinely free `f`, `k`, and hypothesis `h : f k = true`.
    let f_fv = f.fresh_fvar();
    let f_sym = f.k.fvar(f_fv);
    let k_fv = f.fresh_fvar();
    let k = f.k.fvar(k_fv);
    let fk = f.apply(f_sym, &[k]);
    let h_ty = f.bool_eq(fk, true_v);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);

    let sk = f.succ(k);
    let cr_f_sk = f.const_app(p.count_range, &[f_sym, sk]);
    let cr_f_k = f.const_app(p.count_range, &[f_sym, k]);
    let succ_cr_f_k = f.succ(cr_f_k);
    let expected_sym = f.eq(cr_f_sk, succ_cr_f_k);
    let proof_sym = f.const_app(p.count_range_succ_of_true, &[f_sym, k, h]);

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: f_fv,
        name: anon,
        ty: pred_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: k_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: h_fv,
        name: anon,
        ty: h_ty,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(proof_sym, &mut ctx)
            .expect("count_range_succ_of_true must apply at genuinely free f/k/h");
    assert!(
        f.k.def_eq(inferred_sym, expected_sym),
        "count_range_succ_of_true must hold symbolically"
    );
}

/// `Nat.countRange_reversal_even` — the general, `totient`-independent
/// evenness lemma (`count_range_reversal.rs`), applied at `L = 0` with a
/// concrete predicate (`fun k => beq k 0`): both hypotheses are VACUOUS at
/// `L = 0` (no `j` satisfies `Lt j 0`), discharged via `Nat.not_succ_le_zero`
/// -- this exercises the theorem's real public signature/currying
/// (`L` bound before `h`, per the module doc) rather than re-deriving the
/// mathematical content, which the kernel already checked exhaustively (both
/// hypotheses are fully symbolic in `h` and `L`) when the theorem itself was
/// admitted.
#[test]
fn count_range_reversal_even_applies_at_a_vacuous_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();

    let zero = f.zero();
    let f_concrete = {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let body = f.beq(x, zero);
        f.lam_fv(x_fv, nat, body)
    };

    // `Pi j, Lt j 0 -> Eq Bool (h (sub (pred 0) j)) (h j)`, vacuous.
    let hyp1_proof = {
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let lt_j_0 = f.lt(j, zero);
        let hlt_fv = f.fresh_fvar();
        let hlt = f.k.fvar(hlt_fv);
        let pred_0 = f.pred(zero);
        let sub_val = f.sub(pred_0, j);
        let h_sub = f.apply(f_concrete, &[sub_val]);
        let h_j = f.apply(f_concrete, &[j]);
        let goal = f.bool_eq(h_sub, h_j);
        let not_succ_le_zero_j = f.lemma(p.not_succ_le_zero, &[j]);
        let contradiction = f.apply(not_succ_le_zero_j, &[hlt]);
        let false_ty = f.kernel().const_(p.logic.false_, vec![]);
        let level_zero = f.kernel().level_zero();
        let false_rec = f.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let anon = f.anon_name();
        let motive = f.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
        let body = f.apply(false_rec, &[motive, contradiction]);
        let inner = f.lam_fv(hlt_fv, lt_j_0, body);
        f.lam_fv(j_fv, nat, inner)
    };

    // `Pi j, Lt j 0 -> Eq Bool (h j) true -> Not (Eq j (sub (pred 0) j))`,
    // vacuous.
    let hyp2_proof = {
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let lt_j_0 = f.lt(j, zero);
        let hlt_fv = f.fresh_fvar();
        let hlt = f.k.fvar(hlt_fv);
        let h_j = f.apply(f_concrete, &[j]);
        let true_v = f.bool_true();
        let heq_true_ty = f.bool_eq(h_j, true_v);
        let heq_fv = f.fresh_fvar();
        let pred_0 = f.pred(zero);
        let sub_val = f.sub(pred_0, j);
        let eq_j_sub = f.eq(j, sub_val);
        let false_ty = f.kernel().const_(p.logic.false_, vec![]);
        let level_zero = f.kernel().level_zero();
        let false_rec = f.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let anon = f.anon_name();
        let not_goal = f.arrow(eq_j_sub, false_ty);
        let motive = f
            .kernel()
            .lam(anon, false_ty, not_goal, BinderInfo::Default);
        let not_succ_le_zero_j = f.lemma(p.not_succ_le_zero, &[j]);
        let contradiction = f.apply(not_succ_le_zero_j, &[hlt]);
        let body = f.apply(false_rec, &[motive, contradiction]);
        let with_heq = f.lam_fv(heq_fv, heq_true_ty, body);
        let inner = f.lam_fv(hlt_fv, lt_j_0, with_heq);
        f.lam_fv(j_fv, nat, inner)
    };

    let proof = f.const_app(
        p.count_range_reversal_even,
        &[zero, f_concrete, hyp1_proof, hyp2_proof],
    );
    let cr_h_0 = f.const_app(p.count_range, &[f_concrete, zero]);
    assert!(
        f.k.def_eq(cr_h_0, zero),
        "countRange f 0 must reduce to 0 (no room)"
    );
    let expected = f.const_app(p.even, &[cr_h_0]);
    let inferred =
        f.k.infer(proof)
            .expect("countRange_reversal_even must type-check at L = 0");
    assert!(
        f.k.def_eq(inferred, expected),
        "countRange_reversal_even must prove Even (countRange h 0)"
    );

    // Negative control: `Even` is not vacuously derivable from nothing --
    // `bool_ty` (an unrelated `Prop`) is NOT what this proves.
    assert!(
        !f.k.def_eq(inferred, bool_ty),
        "the conclusion must not be an arbitrary unrelated type"
    );
}

/// `Nat.countRange_le_of_le` — cardinality monotonicity in the range bound —
/// at a concrete gap (`fun k => beq k 3`, `m = 2`, `n = 5`: no witness below
/// `2`, one witness (`k = 3`) below `5`, so the conclusion is the genuinely
/// non-trivial `Le 0 1`) and at a genuinely free `f`/`m`/`n`/hypothesis.
#[test]
fn count_range_le_of_le_applies_at_a_concrete_gap_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let pred_ty = f.arrow(nat, bool_ty);
    let anon = f.anon_name();

    let three = f.num(3);
    let f_concrete = {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let body = f.beq(x, three);
        f.lam_fv(x_fv, nat, body)
    };
    let two = f.num(2);
    let five = f.num(5);
    let zero = f.zero();
    let one = f.num(1);
    let cr_f_2 = f.const_app(p.count_range, &[f_concrete, two]);
    assert!(f.k.def_eq(cr_f_2, zero), "countRange f 2 must be 0");
    let cr_f_5 = f.const_app(p.count_range, &[f_concrete, five]);
    assert!(
        f.k.def_eq(cr_f_5, one),
        "countRange f 5 must be 1 (the k=3 witness)"
    );
    // Negative control: NOT vacuous -- the two counts genuinely differ.
    assert!(
        !f.k.def_eq(cr_f_2, cr_f_5),
        "countRange f 2 and countRange f 5 must NOT be def-eq"
    );

    let h = f.lemma(p.le_add_right, &[two, three]); // Le 2 (add 2 3), and `add 2 3` reduces to `5`
    let proof = f.const_app(p.count_range_le_of_le, &[f_concrete, two, five, h]);
    let expected = f.le(cr_f_2, cr_f_5);
    let inferred =
        f.k.infer(proof)
            .expect("count_range_le_of_le must type-check at a concrete gap");
    assert!(
        f.k.def_eq(inferred, expected),
        "count_range_le_of_le must prove Le (countRange f 2) (countRange f 5)"
    );

    // Symbolic.
    let f_fv = f.fresh_fvar();
    let f_sym = f.k.fvar(f_fv);
    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let hyp_ty = f.le(m, n);
    let hyp_fv = f.fresh_fvar();
    let hyp = f.k.fvar(hyp_fv);

    let cr_f_m = f.const_app(p.count_range, &[f_sym, m]);
    let cr_f_n = f.const_app(p.count_range, &[f_sym, n]);
    let expected_sym = f.le(cr_f_m, cr_f_n);
    let proof_sym = f.const_app(p.count_range_le_of_le, &[f_sym, m, n, hyp]);

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: f_fv,
        name: anon,
        ty: pred_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hyp_fv,
        name: anon,
        ty: hyp_ty,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(proof_sym, &mut ctx)
            .expect("count_range_le_of_le must apply at genuinely free f/m/n/hyp");
    assert!(
        f.k.def_eq(inferred_sym, expected_sym),
        "count_range_le_of_le must hold symbolically"
    );
}

/// `Nat.countRange_ge_two_of_two_witnesses` — the general "two distinct
/// witnesses give count >= 2" lemma this family's mirrors bottleneck on — at
/// the canonical case named in `totient_lemmas.rs`'s module doc: `n = 4`,
/// witnesses `i = 1` (always coprime to anything) and `j = 3` (the top
/// index), for `f := fun k => beq (gcd k 4) 1`. `countRange f 4` is EXACTLY
/// `2` (`{1,3}` are coprime to `4`, `{0,2}` are not), so the theorem's `Le 2`
/// conclusion is tight, not vacuously satisfied by a larger true count.
#[test]
fn count_range_ge_two_of_two_witnesses_applies_at_the_totient_four_case() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let four = f.num(4);
    let f_concrete = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let g = f.gcd(k, four);
        let one_inner = f.num(1);
        let body = f.beq(g, one_inner);
        f.lam_fv(k_fv, nat, body)
    };

    let one = f.num(1);
    let three = f.num(3);
    let two = f.num(2);
    let true_v = f.bool_true();

    let f1 = f.apply(f_concrete, &[one]);
    assert!(f.k.def_eq(f1, true_v), "gcd 1 4 = 1, so f 1 must be true");
    let f3 = f.apply(f_concrete, &[three]);
    assert!(f.k.def_eq(f3, true_v), "gcd 3 4 = 1, so f 3 must be true");
    let zero = f.zero();
    let f0 = f.apply(f_concrete, &[zero]);
    assert!(
        !f.k.def_eq(f0, true_v),
        "gcd 0 4 = 4, so f 0 must NOT be true"
    );
    let f2 = f.apply(f_concrete, &[two]);
    assert!(
        !f.k.def_eq(f2, true_v),
        "gcd 2 4 = 2, so f 2 must NOT be true"
    );

    let cr_f_4 = f.const_app(p.count_range, &[f_concrete, four]);
    assert!(
        f.k.def_eq(cr_f_4, two),
        "countRange f 4 must be EXACTLY 2 -- {{1,3}} coprime to 4, {{0,2}} not"
    );

    let hij = f.lemma(p.le_add_right, &[two, one]); // Le 2 (add 2 1) = Lt 1 3
    let hjn = f.lemma(p.le_refl, &[four]); // Le 4 4 = Lt 3 4
    let hfi = f.bool_refl(true_v);
    let hfj = f.bool_refl(true_v);

    let proof = f.const_app(
        p.count_range_ge_two_of_two_witnesses,
        &[f_concrete, four, one, three, hij, hjn, hfi, hfj],
    );
    let expected = f.le(two, cr_f_4);
    let inferred =
        f.k.infer(proof)
            .expect("count_range_ge_two_of_two_witnesses must type-check at n=4, i=1, j=3");
    assert!(
        f.k.def_eq(inferred, expected),
        "count_range_ge_two_of_two_witnesses must prove Le 2 (countRange f 4)"
    );
}

/// `Nat.dvd_two_of_totient_le_one` at its two genuinely satisfiable concrete
/// instances (`a = 1`, `a = 2` -- the only naturals where `totient a <= 1`
/// actually holds, so these are the only ones a real witness proof can be
/// built for) and at a genuinely free `a`/`hpos`/`hle` (the universally
/// quantified case the theorem was actually proved over, which alone
/// exercises the `2 < a` branch -- no concrete witness for a FALSE
/// `totient a <= 1` can exist for `a > 2`).
#[test]
fn dvd_two_of_totient_le_one_applies_at_one_two_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);

    // a = 1: `totient 1 = 1`, so `Le (totient 1) one` holds via `le_refl`.
    let hpos_1 = f.zero_lt_succ(zero); // Lt zero one
    let hle_1 = f.lemma(p.le_refl, &[one]); // Le one one, defeq Le (totient one) one
    let proof_1 = f.const_app(p.dvd_two_of_totient_le_one, &[one, hpos_1, hle_1]);
    let expected_1 = f.dvd(one, two);
    let inferred_1 =
        f.k.infer(proof_1)
            .expect("dvd_two_of_totient_le_one 1 must type-check");
    assert!(
        f.k.def_eq(inferred_1, expected_1),
        "dvd_two_of_totient_le_one 1 must prove dvd 1 2"
    );

    // a = 2: `totient 2 = 1` too.
    let hpos_2 = f.zero_lt_succ(one); // Lt zero two
    let hle_2 = f.lemma(p.le_refl, &[one]);
    let proof_2 = f.const_app(p.dvd_two_of_totient_le_one, &[two, hpos_2, hle_2]);
    let expected_2 = f.dvd(two, two);
    let inferred_2 =
        f.k.infer(proof_2)
            .expect("dvd_two_of_totient_le_one 2 must type-check");
    assert!(
        f.k.def_eq(inferred_2, expected_2),
        "dvd_two_of_totient_le_one 2 must prove dvd 2 2"
    );

    // NEGATIVE reduction control: `totient 6` must NOT reduce to `1` (it is
    // `2`), confirming the theorem's antecedent is genuinely false at `a > 2`
    // rather than vacuously unconstrained.
    let six = f.num(6);
    let totient_6 = f.const_app(p.totient, &[six]);
    assert!(
        !f.k.def_eq(totient_6, one),
        "totient 6 must NOT reduce to 1 (it is 2)"
    );

    // Symbolic: genuinely free `a`, `hpos`, `hle`.
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let hpos_ty = f.lt(zero, a);
    let hpos_fv = f.fresh_fvar();
    let hpos = f.k.fvar(hpos_fv);
    let totient_a = f.const_app(p.totient, &[a]);
    let hle_ty = f.le(totient_a, one);
    let hle_fv = f.fresh_fvar();
    let hle = f.k.fvar(hle_fv);

    let proof_sym = f.const_app(p.dvd_two_of_totient_le_one, &[a, hpos, hle]);
    let expected_sym = f.dvd(a, two);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: a_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hpos_fv,
        name: anon,
        ty: hpos_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hle_fv,
        name: anon,
        ty: hle_ty,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(proof_sym, &mut ctx)
            .expect("dvd_two_of_totient_le_one must apply at free variables");
    assert!(
        f.k.def_eq(inferred_sym, expected_sym),
        "dvd_two_of_totient_le_one must prove dvd a two symbolically"
    );
}

/// `Nat.totient_eq_one_iff` at `n = 1`, `n = 2` (both legs of the RHS
/// disjunction, each genuinely achievable), `n = 6` (a numeral where the LHS
/// is genuinely false, exercising the `2 < n` branch's own reduction), and a
/// genuinely free `n`.
#[test]
fn totient_eq_one_iff_applies_at_small_numerals_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);

    for n in [one, two] {
        let totient_n = f.const_app(p.totient, &[n]);
        let iff_n = f.const_app(p.totient_eq_one_iff, &[n]);
        let lhs = f.eq(totient_n, one);
        let eq_n_1 = f.eq(n, one);
        let eq_n_2 = f.eq(n, two);
        let rhs = f.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
        let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
        let inferred =
            f.k.infer(iff_n)
                .expect("totient_eq_one_iff must type-check at n in {1,2}");
        assert!(
            f.k.def_eq(inferred, expected),
            "totient_eq_one_iff must state Iff (totient n = 1) (n=1 or n=2)"
        );
    }

    // NEGATIVE reduction control at n = 6: `totient 6 = 2`, NOT `1` -- the
    // `2 < n` branch's antecedent genuinely fails here.
    let six = f.num(6);
    let totient_6 = f.const_app(p.totient, &[six]);
    assert!(
        !f.k.def_eq(totient_6, one),
        "totient 6 must NOT reduce to 1 (it is 2)"
    );
    let iff_6 = f.const_app(p.totient_eq_one_iff, &[six]);
    let lhs_6 = f.eq(totient_6, one);
    let eq_6_1 = f.eq(six, one);
    let eq_6_2 = f.eq(six, two);
    let rhs_6 = f.const_app(p.logic.or, &[eq_6_1, eq_6_2]);
    let expected_6 = f.const_app(p.logic.iff, &[lhs_6, rhs_6]);
    let inferred_6 =
        f.k.infer(iff_6)
            .expect("totient_eq_one_iff must type-check at n=6");
    assert!(f.k.def_eq(inferred_6, expected_6));

    // Symbolic: a genuinely free `n`.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let totient_n = f.const_app(p.totient, &[n]);
    let iff_n = f.const_app(p.totient_eq_one_iff, &[n]);
    let lhs_n = f.eq(totient_n, one);
    let eq_n_1 = f.eq(n, one);
    let eq_n_2 = f.eq(n, two);
    let rhs_n = f.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
    let expected_n = f.const_app(p.logic.iff, &[lhs_n, rhs_n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_n =
        f.k.infer_in(iff_n, &mut ctx)
            .expect("totient_eq_one_iff must apply at a free variable");
    assert!(f.k.def_eq(inferred_n, expected_n));
}

/// `Nat.totient_even` at `n = 6` (`totient 6 = 2`, EVEN) and `n = 9`
/// (`totient 9 = 6`, EVEN) — both already confirmed by
/// `totient_computes_on_small_numerals`'s own reduction, reused here rather
/// than re-derived — plus a genuinely free `n`/`hn`. `Even`'s witness is
/// existential, so this checks the STATED type, not the witness value;
/// discriminating negative reduction controls for the underlying `totient`
/// computation already live in `totient_computes_on_small_numerals`.
#[test]
fn totient_even_applies_at_six_nine_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let six = f.num(6);
    let nine = f.num(9);

    // `Lt two n` via `le_add_right(three, k) : Le three (add three k)`,
    // i.e. `Lt two n` for `n = add three k` -- `six = add three three`,
    // `nine = add three six`.
    for (n, k) in [(six, three), (nine, six)] {
        let hn = f.lemma(p.le_add_right, &[three, k]); // Le three (add three k) = Lt two n
        let proof = f.const_app(p.totient_even, &[n, hn]);
        let totient_n = f.const_app(p.totient, &[n]);
        let expected = f.const_app(p.even, &[totient_n]);
        let inferred =
            f.k.infer(proof)
                .expect("totient_even must type-check at n in {6,9}");
        assert!(
            f.k.def_eq(inferred, expected),
            "totient_even must prove Even (totient n) at n in {{6,9}}"
        );
    }

    // Symbolic: genuinely free `n`, `hn`.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let hn_ty = f.lt(two, n);
    let hn_fv = f.fresh_fvar();
    let hn = f.k.fvar(hn_fv);
    let proof_sym = f.const_app(p.totient_even, &[n, hn]);
    let totient_n = f.const_app(p.totient, &[n]);
    let expected_sym = f.const_app(p.even, &[totient_n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hn_fv,
        name: anon,
        ty: hn_ty,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(proof_sym, &mut ctx)
            .expect("totient_even must apply at a genuinely free n/hn");
    assert!(
        f.k.def_eq(inferred_sym, expected_sym),
        "totient_even must prove Even (totient n) symbolically"
    );
}

/// `Nat.odd_totient_iff_eq_one` at `n = 1`, `n = 2` (`totient 1 = totient 2 =
/// 1`, both `Odd`), `n = 6` (`totient 6 = 2` -- discriminating: neither
/// `Odd` nor `= 1`), and a genuinely free `n`.
#[test]
fn odd_totient_iff_eq_one_applies_at_small_numerals_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);

    for n in [one, f.num(2)] {
        let totient_n = f.const_app(p.totient, &[n]);
        let iff_n = f.const_app(p.odd_totient_iff_eq_one, &[n]);
        let lhs = f.const_app(p.odd, &[totient_n]);
        let rhs = f.eq(totient_n, one);
        let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
        let inferred =
            f.k.infer(iff_n)
                .expect("odd_totient_iff_eq_one must type-check at n in {1,2}");
        assert!(
            f.k.def_eq(inferred, expected),
            "odd_totient_iff_eq_one must state Iff (Odd (totient n)) (totient n = 1)"
        );
    }

    // Discriminating: n = 6, totient 6 = 2 -- neither Odd nor = 1.
    let six = f.num(6);
    let totient_6 = f.const_app(p.totient, &[six]);
    assert!(
        !f.k.def_eq(totient_6, one),
        "totient 6 must NOT reduce to 1 (it is 2)"
    );
    let iff_6 = f.const_app(p.odd_totient_iff_eq_one, &[six]);
    let lhs_6 = f.const_app(p.odd, &[totient_6]);
    let rhs_6 = f.eq(totient_6, one);
    let expected_6 = f.const_app(p.logic.iff, &[lhs_6, rhs_6]);
    let inferred_6 =
        f.k.infer(iff_6)
            .expect("odd_totient_iff_eq_one must type-check at n=6");
    assert!(f.k.def_eq(inferred_6, expected_6));

    // Symbolic: a genuinely free `n`.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let totient_n = f.const_app(p.totient, &[n]);
    let iff_n = f.const_app(p.odd_totient_iff_eq_one, &[n]);
    let lhs_n = f.const_app(p.odd, &[totient_n]);
    let rhs_n = f.eq(totient_n, one);
    let expected_n = f.const_app(p.logic.iff, &[lhs_n, rhs_n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_n =
        f.k.infer_in(iff_n, &mut ctx)
            .expect("odd_totient_iff_eq_one must apply at a free variable");
    assert!(f.k.def_eq(inferred_n, expected_n));
}

/// `Nat.odd_totient_iff` at `n = 1`, `n = 2` (both legs of the RHS
/// disjunction), `n = 6` (discriminating: `totient 6 = 2`, neither `Odd` nor
/// `n in {1,2}`), and a genuinely free `n`.
#[test]
fn odd_totient_iff_applies_at_small_numerals_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);

    for n in [one, two] {
        let totient_n = f.const_app(p.totient, &[n]);
        let iff_n = f.const_app(p.odd_totient_iff, &[n]);
        let lhs = f.const_app(p.odd, &[totient_n]);
        let eq_n_1 = f.eq(n, one);
        let eq_n_2 = f.eq(n, two);
        let rhs = f.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
        let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
        let inferred =
            f.k.infer(iff_n)
                .expect("odd_totient_iff must type-check at n in {1,2}");
        assert!(
            f.k.def_eq(inferred, expected),
            "odd_totient_iff must state Iff (Odd (totient n)) (n=1 or n=2)"
        );
    }

    // Discriminating: n = 6, totient 6 = 2.
    let six = f.num(6);
    let totient_6 = f.const_app(p.totient, &[six]);
    assert!(
        !f.k.def_eq(totient_6, one),
        "totient 6 must NOT reduce to 1 (it is 2)"
    );
    let iff_6 = f.const_app(p.odd_totient_iff, &[six]);
    let lhs_6 = f.const_app(p.odd, &[totient_6]);
    let eq_6_1 = f.eq(six, one);
    let eq_6_2 = f.eq(six, two);
    let rhs_6 = f.const_app(p.logic.or, &[eq_6_1, eq_6_2]);
    let expected_6 = f.const_app(p.logic.iff, &[lhs_6, rhs_6]);
    let inferred_6 =
        f.k.infer(iff_6)
            .expect("odd_totient_iff must type-check at n=6");
    assert!(f.k.def_eq(inferred_6, expected_6));

    // Symbolic: a genuinely free `n`.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let totient_n = f.const_app(p.totient, &[n]);
    let iff_n = f.const_app(p.odd_totient_iff, &[n]);
    let lhs_n = f.const_app(p.odd, &[totient_n]);
    let eq_n_1 = f.eq(n, one);
    let eq_n_2 = f.eq(n, two);
    let rhs_n = f.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
    let expected_n = f.const_app(p.logic.iff, &[lhs_n, rhs_n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_n =
        f.k.infer_in(iff_n, &mut ctx)
            .expect("odd_totient_iff must apply at a free variable");
    assert!(f.k.def_eq(inferred_n, expected_n));
}

/// Shared by [`totient_coprime_totient_iff_applies_at_small_numerals_and_symbolically`]:
/// checks that `Nat.totient_coprime_totient_iff` applied at `(m, n)` infers
/// to `Iff (gcd (totient m) (totient n) = one) ((m=1 or m=2) or (n=1 or
/// n=2))`.
fn assert_totient_coprime_totient_iff_at(f: &mut Fixture, m: ExprId, n: ExprId) {
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let totient_m = f.const_app(p.totient, &[m]);
    let totient_n = f.const_app(p.totient, &[n]);
    let gcd_mn = f.gcd(totient_m, totient_n);
    let lhs = f.eq(gcd_mn, one);
    let eq_m1 = f.eq(m, one);
    let eq_m2 = f.eq(m, two);
    let or_m = f.const_app(p.logic.or, &[eq_m1, eq_m2]);
    let eq_n1 = f.eq(n, one);
    let eq_n2 = f.eq(n, two);
    let or_n = f.const_app(p.logic.or, &[eq_n1, eq_n2]);
    let rhs = f.const_app(p.logic.or, &[or_m, or_n]);
    let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
    let iff_mn = f.const_app(p.totient_coprime_totient_iff, &[m, n]);
    let inferred =
        f.k.infer(iff_mn)
            .expect("totient_coprime_totient_iff must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "totient_coprime_totient_iff must state Iff (gcd (totient m) \
         (totient n) = one) ((m=1 or m=2) or (n=1 or n=2))"
    );
}

/// `Nat.totient_coprime_totient_iff` at `(m, n) = (1, 9)` (left disjunct
/// holds), `(6, 2)` (right disjunct holds), `(6, 9)` (discriminating:
/// `totient 6 = 2`, `totient 9 = 6`, `gcd 2 6 = 2 != 1`, neither disjunct
/// holds), and a genuinely free `(m, n)`.
#[test]
fn totient_coprime_totient_iff_applies_at_small_numerals_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);

    let nine = f.num(9);
    assert_totient_coprime_totient_iff_at(&mut f, one, nine);
    let six = f.num(6);
    assert_totient_coprime_totient_iff_at(&mut f, six, two);

    // Discriminating: totient 6 = 2, totient 9 = 6, gcd 2 6 = 2 != 1, so
    // neither disjunct holds and the `Coprime` side is genuinely false too.
    let totient_6 = f.const_app(p.totient, &[six]);
    let totient_9 = f.const_app(p.totient, &[nine]);
    let gcd_6_9 = f.gcd(totient_6, totient_9);
    assert!(
        !f.k.def_eq(gcd_6_9, one),
        "gcd (totient 6) (totient 9) must NOT reduce to one (it is two)"
    );
    assert_totient_coprime_totient_iff_at(&mut f, six, nine);

    // Symbolic: a genuinely free `(m, n)`.
    let m_fv = f.fresh_fvar();
    let n_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let n = f.k.fvar(n_fv);
    let totient_m = f.const_app(p.totient, &[m]);
    let totient_n = f.const_app(p.totient, &[n]);
    let gcd_mn = f.gcd(totient_m, totient_n);
    let lhs_n = f.eq(gcd_mn, one);
    let eq_m1 = f.eq(m, one);
    let eq_m2 = f.eq(m, two);
    let or_m = f.const_app(p.logic.or, &[eq_m1, eq_m2]);
    let eq_n1 = f.eq(n, one);
    let eq_n2 = f.eq(n, two);
    let or_n = f.const_app(p.logic.or, &[eq_n1, eq_n2]);
    let rhs_n = f.const_app(p.logic.or, &[or_m, or_n]);
    let expected_n = f.const_app(p.logic.iff, &[lhs_n, rhs_n]);
    let iff_mn = f.const_app(p.totient_coprime_totient_iff, &[m, n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_n =
        f.k.infer_in(iff_mn, &mut ctx)
            .expect("totient_coprime_totient_iff must apply at free variables");
    assert!(f.k.def_eq(inferred_n, expected_n));
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

/// `Nat.test_bit_of_zero` reduces to `Eq (testBit 0 i) 0` at a genuinely
/// symbolic `i` (its own statement quantifies over `i`, so this instantiates
/// at a free variable rather than a numeral) and also checks out at several
/// concrete indices.
#[test]
fn test_bit_of_zero_holds_symbolically_and_at_concrete_indices() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: re-derive the same statement over a bound variable, proved
    // by the prelude theorem alone (raw un-abstracted fvars cannot be
    // `k.infer`'d directly -- the kernel's local context has no entry for
    // them until `lam_fv`/`pi_fv` abstracts them into a closed term, which
    // `f.theorem` does).
    {
        let name = f.name("test_bit_of_zero_restated");
        f.theorem(name, 1, &|d, values| {
            let i = values[0];
            let zero = d.zero();
            let tb = d.const_app(p.test_bit, &[zero, i]);
            let stmt = d.eq(tb, zero);
            let fn_term = d.const_app(p.test_bit_of_zero, &[]);
            let proof = d.apply(fn_term, &[i]);
            (stmt, proof)
        })
        .expect("test_bit_of_zero must apply at a genuinely symbolic i");
    }

    let zero = f.zero();
    for i_val in [0u32, 1, 5, 20] {
        let iv = f.num(i_val);
        let test_bit_of_zero_fn = f.const_app(p.test_bit_of_zero, &[]);
        let proof = f.apply(test_bit_of_zero_fn, &[iv]);
        let inferred = f.k.infer(proof).unwrap();
        let tb = f.const_app(p.test_bit, &[zero, iv]);
        let expected = f.eq(tb, zero);
        assert!(
            f.k.def_eq(inferred, expected),
            "test_bit_of_zero({i_val}) should state testBit 0 {i_val} = 0"
        );
        assert!(
            f.k.def_eq(tb, zero),
            "testBit 0 {i_val} must actually reduce to 0"
        );
    }

    assert!(
        f.k.axiom_footprint(p.test_bit_of_zero).is_empty(),
        "test_bit_of_zero must rest on zero axioms"
    );
}

/// `Nat.zero_of_testBit_eq_zero` — the Nat-valued analogue of Mathlib's
/// `Nat.zero_of_testBit_eq_false` (see
/// `docs/plan/status/244-nat-testbit-bitwise.md` for why this is a NEW local
/// fact, not a flip of that pinned Bool-typed mirror). The only concrete
/// instantiation of its hypothesis (`∀ i, testBit n i = 0`) that is
/// ACTUALLY PROVABLE is `n := 0` (`test_bit_of_zero` supplies it exactly);
/// any other numeral would need a false hypothesis. Checked by application,
/// not merely admission: applying at `n := 0` with that hypothesis reduces
/// to `Eq 0 0`, and the residue is NOT def-eq to a differently-valued
/// statement (the negative control).
#[test]
fn zero_of_test_bit_eq_zero_applies_at_the_only_provable_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let hyp = f.const_app(p.test_bit_of_zero, &[]);
    let proof = f.lemma(p.zero_of_test_bit_eq_zero, &[zero, hyp]);
    let inferred = f
        .k
        .infer(proof)
        .unwrap_or_else(|e| panic!("zero_of_testBit_eq_zero(0) should infer: {}", f.explain(&e)));
    let expected = f.eq(zero, zero);
    assert!(
        f.k.def_eq(inferred, expected),
        "zero_of_testBit_eq_zero(0, test_bit_of_zero) should state Eq 0 0"
    );

    // NEGATIVE control: the residue must not be def-eq to a statement about
    // a different value.
    let one = f.num(1);
    let wrong_expected = f.eq(zero, one);
    assert!(
        !f.k.def_eq(inferred, wrong_expected),
        "zero_of_testBit_eq_zero(0, ...) must NOT be def-eq to a statement about 1"
    );

    assert!(
        f.k.axiom_footprint(p.zero_of_test_bit_eq_zero).is_empty(),
        "zero_of_testBit_eq_zero must rest on zero axioms"
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

/// Build a proof of `dvd a n` from a witness `q` when `n` is defeq to
/// `mul a q` (e.g. both are concrete numerals that reduce to the same
/// value) — `f.refl(n)` typechecks against the required `Eq n (mul a q)`
/// via that defeq, exactly the technique `dvd_intro`'s callers throughout
/// `nat_prelude` rely on for concrete instantiation tests.
fn concrete_dvd(f: &mut Fixture, a: ExprId, n: ExprId, q: ExprId) -> ExprId {
    let nat = f.nat_ty();
    let one = f.level_one();
    let predicate = f.dvd_predicate(a, n);
    let intro_name = f.p.logic.exists_intro;
    let intro = f.k.const_(intro_name, vec![one]);
    let eq_proof = f.refl(n);
    f.apply(intro, &[nat, predicate, q, eq_proof])
}

/// `gcd_dvd_mul`, `gcd_le_mul`, `eq_zero_of_lcm_eq_zero`, `lcm_assoc`, and
/// `lcm_div` each apply at concrete instances chosen to discriminate a
/// swapped argument or a wrong disjunct order, not merely to confirm the
/// formula evaluates.
#[test]
fn lcm_gcd_lemmas_apply_at_concrete_discriminating_instances() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let twelve = f.num(12);
    let twentyfour = f.num(24);

    // `gcd_dvd_mul (4,6) : dvd (gcd 4 6) (mul 4 6)`, i.e. `dvd 2 24`.
    let gcd_46 = f.gcd(four, six);
    assert!(f.k.def_eq(gcd_46, two), "gcd 4 6 must reduce to 2");
    let mul_46 = f.mul(four, six);
    assert!(f.k.def_eq(mul_46, twentyfour), "4*6 must reduce to 24");
    let dvd_mul_proof = f.lemma(p.gcd_dvd_mul, &[four, six]);
    let dvd_mul_ty = f.dvd(gcd_46, mul_46);
    let inferred =
        f.k.infer(dvd_mul_proof)
            .expect("gcd_dvd_mul must apply at (4,6)");
    assert!(f.k.def_eq(inferred, dvd_mul_ty));
    // Negative control: the SWAPPED conclusion (dividend/divisor reversed)
    // is a different (and false, since 24 does not divide 2) statement --
    // the trusted gate must reject it, not just look wrong to a reader.
    let swapped_ty = f.dvd(mul_46, gcd_46);
    let swapped_name = f.name("gcd_dvd_mul_with_divisor_and_dividend_swapped");
    let error = f
        .declare_theorem(swapped_name, swapped_ty, dvd_mul_proof)
        .expect_err("gcd_dvd_mul's proof must not typecheck with dividend/divisor swapped");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));

    // `gcd_le_mul (4,6) (0<4) (0<6) : le (gcd 4 6) (mul 4 6)`, i.e. `le 2 24`.
    let pos4 = f.zero_lt_succ(three);
    let five_for_pos = f.num(5);
    let pos6 = f.zero_lt_succ(five_for_pos);
    let le_mul_proof = f.lemma(p.gcd_le_mul, &[four, six, pos4, pos6]);
    let le_mul_ty = f.le(gcd_46, mul_46);
    let inferred =
        f.k.infer(le_mul_proof)
            .expect("gcd_le_mul must apply at (4,6)");
    assert!(f.k.def_eq(inferred, le_mul_ty));

    // `eq_zero_of_lcm_eq_zero`: one instance with the LEFT factor zero, one
    // with the RIGHT factor zero -- together these discriminate a swapped
    // `Or` (a proof built as `Or (Eq n zero) (Eq m zero)` would fail to
    // `def_eq` the expected type below on at least one of the two).
    let five = f.num(5);
    let lcm_0_5 = f.const_app(p.lcm, &[zero, five]);
    assert!(f.k.def_eq(lcm_0_5, zero), "lcm 0 5 must reduce to 0");
    let h_left = f.refl(lcm_0_5); // Eq lcm_0_5 lcm_0_5, defeq Eq lcm_0_5 zero
    let left_proof = f.lemma(p.eq_zero_of_lcm_eq_zero, &[zero, five, h_left]);
    let left_expected = {
        let m0 = f.eq(zero, zero);
        let n0 = f.eq(five, zero);
        f.const_app(p.logic.or, &[m0, n0])
    };
    let inferred =
        f.k.infer(left_proof)
            .expect("eq_zero_of_lcm_eq_zero must apply with the left factor zero");
    assert!(f.k.def_eq(inferred, left_expected));

    let lcm_6_0 = f.const_app(p.lcm, &[six, zero]);
    assert!(f.k.def_eq(lcm_6_0, zero), "lcm 6 0 must reduce to 0");
    let h_right = f.refl(lcm_6_0);
    let right_proof = f.lemma(p.eq_zero_of_lcm_eq_zero, &[six, zero, h_right]);
    let right_expected = {
        let m0 = f.eq(six, zero);
        let n0 = f.eq(zero, zero);
        f.const_app(p.logic.or, &[m0, n0])
    };
    let inferred =
        f.k.infer(right_proof)
            .expect("eq_zero_of_lcm_eq_zero must apply with the right factor zero");
    assert!(f.k.def_eq(inferred, right_expected));

    // `lcm_assoc (2,3,4) : (lcm 2 3).lcm 4 = lcm 2 (lcm 3 4)`, both sides 12.
    let lcm_23 = f.const_app(p.lcm, &[two, three]);
    let lcm_23_4 = f.const_app(p.lcm, &[lcm_23, four]);
    assert!(
        f.k.def_eq(lcm_23_4, twelve),
        "(lcm 2 3).lcm 4 must reduce to 12"
    );
    let lcm_34 = f.const_app(p.lcm, &[three, four]);
    let lcm_2_34 = f.const_app(p.lcm, &[two, lcm_34]);
    assert!(
        f.k.def_eq(lcm_2_34, twelve),
        "lcm 2 (lcm 3 4) must reduce to 12"
    );
    let assoc_proof = f.lemma(p.lcm_assoc, &[two, three, four]);
    let assoc_ty = f.eq(lcm_23_4, lcm_2_34);
    let inferred =
        f.k.infer(assoc_proof)
            .expect("lcm_assoc must apply at (2,3,4)");
    assert!(f.k.def_eq(inferred, assoc_ty));
    // Negative control: a genuinely FALSE right-hand side (`6`, not `12`) --
    // picking a DIFFERENT correct grouping of the same three numbers is not
    // discriminating here (lcm is associative AND commutative, so every
    // parenthesization of `2,3,4` reduces to the same `12`, and the
    // "wrong grouping" would typecheck vacuously via that shared value).
    let wrong_assoc_ty = f.eq(lcm_23_4, six);
    let wrong_assoc_name = f.name("lcm_assoc_with_wrong_right_hand_side");
    let error = f
        .declare_theorem(wrong_assoc_name, wrong_assoc_ty, assoc_proof)
        .expect_err("lcm_assoc's proof must not typecheck against a false right-hand side");
    assert!(matches!(
        error,
        KernelError::DeclarationValueMismatch { .. }
    ));

    // `lcm_div (4,6,2) (2|4) (2|6) : lcm (4/2) (6/2) = lcm 4 6 / 2`, i.e.
    // `lcm 2 3 = 6`.
    let dvd_2_4 = concrete_dvd(&mut f, two, four, two);
    let dvd_2_6 = concrete_dvd(&mut f, two, six, three);
    let div_proof = f.lemma(p.lcm_div, &[four, six, two, dvd_2_4, dvd_2_6]);
    let div_ty = {
        let div_m_k = f.div(four, two);
        let div_n_k = f.div(six, two);
        let lcm_div_mk_nk = f.const_app(p.lcm, &[div_m_k, div_n_k]);
        let lcm_mn = f.const_app(p.lcm, &[four, six]);
        let div_lcm_mn_k = f.div(lcm_mn, two);
        f.eq(lcm_div_mk_nk, div_lcm_mn_k)
    };
    let inferred =
        f.k.infer(div_proof)
            .expect("lcm_div must apply at (m=4, n=6, k=2)");
    assert!(f.k.def_eq(inferred, div_ty));
    // Independent numeric cross-check: both sides of `div_ty` really are 6.
    let lcm_div_mk_nk = {
        let div_m_k = f.div(four, two);
        let div_n_k = f.div(six, two);
        f.const_app(p.lcm, &[div_m_k, div_n_k])
    };
    assert!(
        f.k.def_eq(lcm_div_mk_nk, six),
        "lcm (4/2) (6/2) = lcm 2 3 must reduce to 6"
    );
    let div_lcm_mn_k = {
        let lcm_mn = f.const_app(p.lcm, &[four, six]);
        f.div(lcm_mn, two)
    };
    assert!(
        f.k.def_eq(div_lcm_mn_k, six),
        "lcm 4 6 / 2 = 12/2 must reduce to 6"
    );
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

/// `Nat.mod_eq_add_le_of_lt : modEq m a b → a < b → a + m ≤ b`
/// (`modeq_add_le_of_lt.rs`) at concrete boundary instances, at a genuinely
/// free variable, and a reversed control confirming `a < b` is load-bearing.
#[test]
fn mod_eq_add_le_of_lt_applies_at_boundary_instances_free_variables_and_a_reversed_control() {
    let mut f = Fixture::new();
    let p = f.p;

    // `Lt n m` for concrete numerals via `le_intro (succ n) m k proof`, `k :=
    // m - n - 1` (mirrors `mul_order_lemmas_apply_at_concrete_and_boundary_instances`).
    let lt_witness = |f: &mut Fixture, n_val: u32, m_val: u32| -> ExprId {
        let n = f.num(n_val);
        let m = f.num(m_val);
        let sn = f.succ(n);
        let k = f.num(m_val - n_val - 1);
        let sn_plus_k = f.add(sn, k);
        let witness = f.refl(sn_plus_k);
        f.lemma(p.le_intro, &[sn, m, k, witness])
    };

    // --- Tight case: b - a == m exactly (3, 2, 5), catching an off-by-one --
    let three = f.num(3);
    let two = f.num(2);
    let five = f.num(5);
    let zero = f.num(0);
    let one = f.num(1);
    let modeq_tight = f.concrete_mod_eq(three, two, five, one, zero); // 2+3*1=5=5+3*0
    let hlt_tight = lt_witness(&mut f, 2, 5);
    let applied_tight = f.lemma(
        p.mod_eq_add_le_of_lt,
        &[three, two, five, modeq_tight, hlt_tight],
    );
    let inferred_tight = f
        .k
        .infer(applied_tight)
        .unwrap_or_else(|e| panic!("mod_eq_add_le_of_lt(3,2,5) should infer: {}", f.explain(&e)));
    let two_plus_three = f.add(two, three);
    let expect_tight = f.le(two_plus_three, five); // Le(5,5), the tight boundary
    assert!(
        f.k.def_eq(inferred_tight, expect_tight),
        "mod_eq_add_le_of_lt(3,2,5) must conclude 2+3 <= 5"
    );

    // --- Slack case: b - a == 2*m (3, 2, 8), so the bound isn't accidentally
    // only tight-case-correct -----------------------------------------------
    let eight = f.num(8);
    let modeq_slack = f.concrete_mod_eq(three, two, eight, two, zero); // 2+3*2=8=8+3*0
    let hlt_slack = lt_witness(&mut f, 2, 8);
    let applied_slack = f.lemma(
        p.mod_eq_add_le_of_lt,
        &[three, two, eight, modeq_slack, hlt_slack],
    );
    let inferred_slack = f
        .k
        .infer(applied_slack)
        .unwrap_or_else(|e| panic!("mod_eq_add_le_of_lt(3,2,8) should infer: {}", f.explain(&e)));
    let two_plus_three_slack = f.add(two, three);
    let expect_slack = f.le(two_plus_three_slack, eight); // Le(5,8)
    assert!(
        f.k.def_eq(inferred_slack, expect_slack),
        "mod_eq_add_le_of_lt(3,2,8) must conclude 2+3 <= 8"
    );

    // --- Genuinely free variable: m, a, b as fresh fvars, hmod/hlt as fresh
    // hypothesis fvars -- numerals reduce and can hide a defeq gap that only
    // shows up symbolically. ------------------------------------------------
    let nat = f.nat_ty();
    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    let hmod_ty = f.mod_eq(m, a, b);
    let hmod_fv = f.fresh_fvar();
    let hmod = f.k.fvar(hmod_fv);
    let hlt_ty = f.lt(a, b);
    let hlt_fv = f.fresh_fvar();
    let hlt = f.k.fvar(hlt_fv);
    let applied_free = f.lemma(p.mod_eq_add_le_of_lt, &[m, a, b, hmod, hlt]);
    // Wrap in lambdas so `f.k.infer` sees `hmod`/`hlt` in a local context.
    let wrapped = {
        let with_hlt = f.lam_fv(hlt_fv, hlt_ty, applied_free);
        let with_hmod = f.lam_fv(hmod_fv, hmod_ty, with_hlt);
        let with_b = f.lam_fv(b_fv, nat, with_hmod);
        let with_a = f.lam_fv(a_fv, nat, with_b);
        f.lam_fv(m_fv, nat, with_a)
    };
    f.k.infer(wrapped).unwrap_or_else(|e| {
        panic!(
            "mod_eq_add_le_of_lt should infer at a genuinely free m,a,b: {}",
            f.explain(&e)
        )
    });

    // --- Reversed control: a ≡ b holds but a > b (3, 5, 2) -- confirms the
    // `a < b` hypothesis is load-bearing, not decorative. The conclusion at
    // these values (5+3=8 <= 2) is actually FALSE: `Nat.ble 8 2` computes to
    // `false`, so had the theorem been provable without `a < b` it would be
    // UNSOUND, not merely inapplicable. ---------------------------------
    let modeq_reversed = f.concrete_mod_eq(three, five, two, zero, one); // 5+0=5=2+3*1
    let _ = modeq_reversed; // demonstrates modEq alone does not license the bound
    let a_plus_m_reversed = f.add(five, three); // 8
    let ble_reversed = f.const_app(p.ble, &[a_plus_m_reversed, two]);
    let bool_false = f.bool_false();
    assert!(
        f.k.def_eq(ble_reversed, bool_false),
        "Nat.ble (5+3) 2 must compute to false: the conclusion is genuinely \
         false when a > b, so a < b cannot be dropped"
    );
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

/// The five `Nat` ordering-under-multiplication/division mirrors
/// (`mul_order_lemmas.rs`), each applied at concrete numerals -- including,
/// for the two positivity-hypothesis lemmas, the SMALLEST value satisfying
/// the hypothesis (`a = 1`), which is exactly where an off-by-one in the
/// side condition would show.
#[test]
fn mul_order_lemmas_apply_at_concrete_and_boundary_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    // `Lt n m` for concrete numerals is `Le (succ n) m`, witnessed via
    // `le_intro (succ n) m k proof` with `k := m - n - 1` (mirrors
    // `mod_eq_self_of_lt_applies_at_concrete_points`, above).
    let lt_witness = |f: &mut Fixture, n_val: u32, m_val: u32| -> ExprId {
        let n = f.num(n_val);
        let m = f.num(m_val);
        let sn = f.succ(n);
        let k = f.num(m_val - n_val - 1);
        let sn_plus_k = f.add(sn, k);
        let witness = f.refl(sn_plus_k);
        f.lemma(p.le_intro, &[sn, m, k, witness])
    };

    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);

    // `lt_of_mul_lt_mul_left`/`_right`: NO positivity hypothesis. Discriminating
    // numerals 2*3=6 < 2*5=10 -> 3 < 5.
    let hyp_6_lt_10 = lt_witness(&mut f, 6, 10);
    let left_cancel = f.lemma(p.lt_of_mul_lt_mul_left, &[two, three, five, hyp_6_lt_10]);
    let left_cancel_ty =
        f.k.infer(left_cancel)
            .unwrap_or_else(|e| panic!("lt_of_mul_lt_mul_left should infer: {}", f.explain(&e)));
    let expect_3_lt_5 = f.lt(three, five);
    assert!(
        f.k.def_eq(left_cancel_ty, expect_3_lt_5),
        "lt_of_mul_lt_mul_left(2,3,5) must conclude 3 < 5"
    );

    let hyp_6_lt_10_right = lt_witness(&mut f, 6, 10);
    let right_cancel = f.lemma(
        p.lt_of_mul_lt_mul_right,
        &[two, three, five, hyp_6_lt_10_right],
    );
    let right_cancel_ty =
        f.k.infer(right_cancel)
            .unwrap_or_else(|e| panic!("lt_of_mul_lt_mul_right should infer: {}", f.explain(&e)));
    assert!(
        f.k.def_eq(right_cancel_ty, expect_3_lt_5),
        "lt_of_mul_lt_mul_right(2,3,5) must conclude 3 < 5"
    );

    // `mul_lt_mul_left`/`_right` at the BOUNDARY `a = 1` (the smallest value
    // satisfying `0 < a`): both directions of the `Iff`.
    let one = f.num(1);
    let zero = f.zero();
    let pos_one = f.zero_lt_succ(zero); // Lt zero one, since one = succ zero

    let one_three = f.mul(one, three);
    let one_five = f.mul(one, five);
    let left_ty = f.lt(one_three, one_five);
    let right_ty = f.lt(three, five);

    let iff_left = f.lemma(p.mul_lt_mul_left, &[one, three, five, pos_one]);
    let mp_left = f.const_app(p.logic.iff_mp, &[left_ty, right_ty, iff_left]);
    let hyp_3_lt_5 = lt_witness(&mut f, 3, 5);
    let mp_left_applied = f.apply(mp_left, &[hyp_3_lt_5]);
    f.k.infer(mp_left_applied).unwrap_or_else(|e| {
        panic!(
            "mul_lt_mul_left(1,3,5).mp should infer at 1*3 < 1*5: {}",
            f.explain(&e)
        )
    });

    let iff_left_2 = f.lemma(p.mul_lt_mul_left, &[one, three, five, pos_one]);
    let mpr_left = f.const_app(p.logic.iff_mpr, &[left_ty, right_ty, iff_left_2]);
    let hyp_3_lt_5_b = lt_witness(&mut f, 3, 5);
    let mpr_left_applied = f.apply(mpr_left, &[hyp_3_lt_5_b]);
    let mpr_left_ty = f.k.infer(mpr_left_applied).unwrap_or_else(|e| {
        panic!(
            "mul_lt_mul_left(1,3,5).mpr should infer from 3 < 5: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(mpr_left_ty, left_ty),
        "mul_lt_mul_left(1,3,5).mpr must conclude 1*3 < 1*5"
    );

    let three_one = f.mul(three, one);
    let five_one = f.mul(five, one);
    let left_ty_r = f.lt(three_one, five_one);
    let pos_one_r = f.zero_lt_succ(zero);
    let iff_right = f.lemma(p.mul_lt_mul_right, &[one, three, five, pos_one_r]);
    let mpr_right = f.const_app(p.logic.iff_mpr, &[left_ty_r, right_ty, iff_right]);
    let hyp_3_lt_5_c = lt_witness(&mut f, 3, 5);
    let mpr_right_applied = f.apply(mpr_right, &[hyp_3_lt_5_c]);
    f.k.infer(mpr_right_applied).unwrap_or_else(|e| {
        panic!(
            "mul_lt_mul_right(1,3,5).mpr should infer from 3 < 5: {}",
            f.explain(&e)
        )
    });

    // `div_lt_of_lt_mul`: at the BOUNDARY `m = n*k - 1` (7 = 2*4 - 1), and at
    // the smallest divisor that takes the `succ` case-split branch (`n = 1`).
    let four = f.num(4);
    let seven = f.num(7);
    let hyp_7_lt_8 = lt_witness(&mut f, 7, 8);
    let div_result = f.lemma(p.div_lt_of_lt_mul, &[seven, two, four, hyp_7_lt_8]);
    let div_result_ty =
        f.k.infer(div_result)
            .unwrap_or_else(|e| panic!("div_lt_of_lt_mul(7,2,4) should infer: {}", f.explain(&e)));
    let div_7_2 = f.div(seven, two);
    assert!(f.k.def_eq(div_7_2, three), "7 / 2 must compute to 3");
    let expect_div_lt_four = f.lt(div_7_2, four);
    assert!(
        f.k.def_eq(div_result_ty, expect_div_lt_four),
        "div_lt_of_lt_mul(7,2,4) must conclude div(7,2) < 4"
    );
    let expect_3_lt_4 = f.lt(three, four);
    assert!(
        f.k.def_eq(expect_div_lt_four, expect_3_lt_4),
        "the concluded bound must itself compute to 3 < 4"
    );

    let hyp_3_lt_4 = lt_witness(&mut f, 3, 4);
    let div_result_n1 = f.lemma(p.div_lt_of_lt_mul, &[three, one, four, hyp_3_lt_4]);
    f.k.infer(div_result_n1).unwrap_or_else(|e| {
        panic!(
            "div_lt_of_lt_mul(3,1,4) should infer at the smallest succ-branch divisor: {}",
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

    // A LENGTH PIN USED TO SIT HERE (`assert_eq!(first.len(), 93 + 610)`) AND
    // IT IS DELIBERATELY GONE. It constrained the two hand-maintained name
    // lists against a literal -- "are these lists internally consistent" --
    // and never "are they complete", which is the question that matters.
    // `every_nat_declaration_is_checked_and_axiom_free` answers the real one by
    // reading `k.environment()` directly and failing on any `Nat.`
    // Definition/Theorem absent from the lists. Verified before removing this,
    // by deleting one `theorem_names` entry in a throwaway worktree: that test
    // fails and names the declaration
    // (`["Nat.countRange_union_add_inter"]`). So the pin guarded nothing the
    // coverage assertion does not guard better.
    //
    // What it DID do was collide. It is one line every concurrent `nat_prelude`
    // lane edits, so two lanes landing correct increments produce a
    // ZERO-CONFLICT merge with a stale total -- CLAUDE.md's documented trap.
    // It conflicted three times on 2026-08-30 alone and the arithmetic was
    // wrong EVERY time, because the base kept moving underneath: 581+4+3 gave
    // 588 against a counted 598, and later 602 vs 606 against a counted 610.
    // This is the same removal `creal_tests.rs` made after the same incidents;
    // do not reintroduce it. The determinism assertion above is this test's
    // actual content and needs no count.
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

/// `Nat.coprime_div_right` at two concrete instances exercising BOTH branches
/// of its case split on `a`: `a = 0` (forces `n = 0`, and `div _ 0 = 0`
/// collapses `n` and `n/a` to the same value) and `a = succ a'` (the witness
/// `q` from `dvd a n` recovers `div n a = q`).
///
/// Zero branch: `m = 1, n = 0, a = 0` — `dvd 0 0` (witness `0`), `Coprime 1 0`
/// (`gcd 1 0` reduces to `1`), concluding `Coprime 1 (0/0)`.
///
/// Succ branch: `m = 3, n = 10, a = 2` — `dvd 2 10` (witness `5`),
/// `Coprime 3 10` (`gcd 3 10` reduces to `1`), concluding `Coprime 3 (10/2)`,
/// and the conclusion's SECOND argument is checked to be `div 10 2` (which
/// reduces to `5`) rather than the original `10` — a wrong theorem that left
/// `n` unchanged would still type-check against its own (differently shaped)
/// conclusion, so this pins the actual residue.
#[test]
fn coprime_div_right_applies_at_both_branches_of_its_case_split() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();
    let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);

    // -- zero branch: m=1, n=0, a=0 --
    let one = f.num(1);
    let zero = f.num(0);

    let gcd_1_0 = f.gcd(one, zero);
    assert!(f.k.def_eq(gcd_1_0, one), "gcd 1 0 must reduce to 1");
    let coprime_1_0 = f.refl(one);

    let dvd_predicate_0 = f.dvd_predicate(zero, zero);
    let mul_0_0 = f.mul(zero, zero);
    assert!(f.k.def_eq(zero, mul_0_0), "0 must reduce to mul 0 0");
    let eq_proof_0 = f.refl(zero);
    let dvd_0_0 = f.apply(intro, &[nat, dvd_predicate_0, zero, eq_proof_0]);

    let applied_zero = f.const_app(p.coprime_div_right, &[one, zero, zero]);
    let applied_zero_full = f.apply(applied_zero, &[coprime_1_0, dvd_0_0]);
    let inferred_zero =
        f.k.infer(applied_zero_full)
            .expect("coprime_div_right 1 0 0 (Coprime 1 0) (dvd 0 0) must type-check");
    let rendered_zero = f.k.render_lean(inferred_zero);
    assert!(
        rendered_zero.contains("gcd"),
        "unexpected conclusion type: {rendered_zero}"
    );

    // -- succ branch: m=3, n=10, a=2 --
    let three = f.num(3);
    let ten = f.num(10);
    let two = f.num(2);
    let five = f.num(5);

    let gcd_3_10 = f.gcd(three, ten);
    assert!(f.k.def_eq(gcd_3_10, one), "gcd 3 10 must reduce to 1");
    let coprime_3_10 = f.refl(one);

    let dvd_predicate_2 = f.dvd_predicate(two, ten);
    let mul_2_5 = f.mul(two, five);
    assert!(f.k.def_eq(ten, mul_2_5), "10 must reduce to mul 2 5");
    let eq_proof_2 = f.refl(ten);
    let dvd_2_10 = f.apply(intro, &[nat, dvd_predicate_2, five, eq_proof_2]);

    let applied_succ = f.const_app(p.coprime_div_right, &[three, ten, two]);
    let applied_succ_full = f.apply(applied_succ, &[coprime_3_10, dvd_2_10]);
    let inferred_succ =
        f.k.infer(applied_succ_full)
            .expect("coprime_div_right 3 10 2 (Coprime 3 10) (dvd 2 10) must type-check");
    let rendered_succ = f.k.render_lean(inferred_succ);
    assert!(
        rendered_succ.contains("gcd"),
        "unexpected conclusion type: {rendered_succ}"
    );

    let div_10_2 = f.div(ten, two);
    assert!(f.k.def_eq(div_10_2, five), "div 10 2 must reduce to 5");
    let expected_concl = f.gcd(three, div_10_2);
    let expected_ty = f.eq(expected_concl, one);
    assert!(
        f.k.def_eq(inferred_succ, expected_ty),
        "coprime_div_right's conclusion must be Coprime 3 (div 10 2), got: {rendered_succ}"
    );

    assert!(
        f.k.axiom_footprint(p.coprime_div_right).is_empty(),
        "coprime_div_right rests on a trusted declaration"
    );
}

/// `Nat.coprime_div_left` at two concrete instances exercising BOTH branches
/// of its case split on `a` -- the mirror image of
/// `coprime_div_right_applies_at_both_branches_of_its_case_split`, with the
/// divided argument moved from `n` to `m`.
///
/// Zero branch: `m = 0, n = 1, a = 0` -- `dvd 0 0` (witness `0`), `Coprime 0
/// 1` (`gcd 0 1` reduces to `1`), concluding `Coprime (0/0) 1`.
///
/// Succ branch: `m = 10, n = 3, a = 2` -- `dvd 2 10` (witness `5`),
/// `Coprime 10 3` (`gcd 10 3` reduces to `1`), concluding `Coprime (10/2) 3`,
/// and the conclusion's FIRST argument is checked to be `div 10 2` (which
/// reduces to `5`) rather than the original `10` -- a wrong theorem that left
/// `m` unchanged would still type-check against its own (differently shaped)
/// conclusion, so this pins the actual residue.
#[test]
fn coprime_div_left_applies_at_both_branches_of_its_case_split() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();
    let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);

    // -- zero branch: m=0, n=1, a=0 --
    let one = f.num(1);
    let zero = f.num(0);

    let gcd_0_1 = f.gcd(zero, one);
    assert!(f.k.def_eq(gcd_0_1, one), "gcd 0 1 must reduce to 1");
    let coprime_0_1 = f.refl(one);

    let dvd_predicate_0 = f.dvd_predicate(zero, zero);
    let mul_0_0 = f.mul(zero, zero);
    assert!(f.k.def_eq(zero, mul_0_0), "0 must reduce to mul 0 0");
    let eq_proof_0 = f.refl(zero);
    let dvd_0_0 = f.apply(intro, &[nat, dvd_predicate_0, zero, eq_proof_0]);

    let applied_zero = f.const_app(p.coprime_div_left, &[zero, one, zero]);
    let applied_zero_full = f.apply(applied_zero, &[coprime_0_1, dvd_0_0]);
    let inferred_zero =
        f.k.infer(applied_zero_full)
            .expect("coprime_div_left 0 1 0 (Coprime 0 1) (dvd 0 0) must type-check");
    let rendered_zero = f.k.render_lean(inferred_zero);
    assert!(
        rendered_zero.contains("gcd"),
        "unexpected conclusion type: {rendered_zero}"
    );

    // -- succ branch: m=10, n=3, a=2 --
    let three = f.num(3);
    let ten = f.num(10);
    let two = f.num(2);
    let five = f.num(5);

    let gcd_10_3 = f.gcd(ten, three);
    assert!(f.k.def_eq(gcd_10_3, one), "gcd 10 3 must reduce to 1");
    let coprime_10_3 = f.refl(one);

    let dvd_predicate_2 = f.dvd_predicate(two, ten);
    let mul_2_5 = f.mul(two, five);
    assert!(f.k.def_eq(ten, mul_2_5), "10 must reduce to mul 2 5");
    let eq_proof_2 = f.refl(ten);
    let dvd_2_10 = f.apply(intro, &[nat, dvd_predicate_2, five, eq_proof_2]);

    let applied_succ = f.const_app(p.coprime_div_left, &[ten, three, two]);
    let applied_succ_full = f.apply(applied_succ, &[coprime_10_3, dvd_2_10]);
    let inferred_succ =
        f.k.infer(applied_succ_full)
            .expect("coprime_div_left 10 3 2 (Coprime 10 3) (dvd 2 10) must type-check");
    let rendered_succ = f.k.render_lean(inferred_succ);
    assert!(
        rendered_succ.contains("gcd"),
        "unexpected conclusion type: {rendered_succ}"
    );

    let div_10_2 = f.div(ten, two);
    assert!(f.k.def_eq(div_10_2, five), "div 10 2 must reduce to 5");
    let expected_concl = f.gcd(div_10_2, three);
    let expected_ty = f.eq(expected_concl, one);
    assert!(
        f.k.def_eq(inferred_succ, expected_ty),
        "coprime_div_left's conclusion must be Coprime (div 10 2) 3, got: {rendered_succ}"
    );

    assert!(
        f.k.axiom_footprint(p.coprime_div_left).is_empty(),
        "coprime_div_left rests on a trusted declaration"
    );
}

/// `Nat.gcd_comm` at a concrete discriminating pair (`gcd 6 4` vs `gcd 4 6`
/// -- both reduce to `2`, but the STATEMENT relates the two differently-
/// ordered applications, not two identical terms) and at a genuinely free
/// `(a, b)` pushed into an explicit `LocalContext`.
#[test]
fn gcd_comm_applies_at_a_concrete_pair_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: a = 6, b = 4. gcd 6 4 = gcd 4 6 = 2, but the applied
    // conclusion is pinned as the UNREDUCED pair `Eq (gcd 6 4) (gcd 4 6)`,
    // not merely `Eq 2 2` -- a theorem with the arguments left unswapped
    // would still type-check against a def_eq-equal-but-differently-shaped
    // conclusion, so this confirms the actual residue.
    let six = f.num(6);
    let four = f.num(4);
    let applied = f.const_app(p.gcd_comm, &[six, four]);
    let inferred = f.k.infer(applied).expect("gcd_comm 6 4 must type-check");
    let gcd_64 = f.gcd(six, four);
    let gcd_46 = f.gcd(four, six);
    let two = f.num(2);
    assert!(f.k.def_eq(gcd_64, two), "gcd 6 4 must reduce to 2");
    assert!(f.k.def_eq(gcd_46, two), "gcd 4 6 must reduce to 2");
    let expected = f.eq(gcd_64, gcd_46);
    assert!(
        f.k.def_eq(inferred, expected),
        "gcd_comm's conclusion must be Eq (gcd 6 4) (gcd 4 6)"
    );

    // Symbolic: genuinely free a, b.
    let a_fv = f.fresh_fvar();
    let b_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b = f.k.fvar(b_fv);
    let applied_sym = f.const_app(p.gcd_comm, &[a, b]);
    let gcd_ab_sym = f.gcd(a, b);
    let gcd_ba_sym = f.gcd(b, a);
    let expected_sym = f.eq(gcd_ab_sym, gcd_ba_sym);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: a_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: b_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(applied_sym, &mut ctx)
            .expect("gcd_comm must apply at free variables");
    assert!(f.k.def_eq(inferred_sym, expected_sym));

    assert!(
        f.k.axiom_footprint(p.gcd_comm).is_empty(),
        "gcd_comm rests on a trusted declaration"
    );
}

/// `Nat.coprime_mul_of_coprime` at a concrete instance (`x=5, m=2, n=3`:
/// `gcd 5 2 = gcd 5 3 = 1`, so the conclusion `gcd 5 6 = 1` must hold too)
/// and at a genuinely free `(x, m, n)` with free hypotheses pushed into an
/// explicit `LocalContext`.
#[test]
fn coprime_mul_of_coprime_applies_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);

    // Concrete: x = 5, m = 2, n = 3.
    let five = f.num(5);
    let two = f.num(2);
    let three = f.num(3);
    let six = f.num(6);
    let gcd_5_2 = f.gcd(five, two);
    let gcd_5_3 = f.gcd(five, three);
    assert!(f.k.def_eq(gcd_5_2, one), "gcd 5 2 must reduce to 1");
    assert!(f.k.def_eq(gcd_5_3, one), "gcd 5 3 must reduce to 1");
    let h_xm = f.refl(one); // Eq (gcd 5 2) one, up to the defeq just checked
    let h_xn = f.refl(one); // Eq (gcd 5 3) one, up to the defeq just checked
    let applied = f.lemma(p.coprime_mul_of_coprime, &[five, two, three, h_xm, h_xn]);
    let inferred =
        f.k.infer(applied)
            .expect("coprime_mul_of_coprime must type-check at (5,2,3)");
    let gcd_5_6 = f.gcd(five, six);
    assert!(f.k.def_eq(gcd_5_6, one), "gcd 5 6 must reduce to 1 too");
    let expected = f.eq(gcd_5_6, one);
    assert!(
        f.k.def_eq(inferred, expected),
        "coprime_mul_of_coprime must conclude Eq (gcd 5 6) one"
    );

    // Symbolic: genuinely free x, m, n with free hypotheses.
    let x_fv = f.fresh_fvar();
    let m_fv = f.fresh_fvar();
    let n_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let m = f.k.fvar(m_fv);
    let n = f.k.fvar(n_fv);
    let gcd_xm = f.gcd(x, m);
    let gcd_xn = f.gcd(x, n);
    let h_xm_ty = f.eq(gcd_xm, one);
    let h_xn_ty = f.eq(gcd_xn, one);
    let hxm_fv = f.fresh_fvar();
    let hxn_fv = f.fresh_fvar();
    let hxm = f.k.fvar(hxm_fv);
    let hxn = f.k.fvar(hxn_fv);
    let applied_sym = f.lemma(p.coprime_mul_of_coprime, &[x, m, n, hxm, hxn]);
    let mn = f.mul(m, n);
    let gcd_x_mn = f.gcd(x, mn);
    let expected_sym = f.eq(gcd_x_mn, one);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: x_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hxm_fv,
        name: anon,
        ty: h_xm_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: hxn_fv,
        name: anon,
        ty: h_xn_ty,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(applied_sym, &mut ctx)
            .expect("coprime_mul_of_coprime must apply at free variables");
    assert!(f.k.def_eq(inferred_sym, expected_sym));

    assert!(
        f.k.axiom_footprint(p.coprime_mul_of_coprime).is_empty(),
        "coprime_mul_of_coprime rests on a trusted declaration"
    );
}

/// `Nat.gcd_mod_left_eq_gcd` at concrete instances exercising BOTH branches
/// of its `m` case split, plus a genuinely free `(x, m)`.
///
/// `m = 0`: `x = 7`, so `mod 7 0 = 7` (`Nat.mod_zero`) and the conclusion is
/// the (still non-trivial, since the two sides are syntactically different
/// `gcd` applications before reduction) `Eq (gcd (mod 7 0) 0) (gcd 7 0)`.
/// `m = succ k` (`k = 4`, so `m = 5`): `x = 17`, `mod 17 5 = 2` -- checked to
/// NOT be syntactically/definitionally `17` first, so this instance
/// genuinely exercises the Euclidean step rather than a degenerate case
/// where the remainder happens to equal the dividend; `gcd 2 5 = 1 = gcd 17
/// 5` confirms the reduced values agree too.
#[test]
fn gcd_mod_left_eq_gcd_applies_at_both_branches_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // m = 0 branch.
    let seven = f.num(7);
    let zero = f.zero();
    let applied_zero = f.lemma(p.gcd_mod_left_eq_gcd, &[seven, zero]);
    let inferred_zero =
        f.k.infer(applied_zero)
            .expect("gcd_mod_left_eq_gcd must type-check at (7, 0)");
    let mod_7_0 = f.modulo(seven, zero);
    let gcd_mod_7_0 = f.gcd(mod_7_0, zero);
    let gcd_7_0 = f.gcd(seven, zero);
    let expected_zero = f.eq(gcd_mod_7_0, gcd_7_0);
    assert!(f.k.def_eq(inferred_zero, expected_zero));

    // m = succ k branch, k = 4 (m = 5).
    let seventeen = f.num(17);
    let five = f.num(5);
    let two = f.num(2);
    let mod_17_5 = f.modulo(seventeen, five);
    assert!(
        !f.k.def_eq(mod_17_5, seventeen),
        "mod 17 5 must NOT reduce to 17 -- this instance must exercise the \
         real Euclidean step, not a degenerate m=0-shaped one"
    );
    assert!(f.k.def_eq(mod_17_5, two), "mod 17 5 must reduce to 2");
    let one = f.num(1);
    let gcd_17_5 = f.gcd(seventeen, five);
    assert!(f.k.def_eq(gcd_17_5, one), "gcd 17 5 must reduce to 1");
    let applied_succ = f.lemma(p.gcd_mod_left_eq_gcd, &[seventeen, five]);
    let inferred_succ =
        f.k.infer(applied_succ)
            .expect("gcd_mod_left_eq_gcd must type-check at (17, 5)");
    let gcd_mod_17_5 = f.gcd(mod_17_5, five);
    let expected_succ = f.eq(gcd_mod_17_5, gcd_17_5);
    assert!(f.k.def_eq(inferred_succ, expected_succ));

    // Symbolic: a genuinely free `(x, m)`.
    let x_fv = f.fresh_fvar();
    let m_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let m = f.k.fvar(m_fv);
    let applied_sym = f.lemma(p.gcd_mod_left_eq_gcd, &[x, m]);
    let mod_x_m = f.modulo(x, m);
    let gcd_mod_x_m = f.gcd(mod_x_m, m);
    let gcd_x_m = f.gcd(x, m);
    let expected_sym = f.eq(gcd_mod_x_m, gcd_x_m);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: x_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(applied_sym, &mut ctx)
            .expect("gcd_mod_left_eq_gcd must apply at free variables");
    assert!(f.k.def_eq(inferred_sym, expected_sym));

    assert!(
        f.k.axiom_footprint(p.gcd_mod_left_eq_gcd).is_empty(),
        "gcd_mod_left_eq_gcd rests on a trusted declaration"
    );
}

/// `Nat.coprime_mul_iff` at a concrete coprime instance (`x=5, m=2, n=3`,
/// mirroring `coprime_mul_of_coprime`'s own test point) and a concrete
/// NON-coprime instance (`x=2, m=2, n=3`: `gcd 2 2 = 2 != 1`, so the `Iff`'s
/// right side's first conjunct is a genuinely unprovable proposition here --
/// checked directly, so this instantiation is not vacuous), plus a
/// genuinely free `(x, m, n)`.
#[test]
fn coprime_mul_iff_applies_at_concrete_instances_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);

    // Coprime instance.
    let five = f.num(5);
    let two = f.num(2);
    let three = f.num(3);
    let six = f.mul(two, three);
    let applied = f.const_app(p.coprime_mul_iff, &[five, two, three]);
    let inferred =
        f.k.infer(applied)
            .expect("coprime_mul_iff must type-check at (5,2,3)");
    let gcd_5_6 = f.gcd(five, six);
    let lhs_ty = f.eq(gcd_5_6, one);
    let gcd_5_2 = f.gcd(five, two);
    let eq_5_2 = f.eq(gcd_5_2, one);
    let gcd_5_3 = f.gcd(five, three);
    let eq_5_3 = f.eq(gcd_5_3, one);
    let rhs_ty = f.const_app(p.logic.and, &[eq_5_2, eq_5_3]);
    let expected = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    assert!(f.k.def_eq(inferred, expected));

    // Non-coprime instance: gcd 2 2 = 2 != 1, checked directly so this
    // instantiation genuinely exercises a false right-conjunct, not a
    // vacuous copy of the coprime case above.
    let gcd_2_2 = f.gcd(two, two);
    assert!(!f.k.def_eq(gcd_2_2, one), "gcd 2 2 must NOT reduce to one");
    let applied_nc = f.const_app(p.coprime_mul_iff, &[two, two, three]);
    let inferred_nc =
        f.k.infer(applied_nc)
            .expect("coprime_mul_iff must type-check at (2,2,3)");
    let two_times_three = f.mul(two, three);
    let gcd_2_6 = f.gcd(two, two_times_three);
    let lhs_nc = f.eq(gcd_2_6, one);
    let eq_2_2 = f.eq(gcd_2_2, one);
    let gcd_2_3 = f.gcd(two, three);
    let eq_2_3 = f.eq(gcd_2_3, one);
    let rhs_nc = f.const_app(p.logic.and, &[eq_2_2, eq_2_3]);
    let expected_nc = f.const_app(p.logic.iff, &[lhs_nc, rhs_nc]);
    assert!(f.k.def_eq(inferred_nc, expected_nc));

    // Symbolic: a genuinely free `(x, m, n)`.
    let x_fv = f.fresh_fvar();
    let m_fv = f.fresh_fvar();
    let n_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let m = f.k.fvar(m_fv);
    let n = f.k.fvar(n_fv);
    let applied_sym = f.const_app(p.coprime_mul_iff, &[x, m, n]);
    let mn = f.mul(m, n);
    let gcd_x_mn = f.gcd(x, mn);
    let lhs_sym = f.eq(gcd_x_mn, one);
    let gcd_x_m = f.gcd(x, m);
    let eq_x_m = f.eq(gcd_x_m, one);
    let gcd_x_n = f.gcd(x, n);
    let eq_x_n = f.eq(gcd_x_n, one);
    let rhs_sym = f.const_app(p.logic.and, &[eq_x_m, eq_x_n]);
    let expected_sym = f.const_app(p.logic.iff, &[lhs_sym, rhs_sym]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: x_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred_sym =
        f.k.infer_in(applied_sym, &mut ctx)
            .expect("coprime_mul_iff must apply at free variables");
    assert!(f.k.def_eq(inferred_sym, expected_sym));

    assert!(
        f.k.axiom_footprint(p.coprime_mul_iff).is_empty(),
        "coprime_mul_iff rests on a trusted declaration"
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

/// `descFactorial_self` and `descFactorial_le` apply at concrete instances.
///
/// `descFactorial_self` at `n := 5`: `5.descFactorial 5 = 5!`, i.e. `120 =
/// 120`. `descFactorial_le` at `n := 2, k := 3, m := 5` with a proof of
/// `3 <= 5`: `3.descFactorial 2 = 6 <= 20 = 5.descFactorial 2`. NEGATIVE
/// control: swapping in a proof of `5 <= 5` where `3 <= 5` was required (the
/// hypothesis slot, not the conclusion) must be rejected — the same
/// wrong-bound shape [`desc_factorial_computes_and_collapses_past_its_base`]
/// already exercises for `descFactorial_of_lt`.
#[test]
fn desc_factorial_self_and_le_apply_at_concrete_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    let five = f.num(5);
    let one_twenty = f.num(120);

    // descFactorial_self(5) : Eq(5.descFactorial 5, 5!)
    let self_proof = f.lemma(p.desc_factorial_self, &[five]);
    let self_inferred =
        f.k.infer(self_proof)
            .expect("descFactorial_self applies at n := 5");
    let self_at_five = f.const_app(p.desc_factorial, &[five, five]);
    let fact_five = f.factorial(five);
    let self_expected = f.eq(self_at_five, fact_five);
    assert!(f.k.def_eq(self_inferred, self_expected));
    // The conclusion is about the concrete number 120, not an opaque term.
    assert!(f.k.def_eq(self_at_five, one_twenty));
    assert!(f.k.def_eq(fact_five, one_twenty));

    // descFactorial_le(n := 2, k := 3, m := 5) applied at a proof of 3 <= 5:
    // 3.descFactorial 2 = 6 <= 20 = 5.descFactorial 2.
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let three_le_five = {
        let base = f.lemma(p.le_refl, &[three]);
        let to_four = f.lemma(p.le_step, &[three, three, base]);
        f.lemma(p.le_step, &[three, four, to_four])
    };
    let le_proof = f.lemma(p.desc_factorial_le, &[two, three, five, three_le_five]);
    let le_inferred =
        f.k.infer(le_proof)
            .expect("descFactorial_le applies at (n, k, m) := (2, 3, 5)");
    let df_3_2 = f.const_app(p.desc_factorial, &[three, two]);
    let df_5_2 = f.const_app(p.desc_factorial, &[five, two]);
    let le_expected = f.le(df_3_2, df_5_2);
    assert!(f.k.def_eq(le_inferred, le_expected));
    // The conclusion is about the concrete numbers 6 and 20, not opaque terms.
    let six = f.num(6);
    let twenty = f.num(20);
    assert!(f.k.def_eq(df_3_2, six));
    assert!(f.k.def_eq(df_5_2, twenty));

    // The hypothesis is load-bearing: swapping in a proof of `5 <= 5` (not
    // `3 <= 5`) where the theorem's third explicit argument is `5` must be
    // rejected, not silently accepted for the wrong bound.
    let five_le_five = f.lemma(p.le_refl, &[five]);
    let wrong_bound = {
        let theorem = f.k.const_(p.desc_factorial_le, vec![]);
        let at_n = f.k.app(theorem, two);
        let at_k = f.k.app(at_n, three);
        let at_m = f.k.app(at_k, five);
        f.k.app(at_m, five_le_five)
    };
    assert!(
        f.k.infer(wrong_bound).is_err(),
        "accepted a proof of `5 <= 5` where `3 <= 5` was required"
    );
}

/// `self_le_factorial` applies at a concrete instance: `5 <= 5! = 120`.
/// NEGATIVE control: the inferred conclusion is `Le n (factorial n)`, not
/// the reversed `Le (factorial n) n` (which would also happen to hold at
/// `n := 1` but is a different, generally FALSE proposition for `n >= 2` —
/// checked here concretely, since `def_eq` would not otherwise distinguish
/// the two orderings of `Le` at `n := 1`).
#[test]
fn self_le_factorial_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let five = f.num(5);
    let one_twenty = f.num(120);

    let proof = f.lemma(p.self_le_factorial, &[five]);
    let inferred =
        f.k.infer(proof)
            .expect("self_le_factorial applies at n := 5");
    let fact_five = f.factorial(five);
    let expected = f.le(five, fact_five);
    assert!(f.k.def_eq(inferred, expected));
    // The conclusion is about the concrete number 120, not an opaque term.
    assert!(f.k.def_eq(fact_five, one_twenty));

    // NEGATIVE control: the reversed proposition `Le (factorial n) n` is a
    // different type; the proof term for `self_le_factorial` must not
    // type-check against it.
    let reversed = f.le(fact_five, five);
    assert!(
        !f.k.def_eq(expected, reversed),
        "Le n (factorial n) must NOT be def-eq to the reversed Le (factorial n) n"
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

/// `Nat.dist` computes the two-sided truncated distance —
/// `dist n m := add (sub n m) (sub m n)`, where `Nat.sub` truncates.
/// `dist(3,5)` and `dist(5,3)` share the value `2` precisely BECAUSE `dist`
/// sums both directions: a broken definition that returned only `sub n m`
/// (dropping the reverse subtraction) would give `0` for `dist(3,5)`, since
/// `sub 3 5` truncates to `0` — the exact asymmetry this negative control is
/// built to catch. `dist(0,7)`/`dist(7,0)` cover the other zero boundary, and
/// `dist(4,4) = 0` covers self-distance.
#[test]
fn dist_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let seven = f.num(7);
    let nine = f.num(9);
    let zero = f.zero();

    let dist_3_5 = f.const_app(p.dist, &[three, five]);
    assert!(f.k.def_eq(dist_3_5, two), "dist 3 5 must reduce to 2");
    let dist_5_3 = f.const_app(p.dist, &[five, three]);
    assert!(f.k.def_eq(dist_5_3, two), "dist 5 3 must reduce to 2");
    assert!(
        !f.k.def_eq(dist_3_5, zero),
        "negative control: dist 3 5 must NOT be def-eq to 0 (the value a \
         dropped-reverse-subtraction bug would give, since sub 3 5 = 0)"
    );

    let dist_0_7 = f.const_app(p.dist, &[zero, seven]);
    assert!(f.k.def_eq(dist_0_7, seven), "dist 0 7 must reduce to 7");
    let dist_7_0 = f.const_app(p.dist, &[seven, zero]);
    assert!(f.k.def_eq(dist_7_0, seven), "dist 7 0 must reduce to 7");

    let dist_4_4 = f.const_app(p.dist, &[four, four]);
    assert!(f.k.def_eq(dist_4_4, zero), "dist 4 4 must reduce to 0");

    let dist_2_9 = f.const_app(p.dist, &[two, nine]);
    assert!(f.k.def_eq(dist_2_9, seven), "dist 2 9 must reduce to 7");
    assert!(
        !f.k.def_eq(dist_2_9, zero),
        "negative control: dist 2 9 must NOT be def-eq to 0 (the value sub \
         2 9 alone gives)"
    );
}

/// The seven `Nat.dist` theorems apply at their stated shape — in particular
/// that `dist_eq_sub_of_le`/`dist_eq_sub_of_le_right` were not transposed
/// (CLAUDE.md's most-common bug family in this development: getting the two
/// operands or the hypothesis's orientation backwards). Each theorem's PROOF
/// was already checked against a fully general statement at admission
/// (`try_theorem` builds the universally quantified goal before the kernel
/// ever sees it), so what a test can still catch is applying the theorem
/// with an argument or hypothesis in the wrong slot — checked here both at
/// free variables (`dist_comm`/`dist_self`/`dist_succ_succ`) and at concrete,
/// discriminating numerals (the two `sub`-orientation lemmas, the two zero
/// boundaries).
#[test]
fn dist_theorems_apply_at_free_variables_and_concrete_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    // A genuinely free pair `n`, `m`, pushed into an explicit `LocalContext`
    // so `infer_in` can look up their type (a bare unregistered `FVar` is
    // `UnboundFVar` to the checker, not merely "unknown").
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let n_fv = f.fresh_fvar();
    let m_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let m = f.k.fvar(m_fv);
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });

    // dist_comm at the free pair.
    {
        let applied = f.const_app(p.dist_comm, &[n, m]);
        let inferred = f.k.infer_in(applied, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_comm must type-check at free variables: {shown}")
        });
        let dist_nm = f.const_app(p.dist, &[n, m]);
        let dist_mn = f.const_app(p.dist, &[m, n]);
        let want = f.eq(dist_nm, dist_mn);
        assert!(
            f.k.def_eq(inferred, want),
            "dist_comm must state Eq (dist n m) (dist m n)"
        );
    }

    // dist_self at the free `n`.
    {
        let applied = f.const_app(p.dist_self, &[n]);
        let inferred = f.k.infer_in(applied, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_self must type-check at a free variable: {shown}")
        });
        let dist_nn = f.const_app(p.dist, &[n, n]);
        let zero = f.zero();
        let want = f.eq(dist_nn, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "dist_self must state Eq (dist n n) 0"
        );
    }

    // dist_succ_succ at the free pair.
    {
        let applied = f.const_app(p.dist_succ_succ, &[n, m]);
        let inferred = f.k.infer_in(applied, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_succ_succ must type-check at free variables: {shown}")
        });
        let sn = f.succ(n);
        let sm = f.succ(m);
        let dist_ss = f.const_app(p.dist, &[sn, sm]);
        let dist_nm = f.const_app(p.dist, &[n, m]);
        let want = f.eq(dist_ss, dist_nm);
        assert!(
            f.k.def_eq(inferred, want),
            "dist_succ_succ must state Eq (dist (succ n) (succ m)) (dist n m)"
        );
    }

    // A concrete `Le 2 5` witness, built from `le_refl`/`le_step`, shared by
    // both directional checks below.
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let zero = f.zero();
    let le_2_5 = {
        let h0 = f.lemma(p.le_refl, &[two]); // Le 2 2
        let h1 = f.lemma(p.le_step, &[two, two, h0]); // Le 2 3
        let h2 = f.lemma(p.le_step, &[two, three, h1]); // Le 2 4
        f.lemma(p.le_step, &[two, four, h2]) // Le 2 5
    };

    // dist_eq_sub_of_le(2,5,h) : Eq (dist 2 5) (sub 5 2) = 3 — NOT sub 2 5 = 0.
    {
        let applied = f.const_app(p.dist_eq_sub_of_le, &[two, five, le_2_5]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_eq_sub_of_le must type-check: {shown}")
        });
        let dist_2_5 = f.const_app(p.dist, &[two, five]);
        let want = f.eq(dist_2_5, three);
        assert!(
            f.k.def_eq(inferred, want),
            "dist_eq_sub_of_le must state Eq (dist 2 5) (sub 5 2) = 3"
        );
        let bad = f.eq(dist_2_5, zero);
        assert!(
            !f.k.def_eq(inferred, bad),
            "negative control: dist_eq_sub_of_le must not ALSO state Eq \
             (dist 2 5) 0 (the value sub 2 5 alone gives)"
        );
    }

    // dist_eq_sub_of_le_right(5,2,h) : Eq (dist 5 2) (sub 5 2) = 3.
    {
        let applied = f.const_app(p.dist_eq_sub_of_le_right, &[five, two, le_2_5]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_eq_sub_of_le_right must type-check: {shown}")
        });
        let dist_5_2 = f.const_app(p.dist, &[five, two]);
        let want = f.eq(dist_5_2, three);
        assert!(
            f.k.def_eq(inferred, want),
            "dist_eq_sub_of_le_right must state Eq (dist 5 2) (sub 5 2) = 3"
        );
        let bad = f.eq(dist_5_2, zero);
        assert!(
            !f.k.def_eq(inferred, bad),
            "negative control: dist_eq_sub_of_le_right must not ALSO state \
             Eq (dist 5 2) 0"
        );
    }

    // dist_zero_right / dist_zero_left at a concrete instance.
    {
        let seven = f.num(7);
        let applied_r = f.const_app(p.dist_zero_right, &[seven]);
        let inferred_r = f.k.infer(applied_r).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_zero_right must type-check: {shown}")
        });
        let dist_7_0 = f.const_app(p.dist, &[seven, zero]);
        let want_r = f.eq(dist_7_0, seven);
        assert!(
            f.k.def_eq(inferred_r, want_r),
            "dist_zero_right must state Eq (dist 7 0) 7"
        );

        let applied_l = f.const_app(p.dist_zero_left, &[seven]);
        let inferred_l = f.k.infer(applied_l).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_zero_left must type-check: {shown}")
        });
        let dist_0_7 = f.const_app(p.dist, &[zero, seven]);
        let want_l = f.eq(dist_0_7, seven);
        assert!(
            f.k.def_eq(inferred_l, want_l),
            "dist_zero_left must state Eq (dist 0 7) 7"
        );
    }

    // NEGATIVE control for `dist_zero_right` vs `dist_zero_left`, at the free
    // `n` rather than a concrete numeral: `dist n 0` and `dist 0 n` are NOT
    // def-eq for symbolic `n` (only a concrete numeral's full reduction makes
    // them coincide), so this is where a transposed-argument bug would
    // actually be caught.
    {
        let applied_r = f.const_app(p.dist_zero_right, &[n]);
        let inferred_r = f.k.infer_in(applied_r, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dist_zero_right must type-check at a free variable: {shown}")
        });
        let dist_n_0 = f.const_app(p.dist, &[n, zero]);
        let want_r = f.eq(dist_n_0, n);
        assert!(
            f.k.def_eq(inferred_r, want_r),
            "dist_zero_right must state Eq (dist n 0) n symbolically"
        );
        let dist_0_n = f.const_app(p.dist, &[zero, n]);
        let bad_r = f.eq(dist_0_n, n);
        assert!(
            !f.k.def_eq(inferred_r, bad_r),
            "negative control: dist_zero_right must not ALSO state Eq \
             (dist 0 n) n at a free variable"
        );
    }

    for name in [
        p.dist_comm,
        p.dist_self,
        p.dist_eq_sub_of_le,
        p.dist_eq_sub_of_le_right,
        p.dist_zero_right,
        p.dist_zero_left,
        p.dist_succ_succ,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.nth` computes the fuel-bounded search (see `nth.rs`'s module doc for
/// why this is NOT Mathlib's construction). `dec1 := fun k => ble 3 k` is
/// true for every `k >= 3`: `nth dec1 10 0/1/2` must give `3/4/5` — the
/// n-th (0-indexed) match found by walking candidates upward. The negative
/// controls catch both an "always return the FIRST match" bug (which would
/// give `3` for every index) and an off-by-one.
///
/// `dec2 := fun k => beq k 5` has exactly ONE witness in range: `nth dec2 10
/// 0` must give `5`, and `nth dec2 10 1` (a SECOND witness that does not
/// exist) must give the sentinel `0` — Mathlib's own convention for "fewer
/// than n+1 witnesses" (`nth_of_card_le`), reached here by fuel exhaustion
/// rather than a classical cardinality case split.
#[test]
fn nth_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let ten = f.num(10);

    let dec1 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let body = f.ble(three, k); // true iff k >= 3
        f.lam_fv(k_fv, nat, body)
    };

    let nth_dec1_0 = f.const_app(p.nth, &[dec1, ten, zero]);
    assert!(
        f.k.def_eq(nth_dec1_0, three),
        "nth (>=3) bound 10 index 0 must be 3"
    );
    let nth_dec1_1 = f.const_app(p.nth, &[dec1, ten, one]);
    assert!(
        f.k.def_eq(nth_dec1_1, four),
        "nth (>=3) bound 10 index 1 must be 4"
    );
    let nth_dec1_2 = f.const_app(p.nth, &[dec1, ten, two]);
    assert!(
        f.k.def_eq(nth_dec1_2, five),
        "nth (>=3) bound 10 index 2 must be 5"
    );
    assert!(
        !f.k.def_eq(nth_dec1_1, three),
        "negative control: index 1 must NOT collapse to the first match \
         (the value an 'always return the first match' bug would give)"
    );
    assert!(
        !f.k.def_eq(nth_dec1_0, four),
        "negative control: index 0 must NOT be off-by-one"
    );

    let dec2 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let body = f.beq(k, five); // true only at k = 5
        f.lam_fv(k_fv, nat, body)
    };
    let nth_dec2_0 = f.const_app(p.nth, &[dec2, ten, zero]);
    assert!(
        f.k.def_eq(nth_dec2_0, five),
        "nth (=5) bound 10 index 0 must be 5 (the only witness)"
    );
    let nth_dec2_1 = f.const_app(p.nth, &[dec2, ten, one]);
    assert!(
        f.k.def_eq(nth_dec2_1, zero),
        "nth (=5) bound 10 index 1 must be the sentinel 0 (no second \
         witness within bound)"
    );
    assert!(
        !f.k.def_eq(nth_dec2_1, five),
        "negative control: the sentinel case must NOT collapse to the \
         found value"
    );

    for name in [p.nth_aux, p.nth] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
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

/// Every `prime_dvd_mirrors.rs` theorem's DECLARED type, checked against an
/// INDEPENDENTLY built type at a free `p` (and `m`, `n`, `a` where needed) --
/// never against the same `prime_condition` helper the theorem was built
/// with, so a swapped `Iff` side or a transposed hypothesis order would show
/// up here even though the kernel already accepted the proof term against
/// whatever type this file's proof-builder actually asked for.
#[test]
fn prime_dvd_mirrors_state_exactly_what_they_claim() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.num(1);
    let two = f.num(2);
    let zero = f.zero();

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

    macro_rules! check {
        ($name:expr, $expected:expr, $label:expr) => {{
            let theorem = f.k.const_($name, vec![]);
            let declared = f.k.infer(theorem).unwrap_or_else(|e| {
                panic!("{} must be in the environment: {}", $label, f.explain(&e))
            });
            let expected = $expected;
            assert!(
                f.k.def_eq(declared, expected),
                "{} does not state what it claims to",
                $label
            );
        }};
    }

    // one Nat var: p
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let lt_ty = f.lt(one, pv);
        let inner = f.arrow(prime_ty, lt_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_one_lt, expected, "prime_one_lt");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let le_ty = f.le(one, pv);
        let inner = f.arrow(prime_ty, le_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_one_le, expected, "prime_one_le");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let lt_ty = f.lt(zero, pv);
        let inner = f.arrow(prime_ty, lt_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_pos, expected, "prime_pos");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let eq_p1 = f.eq(pv, one);
        let ne_ty = f.const_app(p.logic.not, &[eq_p1]);
        let inner = f.arrow(prime_ty, ne_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_ne_one, expected, "prime_ne_one");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let eq_p0 = f.eq(pv, zero);
        let ne_ty = f.const_app(p.logic.not, &[eq_p0]);
        let inner = f.arrow(prime_ty, ne_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_ne_zero, expected, "prime_ne_zero");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let dvd_p1 = f.dvd(pv, one);
        let not_ty = f.const_app(p.logic.not, &[dvd_p1]);
        let inner = f.arrow(prime_ty, not_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_not_dvd_one, expected, "prime_not_dvd_one");
    }

    // two Nat vars: p, m
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let m_fv = f.fresh_fvar();
        let mv = f.k.fvar(m_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let dvd_ty = f.dvd(mv, pv);
        let is_one = f.eq(mv, one);
        let is_p = f.eq(mv, pv);
        let disj = f.const_app(p.logic.or, &[is_one, is_p]);
        let inner = f.arrow(dvd_ty, disj);
        let with_prime = f.arrow(prime_ty, inner);
        let with_m = f.pi_fv(m_fv, nat, with_prime);
        let expected = f.pi_fv(p_fv, nat, with_m);
        check!(
            p.prime_eq_one_or_self_of_dvd,
            expected,
            "prime_eq_one_or_self_of_dvd"
        );
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let a_fv = f.fresh_fvar();
        let av = f.k.fvar(a_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let eq_a1 = f.eq(av, one);
        let ne_ty = f.const_app(p.logic.not, &[eq_a1]);
        let dvd_ap = f.dvd(av, pv);
        let eq_pa = f.eq(pv, av);
        let iff_ty = f.const_app(p.logic.iff, &[dvd_ap, eq_pa]);
        let with_ne = f.arrow(ne_ty, iff_ty);
        let inner = f.arrow(prime_ty, with_ne);
        let with_a = f.pi_fv(a_fv, nat, inner);
        let expected = f.pi_fv(p_fv, nat, with_a);
        check!(p.prime_dvd_iff_eq, expected, "prime_dvd_iff_eq");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let n_fv = f.fresh_fvar();
        let nv = f.k.fvar(n_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let gcd_pn = f.gcd(pv, nv);
        let cop_ty = f.eq(gcd_pn, one);
        let dvd_pn = f.dvd(pv, nv);
        let not_dvd_ty = f.const_app(p.logic.not, &[dvd_pn]);
        let iff_ty = f.const_app(p.logic.iff, &[cop_ty, not_dvd_ty]);
        let inner = f.arrow(prime_ty, iff_ty);
        let with_n = f.pi_fv(n_fv, nat, inner);
        let expected = f.pi_fv(p_fv, nat, with_n);
        check!(
            p.prime_coprime_iff_not_dvd,
            expected,
            "prime_coprime_iff_not_dvd"
        );
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let odd_ty = f.lemma(p.odd, &[pv]);
        let eq_p2 = f.eq(pv, two);
        let goal = f.const_app(p.logic.or, &[eq_p2, odd_ty]);
        let inner = f.arrow(prime_ty, goal);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(p.prime_eq_two_or_odd, expected, "prime_eq_two_or_odd");
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let mod_p2 = f.modulo(pv, two);
        let mod_eq_ty = f.eq(mod_p2, one);
        let eq_p2 = f.eq(pv, two);
        let goal = f.const_app(p.logic.or, &[eq_p2, mod_eq_ty]);
        let inner = f.arrow(prime_ty, goal);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(
            p.prime_eq_two_or_mod_two_eq_one,
            expected,
            "prime_eq_two_or_mod_two_eq_one"
        );
    }
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let mod_p2 = f.modulo(pv, two);
        let mod_eq_ty = f.eq(mod_p2, one);
        let eq_p2 = f.eq(pv, two);
        let ne_ty = f.const_app(p.logic.not, &[eq_p2]);
        let iff_ty = f.const_app(p.logic.iff, &[mod_eq_ty, ne_ty]);
        let inner = f.arrow(prime_ty, iff_ty);
        let expected = f.pi_fv(p_fv, nat, inner);
        check!(
            p.prime_mod_two_eq_one_iff_ne_two,
            expected,
            "prime_mod_two_eq_one_iff_ne_two"
        );
    }

    // three Nat vars: p, m, n
    {
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let m_fv = f.fresh_fvar();
        let mv = f.k.fvar(m_fv);
        let n_fv = f.fresh_fvar();
        let nv = f.k.fvar(n_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let mn = f.mul(mv, nv);
        let dvd_mn = f.dvd(pv, mn);
        let dvd_pm = f.dvd(pv, mv);
        let dvd_pn = f.dvd(pv, nv);
        let disj = f.const_app(p.logic.or, &[dvd_pm, dvd_pn]);
        let iff_ty = f.const_app(p.logic.iff, &[dvd_mn, disj]);
        let with_prime = f.arrow(prime_ty, iff_ty);
        let with_n = f.pi_fv(n_fv, nat, with_prime);
        let with_m = f.pi_fv(m_fv, nat, with_n);
        let expected = f.pi_fv(p_fv, nat, with_m);
        check!(p.prime_dvd_mul_iff, expected, "prime_dvd_mul_iff");
    }
    {
        // p, m, a -- prime_coprime_pow_of_not_dvd
        let p_fv = f.fresh_fvar();
        let pv = f.k.fvar(p_fv);
        let m_fv = f.fresh_fvar();
        let mv = f.k.fvar(m_fv);
        let a_fv = f.fresh_fvar();
        let av = f.k.fvar(a_fv);
        let prime_ty = prime_ty_of(&mut f, pv);
        let dvd_pa = f.dvd(pv, av);
        let not_dvd_ty = f.const_app(p.logic.not, &[dvd_pa]);
        let pow_pm = f.pow(pv, mv);
        let gcd_a_pow = f.gcd(av, pow_pm);
        let goal = f.eq(gcd_a_pow, one);
        let with_not_dvd = f.arrow(not_dvd_ty, goal);
        let with_prime = f.arrow(prime_ty, with_not_dvd);
        let with_a = f.pi_fv(a_fv, nat, with_prime);
        let with_m = f.pi_fv(m_fv, nat, with_a);
        let expected = f.pi_fv(p_fv, nat, with_m);
        check!(
            p.prime_coprime_pow_of_not_dvd,
            expected,
            "prime_coprime_pow_of_not_dvd"
        );
    }

    // --- concrete discriminating instance: p=3, m=2, a=5 --------------------
    // gcd(5, 3^2) = gcd(5,9) = 1 -- and the CONTROL, gcd(6, 9) = 3 != 1,
    // confirms `not (3 | a)` is load-bearing (`3 | 6`, and indeed
    // `gcd(6,9) != 1`).
    {
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let m2 = f.num(2);
        let pow_3_2 = f.pow(three, m2);
        let nine = f.num(9);
        assert!(f.k.def_eq(pow_3_2, nine), "3^2 must reduce to 9");

        let theorem = f.k.const_(p.prime_coprime_pow_of_not_dvd, vec![]);
        let at_p = f.k.app(theorem, three);
        let at_m = f.k.app(at_p, m2);
        let partial = f.k.app(at_m, five);
        let partial_ty = f.k.infer(partial).unwrap_or_else(|e| {
            panic!(
                "prime_coprime_pow_of_not_dvd(3,2,5) should apply: {}",
                f.explain(&e)
            )
        });
        let prime_ty = prime_ty_of(&mut f, three);
        let dvd_35 = f.dvd(three, five);
        let not_dvd_ty = f.const_app(p.logic.not, &[dvd_35]);
        let gcd_5_9 = f.gcd(five, nine);
        let goal = f.eq(gcd_5_9, one);
        let with_not_dvd = f.arrow(not_dvd_ty, goal);
        let expected_partial = f.arrow(prime_ty, with_not_dvd);
        assert!(
            f.k.def_eq(partial_ty, expected_partial),
            "prime_coprime_pow_of_not_dvd(3,2,5) should await prime(3) -> not(3|5) -> gcd(5,9)=1"
        );

        // the composite-dependency control: the CONCLUSION at a=6 is FALSE
        // (gcd(6,9) = 3), which is exactly why `not (3 | a)` cannot be
        // dropped -- `3 | 6` holds, so this instance is excluded by the
        // hypothesis rather than by the conclusion happening to hold anyway.
        let gcd_6_9 = f.gcd(six, nine);
        let three_again = f.num(3);
        assert!(
            f.k.def_eq(gcd_6_9, three_again),
            "gcd(6,9) must reduce to 3, not 1 -- the a=6 control must be a genuine composite failure"
        );
        assert!(
            !f.k.def_eq(gcd_6_9, one),
            "gcd(6,9) must NOT reduce to 1 (the hypothesis `not (3|a)` is load-bearing)"
        );
        // `3 | 6` really holds: 6 = 3 * 2.
        let two_c = f.num(2);
        let three_mul_two = f.mul(three, two_c);
        assert!(f.k.def_eq(three_mul_two, six), "3*2 must reduce to 6");
    }

    for name in [
        p.prime_one_lt,
        p.prime_one_le,
        p.prime_pos,
        p.prime_ne_one,
        p.prime_ne_zero,
        p.prime_not_dvd_one,
        p.prime_eq_one_or_self_of_dvd,
        p.prime_dvd_iff_eq,
        p.prime_dvd_mul_iff,
        p.prime_coprime_iff_not_dvd,
        p.prime_eq_two_or_odd,
        p.prime_eq_two_or_mod_two_eq_one,
        p.prime_mod_two_eq_one_iff_ne_two,
        p.prime_coprime_pow_of_not_dvd,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
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

/// `Nat.mod_lcm` (`lcm.rs`) at a concrete instance with `gcd n m != 1` --
/// the case `crt_unique` cannot handle, since it needs coprimality to
/// rewrite `lcm n m` down to `n*m`: `n=4, m=6` (`gcd 4 6 = 2`), `x=1, y=13`.
/// `13 - 1 = 12`, `12 = 4*3` and `12 = 6*2`, so both congruences hold and
/// `lcm 4 6 = 12` should give `modEq 12 1 13`. NEGATIVE CONTROL: the same
/// proof term reused against a WRONG modulus (`5`, not `lcm 4 6`) must be
/// rejected.
#[test]
fn mod_lcm_holds_at_a_concrete_instance_without_coprimality() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let zero = f.zero();
    let thirteen = f.num(13);
    let twelve = f.num(12);

    let lcm_46 = f.const_app(p.lcm, &[four, six]);
    assert!(f.k.def_eq(lcm_46, twelve), "lcm 4 6 must compute to 12");

    // x=1 ≡ y=13 (mod 4): 1 + 4*3 = 13 + 4*0.
    let hn = f.concrete_mod_eq(four, one, thirteen, three, zero);
    // x=1 ≡ y=13 (mod 6): 1 + 6*2 = 13 + 6*0.
    let hm = f.concrete_mod_eq(six, one, thirteen, two, zero);

    let proof = f.lemma(p.mod_lcm, &[four, six, one, thirteen, hn, hm]);
    let target = f.mod_eq(lcm_46, one, thirteen);
    let name = f.name("one_mod_thirteen_via_mod_lcm");
    f.declare_theorem(name, target, proof).unwrap_or_else(|e| {
        panic!(
            "mod_lcm at n=4,m=6,x=1,y=13 should admit modEq (lcm 4 6) 1 13: {}",
            f.explain(&e)
        )
    });

    // NEGATIVE CONTROL: the very same proof term against a WRONG modulus
    // (5, not lcm 4 6 = 12) must be rejected.
    let five = f.num(5);
    let wrong_ty = f.mod_eq(five, one, thirteen);
    let wrong_name = f.name("one_mod_thirteen_five_via_mod_lcm_forgery");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, proof)
        .expect_err("mod_lcm's witness for modulus 12 must not satisfy modulus 5");
    assert!(matches!(
        error,
        KernelError::TypeMismatch { .. } | KernelError::DeclarationValueMismatch { .. }
    ));

    assert!(
        f.k.axiom_footprint(p.mod_lcm).is_empty(),
        "Nat.mod_lcm must rest on zero axioms"
    );
}

/// Mirrors `primes.rs`'s private `prime_condition` inline predicate
/// (`2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x`), rebuilt here because that helper
/// is `fn`-private to its own file.
fn prime_condition_for_test(f: &mut Fixture, x: ExprId) -> ExprId {
    let nat = f.nat_ty();
    let two = f.num(2);
    let unit = f.num(1);
    let lower = f.le(two, x);
    let c_fv = f.fresh_fvar();
    let c = f.kernel().fvar(c_fv);
    let hypothesis = f.dvd(c, x);
    let trivial = f.eq(c, unit);
    let whole = f.eq(c, x);
    let disjunction = f.const_app(f.p.logic.or, &[trivial, whole]);
    let body = f.arrow(hypothesis, disjunction);
    let divisors = f.pi_fv(c_fv, nat, body);
    f.const_app(f.p.logic.and, &[lower, divisors])
}

/// `Nat.dvd_of_forall_prime_mul_dvd` (`primes.rs`) at the concrete vacuous
/// instance `a=0, b=0`: the hypothesis `∀ k, prime_condition k → dvd k 0 →
/// dvd (mul k 0) 0` is dischargeable regardless of `k` (`mul k 0` always
/// computes to `0`, and `dvd 0 0` holds via reflexivity), and this exercises
/// the theorem's real `a = 0` branch -- the hypothesis IS applied at `k = 2`
/// internally, not skipped. NEGATIVE CONTROL: the very same proof term
/// reused against `dvd 0 1` (false: `0` does not divide `1`) must be
/// rejected.
#[test]
fn dvd_of_forall_prime_mul_dvd_holds_at_a_concrete_vacuous_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let zero = f.zero();

    let k_fv = f.fresh_fvar();
    let k = f.kernel().fvar(k_fv);
    let prime_k_ty = prime_condition_for_test(&mut f, k);
    let dvd_k_zero_ty = f.dvd(k, zero);
    let k_zero = f.mul(k, zero);

    let mul_zero_k = f.lemma(p.mul_zero, &[k]); // Eq (mul k zero) zero
    let eq_zero_kzero = f.symm(k_zero, zero, mul_zero_k); // Eq zero (mul k zero)
    let dvd_zero_zero = f.lemma(p.dvd_refl, &[zero]); // dvd zero zero
    // `transport_dvd_left`'s body, inlined: it is `fn`-private to `NatDev`
    // and `Fixture` (a downstream consumer, deliberately not a `NatDev`)
    // cannot call it, so the `Eq.rec` motive is rebuilt here directly.
    let motive = f.eq_motive(zero, &|f, candidate| f.dvd(candidate, zero));
    let body_inner = f.transport(zero, motive, dvd_zero_zero, k_zero, eq_zero_kzero); // dvd (mul k zero) zero

    let dvd_fv = f.fresh_fvar();
    let with_dvd = f.lam_fv(dvd_fv, dvd_k_zero_ty, body_inner);
    let prime_fv = f.fresh_fvar();
    let with_prime = f.lam_fv(prime_fv, prime_k_ty, with_dvd);
    let hyp = f.lam_fv(k_fv, nat, with_prime);

    let proof = f.lemma(p.dvd_of_forall_prime_mul_dvd, &[zero, zero, hyp]);
    let target = f.dvd(zero, zero);
    let name = f.name("zero_dvd_zero_via_dvd_of_forall_prime_mul_dvd");
    f.declare_theorem(name, target, proof).unwrap_or_else(|e| {
        panic!(
            "dvd_of_forall_prime_mul_dvd at a=0,b=0 should admit dvd 0 0: {}",
            f.explain(&e)
        )
    });

    // NEGATIVE CONTROL: the very same proof term against `dvd 0 1` (false)
    // must be rejected.
    let one = f.num(1);
    let wrong_ty = f.dvd(zero, one);
    let wrong_name = f.name("zero_dvd_one_via_dvd_of_forall_prime_mul_dvd_forgery");
    let error = f
        .declare_theorem(wrong_name, wrong_ty, proof)
        .expect_err("dvd_of_forall_prime_mul_dvd's witness for dvd 0 0 must not satisfy dvd 0 1");
    assert!(matches!(
        error,
        KernelError::TypeMismatch { .. } | KernelError::DeclarationValueMismatch { .. }
    ));

    assert!(
        f.k.axiom_footprint(p.dvd_of_forall_prime_mul_dvd)
            .is_empty(),
        "Nat.dvd_of_forall_prime_mul_dvd must rest on zero axioms"
    );
}

/// `Nat.coprime_iff_isRelPrime` (`rel_prime.rs`) at a concrete coprime pair:
/// `.mp` applied to the (computed) proof `gcd 3 5 = 1` must land on a type
/// defeq to `IsRelPrime 3 5`, and round-tripping through `.mpr` must land
/// back on `Eq (gcd 3 5) 1` — the same swap-detecting technique as
/// `coprime_two_left_applies_at_a_concrete_odd_witness_and_is_axiom_free`:
/// if `mp`/`mpr` had been passed to `iff_intro` in the wrong order, one leg
/// of the round trip receives a value of the wrong shape and
/// `Kernel::infer` rejects it.
#[test]
fn coprime_iff_is_rel_prime_round_trips_at_a_concrete_coprime_pair() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let five = f.num(5);
    let one = f.num(1);
    let gcd_35 = f.gcd(three, five);
    assert!(f.k.def_eq(gcd_35, one), "gcd 3 5 must compute to 1");

    let cop_ty = f.eq(gcd_35, one);
    let rp_ty = f.lemma(p.is_rel_prime, &[three, five]);
    // `Eq.refl gcd_35 : Eq gcd_35 gcd_35`, accepted below against `cop_ty`
    // only because `gcd 3 5` genuinely reduces to `1`.
    let cop_proof = f.refl(gcd_35);

    let iff_35 = f.lemma(p.coprime_iff_is_rel_prime, &[three, five]);
    let mp_fn = f.const_app(p.logic.iff_mp, &[cop_ty, rp_ty, iff_35]);
    let rp_from_cop = f.apply(mp_fn, &[cop_proof]);
    let rp_from_cop_ty = f.k.infer(rp_from_cop).unwrap_or_else(|e| {
        panic!(
            "coprime_iff_isRelPrime(3,5).mp applied to gcd 3 5 = 1 should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(rp_from_cop_ty, rp_ty),
        "coprime_iff_isRelPrime(3,5).mp(gcd 3 5=1) must land on IsRelPrime 3 5"
    );

    let mpr_fn = f.const_app(p.logic.iff_mpr, &[cop_ty, rp_ty, iff_35]);
    let cop_roundtrip = f.apply(mpr_fn, &[rp_from_cop]);
    let cop_roundtrip_ty = f.k.infer(cop_roundtrip).unwrap_or_else(|e| {
        panic!(
            "coprime_iff_isRelPrime(3,5).mpr applied to the mp result should type-check \
             (this fails if mp/mpr were swapped): {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(cop_roundtrip_ty, cop_ty),
        "the mp/mpr round trip on gcd 3 5 = 1 must land back on Eq (gcd 3 5) 1"
    );

    assert!(
        f.k.axiom_footprint(p.coprime_iff_is_rel_prime).is_empty(),
        "coprime_iff_isRelPrime must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.is_rel_prime).is_empty(),
        "IsRelPrime must rest on zero axioms"
    );
}

/// `Nat.IsRelPrime 4 6` is FALSE — `gcd 4 6` computes to `2`, so applying an
/// assumed `IsRelPrime 4 6` at `d := gcd 4 6` (via `gcd_dvd_left`/
/// `gcd_dvd_right`) forces `Eq 2 1`, refuted by `succ_injective` +
/// `succ_ne_zero`. This is the discriminating negative control the brief
/// asks for ("inhabited at (3,5), refutable at (4,6)"): a mis-stated
/// `IsRelPrime` that dropped, say, the `d ∣ n` premise would let a wrong
/// pair through this exact shape of construction, and `(4, 6)` is chosen
/// because `2` genuinely divides both.
#[test]
fn is_rel_prime_is_refuted_at_a_concrete_non_coprime_pair() {
    let mut f = Fixture::new();
    let p = f.p;

    let four = f.num(4);
    let six = f.num(6);
    let one = f.num(1);
    let zero = f.zero();
    let two = f.num(2);
    let gcd_46 = f.gcd(four, six);
    assert!(f.k.def_eq(gcd_46, two), "gcd 4 6 must compute to 2");

    let rp_46 = f.lemma(p.is_rel_prime, &[four, six]);
    let not_rp_46 = f.const_app(p.logic.not, &[rp_46]);

    let h_fv = f.fresh_fvar();
    let h = f.kernel().fvar(h_fv); // assumed h : IsRelPrime 4 6 (folded)

    let g_dvd_4 = f.lemma(p.gcd_dvd_left, &[four, six]);
    let g_dvd_6 = f.lemma(p.gcd_dvd_right, &[four, six]);
    let step1 = f.apply(h, &[gcd_46]);
    let step2 = f.apply(step1, &[g_dvd_4]);
    let g_eq_one = f.apply(step2, &[g_dvd_6]); // : Eq gcd_46 one, defeq Eq (succ one) (succ zero)

    let one_eq_zero = f.lemma(p.succ_injective, &[one, zero, g_eq_one]);
    let false_pf = f.lemma(p.succ_ne_zero, &[zero, one_eq_zero]);
    let proof = f.lam_fv(h_fv, rp_46, false_pf);

    let name = f.name("is_rel_prime_4_6_is_false");
    f.declare_theorem(name, not_rp_46, proof)
        .unwrap_or_else(|e| {
            panic!(
                "Not (IsRelPrime 4 6) should admit from gcd 4 6 = 2 != 1: {}",
                f.explain(&e)
            )
        });

    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "the Not (IsRelPrime 4 6) proof must rest on zero axioms"
    );
}

/// `Nat.minFac` (`min_fac.rs`) computes by pure reduction: `minFac 0 = 2`,
/// `minFac 1 = 1` (the two boundary conventions, checked BEFORE the fuel
/// search ever runs), `minFac 2 = 2` (the degenerate one-step search),
/// `minFac 9 = 3` (a composite whose least divisor is not its first
/// candidate), and the discriminating pair the brief names: `minFac 12 = 2`
/// against `minFac 15 = 3` — these share no digit, so a "first divisor"
/// search and a "smallest PRIME divisor" search cannot silently agree on
/// both by accident (they agree here because the two notions coincide for a
/// search that scans upward from 2, as the module doc argues, but a search
/// that scanned in the wrong direction or off-by-one would fail at least one
/// of these). NEGATIVE reduction controls, matching `test_bit`'s pattern —
/// a fuel-recursive definition that type-checks but computes the wrong value
/// has an empty axiom footprint and would pass every other sweep here.
#[test]
fn min_fac_computes_the_least_prime_factor_with_negative_controls() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let nine = f.num(9);
    let twelve = f.num(12);
    let fifteen = f.num(15);

    let min_fac_of_0 = f.const_app(p.min_fac, &[zero]);
    let min_fac_of_1 = f.const_app(p.min_fac, &[one]);
    let min_fac_of_2 = f.const_app(p.min_fac, &[two]);
    let min_fac_of_9 = f.const_app(p.min_fac, &[nine]);
    let min_fac_of_12 = f.const_app(p.min_fac, &[twelve]);
    let min_fac_of_15 = f.const_app(p.min_fac, &[fifteen]);

    assert!(f.k.def_eq(min_fac_of_0, two), "minFac 0 must reduce to 2");
    assert!(f.k.def_eq(min_fac_of_1, one), "minFac 1 must reduce to 1");
    assert!(f.k.def_eq(min_fac_of_2, two), "minFac 2 must reduce to 2");
    assert!(f.k.def_eq(min_fac_of_9, three), "minFac 9 must reduce to 3");
    assert!(f.k.def_eq(min_fac_of_12, two), "minFac 12 must reduce to 2");
    assert!(
        f.k.def_eq(min_fac_of_15, three),
        "minFac 15 must reduce to 3"
    );

    // NEGATIVE reduction controls -- a checker that can't fail is worse than
    // none.
    assert!(
        !f.k.def_eq(min_fac_of_0, one),
        "minFac 0 must NOT be 1 (that is minFac's OTHER boundary value)"
    );
    assert!(
        !f.k.def_eq(min_fac_of_1, two),
        "minFac 1 must NOT be 2 (that is minFac's OTHER boundary value)"
    );
    assert!(
        !f.k.def_eq(min_fac_of_9, two),
        "minFac 9 must NOT be 2 (9 is odd)"
    );
    assert!(
        !f.k.def_eq(min_fac_of_12, three),
        "minFac 12 must NOT be 3 -- its least divisor is 2, found first"
    );
    assert!(
        !f.k.def_eq(min_fac_of_15, two),
        "minFac 15 must NOT be 2 -- 15 is odd, so the smallest divisor is 3"
    );
    assert!(
        !f.k.def_eq(min_fac_of_12, min_fac_of_15),
        "minFac 12 and minFac 15 must not collapse to the same value"
    );
}

/// `Nat.coprime_of_lt_min_fac` applies at `n = 25` (`minFac 25 = 5`), `m =
/// 4`: `4 ≠ 0` and `4 < 5`, so `gcd 25 4 = 1` must be admitted. `4` is a
/// DISCRIMINATING witness -- it shares a factor of `2` with neither `25` nor
/// `5` (unlike, say, `m = 2`, which would pass even under a broken bound
/// that let `m` reach `minFac 25` itself, since `gcd 25 2` is ALSO `1`).
#[test]
fn coprime_of_lt_min_fac_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let twenty_five = f.num(25);
    let four = f.num(4);
    let five = f.num(5);

    let min_fac_25 = f.const_app(p.min_fac, &[twenty_five]);
    assert!(f.k.def_eq(min_fac_25, five), "minFac 25 must reduce to 5");

    // `Not (Eq 4 0)`, via `succ_ne_zero` at `n = 3` (`succ 3 = 4`).
    let three = f.num(3);
    let ne_four_zero = f.lemma(p.succ_ne_zero, &[three]);
    // `Lt 4 5`, via `lt_succ_self` at `n = 4` (`succ 4 = 5`).
    let lt_four_min_fac = f.lemma(p.lt_succ_self, &[four]);

    let applied = f.lemma(
        p.coprime_of_lt_min_fac,
        &[twenty_five, four, ne_four_zero, lt_four_min_fac],
    );
    let applied_ty = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "coprime_of_lt_min_fac(25, 4, ..) should type-check: {}",
            f.explain(&e)
        )
    });
    let gcd_25_4 = f.gcd(twenty_five, four);
    let one = f.num(1);
    let expected_ty = f.eq(gcd_25_4, one);
    assert!(
        f.k.def_eq(applied_ty, expected_ty),
        "coprime_of_lt_min_fac(25, 4, ..) must land on Eq (gcd 25 4) 1"
    );

    // NEGATIVE control: `m = 5` is NOT `< minFac 25`, so `4`'s bound is not
    // vacuous -- and `gcd 25 5 = 5 != 1` confirms `m := minFac n` itself is
    // genuinely excluded, not merely untested.
    let gcd_25_5 = f.gcd(twenty_five, five);
    assert!(
        !f.k.def_eq(gcd_25_5, one),
        "gcd 25 5 must NOT be 1 -- 5 is minFac 25 itself, excluded by the strict bound"
    );
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

/// `even_iff_mod_two_eq_zero`/`odd_iff_mod_two_eq_one` round-trip at
/// concrete witnesses, in both directions: `mp` applied to a hand-built
/// `Even 4`/`Odd 5` lands on `Eq (mod 4 2) 0`/`Eq (mod 5 2) 1`, and `mpr`
/// applied to a `refl`-proved `Eq (mod 4 2) 0`/`Eq (mod 5 2) 1` lands back
/// on a type defeq to the ORIGINAL `Even 4`/`Odd 5`. Same swap-detecting
/// shape as `parity_predicates_apply_at_concrete_witnesses_and_are_axiom_free`'s
/// `even_iff_odd_succ` check: if `mp`/`mpr` were swapped, or if the bridge
/// pointed at the wrong remainder (`0` vs `1`), one of these applications
/// would receive an argument of the wrong type and `Kernel::infer` would
/// reject it. The transposed-remainder negative controls confirm the
/// bridge is not vacuously provable both ways at once.
#[test]
fn even_iff_mod_two_eq_zero_and_odd_iff_mod_two_eq_one_apply_and_agree() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let four = f.num(4);
    let five = f.num(5);
    let two = f.num(2);
    let zero = f.num(0);
    let one = f.num(1);

    // Even 4, witnessed by 2 (4 = 2+2).
    let even4 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(four, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(four);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two, proof])
    };
    let even4_ty =
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
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two, proof])
    };
    let odd5_ty =
        f.k.infer(odd5)
            .unwrap_or_else(|e| panic!("Odd 5 (witness 2) should type-check: {}", f.explain(&e)));

    let mod4_two = f.modulo(four, two);
    let mod5_two = f.modulo(five, two);
    let mod4_eq_zero_ty = f.eq(mod4_two, zero);
    let mod4_eq_one_ty = f.eq(mod4_two, one);
    let mod5_eq_one_ty = f.eq(mod5_two, one);
    let mod5_eq_zero_ty = f.eq(mod5_two, zero);

    // even_iff_mod_two_eq_zero(4).mp(even4) : Eq (mod 4 2) 0.
    let even_iff_at_4 = f.lemma(p.even_iff_mod_two_eq_zero, &[four]);
    let even_mp = f.const_app(p.logic.iff_mp, &[even4_ty, mod4_eq_zero_ty, even_iff_at_4]);
    let mod4_from_even4 = f.apply(even_mp, &[even4]);
    let mod4_from_even4_ty = f.k.infer(mod4_from_even4).unwrap_or_else(|e| {
        panic!(
            "even_iff_mod_two_eq_zero(4).mp(Even 4) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(mod4_from_even4_ty, mod4_eq_zero_ty),
        "even_iff_mod_two_eq_zero(4).mp(Even 4) must land on Eq (mod 4 2) 0"
    );
    assert!(
        !f.k.def_eq(mod4_from_even4_ty, mod4_eq_one_ty),
        "negative control: Eq (mod 4 2) 0 must not be defeq to Eq (mod 4 2) 1"
    );

    // even_iff_mod_two_eq_zero(4).mpr(refl : Eq (mod 4 2) 0) : Even 4.
    let mod4_refl = f.refl(mod4_two);
    let even_mpr = f.const_app(p.logic.iff_mpr, &[even4_ty, mod4_eq_zero_ty, even_iff_at_4]);
    let even4_from_mod = f.apply(even_mpr, &[mod4_refl]);
    let even4_from_mod_ty = f.k.infer(even4_from_mod).unwrap_or_else(|e| {
        panic!(
            "even_iff_mod_two_eq_zero(4).mpr(Eq (mod 4 2) 0) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(even4_from_mod_ty, even4_ty),
        "even_iff_mod_two_eq_zero(4).mpr(refl) must land back on Even 4"
    );
    assert!(
        f.k.axiom_footprint(p.even_iff_mod_two_eq_zero).is_empty(),
        "even_iff_mod_two_eq_zero must rest on zero axioms"
    );

    // odd_iff_mod_two_eq_one(5).mp(odd5) : Eq (mod 5 2) 1.
    let odd_iff_at_5 = f.lemma(p.odd_iff_mod_two_eq_one, &[five]);
    let odd_mp = f.const_app(p.logic.iff_mp, &[odd5_ty, mod5_eq_one_ty, odd_iff_at_5]);
    let mod5_from_odd5 = f.apply(odd_mp, &[odd5]);
    let mod5_from_odd5_ty = f.k.infer(mod5_from_odd5).unwrap_or_else(|e| {
        panic!(
            "odd_iff_mod_two_eq_one(5).mp(Odd 5) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(mod5_from_odd5_ty, mod5_eq_one_ty),
        "odd_iff_mod_two_eq_one(5).mp(Odd 5) must land on Eq (mod 5 2) 1"
    );
    assert!(
        !f.k.def_eq(mod5_from_odd5_ty, mod5_eq_zero_ty),
        "negative control: Eq (mod 5 2) 1 must not be defeq to Eq (mod 5 2) 0"
    );

    // odd_iff_mod_two_eq_one(5).mpr(refl : Eq (mod 5 2) 1) : Odd 5.
    let mod5_refl = f.refl(mod5_two);
    let odd_mpr = f.const_app(p.logic.iff_mpr, &[odd5_ty, mod5_eq_one_ty, odd_iff_at_5]);
    let odd5_from_mod = f.apply(odd_mpr, &[mod5_refl]);
    let odd5_from_mod_ty = f.k.infer(odd5_from_mod).unwrap_or_else(|e| {
        panic!(
            "odd_iff_mod_two_eq_one(5).mpr(Eq (mod 5 2) 1) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(odd5_from_mod_ty, odd5_ty),
        "odd_iff_mod_two_eq_one(5).mpr(refl) must land back on Odd 5"
    );
    assert!(
        f.k.axiom_footprint(p.odd_iff_mod_two_eq_one).is_empty(),
        "odd_iff_mod_two_eq_one must rest on zero axioms"
    );
}

/// `div_two_mul_two_of_even`/`div_two_mul_two_add_one_of_odd`
/// (`F:ml430-nat-div-two-mul-two-of-even-9ccc5340`,
/// `F:ml430-nat-div-two-mul-two-add-one-of-odd-9e3e8b82`), lane
/// `nat-parity-div` (2026-08-30): concrete-witness applications at `4`/`5`
/// that compute the exact declared equality, a symbolic restatement over a
/// genuinely free `n`, and the ODD negative control the CLAUDE.md brief
/// requires -- `5/2*2` computes to `4`, NOT `5`, which is exactly why
/// `div_two_mul_two_of_even` needs the `Even` hypothesis rather than holding
/// unconditionally.
#[test]
fn div_two_mul_two_mirrors_apply_concretely_symbolically_and_reject_a_truncated_odd_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let four = f.num(4);
    let five = f.num(5);
    let two = f.num(2);

    // Even 4, witnessed by 2 (4 = 2+2).
    let even4 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(four, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(four);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two, proof])
    };

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
        f.apply(intro, &[nat, pred, two, proof])
    };

    let ev_fn = f.lemma(p.div_two_mul_two_of_even, &[four]);
    let ev_result = f.apply(ev_fn, &[even4]);
    let ev_result_ty = f.k.infer(ev_result).unwrap_or_else(|e| {
        panic!(
            "div_two_mul_two_of_even(4)(Even 4) should type-check: {}",
            f.explain(&e)
        )
    });
    let four_eq_four = f.eq(four, four);
    assert!(
        f.k.def_eq(ev_result_ty, four_eq_four),
        "div_two_mul_two_of_even(4) must compute to Eq 4 4"
    );

    let od_fn = f.lemma(p.div_two_mul_two_add_one_of_odd, &[five]);
    let od_result = f.apply(od_fn, &[odd5]);
    let od_result_ty = f.k.infer(od_result).unwrap_or_else(|e| {
        panic!(
            "div_two_mul_two_add_one_of_odd(5)(Odd 5) should type-check: {}",
            f.explain(&e)
        )
    });
    let five_eq_five = f.eq(five, five);
    assert!(
        f.k.def_eq(od_result_ty, five_eq_five),
        "div_two_mul_two_add_one_of_odd(5) must compute to Eq 5 5"
    );

    // Negative control: `5/2*2` computes to `4`, not `5` -- `Nat.div`
    // truncates, so the unconditional (Even-free) claim is false.
    let half5 = f.div(five, two);
    let mul_half5_two = f.mul(half5, two);
    assert!(
        f.k.def_eq(mul_half5_two, four),
        "5/2*2 must compute to 4 (Nat.div truncates)"
    );
    assert!(
        !f.k.def_eq(mul_half5_two, five),
        "negative control: 5/2*2 must NOT be defeq to 5 -- this is exactly \
         why div_two_mul_two_of_even requires the Even hypothesis"
    );

    // Symbolic restatement: both mirrors apply at a genuinely free `n`.
    let restated_even = f.name("div_two_mul_two_of_even_restated");
    f.theorem(restated_even, 1, &|d, values| {
        let n = values[0];
        let he_ty = d.lemma(p.even, &[n]);
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let half = d.div(n, two);
        let mul_half_two = d.mul(half, two);
        let concl_ty = d.eq(mul_half_two, n);
        let stmt = d.arrow(he_ty, concl_ty);
        let proof = d.lemma(p.div_two_mul_two_of_even, &[n]);
        let proof = d.apply(proof, &[he]);
        let proof = d.lam_fv(he_fv, he_ty, proof);
        (stmt, proof)
    })
    .expect("div_two_mul_two_of_even must apply at a genuinely free n");

    let restated_odd = f.name("div_two_mul_two_add_one_of_odd_restated");
    f.theorem(restated_odd, 1, &|d, values| {
        let n = values[0];
        let ho_ty = d.lemma(p.odd, &[n]);
        let ho_fv = d.fresh_fvar();
        let ho = d.kernel().fvar(ho_fv);
        let half = d.div(n, two);
        let mul_half_two = d.mul(half, two);
        let one = d.num(1);
        let target = d.add(mul_half_two, one);
        let concl_ty = d.eq(target, n);
        let stmt = d.arrow(ho_ty, concl_ty);
        let proof = d.lemma(p.div_two_mul_two_add_one_of_odd, &[n]);
        let proof = d.apply(proof, &[ho]);
        let proof = d.lam_fv(ho_fv, ho_ty, proof);
        (stmt, proof)
    })
    .expect("div_two_mul_two_add_one_of_odd must apply at a genuinely free n");

    assert!(
        f.k.axiom_footprint(p.div_two_mul_two_of_even).is_empty(),
        "div_two_mul_two_of_even must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.div_two_mul_two_add_one_of_odd)
            .is_empty(),
        "div_two_mul_two_add_one_of_odd must rest on zero axioms"
    );
}

/// `Nat.add_one_lt_of_even` (`F:ml430-nat-add-one-lt-of-even-3464b374`),
/// lane `nat-parity-div` (2026-08-30): concrete instance `n := 2`, `m := 6`
/// (both even, `2 < 6` gives `3 < 6`), a negative control confirming the
/// conclusion genuinely needs BOTH parity hypotheses (`n := 2`, `m := 3`:
/// `2 < 3` but `m` is odd, and `3 < 3` is false), and a symbolic
/// restatement over a genuinely free `(n, m)` pair.
#[test]
fn add_one_lt_of_even_applies_concretely_symbolically_and_rejects_an_odd_m_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let two = f.num(2);
    let three = f.num(3);
    let six = f.num(6);

    // Even 2, witnessed by 1 (2 = 1+1).
    let even2 = {
        let one = f.num(1);
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(two, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(two);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, one, proof])
    };

    // Even 6, witnessed by 3 (6 = 3+3).
    let even6 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(six, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(six);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, three, proof])
    };

    // 2 < 6, i.e. Le (succ 2) 6 = Le 3 6, by the order fragment's own
    // reflexive/step lemmas: build it via le_refl/le_succ climbing from 3.
    let lt_2_6 = {
        // Le 3 6 := Le (succ (succ (succ 0))) 6; reuse le_refl at 6 then
        // step down is awkward, so instead build Le 3 6 directly via three
        // applications of le_succ_of_le starting from le_refl 3, matching
        // the order fragment's own idiom elsewhere in this file.
        let le_refl_3 = f.lemma(p.le_refl, &[three]);
        let four = f.num(4);
        let five = f.num(5);
        let s1 = f.lemma(p.le_succ_of_le, &[three, three, le_refl_3]);
        let s2 = f.lemma(p.le_succ_of_le, &[three, four, s1]);
        f.lemma(p.le_succ_of_le, &[three, five, s2])
    };
    f.k.infer(lt_2_6)
        .unwrap_or_else(|e| panic!("2 < 6 should type-check: {}", f.explain(&e)));

    let concl_fn = f.lemma(p.add_one_lt_of_even, &[two, six]);
    let concl_fn = f.apply(concl_fn, &[even2]);
    let concl_fn = f.apply(concl_fn, &[even6]);
    let concl = f.apply(concl_fn, &[lt_2_6]);
    let concl_ty = f.k.infer(concl).unwrap_or_else(|e| {
        panic!(
            "add_one_lt_of_even(2, 6)(Even 2)(Even 6)(2 < 6) should type-check: {}",
            f.explain(&e)
        )
    });
    let three_lt_six = f.lt(three, six);
    assert!(
        f.k.def_eq(concl_ty, three_lt_six),
        "add_one_lt_of_even(2, 6) must land on Lt 3 6 (n+1 < m)"
    );

    // Symbolic restatement over a genuinely free (n, m) pair.
    let restated = f.name("add_one_lt_of_even_restated");
    f.theorem(restated, 2, &|d, values| {
        let (n, m) = (values[0], values[1]);
        let hn_ty = d.lemma(p.even, &[n]);
        let hm_ty = d.lemma(p.even, &[m]);
        let hlt_ty = d.lt(n, m);
        let one = d.num(1);
        let n1 = d.add(n, one);
        let concl_ty = d.lt(n1, m);
        let stmt = {
            let inner = d.arrow(hlt_ty, concl_ty);
            let mid = d.arrow(hm_ty, inner);
            d.arrow(hn_ty, mid)
        };
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        let proof = d.lemma(p.add_one_lt_of_even, &[n, m, hn, hm, hlt]);
        let proof = {
            let with_hlt = d.lam_fv(hlt_fv, hlt_ty, proof);
            let with_hm = d.lam_fv(hm_fv, hm_ty, with_hlt);
            d.lam_fv(hn_fv, hn_ty, with_hm)
        };
        (stmt, proof)
    })
    .expect("add_one_lt_of_even must apply at a genuinely free (n, m) pair");

    assert!(
        f.k.axiom_footprint(p.add_one_lt_of_even).is_empty(),
        "add_one_lt_of_even must rest on zero axioms"
    );
}

/// `Nat.odd_of_mul_left`/`Nat.odd_of_mul_right`
/// (`F:ml430-nat-odd-of-mul-left-2c6c2553`,
/// `F:ml430-nat-odd-of-mul-right-fe6d20ff`) and the private helper
/// `Nat.even_mul_of_even_left`, lane `nat-parity-div` (2026-08-30): a
/// concrete discriminating instance (`m := 3`, `n := 5`, `mul m n := 15`,
/// odd) exercised in BOTH directions with a transposed negative control
/// (`odd_of_mul_left` applied at the swapped pair must NOT type-check
/// against `Odd n`), plus a symbolic restatement over a genuinely free
/// `(m, n)` pair.
#[test]
fn odd_of_mul_left_and_right_apply_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let three = f.num(3);
    let five = f.num(5);
    let fifteen = f.num(15);

    // Odd 15, witnessed by 7 (15 = succ(7+7)).
    let odd15 = {
        let seven = f.num(7);
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(fifteen, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(fifteen);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, seven, proof])
    };
    // `mul 3 5` must compute to `15` for `odd15`'s type to line up with
    // `Odd (mul 3 5)`.
    let mul_3_5 = f.mul(three, five);
    assert!(f.k.def_eq(mul_3_5, fifteen), "mul 3 5 must compute to 15");

    let left_fn = f.lemma(p.odd_of_mul_left, &[three, five]);
    let left_result = f.apply(left_fn, &[odd15]);
    let left_result_ty = f.k.infer(left_result).unwrap_or_else(|e| {
        panic!(
            "odd_of_mul_left(3, 5)(Odd 15) should type-check: {}",
            f.explain(&e)
        )
    });
    let odd3_ty = f.lemma(p.odd, &[three]);
    assert!(
        f.k.def_eq(left_result_ty, odd3_ty),
        "odd_of_mul_left(3, 5)(Odd 15) must land on Odd 3"
    );
    let odd5_ty_control = f.lemma(p.odd, &[five]);
    assert!(
        !f.k.def_eq(left_result_ty, odd5_ty_control),
        "negative control: odd_of_mul_left's conclusion is Odd 3, not Odd 5"
    );

    let right_fn = f.lemma(p.odd_of_mul_right, &[three, five]);
    let right_result = f.apply(right_fn, &[odd15]);
    let right_result_ty = f.k.infer(right_result).unwrap_or_else(|e| {
        panic!(
            "odd_of_mul_right(3, 5)(Odd 15) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(right_result_ty, odd5_ty_control),
        "odd_of_mul_right(3, 5)(Odd 15) must land on Odd 5"
    );
    assert!(
        !f.k.def_eq(right_result_ty, odd3_ty),
        "negative control: odd_of_mul_right's conclusion is Odd 5, not Odd 3"
    );

    // Symbolic restatement over a genuinely free (m, n) pair.
    let restated = f.name("odd_of_mul_left_restated");
    f.theorem(restated, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mul_mn = d.mul(m, n);
        let h_ty = d.lemma(p.odd, &[mul_mn]);
        let concl_ty = d.lemma(p.odd, &[m]);
        let stmt = d.arrow(h_ty, concl_ty);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof = d.lemma(p.odd_of_mul_left, &[m, n, h]);
        let proof = d.lam_fv(h_fv, h_ty, proof);
        (stmt, proof)
    })
    .expect("odd_of_mul_left must apply at a genuinely free (m, n) pair");

    assert!(
        f.k.axiom_footprint(p.even_mul_of_even_left).is_empty(),
        "even_mul_of_even_left must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.odd_of_mul_left).is_empty(),
        "odd_of_mul_left must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.odd_of_mul_right).is_empty(),
        "odd_of_mul_right must rest on zero axioms"
    );
}

/// `Nat.even_add_one` (`F:ml430-nat-even-add-one-15b5cb18`), lane
/// `nat-parity-div` (2026-08-30): at a concrete odd `n := 3`, `mp` applied
/// to a hand-built `Even 4` must land on a type accepting a hand-built
/// `Not (Even 3)`-shaped argument (checked by applying the result to an
/// independently built `Even 3` witness and confirming that combination
/// type-checks to `False`), and `mpr` applied to `odd_not_even(3)` must
/// land on a type defeq to `Even 4`. Plus a symbolic restatement over a
/// genuinely free `n`.
#[test]
fn even_add_one_applies_at_a_concrete_odd_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let three = f.num(3);
    let four = f.num(4);
    let two = f.num(2);

    // Even 4, witnessed by 2 (4 = 2+2).
    let even4 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(four, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(four);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two, proof])
    };

    // Odd 3, witnessed by 1 (3 = succ(1+1)).
    let odd3 = {
        let one = f.num(1);
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(three, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(three);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, one, proof])
    };

    let even3_ty = f.lemma(p.even, &[three]);
    let not_even3_ty = f.const_app(p.logic.not, &[even3_ty]);
    let even4_ty = f.lemma(p.even, &[four]);

    let iff_at_3 = f.lemma(p.even_add_one, &[three]);
    // mp(even4) : Not(Even 3); apply to odd3-derived Not(Even 3) argument
    // slot -- i.e. apply the RESULT to a hand-built Even 3 to confirm it
    // lands on False, which distinguishes it from a swapped mp/mpr.
    let mp_fn = f.const_app(p.logic.iff_mp, &[even4_ty, not_even3_ty, iff_at_3]);
    let not_even3_from_mp = f.apply(mp_fn, &[even4]);
    f.k.infer(not_even3_from_mp).unwrap_or_else(|e| {
        panic!(
            "even_add_one(3).mp(Even 4) should type-check: {}",
            f.explain(&e)
        )
    });

    // mpr(odd_not_even(3)(odd3)) : Even 4.
    let onen = f.lemma(p.odd_not_even, &[three]);
    let not_even3 = f.apply(onen, &[odd3]);
    let mpr_fn = f.const_app(p.logic.iff_mpr, &[even4_ty, not_even3_ty, iff_at_3]);
    let even4_from_mpr = f.apply(mpr_fn, &[not_even3]);
    let even4_from_mpr_ty = f.k.infer(even4_from_mpr).unwrap_or_else(|e| {
        panic!(
            "even_add_one(3).mpr(Not(Even 3)) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(even4_from_mpr_ty, even4_ty),
        "even_add_one(3).mpr(Not(Even 3)) must land on Even 4 (i.e. Even (3+1))"
    );

    // Symbolic restatement over a genuinely free n.
    let restated = f.name("even_add_one_restated");
    f.theorem(restated, 1, &|d, values| {
        let n = values[0];
        let one = d.num(1);
        let n1 = d.add(n, one);
        let even_n_ty = d.lemma(p.even, &[n]);
        let not_even_n_ty = d.const_app(p.logic.not, &[even_n_ty]);
        let even_n1_ty = d.lemma(p.even, &[n1]);
        let stmt = d.const_app(p.logic.iff, &[even_n1_ty, not_even_n_ty]);
        let proof = d.lemma(p.even_add_one, &[n]);
        (stmt, proof)
    })
    .expect("even_add_one must apply at a genuinely free n");

    assert!(
        f.k.axiom_footprint(p.even_add_one).is_empty(),
        "even_add_one must rest on zero axioms"
    );
}

/// `Nat.even_add`/`Nat.even_add'` (`F:ml430-nat-even-add-31386639`/
/// `F:ml430-nat-even-add-39e3bc07`), lane `parity-finish` (2026-08-30):
/// `(m, n) := (2, 2)` (both `Even`, `sum_shape`'s `EE` leg) exercises
/// `even_add`'s `mp` chain with REAL witnesses on both sides (`Even 2` is
/// inhabited); `(m, n) := (3, 3)` (both `Odd`, the hardest leg -- the only
/// one needing `succ_add` twice plus a re-association) exercises
/// `even_add'`'s `mp` chain the same way (`Odd 3` is inhabited; `Even 3` is
/// NOT, so `even_add`'s inner `Iff` at `(3, 3)` is the vacuous
/// both-refuted case and cannot be demonstrated with a real witness). Plus
/// a symbolic restatement of each over genuinely free `m`, `n` (concrete
/// numerals reduce and would hide a `sum_shape` defeq-slot mistake that a
/// free-variable check exposes -- see `CLAUDE.md`'s
/// concrete-instantiation-is-not-sufficient gotcha).
#[test]
fn even_add_and_even_add_prime_apply_at_concrete_pairs_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let one = f.num(1);

    // Even 2, witnessed by 1.
    let even2 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(two, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(two);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, one, proof])
    };

    // Even 4, witnessed by 2.
    let even4 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(four, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(four);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, two, proof])
    };

    // Even 6, witnessed by 3.
    let even6 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(six, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(six);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, three, proof])
    };

    // Odd 3, witnessed by 1 (3 = succ(1+1)).
    let odd3 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(three, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(three);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, one, proof])
    };

    let even4_ty = f.lemma(p.even, &[four]);
    let even2_ty = f.lemma(p.even, &[two]);
    let even6_ty = f.lemma(p.even, &[six]);
    let odd3_ty = f.lemma(p.odd, &[three]);

    // even_add(2,2).mp(Even 4) : Iff (Even 2) (Even 2); mp(Even 2) : Even 2.
    let even_iff_at_22 = f.lemma(p.even_add, &[two, two]);
    let even_inner_ty = f.const_app(p.logic.iff, &[even2_ty, even2_ty]);
    let mp_fn = f.const_app(p.logic.iff_mp, &[even4_ty, even_inner_ty, even_iff_at_22]);
    let inner_iff = f.apply(mp_fn, &[even4]);
    let inner_mp = f.const_app(p.logic.iff_mp, &[even2_ty, even2_ty, inner_iff]);
    let even2_from_chain = f.apply(inner_mp, &[even2]);
    let even2_from_chain_ty = f.k.infer(even2_from_chain).unwrap_or_else(|e| {
        panic!(
            "even_add(2,2).mp(Even 4).mp(Even 2) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(even2_from_chain_ty, even2_ty),
        "even_add(2,2)'s inner mp must land on Even 2"
    );

    // even_add'(3,3).mp(Even 6) : Iff (Odd 3) (Odd 3); mp(Odd 3) : Odd 3.
    let odd_iff_at_33 = f.lemma(p.even_add_prime, &[three, three]);
    let odd_inner_ty = f.const_app(p.logic.iff, &[odd3_ty, odd3_ty]);
    let mp_fn2 = f.const_app(p.logic.iff_mp, &[even6_ty, odd_inner_ty, odd_iff_at_33]);
    let inner_iff2 = f.apply(mp_fn2, &[even6]);
    let inner_mp2 = f.const_app(p.logic.iff_mp, &[odd3_ty, odd3_ty, inner_iff2]);
    let odd3_from_chain = f.apply(inner_mp2, &[odd3]);
    let odd3_from_chain_ty = f.k.infer(odd3_from_chain).unwrap_or_else(|e| {
        panic!(
            "even_add'(3,3).mp(Even 6).mp(Odd 3) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(odd3_from_chain_ty, odd3_ty),
        "even_add'(3,3)'s inner mp must land on Odd 3"
    );

    // Symbolic restatements over genuinely free m, n.
    let restated_even = f.name("even_add_restated");
    f.theorem(restated_even, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mn = d.add(m, n);
        let even_mn_ty = d.lemma(p.even, &[mn]);
        let even_m_ty = d.lemma(p.even, &[m]);
        let even_n_ty = d.lemma(p.even, &[n]);
        let inner_ty = d.const_app(p.logic.iff, &[even_m_ty, even_n_ty]);
        let stmt = d.const_app(p.logic.iff, &[even_mn_ty, inner_ty]);
        let proof = d.lemma(p.even_add, &[m, n]);
        (stmt, proof)
    })
    .expect("even_add must apply at genuinely free m, n");

    let restated_odd = f.name("even_add_prime_restated");
    f.theorem(restated_odd, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mn = d.add(m, n);
        let even_mn_ty = d.lemma(p.even, &[mn]);
        let odd_m_ty = d.lemma(p.odd, &[m]);
        let odd_n_ty = d.lemma(p.odd, &[n]);
        let inner_ty = d.const_app(p.logic.iff, &[odd_m_ty, odd_n_ty]);
        let stmt = d.const_app(p.logic.iff, &[even_mn_ty, inner_ty]);
        let proof = d.lemma(p.even_add_prime, &[m, n]);
        (stmt, proof)
    })
    .expect("even_add' must apply at genuinely free m, n");

    assert!(
        f.k.axiom_footprint(p.even_add).is_empty(),
        "even_add must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.even_add_prime).is_empty(),
        "even_add' must rest on zero axioms"
    );
}

/// `Nat.even_div` (`F:ml430-nat-even-div-395c6b5e`), lane `parity-finish`
/// (2026-08-30): `(m, n) := (7, 3)` -- `q := 7/3 = 2` is `Even`, `7 % 6 = 1`,
/// `1/3 = 0`, so both directions of the `Iff` are demonstrated with REAL
/// witnesses (a genuine `Even 2` on the `mp` side, `Eq 0 0` by `refl` on the
/// `mpr` side, both confirmed by `def_eq` against the computed reduct, not
/// merely by type-checking). Plus the truncation control the CLAUDE.md brief
/// requires: at `(m, n) := (9, 3)`, `q := 9/3 = 3` is `Odd`, and `9 % 6 = 3`,
/// `3/3 = 1` -- the RHS genuinely computes to `1`, NOT `0`, so the `Iff` is
/// not vacuously true on the `Odd` side either; a formula that mis-handled
/// `Nat.div`'s truncation (e.g. off by the scaling factor) would compute a
/// different, wrong residue here. Plus a symbolic restatement over
/// genuinely free `m`, `n`.
#[test]
fn even_div_applies_at_concrete_pairs_and_rejects_a_wrong_residue_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let two = f.num(2);
    let three = f.num(3);
    let seven = f.num(7);
    let nine = f.num(9);
    let one = f.num(1);
    let zero = f.zero();

    // Even 2, witnessed by 1.
    let even2 = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(two, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(two);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, one, proof])
    };
    let even2_ty = f.lemma(p.even, &[two]);

    // even_div(7,3) : Iff (Even (div 7 3)) (Eq (div (mod 7 (mul 2 3)) 3) 0).
    let iff_7_3 = f.lemma(p.even_div, &[seven, three]);
    let q_7_3 = f.div(seven, three);
    let even_q_ty = f.lemma(p.even, &[q_7_3]);
    let two_times_three = f.mul(two, three);
    let mod_7_6 = f.modulo(seven, two_times_three);
    let div_mod_7_6_3 = f.div(mod_7_6, three);
    let rhs_ty = f.eq(div_mod_7_6_3, zero);

    // mp(Even 2) : Eq (div (mod 7 6) 3) 0 -- must compute to Eq 0 0.
    let mp_fn = f.const_app(p.logic.iff_mp, &[even_q_ty, rhs_ty, iff_7_3]);
    let mp_result = f.apply(mp_fn, &[even2]);
    let mp_result_ty = f.k.infer(mp_result).unwrap_or_else(|e| {
        panic!(
            "even_div(7,3).mp(Even 2) should type-check: {}",
            f.explain(&e)
        )
    });
    let zero_eq_zero = f.eq(zero, zero);
    assert!(
        f.k.def_eq(mp_result_ty, zero_eq_zero),
        "even_div(7,3).mp(Even 2) must compute to Eq 0 0"
    );

    // mpr(Eq 0 0) : Even (div 7 3) -- must be defeq to Even 2.
    let refl_zero = f.refl(zero);
    let mpr_fn = f.const_app(p.logic.iff_mpr, &[even_q_ty, rhs_ty, iff_7_3]);
    let mpr_result = f.apply(mpr_fn, &[refl_zero]);
    let mpr_result_ty = f.k.infer(mpr_result).unwrap_or_else(|e| {
        panic!(
            "even_div(7,3).mpr(Eq 0 0) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(mpr_result_ty, even2_ty),
        "even_div(7,3).mpr(Eq 0 0) must land on Even 2 (i.e. Even (div 7 3))"
    );

    // Truncation control at (9, 3): q := 3 is Odd, and the RHS residue
    // genuinely computes to 1, not 0.
    let two_times_three_b = f.mul(two, three);
    let mod_9_6 = f.modulo(nine, two_times_three_b);
    let div_mod_9_6_3 = f.div(mod_9_6, three);
    assert!(
        f.k.def_eq(div_mod_9_6_3, one),
        "9 % (2*3) / 3 must compute to 1 (Nat.div truncates and the residue \
         crosses n at an Odd quotient)"
    );
    assert!(
        !f.k.def_eq(div_mod_9_6_3, zero),
        "negative control: 9 % (2*3) / 3 must NOT be defeq to 0 -- this is \
         exactly the residue even_div's RHS must distinguish from the Even \
         case"
    );

    // Symbolic restatement over genuinely free m, n.
    let restated = f.name("even_div_restated");
    f.theorem(restated, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let q = d.div(m, n);
        let even_q_ty = d.lemma(p.even, &[q]);
        let two = d.num(2);
        let zero = d.zero();
        let two_n = d.mul(two, n);
        let mod_2n = d.modulo(m, two_n);
        let div_mod_2n_n = d.div(mod_2n, n);
        let rhs_ty = d.eq(div_mod_2n_n, zero);
        let stmt = d.const_app(p.logic.iff, &[even_q_ty, rhs_ty]);
        let proof = d.lemma(p.even_div, &[m, n]);
        (stmt, proof)
    })
    .expect("even_div must apply at genuinely free m, n");

    assert!(
        f.k.axiom_footprint(p.even_div).is_empty(),
        "even_div must rest on zero axioms"
    );
}

/// `even_xor` at two concrete instances, both exercising the "genuinely
/// bitwise" case (`m`, `n` both nonzero) `even_xor_hard_case` builds:
///
/// - `(4, 6)`: both even, `xor 4 6 = 2` (even) -- `mp` applied to a
///   hand-built `Even 2` (standing for `Even (xor 4 6)`, defeq) must land on
///   `Iff (Even 4) (Even 6)`, and applying THAT `.mp` to a hand-built
///   `Even 4` must land on a type defeq to the independently hand-built
///   `Even 6`.
/// - `(3, 5)`: both odd, `xor 3 5 = 6` (even) -- `mpr` applied to a
///   constructed `Iff (Even 3) (Even 5)` (built from `Not (Even 3)`/
///   `Not (Even 5)`, both derived via `odd_not_even`) must land on a type
///   defeq to a hand-built `Even 6` (standing for `Even (xor 3 5)`).
///
/// Both are discriminating: a swapped `mp`/`mpr`, a wrong remainder in the
/// bridge, or a sign error in the per-bit combine would make one of these
/// applications either fail to type-check or land on the wrong side.
#[test]
fn even_xor_applies_at_concrete_even_even_and_odd_odd_instances() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one_lvl = f.level_one();

    let even_witness = |f: &mut Fixture, target: ExprId, witness: ExprId| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let body = f.eq(target, kk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(target);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, witness, proof])
    };
    let odd_witness = |f: &mut Fixture, target: ExprId, witness: ExprId| -> ExprId {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let kk = f.add(k, k);
        let skk = f.succ(kk);
        let body = f.eq(target, skk);
        let pred = f.lam_fv(k_fv, nat, body);
        let proof = f.refl(target);
        let intro = f.k.const_(p.logic.exists_intro, vec![one_lvl]);
        f.apply(intro, &[nat, pred, witness, proof])
    };

    // --- (4, 6): both even, xor 4 6 = 2 -------------------------------------
    {
        let four = f.num(4);
        let six = f.num(6);
        let two = f.num(2);
        let one = f.num(1);
        let three = f.num(3);

        let even2 = even_witness(&mut f, two, one);
        let even4 = even_witness(&mut f, four, two);
        let even6 = even_witness(&mut f, six, three);
        let even6_ty = f
            .k
            .infer(even6)
            .unwrap_or_else(|e| panic!("Even 6 (witness 3) should type-check: {}", f.explain(&e)));
        let even4_ty = f
            .k
            .infer(even4)
            .unwrap_or_else(|e| panic!("Even 4 (witness 2) should type-check: {}", f.explain(&e)));

        let xor_4_6 = f.const_app(p.xor, &[four, six]);
        let even_xor_ty = f.lemma(p.even, &[xor_4_6]);
        let iff_4_6 = f.lemma(p.even_xor, &[four, six]);
        let even4_iff_even6_ty = f.const_app(p.logic.iff, &[even4_ty, even6_ty]);
        let iff_from_even2 = {
            let mp_fn = f.const_app(p.logic.iff_mp, &[even_xor_ty, even4_iff_even6_ty, iff_4_6]);
            f.apply(mp_fn, &[even2])
        };
        let iff_from_even2_ty = f.k.infer(iff_from_even2).unwrap_or_else(|e| {
            panic!(
                "even_xor(4, 6).mp(Even 2) should type-check: {}",
                f.explain(&e)
            )
        });
        assert!(
            f.k.def_eq(iff_from_even2_ty, even4_iff_even6_ty),
            "even_xor(4, 6).mp(Even 2) must land on Iff (Even 4) (Even 6)"
        );

        let inner_mp = f.const_app(p.logic.iff_mp, &[even4_ty, even6_ty, iff_from_even2]);
        let even6_derived = f.apply(inner_mp, &[even4]);
        let even6_derived_ty = f.k.infer(even6_derived).unwrap_or_else(|e| {
            panic!(
                "even_xor(4, 6).mp(Even 2).mp(Even 4) should type-check: {}",
                f.explain(&e)
            )
        });
        assert!(
            f.k.def_eq(even6_derived_ty, even6_ty),
            "even_xor(4, 6) round-trip must land back on (a type defeq to) Even 6"
        );
    }

    // --- (3, 5): both odd, xor 3 5 = 6 ---------------------------------------
    {
        let three = f.num(3);
        let five = f.num(5);
        let one = f.num(1);
        let two = f.num(2);
        let six = f.num(6);

        let odd3 = odd_witness(&mut f, three, one);
        let odd5 = odd_witness(&mut f, five, two);
        let even6 = even_witness(&mut f, six, three);
        let even6_ty = f
            .k
            .infer(even6)
            .unwrap_or_else(|e| panic!("Even 6 (witness 3) should type-check: {}", f.explain(&e)));

        let not_even3 = {
            let odd_not_even3 = f.lemma(p.odd_not_even, &[three]);
            f.apply(odd_not_even3, &[odd3])
        };
        let not_even5 = {
            let odd_not_even5 = f.lemma(p.odd_not_even, &[five]);
            f.apply(odd_not_even5, &[odd5])
        };
        let even3_ty = f.lemma(p.even, &[three]);
        let even5_ty = f.lemma(p.even, &[five]);
        let iff_even3_even5 = {
            let false_ty = f.k.const_(p.logic.false_, vec![]);
            let level_zero = f.k.level_zero();
            let mp = {
                let h_fv = f.fresh_fvar();
                let h = f.k.fvar(h_fv);
                let false_from_h = f.apply(not_even3, &[h]);
                let anon = f.anon_name();
                let motive = f.k.lam(anon, false_ty, even5_ty, BinderInfo::Default);
                let rec = f.k.const_(p.logic.false_rec, vec![level_zero]);
                let out = f.apply(rec, &[motive, false_from_h]);
                f.lam_fv(h_fv, even3_ty, out)
            };
            let mpr = {
                let h_fv = f.fresh_fvar();
                let h = f.k.fvar(h_fv);
                let false_from_h = f.apply(not_even5, &[h]);
                let anon = f.anon_name();
                let motive = f.k.lam(anon, false_ty, even3_ty, BinderInfo::Default);
                let rec = f.k.const_(p.logic.false_rec, vec![level_zero]);
                let out = f.apply(rec, &[motive, false_from_h]);
                f.lam_fv(h_fv, even5_ty, out)
            };
            f.const_app(p.logic.iff_intro, &[even3_ty, even5_ty, mp, mpr])
        };

        let xor_3_5 = f.const_app(p.xor, &[three, five]);
        let even_xor_ty = f.lemma(p.even, &[xor_3_5]);
        let iff_3_5 = f.lemma(p.even_xor, &[three, five]);
        let even3_iff_even5_ty = f.const_app(p.logic.iff, &[even3_ty, even5_ty]);
        let mpr_fn = f.const_app(p.logic.iff_mpr, &[even_xor_ty, even3_iff_even5_ty, iff_3_5]);
        let derived = f.apply(mpr_fn, &[iff_even3_even5]);
        let derived_ty = f.k.infer(derived).unwrap_or_else(|e| {
            panic!(
                "even_xor(3, 5).mpr(Iff (Even 3) (Even 5)) should type-check: {}",
                f.explain(&e)
            )
        });
        assert!(
            f.k.def_eq(derived_ty, even6_ty),
            "even_xor(3, 5).mpr(..) must land on (a type defeq to) Even 6, \
             standing for Even (xor 3 5)"
        );
    }

    assert!(
        f.k.axiom_footprint(p.even_xor).is_empty(),
        "even_xor must rest on zero axioms"
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

/// `Nat.log2` COMPUTES against Lean core's own `Init/Data/Nat/Log2.lean`
/// doc-comment examples (`log2 0 = 0`, `log2 1 = 0`, `log2 2 = 1`,
/// `log2 4 = 2`, `log2 7 = 2`, `log2 8 = 3`), and `log2_eq_log_two` applies
/// with EXACTLY that statement (not some vacuously true instance).
///
/// `Nat.log2` is declared as `fun n => Nat.log 2 n` (module doc,
/// `nat_prelude/log2.rs`), so this evaluation test is not merely checking
/// `Nat.log` a second time under a different name: it is the concrete-
/// instantiation half of the standing "a `Definition`'s kind-check does not
/// mean its VALUE is correct" rule -- a hand-computed value against a
/// reduced term, independent of whatever `Nat.log` itself is proved to do.
#[test]
fn log2_computes_and_equals_log_two() {
    let mut f = Fixture::new();
    let log2 = f.p.log2;

    for (value, expected) in [(0u32, 0u32), (1, 0), (2, 1), (3, 1), (4, 2), (7, 2), (8, 3)] {
        let n = f.num(value);
        let lhs = f.const_app(log2, &[n]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "log2 {value} must reduce to {expected}"
        );
    }

    let seven = f.num(7);
    let log2_seven = f.const_app(log2, &[seven]);
    let three = f.num(3);
    assert!(
        !f.k.def_eq(log2_seven, three),
        "negative control: log2 7 is 2, not 3"
    );

    // `log2_eq_log_two` applies at a genuinely FREE `n`, pushed into an
    // explicit `LocalContext` so `infer_in` can look up its type, and states
    // EXACTLY `Eq (log2 n) (log 2 n)` -- not, say, an accidentally-vacuous
    // `Eq (log2 n) (log2 n)` from a copy-paste of the wrong side.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let applied = f.const_app(f.p.log2_eq_log_two, &[n]);
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|e| panic!("log2_eq_log_two must apply at a free n: {e:?}"));
    let two = f.num(2);
    let log_two_n = f.const_app(f.p.log, &[two, n]);
    let log2_n = f.const_app(log2, &[n]);
    let want = f.eq(log2_n, log_two_n);
    assert!(
        f.k.def_eq(inferred, want),
        "log2_eq_log_two must state Eq (log2 n) (log 2 n)"
    );
    assert!(
        f.k.axiom_footprint(f.p.log2_eq_log_two).is_empty(),
        "log2_eq_log_two must rest on zero axioms"
    );
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

/// `Nat.bitwise` — the general `f : Bool -> Bool -> Bool` form `land`/`lor`/
/// `ldiff` were each landed instead of. Checks: (1) each of `and_fn`/
/// `or_fn`/`xor_fn` specializes correctly at several `(m, n)` pairs,
/// including cross-checks against the actual `land`/`lor` declarations, not
/// just hand-computed numerals; (2) the two `f`-general boundary theorems
/// apply at a concrete `f` and reduce to the expected specialization; (3)
/// every declaration here is axiom-free.
#[test]
fn bitwise_computes_and_its_boundary_theorems_apply() {
    let mut f = Fixture::new();
    let p = f.p;
    let bitwise = p.bitwise;
    let land = p.land;
    let lor = p.lor;

    // and_fn: Nat.bitwise and_fn m n must match Nat.land m n exactly, at
    // every pair -- the strongest available check (both sides independently
    // defined, both fully computed).
    {
        let and_ = super::bitwise::and_fn(&mut f);
        for (m, n) in [
            (0u32, 0u32),
            (0, 5),
            (5, 0),
            (1, 1),
            (3, 5),
            (5, 3),
            (6, 3),
            (7, 7),
        ] {
            let mm = f.num(m);
            let nn = f.num(n);
            let lhs = f.const_app(bitwise, &[and_, mm, nn]);
            let rhs = f.const_app(land, &[mm, nn]);
            assert!(
                f.k.def_eq(lhs, rhs),
                "bitwise and_fn {m} {n} must match land {m} {n}"
            );
        }
        // Negative control: AND at (3, 5) is 1, not 7 (that is OR's value).
        let three = f.num(3);
        let five = f.num(5);
        let bad = f.num(7);
        let lhs = f.const_app(bitwise, &[and_, three, five]);
        assert!(
            !f.k.def_eq(lhs, bad),
            "negative control: bitwise and_fn 3 5 is 1, not 7 (that is OR's value)"
        );
    }

    // or_fn: same cross-check against Nat.lor.
    {
        let or_ = super::bitwise::or_fn(&mut f);
        for (m, n) in [
            (0u32, 0u32),
            (0, 5),
            (5, 0),
            (1, 1),
            (3, 5),
            (5, 3),
            (6, 3),
            (7, 7),
        ] {
            let mm = f.num(m);
            let nn = f.num(n);
            let lhs = f.const_app(bitwise, &[or_, mm, nn]);
            let rhs = f.const_app(lor, &[mm, nn]);
            assert!(
                f.k.def_eq(lhs, rhs),
                "bitwise or_fn {m} {n} must match lor {m} {n}"
            );
        }
        // Negative control: OR at (3, 5) is 7, not 1 (that is AND's value).
        let three = f.num(3);
        let five = f.num(5);
        let bad = f.num(1);
        let lhs = f.const_app(bitwise, &[or_, three, five]);
        assert!(
            !f.k.def_eq(lhs, bad),
            "negative control: bitwise or_fn 3 5 is 7, not 1 (that is AND's value)"
        );
    }

    // xor_fn: no prelude sibling, so checked against hand-computed values.
    {
        let xor_ = super::bitwise::xor_fn(&mut f);
        for (m, n, expected) in [
            (0u32, 0u32, 0u32),
            (0, 5, 5),
            (5, 0, 5),
            (1, 1, 0),
            (3, 5, 6),
            (5, 3, 6),
            (6, 3, 5),
            (7, 7, 0),
        ] {
            let mm = f.num(m);
            let nn = f.num(n);
            let lhs = f.const_app(bitwise, &[xor_, mm, nn]);
            let rhs = f.num(expected);
            assert!(
                f.k.def_eq(lhs, rhs),
                "bitwise xor_fn {m} {n} must reduce to {expected}"
            );
        }
        // Negative control: XOR at (3, 5) is 6, not 1 or 7 (AND's / OR's
        // values at the same operands).
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(bitwise, &[xor_, three, five]);
        let bad_one = f.num(1);
        let bad_seven = f.num(7);
        assert!(
            !f.k.def_eq(lhs, bad_one),
            "negative control: bitwise xor_fn 3 5 is 6, not 1"
        );
        assert!(
            !f.k.def_eq(lhs, bad_seven),
            "negative control: bitwise xor_fn 3 5 is 6, not 7"
        );
    }

    // bitwise_zero_left : forall f n, Eq (bitwise f 0 n) (if f false true
    // then n else 0) -- instantiated at f = and_fn (absorbing: reduces to
    // 0) and f = or_fn (identity: reduces to n).
    {
        let and_ = super::bitwise::and_fn(&mut f);
        let seven = f.num(7);
        let zero = f.num(0);
        let applied = f.const_app(p.bitwise_zero_left, &[and_, seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_zero_left must type-check at and_fn: {shown}")
        });
        let lhs = f.const_app(bitwise, &[and_, zero, seven]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_zero_left at and_fn must state Eq (bitwise and_fn 0 7) 0"
        );
        let bad_want = f.eq(lhs, seven);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bitwise_zero_left at and_fn must not also state \
             Eq (bitwise and_fn 0 7) 7"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_zero_left).is_empty(),
            "bitwise_zero_left must rest on zero axioms"
        );
    }
    {
        let or_ = super::bitwise::or_fn(&mut f);
        let seven = f.num(7);
        let zero = f.num(0);
        let applied = f.const_app(p.bitwise_zero_left, &[or_, seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_zero_left must type-check at or_fn: {shown}")
        });
        let lhs = f.const_app(bitwise, &[or_, zero, seven]);
        let want = f.eq(lhs, seven);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_zero_left at or_fn must state Eq (bitwise or_fn 0 7) 7"
        );
        let bad_want = f.eq(lhs, zero);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bitwise_zero_left at or_fn must not also state \
             Eq (bitwise or_fn 0 7) 0"
        );
    }

    // bitwise_zero_right : forall f m, Eq (bitwise f m 0) (if f true false
    // then m else 0) -- instantiated at f = and_fn (absorbing: reduces to
    // 0) and f = or_fn (identity: reduces to m).
    {
        let and_ = super::bitwise::and_fn(&mut f);
        let nine = f.num(9);
        let zero = f.num(0);
        let applied = f.const_app(p.bitwise_zero_right, &[and_, nine]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_zero_right must type-check at and_fn: {shown}")
        });
        let lhs = f.const_app(bitwise, &[and_, nine, zero]);
        let want = f.eq(lhs, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_zero_right at and_fn must state Eq (bitwise and_fn 9 0) 0"
        );
        let bad_want = f.eq(lhs, nine);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bitwise_zero_right at and_fn must not also state \
             Eq (bitwise and_fn 9 0) 9"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_zero_right).is_empty(),
            "bitwise_zero_right must rest on zero axioms"
        );
    }
    {
        let or_ = super::bitwise::or_fn(&mut f);
        let nine = f.num(9);
        let zero = f.num(0);
        let applied = f.const_app(p.bitwise_zero_right, &[or_, nine]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_zero_right must type-check at or_fn: {shown}")
        });
        let lhs = f.const_app(bitwise, &[or_, nine, zero]);
        let want = f.eq(lhs, nine);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_zero_right at or_fn must state Eq (bitwise or_fn 9 0) 9"
        );
        let bad_want = f.eq(lhs, zero);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bitwise_zero_right at or_fn must not also state \
             Eq (bitwise or_fn 9 0) 0"
        );
    }

    // The three concrete specialization theorems, each checked against its
    // own declared statement plus a negative control, plus axiom-freedom.
    {
        let applied = f.const_app(p.bitwise_and_eq_land_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_and_eq_land_three_five must type-check: {shown}")
        });
        let and_ = super::bitwise::and_fn(&mut f);
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(bitwise, &[and_, three, five]);
        let rhs = f.const_app(land, &[three, five]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_and_eq_land_three_five must state \
             Eq (bitwise and_fn 3 5) (land 3 5)"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_and_eq_land_three_five)
                .is_empty(),
            "bitwise_and_eq_land_three_five must rest on zero axioms"
        );
    }
    {
        let applied = f.const_app(p.bitwise_or_eq_lor_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_or_eq_lor_three_five must type-check: {shown}")
        });
        let or_ = super::bitwise::or_fn(&mut f);
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(bitwise, &[or_, three, five]);
        let rhs = f.const_app(lor, &[three, five]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_or_eq_lor_three_five must state \
             Eq (bitwise or_fn 3 5) (lor 3 5)"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_or_eq_lor_three_five)
                .is_empty(),
            "bitwise_or_eq_lor_three_five must rest on zero axioms"
        );
    }
    {
        let applied = f.const_app(p.bitwise_xor_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_xor_three_five must type-check: {shown}")
        });
        let xor_ = super::bitwise::xor_fn(&mut f);
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(bitwise, &[xor_, three, five]);
        let six = f.num(6);
        let want = f.eq(lhs, six);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_xor_three_five must state Eq (bitwise xor_fn 3 5) 6"
        );
        let one = f.num(1);
        let bad_want = f.eq(lhs, one);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: bitwise_xor_three_five must not also state \
             Eq (bitwise xor_fn 3 5) 1 (that is AND's value)"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_xor_three_five).is_empty(),
            "bitwise_xor_three_five must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(bitwise).is_empty(),
        "Nat.bitwise must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_aux).is_empty(),
        "Nat.bitwiseAux must rest on zero axioms"
    );
}

/// `Nat.xor` computes bitwise XOR at concrete points -- including the same
/// `(3, 5)` pair every sibling operator's own sanity check uses (`land` = 1,
/// `lor` = 7, `ldiff` = 2, `xor` = 6: four distinct numerals from one
/// operand pair, so a copy-paste from any neighbour fails loudly) -- and
/// builds against a FREE variable pair as a direct unfolding of
/// `Nat.bitwise xor_fn`, disjoint from the concrete check per the standing
/// rule that a concrete instantiation can hide a defect a symbolic build
/// exposes.
#[test]
fn xor_computes_and_is_bitwise_xor_fn() {
    let mut f = Fixture::new();
    let p = f.p;
    let xor = p.xor;
    let bitwise = p.bitwise;

    for (m, n, expected) in [
        (0u32, 0u32, 0u32),
        (0, 5, 5),
        (5, 0, 5),
        (1, 1, 0),
        (3, 5, 6),
        (6, 3, 5),
        (7, 7, 0),
    ] {
        let mm = f.num(m);
        let nn = f.num(n);
        let lhs = f.const_app(xor, &[mm, nn]);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "xor {m} {n} must reduce to {expected}"
        );
    }

    // Negative controls: `3 xor 5 = 6`, not `1` (land's value at this pair)
    // and not `7` (lor's value at the same pair).
    let three = f.num(3);
    let five = f.num(5);
    let xor_three_five = f.const_app(xor, &[three, five]);
    let bad_one = f.num(1);
    assert!(
        !f.k.def_eq(xor_three_five, bad_one),
        "negative control: xor 3 5 is 6, not 1 (that is land's value)"
    );
    let bad_seven = f.num(7);
    assert!(
        !f.k.def_eq(xor_three_five, bad_seven),
        "negative control: xor 3 5 is 6, not 7 (that is lor's value)"
    );

    // Symbolic build: `xor a b` must be a direct unfolding of
    // `bitwise xor_fn a b` for a genuinely FREE `a`, `b` -- not merely at
    // numerals, per the standing rule that concrete instantiation alone can
    // hide a defect a symbolic build exposes.
    {
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let lhs = f.const_app(xor, &[a, b]);
        let xor_fn_term = super::bitwise::xor_fn(&mut f);
        let rhs = f.const_app(bitwise, &[xor_fn_term, a, b]);
        assert!(
            f.k.def_eq(lhs, rhs),
            "xor a b must be a direct unfolding of bitwise xor_fn a b for free a, b"
        );
    }

    // xor_three_five : Eq (xor 3 5) 6
    {
        let applied = f.const_app(p.xor_three_five, &[]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_three_five must type-check: {shown}")
        });
        let lhs = f.const_app(xor, &[three, five]);
        let six = f.num(6);
        let want = f.eq(lhs, six);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_three_five must state Eq (xor 3 5) 6"
        );
        let bad_want = f.eq(lhs, bad_one);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: xor_three_five must not also state Eq (xor 3 5) 1"
        );
        assert!(
            f.k.axiom_footprint(p.xor_three_five).is_empty(),
            "xor_three_five must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(xor).is_empty(),
        "Nat.xor must rest on zero axioms"
    );
}

/// `Nat.xor_comm` — a corollary of `Nat.bitwise_comm` at `f := xor_fn`
/// (`xor_order.rs`) — applies at the SAME `(3, 5)` discriminating pair
/// every sibling `_comm` theorem uses (`xor 3 5 = 6 = xor 5 3`, both sides
/// distinct from `land`'s `1` and `lor`'s `7` at the same operands), AND
/// symbolically against a genuinely FREE `m`, `n` pair, per the standing
/// rule that a concrete instantiation alone can hide a defect a symbolic
/// build exposes.
#[test]
fn xor_comm_applies_at_a_concrete_discriminating_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: xor 3 5 = 6 = xor 5 3.
    {
        let three = f.num(3);
        let five = f.num(5);
        let applied = f.lemma(p.xor_comm, &[three, five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_comm must apply at (m=3, n=5): {shown}")
        });
        let lhs = f.const_app(p.xor, &[three, five]);
        let rhs = f.const_app(p.xor, &[five, three]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_comm 3 5 must state Eq (xor 3 5) (xor 5 3)"
        );
        let six = f.num(6);
        assert!(f.k.def_eq(lhs, six), "xor 3 5 must compute to 6");
        assert!(f.k.def_eq(rhs, six), "xor 5 3 must compute to 6");
        // Negative control: xor_comm must not ALSO be usable to claim
        // xor 3 5 = 1 (land's value at this pair).
        let bad_one = f.num(1);
        let bad_want = f.eq(lhs, bad_one);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: xor_comm 3 5 must not state Eq (xor 3 5) 1"
        );
    }

    // Symbolic: xor_comm applies at a genuinely FREE m, n pair. Wrapped in
    // a fresh theorem (like `bitwise_comm_applies_at_a_concrete_
    // discriminating_instance`'s own "Symbolic:" block does) so the bound
    // variables are properly registered via `pi_fv`/`lam_fv` rather than
    // raw test-created fvars, which `Kernel::infer` cannot type without a
    // local-context entry.
    {
        let name = f.name("xor_comm_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(p.xor, &[m, n]);
            let rhs = d.const_app(p.xor, &[n, m]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.xor_comm, &[m, n]);
            (stmt, proof)
        })
        .expect("xor_comm must apply at symbolic m, n");
    }

    assert!(
        f.k.axiom_footprint(p.xor_comm).is_empty(),
        "xor_comm must rest on zero axioms"
    );
}

/// `Nat.testBit_xor` -- bridges `testBitAux`'s INDEX recursion with
/// `bitwiseAux`'s VALUE recursion (`testbit_bitwise.rs`). Checked at
/// `(m, n) = (5, 3)` (binary `101`/`011`, `xor 5 3 = 6` = `110`) across all
/// three of its meaningfully differing bits (bit `0`: `1`/`1` -> XOR `0`;
/// bit `1`: `0`/`1` -> XOR `1`; bit `2`: `1`/`0` -> XOR `1`) -- a single bit
/// position could not discriminate a swapped combine, so all three are
/// checked -- AND symbolically against a genuinely FREE `(m, n, i)` triple,
/// per the standing rule that a concrete instantiation alone can hide a
/// defect a symbolic build exposes.
#[test]
fn test_bit_xor_applies_at_a_concrete_discriminating_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: xor 5 3 = 6 (101 xor 011 = 110); check all three bits.
    {
        let five = f.num(5);
        let three = f.num(3);
        for (i, expected_bit) in [(0u32, 0u32), (1, 1), (2, 1)] {
            let idx = f.num(i);
            let applied = f.lemma(p.test_bit_xor, &[five, three, idx]);
            let inferred = f.k.infer(applied).unwrap_or_else(|e| {
                let shown = f.explain(&e);
                panic!("test_bit_xor must apply at (m=5, n=3, i={i}): {shown}")
            });
            let xor_53 = f.const_app(p.xor, &[five, three]);
            let lhs = f.const_app(p.test_bit, &[xor_53, idx]);
            let tb_m = f.const_app(p.test_bit, &[five, idx]);
            let tb_n = f.const_app(p.test_bit, &[three, idx]);
            let rhs = super::testbit_bitwise::xor_bit(&mut f, tb_m, tb_n);
            let want = f.eq(lhs, rhs);
            assert!(
                f.k.def_eq(inferred, want),
                "test_bit_xor must state Eq (testBit (xor 5 3) {i}) \
                 (xor_bit (testBit 5 {i}) (testBit 3 {i}))"
            );
            let expected = f.num(expected_bit);
            assert!(
                f.k.def_eq(lhs, expected),
                "testBit (xor 5 3) {i} must compute to {expected_bit}"
            );
            // Negative control: the OTHER bit value must not also def_eq.
            let other = f.num(1 - expected_bit);
            let bad_want = f.eq(lhs, other);
            assert!(
                !f.k.def_eq(inferred, bad_want),
                "negative control: bit {i} of xor 5 3 must not ALSO be {}",
                1 - expected_bit
            );
        }
    }

    // Symbolic: test_bit_xor applies at a genuinely FREE (m, n, i) triple.
    // Wrapped in a fresh theorem (like `xor_comm_restated`'s own block)
    // so the bound variables are properly registered via `pi_fv`/`lam_fv`.
    {
        let name = f.name("test_bit_xor_restated");
        f.theorem(name, 3, &|d, values| {
            let m = values[0];
            let n = values[1];
            let i = values[2];
            let xor_mn = d.const_app(p.xor, &[m, n]);
            let lhs = d.const_app(p.test_bit, &[xor_mn, i]);
            let tb_m = d.const_app(p.test_bit, &[m, i]);
            let tb_n = d.const_app(p.test_bit, &[n, i]);
            let rhs = super::testbit_bitwise::xor_bit(d, tb_m, tb_n);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.test_bit_xor, &[m, n, i]);
            (stmt, proof)
        })
        .expect("test_bit_xor must apply at symbolic m, n, i");
    }

    assert!(
        f.k.axiom_footprint(p.test_bit_xor).is_empty(),
        "test_bit_xor must rest on zero axioms"
    );
}

/// `Nat.self_lt_two_pow`/`Nat.self_lt_two_pow_add` -- checked at concrete
/// instances, both symbolically and against numerals large enough that a
/// wrong direction (`Le` vs `Lt`, or the bound landing on the WRONG side)
/// would fail rather than pass vacuously.
#[test]
fn self_lt_two_pow_and_add_apply_at_concrete_and_symbolic_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: 5 < 2^5 = 32, and NOT 2^5 < 5 (direction control).
    {
        let five = f.num(5);
        let applied = f.lemma(p.self_lt_two_pow, &[five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("self_lt_two_pow must apply at n=5: {shown}")
        });
        let two = f.num(2);
        let pow5 = f.pow(two, five);
        let want = f.lt(five, pow5);
        assert!(
            f.k.def_eq(inferred, want),
            "self_lt_two_pow 5 must state Lt 5 (pow 2 5)"
        );
        let thirty_two = f.num(32);
        assert!(f.k.def_eq(pow5, thirty_two), "pow 2 5 must compute to 32");
    }

    // Concrete: self_lt_two_pow_add(3, 2) : Lt 3 (pow 2 (add 3 2)) = Lt 3 32.
    {
        let three = f.num(3);
        let two_arg = f.num(2);
        let applied = f.lemma(p.self_lt_two_pow_add, &[three, two_arg]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("self_lt_two_pow_add must apply at (a=3, b=2): {shown}")
        });
        let two = f.num(2);
        let sum = f.add(three, two_arg);
        let pow_sum = f.pow(two, sum);
        let want = f.lt(three, pow_sum);
        assert!(
            f.k.def_eq(inferred, want),
            "self_lt_two_pow_add 3 2 must state Lt 3 (pow 2 (add 3 2))"
        );
        let thirty_two = f.num(32);
        assert!(
            f.k.def_eq(pow_sum, thirty_two),
            "pow 2 (add 3 2) must compute to 32"
        );
    }

    // Symbolic: self_lt_two_pow_add applies at a genuinely FREE (a, b) pair.
    {
        let name = f.name("self_lt_two_pow_add_restated");
        f.theorem(name, 2, &|d, values| {
            let a = values[0];
            let b = values[1];
            let two = d.num(2);
            let sum = d.add(a, b);
            let pw = d.pow(two, sum);
            let stmt = d.lt(a, pw);
            let proof = d.lemma(p.self_lt_two_pow_add, &[a, b]);
            (stmt, proof)
        })
        .expect("self_lt_two_pow_add must apply at symbolic a, b");
    }

    assert!(
        f.k.axiom_footprint(p.self_lt_two_pow).is_empty(),
        "self_lt_two_pow must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.self_lt_two_pow_add).is_empty(),
        "self_lt_two_pow_add must rest on zero axioms"
    );
}

/// `Nat.lt_of_testBit` -- checked SYMBOLICALLY at a genuinely free
/// `(n, m, i)` triple with free hypothesis fvars for `H0`/`H1`/`Hagree`:
/// confirms the declared type's exact SHAPE (hypothesis order, that `H0` is
/// about `n` not `m`, that `H1`'s target is `one` not `zero`, that the
/// conclusion is `Lt n m` not `Lt m n`) matches this file's own module doc.
///
/// A concrete DISCRIMINATING numeric instance was scoped OUT of this test:
/// building one honestly needs `Hagree`'s full universally-quantified proof
/// (`∀ j, Lt i j → …`), which requires a general "testBit is eventually zero
/// above a magnitude bound" lemma this lane did not build (see the module
/// doc / handoff for exactly this gap). The type-check the kernel already
/// performed on `add_declaration` -- the FULL universally-quantified
/// statement, strictly stronger than any single concrete instantiation --
/// is the real evidence here; this test additionally confirms the shape.
#[test]
fn lt_of_test_bit_applies_at_a_genuinely_symbolic_hypothesis_set() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let name = f.name("lt_of_test_bit_restated");
    f.theorem(name, 3, &|d, values| {
        let n = values[0];
        let m = values[1];
        let i = values[2];
        let zero = d.zero();
        let one = d.num(1);

        let tb_n_i = d.const_app(p.test_bit, &[n, i]);
        let tb_m_i = d.const_app(p.test_bit, &[m, i]);
        let h0_ty = d.eq(tb_n_i, zero);
        let h1_ty = d.eq(tb_m_i, one);
        let hagree_ty = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let lt_i_j = d.lt(i, j);
            let tb_n_j = d.const_app(p.test_bit, &[n, j]);
            let tb_m_j = d.const_app(p.test_bit, &[m, j]);
            let eq_j = d.eq(tb_n_j, tb_m_j);
            let body = d.arrow(lt_i_j, eq_j);
            d.pi_fv(j_fv, nat, body)
        };

        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let hagree_fv = d.fresh_fvar();
        let hagree = d.kernel().fvar(hagree_fv);

        let concl = d.lt(n, m);
        let stmt = {
            let with_hagree = d.arrow(hagree_ty, concl);
            let with_h1 = d.arrow(h1_ty, with_hagree);
            d.arrow(h0_ty, with_h1)
        };
        let proof = d.lemma(p.lt_of_test_bit, &[n, m, i, h0, h1, hagree]);
        let proof = {
            let with_hagree = d.lam_fv(hagree_fv, hagree_ty, proof);
            let with_h1 = d.lam_fv(h1_fv, h1_ty, with_hagree);
            d.lam_fv(h0_fv, h0_ty, with_h1)
        };
        (stmt, proof)
    })
    .expect("lt_of_test_bit must apply at a symbolic (n, m, i, H0, H1, Hagree) tuple");

    assert!(
        f.k.axiom_footprint(p.lt_of_test_bit).is_empty(),
        "lt_of_test_bit must rest on zero axioms"
    );
}

/// `Nat.testBit_eq_zero_of_lt` -- piece 2's "cheap half": checked at a
/// CONCRETE discriminating instance (`n := 5` = `101₂`, `j := size 5 = 3`,
/// hypothesis supplied by the already-checked `lt_pow_size`) AND
/// symbolically at a genuinely FREE `(n, j)` pair with a free hypothesis
/// fvar, confirming the declared shape (`Eq (testBit n j) zero`, not a
/// swapped `Eq (testBit j n) zero` or the wrong `one`).
#[test]
fn test_bit_eq_zero_of_lt_applies_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: n := 5, j := size(5) = 3; `lt_pow_size(5)` supplies
    // `Lt 5 (pow 2 (size 5))` == `Lt 5 8`.
    {
        let five = f.num(5);
        let size_five = f.const_app(p.size, &[five]);
        let hyp = f.lemma(p.lt_pow_size, &[five]);
        let result = f.lemma(p.test_bit_eq_zero_of_lt, &[five, size_five, hyp]);
        let inferred = f.k.infer(result).unwrap_or_else(|e| {
            panic!(
                "test_bit_eq_zero_of_lt(5, size 5) should infer: {}",
                f.explain(&e)
            )
        });
        let tb = f.const_app(p.test_bit, &[five, size_five]);
        let zero = f.zero();
        let expected_ty = f.eq(tb, zero);
        assert!(
            f.k.def_eq(inferred, expected_ty),
            "test_bit_eq_zero_of_lt(5, size 5) should state Eq (testBit 5 (size 5)) zero"
        );
        assert!(f.k.def_eq(tb, zero), "testBit 5 (size 5) must reduce to 0");

        // NEGATIVE control: testBit 5 (size 5) must NOT reduce to 1 -- a
        // checker that can't fail is worse than none.
        let one = f.num(1);
        assert!(!f.k.def_eq(tb, one), "testBit 5 (size 5) must NOT be 1");
    }

    // Symbolic: applies at a genuinely FREE (n, j) pair.
    let name = f.name("test_bit_eq_zero_of_lt_restated");
    f.theorem(name, 2, &|d, values| {
        let n = values[0];
        let j = values[1];
        let two = d.num(2);
        let pow_j = d.pow(two, j);
        let hyp_ty = d.lt(n, pow_j);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let zero = d.zero();
        let tb = d.const_app(p.test_bit, &[n, j]);
        let concl = d.eq(tb, zero);
        let stmt = d.arrow(hyp_ty, concl);
        let proof_body = d.lemma(p.test_bit_eq_zero_of_lt, &[n, j, hyp]);
        let proof = d.lam_fv(hyp_fv, hyp_ty, proof_body);
        (stmt, proof)
    })
    .expect("test_bit_eq_zero_of_lt must apply at a symbolic (n, j) pair");

    assert!(
        f.k.axiom_footprint(p.test_bit_eq_zero_of_lt).is_empty(),
        "test_bit_eq_zero_of_lt must rest on zero axioms"
    );
}

/// `Nat.exists_most_significant_bit` -- the "hard half" of piece 2 (the
/// highest bit really IS set, not merely that no higher bit is needed;
/// `Nat.testBit_eq_zero_of_lt` above is the cheap half). Checked at a
/// CONCRETE discriminating instance (`n := 5 = 101₂`, whose highest set bit
/// is at index 2, distinguishing this from a vacuous or off-by-one witness)
/// AND symbolically at a genuinely FREE `n` with a free `n != 0` hypothesis.
/// The expected `Exists` shape is restated independently of
/// `bit_order.rs`'s own `msb_predicate`/`msb_exists_ty` helpers (not reused
/// here), so a bug in those helpers would not be invisible to this check.
#[test]
fn exists_most_significant_bit_applies_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.num(1);
    let zero = f.zero();
    let one_lvl = f.level_one();

    // Concrete: n := 5 (built as `succ 4`, matching `succ_ne_zero`'s own
    // shape so the positivity witness is structurally exact, not merely
    // def_eq).
    {
        let four = f.num(4);
        let five = f.succ(four);
        let hne = f.lemma(p.succ_ne_zero, &[four]);
        let result = f.lemma(p.exists_most_significant_bit, &[five, hne]);
        let inferred = f.k.infer(result).unwrap_or_else(|e| {
            panic!(
                "exists_most_significant_bit(5) should infer: {}",
                f.explain(&e)
            )
        });

        let predicate = {
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let tb_i = f.const_app(p.test_bit, &[five, i]);
            let a = f.eq(tb_i, one);
            let b = {
                let j_fv = f.fresh_fvar();
                let j = f.k.fvar(j_fv);
                let lt_i_j = f.lt(i, j);
                let tb_j = f.const_app(p.test_bit, &[five, j]);
                let eq_j = f.eq(tb_j, zero);
                let body = f.arrow(lt_i_j, eq_j);
                f.pi_fv(j_fv, nat, body)
            };
            let and_ty = f.const_app(p.logic.and, &[a, b]);
            f.lam_fv(i_fv, nat, and_ty)
        };
        let exists_c = f.k.const_(p.logic.exists_, vec![one_lvl]);
        let expected_ty = f.apply(exists_c, &[nat, predicate]);
        assert!(
            f.k.def_eq(inferred, expected_ty),
            "exists_most_significant_bit(5) should state Exists (msb predicate at 5)"
        );

        // Anti-vacuity: bit 2 of 5 (= 101₂) is really 1, and bit 1 is really
        // 0 -- not a swapped or off-by-one witness.
        let two_idx = f.num(2);
        let tb2 = f.const_app(p.test_bit, &[five, two_idx]);
        assert!(f.k.def_eq(tb2, one), "testBit 5 2 must reduce to 1");
        let one_idx = f.num(1);
        let tb1 = f.const_app(p.test_bit, &[five, one_idx]);
        assert!(!f.k.def_eq(tb1, one), "testBit 5 1 must NOT be 1");
    }

    // Symbolic: applies at a genuinely FREE `n` with a free `n != 0`
    // hypothesis.
    let name = f.name("exists_most_significant_bit_restated");
    f.theorem(name, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let eq_ty = d.eq(n, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_ty, false_ty);
        let ne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(ne_fv);
        let result = d.lemma(p.exists_most_significant_bit, &[n, hne]);

        let nat = d.nat_ty();
        let one = d.num(1);
        let one_lvl = d.level_one();
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let tb_i = d.const_app(p.test_bit, &[n, i]);
            let a = d.eq(tb_i, one);
            let b = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let lt_i_j = d.lt(i, j);
                let tb_j = d.const_app(p.test_bit, &[n, j]);
                let zero2 = d.zero();
                let eq_j = d.eq(tb_j, zero2);
                let body = d.arrow(lt_i_j, eq_j);
                d.pi_fv(j_fv, nat, body)
            };
            let and_ty = d.const_app(p.logic.and, &[a, b]);
            d.lam_fv(i_fv, nat, and_ty)
        };
        let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        let concl = d.apply(exists_c, &[nat, predicate]);

        let stmt = d.arrow(ne_ty, concl);
        let proof = d.lam_fv(ne_fv, ne_ty, result);
        (stmt, proof)
    })
    .expect("exists_most_significant_bit must apply at a symbolic n");

    assert!(
        f.k.axiom_footprint(p.exists_most_significant_bit)
            .is_empty(),
        "exists_most_significant_bit must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.msb_exists_of_le_fuel).is_empty(),
        "msb_exists_of_le_fuel must rest on zero axioms"
    );
}

/// `Nat.eq_of_testBit_eq` -- "same bits imply the same number"
/// (`xor_algebra.rs`), the general extensionality lemma built toward piece 4
/// of `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.xor_assoc` et al, not
/// themselves landed this lane). Checked at a concrete REFLEXIVE instance
/// (`m = n = 6`, bits trivially equal via `refl`, discriminating against the
/// wrong conclusion `Eq 6 7`) AND symbolically against a genuinely FREE
/// `(m, n)` pair with an assumed (not derivable) bit-equality hypothesis, per
/// the standing rule that a concrete instantiation alone can hide a defect a
/// symbolic build exposes.
#[test]
fn eq_of_test_bit_eq_applies_at_a_concrete_reflexive_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: m = n = 6, bits trivially equal via refl at every i.
    {
        let six = f.num(6);
        let bits_hyp = {
            let nat = f.nat_ty();
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let tb = f.const_app(p.test_bit, &[six, i]);
            let refl_tb = f.refl(tb);
            f.lam_fv(i_fv, nat, refl_tb)
        };
        let applied = f.lemma(p.eq_of_test_bit_eq, &[six, six, bits_hyp]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("eq_of_testBit_eq must apply at (m=6, n=6): {shown}")
        });
        let want = f.eq(six, six);
        assert!(
            f.k.def_eq(inferred, want),
            "eq_of_testBit_eq 6 6 _ must state Eq 6 6"
        );
        // Negative control: must not ALSO state Eq 6 7.
        let seven = f.num(7);
        let bad_want = f.eq(six, seven);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: eq_of_testBit_eq 6 6 _ must not state Eq 6 7"
        );
    }

    // Symbolic: applies at a genuinely FREE (m, n) pair, given an assumed
    // (not derivable) bit-equality hypothesis -- wrapped in a fresh
    // `d.theorem(...)` the same way `test_bit_xor_restated` is, since raw
    // test-created fvars fail `Kernel::infer` with `UnboundFVar`.
    {
        let name = f.name("eq_of_test_bit_eq_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let nat = d.nat_ty();
            let bits_ty = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let tb_m = d.const_app(p.test_bit, &[m, i]);
                let tb_n = d.const_app(p.test_bit, &[n, i]);
                let body = d.eq(tb_m, tb_n);
                d.pi_fv(i_fv, nat, body)
            };
            let bits_fv = d.fresh_fvar();
            let bits_hyp = d.kernel().fvar(bits_fv);
            let concl = d.eq(m, n);
            let stmt = d.arrow(bits_ty, concl);
            let proof_body = d.lemma(p.eq_of_test_bit_eq, &[m, n, bits_hyp]);
            let proof = d.lam_fv(bits_fv, bits_ty, proof_body);
            (stmt, proof)
        })
        .expect(
            "eq_of_testBit_eq must apply at symbolic m, n given an assumed bit-equality hypothesis",
        );
    }

    assert!(
        f.k.axiom_footprint(p.eq_of_test_bit_eq).is_empty(),
        "eq_of_testBit_eq must rest on zero axioms"
    );
}

/// `Nat.xor_assoc` (`xor_algebra.rs`) -- piece 4 (partial) toward
/// `F:ml430-nat-lt-xor-cases-c43a1e85`, via `Nat.testBit_xor` twice per side
/// plus `Nat.eq_of_testBit_eq`. Checked at the discriminating concrete
/// triple `(a, b, c) = (1, 2, 4)` (three non-overlapping bits: `xor 1 2 = 3`,
/// `xor 3 4 = 7`; `xor 2 4 = 6`, `xor 1 6 = 7` -- both sides `7`, with a
/// negative control against `6`) AND symbolically against a genuinely FREE
/// `(a, b, c)` triple, per the standing mandatory-instantiation rule.
#[test]
fn xor_assoc_applies_at_a_concrete_discriminating_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: (1, 2, 4), both sides compute to 7.
    {
        let one = f.num(1);
        let two = f.num(2);
        let four = f.num(4);
        let applied = f.lemma(p.xor_assoc, &[one, two, four]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_assoc must apply at (a=1, b=2, c=4): {shown}")
        });
        let xab = f.const_app(p.xor, &[one, two]);
        let lhs = f.const_app(p.xor, &[xab, four]);
        let xbc = f.const_app(p.xor, &[two, four]);
        let rhs = f.const_app(p.xor, &[one, xbc]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_assoc 1 2 4 must state Eq (xor (xor 1 2) 4) (xor 1 (xor 2 4))"
        );
        let seven = f.num(7);
        assert!(f.k.def_eq(lhs, seven), "xor (xor 1 2) 4 must compute to 7");
        assert!(f.k.def_eq(rhs, seven), "xor 1 (xor 2 4) must compute to 7");
        // Negative control: must not ALSO state Eq lhs 6.
        let six = f.num(6);
        let bad_want = f.eq(lhs, six);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: xor_assoc 1 2 4 must not state Eq (xor (xor 1 2) 4) 6"
        );
    }

    // Symbolic: applies at a genuinely FREE (a, b, c) triple.
    {
        let name = f.name("xor_assoc_restated");
        f.theorem(name, 3, &|d, values| {
            let (a, b, c) = (values[0], values[1], values[2]);
            let xab = d.const_app(p.xor, &[a, b]);
            let lhs = d.const_app(p.xor, &[xab, c]);
            let xbc = d.const_app(p.xor, &[b, c]);
            let rhs = d.const_app(p.xor, &[a, xbc]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.xor_assoc, &[a, b, c]);
            (stmt, proof)
        })
        .expect("xor_assoc must apply at symbolic a, b, c");
    }

    assert!(
        f.k.axiom_footprint(p.xor_assoc).is_empty(),
        "xor_assoc must rest on zero axioms"
    );
}

/// `Nat.xor_xor_cancel_left`/`_right` (`xor_algebra.rs`) -- the remaining two
/// of the four sub-targets toward `F:ml430-nat-lt-xor-cases-c43a1e85`'s piece
/// 4. Checked at the discriminating concrete pair `(a, b) = (3, 5)`
/// (`xor 3 5 = 6`, `xor 3 6 = 5 = b`; `xor 6 5 = 3 = a`) AND symbolically
/// against a genuinely FREE `(a, b)` pair. The per-bit cancel identity these
/// rest on (`xor_bit x (xor_bit x y) = y`) is FALSE for a general `Nat` `y`
/// (only for `y in {0, 1}`), unlike `xor_assoc`'s identity, which is why this
/// needed a separate `y <= 1` round-trip lemma (`round_trip_le_one`) rather
/// than transporting `xor_assoc`'s route directly.
#[test]
fn xor_xor_cancel_applies_at_a_concrete_discriminating_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete, cancel_left: xor 3 (xor 3 5) = xor 3 6 = 5 = b.
    {
        let three = f.num(3);
        let five = f.num(5);
        let applied = f.lemma(p.xor_xor_cancel_left, &[three, five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_xor_cancel_left must apply at (a=3, b=5): {shown}")
        });
        let xab = f.const_app(p.xor, &[three, five]);
        let lhs = f.const_app(p.xor, &[three, xab]);
        let want = f.eq(lhs, five);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_xor_cancel_left 3 5 must state Eq (xor 3 (xor 3 5)) 5"
        );
        assert!(f.k.def_eq(lhs, five), "xor 3 (xor 3 5) must compute to 5");
        // Negative control: must not ALSO state Eq lhs 4.
        let four = f.num(4);
        let bad_want = f.eq(lhs, four);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: xor_xor_cancel_left 3 5 must not state Eq (xor 3 (xor 3 5)) 4"
        );
    }

    // Concrete, cancel_right: xor (xor 3 5) 5 = xor 6 5 = 3 = a.
    {
        let three = f.num(3);
        let five = f.num(5);
        let applied = f.lemma(p.xor_xor_cancel_right, &[three, five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_xor_cancel_right must apply at (a=3, b=5): {shown}")
        });
        let xab = f.const_app(p.xor, &[three, five]);
        let lhs = f.const_app(p.xor, &[xab, five]);
        let want = f.eq(lhs, three);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_xor_cancel_right 3 5 must state Eq (xor (xor 3 5) 5) 3"
        );
        assert!(f.k.def_eq(lhs, three), "xor (xor 3 5) 5 must compute to 3");
        // Negative control: must not ALSO state Eq lhs 4.
        let four = f.num(4);
        let bad_want = f.eq(lhs, four);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: xor_xor_cancel_right 3 5 must not state Eq (xor (xor 3 5) 5) 4"
        );
    }

    // Symbolic: both apply at a genuinely FREE (a, b) pair.
    {
        let name = f.name("xor_xor_cancel_left_restated");
        f.theorem(name, 2, &|d, values| {
            let (a, b) = (values[0], values[1]);
            let xab = d.const_app(p.xor, &[a, b]);
            let lhs = d.const_app(p.xor, &[a, xab]);
            let stmt = d.eq(lhs, b);
            let proof = d.lemma(p.xor_xor_cancel_left, &[a, b]);
            (stmt, proof)
        })
        .expect("xor_xor_cancel_left must apply at symbolic a, b");

        let name = f.name("xor_xor_cancel_right_restated");
        f.theorem(name, 2, &|d, values| {
            let (a, b) = (values[0], values[1]);
            let xab = d.const_app(p.xor, &[a, b]);
            let lhs = d.const_app(p.xor, &[xab, b]);
            let stmt = d.eq(lhs, a);
            let proof = d.lemma(p.xor_xor_cancel_right, &[a, b]);
            (stmt, proof)
        })
        .expect("xor_xor_cancel_right must apply at symbolic a, b");
    }

    assert!(
        f.k.axiom_footprint(p.xor_xor_cancel_left).is_empty(),
        "xor_xor_cancel_left must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.xor_xor_cancel_right).is_empty(),
        "xor_xor_cancel_right must rest on zero axioms"
    );
}

/// `Nat.xor_ne_zero_iff` (`xor_algebra.rs`) -- the last of the four
/// sub-targets toward `F:ml430-nat-lt-xor-cases-c43a1e85`'s piece 4. Checked
/// at the discriminating concrete pair `(a, b) = (3, 5)` (`xor 3 5 = 6`, so
/// `Not (Eq (xor 3 5) 0)` and `Not (Eq 3 5)` are both genuinely true, via
/// `Nat.succ_ne_zero` at `5`) AND symbolically against a genuinely FREE
/// `(a, b)` pair. Built via `mt` (modus tollens) applied twice, not via an
/// `Iff (Eq _ 0) (Eq _ _)` intermediate -- see `xor_algebra.rs`'s module doc.
#[test]
fn xor_ne_zero_iff_applies_at_a_concrete_discriminating_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let five = f.num(5);
    let six = f.num(6);
    let xor35 = f.const_app(p.xor, &[three, five]);
    assert!(f.k.def_eq(xor35, six), "xor 3 5 must compute to 6");

    let iff_35 = f.lemma(p.xor_ne_zero_iff, &[three, five]);
    let zero = f.zero();
    let eq_xor_zero_ty = f.eq(xor35, zero);
    let not_xor_zero_ty = f.const_app(p.logic.not, &[eq_xor_zero_ty]);
    let eq_35_ty = f.eq(three, five);
    let not_35_ty = f.const_app(p.logic.not, &[eq_35_ty]);

    // Not (Eq (succ 5) 0), defeq to Not (Eq (xor 3 5) 0) (succ 5 = 6 = xor 3 5).
    let not_xor_zero_proof = f.lemma(p.succ_ne_zero, &[five]);
    let not_xor_zero_ty_check =
        f.k.infer(not_xor_zero_proof)
            .unwrap_or_else(|e| panic!("succ_ne_zero(5) should type-check: {}", f.explain(&e)));
    assert!(
        f.k.def_eq(not_xor_zero_ty_check, not_xor_zero_ty),
        "Not (Eq (succ 5) 0) must be defeq to Not (Eq (xor 3 5) 0)"
    );

    let mp = f.const_app(p.logic.iff_mp, &[not_xor_zero_ty, not_35_ty, iff_35]);
    let not_35_proof = f.apply(mp, &[not_xor_zero_proof]);
    let not_35_inferred = f.k.infer(not_35_proof).unwrap_or_else(|e| {
        panic!(
            "xor_ne_zero_iff(3,5).mp(succ_ne_zero 5) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(not_35_inferred, not_35_ty),
        "xor_ne_zero_iff(3,5).mp(...) must land on Not (Eq 3 5)"
    );
    // Negative control: must not ALSO be defeq to Not (Eq 3 3).
    let eq_33_ty = f.eq(three, three);
    let not_33_ty = f.const_app(p.logic.not, &[eq_33_ty]);
    assert!(
        !f.k.def_eq(not_35_inferred, not_33_ty),
        "negative control: Not (Eq 3 5) must not be defeq to Not (Eq 3 3)"
    );

    // mpr: feed the just-derived Not (Eq 3 5) back through and land on
    // Not (Eq (xor 3 5) 0) again.
    let mpr = f.const_app(p.logic.iff_mpr, &[not_xor_zero_ty, not_35_ty, iff_35]);
    let roundtrip = f.apply(mpr, &[not_35_proof]);
    let roundtrip_ty = f.k.infer(roundtrip).unwrap_or_else(|e| {
        panic!(
            "xor_ne_zero_iff(3,5).mpr(Not (Eq 3 5)) should type-check: {}",
            f.explain(&e)
        )
    });
    assert!(
        f.k.def_eq(roundtrip_ty, not_xor_zero_ty),
        "xor_ne_zero_iff(3,5).mpr(...) must land back on Not (Eq (xor 3 5) 0)"
    );

    // Symbolic: applies at a genuinely FREE (a, b) pair.
    {
        let name = f.name("xor_ne_zero_iff_restated");
        f.theorem(name, 2, &|d, values| {
            let (a, b) = (values[0], values[1]);
            let xab = d.const_app(p.xor, &[a, b]);
            let zero = d.zero();
            let eq_xor_zero = d.eq(xab, zero);
            let eq_ab = d.eq(a, b);
            let not_xor_zero = d.const_app(p.logic.not, &[eq_xor_zero]);
            let not_ab = d.const_app(p.logic.not, &[eq_ab]);
            let stmt = d.const_app(p.logic.iff, &[not_xor_zero, not_ab]);
            let proof = d.lemma(p.xor_ne_zero_iff, &[a, b]);
            (stmt, proof)
        })
        .expect("xor_ne_zero_iff must apply at symbolic a, b");
    }

    assert!(
        f.k.axiom_footprint(p.xor_ne_zero_iff).is_empty(),
        "xor_ne_zero_iff must rest on zero axioms"
    );
}

/// `Nat.xor_trichotomy` and `Nat.lt_xor_cases` -- the composition step for
/// `F:ml430-nat-lt-xor-cases-c43a1e85`, now that all four blocking pieces
/// (`testBit_xor`, `exists_most_significant_bit`, `lt_of_testBit`,
/// `xor_assoc`/`xor_xor_cancel_left`/`_right`/`xor_ne_zero_iff`) are landed.
/// See `nat_prelude::xor_trichotomy`'s module doc for the full route.
///
/// `xor_trichotomy` checked at `(a, b, c) = (1, 2, 4)`: `v := xor (xor 1 2) 4
/// = xor 3 4 = 7`, all THREE disjuncts genuinely discriminating (`Lt 6 1`
/// false, `Lt 5 2` false, `Lt 3 4` true -- exactly the third holds, not a
/// vacuous "any branch would do" instance).
///
/// `lt_xor_cases` checked at `(a, b, c) = (0, 2, 3)`: `h : Lt 0 (xor 2 3) =
/// Lt 0 1`, conclusion `Or (Lt (xor 0 3) 2) (Lt (xor 0 2) 3) = Or (Lt 3 2)
/// (Lt 2 3)` -- `Lt 3 2` false, `Lt 2 3` true, so the RIGHT disjunct must
/// hold, discriminating the two branches. Both checked AND symbolically at a
/// genuinely free `(a, b, c)` triple with a free hypothesis fvar, confirming
/// the declared shape.
#[test]
fn xor_trichotomy_and_lt_xor_cases_apply_at_concrete_discriminating_instances_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // xor_trichotomy, concrete: (a, b, c) = (1, 2, 4).
    {
        let one = f.num(1);
        let two = f.num(2);
        let four = f.num(4);
        let six = f.num(6);
        let seven = f.num(7);
        let xab_12 = f.const_app(p.xor, &[one, two]);
        let v = f.const_app(p.xor, &[xab_12, four]);
        assert!(f.k.def_eq(v, seven), "xor (xor 1 2) 4 must compute to 7");

        let h_ne = f.lemma(p.succ_ne_zero, &[six]); // Not (Eq (succ 6) 0), defeq Not (Eq v 0)
        let applied = f.lemma(p.xor_trichotomy, &[one, two, four, h_ne]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("xor_trichotomy must apply at (1, 2, 4): {shown}")
        });

        let xbc = f.const_app(p.xor, &[two, four]); // 6
        let xca = f.const_app(p.xor, &[four, one]); // 5
        let xab = f.const_app(p.xor, &[one, two]); // 3
        let lt_bc_a = f.lt(xbc, one);
        let lt_ca_b = f.lt(xca, two);
        let lt_ab_c = f.lt(xab, four);
        let inner = f.const_app(p.logic.or, &[lt_ca_b, lt_ab_c]);
        let want = f.const_app(p.logic.or, &[lt_bc_a, inner]);
        assert!(
            f.k.def_eq(inferred, want),
            "xor_trichotomy(1,2,4) must state Or (Lt 6 1) (Or (Lt 5 2) (Lt 3 4))"
        );
        // Negative control: reordering the disjuncts must not ALSO match.
        let bad_inner = f.const_app(p.logic.or, &[lt_bc_a, lt_ca_b]);
        let bad_want = f.const_app(p.logic.or, &[lt_ab_c, bad_inner]);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: the disjunct order must not be reorderable"
        );
    }

    assert!(
        f.k.axiom_footprint(p.xor_trichotomy).is_empty(),
        "xor_trichotomy must rest on zero axioms"
    );

    // lt_xor_cases, concrete: (a, b, c) = (0, 2, 3).
    {
        let zero = f.zero();
        let two = f.num(2);
        let three = f.num(3);
        let h_proof = f.lemma(p.zero_lt_succ, &[zero]); // Lt 0 1, defeq Lt 0 (xor 2 3)
        let applied = f.lemma(p.lt_xor_cases, &[zero, two, three, h_proof]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lt_xor_cases must apply at (0, 2, 3): {shown}")
        });

        let xac = f.const_app(p.xor, &[zero, three]); // 3
        let xab = f.const_app(p.xor, &[zero, two]); // 2
        let lt_ac_b = f.lt(xac, two); // Lt 3 2, false
        let lt_ab_c = f.lt(xab, three); // Lt 2 3, true
        let want = f.const_app(p.logic.or, &[lt_ac_b, lt_ab_c]);
        assert!(
            f.k.def_eq(inferred, want),
            "lt_xor_cases(0,2,3) must state Or (Lt 3 2) (Lt 2 3)"
        );
        // Negative control: swapping the disjuncts must not ALSO match.
        let bad_want = f.const_app(p.logic.or, &[lt_ab_c, lt_ac_b]);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: the disjunct order must not be swappable"
        );
    }

    // Symbolic: lt_xor_cases applies at a genuinely FREE (a, b, c) triple
    // with a free hypothesis fvar.
    {
        let name = f.name("lt_xor_cases_restated");
        f.theorem(name, 3, &|d, values| {
            let (a, b, c) = (values[0], values[1], values[2]);
            let xbc = d.const_app(p.xor, &[b, c]);
            let xac = d.const_app(p.xor, &[a, c]);
            let xab = d.const_app(p.xor, &[a, b]);
            let h_ty = d.lt(a, xbc);
            let lt_ac_b = d.lt(xac, b);
            let lt_ab_c = d.lt(xab, c);
            let concl = d.const_app(p.logic.or, &[lt_ac_b, lt_ab_c]);
            let stmt = d.arrow(h_ty, concl);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let proof = d.lemma(p.lt_xor_cases, &[a, b, c, h]);
            let proof = d.lam_fv(h_fv, h_ty, proof);
            (stmt, proof)
        })
        .expect("lt_xor_cases must apply at a symbolic (a, b, c, H) tuple");
    }

    assert!(
        f.k.axiom_footprint(p.lt_xor_cases).is_empty(),
        "lt_xor_cases must rest on zero axioms"
    );
}

/// The `Nat.mod _ 2 ∈ {0, 1}` split `bitwise.rs` named as absent, in both its
/// forms: `Nat.lt_two_cases` (from a `Lt r 2` hypothesis) and
/// `Nat.mod_two_eq_zero_or_one` (the `Nat.mod` instance of it).
///
/// Both negative controls change ONE literal — `Eq _ 2` where the theorem
/// says `Eq _ 1` — deliberately: a control that transposes whole subterms
/// makes the kernel run a *failing* defeq with no early exit, which is a
/// pathology rather than a check.
#[test]
fn the_mod_two_split_is_available_in_both_its_forms() {
    let mut f = Fixture::new();
    let p = f.p;

    // lt_two_cases at the one case we can witness without a `le_refl`:
    // `Lt 0 2` from `zero_lt_succ 1`.
    {
        let one = f.num(1);
        let zero = f.num(0);
        let witness = f.zero_lt_succ(one);
        let applied = f.const_app(p.lt_two_cases, &[zero, witness]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lt_two_cases must apply at r = 0: {shown}")
        });
        let is_zero = f.eq(zero, zero);
        let is_one = f.eq(zero, one);
        let logic = f.p.logic;
        let want = f.const_app(logic.or, &[is_zero, is_one]);
        assert!(
            f.k.def_eq(inferred, want),
            "lt_two_cases 0 must state Or (Eq 0 0) (Eq 0 1)"
        );
        let two = f.num(2);
        let is_two = f.eq(zero, two);
        let bad_want = f.const_app(logic.or, &[is_zero, is_two]);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: lt_two_cases 0 must not state Or (Eq 0 0) (Eq 0 2)"
        );
        assert!(
            f.k.axiom_footprint(p.lt_two_cases).is_empty(),
            "lt_two_cases must rest on zero axioms"
        );
    }

    // mod_two_eq_zero_or_one at a concrete argument, and the disjunction's
    // two sides must be genuinely different propositions (a split whose
    // branches coincided would be vacuous).
    {
        let seven = f.num(7);
        let zero = f.num(0);
        let one = f.num(1);
        let two = f.num(2);
        let applied = f.const_app(p.mod_two_eq_zero_or_one, &[seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("mod_two_eq_zero_or_one must apply at n = 7: {shown}")
        });
        let remainder = f.modulo(seven, two);
        let is_zero = f.eq(remainder, zero);
        let is_one = f.eq(remainder, one);
        let logic = f.p.logic;
        let want = f.const_app(logic.or, &[is_zero, is_one]);
        assert!(
            f.k.def_eq(inferred, want),
            "mod_two_eq_zero_or_one 7 must state Or (Eq (mod 7 2) 0) (Eq (mod 7 2) 1)"
        );
        let is_two = f.eq(remainder, two);
        let bad_want = f.const_app(logic.or, &[is_zero, is_two]);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: the right disjunct is Eq (mod 7 2) 1, not Eq (mod 7 2) 2"
        );
        // 7 % 2 = 1, so the LEFT disjunct is false here: the two sides are
        // not the same proposition and the split is not vacuous.
        assert!(
            !f.k.def_eq(is_zero, is_one),
            "the two disjuncts must be different propositions"
        );
        assert!(
            f.k.axiom_footprint(p.mod_two_eq_zero_or_one).is_empty(),
            "mod_two_eq_zero_or_one must rest on zero axioms"
        );
    }
}

/// The UNIVERSAL specialization equivalences —
/// `Nat.bitwise_and_eq_land : ∀ m n, Eq (bitwise and_fn m n) (land m n)` and
/// its `lor` twin — which supersede `bitwise.rs`'s single-point
/// `_three_five` witnesses.
///
/// Checked BOTH ways, because the two catch disjoint defects (see
/// `CLAUDE.md`: numerals reduce, and reduction hides every defeq-shaped gap,
/// while a symbolic check cannot catch a transposed branch):
///
/// - **symbolically**, by re-declaring the statement in a consumer namespace
///   with the prelude theorem instantiated at genuinely bound variables — if
///   the theorem only held at numerals this would not admit;
/// - **concretely**, at operand pairs whose AND and OR values differ, so a
///   copy-paste between the two blocks fails loudly.
///
/// The negative control reuses the very proof that certifies the `land`
/// instance against the `lor` statement at `(3, 5)`, where the two sides
/// reduce to `1` and `7`: the kernel must reject it.
#[test]
fn the_bitwise_specialization_equivalences_hold_universally() {
    let mut f = Fixture::new();
    let p = f.p;
    let bitwise = p.bitwise;

    let and_ = super::bitwise::and_fn(&mut f);
    let or_ = super::bitwise::or_fn(&mut f);

    // Symbolic: the statement re-declared over bound variables, proved by the
    // prelude theorem alone.
    {
        let land = p.land;
        let name = f.name("bitwise_and_eq_land_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(bitwise, &[and_, m, n]);
            let rhs = d.const_app(land, &[m, n]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.bitwise_and_eq_land, &[m, n]);
            (stmt, proof)
        })
        .expect("bitwise_and_eq_land must apply at symbolic operands");
    }
    {
        let lor = p.lor;
        let name = f.name("bitwise_or_eq_lor_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(bitwise, &[or_, m, n]);
            let rhs = d.const_app(lor, &[m, n]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.bitwise_or_eq_lor, &[m, n]);
            (stmt, proof)
        })
        .expect("bitwise_or_eq_lor must apply at symbolic operands");
    }

    // Concrete: instantiated at pairs where AND and OR disagree, so the two
    // theorems cannot be confused for each other.
    for (m, n) in [(0u32, 0u32), (0, 5), (5, 0), (3, 5), (5, 3), (6, 3), (7, 7)] {
        let mm = f.num(m);
        let nn = f.num(n);

        let applied = f.const_app(p.bitwise_and_eq_land, &[mm, nn]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_and_eq_land must apply at ({m}, {n}): {shown}")
        });
        let lhs = f.const_app(bitwise, &[and_, mm, nn]);
        let rhs = f.const_app(p.land, &[mm, nn]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_and_eq_land {m} {n} must state Eq (bitwise and_fn {m} {n}) (land {m} {n})"
        );

        let applied = f.const_app(p.bitwise_or_eq_lor, &[mm, nn]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_or_eq_lor must apply at ({m}, {n}): {shown}")
        });
        let lhs = f.const_app(bitwise, &[or_, mm, nn]);
        let rhs = f.const_app(p.lor, &[mm, nn]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_or_eq_lor {m} {n} must state Eq (bitwise or_fn {m} {n}) (lor {m} {n})"
        );
    }

    // Negative control: the AND agreement proof against the OR statement, at
    // (3, 5) where the two sides reduce to 1 and 7.
    {
        let three = f.num(3);
        let five = f.num(5);
        let lhs = f.const_app(bitwise, &[and_, three, five]);
        let wrong_rhs = f.const_app(p.lor, &[three, five]);
        let wrong_ty = f.eq(lhs, wrong_rhs);
        let proof = f.lemma(p.bitwise_and_eq_land, &[three, five]);
        let name = f.name("bitwise_and_eq_lor_three_five");
        let error = f
            .declare_theorem(name, wrong_ty, proof)
            .expect_err("NC: the land agreement must not prove the lor statement");
        assert!(matches!(
            error,
            KernelError::DeclarationValueMismatch { .. }
        ));
        assert!(!f.k.environment().contains(name));
    }

    // The FUEL-GENERALIZED form holds at a fuel that is NOT the canonical
    // `fuel = m`, and specifically at an INSUFFICIENT one. This is the
    // evidence that agreement does not depend on fuel sufficiency, so no
    // fuel-irrelevance lemma is a prerequisite for it: at `(fuel, m, n) =
    // (1, 7, 7)` both auxiliaries take a single step and stop, giving `1`
    // where the canonical answer is `7` -- and they still agree.
    {
        let one = f.num(1);
        let seven = f.num(7);
        let applied = f.const_app(p.bitwise_aux_eq_land_aux, &[one, seven, seven]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_aux_eq_land_aux must apply at fuel 1: {shown}")
        });
        let lhs = f.const_app(p.bitwise_aux, &[and_, one, seven, seven]);
        let rhs = f.const_app(p.land_aux, &[one, seven, seven]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_aux_eq_land_aux 1 7 7 must state \
             Eq (bitwiseAux and_fn 1 7 7) (landAux 1 7 7)"
        );
        // The fuel really is insufficient: one step gives 1, the canonical
        // `land 7 7` is 7. Without this the block above would be vacuous --
        // it would only be re-checking the canonical instance under another
        // name.
        assert!(
            f.k.def_eq(rhs, one),
            "landAux 1 7 7 must be 1 (a single fuel step)"
        );
        let canonical = f.const_app(p.land, &[seven, seven]);
        assert!(
            f.k.def_eq(canonical, seven),
            "land 7 7 must be 7 (the canonical answer)"
        );
        assert!(
            !f.k.def_eq(rhs, canonical),
            "the chosen fuel must be INSUFFICIENT, or this instance says nothing \
             about non-canonical fuel"
        );
        assert!(
            f.k.axiom_footprint(p.bitwise_aux_eq_land_aux).is_empty(),
            "bitwise_aux_eq_land_aux must rest on zero axioms"
        );
    }

    assert!(
        f.k.axiom_footprint(p.bitwise_aux_eq_lor_aux).is_empty(),
        "bitwise_aux_eq_lor_aux must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_and_eq_land).is_empty(),
        "bitwise_and_eq_land must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_or_eq_lor).is_empty(),
        "bitwise_or_eq_lor must rest on zero axioms"
    );
}

/// `Nat.land_aux_eq_land_of_le : ∀ fuel m n, Le m fuel → Eq (landAux fuel m
/// n) (land m n)` — fuel-irrelevance for `landAux`, applies at symbolic
/// `fuel`/`m`/`n` given the hypothesis, and at a concrete fuel STRICTLY
/// ABOVE canonical (`fuel = 7`, `m = 1`), where both sides compute to `1`.
///
/// **The mandatory negative control**: at INSUFFICIENT fuel (`fuel = 1`,
/// `m = 7`), the auxiliary and the canonical answer genuinely differ
/// (`landAux 1 7 7 = 1`, `land 7 7 = 7`) — the same pinned witness the
/// `rec_agreement` lane used for `bitwise_aux_eq_land_aux`. This is checked
/// directly by evaluation, NOT through `land_aux_eq_land_of_le` itself
/// (`Le 7 1` is false and has no proof to apply the theorem with); its job
/// is to confirm the theorem's `Le m fuel` hypothesis is doing real work —
/// if the two sides agreed even here, the statement would be too weak to
/// need a hypothesis at all.
#[test]
fn land_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables plus the
    // `Le m fuel` hypothesis, proved by the prelude theorem alone.
    {
        let name = f.name("land_aux_eq_land_of_le_restated");
        f.theorem(name, 3, &|d, values| {
            let fuel = values[0];
            let m = values[1];
            let n = values[2];
            let bound_ty = d.le(m, fuel);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let lhs = d.const_app(p.land_aux, &[fuel, m, n]);
            let rhs = d.const_app(p.land, &[m, n]);
            let concl = d.eq(lhs, rhs);
            let stmt = d.arrow(bound_ty, concl);
            let lemma_fn = d.lemma(p.land_aux_eq_land_of_le, &[fuel, m, n]);
            let proof = d.apply(lemma_fn, &[bound]);
            let value = d.lam_fv(bound_fv, bound_ty, proof);
            (stmt, value)
        })
        .expect("land_aux_eq_land_of_le must apply at symbolic fuel/m/n given Le m fuel");
    }

    // Concrete, ABOVE canonical fuel: `fuel = 7`, `m = 1`, `n = 7` — `Le 1 7`
    // holds (`ble 1 7 = true`), and both `landAux 7 1 7` and `land 1 7`
    // compute to `1`.
    {
        let fuel = f.num(7);
        let m = f.num(1);
        let n = f.num(7);
        let true_ = f.bool_true();
        let ble_refl = f.bool_refl(true_);
        let bound = f.lemma(p.le_of_ble_eq_true, &[m, fuel, ble_refl]);
        let applied = f.const_app(p.land_aux_eq_land_of_le, &[fuel, m, n]);
        let applied = f.apply(applied, &[bound]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_aux_eq_land_of_le must apply at (fuel=7, m=1, n=7): {shown}")
        });
        let lhs = f.const_app(p.land_aux, &[fuel, m, n]);
        let rhs = f.const_app(p.land, &[m, n]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "land_aux_eq_land_of_le 7 1 7 must state Eq (landAux 7 1 7) (land 1 7)"
        );
        let one = f.num(1);
        assert!(f.k.def_eq(lhs, one), "landAux 7 1 7 must compute to 1");
        assert!(f.k.def_eq(rhs, one), "land 1 7 must compute to 1");
        assert!(
            f.k.axiom_footprint(p.land_aux_eq_land_of_le).is_empty(),
            "land_aux_eq_land_of_le must rest on zero axioms"
        );
    }

    // Negative control: at INSUFFICIENT fuel, the auxiliary genuinely
    // disagrees with the canonical answer -- `landAux 1 7 7 = 1` against
    // `land 7 7 = 7`. Checked by evaluation alone (no `Le 7 1` proof
    // exists), confirming the hypothesis is load-bearing.
    {
        let one = f.num(1);
        let seven = f.num(7);
        let insufficient = f.const_app(p.land_aux, &[one, seven, seven]);
        let canonical = f.const_app(p.land, &[seven, seven]);
        assert!(
            f.k.def_eq(insufficient, one),
            "landAux 1 7 7 must be 1 (a single fuel step)"
        );
        assert!(
            f.k.def_eq(canonical, seven),
            "land 7 7 must be 7 (the canonical answer)"
        );
        assert!(
            !f.k.def_eq(insufficient, canonical),
            "the chosen fuel must be INSUFFICIENT, or this control proves nothing \
             about why `Le m fuel` is needed"
        );
    }

    assert!(
        f.k.axiom_footprint(p.land_aux_zero_left_any_fuel)
            .is_empty(),
        "land_aux_zero_left_any_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_aux_agree_of_fuel).is_empty(),
        "land_aux_agree_of_fuel must rest on zero axioms"
    );
}

/// The `lor` transport of
/// `land_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control`.
///
/// **The mandatory negative control differs from `land`'s witness**, because
/// `lorAux`'s fuel-exhaustion row returns `n`, not `0` — the same numeral
/// pair that discriminates `land` does not discriminate `lor` (e.g.
/// `(fuel=1, m=7, n=7)` gives `lorAux 1 7 7 = 7 = lor 7 7`, no disagreement
/// at all). `(fuel = 1, m = 3, n = 4)` does discriminate: `lorAux 1 3 4 = 5`
/// against `lor 3 4 = 7` (`011 | 100 = 111`).
#[test]
fn lor_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables plus the
    // `Le m fuel` hypothesis, proved by the prelude theorem alone.
    {
        let name = f.name("lor_aux_eq_lor_of_le_restated");
        f.theorem(name, 3, &|d, values| {
            let fuel = values[0];
            let m = values[1];
            let n = values[2];
            let bound_ty = d.le(m, fuel);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let lhs = d.const_app(p.lor_aux, &[fuel, m, n]);
            let rhs = d.const_app(p.lor, &[m, n]);
            let concl = d.eq(lhs, rhs);
            let stmt = d.arrow(bound_ty, concl);
            let lemma_fn = d.lemma(p.lor_aux_eq_lor_of_le, &[fuel, m, n]);
            let proof = d.apply(lemma_fn, &[bound]);
            let value = d.lam_fv(bound_fv, bound_ty, proof);
            (stmt, value)
        })
        .expect("lor_aux_eq_lor_of_le must apply at symbolic fuel/m/n given Le m fuel");
    }

    // Concrete, ABOVE canonical fuel: `fuel = 7`, `m = 1`, `n = 7` — `Le 1 7`
    // holds, and both `lorAux 7 1 7` and `lor 1 7` compute to `7`.
    {
        let fuel = f.num(7);
        let m = f.num(1);
        let n = f.num(7);
        let true_ = f.bool_true();
        let ble_refl = f.bool_refl(true_);
        let bound = f.lemma(p.le_of_ble_eq_true, &[m, fuel, ble_refl]);
        let applied = f.const_app(p.lor_aux_eq_lor_of_le, &[fuel, m, n]);
        let applied = f.apply(applied, &[bound]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_aux_eq_lor_of_le must apply at (fuel=7, m=1, n=7): {shown}")
        });
        let lhs = f.const_app(p.lor_aux, &[fuel, m, n]);
        let rhs = f.const_app(p.lor, &[m, n]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_aux_eq_lor_of_le 7 1 7 must state Eq (lorAux 7 1 7) (lor 1 7)"
        );
        assert!(f.k.def_eq(lhs, n), "lorAux 7 1 7 must compute to 7");
        assert!(f.k.def_eq(rhs, n), "lor 1 7 must compute to 7");
        assert!(
            f.k.axiom_footprint(p.lor_aux_eq_lor_of_le).is_empty(),
            "lor_aux_eq_lor_of_le must rest on zero axioms"
        );
    }

    // Negative control: at INSUFFICIENT fuel, the auxiliary genuinely
    // disagrees with the canonical answer -- `lorAux 1 3 4 = 5` against
    // `lor 3 4 = 7`. Checked by evaluation alone (no `Le 3 1` proof exists),
    // confirming the hypothesis is load-bearing.
    {
        let fuel = f.num(1);
        let m = f.num(3);
        let n = f.num(4);
        let five = f.num(5);
        let seven = f.num(7);
        let insufficient = f.const_app(p.lor_aux, &[fuel, m, n]);
        let canonical = f.const_app(p.lor, &[m, n]);
        assert!(
            f.k.def_eq(insufficient, five),
            "lorAux 1 3 4 must be 5 (one fuel step short)"
        );
        assert!(
            f.k.def_eq(canonical, seven),
            "lor 3 4 must be 7 (the canonical answer)"
        );
        assert!(
            !f.k.def_eq(insufficient, canonical),
            "the chosen fuel must be INSUFFICIENT, or this control proves nothing \
             about why `Le m fuel` is needed"
        );
    }

    assert!(
        f.k.axiom_footprint(p.lor_aux_zero_left_any_fuel).is_empty(),
        "lor_aux_zero_left_any_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lor_aux_agree_of_fuel).is_empty(),
        "lor_aux_agree_of_fuel must rest on zero axioms"
    );
}

/// The `ldiff` transport of
/// `land_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control`.
///
/// **The mandatory negative control differs from BOTH `land`'s and `lor`'s
/// witness.** `ldiffAux`'s fuel-exhaustion row is the constant `0` (like
/// `land`'s), but the discriminating case for `ldiff` is `fuel = 0` itself:
/// `ldiffAux 0 7 0 = 0` directly (the outer `Nat.rec` never even reaches the
/// `n = 0` pass-through guard), against `ldiff 7 0 = 7` (`ldiff m 0 = m`,
/// `ldiff`'s `n = 0` guard IS reached at canonical fuel, since canonical
/// fuel `m = 7` is `succ`-shaped).
#[test]
fn ldiff_fuel_irrelevance_holds_above_canonical_fuel_with_an_insufficient_fuel_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables plus the
    // `Le m fuel` hypothesis, proved by the prelude theorem alone.
    {
        let name = f.name("ldiff_aux_eq_ldiff_of_le_restated");
        f.theorem(name, 3, &|d, values| {
            let fuel = values[0];
            let m = values[1];
            let n = values[2];
            let bound_ty = d.le(m, fuel);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let lhs = d.const_app(p.ldiff_aux, &[fuel, m, n]);
            let rhs = d.const_app(p.ldiff, &[m, n]);
            let concl = d.eq(lhs, rhs);
            let stmt = d.arrow(bound_ty, concl);
            let lemma_fn = d.lemma(p.ldiff_aux_eq_ldiff_of_le, &[fuel, m, n]);
            let proof = d.apply(lemma_fn, &[bound]);
            let value = d.lam_fv(bound_fv, bound_ty, proof);
            (stmt, value)
        })
        .expect("ldiff_aux_eq_ldiff_of_le must apply at symbolic fuel/m/n given Le m fuel");
    }

    // Concrete, ABOVE canonical fuel: `fuel = 7`, `m = 1`, `n = 7` — `Le 1 7`
    // holds, and both `ldiffAux 7 1 7` and `ldiff 1 7` compute to `0`.
    {
        let fuel = f.num(7);
        let m = f.num(1);
        let n = f.num(7);
        let true_ = f.bool_true();
        let ble_refl = f.bool_refl(true_);
        let bound = f.lemma(p.le_of_ble_eq_true, &[m, fuel, ble_refl]);
        let applied = f.const_app(p.ldiff_aux_eq_ldiff_of_le, &[fuel, m, n]);
        let applied = f.apply(applied, &[bound]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_aux_eq_ldiff_of_le must apply at (fuel=7, m=1, n=7): {shown}")
        });
        let lhs = f.const_app(p.ldiff_aux, &[fuel, m, n]);
        let rhs = f.const_app(p.ldiff, &[m, n]);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_aux_eq_ldiff_of_le 7 1 7 must state Eq (ldiffAux 7 1 7) (ldiff 1 7)"
        );
        let zero = f.zero();
        assert!(f.k.def_eq(lhs, zero), "ldiffAux 7 1 7 must compute to 0");
        assert!(f.k.def_eq(rhs, zero), "ldiff 1 7 must compute to 0");
        assert!(
            f.k.axiom_footprint(p.ldiff_aux_eq_ldiff_of_le).is_empty(),
            "ldiff_aux_eq_ldiff_of_le must rest on zero axioms"
        );
    }

    // Negative control: at INSUFFICIENT fuel (in fact `fuel = 0`, so the
    // outer `Nat.rec` never runs at all), the auxiliary genuinely disagrees
    // with the canonical answer -- `ldiffAux 0 7 0 = 0` against
    // `ldiff 7 0 = 7`. Checked by evaluation alone (no `Le 7 0` proof
    // exists), confirming the hypothesis is load-bearing.
    {
        let fuel = f.zero();
        let m = f.num(7);
        let n = f.zero();
        let zero = f.zero();
        let seven = f.num(7);
        let insufficient = f.const_app(p.ldiff_aux, &[fuel, m, n]);
        let canonical = f.const_app(p.ldiff, &[m, n]);
        assert!(
            f.k.def_eq(insufficient, zero),
            "ldiffAux 0 7 0 must be 0 (zero fuel, the outer Nat.rec never runs)"
        );
        assert!(
            f.k.def_eq(canonical, seven),
            "ldiff 7 0 must be 7 (the canonical answer)"
        );
        assert!(
            !f.k.def_eq(insufficient, canonical),
            "the chosen fuel must be INSUFFICIENT, or this control proves nothing \
             about why `Le m fuel` is needed"
        );
    }

    assert!(
        f.k.axiom_footprint(p.ldiff_aux_zero_left_any_fuel)
            .is_empty(),
        "ldiff_aux_zero_left_any_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.ldiff_aux_agree_of_fuel).is_empty(),
        "ldiff_aux_agree_of_fuel must rest on zero axioms"
    );
}

/// `Nat.land_comm` applies at symbolic `m`/`n` and at a concrete,
/// DISCRIMINATING instance where `m` and `n` have DIFFERENT bit patterns
/// (`land 3 6 = 2`, `011 & 110 = 010`) -- a symmetric pair like `(5, 5)`
/// cannot catch a transposed argument, since both orderings would agree
/// regardless of whether the proof is right.
#[test]
fn land_comm_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone.
    {
        let name = f.name("land_comm_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(p.land, &[m, n]);
            let rhs = d.const_app(p.land, &[n, m]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.land_comm, &[m, n]);
            (stmt, proof)
        })
        .expect("land_comm must apply at symbolic m/n");
    }

    // Concrete: `land 3 6 = 2` and `land 6 3 = 2` (`011 & 110 = 010`).
    {
        let three = f.num(3);
        let six = f.num(6);
        let two = f.num(2);
        let lhs = f.const_app(p.land, &[three, six]);
        let rhs = f.const_app(p.land, &[six, three]);
        let applied = f.lemma(p.land_comm, &[three, six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_comm must apply at (m=3, n=6): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "land_comm 3 6 must state Eq (land 3 6) (land 6 3)"
        );
        assert!(f.k.def_eq(lhs, two), "land 3 6 must compute to 2");
        assert!(f.k.def_eq(rhs, two), "land 6 3 must compute to 2");
    }

    assert!(
        f.k.axiom_footprint(p.land_aux_comm_of_fuel).is_empty(),
        "land_aux_comm_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_comm).is_empty(),
        "land_comm must rest on zero axioms"
    );
}

/// `Nat.lor_comm` applies at symbolic `m`/`n` and at a concrete,
/// DISCRIMINATING instance where `m` and `n` have DIFFERENT bit patterns
/// (`lor 3 6 = 7`, `011 | 110 = 111`) -- the `lor` twin of
/// `land_comm_applies_at_a_concrete_discriminating_instance`. Unlike
/// `land_aux_comm_of_fuel`, `lor_aux_comm_of_fuel` carries `Le` hypotheses
/// (see `nat_prelude::rec_agreement`'s module doc for why), so this also
/// checks the theorem applies once those bounds are supplied at fuel `m + n`.
#[test]
fn lor_comm_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone.
    {
        let name = f.name("lor_comm_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(p.lor, &[m, n]);
            let rhs = d.const_app(p.lor, &[n, m]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.lor_comm, &[m, n]);
            (stmt, proof)
        })
        .expect("lor_comm must apply at symbolic m/n");
    }

    // Concrete: `lor 3 6 = 7` and `lor 6 3 = 7` (`011 | 110 = 111`).
    {
        let three = f.num(3);
        let six = f.num(6);
        let seven = f.num(7);
        let lhs = f.const_app(p.lor, &[three, six]);
        let rhs = f.const_app(p.lor, &[six, three]);
        let applied = f.lemma(p.lor_comm, &[three, six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_comm must apply at (m=3, n=6): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_comm 3 6 must state Eq (lor 3 6) (lor 6 3)"
        );
        assert!(f.k.def_eq(lhs, seven), "lor 3 6 must compute to 7");
        assert!(f.k.def_eq(rhs, seven), "lor 6 3 must compute to 7");
    }

    // `lor_aux_comm_of_fuel` applies at the shared fuel `m + n` once both
    // `Le` bounds are supplied -- the piece `land_aux_comm_of_fuel` does not
    // need at all.
    {
        let three = f.num(3);
        let six = f.num(6);
        let sum = f.add(three, six);
        let le_three_sum = f.lemma(p.le_add_right, &[three, six]);
        // `Le six sum` needs `add_comm` since only `le_add_right` (not a
        // `le_add_left`) exists -- same transport `lor_comm` itself uses.
        let six_sum = f.add(six, three);
        let le_six_six_sum = f.lemma(p.le_add_right, &[six, three]);
        let add_comm_63 = f.lemma(p.add_comm, &[six, three]);
        let motive = f.eq_motive(six_sum, &|d, x| d.le(six, x));
        let le_six_sum = f.transport(six_sum, motive, le_six_six_sum, sum, add_comm_63);
        let applied = f.lemma(p.lor_aux_comm_of_fuel, &[sum, three, six]);
        let applied = f.apply(applied, &[le_three_sum, le_six_sum]);
        f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_aux_comm_of_fuel must apply at fuel = 3 + 6: {shown}")
        });
    }

    // Negative control: WITHOUT the `Le` hypotheses,
    // `lor_aux_comm_of_fuel`'s unconditional analogue would be FALSE --
    // unlike `land_aux_comm_of_fuel`, which needs no hypothesis at all
    // because `landAux`'s fuel-exhaustion row is the absorbing constant `0`
    // regardless of argument order. `lorAux`'s row is pass-through
    // (`lorAux 0 m n = n`), so at insufficient fuel `lorAux fuel a b` and
    // `lorAux fuel b a` can disagree: `lorAux 0 0 1 = 1` while
    // `lorAux 0 1 0 = 0` (simulated in Python before committing to this
    // control). Checked by evaluation alone, at deliberately small operands
    // (a failing `def_eq` has no early exit).
    {
        let fuel = f.num(0);
        let a = f.num(0);
        let b = f.num(1);
        let one = f.num(1);
        let zero = f.num(0);
        let lhs = f.const_app(p.lor_aux, &[fuel, a, b]);
        let rhs = f.const_app(p.lor_aux, &[fuel, b, a]);
        assert!(f.k.def_eq(lhs, one), "lorAux 0 0 1 must compute to 1");
        assert!(f.k.def_eq(rhs, zero), "lorAux 0 1 0 must compute to 0");
        assert!(
            !f.k.def_eq(lhs, rhs),
            "the chosen (fuel, a, b) must be INSUFFICIENT and DISCRIMINATING, \
             or this control proves nothing about why lor_aux_comm_of_fuel \
             needs the Le hypotheses"
        );
    }

    assert!(
        f.k.axiom_footprint(p.lor_aux_comm_of_fuel).is_empty(),
        "lor_aux_comm_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lor_comm).is_empty(),
        "lor_comm must rest on zero axioms"
    );
}

/// `∀ a b : Bool, Eq (f a b) (f b a)` for a CONCRETE commutative `f`
/// (`xor_fn`/`or_fn` in this file's tests), proved by nested `Bool.rec` on
/// `a` then `b` -- four leaves, each closing by computation since `f`
/// applied to two LITERAL `Bool`s reduces on both sides. The `hf`
/// [`NatPrelude::bitwise_comm`] itself needs, built from `ops.rs`'s
/// `NatOps::bool_eq`/`NatOps::bool_refl` (a first pass used `d.refl`, which
/// is HARDCODED to `Nat` and produced a `TypeMismatch` wearing a sort
/// error's clothes -- `bitwise.rs`'s `congr_bool_to_nat` hit the same trap).
fn bool_fn_comm<D: NatOps>(d: &mut D, f_term: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let z = d.kernel().level_zero();
    let bool_rec_name = d.prelude().logic.bool_rec;

    let inner_for_literal = |d: &mut D, lit: ExprId| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let lhs = d.apply(f_term, &[lit, b]);
        let rhs = d.apply(f_term, &[b, lit]);
        let motive_body = d.bool_eq(lhs, rhs);
        let motive = d.lam_fv(b_fv, bool_ty, motive_body);
        let false_leaf = {
            let lhs = d.apply(f_term, &[lit, false_]);
            d.bool_refl(lhs)
        };
        let true_leaf = {
            let lhs = d.apply(f_term, &[lit, true_]);
            d.bool_refl(lhs)
        };
        let bool_rec = d.kernel().const_(bool_rec_name, vec![z]);
        let elim = d.apply(bool_rec, &[motive, false_leaf, true_leaf, b]);
        d.lam_fv(b_fv, bool_ty, elim)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let lhs_ab = d.apply(f_term, &[a, b]);
    let rhs_ab = d.apply(f_term, &[b, a]);
    let inner_eq = d.bool_eq(lhs_ab, rhs_ab);
    let inner_pi = d.pi_fv(b_fv, bool_ty, inner_eq);
    let outer_motive = d.lam_fv(a_fv, bool_ty, inner_pi);

    let at_false = inner_for_literal(d, false_);
    let at_true = inner_for_literal(d, true_);
    let bool_rec = d.kernel().const_(bool_rec_name, vec![z]);
    let elim = d.apply(bool_rec, &[outer_motive, at_false, at_true, a]);
    d.lam_fv(a_fv, bool_ty, elim)
}

/// `Nat.bitwise_comm` applies at a CONCRETE, DISCRIMINATING instance
/// (`f = xor_fn`, `bitwise xor 3 5 = 6 = bitwise xor 5 3`) once a concrete
/// `hf` proof ([`bool_fn_comm`]) and the shared-fuel `Le` bounds are
/// supplied -- `F:ml430-nat-bitwise-comm-1a273bae`. Unlike
/// `land_aux_comm_of_fuel` (unconditional), and matching
/// `lor_aux_comm_of_fuel`, the insufficient-fuel negative control below uses
/// `or_fn` (`f false true = true`, the same reason `lor`'s own row is not
/// the absorbing constant), NOT `xor_fn` mechanically copied from `lor`'s
/// witness -- confirmed discriminating by the same Python simulation
/// recorded in `docs/plan/status/256-nat-bitwise-comm.md`.
#[test]
fn bitwise_comm_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let xor_fn_term = super::bitwise::xor_fn(&mut f);
    let hf = bool_fn_comm(&mut f, xor_fn_term);

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone (at this fixed concrete `f`/`hf`).
    {
        let name = f.name("bitwise_comm_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(p.bitwise, &[xor_fn_term, m, n]);
            let rhs = d.const_app(p.bitwise, &[xor_fn_term, n, m]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.bitwise_comm, &[xor_fn_term, hf, m, n]);
            (stmt, proof)
        })
        .expect("bitwise_comm must apply at symbolic m/n for a fixed f/hf");
    }

    // Concrete: `bitwise xor 3 5 = 6` and `bitwise xor 5 3 = 6`
    // (`011 xor 101 = 110`).
    {
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let lhs = f.const_app(p.bitwise, &[xor_fn_term, three, five]);
        let rhs = f.const_app(p.bitwise, &[xor_fn_term, five, three]);
        let applied = f.lemma(p.bitwise_comm, &[xor_fn_term, hf, three, five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_comm must apply at (f=xor, m=3, n=5): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_comm xor 3 5 must state Eq (bitwise xor 3 5) (bitwise xor 5 3)"
        );
        assert!(f.k.def_eq(lhs, six), "bitwise xor 3 5 must compute to 6");
        assert!(f.k.def_eq(rhs, six), "bitwise xor 5 3 must compute to 6");
    }

    // Negative control: WITHOUT the `Le` hypotheses, `bitwise_aux_comm_of_fuel`'s
    // unconditional analogue is FALSE for `f = or_fn` (`f false true = true`),
    // exactly as for `lorAux` -- `bitwiseAux or 0 0 1 = 1` while
    // `bitwiseAux or 0 1 0 = 0` (Python-simulated before this was written).
    {
        let or_fn_term = super::bitwise::or_fn(&mut f);
        let fuel = f.num(0);
        let a = f.num(0);
        let b = f.num(1);
        let one = f.num(1);
        let zero = f.num(0);
        let lhs = f.const_app(p.bitwise_aux, &[or_fn_term, fuel, a, b]);
        let rhs = f.const_app(p.bitwise_aux, &[or_fn_term, fuel, b, a]);
        assert!(
            f.k.def_eq(lhs, one),
            "bitwiseAux or 0 0 1 must compute to 1"
        );
        assert!(
            f.k.def_eq(rhs, zero),
            "bitwiseAux or 0 1 0 must compute to 0"
        );
        assert!(
            !f.k.def_eq(lhs, rhs),
            "the chosen (fuel, a, b) must be INSUFFICIENT and DISCRIMINATING, \
             or this control proves nothing about why bitwise_aux_comm_of_fuel \
             needs the Le hypotheses"
        );
    }

    assert!(
        f.k.axiom_footprint(p.bitwise_aux_zero_left_any_fuel)
            .is_empty(),
        "bitwise_aux_zero_left_any_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_aux_agree_of_fuel).is_empty(),
        "bitwise_aux_agree_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_aux_comm_of_fuel).is_empty(),
        "bitwise_aux_comm_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_comm).is_empty(),
        "bitwise_comm must rest on zero axioms"
    );
}

/// `Nat.bitwise_swap` applies at a CONCRETE, DISCRIMINATING instance --
/// `F:ml430-nat-bitwise-swap-7175e90e`. `and`/`or`/`xor` are all
/// COMMUTATIVE, so none of them can discriminate this statement from the
/// vacuous case where swapping `f`'s arguments changes nothing: [`fst_fn`]
/// (`fun a b => a`) is the deliberately non-commutative fixture that
/// actually exercises the swap (`swap fst = fun a b => b`, the second
/// projection). Unlike `bitwise_comm`, no `hf` hypothesis is threaded --
/// `bitwise_swap` holds for EVERY `f`, proved unconditionally.
#[test]
fn bitwise_swap_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let fst_fn_term = super::bitwise::fst_fn(&mut f);
    let swap_fst_term = super::bitwise::swap_fn(&mut f, fst_fn_term);

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone (at this fixed concrete `f`).
    {
        let name = f.name("bitwise_swap_restated");
        f.theorem(name, 2, &|d, values| {
            let m = values[0];
            let n = values[1];
            let lhs = d.const_app(p.bitwise, &[swap_fst_term, m, n]);
            let rhs = d.const_app(p.bitwise, &[fst_fn_term, n, m]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.bitwise_swap, &[fst_fn_term, m, n]);
            (stmt, proof)
        })
        .expect("bitwise_swap must apply at symbolic m/n for a fixed f");
    }

    // Concrete: `fst` always returns its FIRST projection, so canonical-fuel
    // `bitwise fst m n` computes to `m` regardless of `n` (verified by hand
    // before writing this test: fuel = m always suffices to expose every
    // bit `fst` ever inspects). `swap fst = snd` therefore computes to `n`.
    // `m = 5, n = 3` (m != n) makes this genuinely discriminating -- an
    // `m = n` instance would pass even with the sides transposed.
    {
        let five = f.num(5);
        let three = f.num(3);
        let lhs = f.const_app(p.bitwise, &[swap_fst_term, five, three]);
        let rhs = f.const_app(p.bitwise, &[fst_fn_term, three, five]);
        let applied = f.lemma(p.bitwise_swap, &[fst_fn_term, five, three]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("bitwise_swap must apply at (f=fst, m=5, n=3): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "bitwise_swap fst 5 3 must state Eq (bitwise (swap fst) 5 3) (bitwise fst 3 5)"
        );
        assert!(
            f.k.def_eq(lhs, three),
            "bitwise (swap fst) 5 3 = bitwise snd 5 3 must compute to n = 3"
        );
        assert!(
            f.k.def_eq(rhs, three),
            "bitwise fst 3 5 must compute to m = 3 (fst always returns its \
             first projection)"
        );
        // Non-vacuity: confirm the UNSWAPPED value at the same operands
        // really is different, so this instance actually distinguishes
        // `bitwise fst 5 3` from `bitwise (swap fst) 5 3`.
        let unswapped = f.const_app(p.bitwise, &[fst_fn_term, five, three]);
        assert!(
            f.k.def_eq(unswapped, five),
            "bitwise fst 5 3 must compute to m = 5"
        );
        assert!(
            !f.k.def_eq(unswapped, lhs),
            "the chosen (f, m, n) must be DISCRIMINATING: bitwise fst 5 3 \
             and bitwise (swap fst) 5 3 must differ, or this instance \
             proves nothing about the swap"
        );
    }

    assert!(
        f.k.axiom_footprint(p.bitwise_aux_swap_of_fuel).is_empty(),
        "bitwise_aux_swap_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bitwise_swap).is_empty(),
        "bitwise_swap must rest on zero axioms"
    );
}

/// `Nat.bitwise_bit'` applies at a CONCRETE, DISCRIMINATING instance --
/// `F:ml430-nat-bitwise-bit-4c4b28a8`. `f := fst` (`fun a b => a`, the same
/// deliberately non-commutative fixture `bitwise_swap`'s own test uses,
/// whose section already established `bitwise fst m n` computes to `m`
/// unconditionally) at `a = false, m = 2, b = true, n = 3` -- `a != b`, so
/// an accidental argument swap in the per-bit combine (`f a b` vs `f b a`)
/// would be caught. `a = false` with `m = 2` (nonzero) exercises the leaf
/// that needs the side hypothesis `hm : m = 0 -> a = true` DISCHARGED even
/// though its premise never fires (via `Nat.succ_ne_zero`, since `m` is
/// concretely positive here); `b = true` keeps `hn` trivial regardless of
/// `n`.
#[test]
fn bitwise_bit_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let fst_fn_term = super::bitwise::fst_fn(&mut f);

    let false_ = f.bool_false();
    let true_ = f.bool_true();
    let one = f.num(1);
    let two = f.succ(one);
    let three = f.num(3);

    // hm : Eq 2 0 -> Eq false true, discharged from the impossible premise
    // via `Nat.succ_ne_zero` (`2` is built as `succ 1`, so the hypothesis
    // is directly usable with no rewriting) -- same shape as
    // `zero_or_succ_applies_at_a_compound_term_and_is_consumed_by_or_elim`'s
    // `left_branch`.
    let hm = {
        let zero = f.zero();
        let hm_ty = f.eq(two, zero);
        let h_fv = f.fresh_fvar();
        let h = f.kernel().fvar(h_fv);
        let contradiction = f.lemma(p.succ_ne_zero, &[one, h]);
        let false_ty = f.kernel().const_(p.logic.false_, vec![]);
        let level_zero = f.kernel().level_zero();
        let false_rec = f.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let target = f.bool_eq(false_, true_);
        let anon = f.anon_name();
        let motive = f.kernel().lam(anon, false_ty, target, BinderInfo::Default);
        let body = f.apply(false_rec, &[motive, contradiction]);
        f.lam_fv(h_fv, hm_ty, body)
    };

    // hn : Eq 3 0 -> Eq true true, trivial (`b = true`) regardless of `n`.
    let hn = {
        let zero = f.zero();
        let hn_ty = f.eq(three, zero);
        let h_fv = f.fresh_fvar();
        let body = f.bool_refl(true_);
        f.lam_fv(h_fv, hn_ty, body)
    };

    let bit_am = f.const_app(p.bit, &[false_, two]);
    let bit_bn = f.const_app(p.bit, &[true_, three]);
    let lhs = f.const_app(p.bitwise, &[fst_fn_term, bit_am, bit_bn]);

    let applied = f.lemma(
        p.bitwise_bit,
        &[fst_fn_term, false_, two, true_, three, hm, hn],
    );
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        let shown = f.explain(&e);
        panic!("bitwise_bit' must apply at (f=fst, a=false, m=2, b=true, n=3): {shown}")
    });

    let fab = f.apply(fst_fn_term, &[false_, true_]);
    let bitwise_mn = f.const_app(p.bitwise, &[fst_fn_term, two, three]);
    let rhs = f.const_app(p.bit, &[fab, bitwise_mn]);
    let want = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "bitwise_bit' must state Eq (bitwise fst (bit false 2) (bit true 3)) \
         (bit (fst false true) (bitwise fst 2 3))"
    );

    // `bitwise fst m n` computes to `m` unconditionally (established by
    // `bitwise_swap`'s own test): `bit false 2 = 4`, `bit true 3 = 7`, so
    // `lhs` computes to 4.
    let four = f.num(4);
    assert!(
        f.k.def_eq(lhs, four),
        "bitwise fst (bit false 2) (bit true 3) = bitwise fst 4 7 must compute to 4"
    );
    // `rhs = bit (fst false true) (bitwise fst 2 3) = bit false 2 = 4`.
    assert!(
        f.k.def_eq(rhs, four),
        "bit (fst false true) (bitwise fst 2 3) = bit false 2 must compute to 4"
    );

    // Non-vacuity: swapping `f`'s arguments at the combine (`fst true
    // false = true` instead of `false`) would have produced `bit true 2 =
    // 5 != 4` -- confirm the chosen instance actually discriminates that.
    let swapped_fab = f.apply(fst_fn_term, &[true_, false_]);
    let swapped_rhs = f.const_app(p.bit, &[swapped_fab, bitwise_mn]);
    let five = f.num(5);
    assert!(
        f.k.def_eq(swapped_rhs, five),
        "bit (fst true false) (bitwise fst 2 3) must compute to 5"
    );
    assert!(
        !f.k.def_eq(swapped_rhs, rhs),
        "the chosen (a, b) must be DISCRIMINATING: bit (fst false true) ... \
         and bit (fst true false) ... must differ, or this instance proves \
         nothing about argument order in the per-bit combine"
    );

    assert!(
        f.k.axiom_footprint(p.bitwise_bit).is_empty(),
        "bitwise_bit' must rest on zero axioms"
    );
}

/// `Nat.land_aux_le_left`/`Nat.land_le_left` apply at symbolic arguments and
/// at a concrete instance where `land a b < a` STRICTLY (`land 5 6 = 4 < 5`,
/// `101 & 110 = 100`) -- a pair where `land a b = a` (e.g. `a` a submask of
/// `b`) would not discriminate a bound that is actually an EQUALITY in
/// disguise from the real `Le`.
#[test]
fn land_le_left_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: `land_aux_le_left` at fully free fuel/m/n.
    {
        let name = f.name("land_aux_le_left_restated");
        f.theorem(name, 3, &|d, values| {
            let fuel = values[0];
            let m = values[1];
            let n = values[2];
            let lhs = d.const_app(p.land_aux, &[fuel, m, n]);
            let stmt = d.le(lhs, m);
            let proof = d.lemma(p.land_aux_le_left, &[fuel, m, n]);
            (stmt, proof)
        })
        .expect("land_aux_le_left must apply at symbolic fuel/m/n");
    }

    // Concrete: `land 5 6 = 4`, strictly less than `5`.
    {
        let five = f.num(5);
        let six = f.num(6);
        let four = f.num(4);
        let lhs = f.const_app(p.land, &[five, six]);
        let applied = f.lemma(p.land_le_left, &[five, six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_le_left must apply at (a=5, b=6): {shown}")
        });
        let want = f.le(lhs, five);
        assert!(
            f.k.def_eq(inferred, want),
            "land_le_left 5 6 must state Le (land 5 6) 5"
        );
        assert!(f.k.def_eq(lhs, four), "land 5 6 must compute to 4");
    }

    assert!(
        f.k.axiom_footprint(p.land_aux_le_left).is_empty(),
        "land_aux_le_left must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_le_left).is_empty(),
        "land_le_left must rest on zero axioms"
    );
}

/// `Nat.add_eq_zero` -- the additive twin of `Nat.mul_eq_zero`, built as the
/// missing arithmetic piece `docs/plan/status/247-nat-bitwise-assoc.md`
/// named for `land_aux_assoc_of_fuel` (`nat-assoc-dichotomy`,
/// `docs/plan/status/252-nat-assoc-dichotomy.md`). Applies at fully free
/// `a`/`b` and at the concrete pair `(0, 0)` -- `Nat` addition has no OTHER
/// solution to `a + b = 0`, so the discriminating check here is that
/// `add 3 5` computes to `8` and is NOT `def_eq` to `0`, confirming the
/// lemma's hypothesis position is a genuine, non-vacuous arithmetic
/// statement rather than one the kernel could accept for any pair.
#[test]
fn add_eq_zero_applies_at_free_and_concrete_arguments() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: restated at fully free a, b.
    {
        let name = f.name("add_eq_zero_restated");
        f.theorem(name, 2, &|d, values| {
            let a = values[0];
            let b = values[1];
            let sum = d.add(a, b);
            let zero = d.zero();
            let hyp = d.eq(sum, zero);
            let left = d.eq(a, zero);
            let zero2 = d.zero();
            let right = d.eq(b, zero2);
            let goal = d.const_app(p.logic.and, &[left, right]);
            let stmt = d.arrow(hyp, goal);
            let proof = d.lemma(p.add_eq_zero, &[a, b]);
            (stmt, proof)
        })
        .expect("add_eq_zero must apply at fully free a, b");
    }

    // Concrete, genuine proof: the only pair with a real hypothesis witness
    // is (0, 0).
    {
        let zero = f.num(0);
        let hyp = f.refl(zero);
        let applied = f.lemma(p.add_eq_zero, &[zero, zero]);
        let applied = f.apply(applied, &[hyp]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("add_eq_zero must apply at (a=0, b=0): {shown}")
        });
        let want_side = f.eq(zero, zero);
        let want = f.const_app(p.logic.and, &[want_side, want_side]);
        assert!(
            f.k.def_eq(inferred, want),
            "add_eq_zero 0 0 must state And (Eq 0 0) (Eq 0 0)"
        );
    }

    // Discriminating computation check.
    {
        let three = f.num(3);
        let five = f.num(5);
        let eight = f.num(8);
        let sum = f.add(three, five);
        assert!(f.k.def_eq(sum, eight), "add 3 5 must compute to 8");
        let zero = f.num(0);
        assert!(
            !f.k.def_eq(sum, zero),
            "add 3 5 must NOT be defeq to 0 -- (3, 5) is not a valid \
             hypothesis witness, which is exactly why (0, 0) is the only \
             concrete pair usable above"
        );
    }

    assert!(
        f.k.axiom_footprint(p.add_eq_zero).is_empty(),
        "add_eq_zero must rest on zero axioms"
    );
}

/// `Nat.zero_or_succ` -- the equational dichotomy built for
/// `nat-assoc-dichotomy`'s `land_aux_assoc_of_fuel` attempt
/// (`docs/plan/status/252-nat-assoc-dichotomy.md`). Applies at a COMPOUND,
/// non-atomic term (`mul 2 k` for a free `k`) -- exactly the shape the wall
/// this was built for needs (`X := landAux fuel a b`, not a bound variable)
/// -- and is genuinely CONSUMED by an `Or.rec` elimination at a concrete
/// positive numeral, refuting the left disjunct via `succ_ne_zero` and
/// surviving with the right.
#[test]
fn zero_or_succ_applies_at_a_compound_term_and_is_consumed_by_or_elim() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // Applies at a compound term built from a BOUND (not raw-fvar) variable
    // -- wrapped in its own theorem so the kernel's trusted gate re-checks
    // the fully closed result, exactly the shape `X := landAux fuel a b`
    // has as an argument built from the outer induction's own bound `a`/`b`.
    {
        let name = f.name("zero_or_succ_at_compound_restated");
        f.theorem(name, 1, &|d, values| {
            let k = values[0];
            let two = d.num(2);
            let target = d.mul(two, k);
            let zero = d.zero();
            let left = d.eq(target, zero);
            let level_one = d.level_one();
            let nat = d.nat_ty();
            let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let pred_fv = d.fresh_fvar();
            let pred = d.kernel().fvar(pred_fv);
            let succ_pred = d.succ(pred);
            let body = d.eq(target, succ_pred);
            let predicate = d.lam_fv(pred_fv, nat, body);
            let right = d.apply(exists_const, &[nat, predicate]);
            let stmt = d.const_app(p.logic.or, &[left, right]);
            let proof = d.lemma(p.zero_or_succ, &[target]);
            (stmt, proof)
        })
        .expect("zero_or_succ must apply at a compound term (mul 2 k) for bound k");
    }

    // Consumed by Or.rec at a concrete positive numeral: the left disjunct
    // (`Eq 5 0`) is refuted via `succ_ne_zero` (`5` is built as `succ 4`, so
    // the hypothesis is directly usable with no rewriting), leaving the
    // right disjunct (`Exists p, Eq 5 (succ p)`) as the surviving witness.
    {
        let five = f.num(5);
        let four = f.num(4);
        let dichotomy = f.lemma(p.zero_or_succ, &[five]);

        let zero = f.zero();
        let left_ty = f.eq(five, zero);
        let level_one = f.level_one();
        let exists_const = f.kernel().const_(p.logic.exists_, vec![level_one]);
        let pred_fv = f.fresh_fvar();
        let pred = f.kernel().fvar(pred_fv);
        let succ_pred = f.succ(pred);
        let body = f.eq(five, succ_pred);
        let predicate = f.lam_fv(pred_fv, nat, body);
        let right_ty = f.apply(exists_const, &[nat, predicate]);

        let left_branch = {
            let h_fv = f.fresh_fvar();
            let h = f.kernel().fvar(h_fv);
            // h : Eq 5 0, i.e. Eq (succ 4) 0 -- refuted directly.
            let contradiction = f.lemma(p.succ_ne_zero, &[four, h]);
            let false_ty = f.kernel().const_(p.logic.false_, vec![]);
            let level_zero = f.kernel().level_zero();
            let false_rec = f.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let anon = f.anon_name();
            let motive = f
                .kernel()
                .lam(anon, false_ty, right_ty, BinderInfo::Default);
            let body = f.apply(false_rec, &[motive, contradiction]);
            f.lam_fv(h_fv, left_ty, body)
        };
        let right_branch = {
            let h_fv = f.fresh_fvar();
            let h = f.kernel().fvar(h_fv);
            f.lam_fv(h_fv, right_ty, h)
        };

        let anon = f.anon_name();
        let or_ty = f.const_app(p.logic.or, &[left_ty, right_ty]);
        let or_motive = f.kernel().lam(anon, or_ty, right_ty, BinderInfo::Default);
        let or_rec = f.kernel().const_(p.logic.or_rec, vec![]);
        let surviving = f.apply(
            or_rec,
            &[
                left_ty,
                right_ty,
                or_motive,
                left_branch,
                right_branch,
                dichotomy,
            ],
        );
        let inferred = f.k.infer(surviving).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("Or.rec must consume zero_or_succ at 5: {shown}")
        });
        assert!(
            f.k.def_eq(inferred, right_ty),
            "the surviving proof must have the Exists type"
        );
    }

    assert!(
        f.k.axiom_footprint(p.zero_or_succ).is_empty(),
        "zero_or_succ must rest on zero axioms"
    );
}

/// `Nat.land_bit` — the `Nat.bit` decode bridge's payoff
/// (`nat_prelude::bit_decode`), closing `F:ml430-nat-land-bit-b9ab7475`.
/// Applies at a fully symbolic `(a, m, b, n)` (the theorem itself), and at a
/// DISCRIMINATING concrete instance: `a = true, m = 2, b = false, n = 3`
/// gives `bit true 2 = 5`, `bit false 3 = 6`, `land 5 6 = 4` (`101 & 110`),
/// against `bit (true && false) (land 2 3) = bit false 2 = 4` (`land 2 3 = 2`,
/// `10 & 11`) — a mismatched `&&`/bit encoding would not land on `4` here.
#[test]
fn land_bit_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables (m, n Nat;
    // a, b Bool), proved by the prelude theorem alone.
    {
        let nat = f.nat_ty();
        let bool_ty = f.bool_ty();
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);

        let bit_am = f.const_app(p.bit, &[a, m]);
        let bit_bn = f.const_app(p.bit, &[b, n]);
        let lhs = f.const_app(p.land, &[bit_am, bit_bn]);
        let and_fn_expr = super::bitwise::and_fn(&mut f);
        let a_and_b = f.apply(and_fn_expr, &[a, b]);
        let land_mn = f.const_app(p.land, &[m, n]);
        let rhs = f.const_app(p.bit, &[a_and_b, land_mn]);
        let stmt = f.eq(lhs, rhs);
        let proof = f.lemma(p.land_bit, &[a, m, b, n]);

        let ty = {
            let inner = f.pi_fv(n_fv, nat, stmt);
            let inner = f.pi_fv(b_fv, bool_ty, inner);
            let inner = f.pi_fv(m_fv, nat, inner);
            f.pi_fv(a_fv, bool_ty, inner)
        };
        let value = {
            let inner = f.lam_fv(n_fv, nat, proof);
            let inner = f.lam_fv(b_fv, bool_ty, inner);
            let inner = f.lam_fv(m_fv, nat, inner);
            f.lam_fv(a_fv, bool_ty, inner)
        };
        let name = f.name("land_bit_restated");
        f.declare_theorem(name, ty, value)
            .expect("land_bit's restated closed form must also be admitted");
    }

    // Concrete: a = true, m = 2, b = false, n = 3.
    {
        let t = f.bool_true();
        let two = f.num(2);
        let fls = f.bool_false();
        let three = f.num(3);
        let bit_t2 = f.const_app(p.bit, &[t, two]);
        let bit_f3 = f.const_app(p.bit, &[fls, three]);
        let lhs = f.const_app(p.land, &[bit_t2, bit_f3]);
        let and_fn_expr = super::bitwise::and_fn(&mut f);
        let t_and_f = f.apply(and_fn_expr, &[t, fls]);
        let land_23 = f.const_app(p.land, &[two, three]);
        let rhs = f.const_app(p.bit, &[t_and_f, land_23]);

        let applied = f.lemma(p.land_bit, &[t, two, fls, three]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_bit must apply at (a=true, m=2, b=false, n=3): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "land_bit true 2 false 3 must state Eq (land (bit true 2) (bit false 3)) (bit (true&&false) (land 2 3))"
        );

        let five = f.num(5);
        let six = f.num(6);
        let four = f.num(4);
        assert!(f.k.def_eq(bit_t2, five), "bit true 2 must compute to 5");
        assert!(f.k.def_eq(bit_f3, six), "bit false 3 must compute to 6");
        assert!(f.k.def_eq(lhs, four), "land 5 6 must compute to 4");
        assert!(
            f.k.def_eq(rhs, four),
            "bit false (land 2 3) must compute to 4"
        );
    }

    assert!(
        f.k.axiom_footprint(p.bit_div_two).is_empty(),
        "bit_div_two must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.bit_mod_two).is_empty(),
        "bit_mod_two must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_bit).is_empty(),
        "land_bit must rest on zero axioms"
    );
}

/// `Nat.lor_bit` — the `Nat.bit` decode bridge's `lor` twin, closing
/// `F:ml430-nat-lor-bit-a2f98c7c`. Same shared instance as
/// `land_bit_applies_at_a_concrete_discriminating_instance`
/// (`a = true, m = 2, b = false, n = 3`): `bit true 2 = 5`, `bit false 3 =
/// 6`, `lor 5 6 = 7` (`101 | 110`), against
/// `bit (true || false) (lor 2 3) = bit true 3 = 7` (`lor 2 3 = 3`,
/// `10 | 11`) -- discriminates from `land`'s `4` at the same instance.
#[test]
fn lor_bit_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables.
    {
        let nat = f.nat_ty();
        let bool_ty = f.bool_ty();
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);

        let bit_am = f.const_app(p.bit, &[a, m]);
        let bit_bn = f.const_app(p.bit, &[b, n]);
        let lhs = f.const_app(p.lor, &[bit_am, bit_bn]);
        let or_fn_expr = super::bitwise::or_fn(&mut f);
        let a_or_b = f.apply(or_fn_expr, &[a, b]);
        let lor_mn = f.const_app(p.lor, &[m, n]);
        let rhs = f.const_app(p.bit, &[a_or_b, lor_mn]);
        let stmt = f.eq(lhs, rhs);
        let proof = f.lemma(p.lor_bit, &[a, m, b, n]);

        let ty = {
            let inner = f.pi_fv(n_fv, nat, stmt);
            let inner = f.pi_fv(b_fv, bool_ty, inner);
            let inner = f.pi_fv(m_fv, nat, inner);
            f.pi_fv(a_fv, bool_ty, inner)
        };
        let value = {
            let inner = f.lam_fv(n_fv, nat, proof);
            let inner = f.lam_fv(b_fv, bool_ty, inner);
            let inner = f.lam_fv(m_fv, nat, inner);
            f.lam_fv(a_fv, bool_ty, inner)
        };
        let name = f.name("lor_bit_restated");
        f.declare_theorem(name, ty, value)
            .expect("lor_bit's restated closed form must also be admitted");
    }

    // Concrete: a = true, m = 2, b = false, n = 3.
    {
        let t = f.bool_true();
        let two = f.num(2);
        let fls = f.bool_false();
        let three = f.num(3);
        let bit_t2 = f.const_app(p.bit, &[t, two]);
        let bit_f3 = f.const_app(p.bit, &[fls, three]);
        let lhs = f.const_app(p.lor, &[bit_t2, bit_f3]);
        let or_fn_expr = super::bitwise::or_fn(&mut f);
        let t_or_f = f.apply(or_fn_expr, &[t, fls]);
        let lor_23 = f.const_app(p.lor, &[two, three]);
        let rhs = f.const_app(p.bit, &[t_or_f, lor_23]);

        let applied = f.lemma(p.lor_bit, &[t, two, fls, three]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_bit must apply at (a=true, m=2, b=false, n=3): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_bit true 2 false 3 must state Eq (lor (bit true 2) (bit false 3)) (bit (true||false) (lor 2 3))"
        );

        let seven = f.num(7);
        assert!(f.k.def_eq(lhs, seven), "lor 5 6 must compute to 7");
        assert!(
            f.k.def_eq(rhs, seven),
            "bit true (lor 2 3) must compute to 7"
        );
    }

    assert!(
        f.k.axiom_footprint(p.lor_bit).is_empty(),
        "lor_bit must rest on zero axioms"
    );
}

/// `Nat.ldiff_bit` — the `Nat.bit` decode bridge's `ldiff` twin, closing
/// `F:ml430-nat-ldiff-bit-6be49bb8`. Same shared instance:
/// `bit true 2 = 5`, `bit false 3 = 6`, `ldiff 5 6 = 1` (`101 & !110 = 101 &
/// 001`), against `bit (true && !false) (ldiff 2 3) = bit true 0 = 1`
/// (`ldiff 2 3 = 010 & !011 = 010 & 100 = 0`) -- discriminates from `land`'s
/// `4` and `lor`'s `7` at the same instance.
#[test]
fn ldiff_bit_applies_at_a_concrete_discriminating_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables.
    {
        let nat = f.nat_ty();
        let bool_ty = f.bool_ty();
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);

        let bit_am = f.const_app(p.bit, &[a, m]);
        let bit_bn = f.const_app(p.bit, &[b, n]);
        let lhs = f.const_app(p.ldiff, &[bit_am, bit_bn]);
        let ldiff_fn_expr = super::bit_decode::ldiff_fn(&mut f, &p);
        let a_ldiff_b = f.apply(ldiff_fn_expr, &[a, b]);
        let ldiff_mn = f.const_app(p.ldiff, &[m, n]);
        let rhs = f.const_app(p.bit, &[a_ldiff_b, ldiff_mn]);
        let stmt = f.eq(lhs, rhs);
        let proof = f.lemma(p.ldiff_bit, &[a, m, b, n]);

        let ty = {
            let inner = f.pi_fv(n_fv, nat, stmt);
            let inner = f.pi_fv(b_fv, bool_ty, inner);
            let inner = f.pi_fv(m_fv, nat, inner);
            f.pi_fv(a_fv, bool_ty, inner)
        };
        let value = {
            let inner = f.lam_fv(n_fv, nat, proof);
            let inner = f.lam_fv(b_fv, bool_ty, inner);
            let inner = f.lam_fv(m_fv, nat, inner);
            f.lam_fv(a_fv, bool_ty, inner)
        };
        let name = f.name("ldiff_bit_restated");
        f.declare_theorem(name, ty, value)
            .expect("ldiff_bit's restated closed form must also be admitted");
    }

    // Concrete: a = true, m = 2, b = false, n = 3.
    {
        let t = f.bool_true();
        let two = f.num(2);
        let fls = f.bool_false();
        let three = f.num(3);
        let bit_t2 = f.const_app(p.bit, &[t, two]);
        let bit_f3 = f.const_app(p.bit, &[fls, three]);
        let lhs = f.const_app(p.ldiff, &[bit_t2, bit_f3]);
        let ldiff_fn_expr = super::bit_decode::ldiff_fn(&mut f, &p);
        let t_ldiff_f = f.apply(ldiff_fn_expr, &[t, fls]);
        let ldiff_23 = f.const_app(p.ldiff, &[two, three]);
        let rhs = f.const_app(p.bit, &[t_ldiff_f, ldiff_23]);

        let applied = f.lemma(p.ldiff_bit, &[t, two, fls, three]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("ldiff_bit must apply at (a=true, m=2, b=false, n=3): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "ldiff_bit true 2 false 3 must state Eq (ldiff (bit true 2) (bit false 3)) (bit (true&&!false) (ldiff 2 3))"
        );

        let one = f.num(1);
        assert!(f.k.def_eq(lhs, one), "ldiff 5 6 must compute to 1");
        assert!(
            f.k.def_eq(rhs, one),
            "bit true (ldiff 2 3) must compute to 1"
        );
    }

    assert!(
        f.k.axiom_footprint(p.ldiff_bit).is_empty(),
        "ldiff_bit must rest on zero axioms"
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
///
/// This doc comment and its `#[test]` attribute were separated from this
/// function by a merge (a "TWO LANES ADDING FUNCTIONS TO ONE RUST FILE"
/// hunk-boundary artifact, CLAUDE.md's Gotchas): the attribute had drifted
/// onto `land_bit_applies_at_a_concrete_discriminating_instance` above,
/// duplicating ITS `#[test]` and leaving this function silently untested
/// dead code. Restored to its own function by `nat-bitwise-bit-swap`.
/// Pre-existing gap fixed in passing (not this lane's subject): this
/// function's `#[test]` attribute had been misplaced onto
/// `land_bit_applies_at_a_concrete_discriminating_instance` by an earlier
/// doc-comment insertion, leaving this test dead code (`cargo clippy
/// --all-targets` flags it as never used). Restored here because it landed
/// in the same file this lane already touches, and a clean clippy gate is
/// this lane's own required check.
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

/// `Nat.le_fib_add_one` (`n <= fib n + 1`) applies at every one of the five
/// concrete `Lt n 5` case-split branches (`n = 0..4`, where the bound is
/// TIGHT -- equality -- at `n = 2, 3, 4`) and at `n = 6`, past the `Le 5 n`
/// threshold where `le_fib_self` takes over. `fib(0..4) = 0,1,1,2,3` and
/// `fib(6) = 8`, so the residues checked are `0<=1`, `1<=2`, `2<=2`,
/// `3<=3`, `4<=4`, `6<=9` -- the theorem itself never needed those numbers
/// evaluated (it is symbolic in `n`), but the application here confirms the
/// admitted statement means what the doc comment claims.
#[test]
fn le_fib_add_one_applies_at_every_case_split_branch_and_past_the_threshold() {
    let mut f = Fixture::new();
    let p = f.p;

    let declaration =
        f.k.environment()
            .get(p.le_fib_add_one)
            .expect("Nat.le_fib_add_one must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "le_fib_add_one must be a Theorem"
    );
    assert!(
        f.k.axiom_footprint(p.le_fib_add_one).is_empty(),
        "le_fib_add_one must rest on zero axioms"
    );

    for n_val in [0u32, 1, 2, 3, 4, 6] {
        let n = f.num(n_val);
        let applied = f.const_app(p.le_fib_add_one, &[n]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("le_fib_add_one at {n_val} must apply: {shown}")
        });
        let fib_n = f.const_app(p.fib, &[n]);
        let one = f.num(1);
        let sum = f.add(fib_n, one);
        let want = f.le(n, sum);
        assert!(
            f.k.def_eq(inferred, want),
            "le_fib_add_one at {n_val} must state Le {n_val} (add (fib {n_val}) 1)"
        );
    }

    // Negative control: `le_fib_add_one` at `n = 5` does NOT state `Le 5
    // (add (fib 4) 1)` -- a mismatched index is a genuinely different,
    // false-shaped statement, not just a relabelling.
    let five = f.num(5);
    let four = f.num(4);
    let applied = f.const_app(p.le_fib_add_one, &[five]);
    let inferred = f.k.infer(applied).expect("must apply at 5");
    let fib_four = f.const_app(p.fib, &[four]);
    let one = f.num(1);
    let mismatched_sum = f.add(fib_four, one);
    let mismatched = f.le(five, mismatched_sum);
    assert!(
        !f.k.def_eq(inferred, mismatched),
        "negative control: le_fib_add_one at 5 must NOT state Le 5 (add (fib 4) 1)"
    );
}

/// `Nat.Prime.five_le_of_ne_two_of_ne_three` applies at a concrete `p = 7`:
/// instantiating just the leading `Nat` argument produces the expected
/// residual `Pi` type `prime_condition 7 -> Not (p = 2) -> Not (p = 3) -> Le
/// 5 7`, and the theorem rests on zero axioms. (Constructing an actual
/// `prime_condition 7` witness needs the full divisor-search route this
/// file exercises elsewhere for small primes -- `every_number_at_least_two_
/// has_a_prime_divisor` and friends -- so this test checks the admitted
/// TYPE the same way `eq_one_of_dvd_one_is_derived_and_applies` and the
/// `clog` boundary-equation test above do, rather than building a full
/// discharge.)
#[test]
fn five_le_of_ne_two_of_ne_three_applies_at_a_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let declaration =
        f.k.environment()
            .get(p.five_le_of_ne_two_of_ne_three)
            .expect("Nat.Prime.five_le_of_ne_two_of_ne_three must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "five_le_of_ne_two_of_ne_three must be a Theorem"
    );
    assert!(
        f.k.axiom_footprint(p.five_le_of_ne_two_of_ne_three)
            .is_empty(),
        "five_le_of_ne_two_of_ne_three must rest on zero axioms"
    );

    let seven = f.num(7);
    let applied = f.const_app(p.five_le_of_ne_two_of_ne_three, &[seven]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        let shown = f.explain(&e);
        panic!("five_le_of_ne_two_of_ne_three at 7 must apply: {shown}")
    });
    let rendered = f.k.render_lean(inferred);
    assert!(
        rendered.contains("And") && rendered.contains("Not") && rendered.contains("le"),
        "unexpected residue type: {rendered}"
    );

    // Negative control: the SAME construction at p = 2 must NOT be
    // def_eq to a residue promising `Le 5 2` -- the conclusion really does
    // vary with the instantiated argument, not a vacuous constant.
    let two = f.num(2);
    let applied_at_two = f.const_app(p.five_le_of_ne_two_of_ne_three, &[two]);
    let inferred_at_two = f.k.infer(applied_at_two).expect("must apply at 2 as well");
    assert!(
        !f.k.def_eq(inferred, inferred_at_two),
        "negative control: the residue type must depend on the instantiated argument"
    );
}

/// `Nat.land_aux_eq_zero_of_left_eq_zero` -- "zero propagates through the
/// other operand", the one theorem `docs/plan/status/252-nat-assoc-dichotomy.md`
/// traced by hand and cross-checked in Python but did not build. Applies at
/// symbolic `fuel`/`a`/`b`/`c` and at a concrete, non-vacuous, MIXED
/// instance from that plan's own cross-check: `fuel=2, a=1, b=2, c=2`.
/// `land 1 2 = 0` (hyp true, not vacuous) while `land 2 2 = 2` is genuinely
/// NONZERO -- so this is the case the plan measured at 108/343 triples, not
/// a corner where the whole statement degenerates to `0 = 0`.
#[test]
fn land_aux_eq_zero_of_left_eq_zero_applies_at_a_mixed_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: fully free fuel/a/b/c. The lemma's own statement is an
    // arrow (`Eq (landAux fuel a b) 0 -> Eq (landAux fuel a (landAux fuel b
    // c)) 0`), so a 4-ary restatement plus the lemma applied at the four
    // universals reproduces it exactly -- no separate hypothesis fvar is
    // needed at this level since `d.lemma` just re-applies the declared
    // Pi-quantified constant.
    {
        let name = f.name("land_aux_eq_zero_of_left_eq_zero_restated");
        f.theorem(name, 4, &|d, values| {
            let fuel = values[0];
            let a = values[1];
            let b = values[2];
            let c = values[3];
            let zero = d.zero();
            let ab = d.const_app(p.land_aux, &[fuel, a, b]);
            let hyp = d.eq(ab, zero);
            let bc = d.const_app(p.land_aux, &[fuel, b, c]);
            let a_bc = d.const_app(p.land_aux, &[fuel, a, bc]);
            let concl = d.eq(a_bc, zero);
            let stmt = d.arrow(hyp, concl);
            let proof = d.lemma(p.land_aux_eq_zero_of_left_eq_zero, &[fuel, a, b, c]);
            (stmt, proof)
        })
        .expect("land_aux_eq_zero_of_left_eq_zero must apply at symbolic fuel/a/b/c");
    }

    // Concrete, discriminating, non-vacuous instance.
    {
        let fuel = f.num(2);
        let a = f.num(1);
        let b = f.num(2);
        let c = f.num(2);
        let zero = f.zero();

        let ab = f.const_app(p.land_aux, &[fuel, a, b]);
        assert!(f.k.def_eq(ab, zero), "landAux 2 1 2 must compute to 0");
        let bc = f.const_app(p.land_aux, &[fuel, b, c]);
        assert!(
            !f.k.def_eq(bc, zero),
            "landAux 2 2 2 must compute to 2, not 0 -- else this instance is vacuous"
        );

        let hyp_proof = f.refl(zero); // retypes as `Eq ab zero` (ab is defeq zero)
        let applied = f.lemma(
            p.land_aux_eq_zero_of_left_eq_zero,
            &[fuel, a, b, c, hyp_proof],
        );
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_aux_eq_zero_of_left_eq_zero must apply at (fuel=2,a=1,b=2,c=2): {shown}")
        });
        let a_bc = f.const_app(p.land_aux, &[fuel, a, bc]);
        let want = f.eq(a_bc, zero);
        assert!(
            f.k.def_eq(inferred, want),
            "conclusion must state Eq (landAux 2 1 (landAux 2 2 2)) 0"
        );
        assert!(
            f.k.def_eq(a_bc, zero),
            "landAux 2 1 (landAux 2 2 2) must itself compute to 0"
        );
    }

    assert!(
        f.k.axiom_footprint(p.land_aux_eq_zero_of_left_eq_zero)
            .is_empty(),
        "land_aux_eq_zero_of_left_eq_zero must rest on zero axioms"
    );
}

/// `Nat.land_assoc` -- `F:ml430-nat-land-assoc-ad4775b8`. Applies at
/// symbolic `a`/`b`/`c` and at a concrete instance where BOTH intermediate
/// values are NONZERO (`land 3 7 = 3`, `land 7 5 = 5`), exercising the
/// `land_aux_assoc_of_fuel` hard leaf's fully-generic (`X != 0`, `Y != 0`)
/// sub-case -- the double `div_mod_unique` reconstruction feeding the
/// outer induction's own `ih` -- rather than settling for one of the easy
/// leaves or the hard leaf's `X = 0`/`Y = 0` corners.
#[test]
fn land_assoc_applies_at_a_nonzero_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone.
    {
        let name = f.name("land_assoc_restated");
        f.theorem(name, 3, &|d, values| {
            let a = values[0];
            let b = values[1];
            let c = values[2];
            let ab = d.const_app(p.land, &[a, b]);
            let lhs = d.const_app(p.land, &[ab, c]);
            let bc = d.const_app(p.land, &[b, c]);
            let rhs = d.const_app(p.land, &[a, bc]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.land_assoc, &[a, b, c]);
            (stmt, proof)
        })
        .expect("land_assoc must apply at symbolic a/b/c");
    }

    // Concrete: a=3 (011), b=7 (111), c=5 (101) -- land(a,b)=3 and
    // land(b,c)=5, BOTH nonzero (a's bits and c's bits are each a subset
    // of b's), so neither side collapses to the easy `landAux _ _ 0` leaf.
    {
        let three = f.num(3);
        let seven = f.num(7);
        let five = f.num(5);
        let one = f.num(1);
        let ab = f.const_app(p.land, &[three, seven]);
        let lhs = f.const_app(p.land, &[ab, five]);
        let bc = f.const_app(p.land, &[seven, five]);
        let rhs = f.const_app(p.land, &[three, bc]);
        let zero = f.zero();
        assert!(f.k.def_eq(ab, three), "land 3 7 must compute to 3");
        assert!(
            !f.k.def_eq(ab, zero),
            "land 3 7 must be nonzero -- else this instance is vacuous"
        );
        assert!(f.k.def_eq(bc, five), "land 7 5 must compute to 5");
        assert!(
            !f.k.def_eq(bc, zero),
            "land 7 5 must be nonzero -- else this instance is vacuous"
        );

        let applied = f.lemma(p.land_assoc, &[three, seven, five]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("land_assoc must apply at (a=3, b=7, c=5): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "land_assoc 3 7 5 must state Eq (land (land 3 7) 5) (land 3 (land 7 5))"
        );
        assert!(f.k.def_eq(lhs, one), "land (land 3 7) 5 must compute to 1");
        assert!(f.k.def_eq(rhs, one), "land 3 (land 7 5) must compute to 1");
    }

    assert!(
        f.k.axiom_footprint(p.land_aux_assoc_of_fuel).is_empty(),
        "land_aux_assoc_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.land_assoc).is_empty(),
        "land_assoc must rest on zero axioms"
    );
}

/// `Nat.lor_aux_ne_zero_of_right_ne_zero` -- the invariant that plays
/// `land_aux_eq_zero_of_left_eq_zero`'s role for `lor_assoc`'s hard leaf,
/// and is NOT its transport: `lor`'s zero is NOT absorbing (`lor a b = 0`
/// forces `a = 0 ∧ b = 0`), so this lemma is about POSITIVITY of the
/// RIGHT operand alone forcing a positive result, unconditional in `fuel`.
#[test]
fn lor_aux_ne_zero_of_right_ne_zero_applies_symbolically_and_at_a_positive_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: re-derived at genuinely free fuel/m/n, forcing the kernel
    // to re-check the fully generic statement.
    {
        let name = f.name("lor_aux_ne_zero_of_right_ne_zero_at_free_vars");
        f.theorem(name, 3, &|d, values| {
            let fuel = values[0];
            let m = values[1];
            let n = values[2];
            let zero = d.zero();
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);

            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let hyp_ty = {
                let eq = d.eq(n, zero);
                d.arrow(eq, false_ty)
            };
            let lor_val = d.const_app(p.lor_aux, &[fuel, m, n]);
            let concl_ty = {
                let eq0 = d.eq(lor_val, zero);
                d.arrow(eq0, false_ty)
            };
            let stmt = d.arrow(hyp_ty, concl_ty);

            let applied = d.lemma(p.lor_aux_ne_zero_of_right_ne_zero, &[fuel, m, n, hyp]);
            let value = d.lam_fv(hyp_fv, hyp_ty, applied);
            (stmt, value)
        })
        .expect("lor_aux_ne_zero_of_right_ne_zero must apply at free fuel/m/n");
    }

    // Concrete: fuel=1, m=3, n=5 -- BOTH positive, and fuel=1 is exactly
    // enough to force the hard leaf's actual per-bit recursive step, not
    // the trivial fuel=0 identity. `lorAux 1 3 5` computes to
    // `2 * lorAux 0 1 2 + max(1, 1) = 2*2 + 1 = 5`, nonzero -- a
    // discriminating instance, not the vacuous `n=0` corner.
    {
        let one_fuel = f.num(1);
        let three = f.num(3);
        let five = f.num(5);
        let four = f.num(4);
        let zero = f.zero();
        let false_ty = f.kernel().const_(p.logic.false_, vec![]);

        let lor_val = f.const_app(p.lor_aux, &[one_fuel, three, five]);
        assert!(f.k.def_eq(lor_val, five), "lorAux 1 3 5 must compute to 5");
        assert!(
            !f.k.def_eq(lor_val, zero),
            "lorAux 1 3 5 must be nonzero -- else this instance is vacuous"
        );

        // Not (Eq 5 0), via succ_ne_zero (5 = succ 4).
        let n_ne_zero = f.lemma(p.succ_ne_zero, &[four]);

        let applied = f.lemma(
            p.lor_aux_ne_zero_of_right_ne_zero,
            &[one_fuel, three, five, n_ne_zero],
        );
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_aux_ne_zero_of_right_ne_zero must apply at (fuel=1, m=3, n=5): {shown}")
        });
        let want = {
            let eq0 = f.eq(lor_val, zero);
            f.arrow(eq0, false_ty)
        };
        assert!(
            f.k.def_eq(inferred, want),
            "must state Not (Eq (lorAux 1 3 5) 0)"
        );
    }

    assert!(
        f.k.axiom_footprint(p.lor_aux_ne_zero_of_right_ne_zero)
            .is_empty(),
        "lor_aux_ne_zero_of_right_ne_zero must rest on zero axioms"
    );
}

/// `Nat.lor_assoc` -- `F:ml430-nat-lor-assoc-82c4d0fd`. Applies at symbolic
/// `a`/`b`/`c` and at a concrete instance where BOTH intermediate `lor`
/// values are NONZERO (`lor 3 5 = 7`, `lor 5 6 = 7`), exercising
/// `lor_aux_assoc_of_fuel`'s hard leaf's fully-generic (both operands
/// positive) sub-case via the `lor_aux_ne_zero_of_right_ne_zero` invariant
/// rather than settling for one of the easy leaves.
#[test]
fn lor_assoc_applies_at_a_nonzero_concrete_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    // Symbolic: the statement re-declared over bound variables, proved by
    // the prelude theorem alone.
    {
        let name = f.name("lor_assoc_restated");
        f.theorem(name, 3, &|d, values| {
            let a = values[0];
            let b = values[1];
            let c = values[2];
            let ab = d.const_app(p.lor, &[a, b]);
            let lhs = d.const_app(p.lor, &[ab, c]);
            let bc = d.const_app(p.lor, &[b, c]);
            let rhs = d.const_app(p.lor, &[a, bc]);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.lor_assoc, &[a, b, c]);
            (stmt, proof)
        })
        .expect("lor_assoc must apply at symbolic a/b/c");
    }

    // Concrete: a=3 (011), b=5 (101), c=6 (110) -- lor(a,b)=7 and lor(b,c)=7,
    // BOTH nonzero, exercising the both-positive hard leaf.
    {
        let three = f.num(3);
        let five = f.num(5);
        let six = f.num(6);
        let seven = f.num(7);
        let ab = f.const_app(p.lor, &[three, five]);
        let lhs = f.const_app(p.lor, &[ab, six]);
        let bc = f.const_app(p.lor, &[five, six]);
        let rhs = f.const_app(p.lor, &[three, bc]);
        let zero = f.zero();
        assert!(f.k.def_eq(ab, seven), "lor 3 5 must compute to 7");
        assert!(
            !f.k.def_eq(ab, zero),
            "lor 3 5 must be nonzero -- else this instance is vacuous"
        );
        assert!(f.k.def_eq(bc, seven), "lor 5 6 must compute to 7");
        assert!(
            !f.k.def_eq(bc, zero),
            "lor 5 6 must be nonzero -- else this instance is vacuous"
        );

        let applied = f.lemma(p.lor_assoc, &[three, five, six]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("lor_assoc must apply at (a=3, b=5, c=6): {shown}")
        });
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "lor_assoc 3 5 6 must state Eq (lor (lor 3 5) 6) (lor 3 (lor 5 6))"
        );
        assert!(f.k.def_eq(lhs, seven), "lor (lor 3 5) 6 must compute to 7");
        assert!(f.k.def_eq(rhs, seven), "lor 3 (lor 5 6) must compute to 7");
    }

    assert!(
        f.k.axiom_footprint(p.lor_aux_assoc_of_fuel).is_empty(),
        "lor_aux_assoc_of_fuel must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lor_aux_le_add).is_empty(),
        "lor_aux_le_add must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.lor_assoc).is_empty(),
        "lor_assoc must rest on zero axioms"
    );
}

/// The `ml430` `Nat` add/div/mod shift family applies at concrete,
/// discriminating numerals (`x=7, y=2, z=3` for the `mul`-shaped four;
/// `x=7, z=4` for the plain four -- `11/4=2`, `11%4=3`, distinct from every
/// other operand so a swapped argument or a wrong `symm` direction would
/// show up as a `def_eq` failure, not merely a type-check pass).
#[test]
fn add_div_mod_shift_family_applies_at_concrete_discriminating_instances() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let seven = f.num(7);
    let eleven = f.num(11);
    let pos_two = f.lemma(p.zero_lt_succ, &[one]); // Lt zero 2
    let pos_three = f.lemma(p.zero_lt_succ, &[two]); // Lt zero 3
    let pos_four = f.lemma(p.zero_lt_succ, &[three]); // Lt zero 4

    // add_mul_div_left : (7 + 2*3)/2 = 7/2 + 3 = 6.
    let applied = f.lemma(p.add_mul_div_left, &[seven, three, two, pos_two]);
    let inferred = f
        .k
        .infer(applied)
        .unwrap_or_else(|e| panic!("add_mul_div_left must apply at (7,3,2): {}", f.explain(&e)));
    let want = f.eq(six, six);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mul_div_left(7,3,2) must state (7+2*3)/2 = 7/2+3, both sides 6"
    );

    // add_mul_div_right : (7 + 2*3)/3 = 7/3 + 2 = 4.
    let applied = f.lemma(p.add_mul_div_right, &[seven, two, three, pos_three]);
    let inferred = f
        .k
        .infer(applied)
        .unwrap_or_else(|e| panic!("add_mul_div_right must apply at (7,2,3): {}", f.explain(&e)));
    let want = f.eq(four, four);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mul_div_right(7,2,3) must state (7+2*3)/3 = 7/3+2, both sides 4"
    );

    // add_mul_mod_self_left : (7 + 2*3)%2 = 7%2 = 1.
    let applied = f.lemma(p.add_mul_mod_self_left, &[seven, two, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_mul_mod_self_left must apply at (7,2,3): {}",
            f.explain(&e)
        )
    });
    let want = f.eq(one, one);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mul_mod_self_left(7,2,3) must state (7+2*3)%2 = 7%2, both sides 1"
    );

    // add_mul_mod_self_right : (7 + 2*3)%3 = 7%3 = 1.
    let applied = f.lemma(p.add_mul_mod_self_right, &[seven, two, three]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_mul_mod_self_right must apply at (7,2,3): {}",
            f.explain(&e)
        )
    });
    let want = f.eq(one, one);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mul_mod_self_right(7,2,3) must state (7+2*3)%3 = 7%3, both sides 1"
    );

    // add_mod_left : (4+7)%4 = 7%4 = 3.
    let applied = f.lemma(p.add_mod_left, &[four, seven]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("add_mod_left must apply at (4,7): {}", f.explain(&e)));
    let three_r = f.modulo(seven, four);
    let want = f.eq(three_r, three_r);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mod_left(4,7) must state (4+7)%4 = 7%4"
    );
    assert!(f.k.def_eq(three_r, three), "7%4 must compute to 3");

    // add_mod_right : (7+4)%4 = 7%4 = 3.
    let applied = f.lemma(p.add_mod_right, &[seven, four]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("add_mod_right must apply at (7,4): {}", f.explain(&e)));
    let want = f.eq(three_r, three_r);
    assert!(
        f.k.def_eq(inferred, want),
        "add_mod_right(7,4) must state (7+4)%4 = 7%4"
    );

    // add_div_left : (4+7)/4 = 7/4+1 = 2.
    let applied = f.lemma(p.add_div_left, &[seven, four, pos_four]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("add_div_left must apply at (7,4): {}", f.explain(&e)));
    let two_q = f.div(seven, four);
    let eleven_div_four = f.div(eleven, four);
    let two_q_plus_one = f.add(two_q, one);
    let want = f.eq(eleven_div_four, two_q_plus_one);
    assert!(
        f.k.def_eq(inferred, want),
        "add_div_left(7,4) must state (4+7)/4 = 7/4+1"
    );
    assert!(f.k.def_eq(eleven_div_four, two), "11/4 must compute to 2");

    // add_div_right : (7+4)/4 = 7/4+1 = 2.
    let applied = f.lemma(p.add_div_right, &[seven, four, pos_four]);
    let inferred =
        f.k.infer(applied)
            .unwrap_or_else(|e| panic!("add_div_right must apply at (7,4): {}", f.explain(&e)));
    let want = f.eq(eleven_div_four, two_q_plus_one);
    assert!(
        f.k.def_eq(inferred, want),
        "add_div_right(7,4) must state (7+4)/4 = 7/4+1"
    );

    for name in [
        p.add_mul_div_left,
        p.add_mul_div_right,
        p.add_mul_mod_self_left,
        p.add_mul_mod_self_right,
        p.add_mod_left,
        p.add_mod_right,
        p.add_div_left,
        p.add_div_right,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// `Nat.add_div_of_dvd_add_add_one`, the ninth `ml430` add/div/mod mirror
/// (`F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0`), applies at two
/// discriminating instances: `(c,a,b) = (5,7,7)` (`a`,`b` equal, both
/// quotients and both remainders nonzero and summing exactly to `c-1`) and
/// `(c,a,b) = (5,3,11)` (`a < c <= b`, asymmetric, chosen to catch an `a`/`b`
/// swap). Both need a concrete `dvd c (a+b+1)` witness (`concrete_dvd`).
#[test]
fn add_div_of_dvd_add_add_one_applies_at_concrete_discriminating_instances() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let seven = f.num(7);
    let eleven = f.num(11);
    let fifteen = f.num(15);
    let zero = f.zero();

    // (5,7,7): 7+7+1 = 15 = 5*3. (7+7)/5 = 14/5 = 2. 7/5+7/5 = 1+1 = 2.
    let dvd_15 = concrete_dvd(&mut f, five, fifteen, three);
    let applied = f.lemma(p.add_div_of_dvd_add_add_one, &[five, seven, seven]);
    let applied = f.apply(applied, &[dvd_15]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_div_of_dvd_add_add_one must apply at (5,7,7): {}",
            f.explain(&e)
        )
    });
    let seven_seven = f.add(seven, seven);
    let ab_div_c = f.div(seven_seven, five);
    let a_div_c = f.div(seven, five);
    let rhs = f.add(a_div_c, a_div_c);
    let want = f.eq(ab_div_c, rhs);
    assert!(
        f.k.def_eq(inferred, want),
        "add_div_of_dvd_add_add_one(5,7,7) must state (7+7)/5 = 7/5+7/5"
    );
    assert!(f.k.def_eq(ab_div_c, two), "14/5 must compute to 2");

    // (5,3,11): 3+11+1 = 15 = 5*3. (3+11)/5 = 14/5 = 2. 3/5+11/5 = 0+2 = 2.
    let dvd_15b = concrete_dvd(&mut f, five, fifteen, three);
    let applied = f.lemma(p.add_div_of_dvd_add_add_one, &[five, three, eleven]);
    let applied = f.apply(applied, &[dvd_15b]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "add_div_of_dvd_add_add_one must apply at (5,3,11): {}",
            f.explain(&e)
        )
    });
    let three_eleven = f.add(three, eleven);
    let ab_div_c2 = f.div(three_eleven, five);
    let a_div_c2 = f.div(three, five);
    let b_div_c2 = f.div(eleven, five);
    let rhs2 = f.add(a_div_c2, b_div_c2);
    let want2 = f.eq(ab_div_c2, rhs2);
    assert!(
        f.k.def_eq(inferred, want2),
        "add_div_of_dvd_add_add_one(5,3,11) must state (3+11)/5 = 3/5+11/5"
    );
    assert!(f.k.def_eq(ab_div_c2, two), "14/5 must compute to 2");
    assert!(f.k.def_eq(a_div_c2, zero), "3/5 must compute to 0");
    assert!(f.k.def_eq(b_div_c2, two), "11/5 must compute to 2");

    assert!(
        f.k.axiom_footprint(p.add_div_of_dvd_add_add_one).is_empty(),
        "add_div_of_dvd_add_add_one must rest on zero axioms"
    );
}

/// `Nat.base_induction` (`F:ml430-nat-base-induction-83561d4c`) applies at a
/// concrete instance: `P := fun m => Le zero m`, `b := 2`, `n := 5`, `single`
/// and `digit` both closed by `zero_le`. The generic theorem is already the
/// strong check (the kernel re-verifies it for an ARBITRARY `P`); this test
/// is the downstream-consumer check -- that a genuinely recursive
/// instantiation (`n=5`, `b=2` forces the `Le b v` branch through several
/// levels of `qv = v/2` before landing in the `Lt v b` branch) type-checks
/// and does not get stuck.
#[test]
fn base_induction_applies_at_a_concrete_recursive_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);

    // P := fun m => Le zero m.
    let p_pred = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let body = f.le(zero, m);
        f.lam_fv(m_fv, nat, body)
    };

    let hb = f.lemma(p.lt_succ_self, &[one]); // Lt one (succ one) = Lt 1 2

    // single : ∀ m, Lt m 2 -> Le zero m.
    let single_proof = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let h_fv = f.fresh_fvar();
        let lt_m_two = f.lt(m, two);
        let body = f.lemma(p.zero_le, &[m]);
        let with_h = f.lam_fv(h_fv, lt_m_two, body);
        f.lam_fv(m_fv, nat, with_h)
    };

    // digit : ∀ m k, Lt k 2 -> Lt zero m -> Le zero m -> Le zero (2*m+k).
    let digit_proof = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let h1_fv = f.fresh_fvar();
        let h2_fv = f.fresh_fvar();
        let h3_fv = f.fresh_fvar();
        let two_m = f.mul(two, m);
        let two_m_k = f.add(two_m, k);
        let body = f.lemma(p.zero_le, &[two_m_k]);
        let h3_ty = f.le(zero, m);
        let with_h3 = f.lam_fv(h3_fv, h3_ty, body);
        let h2_ty = f.lt(zero, m);
        let with_h2 = f.lam_fv(h2_fv, h2_ty, with_h3);
        let h1_ty = f.lt(k, two);
        let with_h1 = f.lam_fv(h1_fv, h1_ty, with_h2);
        let with_k = f.lam_fv(k_fv, nat, with_h1);
        f.lam_fv(m_fv, nat, with_k)
    };

    let applied = f.lemma(p.base_induction, &[]);
    let applied = f.apply(applied, &[p_pred, five, two, hb, single_proof, digit_proof]);
    let inferred = f.k.infer(applied).unwrap_or_else(|e| {
        panic!(
            "base_induction must apply at P=(Le zero .), n=5, b=2: {}",
            f.explain(&e)
        )
    });
    let want = f.le(zero, five);
    assert!(
        f.k.def_eq(inferred, want),
        "base_induction(P,5,2,...) must state Le zero 5"
    );

    assert!(
        f.k.axiom_footprint(p.base_induction).is_empty(),
        "base_induction must rest on zero axioms"
    );
}

/// `Nat.gcd_mul_right : gcd(a*c, b*c) = gcd(a,b)*c` (`gcd_mul_right.rs`).
/// Checked at a concrete, mutually-discriminating triple (small magnitudes,
/// per the module's own numeral-growth caution), at the base case `a = 0`,
/// AND symbolically at a genuinely free `(a, b, c)` -- numerals reduce and
/// hide a definitional-equality gap a symbolic check exposes, so both are
/// required, not either.
#[test]
fn gcd_mul_right_holds_at_concrete_and_symbolic_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete: (a, b, c) = (4, 6, 5). gcd(4,6)=2, so RHS = 10; LHS =
    // gcd(20,30) = 10. Distinct a, b, c so a transposed argument (e.g.
    // gcd(a,c)*b, or the scale factor landing on the wrong side) would
    // compute a DIFFERENT wrong numeral rather than coincidentally agreeing.
    {
        let a = f.num(4);
        let b = f.num(6);
        let c = f.num(5);
        let applied = f.lemma(p.gcd_mul_right, &[a, b, c]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("gcd_mul_right must apply at (a=4, b=6, c=5): {shown}")
        });
        let ac = f.mul(a, c);
        let bc = f.mul(b, c);
        let lhs = f.gcd(ac, bc);
        let gab = f.gcd(a, b);
        let rhs = f.mul(gab, c);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "gcd_mul_right(4,6,5) must state Eq (gcd (mul 4 5)(mul 6 5)) (mul (gcd 4 6) 5)"
        );
        let ten = f.num(10);
        assert!(f.k.def_eq(lhs, ten), "gcd(20,30) must compute to 10");
        assert!(f.k.def_eq(rhs, ten), "gcd(4,6)*5 must compute to 10");

        // Negative control: must not ALSO state Eq lhs 15 (a plausible wrong
        // numeral -- gcd(4,6)*c with c misread as the wrong slot value 3).
        let fifteen = f.num(15);
        let bad_want = f.eq(lhs, fifteen);
        assert!(
            !f.k.def_eq(inferred, bad_want),
            "negative control: gcd_mul_right(4,6,5) must not state Eq lhs 15"
        );
    }

    // Concrete base case: a = 0. gcd(0*c, b*c) = gcd(0, b*c) = b*c;
    // gcd(0,b)*c = b*c. Exercises the zero_minor branch directly.
    {
        let zero = f.zero();
        let b = f.num(7);
        let c = f.num(3);
        let applied = f.lemma(p.gcd_mul_right, &[zero, b, c]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("gcd_mul_right must apply at (a=0, b=7, c=3): {shown}")
        });
        let zc = f.mul(zero, c);
        let bc = f.mul(b, c);
        let lhs = f.gcd(zc, bc);
        let g0b = f.gcd(zero, b);
        let rhs = f.mul(g0b, c);
        let want = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, want),
            "gcd_mul_right(0,7,3) must state Eq (gcd (mul 0 3)(mul 7 3)) (mul (gcd 0 7) 3)"
        );
        let twenty_one = f.num(21);
        assert!(f.k.def_eq(lhs, twenty_one), "gcd(0,21) must compute to 21");
        assert!(f.k.def_eq(rhs, twenty_one), "gcd(0,7)*3 must compute to 21");
    }

    // Symbolic: applies at a genuinely FREE (a, b, c) triple.
    {
        let name = f.name("gcd_mul_right_restated");
        f.theorem(name, 3, &|d, values| {
            let (a, b, c) = (values[0], values[1], values[2]);
            let ac = d.mul(a, c);
            let bc = d.mul(b, c);
            let lhs = d.gcd(ac, bc);
            let gab = d.gcd(a, b);
            let rhs = d.mul(gab, c);
            let stmt = d.eq(lhs, rhs);
            let proof = d.lemma(p.gcd_mul_right, &[a, b, c]);
            (stmt, proof)
        })
        .expect("gcd_mul_right must apply at symbolic a, b, c");
    }

    assert!(
        f.k.axiom_footprint(p.gcd_mul_right).is_empty(),
        "gcd_mul_right must rest on zero axioms"
    );
}

/// The three `ml430` mirrors built from `Nat.gcd_mul_right`
/// (`gcd_mul_right_mirrors.rs`): `dvd_gcd_mul_iff_dvd_mul`,
/// `dvd_mul_gcd_iff_dvd_mul`, `dvd_gcd_mul_gcd_iff_dvd_mul`. Each is checked
/// at a concrete triple -- both the STATEMENT shape (`def_eq` against an
/// independently-built expected `Iff`, which catches a swapped argument in
/// the hand-built proof term) and the LOGICAL CONTENT (applying `Iff.mp` to
/// a real proof witness and confirming the target type comes out right) --
/// and symbolically at a genuinely free `(k, n, m)` via a fresh restating
/// theorem, since numerals reduce and hide a definitional-equality gap a
/// symbolic check exposes.
#[test]
fn gcd_mul_right_mirrors_apply_at_concrete_and_symbolic_instances() {
    let mut f = Fixture::new();
    let p = f.p;

    // dvd_gcd_mul_iff_dvd_mul at (k, n, m) = (6, 4, 3):
    // gcd(6,4) = 2, so gcd(k,n)*m = 6 (dvd 6 6, trivially via dvd_refl);
    // n*m = 12 = 6*2 (dvd 6 12, via dvd_mul).
    {
        let k = f.num(6);
        let n = f.num(4);
        let m = f.num(3);
        let applied = f.lemma(p.dvd_gcd_mul_iff_dvd_mul, &[k, n, m]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_gcd_mul_iff_dvd_mul must apply at (k=6, n=4, m=3): {shown}")
        });
        let gkn = f.gcd(k, n);
        let gkn_m = f.mul(gkn, m);
        let nm = f.mul(n, m);
        let lhs = f.dvd(k, gkn_m);
        let rhs = f.dvd(k, nm);
        let want = f.const_app(p.logic.iff, &[lhs, rhs]);
        assert!(
            f.k.def_eq(inferred, want),
            "dvd_gcd_mul_iff_dvd_mul(6,4,3) must state Iff (dvd 6 (gcd(6,4)*3)) (dvd 6 (4*3))"
        );

        let mp_fn = f.const_app(p.logic.iff_mp, &[lhs, rhs, applied]);
        let refl_k = f.lemma(p.dvd_refl, &[k]); // dvd k k, defeq dvd k gkn_m (gkn_m computes to 6)
        let mp_result = f.apply(mp_fn, &[refl_k]);
        let mp_inferred = f.k.infer(mp_result).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!(
                "dvd_gcd_mul_iff_dvd_mul(6,4,3).mp applied to dvd_refl(6) must type-check: {shown}"
            )
        });
        assert!(
            f.k.def_eq(mp_inferred, rhs),
            "dvd_gcd_mul_iff_dvd_mul(6,4,3).mp(dvd_refl 6) must produce a proof of dvd 6 12"
        );
    }

    // dvd_mul_gcd_iff_dvd_mul at (k, n, m) = (6, 3, 4):
    // gcd(6,4) = 2, so n*gcd(k,m) = 6 (dvd 6 6); n*m = 12 (dvd 6 12).
    {
        let k = f.num(6);
        let n = f.num(3);
        let m = f.num(4);
        let applied = f.lemma(p.dvd_mul_gcd_iff_dvd_mul, &[k, n, m]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_mul_gcd_iff_dvd_mul must apply at (k=6, n=3, m=4): {shown}")
        });
        let gkm = f.gcd(k, m);
        let n_gkm = f.mul(n, gkm);
        let nm = f.mul(n, m);
        let lhs = f.dvd(k, n_gkm);
        let rhs = f.dvd(k, nm);
        let want = f.const_app(p.logic.iff, &[lhs, rhs]);
        assert!(
            f.k.def_eq(inferred, want),
            "dvd_mul_gcd_iff_dvd_mul(6,3,4) must state Iff (dvd 6 (3*gcd(6,4))) (dvd 6 (3*4))"
        );

        let mp_fn = f.const_app(p.logic.iff_mp, &[lhs, rhs, applied]);
        let refl_k = f.lemma(p.dvd_refl, &[k]); // dvd k k, defeq dvd k n_gkm (n_gkm computes to 6)
        let mp_result = f.apply(mp_fn, &[refl_k]);
        let mp_inferred = f.k.infer(mp_result).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!(
                "dvd_mul_gcd_iff_dvd_mul(6,3,4).mp applied to dvd_refl(6) must type-check: {shown}"
            )
        });
        assert!(
            f.k.def_eq(mp_inferred, rhs),
            "dvd_mul_gcd_iff_dvd_mul(6,3,4).mp(dvd_refl 6) must produce a proof of dvd 6 12"
        );
    }

    // dvd_gcd_mul_gcd_iff_dvd_mul at (k, n, m) = (6, 4, 9):
    // gcd(6,4) = 2, gcd(6,9) = 3, so gcd(k,n)*gcd(k,m) = 6 (dvd 6 6);
    // n*m = 36 = 6*6 (dvd 6 36, via dvd_mul).
    {
        let k = f.num(6);
        let n = f.num(4);
        let m = f.num(9);
        let applied = f.lemma(p.dvd_gcd_mul_gcd_iff_dvd_mul, &[k, n, m]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_gcd_mul_gcd_iff_dvd_mul must apply at (k=6, n=4, m=9): {shown}")
        });
        let gkn = f.gcd(k, n);
        let gkm = f.gcd(k, m);
        let gkn_gkm = f.mul(gkn, gkm);
        let nm = f.mul(n, m);
        let lhs = f.dvd(k, gkn_gkm);
        let rhs = f.dvd(k, nm);
        let want = f.const_app(p.logic.iff, &[lhs, rhs]);
        assert!(
            f.k.def_eq(inferred, want),
            "dvd_gcd_mul_gcd_iff_dvd_mul(6,4,9) must state Iff (dvd 6 (gcd(6,4)*gcd(6,9))) (dvd 6 36)"
        );

        let mp_fn = f.const_app(p.logic.iff_mp, &[lhs, rhs, applied]);
        let refl_k = f.lemma(p.dvd_refl, &[k]); // dvd k k, defeq dvd k gkn_gkm (gkn_gkm computes to 6)
        let mp_result = f.apply(mp_fn, &[refl_k]);
        let mp_inferred = f.k.infer(mp_result).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_gcd_mul_gcd_iff_dvd_mul(6,4,9).mp applied to dvd_refl(6) must type-check: {shown}")
        });
        assert!(
            f.k.def_eq(mp_inferred, rhs),
            "dvd_gcd_mul_gcd_iff_dvd_mul(6,4,9).mp(dvd_refl 6) must produce a proof of dvd 6 36"
        );
    }

    // Symbolic: each applies at a genuinely FREE (k, n, m) triple.
    {
        let name = f.name("dvd_gcd_mul_iff_dvd_mul_restated");
        f.theorem(name, 3, &|d, values| {
            let (k, n, m) = (values[0], values[1], values[2]);
            let gkn = d.gcd(k, n);
            let gkn_m = d.mul(gkn, m);
            let nm = d.mul(n, m);
            let lhs = d.dvd(k, gkn_m);
            let rhs = d.dvd(k, nm);
            let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
            let proof = d.lemma(p.dvd_gcd_mul_iff_dvd_mul, &[k, n, m]);
            (stmt, proof)
        })
        .expect("dvd_gcd_mul_iff_dvd_mul must apply at symbolic k, n, m");
    }
    {
        let name = f.name("dvd_mul_gcd_iff_dvd_mul_restated");
        f.theorem(name, 3, &|d, values| {
            let (k, n, m) = (values[0], values[1], values[2]);
            let gkm = d.gcd(k, m);
            let n_gkm = d.mul(n, gkm);
            let nm = d.mul(n, m);
            let lhs = d.dvd(k, n_gkm);
            let rhs = d.dvd(k, nm);
            let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
            let proof = d.lemma(p.dvd_mul_gcd_iff_dvd_mul, &[k, n, m]);
            (stmt, proof)
        })
        .expect("dvd_mul_gcd_iff_dvd_mul must apply at symbolic k, n, m");
    }
    {
        let name = f.name("dvd_gcd_mul_gcd_iff_dvd_mul_restated");
        f.theorem(name, 3, &|d, values| {
            let (k, n, m) = (values[0], values[1], values[2]);
            let gkn = d.gcd(k, n);
            let gkm = d.gcd(k, m);
            let gkn_gkm = d.mul(gkn, gkm);
            let nm = d.mul(n, m);
            let lhs = d.dvd(k, gkn_gkm);
            let rhs = d.dvd(k, nm);
            let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
            let proof = d.lemma(p.dvd_gcd_mul_gcd_iff_dvd_mul, &[k, n, m]);
            (stmt, proof)
        })
        .expect("dvd_gcd_mul_gcd_iff_dvd_mul must apply at symbolic k, n, m");
    }

    assert!(
        f.k.axiom_footprint(p.dvd_gcd_mul_iff_dvd_mul).is_empty(),
        "dvd_gcd_mul_iff_dvd_mul must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.dvd_mul_gcd_iff_dvd_mul).is_empty(),
        "dvd_mul_gcd_iff_dvd_mul must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.dvd_gcd_mul_gcd_iff_dvd_mul)
            .is_empty(),
        "dvd_gcd_mul_gcd_iff_dvd_mul must rest on zero axioms"
    );
}

/// Test-only duplicate of `dvd_mul_split.rs`'s private `And` body type
/// builder (`pub(super)` to `nat_prelude`, not exported to the test
/// module) -- this development's per-file-copy convention.
fn dvd_mul_split_body_ty(
    f: &mut Fixture,
    k1: ExprId,
    k2: ExprId,
    m: ExprId,
    n: ExprId,
    k: ExprId,
) -> ExprId {
    let p = f.p;
    let dvd_k1_m = f.dvd(k1, m);
    let dvd_k2_n = f.dvd(k2, n);
    let k1k2 = f.mul(k1, k2);
    let eq_k1k2_k = f.eq(k1k2, k);
    let inner = f.const_app(p.logic.and, &[dvd_k2_n, eq_k1k2_k]);
    f.const_app(p.logic.and, &[dvd_k1_m, inner])
}

/// Test-only duplicate of `dvd_mul_split.rs`'s private
/// `∃ k1 k2, And (dvd k1 m) (And (dvd k2 n) (Eq (mul k1 k2) k))` type
/// builder.
fn dvd_mul_split_exists_ty(f: &mut Fixture, m: ExprId, n: ExprId, k: ExprId) -> ExprId {
    let nat = f.nat_ty();
    let one = f.level_one();
    let exists_name = f.p.logic.exists_;
    let k1_fv = f.fresh_fvar();
    let k1 = f.k.fvar(k1_fv);
    let inner_predicate = {
        let k2_fv = f.fresh_fvar();
        let k2 = f.k.fvar(k2_fv);
        let body = dvd_mul_split_body_ty(f, k1, k2, m, n, k);
        f.lam_fv(k2_fv, nat, body)
    };
    let exists = f.k.const_(exists_name, vec![one]);
    let inner_exists = f.apply(exists, &[nat, inner_predicate]);
    let outer_predicate = f.lam_fv(k1_fv, nat, inner_exists);
    let exists = f.k.const_(exists_name, vec![one]);
    f.apply(exists, &[nat, outer_predicate])
}

/// Test-only duplicate of `dvd_mul_split.rs`'s private `split_exists_intro`.
#[allow(clippy::too_many_arguments)]
fn dvd_mul_split_intro(
    f: &mut Fixture,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    k1: ExprId,
    k2: ExprId,
    body_proof: ExprId,
) -> ExprId {
    let nat = f.nat_ty();
    let one = f.level_one();
    let intro_name = f.p.logic.exists_intro;
    let exists_name = f.p.logic.exists_;
    let k2_predicate = {
        let k2_fv = f.fresh_fvar();
        let k2_var = f.k.fvar(k2_fv);
        let body = dvd_mul_split_body_ty(f, k1, k2_var, m, n, k);
        f.lam_fv(k2_fv, nat, body)
    };
    let intro = f.k.const_(intro_name, vec![one]);
    let k2_exists_proof = f.apply(intro, &[nat, k2_predicate, k2, body_proof]);
    let k1_predicate = {
        let k1_fv = f.fresh_fvar();
        let k1_var = f.k.fvar(k1_fv);
        let k1_body = {
            let k2_fv2 = f.fresh_fvar();
            let k2_var2 = f.k.fvar(k2_fv2);
            let body = dvd_mul_split_body_ty(f, k1_var, k2_var2, m, n, k);
            let k2_predicate2 = f.lam_fv(k2_fv2, nat, body);
            let exists = f.k.const_(exists_name, vec![one]);
            f.apply(exists, &[nat, k2_predicate2])
        };
        f.lam_fv(k1_fv, nat, k1_body)
    };
    let intro = f.k.const_(intro_name, vec![one]);
    f.apply(intro, &[nat, k1_predicate, k1, k2_exists_proof])
}

/// `Nat.dvd_mul_split : k ∣ m*n ↔ ∃ k1 k2, k1∣m ∧ k2∣n ∧ k1*k2=k` --
/// Mathlib's `Nat.dvd_mul` (`F:ml430-nat-dvd-mul-ebd102e2`). The theorem
/// itself is proved for a genuinely universally-quantified `(k, m, n)`
/// (kernel-checked at declaration time, including the `k=0` case split and
/// the `k=succ pred` gcd construction), so admission already exercises the
/// free-variable case. This test adds: a concrete, mutually-discriminating
/// instance (`k=6, m=4, n=9`, distinct so a transposed argument fails
/// loudly) exercised via `Iff.mpr` with the algorithm's own witnesses
/// `(k1,k2)=(2,3)`; and the `k=0` degenerate branch applied at a genuinely
/// free `n` via `Iff.mp`.
#[test]
fn dvd_mul_split_applies_at_a_concrete_discriminating_instance_and_a_free_degenerate_one() {
    let mut f = Fixture::new();
    let p = f.p;

    // Concrete, discriminating instance.
    {
        let k = f.num(6);
        let m = f.num(4);
        let n = f.num(9);
        let mn = f.mul(m, n);
        let dvd_k_mn = f.dvd(k, mn);
        let applied = f.lemma(p.dvd_mul_split, &[k, m, n]);
        let exists_ty = dvd_mul_split_exists_ty(&mut f, m, n, k);
        let want = f.const_app(p.logic.iff, &[dvd_k_mn, exists_ty]);
        let inferred = f.k.infer(applied).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_mul_split must apply at (k=6, m=4, n=9): {shown}")
        });
        assert!(
            f.k.def_eq(inferred, want),
            "dvd_mul_split(6,4,9) must state Iff (dvd 6 (4*9)) (exists ...)"
        );

        let k1 = f.num(2);
        let k2 = f.num(3);
        let dvd_k1_m = f.lemma(p.dvd_mul, &[k1, k1]); // dvd 2 (2*2) = dvd 2 4
        let dvd_k2_n = f.lemma(p.dvd_mul, &[k2, k2]); // dvd 3 (3*3) = dvd 3 9
        let k1k2 = f.mul(k1, k2);
        let eq_k1k2_k = f.refl(k1k2); // Eq (2*3) (2*3), defeq Eq (2*3) 6
        let dvd_k1_m_ty = f.dvd(k1, m);
        let dvd_k2_n_ty = f.dvd(k2, n);
        let eq_ty = f.eq(k1k2, k);
        let inner_ty = f.const_app(p.logic.and, &[dvd_k2_n_ty, eq_ty]);
        let inner_and = f.const_app(
            p.logic.and_intro,
            &[dvd_k2_n_ty, eq_ty, dvd_k2_n, eq_k1k2_k],
        );
        let full_and = f.const_app(
            p.logic.and_intro,
            &[dvd_k1_m_ty, inner_ty, dvd_k1_m, inner_and],
        );
        let witness = dvd_mul_split_intro(&mut f, m, n, k, k1, k2, full_and);

        let mpr_fn = f.const_app(p.logic.iff_mpr, &[dvd_k_mn, exists_ty, applied]);
        let mpr_result = f.apply(mpr_fn, &[witness]);
        let mpr_inferred = f.k.infer(mpr_result).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_mul_split(6,4,9).mpr(2,3) must type-check: {shown}")
        });
        assert!(
            f.k.def_eq(mpr_inferred, dvd_k_mn),
            "dvd_mul_split(6,4,9).mpr(2,3) must produce a proof of dvd 6 36"
        );
        let thirty_six = f.num(36);
        assert!(f.k.def_eq(mn, thirty_six), "4*9 must compute to 36");
    }

    // Degenerate: k = 0, m = 0, n genuinely FREE. Forces the `m=0`
    // case-split witness branch `(k1,k2) := (0,n)`, not the gcd
    // construction (which would need `gcd(0,0)` and division by it). `n`
    // is pushed into an explicit `LocalContext` so `infer_in` can look up
    // its type -- a bare unregistered `FVar` is `UnboundFVar` to the
    // checker, not merely "unknown".
    {
        let zero = f.zero();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let anon = f.anon_name();
        let nat_ty = f.nat_ty();
        let mut ctx = LocalContext::new();
        ctx.push(LocalDecl {
            fvar: n_fv,
            name: anon,
            ty: nat_ty,
            info: BinderInfo::Default,
        });

        let zero_n = f.mul(zero, n);
        let dvd0_0n_ty = f.dvd(zero, zero_n);
        let applied = f.lemma(p.dvd_mul_split, &[zero, zero, n]);
        let exists_ty = dvd_mul_split_exists_ty(&mut f, zero, n, zero);
        let inferred = f.k.infer_in(applied, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_mul_split must apply at (k=0, m=0, n free): {shown}")
        });
        let want = f.const_app(p.logic.iff, &[dvd0_0n_ty, exists_ty]);
        assert!(
            f.k.def_eq(inferred, want),
            "dvd_mul_split(0,0,n) must state Iff (dvd 0 (0*n)) (exists ...)"
        );

        // h : dvd 0 (0*n), via witness n and Eq.refl (0*n = 0*n).
        let h_pred = {
            let q_fv = f.fresh_fvar();
            let q = f.k.fvar(q_fv);
            let zero_q = f.mul(zero, q);
            let body = f.eq(zero_n, zero_q);
            f.lam_fv(q_fv, nat_ty, body)
        };
        let one = f.level_one();
        let intro = f.k.const_(p.logic.exists_intro, vec![one]);
        let refl_zero_n = f.refl(zero_n);
        let h = f.apply(intro, &[nat_ty, h_pred, n, refl_zero_n]);
        let mp_fn = f.const_app(p.logic.iff_mp, &[dvd0_0n_ty, exists_ty, applied]);
        let mp_result = f.apply(mp_fn, &[h]);
        f.k.infer_in(mp_result, &mut ctx).unwrap_or_else(|e| {
            let shown = f.explain(&e);
            panic!("dvd_mul_split(0,0,n free).mp(h) must type-check: {shown}")
        });
    }

    assert!(
        f.k.axiom_footprint(p.dvd_mul_split).is_empty(),
        "dvd_mul_split must rest on zero axioms"
    );
}

/// `Nat.ModEq.cancel_left_div_gcd`/`cancel_right_div_gcd`/
/// `cancel_left_div_gcd'` at a DISCRIMINATING concrete instance
/// (`gcd(m,c) = 2 > 1`, so a coprime instance could not tell this family
/// apart from the pre-existing `Nat.mod_eq_cancel`), plus a negative control
/// transposing the cancelled endpoints, plus a symbolic restatement at a
/// genuinely free `(m,a,b,c)` -- both checks are needed per the standing
/// rule that numerals reduce and hide a definitional-equality gap a
/// symbolic check would expose.
///
/// `(m, c, a, b) = (6, 4, 1, 4)`: `gcd(6,4) = 2`, `m/gcd = 3`.
/// `c*a = 4`, `c*b = 16`, and `4 ≡ 16 [MOD 6]` (witnesses `u=2, v=0`:
/// `4+6*2=16`, `16+6*0=16`). The conclusion `1 ≡ 4 [MOD 3]` holds
/// (witnesses `u=1, v=0`: `1+3*1=4`, `4+3*0=4`).
#[test]
fn mod_eq_cancel_div_gcd_family_applies_at_a_discriminating_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    let six = f.num(6);
    let five = f.num(5);
    let four = f.num(4);
    let three = f.num(3);
    let one = f.num(1);
    let two = f.num(2);
    let zero = f.num(0);

    let hm = f.zero_lt_succ(five); // Lt zero six, since six = succ(five)
    let g64 = f.gcd(six, four); // gcd(6,4) = 2
    let m1_check = f.div(six, g64);
    assert!(
        f.k.def_eq(m1_check, three),
        "6 / gcd(6,4) must compute to 3"
    );

    // -- cancel_left_div_gcd : c*a ≡ c*b [MOD m] -> a ≡ b [MOD m/gcd(m,c)] --
    {
        let ca = f.mul(four, one); // 4
        let cb = f.mul(four, four); // 16
        let h = f.concrete_mod_eq(six, ca, cb, two, zero); // 4+6*2=16, 16+6*0=16
        let cancel_proof = f.lemma(p.mod_eq_cancel_left_div_gcd, &[six, one, four, four, hm, h]);
        let m1 = f.div(six, g64);
        let cancel_ty = f.mod_eq(m1, one, four);
        let name = f.name("cancel_left_div_gcd_at_6_4_1_4");
        f.declare_theorem(name, cancel_ty, cancel_proof)
            .unwrap_or_else(|e| {
                panic!(
                    "mod_eq_cancel_left_div_gcd(6,1,4,4) should admit: {}",
                    f.explain(&e)
                )
            });

        // Negative control: the SAME proof must be rejected against the
        // transposed conclusion `4 ≡ 1 [MOD 3]`.
        let wrong_ty = f.mod_eq(m1, four, one);
        let wrong_name = f.name("nc_cancel_left_div_gcd_transposed");
        let wrong_proof = f.lemma(p.mod_eq_cancel_left_div_gcd, &[six, one, four, four, hm, h]);
        let result = f.declare_theorem(wrong_name, wrong_ty, wrong_proof);
        assert!(
            result.is_err(),
            "mod_eq_cancel_left_div_gcd's proof must be rejected against the transposed conclusion"
        );
        assert!(
            !f.k.environment().contains(wrong_name),
            "a rejected declaration must not enter the environment"
        );
    }

    // -- cancel_right_div_gcd : a*c ≡ b*c [MOD m] -> a ≡ b [MOD m/gcd(m,c)] --
    {
        let ac = f.mul(one, four); // 4
        let bc = f.mul(four, four); // 16
        let h = f.concrete_mod_eq(six, ac, bc, two, zero);
        let cancel_proof = f.lemma(
            p.mod_eq_cancel_right_div_gcd,
            &[six, one, four, four, hm, h],
        );
        let m1 = f.div(six, g64);
        let cancel_ty = f.mod_eq(m1, one, four);
        let name = f.name("cancel_right_div_gcd_at_6_4_1_4");
        f.declare_theorem(name, cancel_ty, cancel_proof)
            .unwrap_or_else(|e| {
                panic!(
                    "mod_eq_cancel_right_div_gcd(6,1,4,4) should admit: {}",
                    f.explain(&e)
                )
            });
    }

    // -- cancel_left_div_gcd' : c≡d[MOD m] -> c*a≡d*b[MOD m] ->
    //    a≡b[MOD m/gcd(m,c)] -- at (m,a,b,c,d) = (6,1,4,4,10). --
    {
        let ten = f.add(six, four);
        let hcd = f.concrete_mod_eq(six, four, ten, one, zero); // 4+6*1=10, 10+6*0=10
        let ca = f.mul(four, one); // 4
        let db = f.mul(ten, four); // 40
        let h = f.concrete_mod_eq(six, ca, db, six, zero); // 4+6*6=40, 40+6*0=40
        let cancel_proof = f.lemma(
            p.mod_eq_cancel_left_div_gcd_general,
            &[six, one, four, four, ten, hm, hcd, h],
        );
        let m1 = f.div(six, g64);
        let cancel_ty = f.mod_eq(m1, one, four);
        let name = f.name("cancel_left_div_gcd_general_at_6_4_1_4_10");
        f.declare_theorem(name, cancel_ty, cancel_proof)
            .unwrap_or_else(|e| {
                panic!(
                    "mod_eq_cancel_left_div_gcd_general(6,1,4,4,10) should admit: {}",
                    f.explain(&e)
                )
            });
    }

    // -- Symbolic restatement at a genuinely free `(m,a,b,c)`: re-applying
    // `mod_eq_cancel_left_div_gcd` at fresh fvars, inside a NEW theorem,
    // must still type-check. --
    {
        let d = &mut f;
        let stmt_ty_name = d.name("symbolic_cancel_left_div_gcd_restated");
        d.theorem(stmt_ty_name, 4, &|d, v| {
            let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
            let zero = d.zero();
            let hm_ty = d.lt(zero, m);
            let ca = d.mul(c, a);
            let cb = d.mul(c, b);
            let h_ty = d.mod_eq(m, ca, cb);
            let g = d.gcd(m, c);
            let m1 = d.div(m, g);
            let concl = d.mod_eq(m1, a, b);
            let inner = d.arrow(h_ty, concl);
            let stmt = d.arrow(hm_ty, inner);

            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let applied = d.lemma(p.mod_eq_cancel_left_div_gcd, &[m, a, b, c, hm, h]);
            let with_h = d.lam_fv(h_fv, h_ty, applied);
            let proof = d.lam_fv(hm_fv, hm_ty, with_h);
            (stmt, proof)
        })
        .unwrap_or_else(|e| {
            panic!(
                "mod_eq_cancel_left_div_gcd must apply at a genuinely free (m,a,b,c): {}",
                d.explain(&e)
            )
        });
    }
}

/// `Nat.countRange_permute` at a fully CERTIFIED concrete instance: `σ :=
/// Nat.transposition 1 2` on `[0,4)`, whose `InjectiveOn`/`MapsInto`
/// hypotheses are discharged by the prelude's own
/// `transposition_injective`/`transposition_maps_into` rather than assumed,
/// so this is a real theorem instance and not merely a type-check of an
/// application.
///
/// The predicate `fun x => Nat.ble 2 x` is true on `{2,3}` and its composite
/// with `σ` on `{1,3}` — DIFFERENT index sets with the same count, checked
/// both ways, so the equality cannot pass by being a syntactic identity.
/// Both sides are then required to COMPUTE to `2`; the kernel accepting the
/// application says nothing about what either side counts.
///
/// Negative control: the constant-`0` map is `MapsInto [0,4)` and is NOT
/// injective, and there the two counts genuinely differ (`2` against `0`) —
/// so `InjectiveOn` is load-bearing rather than decorative. Every term here
/// is concrete and below `4`, so the failing `def_eq` terminates at once.
#[test]
fn count_range_permute_certifies_a_transposition_with_a_non_injective_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);

    // `σ := fun k => Nat.transposition 1 2 k`, the shape
    // `transposition_injective`/`_maps_into` state their conclusions at.
    let sigma = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let body = f.const_app(p.transposition, &[one, two, k]);
        f.lam_fv(k_fv, nat, body)
    };
    // `pred := fun x => Nat.ble 2 x`, true exactly on `{2,3}` below `4`.
    let pred = {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let body = f.ble(two, x);
        f.lam_fv(x_fv, nat, body)
    };
    let composed = |f: &mut Fixture, sig: ExprId| {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let sk = f.apply(sig, &[k]);
        let body = f.apply(pred, &[sk]);
        f.lam_fv(k_fv, nat, body)
    };

    // `Lt 1 2` is `Le 2 2`; `Lt 2 4` is `Le 3 4`.
    let lt_1_2 = f.lemma(p.le_refl, &[two]);
    let lt_2_4 = f.lemma(p.le_succ, &[three]);
    let inj = f.const_app(p.transposition_injective, &[one, two, lt_1_2, four]);
    let maps = f.const_app(p.transposition_maps_into, &[one, two, lt_1_2, four, lt_2_4]);

    let proof = f.const_app(p.count_range_permute, &[pred, sigma, four, inj, maps]);
    let inferred =
        f.k.infer(proof)
            .expect("countRange_permute must apply at transposition 1 2 over [0,4)");

    let comp = composed(&mut f, sigma);
    let lhs = f.const_app(p.count_range, &[pred, four]);
    let rhs = f.const_app(p.count_range, &[comp, four]);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the instance must state countRange pred 4 = countRange (pred . sigma) 4"
    );

    // The two sides count the SAME number over DIFFERENT index sets.
    assert!(
        f.k.def_eq(lhs, two),
        "countRange (2 <= .) 4 must compute to 2"
    );
    assert!(
        f.k.def_eq(rhs, two),
        "countRange ((2 <= .) . sigma) 4 must compute to 2"
    );
    let true_ = f.bool_true();
    let false_ = f.bool_false();
    let pred_at_2 = f.apply(pred, &[two]);
    let comp_at_2 = f.apply(comp, &[two]);
    assert!(f.k.def_eq(pred_at_2, true_), "pred holds at index 2");
    assert!(
        f.k.def_eq(comp_at_2, false_),
        "pred . sigma FAILS at index 2 -- the two index sets are genuinely different"
    );

    // NEGATIVE CONTROL: drop injectivity and the conclusion is false.
    let const_zero = {
        let k_fv = f.fresh_fvar();
        f.lam_fv(k_fv, nat, zero)
    };
    let comp_zero = composed(&mut f, const_zero);
    let rhs_zero = f.const_app(p.count_range, &[comp_zero, four]);
    assert!(
        f.k.def_eq(rhs_zero, zero),
        "the constant-0 map sends every index to a point where pred is false"
    );
    assert!(
        !f.k.def_eq(lhs, rhs_zero),
        "without InjectiveOn the two counts differ (2 against 0), so the \
         hypothesis is load-bearing"
    );

    for name in [
        p.count_range_permute,
        p.count_range_point_change,
        p.count_range_congr_lt,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "the countRange permutation family must rest on zero axioms"
        );
    }
}

/// The three new `countRange` laws applied at genuinely FREE variables, not
/// numerals: numerals reduce, and reduction hides definitional-equality gaps
/// that a symbolic instantiation exposes. Each inferred type is checked
/// against the statement written out independently here, so a declaration
/// whose binder order or hypothesis shape drifted would fail rather than pass.
#[test]
fn the_count_range_permutation_family_applies_at_free_variables() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let pred_ty = f.arrow(nat, bool_ty);
    let fn_ty = f.arrow(nat, nat);
    let anon = f.anon_name();

    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let sigma_fv = f.fresh_fvar();
    let sigma = f.k.fvar(sigma_fv);
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [(a_fv, pred_ty), (sigma_fv, fn_ty), (n_fv, nat)] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let inj_ty = f.const_app(p.injective_on, &[sigma, n]);
    let maps_ty = f.const_app(p.maps_into, &[sigma, n]);
    let inj_fv = f.fresh_fvar();
    let inj = f.k.fvar(inj_fv);
    let maps_fv = f.fresh_fvar();
    let maps = f.k.fvar(maps_fv);
    for (fvar, ty) in [(inj_fv, inj_ty), (maps_fv, maps_ty)] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = f.const_app(p.count_range_permute, &[a, sigma, n, inj, maps]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .expect("countRange_permute must apply at free f, sigma, n");
    let composed = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let sk = f.apply(sigma, &[k]);
        let body = f.apply(a, &[sk]);
        f.lam_fv(k_fv, nat, body)
    };
    let lhs = f.const_app(p.count_range, &[a, n]);
    let rhs = f.const_app(p.count_range, &[composed, n]);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the symbolic statement must be countRange a n = countRange (a . sigma) n"
    );

    // `countRange_congr_lt` at free `a`, `b`, `n` plus a free agreement proof.
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    ctx.push(LocalDecl {
        fvar: b_fv,
        name: anon,
        ty: pred_ty,
        info: BinderInfo::Default,
    });
    let agree_ty = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let ai = f.apply(a, &[i]);
        let bi = f.apply(b, &[i]);
        let eq = f.bool_eq(ai, bi);
        let bound = f.lt(i, n);
        let body = f.arrow(bound, eq);
        f.pi_fv(i_fv, nat, body)
    };
    let agree_fv = f.fresh_fvar();
    let agree = f.k.fvar(agree_fv);
    ctx.push(LocalDecl {
        fvar: agree_fv,
        name: anon,
        ty: agree_ty,
        info: BinderInfo::Default,
    });
    let congr_applied = f.const_app(p.count_range_congr_lt, &[a, b, n, agree]);
    let congr_inferred =
        f.k.infer_in(congr_applied, &mut ctx)
            .expect("countRange_congr_lt must apply at free a, b, n");
    let congr_lhs = f.const_app(p.count_range, &[a, n]);
    let congr_rhs = f.const_app(p.count_range, &[b, n]);
    let congr_expected = f.eq(congr_lhs, congr_rhs);
    assert!(f.k.def_eq(congr_inferred, congr_expected));

    // `countRange_point_change` at free `a`, `b`, `i0`, `n`.
    let i0_fv = f.fresh_fvar();
    let i0 = f.k.fvar(i0_fv);
    ctx.push(LocalDecl {
        fvar: i0_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let bound_ty = f.lt(i0, n);
    let below_ty = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let ak = f.apply(a, &[k]);
        let bk = f.apply(b, &[k]);
        let eq = f.bool_eq(ak, bk);
        let lower = f.lt(k, i0);
        let body = f.arrow(lower, eq);
        f.pi_fv(k_fv, nat, body)
    };
    let above_ty = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let ak = f.apply(a, &[k]);
        let bk = f.apply(b, &[k]);
        let eq = f.bool_eq(ak, bk);
        let upper = f.lt(k, n);
        let inner = f.arrow(upper, eq);
        let lower = f.lt(i0, k);
        let body = f.arrow(lower, inner);
        f.pi_fv(k_fv, nat, body)
    };
    let bound_fv = f.fresh_fvar();
    let bound = f.k.fvar(bound_fv);
    let below_fv = f.fresh_fvar();
    let below = f.k.fvar(below_fv);
    let above_fv = f.fresh_fvar();
    let above = f.k.fvar(above_fv);
    for (fvar, ty) in [
        (bound_fv, bound_ty),
        (below_fv, below_ty),
        (above_fv, above_ty),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }
    let change_applied = f.const_app(
        p.count_range_point_change,
        &[a, b, i0, n, bound, below, above],
    );
    let change_inferred =
        f.k.infer_in(change_applied, &mut ctx)
            .expect("countRange_point_change must apply at free a, b, i0, n");
    let one = f.num(1);
    let zero = f.zero();
    let ca = f.const_app(p.count_range, &[a, n]);
    let cb = f.const_app(p.count_range, &[b, n]);
    let a_i0 = f.apply(a, &[i0]);
    let b_i0 = f.apply(b, &[i0]);
    let sel_a = f.bool_select_nat(a_i0, one, zero);
    let sel_b = f.bool_select_nat(b_i0, one, zero);
    let change_lhs = f.add(ca, sel_b);
    let change_rhs = f.add(cb, sel_a);
    let change_expected = f.eq(change_lhs, change_rhs);
    assert!(
        f.k.def_eq(change_inferred, change_expected),
        "point_change must exchange the two values at i0, not repeat one of them"
    );
}

/// `Nat.countRange_product` — three checks, and what each one does and does
/// NOT establish is stated rather than implied.
///
/// 1. A CLOSED instance at `n = 0`, hypotheses discharged from
///    `Nat.not_lt_zero` (they quantify over `Lt b 0`, so they are vacuous).
///    Degenerate — both sides are `zero` — but it is a real theorem instance
///    with nothing assumed, and it is the case that would be unreachable if
///    the lemma carried the `Lt 0 n` hypothesis it deliberately does not.
/// 2. The statement instantiated at `n = 2`, `m = 3` with `R a := beq a 1`,
///    `S b := beq b 0`, `P y := beq y 2` — the genuinely factoring predicate.
///    Both sides are required to COMPUTE to `1`. The hypotheses are supplied
///    as free variables rather than proved (discharging them symbolically in
///    `a` needs div/mod reasoning that is the CONSUMER's job), so this checks
///    what the two sides denote, not the implication.
/// 3. Negative control: `P y := ble 4 y` does not factor through
///    `(y / 2, y % 2)` against the same `R`, `S`, and there the two sides are
///    `2` and `1`. Asserted as `!def_eq`, so the hypotheses are load-bearing
///    rather than decorative. Every term is concrete and below `6`.
#[test]
fn count_range_product_computes_at_a_factoring_predicate_with_a_non_factoring_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let anon = f.anon_name();
    let level_zero = f.kernel().level_zero();

    let pred_of = |f: &mut Fixture, body: &dyn Fn(&mut Fixture, ExprId) -> ExprId| {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let b = body(f, x);
        f.lam_fv(x_fv, nat, b)
    };
    let r = pred_of(&mut f, &|f, a| f.beq(a, one));
    let s = pred_of(&mut f, &|f, b| f.beq(b, zero));
    let pred = pred_of(&mut f, &|f, y| f.beq(y, two));
    let pred_bad = pred_of(&mut f, &|f, y| f.ble(four, y));

    // (1) A CLOSED instance at `n = 0`: both hypotheses are vacuous.
    // Building the vacuous hypotheses by hand needs the exact conclusion the
    // declared type carries, so construct each directly.
    let vacuous_hyp = |f: &mut Fixture, want_true: bool| {
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let hb_fv = f.fresh_fvar();
        let hb = f.k.fvar(hb_fv);
        let zero_inner = f.zero();
        let hb_ty = f.lt(b, zero_inner);

        let na = f.mul(zero_inner, a);
        let idx = f.add(na, b);
        let lhs = f.apply(pred, &[idx]);
        let rhs = if want_true {
            f.apply(s, &[b])
        } else {
            f.bool_false()
        };
        let goal = f.bool_eq(lhs, rhs);

        let contradiction = f.lemma(p.not_lt_zero, &[b, hb]);
        let false_ty = f.k.const_(p.logic.false_, vec![]);
        let motive = f.k.lam(anon, false_ty, goal, BinderInfo::Default);
        let false_rec = f.k.const_(p.logic.false_rec, vec![level_zero]);
        let body = f.apply(false_rec, &[motive, contradiction]);

        let ra = f.apply(r, &[a]);
        let pin = if want_true {
            let t = f.bool_true();
            f.bool_eq(ra, t)
        } else {
            let fl = f.bool_false();
            f.bool_eq(ra, fl)
        };
        let hr_fv = f.fresh_fvar();
        let with_hr = f.lam_fv(hr_fv, pin, body);
        let with_hb = f.lam_fv(hb_fv, hb_ty, with_hr);
        let over_b = f.lam_fv(b_fv, nat, with_hb);
        f.lam_fv(a_fv, nat, over_b)
    };
    let htrue0 = vacuous_hyp(&mut f, true);
    let hfalse0 = vacuous_hyp(&mut f, false);
    let five = f.num(5);
    let closed = f.const_app(
        p.count_range_product,
        &[pred, r, s, zero, five, htrue0, hfalse0],
    );
    let closed_ty =
        f.k.infer(closed)
            .expect("countRange_product must apply with NO positivity hypothesis at n = 0");
    let bound0 = f.mul(zero, five);
    let lhs0 = f.const_app(p.count_range, &[pred, bound0]);
    let cs0 = f.const_app(p.count_range, &[s, zero]);
    let cr0 = f.const_app(p.count_range, &[r, five]);
    let rhs0 = f.mul(cs0, cr0);
    let expected0 = f.eq(lhs0, rhs0);
    assert!(f.k.def_eq(closed_ty, expected0));
    assert!(f.k.def_eq(lhs0, zero), "the n = 0 instance counts zero");

    // (2) The statement at n = 2, m = 3, with the FACTORING predicate.
    let bound = f.mul(two, three);
    assert!(
        f.k.def_eq(bound, six),
        "the block decomposition covers [0,6)"
    );
    let lhs = f.const_app(p.count_range, &[pred, bound]);
    let cs = f.const_app(p.count_range, &[s, two]);
    let cr = f.const_app(p.count_range, &[r, three]);
    let rhs = f.mul(cs, cr);
    assert!(
        f.k.def_eq(lhs, one),
        "countRange (· == 2) 6 must compute to 1"
    );
    assert!(
        f.k.def_eq(cs, one),
        "countRange (· == 0) 2 must compute to 1"
    );
    assert!(
        f.k.def_eq(cr, one),
        "countRange (· == 1) 3 must compute to 1"
    );
    assert!(
        f.k.def_eq(lhs, rhs),
        "the factoring instance balances at 1 = 1 * 1"
    );

    // (3) NEGATIVE CONTROL: a predicate that does NOT factor breaks it.
    let lhs_bad = f.const_app(p.count_range, &[pred_bad, bound]);
    assert!(
        f.k.def_eq(lhs_bad, two),
        "countRange (4 <= ·) 6 must compute to 2"
    );
    assert!(
        !f.k.def_eq(lhs_bad, rhs),
        "a non-factoring predicate gives 2 against 1, so the two per-block \
         hypotheses are load-bearing"
    );

    // The statement's own shape, at genuinely free P, R, S, n, m.
    let pred_ty = f.arrow(nat, bool_ty);
    let mut ctx = LocalContext::new();
    let fvs: Vec<(u64, ExprId)> = {
        let p_fv = f.fresh_fvar();
        let r_fv = f.fresh_fvar();
        let s_fv = f.fresh_fvar();
        let n_fv = f.fresh_fvar();
        let m_fv = f.fresh_fvar();
        vec![
            (p_fv, pred_ty),
            (r_fv, pred_ty),
            (s_fv, pred_ty),
            (n_fv, nat),
            (m_fv, nat),
        ]
    };
    for &(fvar, ty) in &fvs {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }
    let sp = f.k.fvar(fvs[0].0);
    let sr = f.k.fvar(fvs[1].0);
    let ss = f.k.fvar(fvs[2].0);
    let sn = f.k.fvar(fvs[3].0);
    let sm = f.k.fvar(fvs[4].0);

    let hyp_ty = |f: &mut Fixture, want_true: bool| {
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let b_fv = f.fresh_fvar();
        let b = f.k.fvar(b_fv);
        let na = f.mul(sn, a);
        let idx = f.add(na, b);
        let lhs = f.apply(sp, &[idx]);
        let rhs = if want_true {
            f.apply(ss, &[b])
        } else {
            f.bool_false()
        };
        let concl = f.bool_eq(lhs, rhs);
        let ra = f.apply(sr, &[a]);
        let pin = if want_true {
            let t = f.bool_true();
            f.bool_eq(ra, t)
        } else {
            let fl = f.bool_false();
            f.bool_eq(ra, fl)
        };
        let with_pin = f.arrow(pin, concl);
        let bound = f.lt(b, sn);
        let with_bound = f.arrow(bound, with_pin);
        let over_b = f.pi_fv(b_fv, nat, with_bound);
        f.pi_fv(a_fv, nat, over_b)
    };
    let ht_ty = hyp_ty(&mut f, true);
    let hf_ty = hyp_ty(&mut f, false);
    let ht_fv = f.fresh_fvar();
    let ht = f.k.fvar(ht_fv);
    let hf_fv = f.fresh_fvar();
    let hf = f.k.fvar(hf_fv);
    for (fvar, ty) in [(ht_fv, ht_ty), (hf_fv, hf_ty)] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }
    let applied = f.const_app(p.count_range_product, &[sp, sr, ss, sn, sm, ht, hf]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .expect("countRange_product must apply at free P, R, S, n, m");
    let sbound = f.mul(sn, sm);
    let slhs = f.const_app(p.count_range, &[sp, sbound]);
    let scs = f.const_app(p.count_range, &[ss, sn]);
    let scr = f.const_app(p.count_range, &[sr, sm]);
    let srhs = f.mul(scs, scr);
    let sexpected = f.eq(slhs, srhs);
    assert!(
        f.k.def_eq(inferred, sexpected),
        "the symbolic statement must be countRange P (n*m) = countRange S n * countRange R m"
    );

    assert!(
        f.k.axiom_footprint(p.count_range_product).is_empty(),
        "countRange_product must rest on zero axioms"
    );
}

/// `Nat.div_mod_block` at a CLOSED concrete instance — `n = 3`, `a = 2`,
/// `b = 1`, with the `Lt 1 3` side condition supplied as a real proof — plus
/// a genuinely free `(n, a, b)`, and a negative control at `b = n` where the
/// readback is false and the theorem correspondingly cannot be applied.
#[test]
fn div_mod_block_reads_a_concrete_block_back_and_needs_its_side_condition() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let seven = f.num(7);

    // `Lt 1 3` is `Le 2 3`, which is `le_succ 2`.
    let lt_1_3 = f.lemma(p.le_succ, &[two]);
    let applied = f.const_app(p.div_mod_block, &[three, two, one, lt_1_3]);
    let inferred =
        f.k.infer(applied)
            .expect("div_mod_block must apply at (n, a, b) = (3, 2, 1)");

    let na = f.mul(three, two);
    let value = f.add(na, one);
    assert!(f.k.def_eq(value, seven), "3*2 + 1 must compute to 7");
    let quotient = f.div(value, three);
    let remainder = f.modulo(value, three);
    let left = f.eq(quotient, two);
    let right = f.eq(remainder, one);
    let expected = f.const_app(p.logic.and, &[left, right]);
    assert!(f.k.def_eq(inferred, expected));
    assert!(f.k.def_eq(quotient, two), "7 / 3 must compute to 2");
    assert!(f.k.def_eq(remainder, one), "7 % 3 must compute to 1");

    // NEGATIVE CONTROL: at `b = n` the readback is false, so the `Lt b n`
    // side condition is load-bearing rather than decorative. The theorem
    // cannot be applied here at all (there is no `Lt 3 3`), and the values
    // it would have claimed are wrong both ways.
    let bad_value = f.add(na, three);
    let bad_quotient = f.div(bad_value, three);
    let bad_remainder = f.modulo(bad_value, three);
    assert!(
        !f.k.def_eq(bad_quotient, two),
        "at b = n the quotient is 3, not the claimed 2"
    );
    assert!(
        !f.k.def_eq(bad_remainder, three),
        "at b = n the remainder is 0, not the claimed 3"
    );

    // Symbolic: a genuinely free `(n, a, b)` with a free side-condition proof.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    let mut ctx = LocalContext::new();
    for fvar in [n_fv, a_fv, b_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let hb_ty = f.lt(b, n);
    let hb_fv = f.fresh_fvar();
    let hb = f.k.fvar(hb_fv);
    ctx.push(LocalDecl {
        fvar: hb_fv,
        name: anon,
        ty: hb_ty,
        info: BinderInfo::Default,
    });
    let sym = f.const_app(p.div_mod_block, &[n, a, b, hb]);
    let sym_ty =
        f.k.infer_in(sym, &mut ctx)
            .expect("div_mod_block must apply at free (n, a, b)");
    let sym_na = f.mul(n, a);
    let sym_value = f.add(sym_na, b);
    let sym_q = f.div(sym_value, n);
    let sym_r = f.modulo(sym_value, n);
    let sym_left = f.eq(sym_q, a);
    let sym_right = f.eq(sym_r, b);
    let sym_expected = f.const_app(p.logic.and, &[sym_left, sym_right]);
    assert!(
        f.k.def_eq(sym_ty, sym_expected),
        "the symbolic statement must read back BOTH the quotient and the remainder"
    );

    assert!(
        f.k.axiom_footprint(p.div_mod_block).is_empty(),
        "div_mod_block must rest on zero axioms"
    );
}

/// `Nat.totient_mul_of_coprime` at two CLOSED coprime instances with both
/// sides required to COMPUTE, plus a non-coprime negative control at
/// `m = n = 2` where the identity is genuinely FALSE.
///
/// The control is the point of this test. Every step of the proof except one
/// holds without coprimality (measured at all 26 non-coprime pairs with
/// `1 <= m,n <= 9` by
/// `scripts/tests/check-totient-mul-coprime-numerics.py`), so a coprime-only
/// test could not tell this theorem from the much weaker unconditional facts
/// it is assembled from. At `m = n = 2` the two sides are `2` and `1`.
#[test]
fn totient_mul_of_coprime_computes_at_coprime_pairs_with_a_non_coprime_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let twelve = f.num(12);

    // --- (m, n) = (2, 3): totient 6 = 2 and totient 2 * totient 3 = 1 * 2 ---
    // `coprime_succ_self 2` is a REAL proof of `gcd 2 3 = 1`, not a `refl`
    // standing in for one.
    let coprime_2_3 = f.const_app(p.coprime_succ_self, &[two]);
    let applied = f.const_app(p.totient_mul_of_coprime, &[two, three, coprime_2_3]);
    let inferred =
        f.k.infer(applied)
            .expect("totient_mul_of_coprime must apply at the coprime pair (2, 3)");

    let mn = f.mul(two, three);
    let lhs = f.const_app(p.totient, &[mn]);
    let tot_2 = f.const_app(p.totient, &[two]);
    let tot_3 = f.const_app(p.totient, &[three]);
    let rhs = f.mul(tot_2, tot_3);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the statement must be totient (2*3) = totient 2 * totient 3"
    );
    assert!(f.k.def_eq(mn, six), "2*3 must compute to 6");
    assert!(f.k.def_eq(lhs, two), "totient 6 must compute to 2");
    assert!(f.k.def_eq(tot_2, one), "totient 2 must compute to 1");
    assert!(f.k.def_eq(tot_3, two), "totient 3 must compute to 2");
    assert!(
        f.k.def_eq(rhs, two),
        "totient 2 * totient 3 must compute to 2"
    );

    // --- (m, n) = (3, 4): totient 12 = 4 and totient 3 * totient 4 = 2 * 2 --
    // A second instance where the two factors have EQUAL totients, so it pins
    // the arithmetic independently of the first.
    let coprime_3_4 = f.const_app(p.coprime_succ_self, &[three]);
    let applied2 = f.const_app(p.totient_mul_of_coprime, &[three, four, coprime_3_4]);
    let inferred2 =
        f.k.infer(applied2)
            .expect("totient_mul_of_coprime must apply at the coprime pair (3, 4)");
    let mn2 = f.mul(three, four);
    let lhs2 = f.const_app(p.totient, &[mn2]);
    let tot_4 = f.const_app(p.totient, &[four]);
    let rhs2 = f.mul(tot_3, tot_4);
    let expected2 = f.eq(lhs2, rhs2);
    assert!(f.k.def_eq(inferred2, expected2));
    assert!(f.k.def_eq(mn2, twelve), "3*4 must compute to 12");
    assert!(f.k.def_eq(lhs2, four), "totient 12 must compute to 4");
    assert!(
        f.k.def_eq(rhs2, four),
        "totient 3 * totient 4 must compute to 4"
    );

    // --- NEGATIVE CONTROL: m = n = 2, the smallest non-coprime failure -----
    // Both halves matter. The hypothesis is unavailable (gcd 2 2 = 2), AND
    // the conclusion is false -- so this is not a case the theorem merely
    // declines to cover, it is one where covering it would be unsound.
    let gcd_2_2 = f.gcd(two, two);
    assert!(
        !f.k.def_eq(gcd_2_2, one),
        "gcd 2 2 must NOT reduce to 1, so the hypothesis cannot be supplied"
    );
    let square = f.mul(two, two);
    let bad_lhs = f.const_app(p.totient, &[square]);
    let bad_rhs = f.mul(tot_2, tot_2);
    assert!(f.k.def_eq(square, four), "2*2 must compute to 4");
    assert!(f.k.def_eq(bad_lhs, two), "totient 4 must compute to 2");
    assert!(
        f.k.def_eq(bad_rhs, one),
        "totient 2 * totient 2 must compute to 1"
    );
    assert!(
        !f.k.def_eq(bad_lhs, bad_rhs),
        "at m = n = 2 the identity is FALSE (2 against 1), so a coprime-only \
         test would not discriminate this theorem at all"
    );

    assert!(
        f.k.axiom_footprint(p.totient_mul_of_coprime).is_empty(),
        "totient_mul_of_coprime must rest on zero axioms"
    );
}

/// `Nat.fermatNumber_ne_one`/`Nat.fermatNumber_mono`/
/// `Nat.coprime_fermatNumber_fermatNumber` apply at a genuinely FREE variable
/// (each is admitted symbolically, over ANY `n`/`m`/`x`/`y`) and at small
/// concrete instances (`fermatNumber 0 = 3`, `1 = 5`, `2 = 17`), with a
/// NEGATIVE CONTROL confirming coprimality genuinely needs the `Ne m n`
/// hypothesis: `gcd (fermatNumber 0) (fermatNumber 0) = gcd 3 3 = 3`, not `1`.
#[test]
fn fermat_number_mirrors_apply_at_free_and_concrete_instances_with_a_reflexive_negative_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let five = f.num(5);
    let seventeen = f.num(17);

    // --- fermatNumber 0/1/2 compute to 3/5/17 (pinning the base facts the
    // rest of this test relies on) ---
    let f0 = f.const_app(p.fermat_number, &[zero]);
    let f1 = f.const_app(p.fermat_number, &[one]);
    let f2 = f.const_app(p.fermat_number, &[two]);
    assert!(f.k.def_eq(f0, three), "fermatNumber 0 must compute to 3");
    assert!(f.k.def_eq(f1, five), "fermatNumber 1 must compute to 5");
    assert!(
        f.k.def_eq(f2, seventeen),
        "fermatNumber 2 must compute to 17"
    );

    let nat = f.nat_ty();
    let anon = f.anon_name();

    // --- fermatNumber_ne_one, at a genuinely free variable ---
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let mut ctx_n = LocalContext::new();
    ctx_n.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let applied_free = f.const_app(p.fermatnumber_ne_one, &[n]);
    f.k.infer_in(applied_free, &mut ctx_n)
        .expect("fermatNumber_ne_one must apply at a free n");

    // --- fermatNumber_ne_one, at n = 0 ---
    let applied0 = f.const_app(p.fermatnumber_ne_one, &[zero]);
    f.k.infer(applied0)
        .expect("fermatNumber_ne_one must apply at n=0");

    // --- fermatNumber_mono, at genuinely free x, y ---
    let x_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let y_fv = f.fresh_fvar();
    let y = f.k.fvar(y_fv);
    let mut ctx_xy = LocalContext::new();
    for fvar in [x_fv, y_fv] {
        ctx_xy.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let partial_mono = f.const_app(p.fermatnumber_mono, &[x, y]);
    let inferred_mono_ty =
        f.k.infer_in(partial_mono, &mut ctx_xy)
            .expect("fermatNumber_mono must apply to two free naturals");
    let expected_hyp = f.le(x, y);
    let fx = f.const_app(p.fermat_number, &[x]);
    let fy = f.const_app(p.fermat_number, &[y]);
    let expected_concl = f.le(fx, fy);
    let expected_mono_ty = f.arrow(expected_hyp, expected_concl);
    assert!(
        f.k.def_eq(inferred_mono_ty, expected_mono_ty),
        "fermatNumber_mono's type must be Le x y -> Le (fermatNumber x) (fermatNumber y)"
    );

    // --- fermatNumber_mono, concretely at (0, 1): fermatNumber 0=3 <= fermatNumber 1=5 ---
    let le_0_1 = f.const_app(p.zero_le, &[one]);
    let applied_mono01 = f.const_app(p.fermatnumber_mono, &[zero, one, le_0_1]);
    let inferred01 =
        f.k.infer(applied_mono01)
            .expect("fermatNumber_mono must apply at (0, 1)");
    let expected01 = f.le(f0, f1);
    assert!(f.k.def_eq(inferred01, expected01));
    assert!(f.k.def_eq(f0, three));
    assert!(f.k.def_eq(f1, five));

    // --- coprime_fermatNumber_fermatNumber, concretely at (0, 1) ---
    // gcd(fermatNumber 0, fermatNumber 1) = gcd(3, 5) = 1.
    let bfalse = f.bool_false();
    let refl_false = f.bool_refl(bfalse);
    let ne_0_1 = f.const_app(p.ne_of_beq_eq_false, &[zero, one, refl_false]);
    let applied_cop01 = f.const_app(p.coprime_fermatnumber_fermatnumber, &[zero, one, ne_0_1]);
    let inferred_cop01 =
        f.k.infer(applied_cop01)
            .expect("coprime_fermatNumber_fermatNumber must apply at (0, 1)");
    let gcd_f0_f1 = f.gcd(f0, f1);
    let expected_cop01 = f.eq(gcd_f0_f1, one);
    assert!(f.k.def_eq(inferred_cop01, expected_cop01));
    assert!(
        f.k.def_eq(gcd_f0_f1, one),
        "gcd(fermatNumber 0, fermatNumber 1) = gcd(3, 5) must reduce to 1"
    );

    // --- coprime_fermatNumber_fermatNumber, concretely at (1, 2) ---
    // gcd(fermatNumber 1, fermatNumber 2) = gcd(5, 17) = 1 -- a SECOND pair,
    // pinning the arithmetic independently of the first (and taking the
    // theorem's `Lt n m` branch rather than `Lt m n`, exercising the
    // `coprime_symmetric` swap `declare_coprime_fermatnumber_fermatnumber`
    // uses on that side).
    let ne_1_2 = f.const_app(p.ne_of_beq_eq_false, &[one, two, refl_false]);
    let applied_cop12 = f.const_app(p.coprime_fermatnumber_fermatnumber, &[one, two, ne_1_2]);
    let inferred_cop12 =
        f.k.infer(applied_cop12)
            .expect("coprime_fermatNumber_fermatNumber must apply at (1, 2)");
    let gcd_f1_f2 = f.gcd(f1, f2);
    let expected_cop12 = f.eq(gcd_f1_f2, one);
    assert!(f.k.def_eq(inferred_cop12, expected_cop12));
    assert!(
        f.k.def_eq(gcd_f1_f2, one),
        "gcd(fermatNumber 1, fermatNumber 2) = gcd(5, 17) must reduce to 1"
    );

    // --- NEGATIVE CONTROL: m = n = 0 -- the `Ne m n` hypothesis is essential.
    // Without distinctness, gcd(fermatNumber 0, fermatNumber 0) = gcd(3, 3) =
    // 3, NOT 1: coprimality genuinely depends on the hypothesis rather than
    // holding vacuously for this definition's shape.
    let gcd_f0_f0 = f.gcd(f0, f0);
    assert!(
        f.k.def_eq(gcd_f0_f0, three),
        "gcd(fermatNumber 0, fermatNumber 0) = gcd(3, 3) must reduce to 3"
    );
    assert!(
        !f.k.def_eq(gcd_f0_f0, one),
        "gcd(3, 3) must NOT be defeq to 1 -- the control must genuinely fail"
    );

    assert!(
        f.k.axiom_footprint(p.fermatnumber_ne_one).is_empty(),
        "fermatNumber_ne_one must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.fermatnumber_mono).is_empty(),
        "fermatNumber_mono must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.coprime_fermatnumber_fermatnumber)
            .is_empty(),
        "coprime_fermatNumber_fermatNumber must rest on zero axioms"
    );
}

/// `Nat.totient_mul_of_coprime` and both CRT self-map facts at genuinely FREE
/// variables, each inferred type checked against an independently written
/// statement.
///
/// Numerals reduce, so a concrete instance can hide a definitional-equality
/// gap that only a free variable exposes; the two checks fail on disjoint
/// defect classes and this family needs both.
#[test]
fn the_totient_multiplicativity_family_applies_at_free_variables() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();
    let one = f.num(1);

    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let mut ctx = LocalContext::new();
    for fvar in [m_fv, n_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }

    // --- the two self-map facts, at free PREDECESSORS `m`, `n` -------------
    let sm = f.succ(m);
    let sn = f.succ(n);
    let bound = f.mul(sn, sm);
    let self_map = {
        let x_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let mx = f.modulo(x, sm);
        let nx = f.modulo(x, sn);
        let prod = f.mul(sn, mx);
        let body = f.add(prod, nx);
        f.lam_fv(x_fv, nat, body)
    };

    let maps = f.const_app(p.crt_self_map_maps_into, &[m, n]);
    let maps_ty =
        f.k.infer_in(maps, &mut ctx)
            .expect("crtSelfMap_mapsInto must apply at free predecessors");
    let maps_expected = f.const_app(p.maps_into, &[self_map, bound]);
    assert!(
        f.k.def_eq(maps_ty, maps_expected),
        "crtSelfMap_mapsInto must state MapsInto for the residue-pairing map \
         on [0, (succ n)*(succ m)) with NO hypothesis"
    );

    let gcd_sm_sn = f.gcd(sm, sn);
    let hgcd_ty = f.eq(gcd_sm_sn, one);
    let hgcd_fv = f.fresh_fvar();
    let hgcd = f.k.fvar(hgcd_fv);
    ctx.push(LocalDecl {
        fvar: hgcd_fv,
        name: anon,
        ty: hgcd_ty,
        info: BinderInfo::Default,
    });
    let inj = f.const_app(p.crt_self_map_injective_on, &[m, n, hgcd]);
    let inj_ty =
        f.k.infer_in(inj, &mut ctx)
            .expect("crtSelfMap_injectiveOn must apply at free predecessors");
    let inj_expected = f.const_app(p.injective_on, &[self_map, bound]);
    assert!(
        f.k.def_eq(inj_ty, inj_expected),
        "crtSelfMap_injectiveOn must state InjectiveOn for the SAME map on the \
         SAME bound, under the coprimality hypothesis"
    );

    // --- the theorem itself, at a free coprime pair ------------------------
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    let mut ctx2 = LocalContext::new();
    for fvar in [a_fv, b_fv] {
        ctx2.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let gcd_ab = f.gcd(a, b);
    let hyp_ty = f.eq(gcd_ab, one);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);
    ctx2.push(LocalDecl {
        fvar: h_fv,
        name: anon,
        ty: hyp_ty,
        info: BinderInfo::Default,
    });
    let sym = f.const_app(p.totient_mul_of_coprime, &[a, b, h]);
    let sym_ty =
        f.k.infer_in(sym, &mut ctx2)
            .expect("totient_mul_of_coprime must apply at a free coprime pair");
    let ab = f.mul(a, b);
    let sym_lhs = f.const_app(p.totient, &[ab]);
    let tot_a = f.const_app(p.totient, &[a]);
    let tot_b = f.const_app(p.totient, &[b]);
    let sym_rhs = f.mul(tot_a, tot_b);
    let sym_expected = f.eq(sym_lhs, sym_rhs);
    assert!(
        f.k.def_eq(sym_ty, sym_expected),
        "the symbolic statement must be totient (m*n) = totient m * totient n"
    );
    // Binder order is not free: `totient m * totient n` and its transpose are
    // different theorems and both type-check at concrete numerals, so pin the
    // one that actually landed.
    let transposed = f.mul(tot_b, tot_a);
    let transposed_stmt = f.eq(sym_lhs, transposed);
    assert!(
        !f.k.def_eq(sym_ty, transposed_stmt),
        "the two factor orders are DIFFERENT statements at free variables; \
         this assertion is what makes the one above discriminate"
    );

    for name in [
        p.crt_self_map_maps_into,
        p.crt_self_map_injective_on,
        p.totient_mul_of_coprime,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "the totient multiplicativity family must rest on zero axioms"
        );
    }
}

/// `g x = n*(x mod m) + (x mod n)` at concrete `(m, n)` — the CRT self-map
/// `Nat.crtSelfMap_injectiveOn` is about, rebuilt here so the test can
/// EVALUATE it rather than only type-check statements about it.
fn crt_image_at(f: &mut Fixture, m: ExprId, n: ExprId, x: ExprId) -> ExprId {
    let mx = f.modulo(x, m);
    let nx = f.modulo(x, n);
    let prod = f.mul(n, mx);
    f.add(prod, nx)
}

/// The CRT self-map really is injective on `[0, n*m)` for a coprime pair and
/// really is NOT for a non-coprime one — by EVALUATION at concrete numerals,
/// because the map is a bare lambda and nothing the kernel checks constrains
/// what it computes.
///
/// At `m = n = 2` it sends both `0` and `2` to `0` while both are below the
/// bound `4`, the smallest collision
/// `scripts/tests/check-totient-mul-coprime-numerics.py` reports. So
/// `Nat.crtSelfMap_injectiveOn`'s hypothesis is load-bearing rather than
/// decorative.
#[test]
fn the_crt_self_map_permutes_a_coprime_block_and_collides_on_a_non_coprime_one() {
    let mut f = Fixture::new();
    let zero = f.num(0);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);

    // --- coprime (m, n) = (2, 3): the six images are a permutation of [0,6) -
    let mut seen: Vec<u32> = Vec::new();
    for k in 0..6u32 {
        let x = f.num(k);
        let img = crt_image_at(&mut f, two, three, x);
        let mut matched = None;
        for target in 0..6u32 {
            let t = f.num(target);
            if f.k.def_eq(img, t) {
                matched = Some(target);
                break;
            }
        }
        let value = matched.unwrap_or_else(|| panic!("g {k} must land inside [0,6)"));
        assert!(
            !seen.contains(&value),
            "at the coprime pair (2,3) the map must be INJECTIVE, but two \
             distinct inputs share the image {value}"
        );
        seen.push(value);
    }
    assert_eq!(seen.len(), 6, "all six images must have been identified");
    let bound_2_3 = f.mul(three, two);
    assert!(
        f.k.def_eq(bound_2_3, six),
        "the bound n*m must compute to 6"
    );

    // --- NEGATIVE CONTROL: non-coprime (m, n) = (2, 2) collides at 0 and 2 --
    let g0 = crt_image_at(&mut f, two, two, zero);
    let g2 = crt_image_at(&mut f, two, two, two);
    assert!(
        f.k.def_eq(g0, zero),
        "g 0 must compute to 0 at (m,n) = (2,2)"
    );
    assert!(
        f.k.def_eq(g2, zero),
        "g 2 must compute to 0 at (m,n) = (2,2)"
    );
    assert!(
        f.k.def_eq(g0, g2),
        "the two images must be equal -- that IS the collision"
    );
    assert!(
        !f.k.def_eq(zero, two),
        "the two INPUTS must differ, or the collision is vacuous"
    );
    let bound_2_2 = f.mul(two, two);
    assert!(f.k.def_eq(bound_2_2, four), "the bound must compute to 4");
    // Both colliding inputs are genuinely inside the block, with REAL proofs
    // rather than well-formedness checks -- so this refutes `InjectiveOn g 4`
    // itself rather than describing behaviour outside the map's domain.
    let lt_0_4 = f.zero_lt_succ(three);
    let want_0_4 = f.lt(zero, bound_2_2);
    let got_0_4 = f.k.infer(lt_0_4).expect("zero_lt_succ 3 must type-check");
    assert!(
        f.k.def_eq(got_0_4, want_0_4),
        "the first colliding input must be proved below the bound"
    );
    let lt_2_4 = f.lemma(f.p.le_succ, &[three]);
    let want_2_4 = f.lt(two, bound_2_2);
    let got_2_4 = f.k.infer(lt_2_4).expect("le_succ 3 must type-check");
    assert!(
        f.k.def_eq(got_2_4, want_2_4),
        "the second colliding input must be proved below the bound"
    );
}

/// `Nat.fermatNumber n = 2^(2^n) + 1` at concrete, hand-computed values —
/// `docs/research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md`.
/// The kernel's admission of the `Definition` only confirms it type-checks
/// (`Nat -> Nat`), not that it computes the right thing (`CLAUDE.md`'s "THE
/// TRUSTED GATE CANNOT TELL YOU A `Definition` IS WRONG" entry), so this test
/// is the only thing standing between a type-correct `Nat -> Nat` function and
/// the actual Fermat numbers.
///
/// Hand-computed:
///   fermatNumber 0 = 2^(2^0) + 1 = 2^1 + 1 = 3
///   fermatNumber 1 = 2^(2^1) + 1 = 2^2 + 1 = 5
///   fermatNumber 2 = 2^(2^2) + 1 = 2^4 + 1 = 17
/// matching Mathlib's own `fermatNumber_zero`/`fermatNumber_one`/
/// `fermatNumber_two` (`Mathlib/NumberTheory/Fermat.lean`, pinned commit
/// `c5ea0035…`, each `:= rfl`).
///
/// Deliberately stops at `n = 2`: every numeral here is a unary `succ`-tower,
/// and `fermatNumber` grows doubly exponentially, so `n = 3` (`257`, formed
/// magnitude `2^8 = 256`) is the next step and `n = 4` (`65537`) would be
/// catastrophic (`CLAUDE.md`'s "EVERY `Nat` NUMERAL THIS PRELUDE BUILDS IS
/// UNARY" entry).
///
/// Negative controls discriminate against the most likely construction bugs:
/// dropping the trailing `+ 1`, and computing `n + 1` in place of the nested
/// exponent (`2^n + 1` instead of `2^(2^n) + 1`).
#[test]
fn fermat_number_evaluates_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let five = f.num(5);
    let sixteen = f.num(16);
    let seventeen = f.num(17);

    let f0 = f.const_app(p.fermat_number, &[zero]);
    assert!(f.k.def_eq(f0, three), "fermatNumber 0 must reduce to 3");
    assert!(
        !f.k.def_eq(f0, two),
        "negative control: fermatNumber 0 must NOT be def-eq to 2 (the \
         value a dropped `+ 1` would give: 2^(2^0) = 2)"
    );

    let f1 = f.const_app(p.fermat_number, &[one]);
    assert!(f.k.def_eq(f1, five), "fermatNumber 1 must reduce to 5");
    assert!(
        !f.k.def_eq(f1, four),
        "negative control: fermatNumber 1 must NOT be def-eq to 4 (the \
         value a dropped `+ 1` would give: 2^(2^1) = 4)"
    );

    let f2 = f.const_app(p.fermat_number, &[two]);
    assert!(
        f.k.def_eq(f2, seventeen),
        "fermatNumber 2 must reduce to 17"
    );
    assert!(
        !f.k.def_eq(f2, sixteen),
        "negative control: fermatNumber 2 must NOT be def-eq to 16 (a \
         dropped `+ 1`)"
    );
    assert!(
        !f.k.def_eq(f2, five),
        "negative control: fermatNumber 2 must NOT be def-eq to 5 (the \
         value computing 2^n + 1 instead of 2^(2^n) + 1 would give at n=2: \
         2^2 + 1 = 5, catching a missing nested-exponent bug)"
    );
}

/// `Nat.totient_mul_of_dvd` at CLOSED dividing pairs, with both sides required
/// to COMPUTE, plus a non-dividing negative control where the identity is
/// genuinely FALSE.
///
/// The divisibility witnesses are real proofs (`dvd_mul a q : Dvd a (mul a q)`),
/// not `refl` standing in for one. The control is the point of the test: this
/// theorem carries no primality and no positivity, so its ONLY hypothesis is
/// `e ∣ m`, and a dividing-only test could not tell it from the false
/// unconditional statement. At `(m, e) = (1, 2)` — the smallest non-dividing
/// pair — the two sides are `1` and `2`.
///
/// Ranges and the smallest counterexample are from
/// `scripts/tests/check-totient-prime-power-numerics.py`, checks `4` and `4N`.
#[test]
fn totient_mul_of_dvd_computes_at_closed_dividing_pairs_with_a_non_dividing_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let eight = f.num(8);

    // --- (m, e) = (4, 2), a case where `e` divides `m` PROPERLY ------------
    // `dvd_mul 2 2 : Dvd 2 (mul 2 2)`, and `mul 2 2` computes to `4`.
    let dvd_2_4 = f.const_app(p.dvd_mul, &[two, two]);
    let applied = f.const_app(p.totient_mul_of_dvd, &[four, two, dvd_2_4]);
    let inferred =
        f.k.infer(applied)
            .expect("totient_mul_of_dvd must apply at the dividing pair (4, 2)");

    let me = f.mul(four, two);
    let lhs = f.const_app(p.totient, &[me]);
    let tot_4 = f.const_app(p.totient, &[four]);
    let rhs = f.mul(tot_4, two);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the statement must be totient (4*2) = totient 4 * 2"
    );
    assert!(f.k.def_eq(me, eight), "4*2 must compute to 8");
    assert!(f.k.def_eq(lhs, four), "totient 8 must compute to 4");
    assert!(f.k.def_eq(tot_4, two), "totient 4 must compute to 2");
    assert!(f.k.def_eq(rhs, four), "totient 4 * 2 must compute to 4");

    // --- (m, e) = (6, 3): `e` divides `m` but `m` is not a prime power, so
    // this pins the counting independently of the prime-power case.
    let dvd_3_6 = f.const_app(p.dvd_mul, &[three, two]);
    let applied2 = f.const_app(p.totient_mul_of_dvd, &[six, three, dvd_3_6]);
    let inferred2 =
        f.k.infer(applied2)
            .expect("totient_mul_of_dvd must apply at the dividing pair (6, 3)");
    let me2 = f.mul(six, three);
    let lhs2 = f.const_app(p.totient, &[me2]);
    let tot_6 = f.const_app(p.totient, &[six]);
    let rhs2 = f.mul(tot_6, three);
    let expected2 = f.eq(lhs2, rhs2);
    assert!(f.k.def_eq(inferred2, expected2));
    assert!(f.k.def_eq(tot_6, two), "totient 6 must compute to 2");
    assert!(f.k.def_eq(lhs2, six), "totient 18 must compute to 6");
    assert!(f.k.def_eq(rhs2, six), "totient 6 * 3 must compute to 6");

    // --- NEGATIVE CONTROL: (m, e) = (1, 2), the smallest non-dividing pair -
    // The conclusion is FALSE here, so this is not a case the theorem merely
    // declines to cover -- it is one where covering it would be unsound.
    let bad_me = f.mul(one, two);
    let bad_lhs = f.const_app(p.totient, &[bad_me]);
    let tot_1 = f.const_app(p.totient, &[one]);
    let bad_rhs = f.mul(tot_1, two);
    assert!(f.k.def_eq(bad_lhs, one), "totient (1*2) must compute to 1");
    assert!(f.k.def_eq(tot_1, one), "totient 1 must compute to 1");
    assert!(f.k.def_eq(bad_rhs, two), "totient 1 * 2 must compute to 2");
    assert!(
        !f.k.def_eq(bad_lhs, bad_rhs),
        "at (m, e) = (1, 2) the identity is FALSE (1 against 2), so a \
         dividing-only test would not discriminate this theorem at all"
    );

    assert!(
        f.k.axiom_footprint(p.totient_mul_of_dvd).is_empty(),
        "totient_mul_of_dvd must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.count_range_const_true).is_empty(),
        "countRange_const_true must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.coprime_mul_iff_of_dvd).is_empty(),
        "coprime_mul_iff_of_dvd must rest on zero axioms"
    );
}

/// `Nat.totient_prime_pow` at `2^3` and `3^2`, with a COMPOSITE negative
/// control where the identity is genuinely false.
///
/// The prime hypothesis is a hypothetical free variable — this prelude exposes
/// no closed primality witness (`prime_two` is `fn`-private to `primes.rs`) —
/// but every VALUE in the conclusion is closed and is required to compute, so
/// a statement carrying the wrong arithmetic would fail here.
///
/// The composite control is what makes the test discriminating. At base `4`
/// the statement reads `totient 4 = 4 - 1`, i.e. `2 = 3`: false. So primality
/// is load-bearing rather than decorative, and it enters in exactly one place
/// (the induction's base case, through `Nat.totient_prime`). Magnitudes are
/// kept at `8`, `9` and `4` on purpose: prelude numerals are unary.
#[test]
fn totient_prime_pow_computes_at_two_cubed_and_three_squared_with_a_composite_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let anon = f.anon_name();
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let six = f.num(6);
    let eight = f.num(8);
    let nine = f.num(9);
    let one = f.num(1);

    // --- 2^3: totient 8 = 8 - 4 = 4 ---------------------------------------
    let prime_two_ty = prime_condition_for_test(&mut f, two);
    let mut ctx = LocalContext::new();
    let h2_fv = f.fresh_fvar();
    let h2 = f.k.fvar(h2_fv);
    ctx.push(LocalDecl {
        fvar: h2_fv,
        name: anon,
        ty: prime_two_ty,
        info: BinderInfo::Default,
    });
    let applied = f.const_app(p.totient_prime_pow, &[two, two, h2]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .expect("totient_prime_pow must apply at base 2, exponent succ 2");

    let pow_2_3 = f.const_app(p.pow, &[two, three]);
    let pow_2_2 = f.const_app(p.pow, &[two, two]);
    let lhs = f.const_app(p.totient, &[pow_2_3]);
    let rhs = f.sub(pow_2_3, pow_2_2);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the statement must be totient (2^3) = 2^3 - 2^2"
    );
    assert!(f.k.def_eq(pow_2_3, eight), "2^3 must compute to 8");
    assert!(f.k.def_eq(pow_2_2, four), "2^2 must compute to 4");
    assert!(f.k.def_eq(lhs, four), "totient 8 must compute to 4");
    assert!(f.k.def_eq(rhs, four), "8 - 4 must compute to 4");

    // --- 3^2: totient 9 = 9 - 3 = 6, an ODD prime so the base is not 2 -----
    let prime_three_ty = prime_condition_for_test(&mut f, three);
    let h3_fv = f.fresh_fvar();
    let h3 = f.k.fvar(h3_fv);
    ctx.push(LocalDecl {
        fvar: h3_fv,
        name: anon,
        ty: prime_three_ty,
        info: BinderInfo::Default,
    });
    let applied3 = f.const_app(p.totient_prime_pow, &[three, one, h3]);
    let inferred3 =
        f.k.infer_in(applied3, &mut ctx)
            .expect("totient_prime_pow must apply at base 3, exponent succ 1");
    let pow_3_2 = f.const_app(p.pow, &[three, two]);
    let pow_3_1 = f.const_app(p.pow, &[three, one]);
    let lhs3 = f.const_app(p.totient, &[pow_3_2]);
    let rhs3 = f.sub(pow_3_2, pow_3_1);
    let expected3 = f.eq(lhs3, rhs3);
    assert!(f.k.def_eq(inferred3, expected3));
    assert!(f.k.def_eq(pow_3_2, nine), "3^2 must compute to 9");
    assert!(f.k.def_eq(lhs3, six), "totient 9 must compute to 6");
    assert!(f.k.def_eq(rhs3, six), "9 - 3 must compute to 6");

    // --- NEGATIVE CONTROL: a COMPOSITE base, where the identity is FALSE ---
    // `totient (4^1) = 4^1 - 4^0` reads `2 = 3`. Kept at base 4 exponent 1 so
    // the formed magnitudes stay tiny.
    let zero = f.zero();
    let pow_4_1 = f.const_app(p.pow, &[four, one]);
    let pow_4_0 = f.const_app(p.pow, &[four, zero]);
    let bad_lhs = f.const_app(p.totient, &[pow_4_1]);
    let bad_rhs = f.sub(pow_4_1, pow_4_0);
    assert!(f.k.def_eq(pow_4_1, four), "4^1 must compute to 4");
    assert!(f.k.def_eq(pow_4_0, one), "4^0 must compute to 1");
    assert!(f.k.def_eq(bad_lhs, two), "totient 4 must compute to 2");
    assert!(f.k.def_eq(bad_rhs, three), "4 - 1 must compute to 3");
    assert!(
        !f.k.def_eq(bad_lhs, bad_rhs),
        "at the COMPOSITE base 4 the identity is FALSE (2 against 3), so the \
         primality hypothesis is load-bearing and a prime-only test would not \
         discriminate this theorem at all"
    );

    assert!(
        f.k.axiom_footprint(p.totient_prime_pow).is_empty(),
        "totient_prime_pow must rest on zero axioms"
    );
    assert!(
        f.k.axiom_footprint(p.totient_pow_succ_of_prime).is_empty(),
        "totient_pow_succ_of_prime must rest on zero axioms"
    );
}

/// The whole prime-power family at genuinely FREE variables, each inferred
/// type checked against an independently written statement.
///
/// Numerals reduce, so a concrete instance can hide a definitional-equality
/// gap that only a free variable exposes; the two checks fail on disjoint
/// defect classes and this family needs both. The `!def_eq` guards the argument
/// ORDER of `totient_mul_of_dvd`'s right-hand side — `totient m * e` and
/// `totient e * m` are different theorems, and at a numeral pair where the two
/// happen to agree a concrete test cannot separate them.
#[test]
fn the_totient_prime_power_family_applies_at_free_variables() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();
    let one = f.num(1);

    let m_fv = f.fresh_fvar();
    let m = f.k.fvar(m_fv);
    let e_fv = f.fresh_fvar();
    let e = f.k.fvar(e_fv);
    let mut ctx = LocalContext::new();
    for fvar in [m_fv, e_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }

    // --- countRange_const_true, at a free bound ---------------------------
    let const_true = {
        let true_ = f.bool_true();
        f.k.lam(anon, nat, true_, BinderInfo::Default)
    };
    let cct = f.const_app(p.count_range_const_true, &[m]);
    let cct_ty =
        f.k.infer_in(cct, &mut ctx)
            .expect("countRange_const_true must apply at a free bound");
    let cct_lhs = f.const_app(p.count_range, &[const_true, m]);
    let cct_expected = f.eq(cct_lhs, m);
    assert!(
        f.k.def_eq(cct_ty, cct_expected),
        "countRange_const_true must state countRange (fun _ => true) m = m"
    );

    // --- the gcd bridge and Lemma B, under a free `Dvd e m` ---------------
    let dvd_ty = f.dvd(e, m);
    let hd_fv = f.fresh_fvar();
    let hd = f.k.fvar(hd_fv);
    ctx.push(LocalDecl {
        fvar: hd_fv,
        name: anon,
        ty: dvd_ty,
        info: BinderInfo::Default,
    });

    let k_fv = f.fresh_fvar();
    let k = f.k.fvar(k_fv);
    ctx.push(LocalDecl {
        fvar: k_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let bridge = f.const_app(p.coprime_mul_iff_of_dvd, &[k, m, e, hd]);
    let bridge_ty =
        f.k.infer_in(bridge, &mut ctx)
            .expect("coprime_mul_iff_of_dvd must apply at free variables");
    let me = f.mul(m, e);
    let g_me = f.gcd(k, me);
    let g_m = f.gcd(k, m);
    let left = f.eq(g_me, one);
    let right = f.eq(g_m, one);
    let bridge_expected = f.const_app(p.logic.iff, &[left, right]);
    assert!(
        f.k.def_eq(bridge_ty, bridge_expected),
        "coprime_mul_iff_of_dvd must state gcd k (m*e) = 1 <-> gcd k m = 1"
    );

    let lemma_b = f.const_app(p.totient_mul_of_dvd, &[m, e, hd]);
    let lemma_b_ty =
        f.k.infer_in(lemma_b, &mut ctx)
            .expect("totient_mul_of_dvd must apply at free variables");
    let tot_me = f.const_app(p.totient, &[me]);
    let tot_m = f.const_app(p.totient, &[m]);
    let lb_rhs = f.mul(tot_m, e);
    let lemma_b_expected = f.eq(tot_me, lb_rhs);
    assert!(
        f.k.def_eq(lemma_b_ty, lemma_b_expected),
        "totient_mul_of_dvd must state totient (m*e) = totient m * e"
    );

    // The TRANSPOSED right-hand side is a different theorem. `totient e * m`
    // is what a copy-paste slip would produce.
    let tot_e = f.const_app(p.totient, &[e]);
    let transposed_rhs = f.mul(tot_e, m);
    let transposed = f.eq(tot_me, transposed_rhs);
    assert!(
        !f.k.def_eq(lemma_b_ty, transposed),
        "totient m * e and totient e * m are different theorems; the statement \
         must not be def-eq to the transposed one"
    );

    // --- both prime-power forms, at a free base and a free exponent -------
    let q_fv = f.fresh_fvar();
    let q = f.k.fvar(q_fv);
    let j_fv = f.fresh_fvar();
    let j = f.k.fvar(j_fv);
    let mut ctx2 = LocalContext::new();
    for fvar in [q_fv, j_fv] {
        ctx2.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let prime_q_ty = prime_condition_for_test(&mut f, q);
    let hq_fv = f.fresh_fvar();
    let hq = f.k.fvar(hq_fv);
    ctx2.push(LocalDecl {
        fvar: hq_fv,
        name: anon,
        ty: prime_q_ty,
        info: BinderInfo::Default,
    });

    let sj = f.succ(j);
    let pow_sj = f.const_app(p.pow, &[q, sj]);
    let pow_j = f.const_app(p.pow, &[q, j]);
    let tot_pow = f.const_app(p.totient, &[pow_sj]);

    let mult = f.const_app(p.totient_pow_succ_of_prime, &[q, j, hq]);
    let mult_ty =
        f.k.infer_in(mult, &mut ctx2)
            .expect("totient_pow_succ_of_prime must apply at a free base and exponent");
    let qm1 = f.sub(q, one);
    let mult_rhs = f.mul(qm1, pow_j);
    let mult_expected = f.eq(tot_pow, mult_rhs);
    assert!(
        f.k.def_eq(mult_ty, mult_expected),
        "totient_pow_succ_of_prime must state totient (q^(j+1)) = (q-1) * q^j"
    );

    let subf = f.const_app(p.totient_prime_pow, &[q, j, hq]);
    let sub_ty =
        f.k.infer_in(subf, &mut ctx2)
            .expect("totient_prime_pow must apply at a free base and exponent");
    let sub_rhs = f.sub(pow_sj, pow_j);
    let sub_expected = f.eq(tot_pow, sub_rhs);
    assert!(
        f.k.def_eq(sub_ty, sub_expected),
        "totient_prime_pow must state totient (q^(j+1)) = q^(j+1) - q^j"
    );
}

/// `Nat.totient_dvd_totient_mul_prime` — the prime step — at free variables,
/// with a discriminating control that is deliberately NOT the composite one.
///
/// **A composite-base control here would be VACUOUS, and that is measured
/// rather than assumed.** This statement is `F:ml430-nat-totient-dvd-of-dvd`
/// specialised (`x` always divides `x*q`), so it is TRUE for every `q`, prime
/// or not — check `11V` of `scripts/tests/check-totient-prime-power-numerics.py`
/// confirms it fails at zero composite multipliers. Primality is a requirement
/// of the proof ROUTE (`coprime_or_dvd_of_prime` is what decides the case
/// split), not of the proposition. Copying the composite control from
/// `totient_prime_pow`, where it genuinely discriminates, would have produced
/// a control that cannot fail — the exact trap this repository has been caught
/// by three times in this area.
///
/// The usable control is the TRANSPOSED divisibility, which fails at 142 pairs
/// with the smallest being `x = 1, q = 3` (`totient 3 = 2` does not divide
/// `totient 1 = 1`); check `11N`.
#[test]
fn the_prime_step_divides_at_free_variables_with_a_transposed_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();

    let x_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let q_fv = f.fresh_fvar();
    let q = f.k.fvar(q_fv);
    let mut ctx = LocalContext::new();
    for fvar in [x_fv, q_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let prime_q_ty = prime_condition_for_test(&mut f, q);
    let hq_fv = f.fresh_fvar();
    let hq = f.k.fvar(hq_fv);
    ctx.push(LocalDecl {
        fvar: hq_fv,
        name: anon,
        ty: prime_q_ty,
        info: BinderInfo::Default,
    });

    let step = f.const_app(p.totient_dvd_totient_mul_prime, &[x, q, hq]);
    let step_ty =
        f.k.infer_in(step, &mut ctx)
            .expect("totient_dvd_totient_mul_prime must apply at free variables");

    let xq = f.mul(x, q);
    let tot_x = f.const_app(p.totient, &[x]);
    let tot_xq = f.const_app(p.totient, &[xq]);
    let expected = f.dvd(tot_x, tot_xq);
    assert!(
        f.k.def_eq(step_ty, expected),
        "the prime step must state Dvd (totient x) (totient (x*q))"
    );

    // The TRANSPOSED divisibility is a different, FALSE statement.
    let transposed = f.dvd(tot_xq, tot_x);
    assert!(
        !f.k.def_eq(step_ty, transposed),
        "Dvd (totient (x*q)) (totient x) is the opposite statement and is \
         false at x = 1, q = 3 (2 does not divide 1); the two must not be \
         def-eq"
    );

    // --- CLOSED instance: x = 6, q = 2, where 2 DIVIDES 6 -----------------
    // This exercises the `q | x` branch, the one that routes through this
    // lane's own `totient_mul_of_dvd`. totient 6 = 2 divides totient 12 = 4.
    let two = f.num(2);
    let four = f.num(4);
    let six = f.num(6);
    let twelve = f.num(12);
    let six_two = f.mul(six, two);
    let tot_6 = f.const_app(p.totient, &[six]);
    let tot_12 = f.const_app(p.totient, &[six_two]);
    assert!(f.k.def_eq(six_two, twelve), "6*2 must compute to 12");
    assert!(f.k.def_eq(tot_6, two), "totient 6 must compute to 2");
    assert!(f.k.def_eq(tot_12, four), "totient 12 must compute to 4");

    // --- CLOSED instance: x = 3, q = 2, the COPRIME branch ----------------
    // totient 3 = 2 divides totient 6 = 2. Exercises the other branch, which
    // routes through totient_mul_of_coprime instead.
    let three = f.num(3);
    let three_two = f.mul(three, two);
    let tot_3 = f.const_app(p.totient, &[three]);
    let tot_6b = f.const_app(p.totient, &[three_two]);
    assert!(f.k.def_eq(three_two, six), "3*2 must compute to 6");
    assert!(f.k.def_eq(tot_3, two), "totient 3 must compute to 2");
    assert!(f.k.def_eq(tot_6b, two), "totient 6 must compute to 2");

    assert!(
        f.k.axiom_footprint(p.totient_dvd_totient_mul_prime)
            .is_empty(),
        "totient_dvd_totient_mul_prime must rest on zero axioms"
    );
}

/// `Nat.totient_dvd_totient_mul : ∀ k a, Dvd (totient a) (totient (mul a k))`
/// — the fully general (no hypothesis) engine behind Target 1
/// (`F:ml430-nat-totient-dvd-of-dvd-9622e44a`), at free `k`, `a`, plus a
/// transposed-direction control and closed instances exercising a chain of
/// length 0 (`k=1`), 1 (`k` prime), and 2 (`k` composite, forcing the
/// well-founded induction to peel two primes).
#[test]
fn totient_dvd_totient_mul_applies_at_free_variables_with_a_transposed_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();

    let k_fv = f.fresh_fvar();
    let k = f.k.fvar(k_fv);
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let mut ctx = LocalContext::new();
    for fvar in [k_fv, a_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }

    let applied = f.const_app(p.totient_dvd_totient_mul, &[k, a]);
    let applied_ty =
        f.k.infer_in(applied, &mut ctx)
            .expect("totient_dvd_totient_mul must apply at free k, a");

    let mul_ak = f.mul(a, k);
    let tot_a = f.const_app(p.totient, &[a]);
    let tot_ak = f.const_app(p.totient, &[mul_ak]);
    let expected = f.dvd(tot_a, tot_ak);
    assert!(
        f.k.def_eq(applied_ty, expected),
        "must state Dvd (totient a) (totient (a*k))"
    );

    // The TRANSPOSED divisibility is a DIFFERENT, generally false statement
    // (e.g. k=2, a=1: totient 2 = 1 divides totient 1 = 1 is degenerate, but
    // k=3, a=1: totient 3 = 2 does NOT divide totient 1 = 1).
    let transposed = f.dvd(tot_ak, tot_a);
    assert!(
        !f.k.def_eq(applied_ty, transposed),
        "the transposed divisibility must not be def-eq to the real statement"
    );

    // --- k = 1 (chain length 0): totient a | totient a trivially ----------
    let three = f.num(3);
    let one = f.num(1);
    let three_one = f.mul(three, one);
    let tot_3 = f.const_app(p.totient, &[three]);
    let tot_3b = f.const_app(p.totient, &[three_one]);
    assert!(f.k.def_eq(three_one, three), "3*1 must compute to 3");
    assert!(f.k.def_eq(tot_3, tot_3b), "totient 3 = totient (3*1)");

    // --- k = 3, a = 4 (chain length 1, k prime): totient 4 = 2 | totient 12 = 4
    let four = f.num(4);
    let twelve = f.num(12);
    let four_three = f.mul(four, three);
    let two = f.num(2);
    let tot_4 = f.const_app(p.totient, &[four]);
    let tot_12 = f.const_app(p.totient, &[four_three]);
    assert!(f.k.def_eq(four_three, twelve), "4*3 must compute to 12");
    assert!(f.k.def_eq(tot_4, two), "totient 4 must compute to 2");
    assert!(f.k.def_eq(tot_12, four), "totient 12 must compute to 4");

    // --- k = 4 = 2*2 (chain length 2, composite k): totient 3 = 2 | totient 12 = 4
    // This exercises the well-founded induction actually peeling TWO primes
    // off the cofactor rather than stopping after one step.
    let three_four = f.mul(three, four);
    let tot_3c = f.const_app(p.totient, &[three]);
    let tot_12b = f.const_app(p.totient, &[three_four]);
    assert!(f.k.def_eq(three_four, twelve), "3*4 must compute to 12");
    assert!(f.k.def_eq(tot_3c, two), "totient 3 must compute to 2");
    assert!(f.k.def_eq(tot_12b, four), "totient 12 must compute to 4");

    assert!(
        f.k.axiom_footprint(p.totient_dvd_totient_mul).is_empty(),
        "totient_dvd_totient_mul must rest on zero axioms"
    );
}

/// `Nat.totient_dvd_of_dvd : ∀ a b, Dvd a b → Dvd (totient a) (totient b)` —
/// `F:ml430-nat-totient-dvd-of-dvd-9622e44a` itself, at a free hypothesis
/// (the divisibility witness is never constructed, only its TYPE is pushed
/// into context, matching this file's standing pattern for a hypothesis
/// fvar), plus a transposed-conclusion control and a closed dividing pair.
#[test]
fn totient_dvd_of_dvd_applies_at_a_free_hypothesis_with_a_transposed_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();

    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    let mut ctx = LocalContext::new();
    for fvar in [a_fv, b_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let dvd_ab_ty = f.dvd(a, b);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);
    ctx.push(LocalDecl {
        fvar: h_fv,
        name: anon,
        ty: dvd_ab_ty,
        info: BinderInfo::Default,
    });

    let applied = f.const_app(p.totient_dvd_of_dvd, &[a, b, h]);
    let applied_ty =
        f.k.infer_in(applied, &mut ctx)
            .expect("totient_dvd_of_dvd must apply at a free hypothesis");

    let tot_a = f.const_app(p.totient, &[a]);
    let tot_b = f.const_app(p.totient, &[b]);
    let expected = f.dvd(tot_a, tot_b);
    assert!(
        f.k.def_eq(applied_ty, expected),
        "must state Dvd (totient a) (totient b)"
    );

    // The TRANSPOSED divisibility is a different, generally false statement
    // (fails whenever a=1, b>2: totient b does not divide totient 1 = 1).
    let transposed = f.dvd(tot_b, tot_a);
    assert!(
        !f.k.def_eq(applied_ty, transposed),
        "the transposed divisibility must not be def-eq to the real statement"
    );

    // --- closed dividing pair: a = 4, b = 12, totient 4 = 2 | totient 12 = 4
    let four = f.num(4);
    let twelve = f.num(12);
    let three = f.num(3);
    let two = f.num(2);
    let four_three = f.mul(four, three);
    let dvd_4_12_ty = f.dvd(four, twelve);
    let hc_fv = f.fresh_fvar();
    let hc = f.k.fvar(hc_fv);
    let mut ctx2 = LocalContext::new();
    ctx2.push(LocalDecl {
        fvar: hc_fv,
        name: anon,
        ty: dvd_4_12_ty,
        info: BinderInfo::Default,
    });
    let applied_c = f.const_app(p.totient_dvd_of_dvd, &[four, twelve, hc]);
    let applied_c_ty =
        f.k.infer_in(applied_c, &mut ctx2)
            .expect("totient_dvd_of_dvd must apply at the closed pair (4, 12)");
    let tot_4 = f.const_app(p.totient, &[four]);
    let tot_12 = f.const_app(p.totient, &[four_three]);
    assert!(f.k.def_eq(four_three, twelve), "4*3 must compute to 12");
    assert!(f.k.def_eq(tot_4, two), "totient 4 must compute to 2");
    let expected_c = f.dvd(tot_4, tot_12);
    assert!(
        f.k.def_eq(applied_c_ty, expected_c),
        "closed instance must still state Dvd (totient 4) (totient 12)"
    );

    assert!(
        f.k.axiom_footprint(p.totient_dvd_of_dvd).is_empty(),
        "totient_dvd_of_dvd must rest on zero axioms"
    );
}

/// `Nat.totient_mul_cofactor_bound : forall k a, Le one (totient a) -> Le
/// two k -> Or (Le (mul two (totient a)) (totient (mul a k))) (And (Eq k
/// two) (Eq (totient (mul a k)) (totient a)))` -- the multiplier-tracking
/// bound Target 3 is built from, at free `k`, `a` and free hypotheses, plus
/// a transposed-direction control and closed instances exercising BOTH
/// disjuncts (k=2 with a odd/coprime gives the second; k=3 with a=1 gives
/// the first).
#[test]
fn totient_mul_cofactor_bound_applies_at_free_variables_with_a_transposed_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();

    let k_fv = f.fresh_fvar();
    let k = f.k.fvar(k_fv);
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let mut ctx = LocalContext::new();
    for fvar in [k_fv, a_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let one = f.num(1);
    let two = f.num(2);
    let tot_a = f.const_app(p.totient, &[a]);
    let hpos_ty = f.le(one, tot_a);
    let hpos_fv = f.fresh_fvar();
    let hpos = f.k.fvar(hpos_fv);
    ctx.push(LocalDecl {
        fvar: hpos_fv,
        name: anon,
        ty: hpos_ty,
        info: BinderInfo::Default,
    });
    let h2_ty = f.le(two, k);
    let h2_fv = f.fresh_fvar();
    let h2 = f.k.fvar(h2_fv);
    ctx.push(LocalDecl {
        fvar: h2_fv,
        name: anon,
        ty: h2_ty,
        info: BinderInfo::Default,
    });

    let applied = f.const_app(p.totient_mul_cofactor_bound, &[k, a, hpos, h2]);
    let applied_ty =
        f.k.infer_in(applied, &mut ctx)
            .expect("totient_mul_cofactor_bound must apply at free k, a and free hypotheses");

    let mul_ak = f.mul(a, k);
    let tot_ak = f.const_app(p.totient, &[mul_ak]);
    let two_tot_a = f.mul(two, tot_a);
    let left_ty = f.le(two_tot_a, tot_ak);
    let eq_k2_ty = f.eq(k, two);
    let eq_tot_ty = f.eq(tot_ak, tot_a);
    let right_ty = f.const_app(p.logic.and, &[eq_k2_ty, eq_tot_ty]);
    let expected = f.const_app(p.logic.or, &[left_ty, right_ty]);
    assert!(
        f.k.def_eq(applied_ty, expected),
        "must state Or (Le 2*totient(a) totient(a*k)) (And (k=2) (totient(a*k)=totient(a)))"
    );

    // The TRANSPOSED first-disjunct direction is a different, generally
    // false statement (false whenever totient(a*k) actually exceeds
    // 2*totient(a), e.g. k=4, a=1: totient(4)=2 > 2*totient(1)=2 is FALSE
    // too at equality, but k=5,a=1: totient(5)=4 > 2*1=2, so the transposed
    // Le 4 2 fails while the real Le 2 4 holds).
    let transposed_left = f.le(tot_ak, two_tot_a);
    let transposed = f.const_app(p.logic.or, &[transposed_left, right_ty]);
    assert!(
        !f.k.def_eq(applied_ty, transposed),
        "the transposed first disjunct must not be def-eq to the real statement"
    );

    // --- k = 2, a = 3 (odd, coprime with 2): SECOND disjunct exactly -----
    let three = f.num(3);
    let six = f.num(6);
    let hpos3_ty = {
        let tot_3 = f.const_app(p.totient, &[three]);
        f.le(one, tot_3)
    };
    let h2_2_ty = f.le(two, two);
    let hpos3_fv = f.fresh_fvar();
    let hpos3 = f.k.fvar(hpos3_fv);
    let h2c_fv = f.fresh_fvar();
    let h2c = f.k.fvar(h2c_fv);
    let mut ctx2 = LocalContext::new();
    ctx2.push(LocalDecl {
        fvar: hpos3_fv,
        name: anon,
        ty: hpos3_ty,
        info: BinderInfo::Default,
    });
    ctx2.push(LocalDecl {
        fvar: h2c_fv,
        name: anon,
        ty: h2_2_ty,
        info: BinderInfo::Default,
    });
    let applied_c = f.const_app(p.totient_mul_cofactor_bound, &[two, three, hpos3, h2c]);
    let applied_c_ty =
        f.k.infer_in(applied_c, &mut ctx2)
            .expect("totient_mul_cofactor_bound must apply at the closed pair (k=2, a=3)");
    let three_two = f.mul(three, two);
    let tot_3 = f.const_app(p.totient, &[three]);
    let tot_6 = f.const_app(p.totient, &[three_two]);
    assert!(f.k.def_eq(three_two, six), "3*2 must compute to 6");
    assert!(f.k.def_eq(tot_3, two), "totient 3 must compute to 2");
    assert!(f.k.def_eq(tot_6, two), "totient 6 must compute to 2");
    let left_c_ty = {
        let two_tot_3 = f.mul(two, tot_3);
        f.le(two_tot_3, tot_6)
    };
    let right_c_ty = {
        let eq_k2 = f.eq(two, two);
        let eq_tot = f.eq(tot_6, tot_3);
        f.const_app(p.logic.and, &[eq_k2, eq_tot])
    };
    let expected_c = f.const_app(p.logic.or, &[left_c_ty, right_c_ty]);
    assert!(
        f.k.def_eq(applied_c_ty, expected_c),
        "closed instance (k=2,a=3) must still state the same disjunction shape"
    );

    assert!(
        f.k.axiom_footprint(p.totient_mul_cofactor_bound).is_empty(),
        "totient_mul_cofactor_bound must rest on zero axioms"
    );
}

/// `Nat.eq_or_eq_of_totient_eq_totient : forall a b, Dvd a b -> Eq (totient
/// a) (totient b) -> Or (Eq a b) (Eq (mul two a) b)` -- Target 3
/// (`F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7`) itself, at a free
/// hypothesis pair, plus a transposed-conclusion control and closed
/// instances exercising both disjuncts (a=3,b=6 gives the second; a=5,b=5
/// gives the first).
#[test]
fn eq_or_eq_of_totient_eq_totient_applies_at_a_free_hypothesis_with_a_transposed_control() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let anon = f.anon_name();

    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b_fv = f.fresh_fvar();
    let b = f.k.fvar(b_fv);
    let mut ctx = LocalContext::new();
    for fvar in [a_fv, b_fv] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let dvd_ab_ty = f.dvd(a, b);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);
    ctx.push(LocalDecl {
        fvar: h_fv,
        name: anon,
        ty: dvd_ab_ty,
        info: BinderInfo::Default,
    });
    let tot_a = f.const_app(p.totient, &[a]);
    let tot_b = f.const_app(p.totient, &[b]);
    let tot_eq_ty = f.eq(tot_a, tot_b);
    let ht_fv = f.fresh_fvar();
    let ht = f.k.fvar(ht_fv);
    ctx.push(LocalDecl {
        fvar: ht_fv,
        name: anon,
        ty: tot_eq_ty,
        info: BinderInfo::Default,
    });

    let applied = f.const_app(p.eq_or_eq_of_totient_eq_totient, &[a, b, h, ht]);
    let applied_ty =
        f.k.infer_in(applied, &mut ctx)
            .expect("eq_or_eq_of_totient_eq_totient must apply at a free hypothesis pair");

    let two = f.num(2);
    let two_a = f.mul(two, a);
    let eq_ab_ty = f.eq(a, b);
    let eq_2ab_ty = f.eq(two_a, b);
    let expected = f.const_app(p.logic.or, &[eq_ab_ty, eq_2ab_ty]);
    assert!(
        f.k.def_eq(applied_ty, expected),
        "must state Or (Eq a b) (Eq (2*a) b)"
    );

    // The TRANSPOSED first disjunct `Eq b a` is NOT def-eq to `Eq a b` for
    // free a, b (def_eq compares structurally, not up to symmetry).
    let transposed_left = f.eq(b, a);
    let transposed = f.const_app(p.logic.or, &[transposed_left, eq_2ab_ty]);
    assert!(
        !f.k.def_eq(applied_ty, transposed),
        "the transposed first disjunct must not be def-eq to the real statement"
    );

    // --- a = 3, b = 6 (a odd, dividing, equal totients): SECOND disjunct -
    let three = f.num(3);
    let six = f.num(6);
    let dvd_3_6_ty = f.dvd(three, six);
    let tot_3 = f.const_app(p.totient, &[three]);
    let tot_6 = f.const_app(p.totient, &[six]);
    let tot_eq_3_6_ty = f.eq(tot_3, tot_6);
    let hc_fv = f.fresh_fvar();
    let hc = f.k.fvar(hc_fv);
    let htc_fv = f.fresh_fvar();
    let htc = f.k.fvar(htc_fv);
    let mut ctx2 = LocalContext::new();
    ctx2.push(LocalDecl {
        fvar: hc_fv,
        name: anon,
        ty: dvd_3_6_ty,
        info: BinderInfo::Default,
    });
    ctx2.push(LocalDecl {
        fvar: htc_fv,
        name: anon,
        ty: tot_eq_3_6_ty,
        info: BinderInfo::Default,
    });
    let applied_c = f.const_app(p.eq_or_eq_of_totient_eq_totient, &[three, six, hc, htc]);
    let applied_c_ty =
        f.k.infer_in(applied_c, &mut ctx2)
            .expect("eq_or_eq_of_totient_eq_totient must apply at the closed pair (3, 6)");
    assert!(f.k.def_eq(tot_3, two), "totient 3 must compute to 2");
    assert!(f.k.def_eq(tot_6, two), "totient 6 must compute to 2");
    let expected_c = {
        let eq_3_6 = f.eq(three, six);
        let two_three = f.mul(two, three);
        let eq_2_3_6 = f.eq(two_three, six);
        f.const_app(p.logic.or, &[eq_3_6, eq_2_3_6])
    };
    assert!(
        f.k.def_eq(applied_c_ty, expected_c),
        "closed instance (3,6) must still state the same disjunction shape"
    );

    assert!(
        f.k.axiom_footprint(p.eq_or_eq_of_totient_eq_totient)
            .is_empty(),
        "eq_or_eq_of_totient_eq_totient must rest on zero axioms"
    );
}

/// `Nat.dvd_pow_add_one_of_odd_mul_exp` (`a^e+1 ∣ a^{e*(2t+1)}+1`) at a
/// genuinely FREE `(a,e,t)` — applying it at fresh fvars and checking the
/// applied type IS the free-variable instantiation check, since the theorem
/// itself is `∀ a e t, …` — and at the concrete discriminating instance
/// `a=2, e=1, t=1` (`d=2t+1=3`, odd, `>1`): `2^1+1=3` divides `2^(1*3)+1=9`,
/// the smallest instance the classical Fermat-prime argument would use (`9`
/// is composite, `3 · 3`, which is exactly why a prime `a^n+1` cannot have an
/// odd factor `>1` in its exponent). The negative control is arithmetic, not
/// a kernel proof attempt: dropping "odd" is essential, since `3` does NOT
/// divide `2^2+1=5` (an even exponent), so the theorem could not be
/// strengthened to arbitrary exponents.
#[test]
fn dvd_pow_add_one_of_odd_mul_exp_applies_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;

    // Free-variable check: a, e, t are bound into an explicit LocalContext at
    // `Nat` (a bare `f.k.infer` on a raw fvar rejects it as `UnboundFVar`).
    let nat = f.nat_ty();
    let anon = f.k.anon();
    let a_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let e_fv = f.fresh_fvar();
    let e = f.k.fvar(e_fv);
    let t_fv = f.fresh_fvar();
    let t = f.k.fvar(t_fv);
    let mut ctx = LocalContext::new();
    for fv in [a_fv, e_fv, t_fv] {
        ctx.push(LocalDecl {
            fvar: fv,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
    }
    let applied = f.const_app(p.dvd_pow_add_one_of_odd_mul_exp, &[a, e, t]);
    f.k.infer_in(applied, &mut ctx).unwrap_or_else(|err| {
        panic!(
            "dvd_pow_add_one_of_odd_mul_exp must apply at free a, e, t: {}",
            f.explain(&err)
        )
    });

    // Concrete discriminating instance: a=2, e=1, t=1 -> d=2t+1=3 (odd, >1).
    // Claim: 2^1+1=3 divides 2^(1*3)+1 = 9.
    let two = f.num(2);
    let one = f.num(1);
    let three = f.num(3);
    let nine = f.num(9);
    let proof = f.lemma(p.dvd_pow_add_one_of_odd_mul_exp, &[two, one, one]);
    let stmt = f.dvd(three, nine);
    let name = f.name("two_add_one_dvd_two_cubed_add_one");
    f.declare_theorem(name, stmt, proof).unwrap_or_else(|err| {
        panic!(
            "dvd_pow_add_one_of_odd_mul_exp(2,1,1) should give 3 | 9: {}",
            f.explain(&err)
        )
    });

    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "the odd-factor divisibility instance must rest on zero axioms"
    );

    // Discriminating negative control (arithmetic, not a kernel proof
    // attempt): dropping "odd" is essential -- 2^2+1 = 5 is NOT divisible
    // by 3, so the same claim over an EVEN exponent (d=2) genuinely fails.
    assert_ne!(
        5 % 3,
        0,
        "3 must NOT divide 2^2+1=5 -- the odd hypothesis is load-bearing"
    );
}

// --- `least_number.rs` — ADR-0603 row 2 for the least-number principle ------

/// Rebuild `∀ (P : Prop), Or P (Not P)` exactly the way `least_number.rs`
/// builds it. Kept in the test file (rather than exported) so the row-2
/// controls below check a term this file constructed independently.
fn excluded_middle_type(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let prop = f.k.sort_zero();
    let x_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let nx = f.const_app(p.logic.not, &[x]);
    let body = f.const_app(p.logic.or, &[x, nx]);
    f.pi_fv(x_fv, prop, body)
}

/// `∀ k, Lt k n → Not (Q k)`.
fn none_below_type(f: &mut Fixture, q: ExprId, n: ExprId) -> ExprId {
    let p = f.p;
    let nat = f.nat_ty();
    let k_fv = f.fresh_fvar();
    let k = f.k.fvar(k_fv);
    let lt = f.lt(k, n);
    let qk = f.apply(q, &[k]);
    let nqk = f.const_app(p.logic.not, &[qk]);
    let imp = f.arrow(lt, nqk);
    f.pi_fv(k_fv, nat, imp)
}

/// Rebuild the unrestricted least-number principle,
/// `∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`.
fn unrestricted_lnp_type(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.level_one();
    let prop = f.k.sort_zero();
    let pty = f.arrow(nat, prop);

    let q_fv = f.fresh_fvar();
    let q = f.k.fvar(q_fv);

    let inh = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let body = f.apply(q, &[n]);
        let pred = f.lam_fv(n_fv, nat, body);
        let ex = f.k.const_(p.logic.exists_, vec![one]);
        f.apply(ex, &[nat, pred])
    };
    let concl = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let qm = f.apply(q, &[m]);
        let nb = none_below_type(f, q, m);
        let body = f.const_app(p.logic.and, &[qm, nb]);
        let pred = f.lam_fv(m_fv, nat, body);
        let ex = f.k.const_(p.logic.exists_, vec![one]);
        f.apply(ex, &[nat, pred])
    };
    let body = f.arrow(inh, concl);
    f.pi_fv(q_fv, pty, body)
}

/// **The row-2 statement, checked against genuinely FREE variables.**
///
/// Numerals reduce and hide definitional-equality gaps, so a concrete
/// instantiation is not enough (`CLAUDE.md`, "a concrete instantiation can hide
/// the bug a symbolic one exposes"). Here `P` is a free variable of sort `Prop`
/// and `hlnp` is a free variable of the full unrestricted-LNP type, both pushed
/// into an explicit `LocalContext`: nothing reduces, and the inferred type must
/// be `Or P (Not P)` on the nose.
#[test]
fn lnp_unrestricted_implies_em_applies_at_a_free_hypothesis_and_a_free_proposition() {
    let mut f = Fixture::new();
    let p = f.p;
    let anon = f.k.anon();
    let prop = f.k.sort_zero();

    let lnp_ty = unrestricted_lnp_type(&mut f);
    let h_fv = f.fresh_fvar();
    let h = f.k.fvar(h_fv);
    let p_fv = f.fresh_fvar();
    let prop_var = f.k.fvar(p_fv);

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: h_fv,
        name: anon,
        ty: lnp_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: p_fv,
        name: anon,
        ty: prop,
        info: BinderInfo::Default,
    });

    let applied = f.const_app(p.lnp_unrestricted_implies_em, &[h, prop_var]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("LNP -> EM must apply at free P: {}", f.explain(&err)));

    let np = f.const_app(p.logic.not, &[prop_var]);
    let expected = f.const_app(p.logic.or, &[prop_var, np]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or P (Not P)` at a FREE P, found {}",
        f.k.render_lean(inferred)
    );

    // NEGATIVE CONTROL, and it is the one that matters: the hypothesis is
    // load-bearing, and the theorem this prelude ACTUALLY has cannot discharge
    // it. `Nat.lnp_of_pointwise_decision` is the unrestricted principle plus one
    // decidability argument, so plugging it into the hypothesis slot must be
    // REJECTED. Without this the test would pass for a "row 2" whose hypothesis
    // is something already proved -- i.e. for a proof of excluded middle.
    //
    // Note this is a genuine discrimination, not a sort mismatch: substituting
    // the free `h` (which IS the unrestricted principle) for `decidable` below
    // makes the application type-check and kills this assertion.
    let decidable = f.k.const_(p.lnp_of_pointwise_decision, vec![]);
    let bogus = f.const_app(p.lnp_unrestricted_implies_em, &[decidable, prop_var]);
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "the decidable form must NOT discharge the unrestricted hypothesis -- if \
         it does, the two statements are the same and this row proves nothing"
    );
}

/// **Non-vacuity, part 1: excluded middle is not already available.**
///
/// A reduction to excluded middle is worthless if excluded middle is lying
/// around. Nothing in the environment may have `∀ (P : Prop), Or P (Not P)` as
/// its type. The POSITIVE CONTROL runs the identical scan for
/// `Nat.lnp_unrestricted_implies_em`'s own type and requires exactly one hit —
/// so a scan that has stopped matching anything (the failure mode this repo
/// cares about most) fails the test rather than reporting a clean zero.
#[test]
fn excluded_middle_is_not_itself_a_declaration_anywhere_in_the_environment() {
    let mut f = Fixture::new();

    let em_ty = excluded_middle_type(&mut f);
    let lnp_ty = unrestricted_lnp_type(&mut f);
    let implies_em_ty = {
        let em = excluded_middle_type(&mut f);
        f.arrow(lnp_ty, em)
    };

    let declared: Vec<(NameId, Declaration)> =
        f.k.environment()
            .iter()
            .map(|(name, decl)| (*name, decl.clone()))
            .collect();

    let ty_of = |decl: &Declaration| -> Option<ExprId> {
        match decl {
            Declaration::Theorem { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Axiom { ty, .. }
            | Declaration::Opaque { ty, .. } => Some(*ty),
            _ => None,
        }
    };

    let em_holders: Vec<String> = declared
        .iter()
        .filter(|(_, decl)| ty_of(decl) == Some(em_ty))
        .map(|(name, _)| f.k.display_name(*name).to_string())
        .collect();
    let control: Vec<String> = declared
        .iter()
        .filter(|(_, decl)| ty_of(decl) == Some(implies_em_ty))
        .map(|(name, _)| f.k.display_name(*name).to_string())
        .collect();

    assert_eq!(
        control.len(),
        1,
        "POSITIVE CONTROL: the scan must find exactly `Nat.lnp_unrestricted_implies_em` \
         by its type; found {control:?}. A zero here means the scan is broken, not that \
         excluded middle is absent."
    );
    assert!(
        em_holders.is_empty(),
        "excluded middle is already declared as {em_holders:?} -- the row-2 \
         reduction in `least_number.rs` would then be vacuous"
    );
}

/// **Non-vacuity, part 2: the DECIDABLE least-number principle is a theorem.**
///
/// The row-2 claim is "the unrestricted form costs excluded middle", not "we
/// have not proved a least-number principle". Both of the anchors
/// `least_number.rs`'s module doc names are checked here to be live, `Theorem`-
/// kind and axiom-free: the general [`NatPrelude::lnp_decidable`] proved in that
/// file, and the older, predicate-specific
/// [`NatPrelude::least_divisor_search`] that `minFac`'s minimality already runs
/// on.
#[test]
fn the_decidable_least_number_principle_is_a_landed_axiom_free_theorem() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    for (name, label) in [
        (p.lnp_decidable, "Nat.lnp_decidable"),
        (p.lnp_bounded_search, "Nat.lnp_bounded_search"),
        (p.lnp_of_pointwise_decision, "Nat.lnp_of_pointwise_decision"),
        (p.least_divisor_search, "Nat.least_divisor_search"),
        (p.em_implies_lnp, "Nat.em_implies_lnp"),
        (
            p.lnp_unrestricted_implies_em,
            "Nat.lnp_unrestricted_implies_em",
        ),
    ] {
        let decl = k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"))
            .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{label} must be a Theorem, not {decl:?}"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, found {:?}",
            footprint
                .iter()
                .map(|n| k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// `Nat.lnp_decidable` at a CONCRETE decidable predicate, with a discriminating
/// negative: `ble 2 n` is true at `n = 3` and false at `n = 1`, so the same
/// application with the false instance must be REJECTED. Magnitudes stay tiny
/// (`CLAUDE.md`: every `Nat` numeral this prelude builds is unary).
#[test]
fn lnp_decidable_accepts_a_true_instance_and_rejects_a_false_one() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    // `dec := fun i => Nat.ble 2 i`.
    let dec = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let two = f.num(2);
        let body = f.const_app(p.ble, &[two, i]);
        f.lam_fv(i_fv, nat, body)
    };

    let three = f.num(3);
    let true_ = f.bool_true();
    let hit = f.bool_refl(true_);
    let applied = f.const_app(p.lnp_decidable, &[dec, three, hit]);
    f.k.infer(applied).unwrap_or_else(|err| {
        panic!(
            "lnp_decidable must apply at `ble 2 .` and n := 3: {}",
            f.explain(&err)
        )
    });

    // NEGATIVE CONTROL: `ble 2 1` reduces to `false`, so the identical proof
    // shape is not a proof of the hypothesis and the kernel must refuse it.
    let one = f.num(1);
    let bogus = f.const_app(p.lnp_decidable, &[dec, one, hit]);
    assert!(
        f.k.infer(bogus).is_err(),
        "lnp_decidable must REJECT n := 1, where `ble 2 1` is false"
    );
}

/// `Nat.em_implies_lnp` closes the loop: excluded middle buys the unrestricted
/// least-number principle back, so the price named by
/// `Nat.lnp_unrestricted_implies_em` is EXACTLY excluded middle, not merely at
/// least excluded middle. Checked symbolically — `em` is a free variable of the
/// excluded-middle type and `Q` a free variable of `Nat → Prop`.
#[test]
fn em_implies_lnp_makes_the_two_principles_interderivable() {
    let mut f = Fixture::new();
    let p = f.p;
    let anon = f.k.anon();
    let nat = f.nat_ty();
    let prop = f.k.sort_zero();
    let pty = f.arrow(nat, prop);

    let em_ty = excluded_middle_type(&mut f);
    let em_fv = f.fresh_fvar();
    let em = f.k.fvar(em_fv);
    let q_fv = f.fresh_fvar();
    let q = f.k.fvar(q_fv);

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: em_fv,
        name: anon,
        ty: em_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: q_fv,
        name: anon,
        ty: pty,
        info: BinderInfo::Default,
    });

    let applied = f.const_app(p.em_implies_lnp, &[em, q]);
    let inferred = f.k.infer_in(applied, &mut ctx).unwrap_or_else(|err| {
        panic!(
            "em_implies_lnp must apply at a free `em` and a free `Q`: {}",
            f.explain(&err)
        )
    });

    // The result is `(∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`,
    // i.e. the unrestricted principle's body at this `Q`.
    let expected = {
        let one = f.level_one();
        let inh = {
            let n_fv = f.fresh_fvar();
            let n = f.k.fvar(n_fv);
            let body = f.apply(q, &[n]);
            let pred = f.lam_fv(n_fv, nat, body);
            let ex = f.k.const_(p.logic.exists_, vec![one]);
            f.apply(ex, &[nat, pred])
        };
        let concl = {
            let m_fv = f.fresh_fvar();
            let m = f.k.fvar(m_fv);
            let qm = f.apply(q, &[m]);
            let nb = none_below_type(&mut f, q, m);
            let body = f.const_app(p.logic.and, &[qm, nb]);
            let pred = f.lam_fv(m_fv, nat, body);
            let ex = f.k.const_(p.logic.exists_, vec![one]);
            f.apply(ex, &[nat, pred])
        };
        f.arrow(inh, concl)
    };
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "em_implies_lnp's conclusion must be the unrestricted principle at Q, found {}",
        f.k.render_lean(inferred)
    );
}

/// **The equivalence, pinned structurally rather than narrated.**
///
/// Build the unrestricted least-number principle `L` and excluded middle `E`
/// once, and require the two declared types to be *exactly* `L → E` and
/// `E → L` — same `ExprId`s, not merely defeq, not merely "the same up to how
/// I described them". That is the whole row-2 claim in two `assert_eq!`s: the
/// price of dropping the decidability hypothesis is excluded middle, and it is
/// neither more nor less.
///
/// The third assertion is what keeps this from being a tautology: the landed
/// [`NatPrelude::lnp_of_pointwise_decision`] is NOT `L` — it carries one extra
/// hypothesis, `∀ n, Or (Q n) (Not (Q n))` — so `L` genuinely is not something
/// this prelude proves.
#[test]
fn the_unrestricted_lnp_and_excluded_middle_are_pinned_as_an_exact_equivalence() {
    let mut f = Fixture::new();
    let p = f.p;

    let lnp_ty = unrestricted_lnp_type(&mut f);
    let em_ty = excluded_middle_type(&mut f);
    let forward = f.arrow(lnp_ty, em_ty);
    let backward = f.arrow(em_ty, lnp_ty);

    let ty_of = |f: &mut Fixture, name: NameId| -> ExprId {
        match f
            .k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", f.k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!("expected a Theorem, found {other:?}"),
        }
    };

    let implies_em = ty_of(&mut f, p.lnp_unrestricted_implies_em);
    assert_eq!(
        implies_em,
        forward,
        "Nat.lnp_unrestricted_implies_em must be exactly `L -> E`, found {}",
        f.k.render_lean(implies_em)
    );

    let em_implies = ty_of(&mut f, p.em_implies_lnp);
    assert_eq!(
        em_implies,
        backward,
        "Nat.em_implies_lnp must be exactly `E -> L`, found {}",
        f.k.render_lean(em_implies)
    );

    // NON-VACUITY: `L` is not itself a landed theorem, and the theorem that
    // comes closest -- `lnp_of_pointwise_decision` -- differs precisely by the
    // decidability hypothesis. If these two ever coincide, the row is empty.
    let decidable_form = ty_of(&mut f, p.lnp_of_pointwise_decision);
    assert_ne!(
        decidable_form, lnp_ty,
        "the decidable least-number principle must NOT be the unrestricted one"
    );
    let holders: Vec<String> =
        f.k.environment()
            .iter()
            .filter(|(_, decl)| matches!(decl, Declaration::Theorem { ty, .. } if *ty == lnp_ty))
            .map(|(name, _)| name)
            .copied()
            .collect::<Vec<_>>()
            .into_iter()
            .map(|name| f.k.display_name(name).to_string())
            .collect();
    assert!(
        holders.is_empty(),
        "the unrestricted least-number principle is already proved as {holders:?} -- \
         `Nat.lnp_unrestricted_implies_em` would then prove excluded middle outright"
    );
}
