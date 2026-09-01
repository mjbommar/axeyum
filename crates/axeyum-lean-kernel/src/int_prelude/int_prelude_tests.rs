//! Proof-term tests for the integer prelude (ADR-0042, the integer-arithmetic /
//! Diophantine reconstruction foundation).
//!
//! These tests build proof terms over the discretely-ordered commutative ring
//! `ℤ` — now *constructed* over the axiom-free `Nat` development — and
//! `infer`-check them. A test passes only if the trusted type-checker genuinely
//! accepts the proof. The headline test exercises the integer-specific
//! **discreteness** law: given `0 < x` and `x < 1`,
//! `no_int_between x (And.intro _ _ h0 h1) : False`.
//!
//! Three assertions carry the construction's weight, and each rules out a
//! different way it could be hollow:
//!
//! - [`the_operations_compute_their_normal_forms`] — the operations are the
//!   right ones. Type-checking `add_comm` does not pin `Int.add` down; a wrong
//!   `add` would satisfy a wrong-but-provable commutativity.
//! - [`derived_laws_have_no_axiom_footprint`] — the derived laws did not
//!   quietly reach for one of the laws still asserted. Only the footprint
//!   catches that; the proof would type-check either way.
//! - [`the_only_trusted_declarations_are_the_asserted_laws`] — nothing was
//!   admitted without a checked body behind the construction's back, including
//!   no `Quotient` primitive.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use super::dvd_mul_split::{split_exists_intro, split_exists_ty};
use super::ops::IntDev;
use crate::ExprId;
use crate::env::Declaration;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, IntPrelude, Kernel, LocalContext, LocalDecl, build_int_prelude};

/// A fixture: a kernel with the integer prelude plus an abstract point `x : Z`;
/// hypotheses are added per-test.
struct Fixture {
    k: Kernel,
    p: IntPrelude,
    x: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    // x : Z.
    let x = k.name_str(anon, "x");
    let z_ty = k.const_(p.z, vec![]);
    k.add_declaration(Declaration::Axiom {
        name: x,
        uparams: vec![],
        ty: z_ty,
    })
    .unwrap();
    Fixture { k, p, x }
}

impl Fixture {
    fn x_const(&mut self) -> crate::ExprId {
        self.k.const_(self.x, vec![])
    }
    /// `lt x y` as a Prop term.
    fn lt(&mut self, x: crate::ExprId, y: crate::ExprId) -> crate::ExprId {
        let ltc = self.k.const_(self.p.lt, vec![]);
        let e = self.k.app(ltc, x);
        self.k.app(e, y)
    }
    fn zero(&mut self) -> crate::ExprId {
        self.k.const_(self.p.zero, vec![])
    }
    fn one(&mut self) -> crate::ExprId {
        self.k.const_(self.p.one, vec![])
    }
    fn false_(&mut self) -> crate::ExprId {
        self.k.const_(self.p.logic.false_, vec![])
    }
    /// `And p q` as a Prop term (two explicit Prop arguments).
    fn and(&mut self, p: crate::ExprId, q: crate::ExprId) -> crate::ExprId {
        let andc = self.k.const_(self.p.logic.and, vec![]);
        let e = self.k.app(andc, p);
        self.k.app(e, q)
    }
    /// `Not r` as a Prop term.
    fn not(&mut self, r: crate::ExprId) -> crate::ExprId {
        let notc = self.k.const_(self.p.logic.not, vec![]);
        self.k.app(notc, r)
    }
    /// Declare a hypothesis axiom `name : ty` and return its const term.
    fn hyp(&mut self, name: &str, ty: crate::ExprId) -> (crate::NameId, crate::ExprId) {
        let anon = self.k.anon();
        let nm = self.k.name_str(anon, name);
        self.k
            .add_declaration(Declaration::Axiom {
                name: nm,
                uparams: vec![],
                ty,
            })
            .unwrap();
        let c = self.k.const_(nm, vec![]);
        (nm, c)
    }
}

/// The prelude admits: every axiom type-checked through the trusted gate and is
/// present in the environment as an `Axiom`. A green build of `build_int_prelude`
/// already *is* the well-formedness proof; this asserts the environment shape.
#[test]
fn int_prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // The carrier is an inductive with two constructors and a recursor; the
    // operations are checked definitions. None of these is asserted.
    for name in [p.z, p.of_nat, p.neg_succ, p.rec] {
        assert!(
            k.environment().contains(name),
            "int prelude should declare {}",
            k.display_name(name)
        );
        assert!(
            !matches!(
                k.environment().get(name).unwrap(),
                Declaration::Axiom { .. }
            ),
            "{} must not be an Axiom — the carrier is constructed",
            k.display_name(name)
        );
    }
    for name in [
        p.add,
        p.mul,
        p.pow,
        p.prod_range,
        p.factorial,
        p.inverse_index,
        p.neg,
        p.zero,
        p.one,
        p.le,
        p.lt,
        p.neg_of_nat,
        p.sub_nat_nat,
        p.ediv,
        p.emod,
        p.dvd,
        p.mod_eq,
        p.gcd,
        p.coprime,
        p.is_quadratic_residue,
        p.is_comm_ring,
    ] {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Definition { .. }
            ),
            "{} should be a checked Definition",
            k.display_name(name)
        );
    }
    for name in derived_laws(&p).into_iter().chain(derived_lemmas(&p)) {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Theorem { .. }
            ),
            "{} should be a checked Theorem",
            k.display_name(name)
        );
    }
    for name in asserted_laws(&p) {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Axiom { .. }
            ),
            "{} is not derived yet, so it should still be an Axiom",
            k.display_name(name)
        );
    }
    // The logical prelude is embedded and present.
    assert!(k.environment().contains(p.logic.false_));
    assert!(k.environment().contains(p.logic.not));
    assert!(k.environment().contains(p.logic.and));
    assert!(k.environment().contains(p.logic.and_intro));
}

/// The integer laws this development **derives** from the axiom-free `Nat`
/// prelude. Each must be a `Theorem` with an empty axiom footprint.
fn derived_laws(p: &IntPrelude) -> [crate::NameId; 263] {
    [
        p.gcd_eq_gcd_ab_witnesses,
        p.gcd_div_gcd_div_gcd,
        p.exists_gcd_one,
        p.exists_gcd_one_prime,
        p.gcd_dvd_iff,
        p.gcd_div,
        p.emod_eq_zero_iff_dvd_general,
        p.int_is_comm_ring,
        p.mul_eq_zero,
        p.fib_cassini,
        p.fib_two_mul_add_one_pos,
        p.odd_iff_nat_abs_odd,
        p.even_iff_nat_abs_even,
        p.emod_two_eq_zero_or_one,
        p.emod_two_ne_zero,
        p.emod_two_ne_one,
        p.ediv_two_mul_two_of_even,
        p.ediv_two_mul_two_add_one_of_odd,
        p.add_one_ediv_two_mul_two_of_odd,
        p.odd_of_mul_left,
        p.odd_of_mul_right,
        p.even_add,
        p.even_add_prime,
        p.even_add_one,
        p.fib_of_odd,
        p.induction_on,
        p.fib_rec,
        p.fib_add,
        p.fib_two_mul,
        p.fib_two_mul_add_two,
        p.odd_two_mul_add_one,
        p.fib_two_mul_add_one_eq_natfib_natabs,
        p.is_quadratic_residue_one,
        p.is_quadratic_residue_mul,
        p.euler_criterion_pm_one,
        p.euler_criterion_residue_imp_one,
        p.euler_criterion_neg_one_imp_not_residue,
        p.euler_unit_coprime,
        p.euler_unit_injective,
        p.euler_unit_coprime_iff,
        p.euler_unit_perm_injective,
        p.euler_unit_perm_maps_into,
        p.prod_range_if_const_eq_pow_count,
        p.prod_range_if_coprime,
        p.prod_range_if_factor_const_left,
        p.prod_range_if_modeq,
        p.euler_totient_theorem,
        p.wilson,
        p.dvd_factorial_of_le,
        p.wilson_converse,
        p.wilson_iff,
        p.factorial_interior_modeq_one,
        p.prod_range_pairing_collapse,
        p.inverse_index_fixes_zero,
        p.inverse_index_fixes_last,
        p.inverse_index_interior_fixed_point_free,
        p.factorial_zero,
        p.factorial_succ,
        p.self_inverse_mod_prime,
        p.factorial_pos,
        p.of_nat_pow,
        p.pow_prime_sub_one_modeq_one,
        p.mul_inv_of_pow,
        p.inverse_index_maps_into,
        p.inverse_index_injective,
        p.inverse_index_fixed_point,
        p.inverse_index_involutive,
        p.factorial_sq_modeq_one,
        p.prod_range_mul,
        p.prod_range_const_pow,
        p.prod_range_scaled_index_eq_pow_mul_factorial,
        p.gauss_sign_prod_eq_pow_neg_one_of_count,
        p.factorial_eq_of_nat_factorial,
        p.coprime_factorial_of_lt_prime,
        // `gauss-final` lane: `int_prelude/gauss_term_congruence.rs`,
        // `int_prelude/gauss_assembly.rs` -- item 1 and item 3 of the
        // connecting theorem (ADR-1130), i.e. Gauss's lemma itself.
        p.gauss_term_mod_eq,
        p.gauss_lemma_sign_count,
        // `second-supplementary-law` lane (ADR-1150): the second supplementary
        // law of quadratic reciprocity and the two sign lemmas it consumes.
        p.pow_neg_one_of_even,
        p.pow_neg_one_of_odd,
        p.second_supplementary_law,
        // `first-supplementary-law` lane (ADR-1230): the first supplementary
        // law's non-residue half and the `ModEq` congruence it needs.
        p.is_quadratic_residue_of_mod_eq,
        p.first_supplementary_law_not_residue,
        // `first-supplementary-residue` lane (ADR-1235): the residue half and
        // the parity-general Wilson split that supplies its witness.
        p.wilson_half_split,
        p.first_supplementary_law_residue,
        p.mod_eq_prod_range_lt,
        p.emod_neg,
        p.mod_eq_of_neg_modulus,
        p.mod_eq_neg_modulus,
        p.mod_eq_one,
        p.mod_eq_add_mul_left,
        p.add_mod_eq_left,
        p.add_mod_eq_right,
        p.mod_mod_eq,
        p.modulus_mod_eq_zero,
        p.mod_eq_sub,
        p.pow_zero,
        p.pow_succ,
        p.pow_add,
        p.pow_mul,
        p.prod_range_zero,
        p.prod_range_succ,
        p.prod_range_shift_front,
        p.prod_range_split,
        p.prod_range_congr,
        p.prod_range_congr_lt,
        p.prod_range_swap_adjacent,
        p.prod_range_swap,
        p.prod_range_permute,
        p.prod_range_if_zero,
        p.prod_range_if_succ,
        p.prod_range_if_permute,
        p.nat_abs_pow,
        p.mod_eq_pow,
        p.mod_eq_prod_range,
        p.nat_abs_mul,
        p.dvd_of_nat_abs_dvd,
        p.nat_abs_dvd_nat_abs_of_dvd,
        p.gcd_dvd_left,
        p.gcd_dvd_right,
        p.gcd_comm,
        p.gcd_one_right,
        p.gcd_zero_right,
        p.dvd_gcd,
        p.ne_zero_of_gcd,
        p.gcd_eq_one_of_gcd_mul_right_eq_one_left,
        p.gcd_eq_one_of_gcd_mul_right_eq_one_right,
        p.dvd_mul_split,
        p.gcd_eq_gcd_ab,
        p.coprime_of_bezout_one,
        p.gauss_lemma,
        p.dvd_of_dvd_mul_right_of_gcd_one,
        p.dvd_of_dvd_mul_left_of_gcd_one,
        p.gcd_greatest,
        p.euclid_lemma,
        p.euclid_infinitude,
        p.crt_exists,
        p.crt_unique,
        p.euclidean_decomposition,
        p.of_nat_nat_abs_of_nonneg,
        p.euclid_of_nat,
        p.euclid_neg_succ,
        p.ediv_add_emod,
        p.emod_nonneg,
        p.emod_lt_of_pos,
        p.emod_natabs_bound,
        p.ediv_emod_unique,
        p.ediv_emod_unique_general,
        p.dvd_refl,
        p.dvd_trans,
        p.dvd_add,
        p.dvd_mul_right,
        p.dvd_mul_left,
        p.emod_eq_zero_iff_dvd,
        p.mod_eq_refl,
        p.mod_eq_symm,
        p.mod_eq_trans,
        p.mod_eq_iff_dvd,
        p.mod_eq_of_nat_mod_eq,
        p.mod_eq_add_right,
        p.mod_eq_add_left,
        p.mod_eq_add_left_cancel,
        p.mod_eq_neg,
        p.neg_mod_eq_neg,
        p.mod_eq_of_dvd,
        p.mod_eq_dvd_iff,
        p.mod_eq_of_mul_left,
        p.mod_eq_of_mul_right,
        p.mod_eq_mul_left,
        p.mod_eq_mul_right,
        p.mod_eq_mul,
        p.mod_eq_cancel,
        p.mod_eq_inverse_exists,
        p.mod_eq_inverse_unique,
        p.mul_neg,
        p.mul_sub,
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.le_total,
        p.zero_lt_one,
        p.no_int_between,
        p.lt_of_le_of_ne,
        p.le_antisymm,
        p.add_zero,
        p.add_comm,
        p.add_assoc,
        p.add_neg,
        p.add_neg_cancel_right,
        p.add_left_neg,
        p.add_neg_eq_sub,
        p.add_left_comm,
        p.add_mul,
        p.add_neg_cancel_left,
        p.add_left_cancel,
        p.add_left_inj,
        p.add_le_add,
        p.add_lt_add_of_le_of_lt,
        p.add_le_add_left,
        p.add_le_add_right,
        p.add_le_add_iff_left,
        p.add_le_add_iff_right,
        p.add_le_add_three,
        p.add_le_iff_le_sub,
        p.add_le_of_le_neg_add,
        p.add_le_of_le_sub_left,
        p.add_le_of_le_sub_right,
        p.mul_zero,
        p.mul_one,
        p.one_mul,
        p.neg_one_mul,
        p.mul_comm,
        p.mul_assoc,
        p.left_distrib,
        p.mul_nonneg,
        p.mul_pos,
        p.sq_nonneg,
        p.mul_le_mul_of_nonneg_left,
        p.eq_em,
        p.le_of_ofnat_le_ofnat,
        p.lt_of_ofnat_lt_ofnat,
        p.le_elim,
        p.lt_elim,
        p.mul_nonneg_of_nonneg_or_nonpos,
        p.mul_nonneg_iff,
        p.mul_pos_iff,
        p.mul_neg_iff,
        p.mul_nonpos_iff,
        // `int-dvd-mirrors` lane: `int_prelude/dvd_gcd_mirrors.rs`.
        p.dvd_gcd_nat,
        p.dvd_gcd_nat_iff,
        p.dvd_coe_gcd_iff,
        p.ediv_gcd_ne_zero_of_ne_zero_left,
        p.ediv_gcd_ne_zero_if_ne_zero_right,
        p.mod_eq_add,
        p.mod_eq_add_right_cancel,
        p.mod_eq_add_left_cancel_general,
        p.mod_eq_add_right_cancel_general,
        p.mod_eq_dvd,
        p.mod_eq_emod_eq,
        p.mod_eq_mul_general,
        // `int-gcd-mul-transport` lane: `int_prelude/gcd_scaled_mirrors.rs`.
        p.dvd_gcd_mul_iff_dvd_mul,
        p.dvd_mul_gcd_iff_dvd_mul,
        p.dvd_gcd_mul_gcd_iff_dvd_mul,
        p.mod_eq_cancel_left_div_gcd,
        p.mod_eq_cancel_right_div_gcd,
        // `int-sumrange` lane: the signed finite sum (`int_prelude/sum.rs`),
        // ADR-1260's named obstruction for Eisenstein's lemma.
        p.sum_range_zero,
        p.sum_range_succ,
        p.sum_range_congr,
        p.sum_range_add,
        p.sum_range_neg,
        p.sum_range_sub,
        p.sum_range_of_nat,
        p.mod_eq_sum_range,
        p.neg_add,
        // `aggregates` lane: the function-space-indexed sum
        // (`int_prelude/sum_maps.rs`), ADR-1315.
        p.sum_range_mul_right,
        p.sum_range_mul_left,
        p.sum_maps_zero,
        p.sum_maps_succ,
        p.sum_maps_congr,
        p.sum_maps_mul_left,
        p.prod_range_sum_range_expand,
    ]
}

/// The `subNatNat` borrow sub-development, and the sign/difference lemmas built
/// on it. These are not laws of `ℤ` a reader would quote, but they are the
/// working parts of five of the laws above, and a footprint that leaked into one
/// of them would leak into the law. They are checked to exactly the same
/// standard.
fn derived_lemmas(p: &IntPrelude) -> [crate::NameId; 42] {
    [
        p.sub_nat_nat_succ_succ,
        p.sub_nat_nat_add_add,
        p.sub_nat_nat_add_add_left,
        p.sub_nat_nat_zero,
        p.zero_sub_nat_nat,
        p.sub_nat_nat_add_left,
        p.sub_nat_nat_add_right,
        p.sub_nat_nat_elim,
        p.of_nat_add_sub_nat_nat,
        p.sub_nat_nat_add_of_nat,
        p.sub_nat_nat_add_neg_succ,
        p.neg_succ_add_sub_nat_nat,
        p.of_nat_add_neg_of_nat,
        p.neg_of_nat_add_of_nat,
        p.neg_of_nat_add_neg_of_nat,
        p.neg_of_nat_add_sub_nat_nat,
        p.mul_of_nat_neg_of_nat,
        p.mul_neg_of_nat_of_nat,
        p.mul_neg_succ_neg_of_nat,
        p.mul_neg_of_nat_neg_succ,
        p.of_nat_mul_sub_nat_nat,
        p.neg_succ_mul_sub_nat_nat,
        p.le_of_nat_add,
        p.le_dest,
        p.lt_of_nat_add,
        p.lt_dest,
        // Found by `every_int_declaration_is_checked_and_axiom_free`'s
        // coverage assertion, not by anyone noticing: these two `natAbs`
        // theorems were live and unlisted here, so no test ever checked their
        // axiom footprint.
        p.nat_abs_neg_of_nat,
        p.nat_abs_neg,
        // `score-the-blind-population` lane: the held-out
        // `integer-absolute-value` family's four `natAbs_inj_of_*` mirrors
        // (`int_prelude/nat_abs_mirrors.rs`).
        p.nat_abs_inj_of_nonneg_of_nonneg,
        p.nat_abs_inj_of_nonpos_of_nonpos,
        p.nat_abs_inj_of_nonneg_of_nonpos,
        p.nat_abs_inj_of_nonpos_of_nonneg,
        // Base case theorems for Int.fib, added by int-fib-base lane
        p.fib_zero,
        p.fib_one,
        p.fib_two,
        p.fib_neg_one,
        p.fib_neg_two,
        // `int-prime-dvd` lane: `ml430` mirrors built directly from
        // `euclid_lemma` and pre-existing `Nat` lemmas
        // (`int_prelude/prime_dvd_mul_mirrors.rs`).
        p.prime_dvd_mul_prime,
        p.prime_dvd_mul,
        p.not_prime_of_int_mul,
        p.gcd_ne_one_iff_gcd_mul_right_ne_one,
        p.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul,
    ]
}

/// The primitive `Int` operations and predicates themselves -- `Definition`s,
/// not derived theorems, but exactly as capable of leaking an axiom footprint
/// (a `Definition`'s value is a checked term too). Found missing entirely by
/// `every_int_declaration_is_checked_and_axiom_free`'s coverage assertion:
/// unlike `nat_prelude_tests.rs`, this file had no `definition_names`
/// counterpart to `derived_laws`/`derived_lemmas` at all, so none of these
/// twenty-two had ever had their footprint checked.
fn definition_names(p: &IntPrelude) -> [crate::NameId; 30] {
    [
        p.fib,
        p.even,
        p.odd,
        p.neg_of_nat,
        p.sub_nat_nat,
        p.add,
        p.mul,
        p.neg,
        p.sub,
        p.zero,
        p.one,
        p.le,
        p.lt,
        p.pow,
        p.prod_range,
        p.sum_range,
        p.prod_range_if,
        p.ediv,
        p.emod,
        p.dvd,
        p.mod_eq,
        p.nat_abs,
        p.gcd,
        p.coprime,
        p.is_comm_ring,
        p.factorial,
        p.is_quadratic_residue,
        p.gcd_a,
        p.gcd_b,
        p.sum_maps,
    ]
}

/// The integer laws still **asserted**. This list was the lane's standing debt;
/// it is expected to shrink and must never grow.
///
/// It is now **empty**: `Int.euclidean_decomposition` was the last member, and
/// it is a theorem as of 2026-08-16. An entry reappearing here is a regression —
/// something previously proved has become an assumption.
fn asserted_laws(_p: &IntPrelude) -> [crate::NameId; 0] {
    []
}

/// Every derived law's trusted closure is **empty** — not merely "smaller".
/// A theorem that silently reached for one of the remaining assumptions would
/// still type-check; only the footprint catches it.
#[test]
fn derived_laws_have_no_axiom_footprint() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in derived_laws(&p).into_iter().chain(derived_lemmas(&p)) {
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} should rest on no axiom, but rests on {:?}",
            k.display_name(name),
            footprint
                .iter()
                .map(|a| k.display_name(*a).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// COVERAGE, checked against the ENVIRONMENT rather than against
/// `derived_laws`/`derived_lemmas` themselves.
///
/// Without this, `derived_laws_have_no_axiom_footprint` only ever inspects the
/// declarations someone remembered to list in those two functions. A
/// `Definition` or `Theorem` declared under `Int.` and omitted from both lists
/// receives no axiom-footprint check at all -- and every run stays green,
/// because a list cannot notice what is missing from it. Mirrors
/// `every_creal_declaration_is_checked_and_axiom_free` (`creal_tests.rs`) and
/// `every_nat_declaration_is_checked_and_axiom_free` (`nat_prelude_tests.rs`),
/// both landed after exactly this gap was found in `creal`.
///
/// Scoped to `Definition`/`Theorem` kinds deliberately: the inductive
/// machinery (`Int`, `Int.ofNat`, `Int.negSucc`, `Int.rec`) is checked by name
/// at line 109 instead, and it has no proof term for `axiom_footprint` to
/// inspect the way a `Definition`'s value or a `Theorem`'s proof does.
#[test]
fn every_int_declaration_is_checked_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let listed: std::collections::BTreeSet<crate::NameId> = derived_laws(&p)
        .into_iter()
        .chain(derived_lemmas(&p))
        .chain(asserted_laws(&p))
        .chain(definition_names(&p))
        .collect();
    let declared: Vec<(crate::NameId, Declaration)> = k
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
            ) && k.display_name(*name).to_string().starts_with("Int.")
                && !listed.contains(name)
        })
        .map(|(name, _)| k.display_name(*name).to_string())
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `Int` definitions/theorems are live in the prelude but absent \
         from `derived_laws`/`derived_lemmas`/`asserted_laws`/`definition_names`, \
         so nothing \
         checks their axiom-footprint: {unlisted:?}. Add them there -- do not \
         delete this assertion."
    );

    for (name, decl) in &declared {
        let shown = k.display_name(*name).to_string();
        if !shown.starts_with("Int.") || !listed.contains(name) {
            continue;
        }
        if matches!(decl, Declaration::Axiom { .. }) {
            // `asserted_laws` legitimately holds axioms; the axiom-freedom
            // check below applies only to the derived laws/lemmas.
            continue;
        }
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

/// The environment carries exactly the asserted laws and nothing else that was
/// admitted without a proof: no axioms crept in, and no `Quotient` primitive
/// was admitted (the reason `Int` is a normalized inductive rather than a
/// setoid quotient of `ℕ × ℕ`).
#[test]
fn the_only_trusted_declarations_are_the_asserted_laws() {
    use std::collections::BTreeSet;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let expected: BTreeSet<_> = asserted_laws(&p).into_iter().collect();
    let mut found = BTreeSet::new();
    for (_, declaration) in k.environment().iter() {
        match declaration {
            Declaration::Axiom { name, .. } => {
                found.insert(*name);
            }
            Declaration::Opaque { name, .. } | Declaration::Quotient { name, .. } => {
                panic!(
                    "{} was admitted without a checked proof body",
                    k.display_name(*name)
                );
            }
            _ => {}
        }
    }
    let unexpected: Vec<_> = found
        .difference(&expected)
        .map(|n| k.display_name(*n).to_string())
        .collect();
    assert!(unexpected.is_empty(), "unexpected axioms: {unexpected:?}");
    let missing: Vec<_> = expected
        .difference(&found)
        .map(|n| k.display_name(*n).to_string())
        .collect();
    assert!(missing.is_empty(), "asserted law not declared: {missing:?}");
}

/// Every axiom's *type* itself infers to a `Sort` — i.e. the whole axiom set is
/// well-formed (the trusted admission gate already enforced this, but we
/// re-check the types infer with no error).
#[test]
fn every_axiom_type_infers_to_a_sort() {
    use crate::expr::ExprNode;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in [
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.add_le_add,
        p.add_comm,
        p.add_assoc,
        p.add_zero,
        p.add_neg,
        p.add_neg_cancel_right,
        p.add_lt_add_of_le_of_lt,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
        p.mul_comm,
        p.mul_assoc,
        p.mul_one,
        p.one_mul,
        p.neg_one_mul,
        p.mul_zero,
        p.left_distrib,
        p.mul_nonneg,
        p.no_int_between,
        p.le_total,
        p.lt_of_le_of_ne,
        p.euclidean_decomposition,
        p.eq_em,
    ] {
        let ty = k.environment().get(name).unwrap().ty();
        let inferred = k.infer(ty).unwrap();
        assert!(
            matches!(k.expr_node(inferred), ExprNode::Sort(_)),
            "axiom {} type should infer to a Sort",
            k.display_name(name)
        );
    }
}

/// **`no_int_between` applied**: `no_int_between x : Not (And (lt zero x)
/// (lt x one))`. We build a fresh `x : Z` const, apply `no_int_between` to it,
/// `infer`, and `def_eq`-check the inferred type against the expected
/// `Not (And (lt zero x) (lt x one))`. (Mirrors `arith_prelude`'s
/// `lt_irrefl_applied_checks`.)
#[test]
fn no_int_between_applied_checks() {
    let mut f = fixture();
    let x = f.x_const();

    // proof := no_int_between x.
    let nib = f.k.const_(f.p.no_int_between, vec![]);
    let proof = f.k.app(nib, x);
    let inferred = f.k.infer(proof).unwrap();

    // Expected: Not (And (lt zero x) (lt x one)).
    let zero = f.zero();
    let x2 = f.x_const();
    let lt_0x = f.lt(zero, x2);
    let x3 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x3, one);
    let conj = f.and(lt_0x, lt_x1);
    let expected = f.not(conj);
    assert!(
        f.k.def_eq(inferred, expected),
        "no_int_between x : Not (And (lt zero x) (lt x one))"
    );
}

/// **discreteness refutation** — the integer-specific content: given
/// `h0 : lt zero x` and `h1 : lt x one`, the term
/// `no_int_between x (And.intro (lt zero x) (lt x one) h0 h1)` infers to `False`.
/// The conjunction is built with the logic prelude's `And.intro`, which takes the
/// two Prop arguments explicitly (`And.intro P Q hp hq : And P Q`), and
/// `no_int_between x : Not (And …)` unfolds to `And … → False`, so the whole term
/// is `False`.
#[test]
fn discreteness_refutes_zero_lt_x_lt_one() {
    let mut f = fixture();

    // Hypotheses h0 : lt zero x, h1 : lt x one.
    let zero = f.zero();
    let x = f.x_const();
    let lt_0x = f.lt(zero, x);
    let x2 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x2, one);
    let (_, h0) = f.hyp("h0", lt_0x);
    let (_, h1) = f.hyp("h1", lt_x1);

    // and_proof := And.intro (lt zero x) (lt x one) h0 h1 : And (lt zero x)(lt x one).
    let zero2 = f.zero();
    let x3 = f.x_const();
    let p_prop = f.lt(zero2, x3); // lt zero x
    let x4 = f.x_const();
    let one2 = f.one();
    let q_prop = f.lt(x4, one2); // lt x one
    let and_proof = {
        let intro = f.k.const_(f.p.logic.and_intro, vec![]);
        let e = f.k.app(intro, p_prop);
        let e = f.k.app(e, q_prop);
        let e = f.k.app(e, h0);
        f.k.app(e, h1)
    };

    // proof := no_int_between x and_proof : False.
    let x5 = f.x_const();
    let proof = {
        let nib = f.k.const_(f.p.no_int_between, vec![]);
        let e = f.k.app(nib, x5); // no_int_between x : Not (And …)
        f.k.app(e, and_proof) // applied to (And …) ⇒ False
    };
    let inferred = f.k.infer(proof).unwrap();
    let false_ = f.false_();
    assert!(
        f.k.def_eq(inferred, false_),
        "no_int_between x (And.intro … h0 h1) : False"
    );
}

/// ADR-0104's trusted theorem has the exact quotient/remainder proposition:
/// applying it to `x`, modulus `1`, and `zero_lt_one` produces
/// `Exists q r, x = 1*q+r ∧ 0≤r ∧ r<1`.
#[test]
fn euclidean_decomposition_applied_checks_exact_type() {
    use crate::BinderInfo;

    let mut f = fixture();
    let x = f.x_const();
    let one = f.one();
    let theorem = f.k.const_(f.p.euclidean_decomposition, vec![]);
    let proof = f.k.app(theorem, x);
    let proof = f.k.app(proof, one);
    let positive = f.k.const_(f.p.zero_lt_one, vec![]);
    let proof = f.k.app(proof, positive);
    let inferred = f.k.infer(proof).unwrap();

    let q_id = 20_000;
    let r_id = 20_001;
    let q = f.k.fvar(q_id);
    let r = f.k.fvar(r_id);
    let mul = f.k.const_(f.p.mul, vec![]);
    let one = f.one();
    let one_q = f.k.app(mul, one);
    let one_q = f.k.app(one_q, q);
    let add = f.k.const_(f.p.add, vec![]);
    let sum = f.k.app(add, one_q);
    let sum = f.k.app(sum, r);
    let zero_level = f.k.level_zero();
    let one_level = f.k.level_succ(zero_level);
    let eq = f.k.const_(f.p.logic.eq, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let recomposition = f.k.app(eq, z_ty);
    let x = f.x_const();
    let recomposition = f.k.app(recomposition, x);
    let recomposition = f.k.app(recomposition, sum);
    let le = f.k.const_(f.p.le, vec![]);
    let zero = f.zero();
    let nonnegative = f.k.app(le, zero);
    let nonnegative = f.k.app(nonnegative, r);
    let r_again = f.k.fvar(r_id);
    let one = f.one();
    let below_one = f.lt(r_again, one);
    let bounds = f.and(nonnegative, below_one);
    let facts = f.and(recomposition, bounds);

    let anon = f.k.anon();
    let r_body = f.k.abstract_fvars(facts, &[r_id]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let r_pred = f.k.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists = f.k.const_(f.p.logic.exists_, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let exists_r = f.k.app(exists, z_ty);
    let exists_r = f.k.app(exists_r, r_pred);
    let q_body = f.k.abstract_fvars(exists_r, &[q_id]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let q_pred = f.k.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists = f.k.const_(f.p.logic.exists_, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let expected = f.k.app(exists, z_ty);
    let expected = f.k.app(expected, q_pred);

    assert!(
        f.k.def_eq(inferred, expected),
        "euclidean_decomposition x one zero_lt_one has the exact residue type"
    );
}

/// ADR-0106 exposes decidability only for integer equality, not unrestricted
/// propositional excluded middle.
#[test]
fn integer_equality_decidability_applied_checks_exact_type() {
    let mut f = fixture();
    let x = f.x_const();
    let zero = f.zero();
    let theorem = f.k.const_(f.p.eq_em, vec![]);
    let proof = f.k.app(theorem, x);
    let proof = f.k.app(proof, zero);
    let inferred = f.k.infer(proof).unwrap();

    let zero_level = f.k.level_zero();
    let one_level = f.k.level_succ(zero_level);
    let eq = f.k.const_(f.p.logic.eq, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let equality = f.k.app(eq, z_ty);
    let x = f.x_const();
    let equality = f.k.app(equality, x);
    let zero = f.zero();
    let equality = f.k.app(equality, zero);
    let not = f.k.const_(f.p.logic.not, vec![]);
    let not_equality = f.k.app(not, equality);
    let or = f.k.const_(f.p.logic.or, vec![]);
    let expected = f.k.app(or, equality);
    let expected = f.k.app(expected, not_equality);
    assert!(
        f.k.def_eq(inferred, expected),
        "eq_em x zero has exactly Eq-or-Not-Eq type"
    );
}

/// Determinism: building the prelude twice yields identical `IntPrelude` (same
/// dense ids), since interning is insertion-ordered.
#[test]
fn build_is_deterministic() {
    let mut k1 = Kernel::new();
    let p1 = build_int_prelude(&mut k1).expect("Int prelude must build");
    let mut k2 = Kernel::new();
    let p2 = build_int_prelude(&mut k2).expect("Int prelude must build");
    assert_eq!(p1, p2, "IntPrelude ids are deterministic");
}

/// `Int.ofNat n` for `n ≥ 0` and `Int.negSucc (-n-1)` for `n < 0` — the unique
/// normal form of the integer `n`.
fn numeral(k: &mut Kernel, p: &IntPrelude, n: i32) -> crate::ExprId {
    let magnitude = if n >= 0 {
        u32::try_from(n).expect("non-negative")
    } else {
        u32::try_from(-n - 1).expect("negative")
    };
    let mut nat = k.const_(p.nat.zero, vec![]);
    for _ in 0..magnitude {
        let succ = k.const_(p.nat.succ, vec![]);
        nat = k.app(succ, nat);
    }
    let ctor = if n >= 0 { p.of_nat } else { p.neg_succ };
    let c = k.const_(ctor, vec![]);
    k.app(c, nat)
}

/// The raw `Nat` numeral `n` (a `zero`/`succ` chain), unwrapped by `Int.ofNat`
/// — for building `Nat.le`/`Nat.lt` witnesses directly.
fn numeral_nat(k: &mut Kernel, p: &IntPrelude, n: u32) -> crate::ExprId {
    let mut nat = k.const_(p.nat.zero, vec![]);
    for _ in 0..n {
        let succ = k.const_(p.nat.succ, vec![]);
        nat = k.app(succ, nat);
    }
    nat
}

/// The construction **computes**. Type-checking the ring laws does not pin the
/// operations down — a wrong `Int.add` would still satisfy a wrong-but-provable
/// `add_comm` — so every case of every operation is evaluated against its
/// normal form here, including the borrow cases where `subNatNat` has to decide
/// which constructor the answer lands in.
#[test]
fn the_operations_compute_their_normal_forms() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let binary = [
        (p.add, 2, 3, 5),
        (p.add, 2, -1, 1),
        (p.add, 1, -3, -2),
        (p.add, -1, 2, 1),
        (p.add, -2, -3, -5),
        (p.add, 3, -3, 0),
        (p.add, -3, 3, 0),
        (p.add, 0, 0, 0),
        (p.add, 0, -4, -4),
        (p.mul, 2, 3, 6),
        (p.mul, 2, -3, -6),
        (p.mul, -2, 3, -6),
        (p.mul, -2, -3, 6),
        (p.mul, 0, -3, 0),
        (p.mul, -3, 0, 0),
        (p.mul, 1, -4, -4),
    ];
    for (operation, left, right, expected) in binary {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(operation, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "{} {left} {right} should be {expected}",
            k.display_name(operation)
        );
    }

    for (input, expected) in [(0, 0), (3, -3), (-3, 3), (1, -1), (-1, 1)] {
        let a = numeral(&mut k, &p, input);
        let f = k.const_(p.neg, vec![]);
        let applied = k.app(f, a);
        let want = numeral(&mut k, &p, expected);
        assert!(k.def_eq(applied, want), "neg {input} should be {expected}");
    }

    // The two constants are the normal forms they claim to be.
    let zero = k.const_(p.zero, vec![]);
    let want = numeral(&mut k, &p, 0);
    assert!(k.def_eq(zero, want), "Int.zero is Int.ofNat 0");
    let one = k.const_(p.one, vec![]);
    let want = numeral(&mut k, &p, 1);
    assert!(k.def_eq(one, want), "Int.one is Int.ofNat 1");
}

/// `Int.prodRange` computes its normal form — `prodRange (fun _ => 2) 3`
/// reduces to `8` by β/δ/ι, the same computational claim
/// [`the_operations_compute_their_normal_forms`] makes for the ring
/// operations — and, symmetrically, the trusted gate REJECTS the false claim
/// that the same product is `7`. A checker that only ever confirms a
/// computation is a checker that cannot fail; this pairs the positive with a
/// negative the kernel must refuse.
#[test]
fn prod_range_computes_and_rejects_a_false_product() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // f := fun (_ : Nat) => 2, so prodRange f 3 = 2 * 2 * 2 = 8.
    let two = numeral(&mut k, &p, 2);
    let f = k.lam(anon, nat_ty, two, BinderInfo::Default);
    let three = numeral_nat(&mut k, &p, 3);
    let prod_range = k.const_(p.prod_range, vec![]);
    let applied_f = k.app(prod_range, f);
    let lhs = k.app(applied_f, three);

    let eight = numeral(&mut k, &p, 8);
    assert!(
        k.def_eq(lhs, eight),
        "prodRange (fun _ => 2) 3 should compute to 8"
    );

    // Negative control: the trusted gate must REFUSE the false claim that
    // `prodRange (fun _ => 2) 3 = 7`. Build the (mis-typed) proof the same
    // way `int_theorem`/`declare_theorem` build every real theorem in this
    // module — a `Theorem` declaration whose `value` the kernel re-checks
    // against `ty` — so a bug that made this pass would be the same bug that
    // could smuggle a false theorem into the prelude itself.
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let seven = numeral(&mut k, &p, 7);
    let int_ty = k.const_(p.z, vec![]);
    let eq = k.const_(p.logic.eq, vec![level_one]);
    let false_stmt = {
        let e = k.app(eq, int_ty);
        let e = k.app(e, lhs);
        k.app(e, seven)
    };
    let refl = k.const_(p.logic.eq_refl, vec![level_one]);
    // `Eq.refl Int 8` genuinely proves `Eq Int 8 8`, not `Eq Int lhs 7` — the
    // kernel must catch the mismatch, not merely trust the annotation.
    let false_proof = {
        let r = k.app(refl, int_ty);
        k.app(r, eight)
    };
    let scratch_name = k.name_str(anon, "prod_range_false_claim_scratch");
    let result = k.add_declaration(Declaration::Theorem {
        name: scratch_name,
        uparams: vec![],
        ty: false_stmt,
        value: false_proof,
    });
    assert!(
        result.is_err(),
        "the trusted gate accepted a false claim that prodRange (fun _ => 2) 3 = 7"
    );
}

/// `Int.prodRange_const_pow` applied at concrete `a := 3, n := 4` proves a
/// statement that itself computes to `81 = 81` on both sides -- the
/// symbolic proof term (fully general over `a`, `n`) is checked by kernel
/// admission (the general theorem is declared axiom-free), and this test is
/// the complementary concrete-instantiation check the standing rule asks
/// for: a symbolic accept can hide a defeq-shaped gap that only a concrete
/// reduction exposes, and a concrete-only check can hide a chain that does
/// not compose symbolically. Both together, per CLAUDE.md's Gotchas.
#[test]
fn prod_range_const_pow_matches_direct_computation() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);
    let three = numeral(&mut k, &p, 3);
    let four_n = numeral_nat(&mut k, &p, 4);

    let lemma = k.const_(p.prod_range_const_pow, vec![]);
    let lemma_a = k.app(lemma, three);
    let applied = k.app(lemma_a, four_n);
    let inferred = k
        .infer(applied)
        .expect("prod_range_const_pow must apply at concrete a, n");

    // The instantiated statement is `Eq Int (prodRange (fun _ => 3) 4) (pow
    // 3 4)`; build that expected shape directly and confirm the general
    // theorem's application infers exactly it.
    let three_lambda = k.lam(anon, nat_ty, three, BinderInfo::Default);
    let prod_range_c = k.const_(p.prod_range, vec![]);
    let prod_range_f = k.app(prod_range_c, three_lambda);
    let lhs_direct = k.app(prod_range_f, four_n);
    let pow_c = k.const_(p.pow, vec![]);
    let pow_a = k.app(pow_c, three);
    let rhs_direct = k.app(pow_a, four_n);
    let int_ty = k.const_(p.z, vec![]);
    let eq_c = k.const_(p.logic.eq, vec![level_one]);
    let expected = {
        let e = k.app(eq_c, int_ty);
        let e = k.app(e, lhs_direct);
        k.app(e, rhs_direct)
    };
    assert!(
        k.def_eq(inferred, expected),
        "prod_range_const_pow's instantiated type must match the direct \
         prodRange/pow application at a := 3, n := 4"
    );

    // And both sides genuinely compute to the SAME concrete numeral --
    // 3*3*3*3 = 81 = 3^4 -- so this is not merely a defeq-shaped statement
    // that could paper over a wrong `pow`/`prodRange` pairing.
    let eighty_one = numeral(&mut k, &p, 81);
    assert!(
        k.def_eq(lhs_direct, eighty_one),
        "prodRange (fun _ => 3) 4 should compute to 81"
    );
    assert!(
        k.def_eq(rhs_direct, eighty_one),
        "pow 3 4 should compute to 81"
    );
}

/// `Int.prodRangeIf` computes its normal form -- and, unlike a constant `f`
/// or an always-true/always-false predicate, this one MIXES both branches of
/// `bool_select_int` in one run, so a definition that dropped the predicate
/// entirely (e.g. always folding `f`, `Nat.lor`'s absorbing-zero mistake in
/// spirit) would not survive it. `pred i := Nat.beq i 2`, `f i := Int.ofNat
/// (Nat.succ i)`, `n := 4`: `i=0,1,3` are excluded (contribute `1`), `i=2` is
/// included and contributes `f 2 = 3`, so `prodRangeIf pred f 4` should
/// reduce to `3`. The trusted gate must also REFUSE the false claim that the
/// same product is `2` -- the same discriminating-negative-control pattern
/// as [`prod_range_computes_and_rejects_a_false_product`], so this checker
/// cannot pass vacuously.
#[test]
fn prod_range_if_computes_and_rejects_a_false_value() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);
    let bool_ty = k.const_(p.logic.bool_, vec![]);

    // pred := fun i => Nat.beq i 2.
    let pred = {
        let i_fv = 900_300;
        let i = k.fvar(i_fv);
        let two_nat = numeral_nat(&mut k, &p, 2);
        let beq = k.const_(p.nat.beq, vec![]);
        let applied = k.app(beq, i);
        let body = k.app(applied, two_nat);
        let abstracted = k.abstract_fvars(body, &[i_fv]);
        k.lam(anon, nat_ty, abstracted, BinderInfo::Default)
    };
    // f := fun i => Int.ofNat (Nat.succ i).
    let f = {
        let i_fv = 900_301;
        let i = k.fvar(i_fv);
        let succ = k.const_(p.nat.succ, vec![]);
        let succ_i = k.app(succ, i);
        let of_nat = k.const_(p.of_nat, vec![]);
        let body = k.app(of_nat, succ_i);
        let abstracted = k.abstract_fvars(body, &[i_fv]);
        k.lam(anon, nat_ty, abstracted, BinderInfo::Default)
    };
    let four = numeral_nat(&mut k, &p, 4);
    let prod_range_if = k.const_(p.prod_range_if, vec![]);
    let applied_pred = k.app(prod_range_if, pred);
    let applied_f = k.app(applied_pred, f);
    let lhs = k.app(applied_f, four);

    let three = numeral(&mut k, &p, 3);
    assert!(
        k.def_eq(lhs, three),
        "prodRangeIf (beq _ 2) (ofNat . succ) 4 should compute to 3"
    );

    let _ = bool_ty; // predicate's codomain, used only for documentation above

    // Negative control: the trusted gate must REFUSE the false claim that
    // the same product is `2`.
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let two_int = numeral(&mut k, &p, 2);
    let int_ty = k.const_(p.z, vec![]);
    let eq = k.const_(p.logic.eq, vec![level_one]);
    let false_stmt = {
        let e = k.app(eq, int_ty);
        let e = k.app(e, lhs);
        k.app(e, two_int)
    };
    let refl = k.const_(p.logic.eq_refl, vec![level_one]);
    let false_proof = {
        let r = k.app(refl, int_ty);
        k.app(r, three)
    };
    let scratch_name = k.name_str(anon, "prod_range_if_false_claim_scratch");
    let result = k.add_declaration(Declaration::Theorem {
        name: scratch_name,
        uparams: vec![],
        ty: false_stmt,
        value: false_proof,
    });
    assert!(
        result.is_err(),
        "the trusted gate accepted a false claim that prodRangeIf (beq _ 2) (ofNat . succ) 4 = 2"
    );
}

/// `Int.prodRangeIf_constEqPowCount` applied at a DISCRIMINATING concrete
/// instance -- `pred i := Nat.ble i 1` (true at `i ∈ {0,1}`, false at
/// `i ∈ {2,3,4}`), `a := 2`, `n := 5` -- so the count is `2`, not `1`: an
/// off-by-one in the exponent (the single most likely defect in an
/// induction pairing `Int.pow`/`Nat.countRange`) would be caught, unlike a
/// count-of-1 instance where `pow a 1 = a` coincides with `a` itself.
/// `prodRangeIf pred (fun _ => 2) 5` folds `2 * 2 * 1 * 1 * 1 = 4`, and
/// `pow 2 (countRange pred 5) = pow 2 2 = 4` independently. The trusted gate
/// must also REFUSE the false claim that the same product is `8` (`pow 2
/// 3`, the off-by-one this instance is chosen to catch) -- the same
/// discriminating-negative-control pattern as
/// [`prod_range_if_computes_and_rejects_a_false_value`].
#[test]
fn prod_range_if_const_eq_pow_count_computes_and_rejects_an_off_by_one_exponent() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // pred := fun i => Nat.ble i 1.
    let pred = {
        let i_fv = 900_400;
        let i = k.fvar(i_fv);
        let one_nat = numeral_nat(&mut k, &p, 1);
        let ble = k.const_(p.nat.ble, vec![]);
        let applied = k.app(ble, i);
        let body = k.app(applied, one_nat);
        let abstracted = k.abstract_fvars(body, &[i_fv]);
        k.lam(anon, nat_ty, abstracted, BinderInfo::Default)
    };
    let two_int = numeral(&mut k, &p, 2);
    let five = numeral_nat(&mut k, &p, 5);

    let lemma = k.const_(p.prod_range_if_const_eq_pow_count, vec![]);
    let lemma_pred = k.app(lemma, pred);
    let lemma_pred_a = k.app(lemma_pred, two_int);
    let applied = k.app(lemma_pred_a, five);
    let inferred = k
        .infer(applied)
        .expect("prod_range_if_const_eq_pow_count must apply at concrete pred, a, n");

    // Build the statement's LHS/RHS directly and confirm the general
    // theorem's application infers exactly that shape, then confirm both
    // sides compute to the SAME concrete numeral (4), independently.
    let two_lambda = k.lam(anon, nat_ty, two_int, BinderInfo::Default);
    let one_i = k.const_(p.one, vec![]);
    let selector = {
        let i_fv = 900_401;
        let i = k.fvar(i_fv);
        let pred_i = k.app(pred, i);
        let two_val = k.app(two_lambda, i);
        let level_one_local = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let bool_rec = k.const_(p.logic.bool_rec, vec![level_one_local]);
        let bool_ty_local = k.const_(p.logic.bool_, vec![]);
        let anon2 = k.anon();
        let int_ty_local = k.const_(p.z, vec![]);
        let motive = k.lam(anon2, bool_ty_local, int_ty_local, BinderInfo::Default);
        let with_motive = k.app(bool_rec, motive);
        let with_false = k.app(with_motive, one_i);
        let with_true = k.app(with_false, two_val);
        let body = k.app(with_true, pred_i);
        let abstracted = k.abstract_fvars(body, &[i_fv]);
        k.lam(anon2, nat_ty, abstracted, BinderInfo::Default)
    };
    let prod_range_c = k.const_(p.prod_range, vec![]);
    let prod_range_sel = k.app(prod_range_c, selector);
    let lhs_direct = k.app(prod_range_sel, five);

    let count_range_c = k.const_(p.nat.count_range, vec![]);
    let count_range_pred = k.app(count_range_c, pred);
    let count5 = k.app(count_range_pred, five);
    let pow_c = k.const_(p.pow, vec![]);
    let pow_a = k.app(pow_c, two_int);
    let rhs_direct = k.app(pow_a, count5);

    let int_ty = k.const_(p.z, vec![]);
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let eq_c = k.const_(p.logic.eq, vec![level_one]);
    let expected = {
        let e = k.app(eq_c, int_ty);
        let e = k.app(e, lhs_direct);
        k.app(e, rhs_direct)
    };
    assert!(
        k.def_eq(inferred, expected),
        "prod_range_if_const_eq_pow_count's instantiated type must match the \
         direct prodRangeIf/pow application"
    );

    let four = numeral(&mut k, &p, 4);
    assert!(
        k.def_eq(lhs_direct, four),
        "prodRangeIf (ble _ 1) (fun _ => 2) 5 should compute to 4"
    );
    assert!(
        k.def_eq(rhs_direct, four),
        "pow 2 (countRange (ble _ 1) 5) should compute to 4"
    );

    // Negative control: the trusted gate must REFUSE the false claim that
    // the same product is `8` (the off-by-one exponent `pow 2 3` would give).
    let eight = numeral(&mut k, &p, 8);
    let false_stmt = {
        let e = k.app(eq_c, int_ty);
        let e = k.app(e, lhs_direct);
        k.app(e, eight)
    };
    let refl = k.const_(p.logic.eq_refl, vec![level_one]);
    let false_proof = {
        let r = k.app(refl, int_ty);
        k.app(r, four)
    };
    let scratch_name = k.name_str(anon, "prod_range_if_const_eq_pow_count_false_claim_scratch");
    let result = k.add_declaration(Declaration::Theorem {
        name: scratch_name,
        uparams: vec![],
        ty: false_stmt,
        value: false_proof,
    });
    assert!(
        result.is_err(),
        "the trusted gate accepted a false claim that prodRangeIf (ble _ 1) (fun _ => 2) 5 = 8"
    );
}

/// `Int.gaussSignProdEqPowNegOneOfCount` at `pp := 11, a := 2, m := 5` --
/// `leastResidue 11 2 k` for `k = 1..5` is `2, 4, 6, 8, 10`, and the
/// threshold is `succ (div 11 2) = 6`, so `gaussSignNeg` is `false, false,
/// true, true, true` -- `gaussNegCount 11 2 5 = 3` (ODD, so the sign
/// product genuinely is `-1`, not `+1` as an even count OR an unrelated
/// wrong formula would give). Checks the intermediate count, the direct
/// sign-product computation, AND that the general theorem's instantiation
/// at these same concrete args matches the direct computation exactly.
#[test]
fn gauss_sign_prod_eq_pow_neg_one_of_count_matches_direct_computation_at_pp_11_a_2_m_5() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    let pp = numeral_nat(&mut k, &p, 11);
    let a = numeral_nat(&mut k, &p, 2);
    let m = numeral_nat(&mut k, &p, 5);

    // pred := fun j => Nat.gaussSignNeg pp a (succ j).
    let pred = {
        let j_fv = 900_500;
        let j = k.fvar(j_fv);
        let succ = k.const_(p.nat.succ, vec![]);
        let sj = k.app(succ, j);
        let gsn = k.const_(p.nat.gauss_sign_neg, vec![]);
        let g1 = k.app(gsn, pp);
        let g2 = k.app(g1, a);
        let body = k.app(g2, sj);
        let abstracted = k.abstract_fvars(body, &[j_fv]);
        k.lam(anon, nat_ty, abstracted, BinderInfo::Default)
    };

    let neg_one = numeral(&mut k, &p, -1);
    let one_i = k.const_(p.one, vec![]);
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };

    // selector := fun j => bool_select_int (pred j) (-1) 1.
    let selector = {
        let j_fv = 900_501;
        let j = k.fvar(j_fv);
        let pj = k.app(pred, j);
        let bool_rec = k.const_(p.logic.bool_rec, vec![level_one]);
        let bool_ty_local = k.const_(p.logic.bool_, vec![]);
        let anon2 = k.anon();
        let int_ty_local = k.const_(p.z, vec![]);
        let motive = k.lam(anon2, bool_ty_local, int_ty_local, BinderInfo::Default);
        let with_motive = k.app(bool_rec, motive);
        let with_false = k.app(with_motive, one_i);
        let with_true = k.app(with_false, neg_one);
        let body = k.app(with_true, pj);
        let abstracted = k.abstract_fvars(body, &[j_fv]);
        k.lam(anon2, nat_ty, abstracted, BinderInfo::Default)
    };

    let prod_range_c = k.const_(p.prod_range, vec![]);
    let prod_range_sel = k.app(prod_range_c, selector);
    let lhs_direct = k.app(prod_range_sel, m);

    let gnc = k.const_(p.nat.gauss_neg_count, vec![]);
    let gnc1 = k.app(gnc, pp);
    let gnc2 = k.app(gnc1, a);
    let count = k.app(gnc2, m);
    let pow_c = k.const_(p.pow, vec![]);
    let pow_neg1 = k.app(pow_c, neg_one);
    let rhs_direct = k.app(pow_neg1, count);

    let three_nat = numeral_nat(&mut k, &p, 3);
    assert!(
        k.def_eq(count, three_nat),
        "gaussNegCount 11 2 5 should compute to 3"
    );
    assert!(
        k.def_eq(lhs_direct, neg_one),
        "the sign product at pp=11, a=2, m=5 should compute to -1"
    );
    assert!(
        k.def_eq(rhs_direct, neg_one),
        "pow (-1) (gaussNegCount 11 2 5) should compute to -1 (count = 3, odd)"
    );

    // The general theorem, applied at these same concrete args, must agree
    // with the direct computation -- not merely that both separately
    // reduce to -1.
    let lemma = k.const_(p.gauss_sign_prod_eq_pow_neg_one_of_count, vec![]);
    let l1 = k.app(lemma, pp);
    let l2 = k.app(l1, a);
    let applied = k.app(l2, m);
    let inferred = k
        .infer(applied)
        .expect("gauss_sign_prod_eq_pow_neg_one_of_count must apply at concrete pp, a, m");
    let eq_c = k.const_(p.logic.eq, vec![level_one]);
    let int_ty = k.const_(p.z, vec![]);
    let expected = {
        let e = k.app(eq_c, int_ty);
        let e = k.app(e, lhs_direct);
        k.app(e, rhs_direct)
    };
    assert!(
        k.def_eq(inferred, expected),
        "gauss_sign_prod_eq_pow_neg_one_of_count's instantiated type must \
         match the direct sign-product/pow computation"
    );
}

/// `Int.prodRange_scaledIndexEqPowMulFactorial` at `a := 2, m := 3` --
/// `∏_{k=1}^3 (2·k) = 2*4*6 = 48`, and independently `2^3 * 3! = 8*6 = 48`.
/// Checks the general theorem's instantiation against a hand-built direct
/// `prodRange` computation AND against `Int.factorial`'s own concrete value,
/// so a defect in either the `prodRange_mul`/`prodRange_const_pow` chaining
/// or the `factorial`-defeq bridge would surface.
#[test]
fn prod_range_scaled_index_eq_pow_mul_factorial_matches_direct_computation_at_a_2_m_3() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    let two = numeral(&mut k, &p, 2);
    let three_n = numeral_nat(&mut k, &p, 3);

    // scaled := fun k => mul 2 (ofNat (succ k)).
    let scaled = {
        let k_fv = 900_600;
        let kk = k.fvar(k_fv);
        let succ = k.const_(p.nat.succ, vec![]);
        let sk = k.app(succ, kk);
        let of_nat = k.const_(p.of_nat, vec![]);
        let ofk = k.app(of_nat, sk);
        let mul_c = k.const_(p.mul, vec![]);
        let m1 = k.app(mul_c, two);
        let body = k.app(m1, ofk);
        let abstracted = k.abstract_fvars(body, &[k_fv]);
        k.lam(anon, nat_ty, abstracted, BinderInfo::Default)
    };
    let prod_range_c = k.const_(p.prod_range, vec![]);
    let prod_range_scaled = k.app(prod_range_c, scaled);
    let lhs_direct = k.app(prod_range_scaled, three_n);

    let forty_eight = numeral(&mut k, &p, 48);
    assert!(
        k.def_eq(lhs_direct, forty_eight),
        "prodRange (fun k => 2 * ofNat (succ k)) 3 should compute to 48"
    );

    let pow_c = k.const_(p.pow, vec![]);
    let pow_two = k.app(pow_c, two);
    let pow_two_3 = k.app(pow_two, three_n);
    let factorial_c = k.const_(p.factorial, vec![]);
    let factorial_3 = k.app(factorial_c, three_n);
    let mul_c = k.const_(p.mul, vec![]);
    let m1 = k.app(mul_c, pow_two_3);
    let rhs_direct = k.app(m1, factorial_3);
    assert!(
        k.def_eq(rhs_direct, forty_eight),
        "pow 2 3 * factorial 3 should compute to 48"
    );

    let lemma = k.const_(p.prod_range_scaled_index_eq_pow_mul_factorial, vec![]);
    let l1 = k.app(lemma, two);
    let applied = k.app(l1, three_n);
    let inferred = k
        .infer(applied)
        .expect("prod_range_scaled_index_eq_pow_mul_factorial must apply at concrete a, m");
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let eq_c = k.const_(p.logic.eq, vec![level_one]);
    let int_ty = k.const_(p.z, vec![]);
    let expected = {
        let e = k.app(eq_c, int_ty);
        let e = k.app(e, lhs_direct);
        k.app(e, rhs_direct)
    };
    assert!(
        k.def_eq(inferred, expected),
        "prod_range_scaled_index_eq_pow_mul_factorial's instantiated type \
         must match the direct prodRange/pow/factorial computation"
    );
}

/// `Int.factorial_eq_of_nat_factorial` (ADR-1070, connecting-theorem item 2)
/// at `m := 4`: `Int.factorial` (this prelude's `prodRange`-built recursion)
/// and `Nat.factorial` (`nat_prelude`'s independent `Nat.mul` recursion) both
/// reduce to `ofNat 24` at a concrete witness, not merely by the induction's
/// own internal logic.
#[test]
fn factorial_eq_of_nat_factorial_matches_direct_computation_at_m_4() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let four = d.num(4);
    let fact_int_4 = d.const_app(p.factorial, &[four]);
    let fact_nat_4 = NatOps::factorial(&mut d, four);
    let of_nat_fact_nat_4 = d.of_nat(fact_nat_4);

    let twenty_four = numeral(d.kernel(), &p, 24);
    assert!(
        d.kernel().def_eq(fact_int_4, twenty_four),
        "sanity: Int.factorial 4 must reduce to ofNat 24"
    );
    assert!(
        d.kernel().def_eq(of_nat_fact_nat_4, twenty_four),
        "sanity: ofNat (Nat.factorial 4) must reduce to ofNat 24"
    );

    let applied = d.lemma(p.factorial_eq_of_nat_factorial, &[four]);
    let inferred = d
        .kernel()
        .infer(applied)
        .expect("factorial_eq_of_nat_factorial must apply at m := 4");
    let expected = d.ieq(fact_int_4, of_nat_fact_nat_4);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "factorial_eq_of_nat_factorial's instantiated type must match the \
         direct Int.factorial/Nat.factorial computation"
    );
}

/// `Int.coprime_factorial_of_lt_prime` (ADR-1070, connecting-theorem item 2)
/// at `pp := 7`, `m := 4`. `PrimeCond` is left as a free variable registered
/// in a `LocalContext` (the conclusion's type does not depend on which proof
/// inhabits that hypothesis); the `Lt m pp` bound is a genuine witness via
/// `le_add_right`, mirroring `nat_prelude/gauss_lemma.rs`'s own concrete
/// test of the Nat-typed half this theorem wraps.
#[test]
fn coprime_factorial_of_lt_prime_computes_at_pp_seven_m_four() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let pp = d.num(7);
    let m = d.num(4);

    let big_pp = d.of_nat(pp);
    let fact_int_m = d.const_app(p.factorial, &[m]);
    let coprime_ty = d.const_app(p.coprime, &[fact_int_m, big_pp]);

    let prime_ty = super::wilson::prime_condition(&mut d, pp);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);

    // Lt m pp = Lt 4 7 = Le 5 7 = Le 5 (add 5 2), via le_add_right(5, 2).
    let five = d.num(5);
    let two = d.num(2);
    let bound_proof = d.lemma(p.nat.le_add_right, &[five, two]);

    let lemma_fn = d.lemma(p.coprime_factorial_of_lt_prime, &[pp, m]);
    let applied = d.apply(lemma_fn, &[prime_proof, bound_proof]);

    // `prime_proof` is a bare free variable and needs a `LocalContext`
    // registration before a top-level `infer` can resolve it (an empty
    // context would reject it with `UnboundFVar`).
    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("coprime_factorial_of_lt_prime must apply at pp := 7, m := 4");
    assert!(
        d.kernel().def_eq(inferred, coprime_ty),
        "coprime_factorial_of_lt_prime's instantiated type must match \
         Int.Coprime (factorial m) (ofNat pp)"
    );
}

/// `Int.ediv`/`Int.emod` compute the exact values Lean 4 core's `Int.ediv`/
/// `Int.emod` document for themselves (`Init.Data.Int.DivMod.Basic`), across
/// every sign combination and the division-by-zero corner — the totality
/// convention this development chose to match, not a case it happened to get
/// right. Both are checked `Declaration::Definition`s with an empty axiom
/// footprint: nothing here was assumed.
#[test]
fn ediv_emod_compute_their_normal_forms() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    assert!(
        k.axiom_footprint(p.ediv).is_empty(),
        "Int.ediv must rest on no axiom"
    );
    assert!(
        k.axiom_footprint(p.emod).is_empty(),
        "Int.emod must rest on no axiom"
    );

    let ediv_cases = [
        (7, 0, 0),
        (0, 7, 0),
        (12, 6, 2),
        (12, -6, -2),
        (-12, 6, -2),
        (-12, -6, 2),
        (12, 7, 1),
        (12, -7, -1),
        (-12, 7, -2),
        (-12, -7, 2),
    ];
    for (left, right, expected) in ediv_cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(p.ediv, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "ediv {left} {right} should be {expected}"
        );
    }

    let emod_cases = [
        (7, 0, 7),
        (0, 7, 0),
        (12, 6, 0),
        (12, -6, 0),
        (-12, 6, 0),
        (-12, -6, 0),
        (12, 7, 5),
        (12, -7, 5),
        (-12, 7, 2),
        (-12, -7, 2),
    ];
    for (left, right, expected) in emod_cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(p.emod, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "emod {left} {right} should be {expected}"
        );
        // The E-rounding invariant: the remainder is always non-negative.
        assert!(expected >= 0, "emod {left} {right} should be non-negative");
    }
}

/// `Int.ediv_add_emod` — the division algorithm as an equation
/// (`b*(a/b)+a%b=a`) — genuinely computes, across every sign combination and
/// the division-by-zero corner, and is a `Theorem` with an empty axiom
/// footprint: the equation was DERIVED from `Nat.div_mod_exec`, not assumed.
#[test]
fn ediv_add_emod_computes_at_concrete_values() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.ediv_add_emod).is_empty(),
        "Int.ediv_add_emod must rest on no axiom"
    );

    let cases = [
        (7, 0),
        (0, 7),
        (12, 6),
        (12, -6),
        (-12, 6),
        (-12, -6),
        (12, 7),
        (12, -7),
        (-12, 7),
        (-12, -7),
    ];
    for (left, right) in cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let theorem = k.const_(p.ediv_add_emod, vec![]);
        let applied = k.app(theorem, a);
        let proof = k.app(applied, b);
        let inferred = k
            .infer(proof)
            .unwrap_or_else(|e| panic!("ediv_add_emod {left} {right} should type-check: {e:?}"));

        // The stated equation, built directly: `Eq Int (b*(a/b)+a%b) a`.
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let ediv = k.const_(p.ediv, vec![]);
        let ediv_ab_f = k.app(ediv, a);
        let ediv_ab = k.app(ediv_ab_f, b);
        let mul = k.const_(p.mul, vec![]);
        let scaled_f = k.app(mul, b);
        let scaled = k.app(scaled_f, ediv_ab);
        let emod = k.const_(p.emod, vec![]);
        let emod_ab_f = k.app(emod, a);
        let emod_ab = k.app(emod_ab_f, b);
        let add = k.const_(p.add, vec![]);
        let sum_f = k.app(add, scaled);
        let sum = k.app(sum_f, emod_ab);
        let zero_level = k.level_zero();
        let one_level = k.level_succ(zero_level);
        let eq = k.const_(p.logic.eq, vec![one_level]);
        let z_ty = k.const_(p.z, vec![]);
        let eq_ty = k.app(eq, z_ty);
        let eq_ty_sum = k.app(eq_ty, sum);
        let expected = k.app(eq_ty_sum, a);

        assert!(
            k.def_eq(inferred, expected),
            "ediv_add_emod {left} {right}: inferred type does not match the stated equation"
        );

        // And it genuinely computes: the reconstruction reduces to `left`.
        let want = numeral(&mut k, &p, left);
        assert!(
            k.def_eq(sum, want),
            "ediv_add_emod {left} {right}: b*(a/b)+a%b should reduce to {left}"
        );
    }
}

/// `Int.emod_natAbs_bound` — the sign-general remainder bound
/// `Int.emod_lt_of_pos` cannot state (bounding against `b` itself is FALSE
/// for a negative `b`). Instantiated at a POSITIVE divisor (`b = 1`, where
/// `natAbs b = b` and the bound coincides with what `emod_lt_of_pos` already
/// gives), a NEGATIVE divisor (`b = -1`, where `emod_lt_of_pos`'s own
/// hypothesis `Int.lt Int.zero b` is structurally FALSE — checked below —
/// so that theorem cannot even be invoked here), and a NEGATIVE CONTROL at
/// the excluded `b = 0` corner, checked independently of the theorem (whose
/// hypothesis is correctly unsatisfiable there): `emod a 0 = a` (the
/// totality convention) and `natAbs 0 = 0`, so the excluded conclusion would
/// demand `5 < 0`, refuted by `Nat.not_succ_le_zero` — confirming the `b ≠
/// 0` hypothesis is genuinely load-bearing, not merely unused decoration.
#[test]
fn emod_natabs_bound_instantiates_at_positive_negative_and_zero_divisors() {
    use crate::BinderInfo;

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.emod_natabs_bound).is_empty(),
        "Int.emod_natAbs_bound must rest on no axiom"
    );

    let zero_c = k.const_(p.zero, vec![]);
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);

    // From `order_at_b : Int.lt zero_c b` (`zero_on_left`) or `Int.lt b
    // zero_c` (otherwise), build `Not (Eq Int b zero_c)`: assume `h : Eq Int
    // b zero_c`, transport `order_at_b` along `h` (`Eq.rec`) to `Int.lt
    // zero_c zero_c` / `Int.lt zero_c zero_c`, and refute with `lt_irrefl`.
    let ne_zero_from_order = |k: &mut Kernel,
                              b: crate::ExprId,
                              order_at_b: crate::ExprId,
                              zero_on_left: bool|
     -> crate::ExprId {
        let int_ty = k.const_(p.z, vec![]);
        let h_fv = 900_100;
        let h = k.fvar(h_fv);
        let eq_ty = {
            let eq = k.const_(p.logic.eq, vec![one_level]);
            let e = k.app(eq, int_ty);
            let e = k.app(e, b);
            k.app(e, zero_c)
        };
        let x_fv = 900_101;
        let x = k.fvar(x_fv);
        let motive_body = {
            let lt = k.const_(p.lt, vec![]);
            if zero_on_left {
                let e = k.app(lt, zero_c);
                k.app(e, x)
            } else {
                let e = k.app(lt, x);
                k.app(e, zero_c)
            }
        };
        let eq_b_x = {
            let eq = k.const_(p.logic.eq, vec![one_level]);
            let e = k.app(eq, int_ty);
            let e = k.app(e, b);
            k.app(e, x)
        };
        let anon = k.anon();
        let inner = k.lam(anon, eq_b_x, motive_body, BinderInfo::Default);
        let motive = {
            let body = k.abstract_fvars(inner, &[x_fv]);
            k.lam(anon, int_ty, body, BinderInfo::Default)
        };
        let rec_name = p.logic.eq_rec;
        let rec = k.const_(rec_name, vec![zero_level, one_level]);
        let e = k.app(rec, int_ty);
        let e = k.app(e, b);
        let e = k.app(e, motive);
        let e = k.app(e, order_at_b);
        let e = k.app(e, zero_c);
        let rewritten = k.app(e, h);
        let irrefl = k.const_(p.lt_irrefl, vec![]);
        let irrefl_zero = k.app(irrefl, zero_c);
        let false_proof = k.app(irrefl_zero, rewritten);
        let body = k.abstract_fvars(false_proof, &[h_fv]);
        k.lam(anon, eq_ty, body, BinderInfo::Default)
    };

    // --- positive divisor: b = Int.one, a = 5.  emod(5,1)=0 < natAbs(1)=1. ---
    {
        let a = numeral(&mut k, &p, 5);
        let b = k.const_(p.one, vec![]);
        // `Int.zero_lt_one : Int.lt Int.zero Int.one` -- exactly `Int.lt
        // zero_c b`, already proved, no fresh `Nat` order proof needed.
        let order_at_b = k.const_(p.zero_lt_one, vec![]);
        let ne_proof = ne_zero_from_order(&mut k, b, order_at_b, true);

        let theorem = k.const_(p.emod_natabs_bound, vec![]);
        let applied = k.app(theorem, a);
        let applied = k.app(applied, b);
        let applied = k.app(applied, ne_proof);
        k.infer(applied).unwrap_or_else(|e| {
            panic!("emod_natAbs_bound at a=5,b=1 (positive divisor) should type-check: {e:?}")
        });

        let emod = k.const_(p.emod, vec![]);
        let e = k.app(emod, a);
        let emod_ab = k.app(e, b);
        let want = numeral(&mut k, &p, 0);
        assert!(k.def_eq(emod_ab, want), "emod 5 1 should be 0");
    }

    // --- negative divisor: b = negSucc 0 = -1, a = 5.  emod(5,-1)=0 <
    //     natAbs(-1)=1.  `Int.lt Int.zero b` is FALSE here (`Int.lt`'s
    //     `ofNat _, negSucc _` branch is unconditionally `False`,
    //     `defs.rs::declare_order_definitions`), so `emod_lt_of_pos` could
    //     not be invoked at this `b` at all -- this theorem is the only one
    //     that can state a bound here. ---
    {
        let a = numeral(&mut k, &p, 5);
        let b = numeral(&mut k, &p, -1);
        // `Int.lt (negSucc 0) zero_c` reduces to `True` unconditionally
        // (the mixed-sign branch), so `True.intro` suffices.
        let order_at_b = k.const_(p.logic.true_intro, vec![]);
        let ne_proof = ne_zero_from_order(&mut k, b, order_at_b, false);

        let theorem = k.const_(p.emod_natabs_bound, vec![]);
        let applied = k.app(theorem, a);
        let applied = k.app(applied, b);
        let applied = k.app(applied, ne_proof);
        k.infer(applied).unwrap_or_else(|e| {
            panic!("emod_natAbs_bound at a=5,b=-1 (negative divisor) should type-check: {e:?}")
        });

        let emod = k.const_(p.emod, vec![]);
        let e = k.app(emod, a);
        let emod_ab = k.app(e, b);
        let want = numeral(&mut k, &p, 0);
        assert!(k.def_eq(emod_ab, want), "emod 5 (-1) should be 0");
    }

    // --- negative control: b = 0 is excluded, and for good reason. The
    //     theorem's hypothesis is correctly unsatisfiable there (no proof of
    //     `Not (Eq Int b zero)` exists for `b = zero`), so the theorem
    //     cannot be applied -- checked instead directly against `emod`'s
    //     own totality convention and `natAbs`. ---
    {
        let a = numeral(&mut k, &p, 5);
        let b = numeral(&mut k, &p, 0);
        let emod = k.const_(p.emod, vec![]);
        let e = k.app(emod, a);
        let emod_ab = k.app(e, b);
        assert!(
            k.def_eq(emod_ab, a),
            "Int.emod a 0 must be the totality convention `a` itself"
        );
        let nat_abs_b = {
            let f = k.const_(p.nat_abs, vec![]);
            k.app(f, b)
        };
        let bound = {
            let of_nat = k.const_(p.of_nat, vec![]);
            k.app(of_nat, nat_abs_b)
        };
        let zero_bound = numeral(&mut k, &p, 0);
        assert!(k.def_eq(bound, zero_bound), "ofNat (natAbs 0) must be 0");

        // The excluded conclusion `Int.lt (emod 5 0) (ofNat (natAbs 0))`
        // is `Int.lt (ofNat 5) (ofNat 0)`, which reduces to `Nat.le 6 0` --
        // refuted by `Nat.not_succ_le_zero`, confirming the `b ≠ 0`
        // hypothesis is load-bearing rather than unused.
        let five_nat = numeral_nat(&mut k, &p, 5);
        let refutation = {
            let lemma = k.const_(p.nat.not_succ_le_zero, vec![]);
            k.app(lemma, five_nat)
        };
        k.infer(refutation).unwrap_or_else(|e| {
            panic!(
                "Nat.not_succ_le_zero should type-check at 5, refuting the excluded bound: {e:?}"
            )
        });
    }
}

/// `Int.ediv_emod_unique` applied at a genuine positive divisor and a genuine
/// valid decomposition (`13 = 4*3+1`, remainder `1` in `[0,4)`) type-checks
/// end to end: every one of the six hypothesis proofs is a real `Nat.le`/
/// `Nat.lt` witness at concrete numerals, not just an abstract variable. The
/// two decompositions supplied are identical, so the conclusion is trivial
/// (`3=3 ∧ 1=1`), but reaching it exercises the divisor-pinning
/// (`Int.lt_dest`) and the `Int.le_total` split on real literals rather than
/// free variables.
#[test]
fn ediv_emod_unique_applies_at_a_concrete_decomposition() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.ediv_emod_unique).is_empty(),
        "Int.ediv_emod_unique must rest on no axiom"
    );

    let a = numeral(&mut k, &p, 13);
    let b = numeral(&mut k, &p, 4);
    let q = numeral(&mut k, &p, 3);
    let r = numeral(&mut k, &p, 1);

    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let z_ty = k.const_(p.z, vec![]);

    // 0 < 4 : Nat.le 1 4, from `le_succ_succ 0 3 (zero_le 3)`.
    let pos_proof = {
        let base = {
            let n3 = numeral_nat(&mut k, &p, 3);
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n3)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let n3 = numeral_nat(&mut k, &p, 3);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n0);
        let f = k.app(f, n3);
        k.app(f, base)
    };

    // 13 = 4*3+1, by computation alone.
    let eq_proof = {
        let refl = k.const_(p.logic.eq_refl, vec![one_level]);
        let refl = k.app(refl, z_ty);
        k.app(refl, a)
    };

    // 0 ≤ 1 : Nat.le 0 1.
    let lower_proof = {
        let n1 = numeral_nat(&mut k, &p, 1);
        let f = k.const_(p.nat.zero_le, vec![]);
        k.app(f, n1)
    };

    // 1 < 4 : Nat.le 2 4, from two `le_succ_succ` steps off `zero_le 2`.
    let upper_proof = {
        let n2 = numeral_nat(&mut k, &p, 2);
        let base = {
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n2)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let step1 = {
            let f = k.const_(p.nat.le_succ_succ, vec![]);
            let f = k.app(f, n0);
            let f = k.app(f, n2);
            k.app(f, base)
        };
        let n1 = numeral_nat(&mut k, &p, 1);
        let n3 = numeral_nat(&mut k, &p, 3);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n1);
        let f = k.app(f, n3);
        k.app(f, step1)
    };

    let theorem = k.const_(p.ediv_emod_unique, vec![]);
    let mut proof = theorem;
    for arg in [a, b, q, r, q, r] {
        proof = k.app(proof, arg);
    }
    for arg in [
        pos_proof,
        eq_proof,
        lower_proof,
        upper_proof,
        eq_proof,
        lower_proof,
        upper_proof,
    ] {
        proof = k.app(proof, arg);
    }
    let inferred = k
        .infer(proof)
        .unwrap_or_else(|e| panic!("ediv_emod_unique 13 4 3 1 3 1 should type-check: {e:?}"));

    let eq = k.const_(p.logic.eq, vec![one_level]);
    let eq_q = k.app(eq, z_ty);
    let eq_q = k.app(eq_q, q);
    let eq_q = k.app(eq_q, q);
    let eq_r = k.const_(p.logic.eq, vec![one_level]);
    let z_ty = k.const_(p.z, vec![]);
    let eq_r = k.app(eq_r, z_ty);
    let eq_r = k.app(eq_r, r);
    let eq_r = k.app(eq_r, r);
    let and = k.const_(p.logic.and, vec![]);
    let expected = k.app(and, eq_q);
    let expected = k.app(expected, eq_r);

    assert!(
        k.def_eq(inferred, expected),
        "ediv_emod_unique's conclusion should be exactly q1=q2 ∧ r1=r2"
    );
}

/// `Nat.le lo hi`, for concrete `lo ≤ hi`, built by peeling `succ` off both
/// sides down to `Nat.le 0 (hi-lo)` (`Nat.zero_le`), then re-wrapping with
/// `le_succ_succ` -- the same recipe `ediv_emod_unique_applies_at_a_concrete_
/// decomposition` inlines twice by hand, generalized so the sign-general
/// test below can build both a `0 ≤ r` and an `r < natAbs b` witness (the
/// latter is `Nat.le (r+1) (natAbs b)`) from the same helper.
fn nat_le_proof(k: &mut Kernel, p: &IntPrelude, lo: u32, hi: u32) -> crate::ExprId {
    assert!(lo <= hi, "nat_le_proof: {lo} > {hi}");
    if lo == 0 {
        let hi_nat = numeral_nat(k, p, hi);
        let f = k.const_(p.nat.zero_le, vec![]);
        return k.app(f, hi_nat);
    }
    let inner = nat_le_proof(k, p, lo - 1, hi - 1);
    let lo1 = numeral_nat(k, p, lo - 1);
    let hi1 = numeral_nat(k, p, hi - 1);
    let f = k.const_(p.nat.le_succ_succ, vec![]);
    let f = k.app(f, lo1);
    let f = k.app(f, hi1);
    k.app(f, inner)
}

/// `Int.ediv_emod_unique_general` applied at a genuine POSITIVE divisor
/// (`13 = 4*3+1`, the same decomposition `ediv_emod_unique_applies_at_a_
/// concrete_decomposition` uses, now via the `b ≠ 0` hypothesis instead of
/// `0 < b`) and at a genuine NEGATIVE divisor (`13 = (-4)*(-3)+1`, remainder
/// `1` in `[0, natAbs(-4)) = [0,4)`) -- a decomposition `ediv_emod_unique`
/// cannot even be STATED for, since its hypothesis `0 < b` is false at
/// `b = -4`. Both instantiations type-check end to end and land on the exact
/// `q1=q2 ∧ r1=r2` conclusion.
#[test]
fn ediv_emod_unique_general_applies_at_a_positive_and_a_negative_divisor() {
    use crate::BinderInfo;

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.ediv_emod_unique_general).is_empty(),
        "Int.ediv_emod_unique_general must rest on no axiom"
    );

    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let z_ty = k.const_(p.z, vec![]);

    // Builds `Not (Eq Int b zero_c)` from `order_at_b : Int.lt zero_c b`
    // (`zero_on_left`) or `Int.lt b zero_c` (otherwise) -- same construction
    // as `emod_natabs_bound_instantiates_at_positive_negative_and_zero_
    // divisors`'s local helper, rebuilt here since each test in this file is
    // self-contained by this file's own convention.
    let ne_zero_from_order = |k: &mut Kernel,
                              b: crate::ExprId,
                              order_at_b: crate::ExprId,
                              zero_on_left: bool|
     -> crate::ExprId {
        let zero_c = k.const_(p.zero, vec![]);
        let int_ty = k.const_(p.z, vec![]);
        let h_fv = 900_200;
        let h = k.fvar(h_fv);
        let eq_ty = {
            let eq = k.const_(p.logic.eq, vec![one_level]);
            let e = k.app(eq, int_ty);
            let e = k.app(e, b);
            k.app(e, zero_c)
        };
        let x_fv = 900_201;
        let x = k.fvar(x_fv);
        let motive_body = {
            let lt = k.const_(p.lt, vec![]);
            if zero_on_left {
                let e = k.app(lt, zero_c);
                k.app(e, x)
            } else {
                let e = k.app(lt, x);
                k.app(e, zero_c)
            }
        };
        let eq_b_x = {
            let eq = k.const_(p.logic.eq, vec![one_level]);
            let e = k.app(eq, int_ty);
            let e = k.app(e, b);
            k.app(e, x)
        };
        let anon = k.anon();
        let inner = k.lam(anon, eq_b_x, motive_body, BinderInfo::Default);
        let motive = {
            let body = k.abstract_fvars(inner, &[x_fv]);
            k.lam(anon, int_ty, body, BinderInfo::Default)
        };
        let rec_name = p.logic.eq_rec;
        let rec = k.const_(rec_name, vec![zero_level, one_level]);
        let e = k.app(rec, int_ty);
        let e = k.app(e, b);
        let e = k.app(e, motive);
        let e = k.app(e, order_at_b);
        let e = k.app(e, zero_c);
        let rewritten = k.app(e, h);
        let irrefl = k.const_(p.lt_irrefl, vec![]);
        let irrefl_zero = k.app(irrefl, zero_c);
        let false_proof = k.app(irrefl_zero, rewritten);
        let body = k.abstract_fvars(false_proof, &[h_fv]);
        k.lam(anon, eq_ty, body, BinderInfo::Default)
    };

    let refl_at = |k: &mut Kernel, at: crate::ExprId| -> crate::ExprId {
        let refl = k.const_(p.logic.eq_refl, vec![one_level]);
        let e = k.app(refl, z_ty);
        k.app(e, at)
    };

    let check_expected_conclusion = |k: &mut Kernel,
                                     inferred: crate::ExprId,
                                     q: crate::ExprId,
                                     r: crate::ExprId,
                                     label: &str| {
        let eq = k.const_(p.logic.eq, vec![one_level]);
        let eq_q = k.app(eq, z_ty);
        let eq_q = k.app(eq_q, q);
        let eq_q = k.app(eq_q, q);
        let eq_r = k.const_(p.logic.eq, vec![one_level]);
        let eq_r = k.app(eq_r, z_ty);
        let eq_r = k.app(eq_r, r);
        let eq_r = k.app(eq_r, r);
        let and = k.const_(p.logic.and, vec![]);
        let expected = k.app(and, eq_q);
        let expected = k.app(expected, eq_r);
        assert!(
            k.def_eq(inferred, expected),
            "ediv_emod_unique_general ({label}): conclusion should be exactly q1=q2 ∧ r1=r2"
        );
    };

    // --- positive divisor: 13 = 4*3+1, remainder 1 in [0, natAbs 4) = [0,4). ---
    {
        let a = numeral(&mut k, &p, 13);
        let b = numeral(&mut k, &p, 4);
        let q = numeral(&mut k, &p, 3);
        let r = numeral(&mut k, &p, 1);

        let order_at_b = nat_le_proof(&mut k, &p, 1, 4); // Nat.le 1 4 ≡ Int.lt zero_c b
        let ne_proof = ne_zero_from_order(&mut k, b, order_at_b, true);
        let eq_proof = refl_at(&mut k, a);
        let lower_proof = nat_le_proof(&mut k, &p, 0, 1); // 0 ≤ 1
        let upper_proof = nat_le_proof(&mut k, &p, 2, 4); // 1 < 4

        let theorem = k.const_(p.ediv_emod_unique_general, vec![]);
        let mut proof = theorem;
        for arg in [a, b, q, r, q, r] {
            proof = k.app(proof, arg);
        }
        for arg in [
            ne_proof,
            eq_proof,
            lower_proof,
            upper_proof,
            eq_proof,
            lower_proof,
            upper_proof,
        ] {
            proof = k.app(proof, arg);
        }
        let inferred = k.infer(proof).unwrap_or_else(|e| {
            panic!("ediv_emod_unique_general 13 4 3 1 3 1 (positive) should type-check: {e:?}")
        });
        check_expected_conclusion(&mut k, inferred, q, r, "positive divisor");
    }

    // --- negative divisor: 13 = (-4)*(-3)+1, remainder 1 in
    //     [0, natAbs (-4)) = [0,4).  `Int.ediv_emod_unique` cannot even be
    //     invoked here: `Int.lt Int.zero (-4)` is FALSE. ---
    {
        let a = numeral(&mut k, &p, 13);
        let b = numeral(&mut k, &p, -4);
        let q = numeral(&mut k, &p, -3);
        let r = numeral(&mut k, &p, 1);

        // `Int.lt (negSucc 3) zero_c` reduces to `True` unconditionally.
        let order_at_b = k.const_(p.logic.true_intro, vec![]);
        let ne_proof = ne_zero_from_order(&mut k, b, order_at_b, false);
        let eq_proof = refl_at(&mut k, a);
        let lower_proof = nat_le_proof(&mut k, &p, 0, 1); // 0 ≤ 1
        let upper_proof = nat_le_proof(&mut k, &p, 2, 4); // 1 < natAbs(-4) = 4

        let theorem = k.const_(p.ediv_emod_unique_general, vec![]);
        let mut proof = theorem;
        for arg in [a, b, q, r, q, r] {
            proof = k.app(proof, arg);
        }
        for arg in [
            ne_proof,
            eq_proof,
            lower_proof,
            upper_proof,
            eq_proof,
            lower_proof,
            upper_proof,
        ] {
            proof = k.app(proof, arg);
        }
        let inferred = k.infer(proof).unwrap_or_else(|e| {
            panic!("ediv_emod_unique_general 13 -4 -3 1 -3 1 (negative) should type-check: {e:?}")
        });
        check_expected_conclusion(&mut k, inferred, q, r, "negative divisor");
    }
}

/// `Int.emod_eq_zero_iff_dvd`'s `mp` direction, applied at a genuine multiple
/// (`12 = 4*3`): feeding it the (computed) proof that `12 % 4 = 0` produces a
/// real divisibility witness of type `Int.dvd 4 12`.
#[test]
fn emod_eq_zero_iff_dvd_mp_produces_a_real_witness() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.emod_eq_zero_iff_dvd).is_empty(),
        "Int.emod_eq_zero_iff_dvd must rest on no axiom"
    );

    let a = numeral(&mut k, &p, 12);
    let b = numeral(&mut k, &p, 4);

    // 0 < 4 : Nat.le 1 4.
    let pos_proof = {
        let n3 = numeral_nat(&mut k, &p, 3);
        let base = {
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n3)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n0);
        let f = k.app(f, n3);
        k.app(f, base)
    };

    let theorem = k.const_(p.emod_eq_zero_iff_dvd, vec![]);
    let mut iff_proof = theorem;
    for arg in [a, b, pos_proof] {
        iff_proof = k.app(iff_proof, arg);
    }

    // 12 % 4 = 0, purely by computation.
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let z_ty = k.const_(p.z, vec![]);
    let emod = k.const_(p.emod, vec![]);
    let emod_ab = k.app(emod, a);
    let emod_ab = k.app(emod_ab, b);
    let refl = k.const_(p.logic.eq_refl, vec![one_level]);
    let refl = k.app(refl, z_ty);
    let zero_remainder_proof = k.app(refl, emod_ab);

    let mp = k.const_(p.logic.iff_mp, vec![]);
    let zero_eq_ty = {
        let eq = k.const_(p.logic.eq, vec![one_level]);
        let eq_ty = k.app(eq, z_ty);
        let eq_ty = k.app(eq_ty, emod_ab);
        let zero = k.const_(p.zero, vec![]);
        k.app(eq_ty, zero)
    };
    let dvd_ba = {
        let dvd = k.const_(p.dvd, vec![]);
        let dvd_ba = k.app(dvd, b);
        k.app(dvd_ba, a)
    };
    let mp = k.app(mp, zero_eq_ty);
    let mp = k.app(mp, dvd_ba);
    let mp = k.app(mp, iff_proof);
    let witness = k.app(mp, zero_remainder_proof);
    let inferred = k
        .infer(witness)
        .unwrap_or_else(|e| panic!("emod_eq_zero_iff_dvd mp at 12 4 should type-check: {e:?}"));

    assert!(
        k.def_eq(inferred, dvd_ba),
        "the witness's type should be exactly Int.dvd 4 12"
    );
}

/// The order relations decide the mixed-sign cases outright: a negative integer
/// is below every non-negative one, and never the reverse. (The same-sign cases
/// delegate to `Nat.le`/`Nat.lt`, which the `Nat` prelude's own suite covers.)
#[test]
fn the_order_relations_decide_mixed_signs() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let true_ = k.const_(p.logic.true_, vec![]);
    let false_ = k.const_(p.logic.false_, vec![]);

    for relation in [p.le, p.lt] {
        for (left, right) in [(-1, 0), (-4, 2), (-1, 7)] {
            let a = numeral(&mut k, &p, left);
            let b = numeral(&mut k, &p, right);
            let f = k.const_(relation, vec![]);
            let applied = k.app(f, a);
            let applied = k.app(applied, b);
            assert!(
                k.def_eq(applied, true_),
                "{} {left} {right} should hold outright",
                k.display_name(relation)
            );
            // …and the reverse orientation is refuted outright.
            let a = numeral(&mut k, &p, right);
            let b = numeral(&mut k, &p, left);
            let f = k.const_(relation, vec![]);
            let applied = k.app(f, a);
            let applied = k.app(applied, b);
            assert!(
                k.def_eq(applied, false_),
                "{} {right} {left} should be refuted outright",
                k.display_name(relation)
            );
        }
    }
}

/// The `Nat` development the construction rests on is itself axiom-free, and
/// building `Int` on top of it introduces no trusted declaration of its own
/// beyond the still-asserted laws. This is the property that makes a derived
/// integer fact's empty footprint mean something.
#[test]
fn the_nat_foundation_stays_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in [
        p.nat.add_comm,
        p.nat.mul_comm,
        p.nat.le_trans,
        p.nat.sub_self,
        p.nat.mul_one,
        p.nat.le_total,
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{} must stay axiom-free",
            k.display_name(name)
        );
    }
}

/// `Int.euclid_of_nat` is a **theorem** with an empty axiom footprint — the
/// non-negative branch of the Euclidean decomposition, derived from the
/// axiom-free `Nat` division development rather than assumed.
///
/// This is the ledger-grade claim about the branch: not that it exists, but
/// that it rests on nothing. `Int.euclidean_decomposition` is deliberately NOT
/// asserted to be gone here — it is still an axiom, and the test that it has
/// become a theorem belongs with the commit that discharges it.
#[test]
fn euclid_of_nat_is_derived_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let declaration = k
        .environment()
        .get(p.euclid_of_nat)
        .expect("Int.euclid_of_nat must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Int.euclid_of_nat must be a Theorem, not an assumption"
    );

    let footprint = k.axiom_footprint(p.euclid_of_nat);
    assert!(
        footprint.is_empty(),
        "Int.euclid_of_nat rests on trusted declarations: {:?}",
        footprint
            .iter()
            .map(|&n| k.display_name(n).to_string())
            .collect::<Vec<_>>()
    );
}

/// `Int.natAbs` computes on both constructors by `rfl`, and the round-trip
/// lemma is a theorem with an empty axiom footprint.
///
/// The `rfl` checks matter: `natAbs` is the first piece of the ℚ groundwork, and
/// its two computation rules being definitional is what lets every later
/// statement about a normalised rational avoid a rewrite.
#[test]
fn nat_abs_computes_and_round_trips() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // natAbs (ofNat 3) ≡ 3 and natAbs (negSucc 2) ≡ 3, by conversion alone.
    let three = {
        let mut n = k.const_(p.nat.zero, vec![]);
        for _ in 0..3 {
            let succ = k.const_(p.nat.succ, vec![]);
            n = k.app(succ, n);
        }
        n
    };
    let two = {
        let mut n = k.const_(p.nat.zero, vec![]);
        for _ in 0..2 {
            let succ = k.const_(p.nat.succ, vec![]);
            n = k.app(succ, n);
        }
        n
    };
    let nat_abs = k.const_(p.nat_abs, vec![]);
    for magnitude in [
        {
            let ctor = k.const_(p.of_nat, vec![]);
            k.app(ctor, three)
        },
        {
            let ctor = k.const_(p.neg_succ, vec![]);
            k.app(ctor, two)
        },
    ] {
        let applied = k.app(nat_abs, magnitude);
        assert!(k.def_eq(applied, three), "natAbs did not compute to 3");
    }

    let declaration = k
        .environment()
        .get(p.of_nat_nat_abs_of_nonneg)
        .expect("of_nat_nat_abs_of_nonneg must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "of_nat_nat_abs_of_nonneg must be a Theorem"
    );
    assert!(
        k.axiom_footprint(p.of_nat_nat_abs_of_nonneg).is_empty(),
        "the round-trip lemma rests on a trusted declaration"
    );
}

/// `Int.fib` computes the sign-extended sequence — a theorem alone does not
/// pin down an algorithm (a `TypeMismatch`-free but wrong sign flip would
/// still kernel-check `fib_two_mul_add_one_pos` at a symbolic argument), so
/// this evaluates the DEFINITION at concrete indices and compares against the
/// hand-computed sequence `…, -3, 2, -1, 1, [0], 1, 1, 2, 3, 5, …` for
/// `fib(-4), fib(-3), fib(-2), fib(-1), fib(0), fib(1), fib(2), fib(3)`.
#[test]
fn fib_computes_the_sign_extended_sequence() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let nat_num = |k: &mut Kernel, n: u32| -> ExprId {
        let mut e = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            e = k.app(succ, e);
        }
        e
    };
    let of_nat = |k: &mut Kernel, n: ExprId| -> ExprId {
        let ctor = k.const_(p.of_nat, vec![]);
        k.app(ctor, n)
    };
    let neg_succ = |k: &mut Kernel, n: ExprId| -> ExprId {
        let ctor = k.const_(p.neg_succ, vec![]);
        k.app(ctor, n)
    };
    let fib_at_of_nat = |k: &mut Kernel, n: u32| -> ExprId {
        let fib = k.const_(p.fib, vec![]);
        let arg_nat = nat_num(k, n);
        let arg = of_nat(k, arg_nat);
        k.app(fib, arg)
    };
    let fib_at_neg_succ = |k: &mut Kernel, m: u32| -> ExprId {
        let fib = k.const_(p.fib, vec![]);
        let arg_nat = nat_num(k, m);
        let arg = neg_succ(k, arg_nat);
        k.app(fib, arg)
    };

    // fib(3) = 2, fib(2) = 1 -- the ordinary `ofNat` branch, unchanged from
    // `Nat.fib`.
    {
        let applied = fib_at_of_nat(&mut k, 3);
        let two = nat_num(&mut k, 2);
        let expected = of_nat(&mut k, two);
        assert!(k.def_eq(applied, expected), "fib(3) must compute to 2");
    }
    {
        let applied = fib_at_of_nat(&mut k, 2);
        let one = nat_num(&mut k, 1);
        let expected = of_nat(&mut k, one);
        assert!(k.def_eq(applied, expected), "fib(2) must compute to 1");
    }

    // fib(-1) = fib(negSucc 0) = 1.
    {
        let applied = fib_at_neg_succ(&mut k, 0);
        let one = nat_num(&mut k, 1);
        let expected = of_nat(&mut k, one);
        assert!(k.def_eq(applied, expected), "fib(-1) must compute to 1");
    }

    // fib(-2) = fib(negSucc 1) = -1 = negSucc 0.
    {
        let applied = fib_at_neg_succ(&mut k, 1);
        let zero = nat_num(&mut k, 0);
        let expected = neg_succ(&mut k, zero);
        assert!(k.def_eq(applied, expected), "fib(-2) must compute to -1");

        // Negative control: guard against a vacuous check that would pass
        // even if the sign never actually flipped (fib(-2)'s MAGNITUDE, 1,
        // is the same numeral as fib(-1)'s VALUE -- so a definition that
        // dropped the sign entirely would still satisfy the positive check
        // above at `fib(-1)` and only be caught here).
        let one = nat_num(&mut k, 1);
        let wrong = of_nat(&mut k, one);
        assert!(
            !k.def_eq(applied, wrong),
            "fib(-2) must NOT compute to 1 -- the sign must actually flip"
        );
    }

    // fib(-3) = fib(negSucc 2) = 2.
    {
        let applied = fib_at_neg_succ(&mut k, 2);
        let two = nat_num(&mut k, 2);
        let expected = of_nat(&mut k, two);
        assert!(k.def_eq(applied, expected), "fib(-3) must compute to 2");
    }

    // fib(-4) = fib(negSucc 3) = -3 = negSucc 2.
    {
        let applied = fib_at_neg_succ(&mut k, 3);
        let two = nat_num(&mut k, 2);
        let expected = neg_succ(&mut k, two);
        assert!(k.def_eq(applied, expected), "fib(-4) must compute to -3");
    }
}

/// A concrete rational is constructible, and a non-normalised one is not.
///
/// `Rat.mk` carries two proof fields, and this test discharges both the way a
/// smart constructor will: positivity from `le_succ_succ`, and reducedness by
/// `rfl` — which works only because **`Nat.gcd` computes in this kernel**.
/// Measured here before relying on it: `gcd 1 2` is definitionally `1`, even
/// though `gcd` is defined by well-founded recursion and `WellFounded.fix` does
/// not generally reduce by iota.
///
/// The rejection half is the point. `2/4` differs from `1/2` only in that its
/// `reduced` field is false, so if the kernel accepted it the structure would be
/// carrying a proof obligation it does not enforce.
#[test]
fn rat_admits_a_normalised_pair_and_rejects_an_unreduced_one() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // `gcd` really does reduce; the `rfl` below depends on it.
    let one = numeral(&mut k, 1);
    let two = numeral(&mut k, 2);
    let gcd = k.const_(p.nat.gcd, vec![]);
    let computed = {
        let at_one = k.app(gcd, one);
        k.app(at_one, two)
    };
    assert!(
        k.def_eq(computed, one),
        "gcd 1 2 must reduce to 1 for a rational's `reduced` field to be rfl"
    );

    // 1/2 : num = ofNat 1, den = 2, 1 <= 2, gcd (natAbs 1) 2 = 1.
    let build = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let zero = k.const_(p.nat.zero, vec![]);
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        // 1 <= den, for den = succ (succ .. zero): le_succ_succ zero (den-1) (zero_le _)
        let predecessor = numeral(k, denominator - 1);
        let positive = {
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        // rfl : gcd (natAbs num) den = 1, by computation.
        let unit = numeral(k, 1);
        let reduced = {
            let level = {
                let zero = k.level_zero();
                k.level_succ(zero)
            };
            let refl = k.const_(p.logic.eq_refl, vec![level]);
            let at_ty = k.app(refl, nat_ty);
            k.app(at_ty, unit)
        };
        let ctor = k.const_(p.rat_mk, vec![]);
        let at_num = k.app(ctor, num);
        let at_den = k.app(at_num, den);
        let at_pos = k.app(at_den, positive);
        k.app(at_pos, reduced)
    };

    let half = build(&mut k, 1, 2);
    let inferred = k.infer(half).expect("1/2 must be a well-formed Rat");
    let rendered = k.render_lean(inferred);
    assert!(rendered.contains("Rat"), "unexpected type: {rendered}");

    // 2/4 is not reduced: gcd 2 4 computes to 2, so the `rfl` cannot check.
    let unreduced = build(&mut k, 2, 4);
    assert!(
        k.infer(unreduced).is_err(),
        "Rat accepted 2/4, whose `reduced` field is false"
    );
}

/// `Rat.normalize` actually normalises: `2/4` and `1/2` are the *same* rational.
///
/// This is the strongest statement available about a smart constructor, and it
/// needs no lemma — `Nat.gcd`, `Nat.div` and `Int.rec` all compute, so the two
/// terms are definitionally equal and `def_eq` decides it.
///
/// The discrimination half matters just as much: `1/2` and `1/3` must NOT be
/// equal, or the check above would be vacuous.
#[test]
fn rat_normalize_reduces_two_quarters_to_one_half() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let one_le = |k: &mut Kernel, n: usize| {
        let predecessor = numeral(k, n - 1);
        let base = {
            let lemma = k.const_(p.nat.zero_le, vec![]);
            k.app(lemma, predecessor)
        };
        let lemma = k.const_(p.nat.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero);
        let at_pred = k.app(at_zero, predecessor);
        k.app(at_pred, base)
    };
    let normalize_at = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = one_le(k, denominator);
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };

    let two_quarters = normalize_at(&mut k, 2, 4);
    let one_half = normalize_at(&mut k, 1, 2);
    assert!(
        k.def_eq(two_quarters, one_half),
        "normalize did not reduce 2/4 to 1/2"
    );

    // Non-vacuity: distinct rationals stay distinct.
    let one_third = normalize_at(&mut k, 1, 3);
    assert!(
        !k.def_eq(one_half, one_third),
        "1/2 and 1/3 compared equal — the check above would be meaningless"
    );

    // And a negative numerator normalises through the `negSucc` branch.
    let minus_two_quarters = {
        let num = {
            let ctor = k.const_(p.neg_succ, vec![]);
            let one = numeral(&mut k, 1);
            k.app(ctor, one)
        };
        let den = numeral(&mut k, 4);
        let positive = one_le(&mut k, 4);
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let inferred = k
        .infer(minus_two_quarters)
        .expect("normalize must accept a negSucc numerator");
    let rendered = k.render_lean(inferred);
    assert!(rendered.contains("Rat"), "unexpected type: {rendered}");
}

/// `Rat.mul` renormalises: `2/3 · 3/2` is `1/1`, not `6/6`.
///
/// This is why multiplication cannot just multiply the stored pairs — the
/// product of two *reduced* fractions need not be reduced, and `Rat`'s
/// `reduced` field would then be unprovable. Routing through `Rat.normalize`
/// fixes that, and because every operation computes, the claim is settled by
/// `def_eq` with no lemma.
#[test]
fn rat_mul_renormalises_two_thirds_times_three_halves_to_one() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let rational = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = {
            let predecessor = numeral(k, denominator - 1);
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let times = |k: &mut Kernel, a: ExprId, b: ExprId| {
        let mul = k.const_(p.rat_mul, vec![]);
        let at_a = k.app(mul, a);
        k.app(at_a, b)
    };

    let two_thirds = rational(&mut k, 2, 3);
    let three_halves = rational(&mut k, 3, 2);
    let product = times(&mut k, two_thirds, three_halves);
    let one = rational(&mut k, 1, 1);
    assert!(
        k.def_eq(product, one),
        "2/3 * 3/2 did not renormalise to 1/1"
    );

    // Non-vacuity, and a product that genuinely stays a fraction.
    let one_half = rational(&mut k, 1, 2);
    let one_third = rational(&mut k, 1, 3);
    let sixth = times(&mut k, one_half, one_third);
    let one_sixth = rational(&mut k, 1, 6);
    assert!(k.def_eq(sixth, one_sixth), "1/2 * 1/3 is not 1/6");
    assert!(
        !k.def_eq(sixth, one_half),
        "1/6 and 1/2 compared equal — the checks above would be meaningless"
    );
}

/// `Rat.add` renormalises and `Rat.neg` is an involution.
///
/// `1/6 + 1/3` reaches `9/18` over the common denominator before reduction, so
/// addition has the same obligation multiplication does. Negation is the
/// opposite case — it rebuilds the pair directly, because `Int.nat_abs_neg`
/// says the magnitude the `reduced` field speaks of is unchanged.
#[test]
fn rat_add_renormalises_and_neg_is_an_involution() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let rational = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = {
            let predecessor = numeral(k, denominator - 1);
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let plus = |k: &mut Kernel, a: ExprId, b: ExprId| {
        let add = k.const_(p.rat_add, vec![]);
        let at_a = k.app(add, a);
        k.app(at_a, b)
    };
    let negate = |k: &mut Kernel, a: ExprId| {
        let neg = k.const_(p.rat_neg, vec![]);
        k.app(neg, a)
    };

    // 1/6 + 1/3 = 9/18 = 1/2
    let sixth = rational(&mut k, 1, 6);
    let third = rational(&mut k, 1, 3);
    let sum = plus(&mut k, sixth, third);
    let half = rational(&mut k, 1, 2);
    assert!(k.def_eq(sum, half), "1/6 + 1/3 did not renormalise to 1/2");
    assert!(
        !k.def_eq(sum, third),
        "1/2 and 1/3 compared equal — the check above would be meaningless"
    );

    // neg is an involution, and moves the value.
    let negated = negate(&mut k, half);
    let twice = negate(&mut k, negated);
    assert!(k.def_eq(twice, half), "neg is not an involution on 1/2");
    assert!(!k.def_eq(negated, half), "neg left 1/2 unchanged");

    // x + (-x) = 0
    let cancelled = plus(&mut k, half, negated);
    let origin = rational(&mut k, 0, 1);
    assert!(k.def_eq(cancelled, origin), "1/2 + (-1/2) is not 0");
}

/// **The two `Int.ModEq` ledger rows say what the ledger says they say.**
///
/// `derived_laws_have_no_axiom_footprint` covers these three names already, and
/// it is not enough on its own: a theorem stating something *weaker* — the
/// `0 < n` hypothesis that every other congruence lemma in `modeq.rs` carries,
/// a swapped `a`/`b`, `emod b n` where `emod a n` belongs — has exactly the same
/// empty footprint and passes that test unchanged. What is being recorded in
/// `artifacts/facts/F-ml430-int-modeq-one-01d9de39.json` and
/// `F-ml430-int-modeq-neg-d6ff57b6.json` is a *statement*, so a statement is
/// what has to be pinned.
///
/// The `-d6ff57b6` row is a biconditional and this kernel has no `Iff` at the
/// `Int` layer, so it is closed only by BOTH halves; both are asserted here, and
/// dropping either one fails this test rather than quietly halving the claim.
///
/// Asserted against `render_lean`, character for character. Note what is
/// deliberately absent from all three: any `Int.lt Int.zero` premise.
#[test]
fn the_modeq_ledger_rows_are_stated_without_a_positivity_hypothesis() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

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

    for (name, expected) in [
        (
            p.mod_eq_one,
            "((x0 : Int) -> ((x1 : Int) -> Int.ModEq Int.one x0 x1))",
        ),
        (
            p.mod_eq_of_neg_modulus,
            "((x0 : Int) -> ((x1 : Int) -> ((x2 : Int) -> ((x3 : Int.ModEq (Int.neg x0) x1 x2) \
             -> Int.ModEq x0 x1 x2))))",
        ),
        (
            p.mod_eq_neg_modulus,
            "((x0 : Int) -> ((x1 : Int) -> ((x2 : Int) -> ((x3 : Int.ModEq x0 x1 x2) -> \
             Int.ModEq (Int.neg x0) x1 x2))))",
        ),
        (
            p.mod_eq_add_mul_left,
            "((x0 : Int) -> ((x1 : Int) -> ((x2 : Int) -> Int.ModEq x0 (Int.add (Int.mul x0 x2) \
             x1) x1)))",
        ),
        (
            p.add_mod_eq_left,
            "((x0 : Int) -> ((x1 : Int) -> Int.ModEq x0 (Int.add x0 x1) x1))",
        ),
        (
            p.add_mod_eq_right,
            "((x0 : Int) -> ((x1 : Int) -> Int.ModEq x0 (Int.add x1 x0) x1))",
        ),
        (
            p.mod_mod_eq,
            "((x0 : Int) -> ((x1 : Int) -> Int.ModEq x1 (Int.emod x0 x1) x0))",
        ),
        (
            p.modulus_mod_eq_zero,
            "((x0 : Int) -> Int.ModEq x0 x0 Int.zero)",
        ),
        (
            p.mod_eq_sub,
            "((x0 : Int) -> ((x1 : Int) -> Int.ModEq (Int.sub x0 x1) x0 x1))",
        ),
    ] {
        let got = rendered(&k, name);
        assert!(
            !got.contains("Int.lt Int.zero"),
            "{} must hold for EVERY modulus -- the ledger row carries no positivity \
             hypothesis, and a proof that needs one closes a different proposition: {got}",
            k.display_name(name)
        );
        assert_eq!(got, expected, "{}", k.display_name(name));
    }
}

/// The unconditional `ModEq` shift family — [`declare_modeq_add_mul_left`]
/// (`int_prelude/modeq_family.rs`) and its five corollaries — genuinely
/// COMPUTES at concrete arguments, at all three regimes a modulus can be in:
/// `n = 0` (the case that motivates unconditionality at all: `Int.emod _ 0`
/// must genuinely reduce to its argument, not merely type-check), a positive
/// `n`, and a NEGATIVE `n` (the leg every OTHER congruence law in
/// `int_prelude/modeq.rs` cannot reach, since `Int.emod_lt_of_pos` has no
/// proved analogue for a negative divisor).
///
/// Each case both type-checks the theorem applied to literal numerals AND
/// confirms the two `emod` sides the `ModEq` unfolds to reduce to the SAME
/// literal — the positive control every `def_eq` check in this module needs,
/// per the repository's own "negative controls fail two ways" rule: two
/// terms that are both merely STUCK would also satisfy `def_eq`.
#[test]
fn add_modeq_family_computes_at_concrete_values() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let emod_of = |k: &mut Kernel, x: crate::ExprId, n: crate::ExprId| {
        let emod = k.const_(p.emod, vec![]);
        let f = k.app(emod, x);
        k.app(f, n)
    };
    let add_of = |k: &mut Kernel, x: crate::ExprId, y: crate::ExprId| {
        let add = k.const_(p.add, vec![]);
        let f = k.app(add, x);
        k.app(f, y)
    };

    // (n, a) — n=0 is the degenerate identity case, n=5 is a genuine positive
    // modulus, n=-4 is a genuine negative modulus (no positivity bound
    // available anywhere in this development).
    let cases = [(0i32, 3i32), (5, 3), (-4, 3)];

    for (n_val, a_val) in cases {
        // `Int.add_modEq_left n a : ModEq n (add n a) a`.
        {
            let n = numeral(&mut k, &p, n_val);
            let a = numeral(&mut k, &p, a_val);
            let theorem = k.const_(p.add_mod_eq_left, vec![]);
            let applied = k.app(theorem, n);
            let proof = k.app(applied, a);
            k.infer(proof).unwrap_or_else(|e| {
                panic!("add_modEq_left {n_val} {a_val} should type-check: {e:?}")
            });

            let n2 = numeral(&mut k, &p, n_val);
            let a2 = numeral(&mut k, &p, a_val);
            let n3 = numeral(&mut k, &p, n_val);
            let na = add_of(&mut k, n2, a2);
            let lhs = emod_of(&mut k, na, n3);
            let a3 = numeral(&mut k, &p, a_val);
            let n4 = numeral(&mut k, &p, n_val);
            let rhs = emod_of(&mut k, a3, n4);
            assert!(
                k.def_eq(lhs, rhs),
                "add_modEq_left {n_val} {a_val}: emod(n+a,n) must reduce to \
                 the same value as emod(a,n)"
            );
            if n_val == 0 {
                let a4 = numeral(&mut k, &p, a_val);
                assert!(
                    k.def_eq(rhs, a4),
                    "add_modEq_left at n=0: emod(a,0) must genuinely reduce to a \
                     (the zero convention this whole family relies on)"
                );
            }
        }

        // `Int.add_modEq_right n a : ModEq n (add a n) a`.
        {
            let n = numeral(&mut k, &p, n_val);
            let a = numeral(&mut k, &p, a_val);
            let theorem = k.const_(p.add_mod_eq_right, vec![]);
            let applied = k.app(theorem, n);
            let proof = k.app(applied, a);
            k.infer(proof).unwrap_or_else(|e| {
                panic!("add_modEq_right {n_val} {a_val} should type-check: {e:?}")
            });

            let n2 = numeral(&mut k, &p, n_val);
            let a2 = numeral(&mut k, &p, a_val);
            let n3 = numeral(&mut k, &p, n_val);
            let an = add_of(&mut k, a2, n2);
            let lhs = emod_of(&mut k, an, n3);
            let a3 = numeral(&mut k, &p, a_val);
            let n4 = numeral(&mut k, &p, n_val);
            let rhs = emod_of(&mut k, a3, n4);
            assert!(
                k.def_eq(lhs, rhs),
                "add_modEq_right {n_val} {a_val}: emod(a+n,n) must reduce to \
                 the same value as emod(a,n)"
            );
        }

        // `Int.modulus_modEq_zero n : ModEq n n zero`.
        {
            let n = numeral(&mut k, &p, n_val);
            let theorem = k.const_(p.modulus_mod_eq_zero, vec![]);
            let proof = k.app(theorem, n);
            k.infer(proof)
                .unwrap_or_else(|e| panic!("modulus_modEq_zero {n_val} should type-check: {e:?}"));

            let n2 = numeral(&mut k, &p, n_val);
            let zero = numeral(&mut k, &p, 0);
            let n3 = numeral(&mut k, &p, n_val);
            let lhs = emod_of(&mut k, n2, n3);
            let rhs = emod_of(&mut k, zero, n3);
            assert!(
                k.def_eq(lhs, rhs),
                "modulus_modEq_zero {n_val}: emod(n,n) must reduce to the \
                 same value as emod(0,n)"
            );
        }

        // `Int.mod_modEq a n : ModEq n (emod a n) a`, with a genuine
        // multi-digit dividend so `Int.ediv`/`Int.emod` do real work.
        {
            let dividend = 17i32;
            let a = numeral(&mut k, &p, dividend);
            let n = numeral(&mut k, &p, n_val);
            let theorem = k.const_(p.mod_mod_eq, vec![]);
            let applied = k.app(theorem, a);
            let proof = k.app(applied, n);
            k.infer(proof).unwrap_or_else(|e| {
                panic!("mod_modEq {dividend} {n_val} should type-check: {e:?}")
            });

            let a2 = numeral(&mut k, &p, dividend);
            let n2 = numeral(&mut k, &p, n_val);
            let r = emod_of(&mut k, a2, n2);
            let n3 = numeral(&mut k, &p, n_val);
            let lhs = emod_of(&mut k, r, n3);
            let a3 = numeral(&mut k, &p, dividend);
            let n4 = numeral(&mut k, &p, n_val);
            let rhs = emod_of(&mut k, a3, n4);
            assert!(
                k.def_eq(lhs, rhs),
                "mod_modEq {dividend} {n_val}: emod(emod(a,n),n) must reduce \
                 to the same value as emod(a,n)"
            );
            if n_val == 0 {
                let a4 = numeral(&mut k, &p, dividend);
                assert!(
                    k.def_eq(rhs, a4),
                    "mod_modEq at n=0: emod(a,0) must genuinely reduce to a"
                );
            }
        }
    }

    // `Int.modEq_sub a b : ModEq (sub a b) a b`, at a genuine pair where
    // `a - b` is a real, non-trivial modulus (not one of the three regimes
    // above, since here the MODULUS itself is derived from `a`/`b`, not
    // handed in directly).
    {
        let a = numeral(&mut k, &p, 17);
        let b = numeral(&mut k, &p, 5);
        let theorem = k.const_(p.mod_eq_sub, vec![]);
        let applied = k.app(theorem, a);
        let proof = k.app(applied, b);
        k.infer(proof)
            .unwrap_or_else(|e| panic!("modEq_sub 17 5 should type-check: {e:?}"));

        let a2 = numeral(&mut k, &p, 17);
        let b2 = numeral(&mut k, &p, 5);
        let sub = k.const_(p.sub, vec![]);
        let sub_f = k.app(sub, a2);
        let diff = k.app(sub_f, b2);
        let a3 = numeral(&mut k, &p, 17);
        let lhs = emod_of(&mut k, a3, diff);
        let b3 = numeral(&mut k, &p, 5);
        let diff2 = {
            let a4 = numeral(&mut k, &p, 17);
            let b4 = numeral(&mut k, &p, 5);
            let sub2 = k.const_(p.sub, vec![]);
            let sub2_f = k.app(sub2, a4);
            k.app(sub2_f, b4)
        };
        let rhs = emod_of(&mut k, b3, diff2);
        assert!(
            k.def_eq(lhs, rhs),
            "modEq_sub 17 5: emod(a,a-b) must reduce to the same value as \
             emod(b,a-b)"
        );
    }

    // `Int.modEq_add_mul_left n a q` at a genuine `q` other than `±1`, so the
    // general multiplier is actually exercised (not just the specializations
    // above, all of which use `q := 1`).
    {
        let n = numeral(&mut k, &p, 5);
        let a = numeral(&mut k, &p, 2);
        let q = numeral(&mut k, &p, 3);
        let theorem = k.const_(p.mod_eq_add_mul_left, vec![]);
        let applied = k.app(theorem, n);
        let applied = k.app(applied, a);
        let proof = k.app(applied, q);
        k.infer(proof)
            .unwrap_or_else(|e| panic!("modEq_add_mul_left 5 2 3 should type-check: {e:?}"));

        let n2 = numeral(&mut k, &p, 5);
        let a2 = numeral(&mut k, &p, 2);
        let q2 = numeral(&mut k, &p, 3);
        let mul = k.const_(p.mul, vec![]);
        let mul_f = k.app(mul, n2);
        let nq = k.app(mul_f, q2);
        let shifted = add_of(&mut k, nq, a2);
        let n3 = numeral(&mut k, &p, 5);
        let lhs = emod_of(&mut k, shifted, n3);
        let a3 = numeral(&mut k, &p, 2);
        let n4 = numeral(&mut k, &p, 5);
        let rhs = emod_of(&mut k, a3, n4);
        assert!(
            k.def_eq(lhs, rhs),
            "modEq_add_mul_left 5 2 3: emod(n*q+a,n) must reduce to the \
             same value as emod(a,n)"
        );
        // 5*3+2 = 17, 17 emod 5 = 2, and 2 emod 5 = 2 -- confirm the shared
        // value is genuinely `2`, not two independently-stuck terms.
        let two = numeral(&mut k, &p, 2);
        assert!(
            k.def_eq(rhs, two),
            "modEq_add_mul_left 5 2 3: emod(a,n) must genuinely reduce to 2"
        );
    }
}

/// `Int.factorial` computes its normal form — `factorial 4` reduces to `24`
/// by β/δ/ι through `prodRange`'s own `Nat.rec` — and, symmetrically, the
/// trusted gate REJECTS the false claim that `factorial 4 = 23`. Same
/// discipline as [`prod_range_computes_and_rejects_a_false_product`]: a
/// checker that only ever confirms a computation is a checker that cannot
/// fail.
///
/// `4 = 5 - 1` is not incidental: `4! = 24 ≡ -1 [5]` is Wilson's theorem's
/// own headline instance (`5` prime), the concrete case
/// `self_inverse_mod_prime` and `factorial` exist to eventually assemble.
#[test]
fn factorial_computes_and_rejects_a_false_value() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();

    let four_nat = numeral_nat(&mut k, &p, 4);
    let factorial = k.const_(p.factorial, vec![]);
    let lhs = k.app(factorial, four_nat);

    let twenty_four = numeral(&mut k, &p, 24);
    assert!(
        k.def_eq(lhs, twenty_four),
        "factorial 4 should compute to 24"
    );

    // Negative control: the trusted gate must REFUSE `factorial 4 = 23`.
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let twenty_three = numeral(&mut k, &p, 23);
    let int_ty = k.const_(p.z, vec![]);
    let eq = k.const_(p.logic.eq, vec![level_one]);
    let false_stmt = {
        let e = k.app(eq, int_ty);
        let e = k.app(e, lhs);
        k.app(e, twenty_three)
    };
    let refl = k.const_(p.logic.eq_refl, vec![level_one]);
    let false_proof = {
        let r = k.app(refl, int_ty);
        k.app(r, twenty_four)
    };
    let scratch_name = k.name_str(anon, "factorial_false_claim_scratch");
    let result = k.add_declaration(Declaration::Theorem {
        name: scratch_name,
        uparams: vec![],
        ty: false_stmt,
        value: false_proof,
    });
    assert!(
        result.is_err(),
        "the trusted gate accepted a false claim that factorial 4 = 23"
    );
}

/// **The pairing collapse carries every hypothesis it needs, and no more.**
/// An empty axiom footprint cannot distinguish this theorem from one that
/// dropped `∀k<n, σ k ≠ k` — and that one is FALSE: without fixed-point
/// freedom, `σ = id` satisfies the involution and the pairing premises while
/// `prodRange F n` is `∏ F k`, not `∏ F k · F (σ k)`. So the statement is
/// pinned character for character, and the two premises whose loss would make
/// it false are asserted by name first.
///
/// Note also what is NOT here: no primality of `x0`. The collapse is a fact
/// about involutions without fixed points, and it holds for any positive
/// modulus. Primality enters only later, when `σ := Nat.inverseIndex p` is
/// supplied and one has to know the pairing exists.
#[test]
fn the_pairing_collapse_keeps_its_fixed_point_free_premise() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let ty = match k
        .environment()
        .get(p.prod_range_pairing_collapse)
        .expect("Int.prod_range_pairing_collapse must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => k.render_lean(*ty),
        other => panic!("{other:?} is not a theorem or definition"),
    };

    assert!(
        ty.contains("Not (Eq.{1} AxNat (x4 x7) x7)"),
        "dropping fixed-point freedom makes this FALSE at σ = id: {ty}"
    );
    assert!(
        ty.contains("Eq.{1} AxNat (x4 (x4 x8)) x8"),
        "dropping the involution premise makes the pairing unusable: {ty}"
    );
    assert!(
        !ty.contains("Prime"),
        "the collapse must NOT require primality -- it is a fact about \
         fixed-point-free involutions, and requiring a prime modulus would \
         narrow it to Wilson's own use: {ty}"
    );
    assert_eq!(ty, PROD_RANGE_PAIRING_COLLAPSE_TYPE);
}

/// The pinned type of [`IntPrelude::prod_range_pairing_collapse`].
const PROD_RANGE_PAIRING_COLLAPSE_TYPE: &str = "((x0 : Int) -> ((x1 : Int.lt Int.zero x0) -> ((x2 : AxNat) -> ((x3 : ((x3 : AxNat) -> Int)) -> ((x4 : ((x4 : AxNat) -> AxNat)) -> ((x5 : AxNat.injectiveOn x4 x2) -> ((x6 : AxNat.mapsInto x4 x2) -> ((x7 : ((x7 : AxNat) -> ((x8 : AxNat.lt x7 x2) -> Not (Eq.{1} AxNat (x4 x7) x7)))) -> ((x8 : ((x8 : AxNat) -> ((x9 : AxNat.lt x8 x2) -> Eq.{1} AxNat (x4 (x4 x8)) x8))) -> ((x9 : ((x9 : AxNat) -> ((x10 : AxNat.lt x9 x2) -> Int.ModEq x0 (Int.mul (x3 x9) (x3 (x4 x9))) Int.one))) -> Int.ModEq x0 (Int.prodRange x3 x2) Int.one))))))))))";

/// **Wilson's theorem carries the NEGATIVE conclusion, and primality, not a
/// weakened `0 < p`.**
///
/// An empty axiom footprint cannot tell `(p-1)! ≡ -1 [p]` apart from `(p-1)!
/// ≡ +1 [p]` (both would type-check as SOME theorem over the same
/// declarations), and it cannot tell "for every prime `p`" apart from "for
/// every `p` with `0 < p`" (composite moduli would sail through a positivity
/// hypothesis, which is precisely the case Wilson's theorem's actual content
/// excludes: `(n-1)! ≡ -1 [n]` is FALSE for composite `n`, e.g. `n=4`:
/// `3! = 6 ≡ 2 [4]`). So the statement itself is pinned character for
/// character, and the two distinctions that matter are asserted by name
/// first.
#[test]
fn wilson_concludes_the_negative_residue_under_primality() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let ty = match k
        .environment()
        .get(p.wilson)
        .expect("Int.wilson must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => k.render_lean(*ty),
        other => panic!("{other:?} is not a theorem or definition"),
    };

    assert!(
        ty.contains("Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one)"),
        "the conclusion must be the NEGATIVE residue `-1`, not `+1` -- a \
         theorem concluding `+1` would have an identically empty axiom \
         footprint and is simply FALSE (e.g. p=5: 4! = 24 ≡ 4 ≡ -1 [5], not \
         1): {ty}"
    );
    assert!(
        ty.contains("AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0")
            && ty.contains("AxNat.dvd x1 x0"),
        "the hypothesis must be PRIMALITY (2 <= p and every divisor is 1 or \
         p), not a weakened `0 < p` -- Wilson's theorem is false for \
         composite moduli (e.g. n=4: 3! = 6 = 2 [4], not -1): {ty}"
    );
    assert_eq!(ty, WILSON_TYPE);
}

/// The pinned type of [`IntPrelude::wilson`].
const WILSON_TYPE: &str = "((x0 : AxNat) -> ((x1 : And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) (((x1 : AxNat) -> ((x2 : AxNat.dvd x1 x0) -> Or (Eq.{1} AxNat x1 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x1 x0))))) -> Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one)))";

/// The converse of [`wilson_concludes_the_negative_residue_under_primality`]:
/// `Int.wilson_converse` must conclude PRIMALITY (`2 ≤ n ∧ ∀ d, d ∣ n → d = 1
/// ∨ d = n`), not merely `2 ≤ n` alone — a converse that only echoed its own
/// `2 ≤ n` hypothesis back would have an identically empty axiom footprint
/// and would assert nothing about `(n-1)! ≡ -1 [n]` at all. And it must take
/// the NEGATIVE residue as its hypothesis, not `+1` (which is simply false
/// for a prime modulus, e.g. `p=5`: `4! = 24 ≡ 4 ≡ -1 [5]`, not `1`) — a
/// theorem hypothesizing the false statement would prove nothing and could
/// still have an empty footprint. So the statement itself is pinned
/// character for character, and the two distinctions that matter are
/// asserted by name first.
#[test]
fn wilson_converse_concludes_primality_from_the_negative_residue() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let ty = match k
        .environment()
        .get(p.wilson_converse)
        .expect("Int.wilson_converse must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => k.render_lean(*ty),
        other => panic!("{other:?} is not a theorem or definition"),
    };

    assert!(
        ty.contains("Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one)"),
        "the hypothesis must be the NEGATIVE residue `-1`, not `+1` -- a \
         theorem hypothesizing `+1` would be vacuous for every prime modulus \
         (e.g. p=5: 4! = 24 ≡ 4 ≡ -1 [5], not 1) and could still carry an \
         empty axiom footprint: {ty}"
    );
    assert!(
        ty.contains("And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0)")
            && ty.contains("AxNat.dvd x3 x0")
            && ty.contains("Or (Eq.{1} AxNat x3 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x3 x0)"),
        "the CONCLUSION must be full primality (2 <= n and every divisor is \
         1 or n), not a weakened restatement of the `2 <= n` hypothesis -- \
         that would leave the converse asserting nothing about the \
         factorial hypothesis at all: {ty}"
    );
    assert_eq!(ty, WILSON_CONVERSE_TYPE);
}

/// The pinned type of [`IntPrelude::wilson_converse`].
const WILSON_CONVERSE_TYPE: &str = "((x0 : AxNat) -> ((x1 : AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) -> ((x2 : Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one)) -> And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) (((x3 : AxNat) -> ((x4 : AxNat.dvd x3 x0) -> Or (Eq.{1} AxNat x3 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x3 x0)))))))";

/// `Int.wilson_iff` must state an `Iff`, and each side must be the FULL
/// statement (not, e.g., only the `2 ≤ n` conjunct or a `+1` residue) --
/// otherwise this "combined" theorem would be strictly weaker than either
/// direction it is supposed to combine.
#[test]
fn wilson_iff_states_the_full_equivalence() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let ty = match k
        .environment()
        .get(p.wilson_iff)
        .expect("Int.wilson_iff must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => k.render_lean(*ty),
        other => panic!("{other:?} is not a theorem or definition"),
    };

    assert!(
        ty.contains("Iff"),
        "wilson_iff must state an Iff, not two one-way implications glued \
         together by name alone: {ty}"
    );
    assert!(
        ty.contains("Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one)"),
        "the equivalence must be with the NEGATIVE residue `-1`: {ty}"
    );
    assert!(
        ty.contains("Or (Eq.{1} AxNat x2 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x2 x0)"),
        "the primality side must carry the full divisor clause, not just \
         `2 <= n`: {ty}"
    );
    assert_eq!(ty, WILSON_IFF_TYPE);
}

/// The pinned type of [`IntPrelude::wilson_iff`].
const WILSON_IFF_TYPE: &str = "((x0 : AxNat) -> ((x1 : AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) -> Iff (And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x0) (((x2 : AxNat) -> ((x3 : AxNat.dvd x2 x0) -> Or (Eq.{1} AxNat x2 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x2 x0))))) (Int.ModEq (Int.ofNat x0) (Int.factorial (AxNat.sub x0 (AxNat.succ AxNat.zero))) (Int.neg Int.one))))";

/// **`Int.mul_eq_zero` computes at a concrete zero product, and the kernel
/// REFUSES reusing `Nat.mul_eq_zero` (ℕ's own integral-domain proof) at the
/// residue `2·3 ≡ 0 (mod 6)`.**
///
/// This is the negative control the `rings` curriculum node's "exhibit a
/// commutative ring that is not an integral domain" asks for (`ring.rs`'s doc
/// comment: ℤ/6, `2·3 ≡ 0` with neither factor `0`), stated at the level this
/// development actually has rather than a full `Nat.IsCommRingOn` bundle for
/// ℤ/n (which does not exist here — building one would need multiplicative
/// associativity/distributivity mod `n`, a separate development). What's
/// checked:
///
/// - `Int.mul_eq_zero` genuinely COMPUTES: applied at the concrete zero
///   product `0·5`, the kernel accepts `Or (0=0) (5=0)`.
/// - `2·3 mod 6` genuinely reduces to `0` — ℤ/6 has a real zero product here,
///   not a stated-but-unverified one.
/// - `2·3` itself (without the `mod 6`) does NOT reduce to `0` — the two
///   hypotheses are genuinely different propositions, not the same fact
///   under different names.
/// - Reusing `Nat.mul_eq_zero`'s own constant at `2, 3`, supplying the mod-6
///   fact where it demands the literal `Nat.mul 2 3 = Nat.zero`, is refused
///   by the trusted gate — a type mismatch, not merely an unproved goal.
///   `Int.IsCommRing`/`Nat`'s ring structure does not hand ℤ/6 the
///   integral-domain property for free, which is exactly the content the
///   `rings` node wants a learner to see.
#[test]
fn mul_eq_zero_computes_and_the_mod_six_reuse_is_refused() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };

    // --- positive: `Int.mul_eq_zero 0 5 (h : 0*5=0) : Or (0=0) (5=0)`. -----
    let int_ty = k.const_(p.z, vec![]);
    let zero = numeral(&mut k, &p, 0);
    let five = numeral(&mut k, &p, 5);
    let mul = k.const_(p.mul, vec![]);
    let product = {
        let e = k.app(mul, zero);
        k.app(e, five)
    };
    let eq_int = k.const_(p.logic.eq, vec![level_one]);
    let refl_int = k.const_(p.logic.eq_refl, vec![level_one]);
    let h_val = {
        let r = k.app(refl_int, int_ty);
        k.app(r, zero)
    };
    assert!(
        k.def_eq(product, zero),
        "0*5 must reduce to 0 for the h : 0*5=0 witness to check"
    );

    let mul_eq_zero = k.const_(p.mul_eq_zero, vec![]);
    let applied = {
        let e = k.app(mul_eq_zero, zero);
        let e = k.app(e, five);
        k.app(e, h_val)
    };
    let a_eq_zero_ty = {
        let e = k.app(eq_int, int_ty);
        let e = k.app(e, zero);
        k.app(e, zero)
    };
    let b_eq_zero_ty = {
        let e = k.app(eq_int, int_ty);
        let e = k.app(e, five);
        k.app(e, zero)
    };
    let or_ty = k.const_(p.logic.or, vec![]);
    let disj_ty = {
        let e = k.app(or_ty, a_eq_zero_ty);
        k.app(e, b_eq_zero_ty)
    };
    let name = k.name_str(anon, "Check.mul_eq_zero_at_zero_five");
    let accepted = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: disj_ty,
        value: applied,
    });
    assert!(
        accepted.is_ok(),
        "Int.mul_eq_zero must compute at 0*5=0: {accepted:?}"
    );

    // --- ℤ/6 genuinely has this zero product, computed. --------------------
    let two = numeral_nat(&mut k, &p, 2);
    let three = numeral_nat(&mut k, &p, 3);
    let six = numeral_nat(&mut k, &p, 6);
    let zero_nat = numeral_nat(&mut k, &p, 0);
    let nat_mul = k.const_(p.nat.mul, vec![]);
    let two_three = {
        let e = k.app(nat_mul, two);
        k.app(e, three)
    };
    let nat_mod = k.const_(p.nat.mod_, vec![]);
    let residue = {
        let e = k.app(nat_mod, two_three);
        k.app(e, six)
    };
    assert!(
        k.def_eq(residue, zero_nat),
        "2*3 mod 6 must reduce to 0 -- ZZ/6 genuinely has this zero product"
    );
    assert!(
        !k.def_eq(two_three, zero_nat),
        "2*3 itself must NOT reduce to 0 -- this is what makes reusing \
         Nat.mul_eq_zero at the residue a type error, not merely unproved"
    );

    let nat_ty = k.const_(p.nat.nat, vec![]);
    let eq_nat = k.const_(p.nat.logic.eq, vec![level_one]);
    let refl_nat = k.const_(p.nat.logic.eq_refl, vec![level_one]);
    let residue_h_ty = {
        let e = k.app(eq_nat, nat_ty);
        let e = k.app(e, residue);
        k.app(e, zero_nat)
    };
    let residue_h_val = {
        let r = k.app(refl_nat, nat_ty);
        k.app(r, residue)
    };
    let sanity_name = k.name_str(anon, "Check.residue_eq_zero");
    let sanity = k.add_declaration(Declaration::Theorem {
        name: sanity_name,
        uparams: vec![],
        ty: residue_h_ty,
        value: residue_h_val,
    });
    assert!(
        sanity.is_ok(),
        "2*3 mod 6 = 0 must check by computation alone: {sanity:?}"
    );

    // --- NEGATIVE CONTROL: reuse `Nat.mul_eq_zero` (ZZ's own integral-domain
    // proof) at 2,3, supplying the mod-6 witness where it demands the
    // LITERAL `Nat.mul 2 3 = Nat.zero`.
    let nat_mul_eq_zero = k.const_(p.nat.mul_eq_zero, vec![]);
    let bad_body = {
        let e = k.app(nat_mul_eq_zero, two);
        let e = k.app(e, three);
        k.app(e, residue_h_val)
    };
    let two_eq_zero_ty = {
        let e = k.app(eq_nat, nat_ty);
        let e = k.app(e, two);
        k.app(e, zero_nat)
    };
    let three_eq_zero_ty = {
        let e = k.app(eq_nat, nat_ty);
        let e = k.app(e, three);
        k.app(e, zero_nat)
    };
    let nat_or = k.const_(p.nat.logic.or, vec![]);
    let bad_ty = {
        let e = k.app(nat_or, two_eq_zero_ty);
        k.app(e, three_eq_zero_ty)
    };
    let bad_name = k.name_str(anon, "Check.mod_six_reuses_the_integral_domain_proof");
    let bad_accepted = k.add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: bad_body,
    });
    assert!(
        bad_accepted.is_err(),
        "the trusted gate ACCEPTED reusing Nat.mul_eq_zero's own constant \
         with a mod-6 hypothesis standing in for a literal-zero one -- ZZ/6 \
         would wrongly inherit the integral-domain property: {bad_accepted:?}"
    );
}

/// Euler's totient theorem's numeric content, at `n = 10`: `φ(10) = 4` and
/// `3^4 = 81 ≡ 1 (mod 10)` (`3` is a unit mod `10`, since `gcd(3,10)=1`) —
/// checked by kernel REDUCTION, not merely stated. `Int.euler_totient_theorem`
/// itself is not proved in this kernel (see `euler_totient.rs`'s module doc
/// for exactly what is missing and why), so this pins down the underlying
/// arithmetic claim directly.
///
/// Negative control: `3^2 = 9 ≢ 1 (mod 10)` — the check above is sensitive to
/// the actual exponent `4 = φ(10)`, not vacuously true for any exponent.
#[test]
fn euler_totient_content_reduces_at_n_equals_10() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let three = numeral(&mut k, &p, 3);
    let ten = numeral(&mut k, &p, 10);
    let four_nat = numeral_nat(&mut k, &p, 4);
    let two_nat = numeral_nat(&mut k, &p, 2);

    let pow = k.const_(p.pow, vec![]);
    let emod = k.const_(p.emod, vec![]);

    let three_pow_4 = {
        let f = k.app(pow, three);
        k.app(f, four_nat)
    };
    let residue_4 = {
        let f = k.app(emod, three_pow_4);
        k.app(f, ten)
    };
    let one = numeral(&mut k, &p, 1);
    assert!(
        k.def_eq(residue_4, one),
        "3^4 mod 10 must reduce to 1 (phi(10) = 4, and 3 is a unit mod 10)"
    );

    let three_pow_2 = {
        let f = k.app(pow, three);
        k.app(f, two_nat)
    };
    let residue_2 = {
        let f = k.app(emod, three_pow_2);
        k.app(f, ten)
    };
    let nine = numeral(&mut k, &p, 9);
    assert!(k.def_eq(residue_2, nine), "3^2 mod 10 must reduce to 9");
    assert!(
        !k.def_eq(residue_2, one),
        "3^2 mod 10 must NOT reduce to 1 -- otherwise the exponent 4 in the \
         check above would be doing no work"
    );
}

/// `Int.euler_unit_coprime` is not vacuous: instantiated at `n=10, a=3, k=7`
/// (both units mod `10`), the SAME `Eq.refl` shape that proves `Coprime a n`
/// and `Coprime k n` (both reduce `gcd _ 10` to `1`) closes the whole
/// application, giving a genuine proof that `emod (3*7) 10` (`= 1`) is
/// coprime to `10`. The negative control swaps `k=7` for `k=2`
/// (`gcd(2,10)=2`): the identically-shaped `Coprime k n` proof is REFUSED by
/// the trusted gate, because `gcd 2 10` does NOT reduce to `1`.
#[test]
fn euler_unit_coprime_instantiates_at_n_10_a_3_and_rejects_a_non_unit() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let nat_ty = k.const_(p.nat.nat, vec![]);

    let ten = numeral(&mut k, &p, 10);
    let three = numeral(&mut k, &p, 3);
    let seven = numeral(&mut k, &p, 7);
    let two = numeral(&mut k, &p, 2);

    // `Int.lt (ofNat 0) (ofNat 10)` is definitionally `Nat.lt 0 10 =
    // Nat.le 1 10` (`defs.rs::declare_order_definitions`'s ofNat-ofNat
    // branch), built the same way `rat_admits_a_normalised_pair_and_rejects_
    // an_unreduced_one` builds `1 <= den`: `le_succ_succ zero 9 (zero_le 9)`.
    let nine_nat = numeral_nat(&mut k, &p, 9);
    let zero_nat = numeral_nat(&mut k, &p, 0);
    let h_pos = {
        let base = {
            let lemma = k.const_(p.nat.zero_le, vec![]);
            k.app(lemma, nine_nat)
        };
        let lemma = k.const_(p.nat.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero_nat);
        let at_pred = k.app(at_zero, nine_nat);
        k.app(at_pred, base)
    };

    // `Coprime a n := Eq Nat (gcd a n) 1`, discharged by `rfl` at `1` --
    // typechecks only when `gcd a n` actually reduces to `1`.
    let coprime_refl = |k: &mut Kernel| -> crate::ExprId {
        let refl = k.const_(p.logic.eq_refl, vec![level_one]);
        let at_ty = k.app(refl, nat_ty);
        let one_nat = numeral_nat(k, &p, 1);
        k.app(at_ty, one_nat)
    };

    let h_cop_a = coprime_refl(&mut k);
    let h_cop_k_good = coprime_refl(&mut k);

    let f = k.const_(p.euler_unit_coprime, vec![]);
    let applied = {
        let f = k.app(f, ten);
        let f = k.app(f, three);
        let f = k.app(f, seven);
        let f = k.app(f, h_pos);
        let f = k.app(f, h_cop_a);
        k.app(f, h_cop_k_good)
    };
    k.infer(applied)
        .expect("Int.euler_unit_coprime applied at n=10, a=3, k=7 must type-check");

    // Negative control: k=2 is NOT coprime to 10 (gcd(2,10)=2).
    let h_cop_k_bad = coprime_refl(&mut k);
    let f2 = k.const_(p.euler_unit_coprime, vec![]);
    let applied_bad = {
        let f2 = k.app(f2, ten);
        let f2 = k.app(f2, three);
        let f2 = k.app(f2, two);
        let f2 = k.app(f2, h_pos);
        let f2 = k.app(f2, h_cop_a);
        k.app(f2, h_cop_k_bad)
    };
    assert!(
        k.infer(applied_bad).is_err(),
        "the trusted gate accepted `Coprime 2 10` via a proof that \
         gcd(2,10)=1, which is FALSE"
    );
}

/// `Nat.gcdA` / `Nat.gcdB` **compute**, and the values they compute satisfy
/// Bézout's identity numerically.
///
/// This is the `the_operations_compute_their_normal_forms` discipline applied
/// to the extended Euclidean witnesses: a type-checked `Nat.gcd_eq_gcd_ab`
/// would be satisfied by *some* pair of coefficients, so the identity alone
/// does not pin the algorithm down. Here every case is evaluated to a normal
/// form and checked against a hand-computed answer, and each is then
/// substituted back into `gcd m n = m*A + n*B` and evaluated again — so a
/// transposed selector or an off-by-one fuel shows up as a wrong integer, not
/// as a proof failure.
///
/// Magnitudes are deliberately tiny (nothing above `6`). Every `Nat` numeral
/// this prelude forms is unary, so the kernel's binary-literal fast path never
/// fires and cost is superlinear in the largest magnitude formed.
#[test]
fn nat_gcd_ab_compute_bezout_coefficients() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // (m, n, gcd m n, gcdA m n, gcdB m n) -- hand-computed from the three
    // definitional equations in `bezout_witnesses.rs`'s module doc.
    for (m, n, gcd, want_a, want_b) in [
        (0_u32, 5_u32, 5_i32, 0_i32, 1_i32),
        (5, 0, 5, 1, 0),
        (3, 2, 1, 1, -1),
        (2, 3, 1, -1, 1),
        (4, 6, 2, -1, 1),
        (6, 4, 2, 1, -1),
        (1, 1, 1, 1, 0),
    ] {
        let m_nat = numeral_nat(&mut k, &p, m);
        let n_nat = numeral_nat(&mut k, &p, n);

        // The gcd itself, so a wrong `gcd` cannot make a wrong pair look right.
        let g = {
            let f = k.const_(p.nat.gcd, vec![]);
            let f = k.app(f, m_nat);
            k.app(f, n_nat)
        };
        let want_gcd = numeral_nat(&mut k, &p, u32::try_from(gcd).expect("nonneg"));
        assert!(k.def_eq(g, want_gcd), "gcd {m} {n} should be {gcd}");

        for (name, want) in [(p.nat_gcd_a, want_a), (p.nat_gcd_b, want_b)] {
            let f = k.const_(name, vec![]);
            let f = k.app(f, m_nat);
            let applied = k.app(f, n_nat);
            let expected = numeral(&mut k, &p, want);
            assert!(
                k.def_eq(applied, expected),
                "{} {m} {n} should be {want}",
                k.display_name(name)
            );
        }

        // ... and the identity itself evaluates: gcd m n = m*A + n*B.
        let coeff_a = {
            let f = k.const_(p.nat_gcd_a, vec![]);
            let f = k.app(f, m_nat);
            k.app(f, n_nat)
        };
        let coeff_b = {
            let f = k.const_(p.nat_gcd_b, vec![]);
            let f = k.app(f, m_nat);
            k.app(f, n_nat)
        };
        let m_int = numeral(&mut k, &p, i32::try_from(m).expect("small"));
        let n_int = numeral(&mut k, &p, i32::try_from(n).expect("small"));
        let left = {
            let f = k.const_(p.mul, vec![]);
            let f = k.app(f, m_int);
            k.app(f, coeff_a)
        };
        let right = {
            let f = k.const_(p.mul, vec![]);
            let f = k.app(f, n_int);
            k.app(f, coeff_b)
        };
        let sum = {
            let f = k.const_(p.add, vec![]);
            let f = k.app(f, left);
            k.app(f, right)
        };
        let want_sum = numeral(&mut k, &p, gcd);
        assert!(
            k.def_eq(sum, want_sum),
            "Bezout should evaluate: gcd {m} {n} = {m}*{want_a} + {n}*{want_b} = {gcd}"
        );
    }
}

/// `Int.gcdA` / `Int.gcdB` compute in **all four sign branches**, and Bézout
/// evaluates in each.
///
/// The sign flip is the whole content of the `Int` layer: `negSucc k` is
/// `-(k+1)` while `natAbs (negSucc k)` is `k+1`, so the coefficient must negate
/// to leave `x * gcdA x y` unchanged. A transposed branch would type-check
/// against any statement that never evaluates; only this catches it.
#[test]
fn int_gcd_ab_compute_in_every_sign_branch() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // (x, y, gcd x y, gcdA x y, gcdB x y).
    for (x, y, gcd, want_a, want_b) in [
        (3_i32, 2_i32, 1_i32, 1_i32, -1_i32),
        (-3, 2, 1, -1, -1),
        (3, -2, 1, 1, 1),
        (-3, -2, 1, -1, 1),
        (0, 5, 5, 0, 1),
        (-4, 6, 2, 1, 1),
    ] {
        let x_int = numeral(&mut k, &p, x);
        let y_int = numeral(&mut k, &p, y);

        for (name, want) in [(p.gcd_a, want_a), (p.gcd_b, want_b)] {
            let f = k.const_(name, vec![]);
            let f = k.app(f, x_int);
            let applied = k.app(f, y_int);
            let expected = numeral(&mut k, &p, want);
            assert!(
                k.def_eq(applied, expected),
                "{} {x} {y} should be {want}",
                k.display_name(name)
            );
        }

        let coeff_a = {
            let f = k.const_(p.gcd_a, vec![]);
            let f = k.app(f, x_int);
            k.app(f, y_int)
        };
        let coeff_b = {
            let f = k.const_(p.gcd_b, vec![]);
            let f = k.app(f, x_int);
            k.app(f, y_int)
        };
        let left = {
            let f = k.const_(p.mul, vec![]);
            let f = k.app(f, x_int);
            k.app(f, coeff_a)
        };
        let right = {
            let f = k.const_(p.mul, vec![]);
            let f = k.app(f, y_int);
            k.app(f, coeff_b)
        };
        let sum = {
            let f = k.const_(p.add, vec![]);
            let f = k.app(f, left);
            k.app(f, right)
        };
        let want_sum = numeral(&mut k, &p, gcd);
        assert!(
            k.def_eq(sum, want_sum),
            "Bezout should evaluate at ({x}, {y}): {gcd} = {x}*{want_a} + {y}*{want_b}"
        );
    }
}

/// The declarations this prelude makes into the **`Nat`** namespace are checked
/// and axiom-free.
///
/// `every_int_declaration_is_checked_and_axiom_free` filters on the `Int.`
/// prefix, so it is structurally blind to them — and a prelude declaring into
/// another prelude's namespace is not hypothetical here (`wilson.rs` puts
/// `Nat.inverseIndex` and eight lemmas there; `bezout_witnesses.rs` puts
/// `Nat.xgcdAux`/`Nat.gcdA`/`Nat.gcdB` there to match Mathlib's names). The
/// list is derived from the ENVIRONMENT, not hand-maintained: every `Nat.`
/// declaration that the *integer* prelude added and the *natural* prelude did
/// not is checked, so a new one cannot be forgotten.
#[test]
fn nat_namespace_declarations_made_by_the_int_prelude_are_axiom_free() {
    let mut nat_only = Kernel::new();
    crate::build_nat_prelude(&mut nat_only).expect("Nat prelude must build");
    let already: std::collections::BTreeSet<String> = nat_only
        .environment()
        .iter()
        .map(|(name, _)| nat_only.display_name(*name).to_string())
        .collect();

    let mut k = Kernel::new();
    build_int_prelude(&mut k).expect("Int prelude must build");
    let added: Vec<crate::NameId> = k
        .environment()
        .iter()
        .filter(|(name, decl)| {
            matches!(
                decl,
                Declaration::Definition { .. } | Declaration::Theorem { .. }
            ) && {
                let shown = k.display_name(**name).to_string();
                shown.starts_with("Nat.") && !already.contains(&shown)
            }
        })
        .map(|(name, _)| *name)
        .collect();

    assert!(
        !added.is_empty(),
        "the Int prelude declares into the `Nat` namespace (`Nat.inverseIndex`, \
         `Nat.xgcdAux`, ...), so an empty list means this test is aimed at \
         nothing -- a passing run would prove no axiom-freedom at all"
    );
    for name in &added {
        let footprint = k.axiom_footprint(*name);
        assert!(
            footprint.is_empty(),
            "{} is declared by the Int prelude into the `Nat` namespace and \
             rests on {:?}",
            k.display_name(*name),
            footprint
                .iter()
                .map(|a| k.display_name(*a).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// `Int.Odd`/`Int.Even` apply at concrete values of BOTH signs — the whole
/// point of an `Int`-level (rather than `Nat`-level) parity predicate.
///
/// A predicate that is accidentally true of the wrong parity type-checks
/// exactly as well as a correct one (`CLAUDE.md`'s guard for this task), so
/// each case below builds a genuine kernel-checked witness — never an
/// absence-of-proof argument — and confirms it lands on the `Int` predicate
/// via `Kernel::def_eq`, the same technique
/// `parity_predicates_apply_at_concrete_witnesses_and_are_axiom_free`
/// (`nat_prelude_tests.rs`) uses for the `Nat` version.
///
/// - `Odd (ofNat 3)`: witnessed directly by `Nat.Odd 3` (`3 = succ(1+1)`).
/// - `Not (Odd (ofNat 4))`: `even_not_odd` applied to a hand-built `Even 4`
///   (`4 = 2+2`) — a genuine proof of refutability, not merely an absent one.
/// - `Odd (negSucc 2)` (i.e. `Odd (-3)`): the SAME `Nat.Odd 3` witness,
///   because `natAbs (negSucc 2) ≡ succ 2 ≡ 3` — confirming sign handling is
///   free, exactly as the module doc claims.
/// - `Not (Odd (negSucc 3))` (i.e. `Not (Odd (-4))`): the SAME `Not (Nat.Odd
///   4)` witness, since `natAbs (negSucc 3) ≡ succ 3 ≡ 4`.
#[test]
fn int_odd_applies_at_concrete_values_of_both_signs() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    let nat = d.nat_ty();
    let one = d.level_one();

    let three = d.num(3);
    let four = d.num(4);
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    // Nat.Odd 3, witnessed by 1 (3 = succ(1+1)).
    let odd3_nat = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let kk = d.add(kv, kv);
        let skk = d.succ(kk);
        let body = d.eq(three, skk);
        let pred = d.lam_fv(k_fv, nat, body);
        let proof = d.refl(three);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        d.apply(intro, &[nat, pred, one_nat, proof])
    };

    // Nat.Even 4, witnessed by 2 (4 = 2+2).
    let even4_nat = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let kk = d.add(kv, kv);
        let body = d.eq(four, kk);
        let pred = d.lam_fv(k_fv, nat, body);
        let proof = d.refl(four);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        d.apply(intro, &[nat, pred, two_nat, proof])
    };
    // Not (Nat.Odd 4), via even_not_odd(4) applied to even4_nat.
    let not_odd4_nat = {
        let even_not_odd_at_4 = d.lemma(p.nat.even_not_odd, &[four]);
        d.apply(even_not_odd_at_4, &[even4_nat])
    };

    // -- ofNat 3 : Odd (ofNat 3) --------------------------------------------
    let ofnat3 = d.of_nat(three);
    let odd_ofnat3_ty = d.const_app(p.odd, &[ofnat3]);
    let odd3_nat_ty = d
        .kernel()
        .infer(odd3_nat)
        .unwrap_or_else(|e| panic!("Nat.Odd 3 (witness 1) should type-check: {e:?}"));
    assert!(
        d.kernel().def_eq(odd3_nat_ty, odd_ofnat3_ty),
        "the Nat.Odd 3 witness must also land on Int.Odd (ofNat 3)"
    );

    // -- ofNat 4 : Not (Odd (ofNat 4)) ---------------------------------------
    let ofnat4 = d.of_nat(four);
    let not_odd_ofnat4_ty = {
        let odd_ofnat4_ty = d.const_app(p.odd, &[ofnat4]);
        d.not(odd_ofnat4_ty)
    };
    let not_odd4_nat_ty = d
        .kernel()
        .infer(not_odd4_nat)
        .unwrap_or_else(|e| panic!("Not (Nat.Odd 4) should type-check: {e:?}"));
    assert!(
        d.kernel().def_eq(not_odd4_nat_ty, not_odd_ofnat4_ty),
        "even_not_odd(4) applied to Even 4 must also land on Not (Int.Odd (ofNat 4))"
    );

    // -- negSucc 2 (i.e. -3) : Odd (negSucc 2) -------------------------------
    let neg_succ_2 = d.neg_succ(two_nat);
    let odd_neg3_ty = d.const_app(p.odd, &[neg_succ_2]);
    assert!(
        d.kernel().def_eq(odd3_nat_ty, odd_neg3_ty),
        "the SAME Nat.Odd 3 witness must also land on Int.Odd (negSucc 2) = \
         Int.Odd (-3), since natAbs (negSucc 2) reduces to 3"
    );

    // -- negSucc 3 (i.e. -4) : Not (Odd (negSucc 3)) -------------------------
    let three_nat_for_neg = d.num(3);
    let neg_succ_3 = d.neg_succ(three_nat_for_neg);
    let not_odd_neg4_ty = {
        let odd_neg4_ty = d.const_app(p.odd, &[neg_succ_3]);
        d.not(odd_neg4_ty)
    };
    assert!(
        d.kernel().def_eq(not_odd4_nat_ty, not_odd_neg4_ty),
        "the SAME Not (Nat.Odd 4) witness must also land on Not (Int.Odd \
         (negSucc 3)) = Not (Int.Odd (-4)), since natAbs (negSucc 3) reduces \
         to 4"
    );

    assert!(
        d.kernel().axiom_footprint(p.odd).is_empty(),
        "Int.Odd must rest on zero axioms"
    );
    assert!(
        d.kernel().axiom_footprint(p.even).is_empty(),
        "Int.Even must rest on zero axioms"
    );
    assert!(
        d.kernel().axiom_footprint(p.odd_iff_nat_abs_odd).is_empty(),
        "Int.odd_iff_nat_abs_odd must rest on zero axioms"
    );
    assert!(
        d.kernel()
            .axiom_footprint(p.even_iff_nat_abs_even)
            .is_empty(),
        "Int.even_iff_nat_abs_even must rest on zero axioms"
    );
}

/// `Int.fib_of_odd` at a concrete odd index of EACH sign: `fib 3 = 2` and
/// `fib (-3) = fib (negSucc 2) = 2` (`natAbs (-3) = 3`, and `Nat.fib 3 = 2`).
/// Uses the same `Nat.Odd 3` witness [`int_odd_applies_at_concrete_values_of_both_signs`]
/// builds, ascribed at each sign via `Kernel::def_eq`.
#[test]
fn fib_of_odd_applies_at_a_concrete_odd_index_of_each_sign() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    let nat = d.nat_ty();
    let one = d.level_one();
    let three = d.num(3);
    let two_nat = d.num(2);
    let one_nat = d.num(1);

    // Nat.Odd 3, witnessed by 1 (3 = succ(1+1)) -- same construction as above.
    let odd3_nat = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let kk = d.add(kv, kv);
        let skk = d.succ(kk);
        let body = d.eq(three, skk);
        let pred = d.lam_fv(k_fv, nat, body);
        let proof = d.refl(three);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        d.apply(intro, &[nat, pred, one_nat, proof])
    };

    let ofnat3 = d.of_nat(three);
    // The raw witness's natural type is `Nat.Odd 3`; passing it where
    // `fib_of_odd`'s hypothesis wants `Int.Odd (ofNat 3)` relies on the
    // kernel's own defeq check at `add_declaration`/`apply`-time — exactly
    // what `fib_of_odd`'s ofNat branch itself relies on.
    let fib_at_pos = d.lemma(p.fib_of_odd, &[ofnat3]);
    let fib3_pos = d.apply(fib_at_pos, &[odd3_nat]);
    let fib3_pos_ty = d
        .kernel()
        .infer(fib3_pos)
        .unwrap_or_else(|e| panic!("fib_of_odd (ofNat 3) (Odd 3) should type-check: {e:?}"));
    let expected_pos_ty = {
        let fib3 = d.const_app(p.fib, &[ofnat3]);
        let two = d.num(2);
        let rhs = d.of_nat(two);
        d.ieq(fib3, rhs)
    };
    assert!(
        d.kernel().def_eq(fib3_pos_ty, expected_pos_ty),
        "fib_of_odd (ofNat 3) (Odd 3) must land on Eq Int (fib 3) (ofNat 2)"
    );

    let neg_succ_2 = d.neg_succ(two_nat);
    let fib_at_neg = d.lemma(p.fib_of_odd, &[neg_succ_2]);
    let fib3_neg = d.apply(fib_at_neg, &[odd3_nat]);
    let fib3_neg_ty = d
        .kernel()
        .infer(fib3_neg)
        .unwrap_or_else(|e| panic!("fib_of_odd (negSucc 2) (Odd (-3)) should type-check: {e:?}"));
    let expected_neg_ty = {
        let fib_neg3 = d.const_app(p.fib, &[neg_succ_2]);
        let two = d.num(2);
        let rhs = d.of_nat(two);
        d.ieq(fib_neg3, rhs)
    };
    assert!(
        d.kernel().def_eq(fib3_neg_ty, expected_neg_ty),
        "fib_of_odd (negSucc 2) (Odd (-3)) must land on Eq Int (fib (-3)) (ofNat 2)"
    );

    assert!(
        d.kernel().axiom_footprint(p.fib_of_odd).is_empty(),
        "Int.fib_of_odd must rest on zero axioms"
    );
}

/// `Int.fib_two_mul_add_one_eq_natfib_natabs` (`F:ml430-int-fib-two-mul-add-one-eq-natfib-natabs-61a8342b`)
/// instantiated at `n := 1` (`2*1+1 = 3`) and `n := negSucc 1` (`2*(-2)+1 =
/// -3 = negSucc 2`) — the SAME two closed values
/// [`fib_of_odd_applies_at_a_concrete_odd_index_of_each_sign`] checks
/// (`fib 3 = fib (-3) = 2`), reached this time through the composite theorem
/// itself (`odd_two_mul_add_one` then `fib_of_odd`) rather than a
/// hand-built `Nat.Odd` witness, so this exercises the wiring between the
/// two new declarations end to end, not just each in isolation.
#[test]
fn fib_two_mul_add_one_eq_natfib_natabs_applies_at_a_concrete_index_of_each_sign() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    let two_nat = d.num(2);
    let one_nat = d.num(1);

    // n := ofNat 1  =>  index = 2*1+1 = 3.
    let n_pos = d.of_nat(one_nat);
    let instance_pos = d.lemma(p.fib_two_mul_add_one_eq_natfib_natabs, &[n_pos]);
    let instance_pos_ty = d.kernel().infer(instance_pos).unwrap_or_else(|e| {
        panic!("fib_two_mul_add_one_eq_natfib_natabs (ofNat 1) should type-check: {e:?}")
    });
    let expected_pos_ty = {
        let three = d.num(3);
        let ofnat3 = d.of_nat(three);
        let fib3 = d.const_app(p.fib, &[ofnat3]);
        let two = d.num(2);
        let rhs = d.of_nat(two);
        d.ieq(fib3, rhs)
    };
    assert!(
        d.kernel().def_eq(instance_pos_ty, expected_pos_ty),
        "fib_two_mul_add_one_eq_natfib_natabs (ofNat 1) must land on Eq Int (fib 3) (ofNat 2)"
    );

    // n := negSucc 1  =>  n = -2, index = 2*(-2)+1 = -3 = negSucc 2.
    let n_neg = d.neg_succ(one_nat);
    let instance_neg = d.lemma(p.fib_two_mul_add_one_eq_natfib_natabs, &[n_neg]);
    let instance_neg_ty = d.kernel().infer(instance_neg).unwrap_or_else(|e| {
        panic!("fib_two_mul_add_one_eq_natfib_natabs (negSucc 1) should type-check: {e:?}")
    });
    let expected_neg_ty = {
        let neg_succ_2 = d.neg_succ(two_nat);
        let fib_neg3 = d.const_app(p.fib, &[neg_succ_2]);
        let two = d.num(2);
        let rhs = d.of_nat(two);
        d.ieq(fib_neg3, rhs)
    };
    assert!(
        d.kernel().def_eq(instance_neg_ty, expected_neg_ty),
        "fib_two_mul_add_one_eq_natfib_natabs (negSucc 1) must land on Eq Int (fib (-3)) (ofNat 2)"
    );

    assert!(
        d.kernel()
            .axiom_footprint(p.fib_two_mul_add_one_eq_natfib_natabs)
            .is_empty(),
        "Int.fib_two_mul_add_one_eq_natfib_natabs must rest on zero axioms"
    );
    assert!(
        d.kernel().axiom_footprint(p.odd_two_mul_add_one).is_empty(),
        "Int.odd_two_mul_add_one must rest on zero axioms"
    );
}

/// `Int.fib_add` read at one `(m, n)` pair in every sign combination, with the
/// arithmetic checked by reduction.
///
/// This is the only check that the *statement* is Mathlib's. The gate proves
/// whatever it is handed, and this statement has four places a transposition
/// would go unnoticed — `fib (m-1) * fib n` against `fib m * fib (n+1)`, and
/// either factor's index. Every case below is a closed numeric identity:
///
/// | `m` | `n` | `fib(m+n)` | `fib(m-1)·fib n + fib m·fib(n+1)` |
/// | --- | --- | --- | --- |
/// | `3` | `4` | `13` | `1·3 + 2·5` |
/// | `0` | `3` | `2` | `1·2 + 0·3` — `fib(-1)` already, at `m = 0` |
/// | `-2` | `3` | `1` | `2·2 + (-1)·3` |
/// | `3` | `-2` | `1` | `1·(-1) + 2·1` |
/// | `-1` | `-2` | `2` | `(-1)·(-1) + 1·1` |
///
/// Only the first row is within reach of `Nat.fib_add`; the second already
/// reads `fib` at a negative index, which is why the ℕ theorem cannot be
/// bridged into this one by sign bookkeeping.
#[test]
fn fib_add_computes_in_every_sign_combination() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    let of = |d: &mut super::ops::IntDev<'_>, v: u32| {
        let n = d.num(v);
        d.of_nat(n)
    };
    let neg = |d: &mut super::ops::IntDev<'_>, v: u32| {
        let n = d.num(v);
        d.neg_succ(n)
    };

    // (m, n, fib(m+n), a value fib(m+n) is NOT)
    let cases: [(ExprId, ExprId, ExprId, ExprId); 5] = {
        let three = of(&mut d, 3);
        let four = of(&mut d, 4);
        let thirteen = of(&mut d, 13);
        let twelve = of(&mut d, 12);
        let zero_i = d.izero();
        let two = of(&mut d, 2);
        let one = d.ione();
        let minus_two = neg(&mut d, 1);
        let minus_one = neg(&mut d, 0);
        [
            (three, four, thirteen, twelve),
            (zero_i, three, two, three),
            (minus_two, three, one, zero_i),
            (three, minus_two, one, zero_i),
            (minus_one, minus_two, two, three),
        ]
    };

    for (m, n, truth, falsehood) in cases {
        let instance = d.lemma(p.fib_add, &[m, n]);
        let ty = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("Int.fib_add must instantiate: {e:?}"));
        let sum = d.iadd(m, n);
        let lhs = d.const_app(p.fib, &[sum]);
        let expected = d.ieq(lhs, truth);
        assert!(
            d.kernel().def_eq(ty, expected),
            "fib_add's instance must reduce to the true arithmetic identity"
        );
        let wrong = d.ieq(lhs, falsehood);
        assert!(
            !d.kernel().def_eq(ty, wrong),
            "the check above must be capable of failing"
        );
    }

    assert!(
        d.kernel().axiom_footprint(p.fib_add).is_empty(),
        "Int.fib_add must rest on zero axioms"
    );
}

/// `Int.fib_rec` read at one index in each of its three branches, and the
/// resulting numeric identity checked by reduction.
///
/// The gate proves whatever statement it is handed: `fib (n+2) = fib (n+1) +
/// fib n` with the summands transposed, or with `fib (n+2)` mis-indexed, would
/// type-check just as happily if the proof were built to match. What rules that
/// out is instantiating at concrete indices where both sides are closed terms
/// and comparing against the arithmetic — `5 = 3 + 2` at `n = 3`, `1 = 1 + 0`
/// at `n = -1` (the `subNatNat` corner), and `-1 = 2 + (-3)` at `n = -4` (the
/// branch that does the sign algebra). Each is paired with a wrong right-hand
/// side that must NOT be accepted.
#[test]
fn fib_rec_computes_the_recurrence_at_indices_of_both_signs() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    // (index, expected value of `fib (index + 2)`, a value it is NOT).
    let cases: [(ExprId, ExprId, ExprId); 3] = {
        let three = d.num(3);
        let pos = d.of_nat(three);
        let five = d.num(5);
        let pos_true = d.of_nat(five);
        let four = d.num(4);
        let pos_false = d.of_nat(four);

        // n = -1: fib 1 = fib 0 + fib (-1), i.e. 1 = 0 + 1.
        let zero_nat = d.zero();
        let minus_one = d.neg_succ(zero_nat);
        let one_nat = d.num(1);
        let minus_one_true = d.of_nat(one_nat);
        let zero_i = d.izero();

        // n = -4: fib (-2) = fib (-3) + fib (-4), i.e. -1 = 2 + (-3).
        let three_nat = d.num(3);
        let minus_four = d.neg_succ(three_nat);
        let minus_four_true = d.neg_succ(zero_nat);
        let minus_four_false = d.of_nat(one_nat);

        [
            (pos, pos_true, pos_false),
            (minus_one, minus_one_true, zero_i),
            (minus_four, minus_four_true, minus_four_false),
        ]
    };

    for (index, truth, falsehood) in cases {
        let instance = d.lemma(p.fib_rec, &[index]);
        let ty = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("Int.fib_rec must instantiate: {e:?}"));

        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let shifted = d.iadd(index, two);
        let lhs = d.const_app(p.fib, &[shifted]);

        let expected = d.ieq(lhs, truth);
        assert!(
            d.kernel().def_eq(ty, expected),
            "fib_rec's instance must reduce to the true arithmetic identity"
        );
        let wrong = d.ieq(lhs, falsehood);
        assert!(
            !d.kernel().def_eq(ty, wrong),
            "the check above must be capable of failing"
        );
    }

    assert!(
        d.kernel().axiom_footprint(p.fib_rec).is_empty(),
        "Int.fib_rec must rest on zero axioms"
    );
}

/// `Int.induction_on` applied to a real motive, and the result read at an
/// index of **each sign**.
///
/// The motive is `zero + n = n`, which the prelude does not carry (it has
/// `add_zero`, not `zero_add`), so both steps genuinely consume the induction
/// hypothesis rather than re-deriving the goal from an existing lemma.
/// Reading the conclusion at `negSucc 4` (`-5`) is the half that an
/// `ofNat`-only combinator could not produce.
#[test]
fn induction_on_proves_a_two_sided_law_and_reaches_both_signs() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    let int_ty = d.int_ty();
    let izero = d.izero();
    let ione = d.ione();

    // P n := Eq Int (add zero n) n
    let motive = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let lhs = d.iadd(izero, n);
        let body = d.ieq(lhs, n);
        d.lam_fv(n_fv, int_ty, body)
    };

    // `add zero zero` reduces PURELY to `zero`, so `irefl` reads at `P zero`.
    let base = {
        let lhs = d.iadd(izero, izero);
        d.irefl(lhs)
    };

    // One step, shared by both directions: `zero + (n + off) = (zero + n) + off
    // = n + off`, the first by `add_assoc` reversed and the second by the
    // induction hypothesis. For `off = neg one` the conclusion is built as
    // `add n (neg one)` and read as `sub n one` -- `Int.sub` is a plain
    // `Definition`, exactly the state-folded/prove-unfolded idiom `sub.rs` uses.
    let stepper = |d: &mut super::ops::IntDev<'_>, offset: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zn = d.iadd(izero, n);
        let ih_ty = d.ieq(zn, n);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);

        let n_off = d.iadd(n, offset);
        let start = d.iadd(izero, n_off);
        let assoc = d.lemma(p.add_assoc, &[izero, n, offset]);
        let left = d.iadd(zn, offset);
        let assoc_rev = d.isymm(left, start, assoc);
        let by_ih = d.icongr(zn, n, ih, &|d, t| d.iadd(t, offset));
        let (_, chained) = d.ichain(start, &[(left, assoc_rev), (n_off, by_ih)]);
        let inner = d.lam_fv(ih_fv, ih_ty, chained);
        d.lam_fv(n_fv, int_ty, inner)
    };

    let up = stepper(&mut d, ione);
    let neg_one = d.ineg(ione);
    let down = stepper(&mut d, neg_one);

    let thm = d.const_app(p.induction_on, &[motive, base, up, down]);
    d.kernel()
        .infer(thm)
        .unwrap_or_else(|e| panic!("Int.induction_on must apply at this motive: {e:?}"));

    let three = d.num(3);
    let pos = d.of_nat(three);
    let at_pos = d.apply(thm, &[pos]);
    let ty_pos = d
        .kernel()
        .infer(at_pos)
        .unwrap_or_else(|e| panic!("the conclusion must read at ofNat 3: {e:?}"));
    let expected_pos = {
        let lhs = d.iadd(izero, pos);
        d.ieq(lhs, pos)
    };
    assert!(
        d.kernel().def_eq(ty_pos, expected_pos),
        "induction_on's conclusion at ofNat 3 must be Eq Int (add zero 3) 3"
    );

    let four = d.num(4);
    let neg_five = d.neg_succ(four);
    let at_neg = d.apply(thm, &[neg_five]);
    let ty_neg = d
        .kernel()
        .infer(at_neg)
        .unwrap_or_else(|e| panic!("the conclusion must read at negSucc 4: {e:?}"));
    let expected_neg = {
        let lhs = d.iadd(izero, neg_five);
        d.ieq(lhs, neg_five)
    };
    assert!(
        d.kernel().def_eq(ty_neg, expected_neg),
        "induction_on's conclusion at negSucc 4 must be Eq Int (add zero (-5)) (-5)"
    );

    // The two `def_eq` assertions above are capable of failing: the same
    // left-hand side against the wrong right-hand side is rejected.
    let wrong = {
        let lhs = d.iadd(izero, neg_five);
        d.ieq(lhs, pos)
    };
    assert!(
        !d.kernel().def_eq(ty_neg, wrong),
        "Eq Int (add zero (-5)) (-5) must NOT be def_eq to Eq Int (add zero (-5)) 3"
    );
}

/// Each of `Int.induction_on`'s three hypotheses is load-bearing.
///
/// The trusted gate proves whatever statement it is handed, so a combinator
/// that *reads* correctly is not thereby correct. Each mutation below keeps the
/// shipped proof value byte-identical and perturbs only the statement; the
/// kernel must reject all three, and must accept the unmutated pair by the same
/// route (without that positive control the loop could be passing because
/// `build` is broken outright).
#[test]
fn induction_on_needs_each_of_its_three_hypotheses() {
    use super::two_sided_induction::{Mutation, build};

    for (mutation, why) in [
        (
            Mutation::BaseAtOne,
            "a base at `one` cannot start either Nat.rec branch",
        ),
        (
            Mutation::UpIsAlsoDown,
            "a second down-step cannot climb the ofNat branch",
        ),
        (
            Mutation::DownIsAlsoUp,
            "a second up-step cannot reach negSucc 0 from zero",
        ),
    ] {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        let anon = k.anon();
        let scratch = k.name_str(anon, "scratchInductionOn");
        let mut d = super::ops::IntDev::new(&mut k, p);
        let (ty, value) = build(&mut d, mutation);
        let outcome = d.kernel().add_declaration(Declaration::Theorem {
            name: scratch,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            outcome.is_err(),
            "the kernel must reject {mutation:?}: {why}"
        );
    }

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let scratch = k.name_str(anon, "scratchInductionOn");
    let mut d = super::ops::IntDev::new(&mut k, p);
    let (ty, value) = build(&mut d, Mutation::None);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: scratch,
            uparams: vec![],
            ty,
            value,
        })
        .expect("the unmutated statement must be accepted by the same route");
}

/// `Int.fib_two_mul` at a positive and a negative index, checked by reduction.
///
/// `n = 5`: `fib(10) = 55`, `fib(5)*(2*fib(6)-fib(5)) = 5*(16-5) = 55`.
/// `n = -3`: `fib(-6) = -8`, `fib(-3)*(2*fib(-2)-fib(-3)) = 2*(-2-2) = -8`
/// (`Int.fib`'s sign extension: `fib(negSucc m) = (-1)^m * fib(succ m)`, so
/// `fib(-2) = -1`, `fib(-3) = 2`, `fib(-6) = -8`). Each case is paired with
/// the value the OTHER plausible-looking (but wrong) coefficient assignment
/// gives -- `fib(n)*(2*fib(n)-fib(n+1))` instead of the true
/// `fib(n)*(2*fib(n+1)-fib(n))` -- which must NOT be `def_eq`.
#[test]
fn fib_two_mul_computes_at_a_concrete_index_of_each_sign() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    // (n, fib(2n), a value fib(2n) is NOT).
    let cases: [(ExprId, ExprId, ExprId); 2] = {
        let five_nat = d.num(5);
        let n_pos = d.of_nat(five_nat);
        let fifty_five_nat = d.num(55);
        let truth_pos = d.of_nat(fifty_five_nat);
        let ten_nat = d.num(10);
        let false_pos = d.of_nat(ten_nat);

        // n = -3 = negSucc 2.
        let two_nat = d.num(2);
        let n_neg = d.neg_succ(two_nat);
        // fib(-6) = -8 = negSucc 7.
        let seven_nat = d.num(7);
        let truth_neg = d.neg_succ(seven_nat);
        let false_neg = d.of_nat(ten_nat);

        [(n_pos, truth_pos, false_pos), (n_neg, truth_neg, false_neg)]
    };

    for (n, truth, falsehood) in cases {
        let instance = d.lemma(p.fib_two_mul, &[n]);
        let ty = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("Int.fib_two_mul must instantiate: {e:?}"));

        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let idx = d.imul(two, n);
        let lhs = d.const_app(p.fib, &[idx]);

        let expected = d.ieq(lhs, truth);
        assert!(
            d.kernel().def_eq(ty, expected),
            "fib_two_mul's instance must reduce to the true arithmetic identity"
        );
        let wrong = d.ieq(lhs, falsehood);
        assert!(
            !d.kernel().def_eq(ty, wrong),
            "the check above must be capable of failing"
        );
    }

    assert!(
        d.kernel().axiom_footprint(p.fib_two_mul).is_empty(),
        "Int.fib_two_mul must rest on zero axioms"
    );
}

/// `Int.fib_two_mul_add_two` at a positive and a negative index, checked by
/// reduction.
///
/// `n = 5`: `fib(12) = 144`, `fib(6)*(2*fib(5)+fib(6)) = 8*(10+8) = 144`.
/// `n = -3`: `fib(-4) = -3`, `fib(-2)*(2*fib(-3)+fib(-2)) = (-1)*(4-1) = -3`.
/// Each case is paired with the value the factors-swapped assignment
/// `fib(n)*(2*fib(n+1)+fib(n))` gives, which must NOT be `def_eq`.
#[test]
fn fib_two_mul_add_two_computes_at_a_concrete_index_of_each_sign() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = super::ops::IntDev::new(&mut k, p);

    // (n, fib(2n+2), a value fib(2n+2) is NOT).
    let cases: [(ExprId, ExprId, ExprId); 2] = {
        let five_nat = d.num(5);
        let n_pos = d.of_nat(five_nat);
        let one_forty_four_nat = d.num(144);
        let truth_pos = d.of_nat(one_forty_four_nat);
        let one_oh_five_nat = d.num(105);
        let false_pos = d.of_nat(one_oh_five_nat);

        // n = -3 = negSucc 2.
        let two_nat = d.num(2);
        let n_neg = d.neg_succ(two_nat);
        // fib(-4) = -3 = negSucc 2.
        let truth_neg = d.neg_succ(two_nat);
        let false_neg = d.izero();

        [(n_pos, truth_pos, false_pos), (n_neg, truth_neg, false_neg)]
    };

    for (n, truth, falsehood) in cases {
        let instance = d.lemma(p.fib_two_mul_add_two, &[n]);
        let ty = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("Int.fib_two_mul_add_two must instantiate: {e:?}"));

        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let mul_two_n = d.imul(two, n);
        let idx = d.iadd(mul_two_n, two);
        let lhs = d.const_app(p.fib, &[idx]);

        let expected = d.ieq(lhs, truth);
        assert!(
            d.kernel().def_eq(ty, expected),
            "fib_two_mul_add_two's instance must reduce to the true arithmetic identity"
        );
        let wrong = d.ieq(lhs, falsehood);
        assert!(
            !d.kernel().def_eq(ty, wrong),
            "the check above must be capable of failing"
        );
    }

    assert!(
        d.kernel().axiom_footprint(p.fib_two_mul_add_two).is_empty(),
        "Int.fib_two_mul_add_two must rest on zero axioms"
    );
}

/// `Int.gcd_div` at three sign combinations `emod_natabs_bound_instantiates_
/// at_positive_negative_and_zero_divisors` established as the discriminating
/// set for this development: a POSITIVE divisor, a NEGATIVE divisor (a case
/// the non-general `Int.gcd_div_gcd_div_gcd` cannot even state, since its
/// divisor is always `ofNat (gcd i j) >= 0`), and the excluded-nowhere `c =
/// 0` degenerate case this theorem's statement does NOT exclude (unlike
/// Mathlib's route through `Nat.gcd_div`, which this development does not
/// have). Builds `Int.dvd` witnesses by the SAME defeq-bridging idiom
/// `Int.gcd_div`'s own proof uses (`irefl` at a concrete numeral, relying on
/// the kernel's own defeq check to confirm `x` computes to `cc*w`), so a
/// wrong witness would be REJECTED by the kernel here exactly as it would be
/// inside the theorem's own proof.
#[test]
fn gcd_div_applies_at_a_positive_a_negative_divisor_and_at_zero() {
    fn int_num(d: &mut IntDev<'_>, n: u32) -> ExprId {
        let mut nat = d.zero();
        for _ in 0..n {
            nat = d.succ(nat);
        }
        d.of_nat(nat)
    }

    fn int_neg_num(d: &mut IntDev<'_>, magnitude: u32) -> ExprId {
        assert!(magnitude >= 1, "negSucc represents magnitudes >= 1");
        let mut nat = d.zero();
        for _ in 0..(magnitude - 1) {
            nat = d.succ(nat);
        }
        d.neg_succ(nat)
    }

    /// `Int.dvd cc x` from a witness `w`, via `Eq.refl x` relying on the
    /// kernel's own defeq check that `x` computes to `cc*w` -- the SAME
    /// idiom `Int.gcd_div`'s own proof uses (`exact_general`/`d.irefl`)
    /// rather than hand-computing the product.
    fn dvd_by_computation(d: &mut IntDev<'_>, cc: ExprId, x: ExprId, w: ExprId) -> ExprId {
        let p = d.int();
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let cq = d.imul(cc, q);
        let body = d.ieq(x, cq);
        let int_ty = d.int_ty();
        let pred = d.lam_fv(q_fv, int_ty, body);
        let one = d.level_one();
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.irefl(x);
        d.apply(intro, &[int_ty, pred, w, proof])
    }

    /// Apply `Int.gcd_div` at concrete `a, b, cc` (with witnesses `wa, wb`
    /// for `cc ∣ a`, `cc ∣ b`), confirm the kernel accepts it, and confirm
    /// the conclusion's LHS/RHS both compute to `expected` (a `Nat`
    /// numeral) -- so a wrong quotient anywhere would show up as a
    /// non-defeq numeral, not merely a type-check pass.
    fn check_gcd_div(
        d: &mut IntDev<'_>,
        a: ExprId,
        b: ExprId,
        cc: ExprId,
        wa: ExprId,
        wb: ExprId,
        expected: u32,
        label: &str,
    ) {
        let p = d.int();
        let dvd_ca = dvd_by_computation(d, cc, a, wa);
        let dvd_cb = dvd_by_computation(d, cc, b, wb);
        let theorem = d.kernel().const_(p.gcd_div, vec![]);
        let applied = d.apply(theorem, &[a, b, cc, dvd_ca, dvd_cb]);
        d.kernel()
            .infer(applied)
            .unwrap_or_else(|e| panic!("Int.gcd_div at {label} should type-check: {e:?}"));

        let qa = d.iediv(a, cc);
        let qb = d.iediv(b, cc);
        let lhs = d.const_app(p.gcd, &[qa, qb]);
        let g = d.const_app(p.gcd, &[a, b]);
        let cabs = d.const_app(p.nat_abs, &[cc]);
        let rhs = NatOps::div(d, g, cabs);

        let want = {
            let mut n = d.zero();
            for _ in 0..expected {
                n = d.succ(n);
            }
            n
        };
        assert!(
            d.kernel().def_eq(lhs, want),
            "{label}: gcd(a/c,b/c) should compute to {expected}"
        );
        assert!(
            d.kernel().def_eq(rhs, want),
            "{label}: gcd(a,b)/natAbs(c) should compute to {expected}"
        );
    }

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.gcd_div).is_empty(),
        "Int.gcd_div must rest on no axiom"
    );
    let mut d = IntDev::new(&mut k, p);

    // --- positive divisor: a=12, b=18, c=6.  gcd(2,3) = gcd(12,18)/6 = 1. --
    {
        let a = int_num(&mut d, 12);
        let b = int_num(&mut d, 18);
        let cc = int_num(&mut d, 6);
        let wa = int_num(&mut d, 2);
        let wb = int_num(&mut d, 3);
        check_gcd_div(&mut d, a, b, cc, wa, wb, 1, "a=12,b=18,c=6 (positive)");
    }

    // --- negative divisor: a=12, b=18, c=-6 -- a case
    //     `Int.gcd_div_gcd_div_gcd` cannot even state (its divisor is always
    //     `ofNat (gcd i j) >= 0`).  ediv(12,-6)=-2, ediv(18,-6)=-3;
    //     gcd(-2,-3) = gcd(12,18)/natAbs(-6) = 1. ---
    {
        let a = int_num(&mut d, 12);
        let b = int_num(&mut d, 18);
        let cc = int_neg_num(&mut d, 6);
        let wa = int_neg_num(&mut d, 2);
        let wb = int_neg_num(&mut d, 3);
        check_gcd_div(&mut d, a, b, cc, wa, wb, 1, "a=12,b=18,c=-6 (negative)");
    }

    // --- c = 0: the degenerate case Mathlib's own hypotheses do NOT
    //     exclude, and which this proof handles rather than refuses.
    //     dvd 0 0 holds at witness 0; both sides collapse to 0. ---
    {
        let a = d.izero();
        let b = d.izero();
        let cc = d.izero();
        let wa = d.izero();
        let wb = d.izero();
        check_gcd_div(&mut d, a, b, cc, wa, wb, 0, "a=0,b=0,c=0 (degenerate)");
    }
}

/// `Int.ModEq.cancel_left_div_gcd`/`cancel_right_div_gcd` at a
/// DISCRIMINATING concrete instance (`gcd(6,4) = 2 > 1` -- this development
/// has no Int-level "cancel a COPRIME factor" lemma at all, so a coprime
/// instance would not even distinguish this family from a hypothetical one),
/// with a wrong-modulus negative control (transposing `a`/`b` is NOT
/// discriminating for this `Eq`-based `ModEq`, since both orderings reduce
/// to the identical closed proposition once `emod` computes -- see the
/// control's own comment below), plus a symbolic restatement at a genuinely
/// free `(m,a,b,c)`.
///
/// `(m, c, a, b) = (6, 4, 1, 4)`: `c*a = 4`, `c*b = 16`, and
/// `4 ≡ 16 [ZMOD 6]` since `emod 4 6 = emod 16 6 = 4` -- built by
/// `Eq.refl (emod (c*a) m)` and accepted only because the kernel's own
/// computation confirms both sides reduce to the same numeral. The
/// conclusion `1 ≡ 4 [ZMOD 3]` similarly holds since `emod 1 3 = emod 4 3 = 1`.
#[test]
fn mod_eq_cancel_div_gcd_family_applies_at_a_discriminating_concrete_instance_and_symbolically() {}

/// `Int.dvd_mul_split` exercised at the axes the working notes called out:
/// a discriminating instance where `c` shares a factor with BOTH `a` and `b`
/// (`Iff.mpr`, real content, `c=6,a=4,b=9,c1=2,c2=3`), a NEGATIVE divisor
/// (`Iff.mp`, `c=-6,a=4,b=9`), and the `c=0` degenerate branch with a
/// genuinely FREE `b` (`Iff.mp`). Each check confirms the kernel's own
/// `infer` accepts the constructed proof term against the exact stated
/// type -- the same idiom `gcd_div_applies_at_a_positive_a_negative_divisor_and_at_zero`
/// and `emod_eq_zero_iff_dvd_mp_produces_a_real_witness` use.
#[test]
fn dvd_mul_split_applies_at_a_discriminating_negative_and_free_degenerate_instance() {
    fn int_num(d: &mut IntDev<'_>, n: u32) -> ExprId {
        let mut nat = d.zero();
        for _ in 0..n {
            nat = d.succ(nat);
        }
        d.of_nat(nat)
    }
    fn nat_num(d: &mut IntDev<'_>, n: u32) -> ExprId {
        let mut nat = d.zero();
        for _ in 0..n {
            nat = d.succ(nat);
        }
        nat
    }

    fn int_neg_num(d: &mut IntDev<'_>, magnitude: u32) -> ExprId {
        assert!(magnitude >= 1, "negSucc represents magnitudes >= 1");
        let mut nat = d.zero();
        for _ in 0..(magnitude - 1) {
            nat = d.succ(nat);
        }
        d.neg_succ(nat)
    }

    /// `Int.dvd cc x` from a witness `w`, via `Eq.refl x` relying on the
    /// kernel's own defeq check that `x` computes to `cc*w` -- the same
    /// idiom `gcd_div_applies_...`'s `dvd_by_computation` uses.
    fn dvd_by_computation(d: &mut IntDev<'_>, cc: ExprId, x: ExprId, w: ExprId) -> ExprId {
        let p = d.int();
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let cq = d.imul(cc, q);
        let body = d.ieq(x, cq);
        let int_ty = d.int_ty();
        let pred = d.lam_fv(q_fv, int_ty, body);
        let one = d.level_one();
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.irefl(x);
        d.apply(intro, &[int_ty, pred, w, proof])
    }

    fn idvd_ty(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
        let f = d.int().dvd;
        d.const_app(f, &[x, y])
    }

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let m = int_num(&mut d, 6);
    let c = int_num(&mut d, 4);
    let a = int_num(&mut d, 1);
    let b = int_num(&mut d, 4);
    let five_nat = nat_num(&mut d, 5);
    let hm = d.zero_lt_succ(five_nat); // Nat.lt zero six, defeq Int.lt zero m

    let g_nat = d.const_app(p.gcd, &[m, c]);
    let g = d.of_nat(g_nat);
    let qm = d.iediv(m, g);
    let want_qm = int_num(&mut d, 3);
    assert!(
        d.kernel().def_eq(qm, want_qm),
        "6 / gcd(6,4) should compute to 3"
    );

    // -- cancel_left_div_gcd --
    {
        let ca = d.imul(c, a);
        let emod_ca_m = d.iemod(ca, m);
        let h = d.irefl(emod_ca_m); // defeq to Eq(emod ca m)(emod cb m), i.e. ModEq m ca cb

        let theorem = d.kernel().const_(p.mod_eq_cancel_left_div_gcd, vec![]);
        let applied = d.apply(theorem, &[m, a, b, c, hm, h]);
        let inferred = d.kernel().infer(applied).unwrap_or_else(|e| {
            panic!("Int.mod_eq_cancel_left_div_gcd at (6,4,1,4) should type-check: {e:?}")
        });
        let want_ty = super::modeq::imodeq(&mut d, qm, a, b);
        assert!(
            d.kernel().def_eq(inferred, want_ty),
            "Int.mod_eq_cancel_left_div_gcd(6,4,1,4) should conclude ModEq 3 1 4"
        );
        // Negative control: transposing `a`/`b` in the conclusion is NOT
        // discriminating here -- `ModEq n a b := emod a n = emod b n`
        // reduces both `ModEq 3 1 4` and `ModEq 3 4 1` to the identical
        // closed proposition `Eq 1 1` once emod computes, so the transposed
        // form is defeq to the original and is not a real negative control.
        // Use a WRONG MODULUS instead: `1 mod 2 = 1` but `4 mod 2 = 0`, so
        // `ModEq 2 1 4` reduces to the genuinely false-shaped `Eq 1 0`.
        let wrong_modulus = int_num(&mut d, 2);
        let wrong_ty = super::modeq::imodeq(&mut d, wrong_modulus, a, b);
        let anon = d.kernel().anon();
        let wrong_name = d
            .kernel()
            .name_str(anon, "nc_int_cancel_left_div_gcd_wrong_modulus");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name: wrong_name,
            uparams: vec![],
            ty: wrong_ty,
            value: applied,
        });
        assert!(
            result.is_err(),
            "Int.mod_eq_cancel_left_div_gcd's proof must be rejected against the wrong-modulus conclusion"
        );
        assert!(
            !d.kernel().environment().contains(wrong_name),
            "a rejected declaration must not enter the environment"
        );
    }

    // -- cancel_right_div_gcd --
    {
        let ac = d.imul(a, c);
        let emod_ac_m = d.iemod(ac, m);
        let h = d.irefl(emod_ac_m);

        let theorem = d.kernel().const_(p.mod_eq_cancel_right_div_gcd, vec![]);
        let applied = d.apply(theorem, &[m, a, b, c, hm, h]);
        let inferred = d.kernel().infer(applied).unwrap_or_else(|e| {
            panic!("Int.mod_eq_cancel_right_div_gcd at (6,4,1,4) should type-check: {e:?}")
        });
        let want_ty = super::modeq::imodeq(&mut d, qm, a, b);
        assert!(
            d.kernel().def_eq(inferred, want_ty),
            "Int.mod_eq_cancel_right_div_gcd(6,4,1,4) should conclude ModEq 3 1 4"
        );
    }

    // -- Symbolic restatement at a genuinely free `(m,a,b,c)`: re-applying
    // `mod_eq_cancel_left_div_gcd` at fresh fvars, inside a NEW theorem,
    // must still type-check. --
    {
        let anon = d.kernel().anon();
        let stmt_name = d
            .kernel()
            .name_str(anon, "symbolic_int_cancel_left_div_gcd_restated");
        d.int_theorem(stmt_name, 4, &|d, v| {
            let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
            let zero_i = d.izero();
            let hm_ty = d.ilt(zero_i, m);
            let ca = d.imul(c, a);
            let cb = d.imul(c, b);
            let h_ty = super::modeq::imodeq(d, m, ca, cb);
            let g_nat = d.const_app(p.gcd, &[m, c]);
            let g = d.of_nat(g_nat);
            let qm = d.iediv(m, g);
            let concl = super::modeq::imodeq(d, qm, a, b);
            let inner = d.arrow(h_ty, concl);
            let stmt = d.arrow(hm_ty, inner);

            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let applied = d.const_app(p.mod_eq_cancel_left_div_gcd, &[m, a, b, c, hm, h]);
            let with_h = d.lam_fv(h_fv, h_ty, applied);
            let proof = d.lam_fv(hm_fv, hm_ty, with_h);
            (stmt, proof)
        })
        .unwrap_or_else(|e| {
            panic!("Int.mod_eq_cancel_left_div_gcd must apply at a genuinely free (m,a,b,c): {e:?}")
        });
    }

    assert!(
        k.axiom_footprint(p.dvd_mul_split).is_empty(),
        "Int.dvd_mul_split must rest on no axiom"
    );
    let mut d = IntDev::new(&mut k, p);

    // ---- Iff.mpr at a discriminating instance where c shares a factor
    //      with BOTH a and b: c=6, a=4, b=9, c1=2, c2=3.
    {
        let a = int_num(&mut d, 4);
        let b = int_num(&mut d, 9);
        let c = int_num(&mut d, 6);
        let c1 = int_num(&mut d, 2);
        let c2 = int_num(&mut d, 3);
        let w1 = int_num(&mut d, 2); // a = c1*w1 = 2*2 = 4
        let w2 = int_num(&mut d, 3); // b = c2*w2 = 3*3 = 9

        let dvd_c1_a = dvd_by_computation(&mut d, c1, a, w1);
        let dvd_c2_b = dvd_by_computation(&mut d, c2, b, w2);
        let dvd_c1_a_ty = idvd_ty(&mut d, c1, a);
        let dvd_c2_b_ty = idvd_ty(&mut d, c2, b);
        let c1c2 = d.imul(c1, c2);
        let eq_ty = d.ieq(c1c2, c);
        let eq_proof = d.irefl(c1c2); // 2*3 computes to 6 = c, by def_eq

        let logic = d.int().logic;
        let inner_ty = d.const_app(logic.and, &[dvd_c2_b_ty, eq_ty]);
        let inner_and = d.const_app(logic.and_intro, &[dvd_c2_b_ty, eq_ty, dvd_c2_b, eq_proof]);
        let full_and = d.const_app(
            logic.and_intro,
            &[dvd_c1_a_ty, inner_ty, dvd_c1_a, inner_and],
        );
        let exists_proof = split_exists_intro(&mut d, a, b, c, c1, c2, full_and);

        let ab = d.imul(a, b);
        let dvd_c_ab_ty = idvd_ty(&mut d, c, ab);
        let ex_ty = split_exists_ty(&mut d, a, b, c);
        let theorem = d.kernel().const_(p.dvd_mul_split, vec![]);
        let iff_term = d.apply(theorem, &[c, a, b]);
        let mpr = d.kernel().const_(p.logic.iff_mpr, vec![]);
        let applied = d.apply(mpr, &[dvd_c_ab_ty, ex_ty, iff_term, exists_proof]);
        let inferred = d.kernel().infer(applied).unwrap_or_else(|e| {
            panic!("Int.dvd_mul_split mpr at c=6,a=4,b=9 should type-check: {e:?}")
        });
        assert!(
            d.kernel().def_eq(inferred, dvd_c_ab_ty),
            "mpr result should have type Int.dvd 6 36"
        );
        let want36 = int_num(&mut d, 36);
        assert!(d.kernel().def_eq(ab, want36), "a*b should compute to 36");
    }

    // ---- Iff.mp at a NEGATIVE divisor: c=-6, a=4, b=9.
    //      dvd(-6,36) via witness -6 (36 = -6 * -6).
    {
        let a = int_num(&mut d, 4);
        let b = int_num(&mut d, 9);
        let c = int_neg_num(&mut d, 6); // -6
        let ab = d.imul(a, b);
        let w = int_neg_num(&mut d, 6); // -6
        let dvd_c_ab = dvd_by_computation(&mut d, c, ab, w);
        let dvd_c_ab_ty = idvd_ty(&mut d, c, ab);
        let ex_ty = split_exists_ty(&mut d, a, b, c);
        let theorem = d.kernel().const_(p.dvd_mul_split, vec![]);
        let iff_term = d.apply(theorem, &[c, a, b]);
        let mp = d.kernel().const_(p.logic.iff_mp, vec![]);
        let applied = d.apply(mp, &[dvd_c_ab_ty, ex_ty, iff_term, dvd_c_ab]);
        let inferred = d.kernel().infer(applied).unwrap_or_else(|e| {
            panic!("Int.dvd_mul_split mp at c=-6,a=4,b=9 should type-check: {e:?}")
        });
        assert!(
            d.kernel().def_eq(inferred, ex_ty),
            "mp result at a negative divisor should have the exists type"
        );
    }

    // ---- Iff.mp at the c = 0 degenerate branch, with a genuinely free b.
    {
        let anon = d.kernel().anon();
        let b_name = d.kernel().name_str(anon, "dvd_mul_split_free_b");
        let int_ty = d.int_ty();
        d.kernel()
            .add_declaration(Declaration::Axiom {
                name: b_name,
                uparams: vec![],
                ty: int_ty,
            })
            .unwrap();
        let b = d.kernel().const_(b_name, vec![]);
        let a = d.izero();
        let c = d.izero();
        let ab = d.imul(a, b); // 0 * b
        // dvd 0 (0*b): witness b, proof 0*b = 0*b (Eq.refl, syntactically).
        let dvd_c_ab = dvd_by_computation(&mut d, c, ab, b);
        let dvd_c_ab_ty = idvd_ty(&mut d, c, ab);
        let ex_ty = split_exists_ty(&mut d, a, b, c);
        let theorem = d.kernel().const_(p.dvd_mul_split, vec![]);
        let iff_term = d.apply(theorem, &[c, a, b]);
        let mp = d.kernel().const_(p.logic.iff_mp, vec![]);
        let applied = d.apply(mp, &[dvd_c_ab_ty, ex_ty, iff_term, dvd_c_ab]);
        let inferred = d.kernel().infer(applied).unwrap_or_else(|e| {
            panic!("Int.dvd_mul_split mp at c=0,a=0,b=free should type-check: {e:?}")
        });
        assert!(
            d.kernel().def_eq(inferred, ex_ty),
            "mp result at the free degenerate branch should have the exists type"
        );
    }
}

/// `Int.gaussTermModEq` (ADR-1130, connecting-theorem item 1) at `pp := 7`,
/// `a := 3`, on BOTH branches of `Nat.gaussSignNeg` -- one branch alone
/// would leave the other's whole derivation unexercised, and the two
/// branches share no proof step.
///
/// Values recomputed independently in Python before being written here
/// (`r := (a*k) mod pp`, `half := pp div 2`, negative iff `r > half`,
/// `fold := pp - r` when negative else `r`):
///
/// | `k` | `r` | negative? | `gaussFold` | `ε` | check |
/// | --- | --- | --- | --- | --- | --- |
/// | 1 | 3 | no (`3 ≤ 3`) | 3 | `1` | `3·1 = 3 ≡ 1·3` |
/// | 2 | 6 | yes (`6 > 3`) | 1 | `-1` | `3·2 = 6 ≡ -1·1` |
///
/// `Int.ModEq n a b` unfolds to `emod a n = emod b n`, so the congruence
/// itself is CHECKED BY COMPUTATION here, not merely asserted to have the
/// stated type -- and the negative control flips only the `k = 2` sign
/// (a single constant, leaving both sides concrete numerals) and requires
/// the kernel to REFUSE it.
#[test]
fn gauss_term_mod_eq_computes_on_both_sign_branches_at_pp_7_a_3() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.gauss_term_mod_eq).is_empty(),
        "Int.gaussTermModEq must rest on no axiom"
    );
    let mut d = IntDev::new(&mut k, p);

    let pp = d.num(7);
    let a = d.num(3);
    let n_int = d.of_nat(pp);
    let a_int = d.of_nat(a);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    for (k_val, fold_val, negative) in [(1_u32, 3_u32, false), (2, 1, true)] {
        let kk = d.num(k_val);
        let k_int = d.of_nat(kk);

        // The concrete sign and fold, read off the definitions themselves.
        let sign = d.const_app(p.nat.gauss_sign_neg, &[pp, a, kk]);
        let expected_sign = if negative {
            d.bool_true()
        } else {
            d.bool_false()
        };
        assert!(
            d.kernel().def_eq(sign, expected_sign),
            "gaussSignNeg 7 3 {k_val} must compute to {negative}"
        );
        let fold = d.const_app(p.nat.gauss_fold, &[pp, a, kk]);
        let expected_fold = d.num(fold_val);
        assert!(
            d.kernel().def_eq(fold, expected_fold),
            "gaussFold 7 3 {k_val} must compute to {fold_val}"
        );

        let sel = super::prod::bool_select_int(&mut d, sign, neg_one, one_i);
        let expected_sel = if negative { neg_one } else { one_i };
        assert!(
            d.kernel().def_eq(sel, expected_sel),
            "the sign selector at k = {k_val} must compute to the expected unit"
        );

        // The congruence itself, by computation: `ModEq n x y` unfolds to
        // `emod x n = emod y n`.
        let lhs = d.imul(a_int, k_int);
        let fold_int = d.of_nat(fold);
        let rhs = d.imul(sel, fold_int);
        let emod_lhs = d.iemod(lhs, n_int);
        let emod_rhs = d.iemod(rhs, n_int);
        assert!(
            d.kernel().def_eq(emod_lhs, emod_rhs),
            "3*{k_val} and its signed fold must have the same residue mod 7"
        );

        // ...and the theorem, instantiated at these arguments, states it.
        let pos_pp = {
            // Lt 0 7 = Le 1 7 = Le 1 (add 1 6), via le_add_right(1, 6).
            let one_n = d.num(1);
            let six = d.num(6);
            d.lemma(p.nat.le_add_right, &[one_n, six])
        };
        let lemma_fn = d.lemma(p.gauss_term_mod_eq, &[pp, a, kk]);
        let applied = d.apply(lemma_fn, &[pos_pp]);
        let inferred = d
            .kernel()
            .infer(applied)
            .unwrap_or_else(|e| panic!("gaussTermModEq must apply at k = {k_val}: {e:?}"));
        let expected = super::modeq::imodeq(&mut d, n_int, lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "gaussTermModEq's instantiated type at k = {k_val} must match the \
             direct sign/fold computation"
        );
    }

    // NEGATIVE CONTROL: at `k = 2` the sign is genuinely `-1`. Replacing it
    // with `+1` -- one constant, both sides still concrete numerals -- makes
    // the congruence FALSE (`emod 6 7 = 6` against `emod 1 7 = 1`), so a
    // wrong-branch defect could not pass the checks above vacuously.
    let two = d.num(2);
    let two_int = d.of_nat(two);
    let lhs_two = d.imul(a_int, two_int);
    let fold_two = d.num(1);
    let fold_two_int = d.of_nat(fold_two);
    let wrong_rhs = d.imul(one_i, fold_two_int);
    let emod_lhs_two = d.iemod(lhs_two, n_int);
    let emod_wrong = d.iemod(wrong_rhs, n_int);
    assert!(
        !d.kernel().def_eq(emod_lhs_two, emod_wrong),
        "control: 3*2 = 6 must NOT be congruent to +1 * gaussFold 7 3 2 = 1 mod 7"
    );
}

/// **Gauss's lemma**, `Int.gaussLemmaSignCount` (ADR-1130), at `pp := 7`
/// (`m := 3`) for `a := 3` and `a := 2` -- the two multipliers chosen because
/// their sign counts have OPPOSITE parity, so the count-to-sign link is
/// genuinely exercised rather than agreeing by accident:
///
/// | `a` | `gaussNegCount 7 a 3` | `a^3 mod 7` | `(-1)^count mod 7` |
/// | --- | --- | --- | --- |
/// | 3 | 1 (odd) | `27 ≡ 6` | `-1 ≡ 6` |
/// | 2 | 2 (even) | `8 ≡ 1` | `+1 ≡ 1` |
///
/// (Recomputed in Python, not inherited: `sum(1 for k in 1..=3 if (a*k)%7 >
/// 3)` gives 1 and 2 respectively.)
///
/// `Nat.PrimeCond 7` is a free variable in a `LocalContext` -- the
/// conclusion's TYPE does not depend on which proof inhabits it, and building
/// a closed witness needs a divisor case analysis that adds nothing here
/// (the same choice `coprime_factorial_of_lt_prime_computes_at_pp_seven_m_four`
/// makes). The coprimality hypothesis is a GENUINE witness: `gcd a 7` reduces
/// to `1` for both multipliers, so `Eq.refl 1` inhabits it.
#[test]
fn gauss_lemma_matches_direct_computation_at_pp_7_for_both_parities() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.gauss_lemma_sign_count).is_empty(),
        "Int.gaussLemmaSignCount must rest on no axiom"
    );
    let mut d = IntDev::new(&mut k, p);

    let m = d.num(3);
    let pp = d.num(7);
    let n_int = d.of_nat(pp);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    for (a_val, count_val, residue) in [(3_u32, 1_u32, 6_u32), (2, 2, 1)] {
        let a = d.num(a_val);
        let a_int = d.of_nat(a);

        let count = d.const_app(p.nat.gauss_neg_count, &[pp, a, m]);
        let expected_count = d.num(count_val);
        assert!(
            d.kernel().def_eq(count, expected_count),
            "gaussNegCount 7 {a_val} 3 must compute to {count_val}"
        );

        let pow_a = d.ipow(a_int, m);
        let pow_neg = d.ipow(neg_one, count);
        let emod_pow_a = d.iemod(pow_a, n_int);
        let emod_pow_neg = d.iemod(pow_neg, n_int);
        let expected_residue = numeral(d.kernel(), &p, i32::try_from(residue).expect("small"));
        assert!(
            d.kernel().def_eq(emod_pow_a, expected_residue),
            "{a_val}^3 mod 7 must compute to {residue}"
        );
        assert!(
            d.kernel().def_eq(emod_pow_neg, expected_residue),
            "(-1)^gaussNegCount(7,{a_val},3) mod 7 must compute to {residue}"
        );

        // The theorem itself, at these arguments.
        let prime_ty = super::wilson::prime_condition(&mut d, pp);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        // `gcd a (succ (mul 2 3))` reduces to `1`, so `Eq.refl 1` inhabits
        // the coprimality hypothesis -- a real witness, not a placeholder.
        let one_n = d.num(1);
        let cop_proof = d.refl(one_n);

        let lemma_fn = d.lemma(p.gauss_lemma_sign_count, &[m, a]);
        let applied = d.apply(lemma_fn, &[prime_proof, cop_proof]);

        let anon = d.anon_name();
        let mut ctx = LocalContext::new();
        ctx.push(LocalDecl {
            fvar: prime_fv,
            name: anon,
            ty: prime_ty,
            info: BinderInfo::Default,
        });
        let inferred = d
            .kernel()
            .infer_in(applied, &mut ctx)
            .unwrap_or_else(|e| panic!("Gauss's lemma must apply at a = {a_val}: {e:?}"));
        let expected = super::modeq::imodeq(&mut d, n_int, pow_a, pow_neg);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "Gauss's lemma's instantiated type at a = {a_val} must match the \
             direct pow/gaussNegCount computation"
        );
    }

    // NEGATIVE CONTROL: the parity genuinely matters. At `a := 3` the count
    // is ODD, so `(-1)^count ≡ -1 ≡ 6`; the even-count value `+1 ≡ 1` is a
    // different residue, and the kernel must refuse to identify them.
    let emod_one = d.iemod(one_i, n_int);
    let six = numeral(d.kernel(), &p, 6);
    assert!(
        !d.kernel().def_eq(emod_one, six),
        "control: +1 and 6 must be different residues mod 7, so the odd-count \
         sign at a = 3 is not vacuously satisfied"
    );
}

/// **The second supplementary law of quadratic reciprocity**,
/// `Int.secondSupplementaryLaw` (ADR-1150), exercised at ALL FOUR residue
/// classes of `p mod 8` — every one of them an actual odd prime, so the
/// numeric half of each check is a true statement rather than a vacuous one:
///
/// | `m` | `p = 2m+1` | `p mod 8` | class index | `2^m mod p` | law says |
/// | --- | --- | --- | --- | --- | --- |
/// | 1 | 3  | 3 | 1 | 2  | `-1` |
/// | 2 | 5  | 5 | 2 | 4  | `-1` |
/// | 3 | 7  | 7 | 3 | 1  | `+1` |
/// | 8 | 17 | 1 | 0 | 1  | `+1` |
///
/// Recomputed in Python, not inherited from the plan:
///
/// ```sh
/// python3 -c "
/// for m in [1,2,3,8]:
///     p=2*m+1; q=(m//2)//2
///     print(m, p, p%8, [r for r in range(4) if 4*q+r==m], pow(2,m,p), (-1)%p)
/// "
/// ```
///
/// Three things are checked per row, and the second and third are what make
/// this a measurement rather than a restatement:
///
/// 1. the class shape the law names for that row really IS `m` — `class_shape`
///    at `q := div (div m 2) 2` reduces to the numeral `m`;
/// 2. the OTHER THREE class shapes are NOT `m`, so the four classes genuinely
///    separate and the disjunction is not satisfiable by accident;
/// 3. `2^m mod p` is the claimed sign's residue and is NOT the other sign's —
///    a negative control that differs in one small term (`1` against `p-1`).
///
/// Finally the theorem is applied at a genuinely FREE `m` and its inferred
/// type compared against the independently rebuilt statement, because a
/// concrete instantiation reduces every numeral and hides any defeq-shaped
/// gap a symbolic one would expose.
#[test]
fn second_supplementary_law_classifies_all_four_residues_mod_eight() {
    use crate::nat_prelude::half_ceil_parity::{class_shape, components};

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for (name, label) in [
        (p.second_supplementary_law, "Int.secondSupplementaryLaw"),
        (p.pow_neg_one_of_even, "Int.pow_neg_one_of_even"),
        (p.pow_neg_one_of_odd, "Int.pow_neg_one_of_odd"),
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{label} must rest on no axiom"
        );
    }
    let mut d = IntDev::new(&mut k, p);
    let two_nat = d.num(2);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    for (m_val, p_val, class_index, is_plus) in [
        (1_u32, 3_u32, 1_u8, false),
        (2, 5, 2, false),
        (3, 7, 3, true),
        (8, 17, 0, true),
    ] {
        let m = d.num(m_val);
        let half = d.div(m, two_nat);
        let quarter = d.div(half, two_nat);

        // (1)/(2) the four class shapes separate, and exactly one is `m`.
        for r in 0_u8..4 {
            let shape = class_shape(&mut d, quarter, r);
            let matches = d.kernel().def_eq(shape, m);
            assert_eq!(
                matches,
                r == class_index,
                "at m = {m_val} (p = {p_val}) class shape {r} must{} be m",
                if r == class_index { "" } else { " NOT" }
            );
        }

        // (3) the sign, with the opposite sign as the negative control.
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);
        let pp_int = d.of_nat(pp);
        let two_int = d.of_nat(two_nat);
        let pow_two_m = d.ipow(two_int, m);
        let residue = d.iemod(pow_two_m, pp_int);
        let plus_residue = d.iemod(one_i, pp_int);
        let minus_residue = d.iemod(neg_one, pp_int);
        let (expected, rejected) = if is_plus {
            (plus_residue, minus_residue)
        } else {
            (minus_residue, plus_residue)
        };
        assert!(
            d.kernel().def_eq(residue, expected),
            "2^{m_val} mod {p_val} must be the {} residue the law names",
            if is_plus { "+1" } else { "-1" }
        );
        assert!(
            !d.kernel().def_eq(residue, rejected),
            "control: at m = {m_val} (p = {p_val}) the two signs must be \
             DIFFERENT residues, or the sign claim is vacuous"
        );
    }

    // The theorem itself, at a genuinely free `m`.
    let m_fv = d.fresh_fvar();
    let m_sym = d.kernel().fvar(m_fv);
    let mul2m = d.mul(two_nat, m_sym);
    let pp_sym = d.succ(mul2m);
    let prime_ty = super::wilson::prime_condition(&mut d, pp_sym);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);

    let lemma_fn = d.lemma(p.second_supplementary_law, &[m_sym]);
    let applied = d.apply(lemma_fn, &[prime_proof]);

    let anon = d.anon_name();
    let nat_ty = d.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .unwrap_or_else(|e| panic!("the law must apply at a free m: {e:?}"));

    let nat_prelude = p.nat;
    let [plus_classes, minus_classes, _, _] = components(&mut d, &nat_prelude, m_sym);
    let pp_int_sym = d.of_nat(pp_sym);
    let two_int = d.of_nat(two_nat);
    let pow_two_m_sym = d.ipow(two_int, m_sym);
    let modeq_plus = super::modeq::imodeq(&mut d, pp_int_sym, pow_two_m_sym, one_i);
    let modeq_minus = super::modeq::imodeq(&mut d, pp_int_sym, pow_two_m_sym, neg_one);
    let logic = p.logic;
    let left = d.const_app(logic.and, &[plus_classes, modeq_plus]);
    let right = d.const_app(logic.and, &[minus_classes, modeq_minus]);
    let expected = d.const_app(logic.or, &[left, right]);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the law's symbolic conclusion must be the p = +-1 / p = +-3 (mod 8) \
         dichotomy over the Gauss's-lemma power residue"
    );

    // Control: the dichotomy is not symmetric -- swapping the two SIGNS while
    // keeping the classes gives a different (and false) statement.
    let swapped_left = d.const_app(logic.and, &[plus_classes, modeq_minus]);
    let swapped_right = d.const_app(logic.and, &[minus_classes, modeq_plus]);
    let swapped = d.const_app(logic.or, &[swapped_left, swapped_right]);
    assert!(
        !d.kernel().def_eq(inferred, swapped),
        "control: the law must not be invariant under swapping +1 and -1, or \
         the sign half of the classification says nothing"
    );
}

/// `Int.firstSupplementaryLawNotResidue` states the first supplementary law's
/// non-residue half — for an odd prime `p = 2m+1` with `m` ODD, i.e.
/// `p = 3 (mod 4)`, `-1` is not a quadratic residue mod `p` — and this test
/// measures the two things its statement could get wrong.
///
/// The numeric content is re-runnable independently of this test:
///
/// ```text
/// python3 docs/research/09-decisions/adr-1230-first-supplementary-checks.py
/// ```
///
/// Three checks, and the second and third are what make this a measurement
/// rather than a restatement:
///
/// 1. **`Odd m` is load-bearing.** `-1` really is a non-residue mod `3` and
///    mod `7` (`m` odd) and really IS one mod `5` (`m` even, witness `2`), by
///    a `Nat.mod` scan the kernel computes. So the theorem is FALSE without
///    its parity hypothesis; nothing about it is vacuous.
/// 2. **The symbolic conclusion is the one intended.** The theorem is applied
///    at a genuinely FREE `m` with free hypotheses and its inferred type
///    compared against an independently rebuilt `Not (IsQuadraticResidue
///    (ofNat (succ (mul 2 m))) (neg one))`.
/// 3. **The negative control is refutable IN-KERNEL, not merely different.**
///    The same statement at `one` in place of `neg one` is false for every
///    modulus — `Int.is_quadratic_residue_one` proves `IsQuadraticResidue p
///    one` outright — so a proof of the mutated statement would contradict an
///    already-admitted theorem. This is the mutation the shape check alone
///    could not distinguish from a harmless renaming.
#[test]
fn first_supplementary_law_refuses_neg_one_exactly_when_the_half_is_odd() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for (name, label) in [
        (
            p.first_supplementary_law_not_residue,
            "Int.firstSupplementaryLawNotResidue",
        ),
        (
            p.is_quadratic_residue_of_mod_eq,
            "Int.isQuadraticResidue_of_modEq",
        ),
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{label} must rest on no axiom"
        );
    }

    let mut d = IntDev::new(&mut k, p);
    let two_nat = d.num(2);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    // (1) `Odd m` is load-bearing: `-1` is a residue mod `p` exactly when the
    // half `m = (p-1)/2` is EVEN, decided here by scanning `x*x + 1 = 0 [p]`
    // over `[0,p)` with `Nat.mod`. Magnitudes stay under 40 deliberately --
    // every numeral this prelude builds is unary.
    for (m_val, p_val, m_is_odd, expect_residue) in [
        (1_u32, 3_u32, true, false),
        (2, 5, false, true),
        (3, 7, true, false),
    ] {
        assert_eq!(m_val % 2 == 1, m_is_odd, "the row's own parity must agree");
        let pp = d.num(p_val);
        let zero = d.zero();
        let one_nat = d.num(1);
        let mut found = None;
        for x_val in 0..p_val {
            let x = d.num(x_val);
            let sq = d.mul(x, x);
            let shifted = d.add(sq, one_nat);
            let r = d.modulo(shifted, pp);
            if d.kernel().def_eq(r, zero) {
                found = Some(x_val);
                break;
            }
        }
        assert_eq!(
            found.is_some(),
            expect_residue,
            "at p = {p_val} (m = {m_val}, m odd = {m_is_odd}) `-1` must{} be a \
             quadratic residue -- if this disagrees, the law's parity \
             hypothesis is not what decides the conclusion",
            if expect_residue { "" } else { " NOT" }
        );
    }

    // (2) The theorem at a genuinely FREE `m`, with free hypotheses.
    let m_fv = d.fresh_fvar();
    let m_sym = d.kernel().fvar(m_fv);
    let mul2m = d.mul(two_nat, m_sym);
    let pp_sym = d.succ(mul2m);
    let pi_sym = d.of_nat(pp_sym);
    let prime_ty = super::wilson::prime_condition(&mut d, pp_sym);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);
    let nat_prelude = p.nat;
    let odd_ty = d.const_app(nat_prelude.odd, &[m_sym]);
    let odd_fv = d.fresh_fvar();
    let odd_proof = d.kernel().fvar(odd_fv);

    let lemma_fn = d.lemma(p.first_supplementary_law_not_residue, &[m_sym]);
    let applied = d.apply(lemma_fn, &[prime_proof, odd_proof]);

    let anon = d.anon_name();
    let nat_ty = d.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: odd_fv,
        name: anon,
        ty: odd_ty,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .unwrap_or_else(|e| panic!("the law must apply at a free m: {e:?}"));

    let qr_neg_one = super::euler::is_quadratic_residue(&mut d, pi_sym, neg_one);
    let expected = d.not(qr_neg_one);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the law's symbolic conclusion must be `-1 is not a quadratic residue \
         mod (2m+1)`"
    );

    // (3) The negative control, refutable in-kernel rather than merely
    // different: the same statement at `one` contradicts
    // `Int.is_quadratic_residue_one`, which holds for EVERY modulus.
    let qr_one = super::euler::is_quadratic_residue(&mut d, pi_sym, one_i);
    let mutated = d.not(qr_one);
    assert!(
        !d.kernel().def_eq(inferred, mutated),
        "control: the law must not be invariant under replacing `-1` by `1`"
    );
    let one_is_a_residue = d.const_app(p.is_quadratic_residue_one, &[pi_sym]);
    let one_residue_ty = d
        .kernel()
        .infer_in(one_is_a_residue, &mut ctx)
        .expect("`Int.is_quadratic_residue_one` must apply at any modulus");
    assert!(
        d.kernel().def_eq(one_residue_ty, qr_one),
        "control: `1` IS a quadratic residue mod every modulus, so the mutated \
         statement is not merely different -- it is refuted by an \
         already-admitted theorem"
    );
}

/// `Int.wilsonHalfSplit` states `(p-1)! = m! · ((-1)^m · m!)` mod `p` for
/// BOTH parities of `m`, and this test measures the SIGN, which is the whole
/// content — the unsigned form is a different, and false, proposition.
///
/// The numeric content is re-runnable independently of this test:
///
/// ```text
/// python3 docs/research/09-decisions/adr-1235-first-supplementary-residue-checks.py
/// ```
///
/// Three checks:
///
/// 1. **The symbolic statement is the one intended**, read from the kernel at
///    a genuinely FREE `m` and compared against an independently rebuilt
///    `ModEq (ofNat (2m+1)) (m! * ((-1)^m * m!)) (-1)`.
/// 2. **Dropping the `(-1)^m` factor is not a renaming.** The unsigned
///    statement is not `def_eq` to the real one, AND at `m = 3` the kernel
///    computes the two sides to different residues mod `7`, so the mutant is
///    refuted rather than merely distinguished.
/// 3. **The identity computes.** `emod` of both sides agrees at `(m,p) =
///    (2,5)` and `(3,7)` — one even `m`, one odd — which is what makes the
///    theorem's parity-generality a measured claim rather than a stated one.
#[test]
fn wilson_half_split_carries_the_sign_and_the_unsigned_form_is_refuted() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for (name, label) in [
        (p.wilson_half_split, "Int.wilsonHalfSplit"),
        (
            p.first_supplementary_law_residue,
            "Int.firstSupplementaryLawResidue",
        ),
        (p.nat.sub_sub_self, "Nat.sub_sub_self"),
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{label} must rest on no axiom"
        );
    }

    let mut d = IntDev::new(&mut k, p);
    let two_nat = d.num(2);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    // (1) the theorem at a genuinely FREE `m`, with a free primality proof.
    let m_fv = d.fresh_fvar();
    let m_sym = d.kernel().fvar(m_fv);
    let mul2m = d.mul(two_nat, m_sym);
    let pp_sym = d.succ(mul2m);
    let pi_sym = d.of_nat(pp_sym);
    let prime_ty = super::wilson::prime_condition(&mut d, pp_sym);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);

    let lemma_fn = d.lemma(p.wilson_half_split, &[m_sym]);
    let applied = d.apply(lemma_fn, &[prime_proof]);

    let anon = d.anon_name();
    let nat_ty = d.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .unwrap_or_else(|e| panic!("the split must apply at a free m: {e:?}"));

    let fact_m = d.const_app(p.factorial, &[m_sym]);
    let pow_m = d.ipow(neg_one, m_sym);
    let signed_inner = d.imul(pow_m, fact_m);
    let signed = d.imul(fact_m, signed_inner);
    let expected = super::modeq::imodeq(&mut d, pi_sym, signed, neg_one);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the split's symbolic statement must be `m! * ((-1)^m * m!) = -1 [2m+1]`"
    );

    // (2) the unsigned mutant is a different proposition.
    let unsigned = d.imul(fact_m, fact_m);
    let mutated = super::modeq::imodeq(&mut d, pi_sym, unsigned, neg_one);
    assert!(
        !d.kernel().def_eq(inferred, mutated),
        "control: dropping the `(-1)^m` factor must change the statement"
    );

    // (3) both sides compute, and the mutant is refuted at an odd `m`.
    for (m_val, p_val, unsigned_also_holds) in [(2_u32, 5_u32, true), (3, 7, false)] {
        let m_c = d.num(m_val);
        let pp_c = d.num(p_val);
        let pi_c = d.of_nat(pp_c);
        let fact_c = d.const_app(p.factorial, &[m_c]);
        let pow_c = d.ipow(neg_one, m_c);
        let inner_c = d.imul(pow_c, fact_c);
        let signed_c = d.imul(fact_c, inner_c);
        let unsigned_c = d.imul(fact_c, fact_c);

        let target = d.iemod(neg_one, pi_c);
        let signed_mod = d.iemod(signed_c, pi_c);
        assert!(
            d.kernel().def_eq(signed_mod, target),
            "at m = {m_val} (p = {p_val}) the signed product must be `-1` mod p"
        );
        let unsigned_mod = d.iemod(unsigned_c, pi_c);
        assert_eq!(
            d.kernel().def_eq(unsigned_mod, target),
            unsigned_also_holds,
            "at m = {m_val} (p = {p_val}) the UNSIGNED product must{} be `-1` \
             mod p -- the odd row is what refutes the dropped-sign mutant, and \
             the even row is what shows the control is not vacuous",
            if unsigned_also_holds { "" } else { " NOT" }
        );
    }
}

/// `Int.firstSupplementaryLawResidue` states the first supplementary law's
/// RESIDUE half — for an odd prime `p = 2m+1` with `m` EVEN, i.e.
/// `p = 1 (mod 4)`, `-1` IS a quadratic residue mod `p`.
///
/// The mutation this test exists for is ADR-1230's M5: a conclusion the kernel
/// admits, which is TRUE, and which is not this law. Concluding at
/// `IsQuadraticResidue p (ofNat (2m))` instead of at `neg one` is exactly that
/// — `2m` is `-1`'s natural representative mod `p`, so the statement holds —
/// and no axiom footprint, prelude build, or inventory check can see the
/// difference. Only check (2) can.
///
/// The numeric content is re-runnable independently of this test:
///
/// ```text
/// python3 docs/research/09-decisions/adr-1235-first-supplementary-residue-checks.py
/// ```
#[test]
fn first_supplementary_law_residue_concludes_at_neg_one_not_its_representative() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);
    let two_nat = d.num(2);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    // (1) `Even m` is load-bearing: `-1` is a residue mod `p` exactly when the
    // half `m = (p-1)/2` is EVEN, decided here by scanning `x*x + 1 = 0 [p]`
    // over `[0,p)` with `Nat.mod`. Magnitudes stay small deliberately -- every
    // numeral this prelude builds is unary.
    for (m_val, p_val, m_is_even, expect_residue) in [
        (1_u32, 3_u32, false, false),
        (2, 5, true, true),
        (3, 7, false, false),
        (6, 13, true, true),
    ] {
        assert_eq!(m_val % 2 == 0, m_is_even, "the row's own parity must agree");
        let pp = d.num(p_val);
        let zero = d.zero();
        let one_nat = d.num(1);
        let mut found = None;
        for x_val in 0..p_val {
            let x = d.num(x_val);
            let sq = d.mul(x, x);
            let shifted = d.add(sq, one_nat);
            let r = d.modulo(shifted, pp);
            if d.kernel().def_eq(r, zero) {
                found = Some(x_val);
                break;
            }
        }
        assert_eq!(
            found.is_some(),
            expect_residue,
            "at p = {p_val} (m = {m_val}, m even = {m_is_even}) `-1` must{} be \
             a quadratic residue -- if this disagrees, the law's parity \
             hypothesis is not what decides the conclusion",
            if expect_residue { "" } else { " NOT" }
        );
    }

    // (2) the theorem at a genuinely FREE `m`, with free hypotheses -- and the
    // M5 control, which is the reason this check exists.
    let m_fv = d.fresh_fvar();
    let m_sym = d.kernel().fvar(m_fv);
    let mul2m = d.mul(two_nat, m_sym);
    let pp_sym = d.succ(mul2m);
    let pi_sym = d.of_nat(pp_sym);
    let prime_ty = super::wilson::prime_condition(&mut d, pp_sym);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);
    let nat_prelude = p.nat;
    let even_ty = d.const_app(nat_prelude.even, &[m_sym]);
    let even_fv = d.fresh_fvar();
    let even_proof = d.kernel().fvar(even_fv);

    let lemma_fn = d.lemma(p.first_supplementary_law_residue, &[m_sym]);
    let applied = d.apply(lemma_fn, &[prime_proof, even_proof]);

    let anon = d.anon_name();
    let nat_ty = d.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: m_fv,
        name: anon,
        ty: nat_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: even_fv,
        name: anon,
        ty: even_ty,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .unwrap_or_else(|e| panic!("the law must apply at a free m: {e:?}"));

    let qr_neg_one = super::euler::is_quadratic_residue(&mut d, pi_sym, neg_one);
    assert!(
        d.kernel().def_eq(inferred, qr_neg_one),
        "the law's symbolic conclusion must be `-1 IS a quadratic residue mod \
         (2m+1)`"
    );

    // The M5 mutation: `ofNat (2m)` is `-1`'s natural representative mod `p`,
    // so a proof concluding there is admitted AND true -- and is not this law.
    let ofnat_2m = d.of_nat(mul2m);
    let representative = super::euler::is_quadratic_residue(&mut d, pi_sym, ofnat_2m);
    assert!(
        !d.kernel().def_eq(inferred, representative),
        "control (ADR-1230 M5): concluding at `-1`'s natural representative \
         `ofNat (2m)` gives a statement the kernel admits and that is TRUE, \
         but is not the first supplementary law"
    );

    // (3) the parity hypothesis is refutable IN-KERNEL, not merely different:
    // the same statement with `Odd m` in place of `Even m` composes with
    // `Int.firstSupplementaryLawNotResidue` to give `False`.
    let odd_ty = d.const_app(nat_prelude.odd, &[m_sym]);
    let odd_fv = d.fresh_fvar();
    let odd_proof = d.kernel().fvar(odd_fv);
    let mutant_fv = d.fresh_fvar();
    let mutant_proof = d.kernel().fvar(mutant_fv);
    ctx.push(LocalDecl {
        fvar: odd_fv,
        name: anon,
        ty: odd_ty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: mutant_fv,
        name: anon,
        ty: qr_neg_one,
        info: BinderInfo::Default,
    });
    let not_residue_fn = d.lemma(p.first_supplementary_law_not_residue, &[m_sym]);
    let not_residue = d.apply(not_residue_fn, &[prime_proof, odd_proof]);
    let contradiction = d.apply(not_residue, &[mutant_proof]);
    let false_ty = d.false_ty();
    let got = d
        .kernel()
        .infer_in(contradiction, &mut ctx)
        .expect("the odd-parity mutant must compose with the non-residue half");
    assert!(
        d.kernel().def_eq(got, false_ty),
        "control: with `Odd m` the SAME conclusion contradicts \
         `Int.firstSupplementaryLawNotResidue`, so swapping the parity \
         hypothesis produces a refutable statement rather than a variant"
    );
}

/// `Int.prodRange_split` cuts a finite product at a symbolic point, and this
/// test measures that the cut is at the RIGHT point rather than merely that
/// some identity type-checks.
///
/// Two disjoint checks, and the concrete one carries the negative control
/// deliberately: a symbolic `!def_eq` between two `prodRange`s at a free bound
/// forces the kernel to unfold `Nat.rec` with no early exit (the pathology
/// `creal`'s riemann-sum control hit), while at concrete numerals every side
/// reduces and the same discrimination is free.
///
/// 1. **Concrete, at `f k = ofNat (succ k)`, `a = 2`, `b = 3`.** Both sides
///    reduce to `ofNat 120` (`5!`), and the SHIFT is what makes them agree:
///    with the tail function left un-shifted the right side is `2! * 3! = 12`,
///    which the control asserts is NOT the left side. Without that row the
///    concrete check would pass for a split that forgot the offset entirely.
/// 2. **Symbolic**, at genuinely free `f`, `a`, `b`: the inferred type is
///    compared against an independently rebuilt statement.
#[test]
fn prod_range_split_cuts_at_the_offset_and_not_merely_somewhere() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.prod_range_split).is_empty(),
        "Int.prodRange_split must rest on no axiom"
    );
    let mut d = IntDev::new(&mut k, p);
    let nat = d.nat_ty();

    // `fun k => ofNat (succ k)` -- `Int.factorial`'s own index function.
    let index_fn = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.of_nat(sk);
        d.lam_fv(k_fv, nat, body)
    };

    // (1) concrete, with the offset and without it.
    {
        let f = index_fn(&mut d);
        let two = d.num(2);
        let three = d.num(3);
        let five = d.num(5);
        let whole = d.const_app(p.prod_range, &[f, five]);
        let expected = {
            let n = d.num(120);
            d.of_nat(n)
        };
        assert!(
            d.kernel().def_eq(whole, expected),
            "prodRange over [0,5) of (k+1) must be 5! = 120"
        );

        let head = d.const_app(p.prod_range, &[f, two]);
        let shifted = {
            let k_fv = d.fresh_fvar();
            let kk = d.kernel().fvar(k_fv);
            let idx = d.add(two, kk);
            let sk = d.succ(idx);
            let body = d.of_nat(sk);
            d.lam_fv(k_fv, nat, body)
        };
        let tail = d.const_app(p.prod_range, &[shifted, three]);
        let split = d.imul(head, tail);
        assert!(
            d.kernel().def_eq(split, expected),
            "the SHIFTED split 2! * (3*4*5) must also be 120"
        );

        // Control: drop the offset from the tail function. `2! * 3! = 12`.
        let unshifted_tail = d.const_app(p.prod_range, &[f, three]);
        let wrong = d.imul(head, unshifted_tail);
        assert!(
            !d.kernel().def_eq(wrong, expected),
            "control: without the `add a k` offset the split is 2! * 3! = 12, \
             not 120 -- if this agrees, the concrete check cannot tell a split \
             that forgot the offset from one that did not"
        );
    }

    // (2) symbolic, at genuinely free `f`, `a`, `b`.
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let applied = d.lemma(p.prod_range_split, &[f, a, b]);

    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    for (fvar, ty) in [(f_fv, fn_ty), (a_fv, nat), (b_fv, nat)] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .unwrap_or_else(|e| panic!("the split must apply at free f, a, b: {e:?}"));

    let expected = {
        let bound = d.add(a, b);
        let lhs = d.const_app(p.prod_range, &[f, bound]);
        let head = d.const_app(p.prod_range, &[f, a]);
        let tail_fn = {
            let k_fv = d.fresh_fvar();
            let kk = d.kernel().fvar(k_fv);
            let shifted = d.add(a, kk);
            let body = d.apply(f, &[shifted]);
            d.lam_fv(k_fv, nat, body)
        };
        let tail = d.const_app(p.prod_range, &[tail_fn, b]);
        let rhs = d.imul(head, tail);
        d.ieq(lhs, rhs)
    };
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the split's symbolic statement must be \
         prodRange f (a+b) = prodRange f a * prodRange (fun k => f (a+k)) b"
    );
}

/// `Int.sumRange` **computes**, over genuinely SIGNED terms, and the trusted
/// gate refuses a near-miss.
///
/// `Int.sumRange` is a `Definition`, so `add_declaration` admitting it means
/// *well-formed*, never *correct* — a fold that returned the wrong value would
/// have exactly the same type. `f k = k − 2` is chosen so the partial sums
/// cross zero (`−2, −3, −3, −2`), which a constant or non-negative family would
/// not exercise, and the magnitudes stay in single digits because every numeral
/// here is unary.
///
/// The bound is **exclusive**: `sumRange f 4 = −2` and `f 4 = 2`, so an
/// inclusive reading of the same expression would give `0`. That is asserted in
/// both directions, which is the only thing in this file that pins the
/// convention numerically.
///
/// What this test **cannot** see, deliberately recorded: `Int.add` is
/// commutative, so folding the fresh term onto the LEFT
/// (`add (f n) (sumRange f n)`) computes the identical value at every argument.
/// No evaluation test can distinguish the two conventions;
/// [`the_sum_range_family_states_the_intended_types`] is what does.
#[test]
fn sum_range_computes_over_signed_terms_and_rejects_a_near_miss() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // f := fun (j : Nat) => Int.sub (Int.ofNat j) 2, so
    // sumRange f 4 = (0−2) + (1−2) + (2−2) + (3−2) = −2.
    let f = {
        let j = k.bvar(0);
        let of_nat = k.const_(p.of_nat, vec![]);
        let coe = k.app(of_nat, j);
        let two = numeral(&mut k, &p, 2);
        let sub = k.const_(p.sub, vec![]);
        let partial = k.app(sub, coe);
        let body = k.app(partial, two);
        k.lam(anon, nat_ty, body, BinderInfo::Default)
    };

    let sum_range = k.const_(p.sum_range, vec![]);
    let applied = k.app(sum_range, f);

    let four = numeral_nat(&mut k, &p, 4);
    let lhs = k.app(applied, four);
    let minus_two = numeral(&mut k, &p, -2);
    assert!(
        k.def_eq(lhs, minus_two),
        "sumRange (fun j => j − 2) 4 should compute to −2"
    );

    // Exclusive bound, asserted in both directions: `f 4 = 2`, so an inclusive
    // reading of the very same expression would give 0.
    let zero_i = k.const_(p.zero, vec![]);
    assert!(
        !k.def_eq(lhs, zero_i),
        "the bound must be EXCLUSIVE — an inclusive fold would add f 4 = 2 and give 0"
    );
    let five = numeral_nat(&mut k, &p, 5);
    let lhs_five = k.app(applied, five);
    assert!(
        k.def_eq(lhs_five, zero_i),
        "sumRange (fun j => j − 2) 5 should compute to 0, one term further"
    );

    // Negative control through the trusted gate itself: the same `Theorem`
    // declaration route every real lemma in `sum.rs` takes must REFUSE
    // `sumRange f 4 = −1`.
    let level_one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let minus_one = numeral(&mut k, &p, -1);
    let int_ty = k.const_(p.z, vec![]);
    let eq = k.const_(p.logic.eq, vec![level_one]);
    let false_stmt = {
        let e = k.app(eq, int_ty);
        let e = k.app(e, lhs);
        k.app(e, minus_one)
    };
    let refl = k.const_(p.logic.eq_refl, vec![level_one]);
    let false_proof = {
        let r = k.app(refl, int_ty);
        k.app(r, minus_two)
    };
    let scratch_name = k.name_str(anon, "sum_range_false_claim_scratch");
    let result = k.add_declaration(Declaration::Theorem {
        name: scratch_name,
        uparams: vec![],
        ty: false_stmt,
        value: false_proof,
    });
    assert!(
        result.is_err(),
        "the trusted gate accepted a false claim that sumRange (fun j => j − 2) 4 = −1"
    );
}

/// The `Int.sumRange` family states the types it is supposed to state, pinned
/// character for character against `render_lean`.
///
/// This is the probe for the third mutation outcome — *admitted, true, and not
/// your theorem*. Two mutations in this family land there and **no evaluation
/// test can see either one**:
///
/// * Folding the fresh term onto the LEFT of the prior sum. `Int.add` is
///   commutative, so every concrete value is unchanged; only
///   `Int.sumRange_succ`'s stated `Int.add (Int.sumRange x0 x1) (x0 x1)`
///   distinguishes it, and it is the convention `Nat.sumRange` and
///   `Int.prodRange` both use.
/// * Adding a `0 < n` premise to `Int.modEq_sumRange`. That statement is true
///   and provable, but strictly weaker; every consumer would then have to
///   discharge `0 < 2`. Note what is deliberately absent from its row below:
///   any `Int.lt Int.zero` hypothesis. `Int.modEq_prodRange` carries one
///   because `Int.ModEq.mul` needs it; `Int.ModEq.add_right`/`add_left` do not.
#[test]
fn the_sum_range_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

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

    for (name, expected) in [
        (
            p.sum_range,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : AxNat) -> Int))",
        ),
        (
            p.sum_range_zero,
            "((x0 : ((x0 : AxNat) -> Int)) -> Eq.{1} Int (Int.sumRange x0 AxNat.zero) Int.zero)",
        ),
        (
            p.sum_range_succ,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : AxNat) -> Eq.{1} Int (Int.sumRange x0 \
             (AxNat.succ x1)) (Int.add (Int.sumRange x0 x1) (x0 x1))))",
        ),
        (
            p.sum_range_congr,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : ((x1 : AxNat) -> Int)) -> ((x2 : AxNat) -> \
             ((x3 : ((x3 : AxNat) -> Eq.{1} Int (x0 x3) (x1 x3))) -> Eq.{1} Int (Int.sumRange x0 \
             x2) (Int.sumRange x1 x2)))))",
        ),
        (
            p.sum_range_add,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : ((x1 : AxNat) -> Int)) -> ((x2 : AxNat) -> \
             Eq.{1} Int (Int.sumRange (fun (x3 : AxNat) => Int.add (x0 x3) (x1 x3)) x2) (Int.add \
             (Int.sumRange x0 x2) (Int.sumRange x1 x2)))))",
        ),
        (
            p.sum_range_neg,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : AxNat) -> Eq.{1} Int (Int.sumRange (fun (x2 \
             : AxNat) => Int.neg (x0 x2)) x1) (Int.neg (Int.sumRange x0 x1))))",
        ),
        (
            p.sum_range_sub,
            "((x0 : ((x0 : AxNat) -> Int)) -> ((x1 : ((x1 : AxNat) -> Int)) -> ((x2 : AxNat) -> \
             Eq.{1} Int (Int.sumRange (fun (x3 : AxNat) => Int.sub (x0 x3) (x1 x3)) x2) (Int.sub \
             (Int.sumRange x0 x2) (Int.sumRange x1 x2)))))",
        ),
        (
            p.sum_range_of_nat,
            "((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : AxNat) -> Eq.{1} Int (Int.sumRange (fun \
             (x2 : AxNat) => Int.ofNat (x0 x2)) x1) (Int.ofNat (AxNat.sumRange x0 x1))))",
        ),
        (
            p.mod_eq_sum_range,
            "((x0 : Int) -> ((x1 : ((x1 : AxNat) -> Int)) -> ((x2 : ((x2 : AxNat) -> Int)) -> \
             ((x3 : AxNat) -> ((x4 : ((x4 : AxNat) -> Int.ModEq x0 (x1 x4) (x2 x4))) -> \
             Int.ModEq x0 (Int.sumRange x1 x3) (Int.sumRange x2 x3))))))",
        ),
        (
            p.neg_add,
            "((x0 : Int) -> ((x1 : Int) -> Eq.{1} Int (Int.neg (Int.add x0 x1)) (Int.add \
             (Int.neg x0) (Int.neg x1))))",
        ),
    ] {
        let got = rendered(&k, name);
        assert!(
            got == expected,
            "{} is stated as\n  {got}\nbut must be\n  {expected}",
            k.display_name(name)
        );
    }

    // `Int.modEq_prodRange` DOES carry the positivity premise, so the absence
    // above is a measured difference between the two aggregates rather than an
    // artefact of how this test reads types.
    let prod_row = rendered(&k, p.mod_eq_prod_range);
    assert!(
        prod_row.contains("Int.lt Int.zero"),
        "control failed: modEq_prodRange should carry `0 < n`, but reads {prod_row}"
    );
    let sum_row = rendered(&k, p.mod_eq_sum_range);
    assert!(
        !sum_row.contains("Int.lt Int.zero"),
        "modEq_sumRange must NOT carry a positivity premise: {sum_row}"
    );
}
