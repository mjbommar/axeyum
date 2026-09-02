//! Tests for the rational prelude.

use super::{RatPrelude, build_rat_prelude};
use crate::expr::{ExprId, ExprNode};
use crate::{Declaration, Kernel};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

#[test]
fn rat_prelude_is_axiom_free() {
    let (kernel, _) = built();
    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the rational prelude must assume nothing, found: {trusted:?}"
    );
}

/// The named surface of [`RatPrelude`], label paired with `NameId`. Extracted
/// to a free function (rather than inlined in one test) so the coverage
/// assertion in `every_rat_declaration_is_checked_and_axiom_free` can check
/// the environment against the very same list `every_named_declaration_exists`
/// uses, instead of a second hand-maintained copy that could drift from it.
fn named(p: &RatPrelude) -> Vec<(&'static str, crate::NameId)> {
    vec![
        ("zero", p.zero),
        ("one", p.one),
        ("le", p.le),
        ("lt", p.lt),
        ("inv", p.inv),
        ("sub", p.sub),
        ("div", p.div),
        ("mk_congr", p.mk_congr),
        ("eta", p.eta),
        ("ext", p.ext),
        ("le_total", p.le_total),
        ("lt_of_not_le", p.lt_of_not_le),
        ("le_antisymm", p.le_antisymm),
        ("lt_trichotomy", p.lt_trichotomy),
        ("mul_eq_zero", p.mul_eq_zero),
        ("normalize_add_normalize", p.normalize_add_normalize),
        ("normalize_mul_normalize", p.normalize_mul_normalize),
        ("mul_neg", p.mul_neg),
        ("neg_mul", p.neg_mul),
        ("mul_le_mul_of_nonneg_right", p.mul_le_mul_of_nonneg_right),
        ("mul_sub_mul", p.mul_sub_mul),
        ("bounds_mul", p.bounds_mul),
        ("neg_mul_le_of_bounds", p.neg_mul_le_of_bounds),
        ("natDivSucc_mul", p.nat_div_succ_mul),
        ("natDivSucc_le_one", p.nat_div_succ_le_one),
        ("natDivSucc_le_scaled", p.nat_div_succ_le_scaled),
        ("nat_index_compose", p.nat_index_compose),
        ("int_le_natAbs", p.int_le_nat_abs),
        ("int_neg_natAbs_le", p.int_neg_nat_abs_le),
        ("bounds_num", p.bounds_num),
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("mul_inv_cancel_of_neg", p.mul_inv_cancel_of_neg),
        ("mul_inv_cancel_of_ne_zero", p.mul_inv_cancel_of_ne_zero),
        ("inv_pos", p.inv_pos),
        ("one_ne_zero", p.one_ne_zero),
        ("IsField", p.is_field),
        ("rat_isField", p.rat_is_field),
        ("mul_left_cancel_of_ne_zero", p.mul_left_cancel_of_ne_zero),
        ("IsOrderedField", p.is_ordered_field),
        ("rat_isOrderedField", p.rat_is_ordered_field),
        ("sub_mul", p.sub_mul),
        ("mul_inv_sub_one", p.mul_inv_sub_one),
        ("inv_sub_inv", p.inv_sub_inv),
        ("inv_le_of_pos_le", p.inv_le_of_pos_le),
        ("mul_pos", p.mul_pos),
        ("lt_of_sq_lt", p.lt_of_sq_lt),
        ("natDivSucc_pos", p.nat_div_succ_pos),
        ("inv_natDivSucc", p.inv_nat_div_succ),
        ("natDivSucc_antitone", p.nat_div_succ_antitone),
        ("nat_index_symm", p.nat_index_symm),
        ("max", p.max),
        ("min", p.min),
        ("max_cases", p.max_cases),
        ("min_cases", p.min_cases),
        ("le_max_left", p.le_max_left),
        ("le_max_right", p.le_max_right),
        ("max_le", p.max_le),
        ("min_le_left", p.min_le_left),
        ("min_le_right", p.min_le_right),
        ("le_min", p.le_min),
        ("le_of_sub_le", p.le_of_sub_le),
        ("sub_le_of_le", p.sub_le_of_le),
        ("sub_max_le", p.sub_max_le),
        ("sub_min_le", p.sub_min_le),
        ("zero_le_max_neg", p.zero_le_max_neg),
        ("abs", p.abs),
        ("abs_nonneg", p.abs_nonneg),
        ("le_abs_self", p.le_abs_self),
        ("neg_le_abs", p.neg_le_abs),
        ("abs_zero", p.abs_zero),
        ("abs_neg", p.abs_neg),
        ("abs_add", p.abs_add),
        ("abs_mul", p.abs_mul),
        ("abs_le_of_le_of_neg_le", p.abs_le_of_le_of_neg_le),
        ("le_of_abs_le", p.le_of_abs_le),
        ("neg_le_of_abs_le", p.neg_le_of_abs_le),
        ("abs_sub_comm", p.abs_sub_comm),
        ("ble", p.ble),
        ("ble_eq_true_of_le", p.ble_eq_true_of_le),
        ("le_of_ble_eq_true", p.le_of_ble_eq_true),
        ("ble_refl", p.ble_refl),
        ("ble_trans", p.ble_trans),
        ("ble_total", p.ble_total),
        ("det2", p.det2),
        ("det2_swap_rows", p.det2_swap_rows),
        ("det2_id", p.det2_id),
        ("det2_scale_row", p.det2_scale_row),
        ("det2_row_add", p.det2_row_add),
        ("det2_mul", p.det2_mul),
        ("det2_eq_zero_of_lin_dep", p.det2_eq_zero_of_lin_dep),
        ("mul_adj2_top_left", p.mul_adj2_top_left),
        ("mul_adj2_top_right", p.mul_adj2_top_right),
        ("mul_adj2_bottom_left", p.mul_adj2_bottom_left),
        ("mul_adj2_bottom_right", p.mul_adj2_bottom_right),
        ("inv2_top_left", p.inv2_top_left),
        ("inv2_top_right", p.inv2_top_right),
        ("inv2_bottom_left", p.inv2_bottom_left),
        ("inv2_bottom_right", p.inv2_bottom_right),
        ("cramer_two_unique_x", p.cramer_two_unique_x),
        ("cramer_two_unique_y", p.cramer_two_unique_y),
        ("cramer2_x", p.cramer2_x),
        ("cramer2_y", p.cramer2_y),
        ("cramer2_solves", p.cramer2_solves),
        ("ofInt", p.of_int),
        ("ofInt_add", p.of_int_add),
        ("ofInt_mul", p.of_int_mul),
        ("ofInt_neg", p.of_int_neg),
        ("det2_fib", p.det2_fib),
        ("det3", p.det3),
        ("det3_id", p.det3_id),
        ("det3_cofactor_row1", p.det3_cofactor_row1),
        ("det3_scale_row", p.det3_scale_row),
        ("det3_ofInt", p.det3_ofint),
        ("det3_example_generic", p.det3_example_generic),
        ("det3_example_diagonal", p.det3_example_diagonal),
        ("det3_example_singular", p.det3_example_singular),
        ("bernoulli", p.bernoulli),
        ("bernoulli_harmonic_bound", p.bernoulli_harmonic_bound),
        ("matSkip", p.mat_skip),
        ("matMinor", p.mat_minor),
        ("altSign", p.alt_sign),
        ("altSign_zero", p.alt_sign_zero),
        ("altSign_succ", p.alt_sign_succ),
        ("det", p.det),
        ("det_zero", p.det_zero),
        ("det_succ", p.det_succ),
        ("det_one", p.det_one),
        ("det_eq_det2", p.det_eq_det2),
        ("det_eq_det3", p.det_eq_det3),
        ("matMinor_eval_example", p.mat_minor_eval_example),
        ("det_eval_example", p.det_eval_example),
        ("det_eval_singular", p.det_eval_singular),
        ("det_eval_example4", p.det_eval_example4),
        ("sumRange_head_of_tail_zero", p.sum_range_head_of_tail_zero),
        ("det_congr", p.det_congr),
        ("matMinor_matId", p.mat_minor_mat_id),
        ("det_matId", p.det_mat_id),
        ("matSkip_zero", p.mat_skip_zero),
        ("matSkip_succ_succ", p.mat_skip_succ_succ),
        ("matSkip_comm", p.mat_skip_comm),
        ("matMinor_col_comm", p.mat_minor_col_comm),
        ("det_minor_col_comm", p.det_minor_col_comm),
        ("sumRange_peel_head", p.sum_range_peel_head),
        ("sumRange_matSkip", p.sum_range_mat_skip),
        ("unskip", p.unskip),
        ("unskip_zero", p.unskip_zero),
        ("unskip_succ_zero", p.unskip_succ_zero),
        ("unskip_succ_succ", p.unskip_succ_succ),
        ("unskip_matSkip", p.unskip_mat_skip),
        ("beq_matSkip", p.beq_mat_skip),
        ("beq_matSkip_left", p.beq_mat_skip_left),
        ("altSign_succ_add", p.alt_sign_succ_add),
        ("ble_flip_of_false", p.ble_flip_of_false),
        ("unskip_le", p.unskip_le),
        ("unskip_gt", p.unskip_gt),
        ("matMinor_double_comm_lo", p.mat_minor_double_comm_lo),
        ("matMinor_double_comm_hi", p.mat_minor_double_comm_hi),
        ("det_double_comm_lo", p.det_double_comm_lo),
        ("det_double_comm_hi", p.det_double_comm_hi),
        ("mul_perm4", p.mul_perm4),
        ("laplaceSummand", p.laplace_summand),
        ("laplaceSummand_rowZero", p.laplace_summand_row_zero),
        ("laplaceSummand_rowI", p.laplace_summand_row_i),
        ("laplaceSummand_diag", p.laplace_summand_diag),
        ("det_row_expansion", p.det_row_expansion),
        ("matMinor_row_col_comm", p.mat_minor_row_col_comm),
        ("det_minor_row_col_comm", p.det_minor_row_col_comm),
        ("det_col_expansion", p.det_col_expansion),
        ("matMinor_transpose", p.mat_minor_transpose),
        ("det_transpose", p.det_transpose),
        ("det_alternating", p.det_alternating),
        ("det_row_swap", p.det_row_swap),
        ("det_row_replaced", p.det_row_replaced),
        ("det_row_zero", p.det_row_zero),
        ("det_row_smul", p.det_row_smul),
        ("det_row_multilinear", p.det_row_multilinear),
        ("det_matMul_2", p.det_mat_mul_2),
        (
            "det_row_selection_of_duplicate",
            p.det_row_selection_of_duplicate,
        ),
        ("det_congr_lt", p.det_congr_lt),
        ("matSkip_lt_succ", p.mat_skip_lt_succ),
        ("det_congr_entry_lt", p.det_congr_entry_lt),
        ("det_row_selection_injective", p.det_row_selection_injective),
        ("det_row_selection", p.det_row_selection),
        ("prodRange", p.prod_range),
        ("prodRange_zero", p.prod_range_zero),
        ("prodRange_succ", p.prod_range_succ),
        ("prodRange_shiftFront", p.prod_range_shift_front),
        ("prodRange_congr", p.prod_range_congr),
        ("sumRange_mul_right", p.sum_range_mul_right),
        ("sumRange_mul_left", p.sum_range_mul_left),
        ("sumMaps", p.sum_maps),
        ("sumMaps_zero", p.sum_maps_zero),
        ("sumMaps_succ", p.sum_maps_succ),
        ("sumMaps_congr", p.sum_maps_congr),
        ("sumMaps_mul_left", p.sum_maps_mul_left),
        ("sumMaps_mul_right", p.sum_maps_mul_right),
        ("matSetRow", p.mat_set_row),
        ("matSetRow_at", p.mat_set_row_at),
        ("matSetRow_off", p.mat_set_row_off),
        ("matSubstRows", p.mat_subst_rows),
        ("matSubstRows_below", p.mat_subst_rows_below),
        ("matSubstRows_at", p.mat_subst_rows_at),
    ]
}

#[test]
fn every_named_declaration_exists() {
    let (kernel, p) = built();
    for (label, name) in named(&p) {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} was interned but never declared"
        );
    }
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// printed as opaque `ExprId`s. A `Debug` of `KernelError` says nothing about
/// what was refused; this says which two types failed to match.
#[test]
fn rat_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_rat_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a rational proof: {explained}");
        }
    }
}

/// Every one of the 22 ordered-commutative-ring laws is a **checked theorem**
/// with an empty axiom footprint — not an axiom, not an opaque, not missing.
///
/// This fails if a law is dropped, demoted to an axiom, or quietly loses its
/// proof: it reads the kernel's own environment and footprint rather than
/// trusting that `build_rat_prelude` returned `Ok`.
#[test]
fn every_ordered_ring_law_is_a_checked_theorem() {
    let (kernel, p) = built();
    for (index, law) in p.ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(
            footprint.is_empty(),
            "ring law #{index} ({rendered}) rests on {footprint:?}"
        );
    }
}

/// Dropping any single law is caught: the list this asserts against is
/// `RatPrelude::ring_laws`, which `build_rat_model_of_arith` pairs positionally
/// with the `Real` package, so a shortened or reordered list is a build failure
/// there rather than a silently weaker claim here.
#[test]
fn the_ring_law_list_has_exactly_twenty_two_distinct_entries() {
    let (kernel, p) = built();
    let mut names: Vec<String> = p
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    assert_eq!(names.len(), 22);
    names.sort();
    names.dedup();
    assert_eq!(names.len(), 22, "the ring-law list repeats an entry");
}

/// COVERAGE, checked against the ENVIRONMENT rather than against `named`
/// itself.
///
/// `every_named_declaration_exists` only ever checks that a hand-maintained
/// list's entries are PRESENT, never their kind or axiom footprint; a
/// `Definition`/`Theorem` declared under `Rat.` and omitted from both `named`
/// and `RatPrelude::ring_laws` would sail through this whole file unchecked.
/// Mirrors `every_creal_declaration_is_checked_and_axiom_free` (`creal_tests.rs`)
/// and `every_nat_declaration_is_checked_and_axiom_free`
/// (`nat_prelude_tests.rs`), both landed after exactly this gap was found in
/// `creal`.
///
/// Scoped to `Definition`/`Theorem` kinds deliberately: `Rat` is a
/// `Definition` over a normalized `Int` pair (not its own inductive), so there
/// is no separate constructor/recursor family to exclude here the way `Nat`'s
/// and `Int`'s inductive machinery is excluded above.
/// Everything `every_rat_declaration_is_checked_and_axiom_free` found live in
/// the prelude and absent from both `named` and `RatPrelude::ring_laws` on its
/// first run, 142 declarations in total (8 structural `Rat.*` definitions
/// reached through `p.int.rat_*` -- interned in `int_prelude.rs` alongside
/// `Int` itself, since `Rat`'s namespace root is minted there -- plus the
/// cross-multiplication/order lemmas, the `sumRange`/`pow`/polynomial/vector
/// machinery, and an entire probability-theory package: `expectation`,
/// `variance`, `covariance`, Markov's and Chebyshev's inequalities, and the
/// weak law of large numbers). None of it had ever had its axiom footprint
/// checked by this file.
fn unnamed_but_live_declarations(p: &RatPrelude) -> Vec<crate::NameId> {
    vec![
        p.int.rat_normalize,
        p.int.rat_num,
        p.int.rat_den,
        p.int.rat_den_pos,
        p.int.rat_mul,
        p.int.rat_reduced,
        p.int.rat_neg,
        p.int.rat_add,
        p.gcd_one_right,
        p.nat_gauss,
        p.nat_dvd_antisymm_pos,
        p.nat_mul_right_cancel,
        p.nat_div_cross,
        p.nat_abs_mul_of_nat,
        p.of_nat_inj,
        p.not_zero_le_neg_of_nat,
        p.int_mul_right_cancel,
        p.int_le_of_mul_le_mul_right,
        p.int_lt_of_mul_lt_mul_right,
        p.int_mul_le_mul_right,
        p.int_mul_lt_mul_right,
        p.int_right_distrib,
        p.int_zero_mul,
        p.eq_zero_of_num_zero,
        p.int_nonneg_of_nonneg,
        p.nonneg_of_int_nonneg,
        p.int_zero_le_of_nat,
        p.int_of_nat_pos,
        p.eq_of_cross,
        p.cross_of_eq,
        p.normalize_cross,
        p.normalize_congr,
        p.self_normalize,
        p.add_cross,
        p.mul_cross,
        p.right_distrib,
        p.nat_div_succ,
        p.int_le_or_lt,
        p.le_or_lt,
        p.int_pos_of_pos,
        p.int_one_le_of_pos,
        p.nat_div_succ_lt_of_pos,
        p.le_of_le_add_nat_div_succ,
        p.zero_add,
        p.neg_add_cancel,
        p.neg_eq_of_add_eq_zero,
        p.neg_neg,
        p.neg_zero,
        p.neg_add,
        p.neg_le_neg,
        p.sub_self,
        p.neg_sub,
        p.sub_add_add,
        p.sub_neg_sub,
        p.sub_add_sub,
        p.bounds_add,
        p.nat_div_succ_add,
        p.nat_div_succ_halve,
        p.nat_div_succ_scale,
        p.nat_div_succ_le_add_left,
        p.zero_le_nat_div_succ,
        p.neg_nonpos_of_nonneg,
        p.bounds_neg,
        p.add_nonneg,
        p.decidable_le,
        p.sum_range,
        p.sum_range_zero,
        p.sum_range_succ,
        p.sum_range_congr,
        p.sum_range_add,
        p.mul_sum_range,
        p.sum_range_le,
        p.sum_range_nonneg,
        p.sum_range_congr_lt,
        p.sum_range_eq_zero_of_lt,
        p.sum_range_swap,
        p.sum_range_split,
        p.sum_range_diagonal,
        p.sum_range_rect_eq_diag_add_corner,
        p.sum_range_mul,
        p.sum_range_mul_double,
        p.sum_range_mul_eq_diag_add_corner,
        p.pow,
        p.pow_zero,
        p.pow_succ,
        p.pow_add,
        p.pow_sub_add,
        p.pow_nat_div_succ_two,
        p.poly_eval,
        p.poly_eval_zero,
        p.poly_eval_succ,
        p.poly_eval_add,
        p.poly_eval_smul,
        p.pow_one,
        p.add_sub_cancel_left,
        p.sq_sub_sq,
        p.poly_eval_deg1,
        p.taylor_deg1,
        p.dot_n,
        p.dot_n_zero,
        p.dot_n_succ,
        p.dot_n_comm,
        p.dot_n_add_left,
        p.dot_n_smul_left,
        p.dot_n_self_nonneg,
        p.dot_n_two,
        p.dot_n_cauchy_schwarz,
        p.mat_mul,
        p.mat_mul_zero,
        p.mat_mul_succ,
        p.mat_mul_assoc,
        p.mat_mul_add_left,
        p.mat_mul_add_right,
        p.mat_mul_smul_left,
        p.sum_range_delta,
        p.mat_id,
        p.mat_id_diag,
        p.mat_id_off_diag,
        p.mat_mul_id_left,
        p.mat_mul_id_right,
        p.mat_transpose,
        p.mat_transpose_transpose,
        p.mat_transpose_mul,
        p.mat_transpose_eval_example,
        p.mat_transpose_mul_example,
        p.mat_inv2,
        p.matinv2_matmul_top_left,
        p.matinv2_matmul_top_right,
        p.matinv2_matmul_bottom_left,
        p.matinv2_matmul_bottom_right,
        p.matmul_matinv2_top_left,
        p.matmul_matinv2_top_right,
        p.matmul_matinv2_bottom_left,
        p.matmul_matinv2_bottom_right,
        p.mat_inv2_eval_example,
        p.mat_inv2_example,
        p.is_distribution,
        p.prob_le_one,
        p.prob_complement,
        p.expectation,
        p.expectation_add,
        p.expectation_smul,
        p.expectation_const,
        p.uniform,
        p.uniform_is_distribution,
        p.expectation_nonneg,
        p.expectation_le,
        p.markov_inequality,
        p.expectation_indicator_le_one,
        p.variance,
        p.variance_nonneg,
        p.variance_eq,
        p.variance_smul,
        p.covariance,
        p.covariance_comm,
        p.variance_add_eq,
        p.variance_add_of_uncorrelated,
        p.indicator,
        p.indicator_nonneg,
        p.indicator_le,
        p.variance_indicator,
        p.variance_indicator_le_quarter,
        p.markov_constructed,
        p.chebyshev_inequality,
        p.covariance_add_right,
        p.covariance_smul_left,
        p.covariance_sq_le_variance_mul,
        p.sum_vars,
        p.expectation_sum_vars,
        p.covariance_sum_vars_left,
        p.covariance_sum_vars,
        p.pairwise_uncorrelated,
        p.variance_sum_vars,
        p.variance_scaled_mean,
        p.chebyshev_sample_mean_uncorrelated,
        p.variance_sample_mean_uncorrelated,
        p.weak_law_of_large_numbers,
        p.bernoulli_law_of_large_numbers,
        p.variance_scaled_add_nonneg,
        p.covariance_sq_le_variance_mul_of_pos,
        p.covariance_sq_le_variance_mul_of_zero_zero,
    ]
}

#[test]
fn every_rat_declaration_is_checked_and_axiom_free() {
    let (kernel, p) = built();
    let listed: std::collections::BTreeSet<crate::NameId> = named(&p)
        .into_iter()
        .map(|(_, name)| name)
        .chain(p.ring_laws())
        .chain(unnamed_but_live_declarations(&p))
        .collect();
    let declared: Vec<(crate::NameId, Declaration)> = kernel
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
            ) && kernel.display_name(*name).to_string().starts_with("Rat.")
                && !listed.contains(name)
        })
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `Rat` definitions/theorems are live in the prelude but absent \
         from `named`/`RatPrelude::ring_laws`/`unnamed_but_live_declarations`, \
         so nothing checks their kind or \
         axiom-footprint: {unlisted:?}. Add them there -- do not delete this \
         assertion."
    );

    for (name, decl) in &declared {
        let shown = kernel.display_name(*name).to_string();
        if !shown.starts_with("Rat.") || !listed.contains(name) {
            continue;
        }
        assert!(
            !matches!(decl, Declaration::Axiom { .. } | Declaration::Opaque { .. }),
            "{shown} is asserted, not derived"
        );
        let footprint = kernel.axiom_footprint(*name);
        assert!(
            footprint.is_empty(),
            "{shown} must have an empty axiom footprint, found {:?}",
            footprint
                .iter()
                .map(|n| kernel.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// `Rat.le` is not just total (`le_total`) but **antisymmetric**
/// (`le_antisymm`) and its strict companion is **trichotomous**
/// (`lt_trichotomy`) — none of which is one of the 22, and the last two did
/// not exist before this development. `le_antisymm` is built directly on
/// `int_prelude`'s own `Int.le_antisymm`. Every declaration involved is a
/// **checked** theorem with an empty axiom footprint — read out of the
/// kernel, not off the diff.
#[test]
fn the_order_is_antisymmetric_and_trichotomous_and_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("le_antisymm", p.le_antisymm),
        ("lt_trichotomy", p.lt_trichotomy),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// The statements are the unweakened ones, rendered verbatim: `le_antisymm`'s
/// conclusion is the bare equality (not, say, `le a b` again), and
/// `lt_trichotomy`'s disjunction is right-associated with `lt a b` first,
/// `a = b` in the middle and `lt b a` last — not some other bracketing that
/// would still have an empty footprint while proving something weaker or
/// differently-shaped than trichotomy.
#[test]
fn the_order_completeness_statements_are_the_unweakened_ones() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.le_antisymm),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat.le x0 x1) -> \
         ((x3 : Rat.le x1 x0) -> Eq.{1} Rat x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_trichotomy),
        "((x0 : Rat) -> ((x1 : Rat) -> \
         Or (Rat.lt x0 x1) (Or (Eq.{1} Rat x0 x1) (Rat.lt x1 x0))))"
    );
}

/// `Rat.mul_eq_zero` is a **checked** theorem with an empty axiom footprint.
///
/// It is not a cross-multiplication fact like the order laws above — `Rat.mul`
/// normalises, so it earns its own check rather than riding along with
/// [`the_order_is_antisymmetric_and_trichotomous_and_axiom_free`].
#[test]
fn mul_eq_zero_is_axiom_free() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.mul_eq_zero)
        .expect("Rat.mul_eq_zero was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Rat.mul_eq_zero must be a checked Theorem, found a different kind"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.mul_eq_zero)
        .into_iter()
        .map(|entry| kernel.display_name(entry).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Rat.mul_eq_zero rests on {footprint:?}"
    );
}

/// `Rat.right_distrib` is a **checked** theorem with an empty axiom
/// footprint, read out of the kernel, not off the diff.
#[test]
fn right_distrib_is_axiom_free() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.right_distrib)
        .expect("Rat.right_distrib was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Rat.right_distrib must be a checked Theorem, found a different kind"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.right_distrib)
        .into_iter()
        .map(|entry| kernel.display_name(entry).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Rat.right_distrib rests on {footprint:?}"
    );
}

/// `Rat.det2` and its theorems — the 2×2 linear algebra `matrix` adds,
/// including the `ℤ→ℚ` cast `Rat.ofInt` and the Fibonacci–determinant bridge
/// `Rat.det2_fib` — are each a **checked** declaration with an empty axiom
/// footprint, read out of the kernel rather than off the diff. `det2` and
/// `ofInt` are `Definition`s (their defining equations hold by unfolding, so
/// neither needs an equation lemma); everything else here is a `Theorem`.
#[test]
fn matrix_laws_are_axiom_free() {
    let (kernel, p) = built();

    let declaration = kernel
        .environment()
        .get(p.det2)
        .expect("Rat.det2 was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.det2 must be a Definition, found a different kind"
    );

    let declaration = kernel
        .environment()
        .get(p.of_int)
        .expect("Rat.ofInt was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.ofInt must be a Definition, found a different kind"
    );

    let declaration = kernel
        .environment()
        .get(p.cramer2_x)
        .expect("Rat.cramer2_x was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.cramer2_x must be a Definition, found a different kind"
    );

    let declaration = kernel
        .environment()
        .get(p.cramer2_y)
        .expect("Rat.cramer2_y was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.cramer2_y must be a Definition, found a different kind"
    );

    let declaration = kernel
        .environment()
        .get(p.det3)
        .expect("Rat.det3 was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.det3 must be a Definition, found a different kind"
    );

    let expected = [
        ("det2_swap_rows", p.det2_swap_rows),
        ("det2_id", p.det2_id),
        ("det2_scale_row", p.det2_scale_row),
        ("det2_row_add", p.det2_row_add),
        ("det2_mul", p.det2_mul),
        ("det2_eq_zero_of_lin_dep", p.det2_eq_zero_of_lin_dep),
        ("mul_adj2_top_left", p.mul_adj2_top_left),
        ("mul_adj2_top_right", p.mul_adj2_top_right),
        ("mul_adj2_bottom_left", p.mul_adj2_bottom_left),
        ("mul_adj2_bottom_right", p.mul_adj2_bottom_right),
        ("inv2_top_left", p.inv2_top_left),
        ("inv2_top_right", p.inv2_top_right),
        ("inv2_bottom_left", p.inv2_bottom_left),
        ("inv2_bottom_right", p.inv2_bottom_right),
        ("cramer_two_unique_x", p.cramer_two_unique_x),
        ("cramer_two_unique_y", p.cramer_two_unique_y),
        ("cramer2_solves", p.cramer2_solves),
        ("ofInt_add", p.of_int_add),
        ("ofInt_mul", p.of_int_mul),
        ("ofInt_neg", p.of_int_neg),
        ("det2_fib", p.det2_fib),
        ("det3_id", p.det3_id),
        ("det3_cofactor_row1", p.det3_cofactor_row1),
        ("det3_scale_row", p.det3_scale_row),
        ("det3_ofInt", p.det3_ofint),
        ("det3_example_generic", p.det3_example_generic),
        ("det3_example_diagonal", p.det3_example_diagonal),
        ("det3_example_singular", p.det3_example_singular),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.det3_scale_row` applied at a concrete, ASYMMETRIC instance —
/// `diag(2,3,4)` (determinant `24`) with row 1 scaled by `5`, expected
/// result `120` — checked by REDUCTION, not merely that the general law
/// type-checks (true of a vacuous law too).
///
/// `Rat.mul`/`Rat.add` do not themselves compute at concrete `Rat` literals
/// (see `declare_det3_ofint`'s own doc comment), so this routes the concrete
/// instance through `Rat.det3_ofInt` (to turn the inner, unscaled
/// `det3 2 0 0 0 3 0 0 0 4` into a pure `Int` expression) and `Rat.ofInt_mul`
/// (to pull the outer `5 *` inside the cast too), exactly the way
/// `declare_det3_example` bridges any concrete `Rat.det3` value to `Int`
/// arithmetic, which the kernel then computes for free. The final declared
/// goal names the literal `120` independently (not the `Int` expression the
/// proof actually produces), so the kernel's own conversion check is what
/// confirms the two agree — a wrong `det3_scale_row` (wrong sign, wrong
/// argument mapping) would make this declaration fail to type-check.
#[test]
fn det3_scale_row_computes_at_diag_2_3_4_scaled_by_5() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rcongr, req, rmul, rsymm, rtrans};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let int_lit = |d: &mut IntDev<'_>, n: u32| -> ExprId {
        let nat = d.num(n);
        d.of_nat(nat)
    };
    let of_int = |d: &mut IntDev<'_>, n: ExprId| -> ExprId { d.const_app(p.of_int, &[n]) };

    let five = int_lit(&mut d, 5);
    let two = int_lit(&mut d, 2);
    let zero_i = int_lit(&mut d, 0);
    let three = int_lit(&mut d, 3);
    let four = int_lit(&mut d, 4);

    let qk = of_int(&mut d, five);
    let qa = of_int(&mut d, two);
    let qz = of_int(&mut d, zero_i);
    let qe = of_int(&mut d, three);
    let qi = of_int(&mut d, four);

    // pf1 : det3 (qk*qa) (qk*qz) (qk*qz) qz qe qz qz qz qi
    //     = qk * det3 qa qz qz qz qe qz qz qz qi
    let pf1 = d.lemma(p.det3_scale_row, &[qk, qa, qz, qz, qz, qe, qz, qz, qz, qi]);

    let ka = rmul(&mut d, qk, qa);
    let kz = rmul(&mut d, qk, qz);
    let lhs0 = d.const_app(p.det3, &[ka, kz, kz, qz, qe, qz, qz, qz, qi]);
    let inner_det = d.const_app(p.det3, &[qa, qz, qz, qz, qe, qz, qz, qz, qi]);
    let rhs0 = rmul(&mut d, qk, inner_det);

    // pf2 : det3 qa qz qz qz qe qz qz qz qi = ofInt (Sarrus at 2,0,0,0,3,0,0,0,4)
    let pf2 = d.lemma(
        p.det3_ofint,
        &[
            two, zero_i, zero_i, zero_i, three, zero_i, zero_i, zero_i, four,
        ],
    );
    let ei = d.imul(three, four);
    let fh = d.imul(zero_i, zero_i);
    let x = d.isub(ei, fh);
    let di = d.imul(zero_i, four);
    let fg = d.imul(zero_i, zero_i);
    let y = d.isub(di, fg);
    let dh = d.imul(zero_i, zero_i);
    let eg = d.imul(three, zero_i);
    let z = d.isub(dh, eg);
    let ax = d.imul(two, x);
    let by = d.imul(zero_i, y);
    let ax_by = d.isub(ax, by);
    let cz = d.imul(zero_i, z);
    let sarrus24 = d.iadd(ax_by, cz); // must REDUCE to 24
    let of_sarrus24 = of_int(&mut d, sarrus24);

    // Rewrite rhs0 = qk * inner_det  into  qk * ofInt(sarrus24).
    let step_inner = rcongr(&mut d, inner_det, of_sarrus24, pf2, &|d, t| rmul(d, qk, t));
    let rhs1 = rmul(&mut d, qk, of_sarrus24);

    // qk * ofInt(sarrus24) = ofInt(5 * sarrus24), via ofInt_mul reversed.
    let mul_lemma = d.lemma(p.of_int_mul, &[five, sarrus24]); // ofInt(5*sarrus24) = qk*ofSarrus24
    let five_sarrus = d.imul(five, sarrus24);
    let of_five_sarrus = of_int(&mut d, five_sarrus);
    let step_outer = rsymm(&mut d, rhs1, of_five_sarrus, mul_lemma);

    let rhs_to_final = rtrans(&mut d, rhs0, rhs1, of_five_sarrus, step_inner, step_outer);
    let full_proof = rtrans(&mut d, lhs0, rhs0, of_five_sarrus, pf1, rhs_to_final);

    // The declared goal names the expected value INDEPENDENTLY (`120`, not the
    // `Int` expression the proof produced) -- the kernel's own conversion
    // check is what confirms `5 * sarrus(2,0,0,0,3,0,0,0,4)` reduces to it.
    let expected = int_lit(&mut d, 120);
    let of_expected = of_int(&mut d, expected);
    let claim = req(&mut d, lhs0, of_expected);
    let name = d
        .kernel()
        .name_str(anon, "Check.det3_scale_row_diag_2_3_4_by_5");
    let accepted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: full_proof,
    });
    assert!(
        accepted.is_ok(),
        "det3_scale_row at diag(2,3,4) scaled by 5 must REDUCE to 120: {accepted:?}"
    );
}

/// `Rat.det2_eq_zero_of_lin_dep`'s statement, asserted verbatim: the
/// nontriviality disjunction first, then the two row equations, then the
/// conclusion — not some other bracketing that would still typecheck while
/// claiming something weaker (e.g. dropping the disjunction, or swapping
/// which row each equation names).
#[test]
fn det2_eq_zero_of_lin_dep_is_the_stated_form() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.det2_eq_zero_of_lin_dep)
        .expect("declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat) -> ((x6 : Or (Not (Eq.{1} Rat x4 Rat.zero)) (Not (Eq.{1} Rat x5 \
         Rat.zero))) -> ((x7 : Eq.{1} Rat (Rat.add (Rat.mul x4 x0) (Rat.mul x5 x2)) \
         Rat.zero) -> ((x8 : Eq.{1} Rat (Rat.add (Rat.mul x4 x1) (Rat.mul x5 x3)) \
         Rat.zero) -> Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)))))))))"
    );
}

/// `Rat.det2_eq_zero_of_lin_dep` applied at an explicit SINGULAR matrix,
/// checked by pure REDUCTION — not merely that the theorem type-checks
/// (true of a vacuous statement too).
///
/// Matrix `[[1,2],[2,4]]` (`a=1,b=2,c=2,d=4`): row 2 is `2·row1`, so
/// `(-2)·row1 + 1·row2 = 0` is a genuine nontrivial dependence (`t=1 ≠ 0`).
/// `det2 1 2 2 4` independently REDUCES to `0` by `Eq.refl` (checked below,
/// separately from the theorem), confirming the theorem's conclusion is the
/// value it claims, not just a type that happens to accept.
///
/// A non-singular instance (`[[2,1],[1,1]]`, `D=1`, the same system
/// `cramer2_solves_computes_an_explicit_two_by_two_system` uses) is checked
/// alongside: `det2` REDUCES to the nonzero `1` there, so the two literal
/// computations of `det2` this file exercises land on different values, not
/// a formula that happens to always produce `0`.
#[test]
fn det2_eq_zero_of_lin_dep_computes_at_an_explicit_singular_matrix() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rmul, rneg, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // The singular matrix and its dependence witness.
    let a = literal(&mut d, 1);
    let b = literal(&mut d, 2);
    let c = literal(&mut d, 2);
    let dd = literal(&mut d, 4);
    let two = literal(&mut d, 2);
    let s = rneg(&mut d, two); // s = -2
    let t = literal(&mut d, 1); // t = 1

    // det2 1 2 2 4 REDUCES to 0.
    let det = d.const_app(p.det2, &[a, b, c, dd]);
    let zero_r = rzero(&mut d, p);
    let claim_det_zero = req(&mut d, det, zero_r);
    let proof_det_zero = rrefl(&mut d, zero_r);
    let name_det_zero = d.kernel().name_str(anon, "Check.det2_singular_value");
    let accepted_det_zero = d.kernel().add_declaration(Declaration::Theorem {
        name: name_det_zero,
        uparams: vec![],
        ty: claim_det_zero,
        value: proof_det_zero,
    });
    assert!(
        accepted_det_zero.is_ok(),
        "det2 1 2 2 4 must REDUCE to 0: {accepted_det_zero:?}"
    );

    // t ≠ 0, from 0 < t = natDivSucc 1 0 (Nat.le 1 1 = Nat.le_refl), the same
    // route `cramer2_solves_computes_an_explicit_two_by_two_system` uses for
    // its D ≠ 0.
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let le_pf = d.lemma(p.int.nat.le_refl, &[one_nat]); // Nat.le 1 1
    let pos = d.lemma(p.nat_div_succ_pos, &[one_nat, zero_nat, le_pf]); // 0 < t
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let t_eq_zero_ty = req(&mut d, t, zero_r);
    let rewritten =
        crate::rat_prelude::ops::rat_eq_rewrite(&mut d, t, zero_r, heq, pos, &|d, w| {
            crate::rat_prelude::ops::rlt(d, p, zero_r, w)
        });
    let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
    let false_proof = d.apply(irrefl, &[rewritten]);
    let t_ne_zero_proof = d.lam_fv(heq_fv, t_eq_zero_ty, false_proof); // Not (t = 0)

    let s_eq_zero_ty = req(&mut d, s, zero_r);
    let s_ne_zero_ty = d.not(s_eq_zero_ty);
    let t_ne_zero_ty = d.not(t_eq_zero_ty);
    let nt = d.or_inr(s_ne_zero_ty, t_ne_zero_ty, t_ne_zero_proof);

    // The two row equations, checked by pure reduction (they are concrete
    // literal arithmetic): (-2)*1+1*2 = 0, (-2)*2+1*4 = 0.
    let sa = rmul(&mut d, s, a);
    let tc = rmul(&mut d, t, c);
    let sa_tc = radd(&mut d, sa, tc);
    let eq1_claim = req(&mut d, sa_tc, zero_r);
    let eq1_proof = rrefl(&mut d, zero_r);
    let name_eq1 = d.kernel().name_str(anon, "Check.det2_singular_eq1");
    let accepted_eq1 = d.kernel().add_declaration(Declaration::Theorem {
        name: name_eq1,
        uparams: vec![],
        ty: eq1_claim,
        value: eq1_proof,
    });
    assert!(
        accepted_eq1.is_ok(),
        "(-2)*1+1*2 must REDUCE to 0: {accepted_eq1:?}"
    );

    let sb = rmul(&mut d, s, b);
    let td = rmul(&mut d, t, dd);
    let sb_td = radd(&mut d, sb, td);
    let eq2_claim = req(&mut d, sb_td, zero_r);
    let eq2_proof = rrefl(&mut d, zero_r);
    let name_eq2 = d.kernel().name_str(anon, "Check.det2_singular_eq2");
    let accepted_eq2 = d.kernel().add_declaration(Declaration::Theorem {
        name: name_eq2,
        uparams: vec![],
        ty: eq2_claim,
        value: eq2_proof,
    });
    assert!(
        accepted_eq2.is_ok(),
        "(-2)*2+1*4 must REDUCE to 0: {accepted_eq2:?}"
    );

    // The theorem itself, applied at this concrete instance.
    let concluded = d.lemma(
        p.det2_eq_zero_of_lin_dep,
        &[a, b, c, dd, s, t, nt, eq1_proof, eq2_proof],
    );
    let name_concl = d.kernel().name_str(anon, "Check.det2_lin_dep_instance");
    let accepted_concl = d.kernel().add_declaration(Declaration::Theorem {
        name: name_concl,
        uparams: vec![],
        ty: claim_det_zero,
        value: concluded,
    });
    assert!(
        accepted_concl.is_ok(),
        "det2_eq_zero_of_lin_dep at the singular instance must discharge \
         det2 1 2 2 4 = 0: {accepted_concl:?}"
    );

    // The non-singular companion: det2 2 1 1 1 REDUCES to 1, not 0.
    let a2 = literal(&mut d, 2);
    let b2 = literal(&mut d, 1);
    let c2 = literal(&mut d, 1);
    let d2 = literal(&mut d, 1);
    let det_ns = d.const_app(p.det2, &[a2, b2, c2, d2]);
    let one_r = crate::rat_prelude::ops::rone(&mut d, p);
    let claim_ns = req(&mut d, det_ns, one_r);
    let proof_ns = rrefl(&mut d, one_r);
    let name_ns = d.kernel().name_str(anon, "Check.det2_nonsingular_value");
    let accepted_ns = d.kernel().add_declaration(Declaration::Theorem {
        name: name_ns,
        uparams: vec![],
        ty: claim_ns,
        value: proof_ns,
    });
    assert!(
        accepted_ns.is_ok(),
        "det2 2 1 1 1 must REDUCE to 1: {accepted_ns:?}"
    );
}

/// The negative control this file's "proportional" statement needs: the
/// NAIVE existential `∃ t, c = t·a ∧ d = t·b` is FALSE at `a = b = 0` with
/// `(c,d)` nonzero, even though `det2` is then always `0` (checked in
/// [`det2_eq_zero_of_lin_dep_computes_at_an_explicit_singular_matrix`]'s
/// style elsewhere in this file). `Rat.mul_zero` gives `t·a = 0` for **any**
/// `t` (symbolic, no case split) when `a = 0`; combined with `c = 1` NOT
/// reducing to `0` (checked below by the kernel REFUSING the claim), no `t`
/// can satisfy `c = t·a` — the naive form has no witness here, which is
/// exactly the gap [`RatPrelude::det2_eq_zero_of_lin_dep`]'s `s,t` form does
/// not have.
#[test]
fn the_naive_proportionality_existential_has_no_witness_at_a_eq_b_eq_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rtrans, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = rzero(&mut d, p); // a = 0
    let c = literal(&mut d, 1); // c = 1, so (c,d) is nonzero regardless of d

    // Positive control: `c = 0` is FALSE — the kernel refuses it.
    let zero_r = rzero(&mut d, p);
    let claim_c_zero = req(&mut d, c, zero_r);
    let proof_c_zero = rrefl(&mut d, zero_r);
    let name_c_zero = d.kernel().name_str(anon, "Check.c_equals_zero_is_false");
    let refused_c_zero = d.kernel().add_declaration(Declaration::Theorem {
        name: name_c_zero,
        uparams: vec![],
        ty: claim_c_zero,
        value: proof_c_zero,
    });
    assert!(
        refused_c_zero.is_err(),
        "the kernel accepted c = 0 with c the literal 1 (1 = 0): {refused_c_zero:?}"
    );

    // For an ARBITRARY (symbolic) t, t*a = 0, since a = 0. Not a case split
    // on t, not a computation on t — `Rat.mul_zero` applied once, generic in
    // t, exactly the fact the naive existential's first conjunct `c = t*a`
    // would need to equal `c = 0` for.
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let ta = rmul(&mut d, t, a);
    let mul_zero_t = d.lemma(p.mul_zero, &[t]); // t*a = 0 (a is literally Rat.zero here)
    let ta_eq_zero_ty = req(&mut d, ta, zero_r);
    let name_ta_zero = d
        .kernel()
        .name_str(anon, "Check.t_times_a_is_zero_for_any_t");
    let carrier = rat_ty(&mut d);
    let ta_zero_ty_pi = d.pi_fv(t_fv, carrier, ta_eq_zero_ty);
    let ta_zero_val = d.lam_fv(t_fv, carrier, mul_zero_t);
    let accepted_ta_zero = d.kernel().add_declaration(Declaration::Theorem {
        name: name_ta_zero,
        uparams: vec![],
        ty: ta_zero_ty_pi,
        value: ta_zero_val,
    });
    assert!(
        accepted_ta_zero.is_ok(),
        "∀ t, t*a = 0 must hold generically when a = 0: {accepted_ta_zero:?}"
    );

    // So `c = t*a` would force `c = 0` for whichever `t` was proposed, and
    // `c = 0` is already refused above: no `t` (symbolic or literal) makes
    // the naive existential's first conjunct hold at this instance.
    let would_force_c_zero = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let c_eq_ta_ty = req(&mut d, c, ta);
        let chained = rtrans(&mut d, c, ta, zero_r, heq, mul_zero_t);
        d.lam_fv(heq_fv, c_eq_ta_ty, chained)
    };
    let _ = would_force_c_zero; // typechecks: (c = t*a) -> (c = 0), for the fresh t above
}

/// `Rat.cramer2_solves`'s statement, asserted verbatim — same discipline as
/// [`cramer_two_unique_x_is_the_stated_forward_direction`]: this is the
/// SUBSTITUTION direction (the `cramer2_x`/`cramer2_y` formulas actually
/// satisfy both equations of the system), bundled as an `And` of the two
/// equations, never a bare existence claim about one variable.
#[test]
fn cramer2_solves_is_the_stated_substitution_direction() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cramer2_solves)
        .expect("declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat) -> ((x6 : Not (Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)) -> \
         And (Eq.{1} Rat (Rat.add (Rat.mul x0 (Rat.cramer2_x x0 x1 x2 x3 x4 x5)) \
         (Rat.mul x1 (Rat.cramer2_y x0 x1 x2 x3 x4 x5))) x4) \
         (Eq.{1} Rat (Rat.add (Rat.mul x2 (Rat.cramer2_x x0 x1 x2 x3 x4 x5)) \
         (Rat.mul x3 (Rat.cramer2_y x0 x1 x2 x3 x4 x5))) x5))))))))"
    );
}

/// `Rat.cramer2_x`/`Rat.cramer2_y` at an explicit 2×2 system, checked by pure
/// REDUCTION (`Eq.refl`) — not merely that `Rat.cramer2_solves` type-checks,
/// which would be true of a vacuous or mis-stated theorem too.
///
/// System `2x+y=5, x+y=3` (`a=2,b=1,c=1,d=1`, `D = 2·1−1·1 = 1`): the unique
/// solution is `x=2, y=1`. `D=1` keeps the positivity witness this test needs
/// (`Rat.nat_div_succ_pos` at `Nat.le 1 1`, i.e. `Nat.le_refl`) a one-liner;
/// `Rat.cramer2_solves` itself carries no such restriction on `D`. Also
/// exercises `Rat.cramer2_solves` applied at this concrete instance, checking
/// the kernel accepts discharging its `D ≠ 0` hypothesis here.
#[test]
fn cramer2_solves_computes_an_explicit_two_by_two_system() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, req, rlt, rmul, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 2);
    let b = literal(&mut d, 1);
    let c = literal(&mut d, 1);
    let dd = literal(&mut d, 1);
    let u = literal(&mut d, 5);
    let v = literal(&mut d, 3);

    // D ≠ 0, derived from 0 < D: D = det2 2 1 1 1 reduces to natDivSucc 1 0,
    // and `nat_div_succ_pos` gives 0 < natDivSucc 1 0 directly (Nat.le 1 1 is
    // `Nat.le_refl`). Same "assume Eq, rewrite the positivity witness along
    // it, refute by lt_irrefl" route `Rat.ne_zero_of_pos` (private to
    // probability.rs) uses.
    let det = d.const_app(p.det2, &[a, b, c, dd]);
    let zero_r = rzero(&mut d, p);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let le_pf = d.lemma(p.int.nat.le_refl, &[one_nat]); // Nat.le 1 1
    let pos = d.lemma(p.nat_div_succ_pos, &[one_nat, zero_nat, le_pf]); // 0 < natDivSucc 1 0, defeq 0 < det
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let eq_ty = req(&mut d, det, zero_r);
    let rewritten = rat_eq_rewrite(&mut d, det, zero_r, heq, pos, &|d, t| rlt(d, p, zero_r, t));
    let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
    let false_proof = d.apply(irrefl, &[rewritten]);
    let h3 = d.lam_fv(heq_fv, eq_ty, false_proof); // Not (Eq Rat det Rat.zero)

    // The formulas compute to the right rationals, by pure reduction.
    let x_val = d.const_app(p.cramer2_x, &[a, b, c, dd, u, v]);
    let two = literal(&mut d, 2);
    let claim_x = req(&mut d, x_val, two);
    let proof_x = rrefl(&mut d, two);
    let name_x = d.kernel().name_str(anon, "Check.cramer2_x_value");
    let accepted_x = d.kernel().add_declaration(Declaration::Theorem {
        name: name_x,
        uparams: vec![],
        ty: claim_x,
        value: proof_x,
    });
    assert!(
        accepted_x.is_ok(),
        "cramer2_x 2 1 1 1 5 3 must REDUCE to 2: {accepted_x:?}"
    );

    let y_val = d.const_app(p.cramer2_y, &[a, b, c, dd, u, v]);
    let one = literal(&mut d, 1);
    let claim_y = req(&mut d, y_val, one);
    let proof_y = rrefl(&mut d, one);
    let name_y = d.kernel().name_str(anon, "Check.cramer2_y_value");
    let accepted_y = d.kernel().add_declaration(Declaration::Theorem {
        name: name_y,
        uparams: vec![],
        ty: claim_y,
        value: proof_y,
    });
    assert!(
        accepted_y.is_ok(),
        "cramer2_y 2 1 1 1 5 3 must REDUCE to 1: {accepted_y:?}"
    );

    // The theorem itself, applied at this concrete instance: both equations
    // hold of the values just computed.
    let solved = d.lemma(p.cramer2_solves, &[a, b, c, dd, u, v, h3]);
    let ax = rmul(&mut d, a, x_val);
    let by = rmul(&mut d, b, y_val);
    let ax_by = radd(&mut d, ax, by);
    let eq1 = req(&mut d, ax_by, u);
    let cx = rmul(&mut d, c, x_val);
    let dy = rmul(&mut d, dd, y_val);
    let cx_dy = radd(&mut d, cx, dy);
    let eq2 = req(&mut d, cx_dy, v);
    let expected = d.and(eq1, eq2);
    let name_s = d.kernel().name_str(anon, "Check.cramer2_solves_instance");
    let accepted_s = d.kernel().add_declaration(Declaration::Theorem {
        name: name_s,
        uparams: vec![],
        ty: expected,
        value: solved,
    });
    assert!(
        accepted_s.is_ok(),
        "cramer2_solves 2 1 1 1 5 3 h3 must discharge both equations of the \
         system it claims to solve: {accepted_s:?}"
    );
}

/// The negative control [`cramer2_solves_computes_an_explicit_two_by_two_system`]
/// needs: at a SINGULAR instance (`D = 0`), the unrestricted claim
/// `a·cramer2_x+b·cramer2_y = u` is not merely unprovable, it is FALSE —
/// exactly the mistake `Rat.inv`'s totality (`inv 0 = 0`) invites, since
/// `cramer2_x`/`cramer2_y` are still total there and silently evaluate to `0`.
///
/// System `x+y=1, x+y=2` (`a=b=c=d=1`, `D = 1·1−1·1 = 0`) has no solution at
/// all (the two equations contradict each other), so `u=1` is as good a
/// target as any: `cramer2_x`/`cramer2_y` both reduce to `0` (numerator times
/// `inv 0 = 0`), so `a·cramer2_x+b·cramer2_y` reduces to `0`, not `1`. Checked
/// both ways — the TRUE value (`0`) is accepted by `Eq.refl`, and the
/// unrestricted claim (`= u = 1`) is REFUSED — so this is a check on the
/// value, not a tool that cannot fail.
#[test]
fn cramer2_solves_needs_its_hypothesis_the_unrestricted_claim_is_false_at_d_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 1);
    let b = literal(&mut d, 1);
    let c = literal(&mut d, 1);
    let dd = literal(&mut d, 1);
    let u = literal(&mut d, 1);
    let v = literal(&mut d, 2);

    let x_val = d.const_app(p.cramer2_x, &[a, b, c, dd, u, v]);
    let y_val = d.const_app(p.cramer2_y, &[a, b, c, dd, u, v]);
    let ax = rmul(&mut d, a, x_val);
    let by = rmul(&mut d, b, y_val);
    let lhs = radd(&mut d, ax, by);

    let zero = literal(&mut d, 0);
    let claim_true = req(&mut d, lhs, zero);
    let proof_true = rrefl(&mut d, zero);
    let name_true = d.kernel().name_str(anon, "Check.cramer2_at_d_zero_is_zero");
    let accepted_true = d.kernel().add_declaration(Declaration::Theorem {
        name: name_true,
        uparams: vec![],
        ty: claim_true,
        value: proof_true,
    });
    assert!(
        accepted_true.is_ok(),
        "at D=0, a*cramer2_x+b*cramer2_y must REDUCE to 0 (Rat.inv 0 = 0): {accepted_true:?}"
    );

    let claim_false = req(&mut d, lhs, u);
    let proof_false = rrefl(&mut d, u);
    let name_false = d
        .kernel()
        .name_str(anon, "Check.cramer2_at_d_zero_equals_u");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name: name_false,
        uparams: vec![],
        ty: claim_false,
        value: proof_false,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted a*cramer2_x+b*cramer2_y = u at D=0 (0 = 1), so \
         dropping the D ≠ 0 hypothesis would not merely be unprovable, it \
         would be FALSE, and this reduction check caught neither: {refused:?}"
    );
}

/// `Rat.det2_fib`'s statement, asserted verbatim — an empty axiom footprint
/// on a theorem *named* `det2_fib` says nothing about which statement it
/// proves; this checks it is genuinely Cassini's identity read through
/// `det2`, cast into `ℚ` by `ofInt`, and not some vacuous or mismatched
/// restatement.
#[test]
fn det2_fib_is_cassini_through_det2() {
    let (kernel, p) = built();
    let ty = match kernel.environment().get(p.det2_fib).expect("declared") {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : AxNat) -> Eq.{1} Rat (Rat.det2 \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ (AxNat.succ x0))))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ x0)))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ x0)))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib x0)))) \
         (Rat.ofInt (Int.pow (Int.neg Int.one) (AxNat.succ x0))))"
    );
}

/// `Rat.inv2_top_left`'s statement, asserted verbatim — the same discipline
/// [`the_rationals_are_a_field_and_the_inverse_is_positive`] applies to
/// `mul_inv_cancel`: an empty axiom footprint on a theorem *named*
/// `inv2_top_left` says nothing about which statement it proves.
#[test]
fn inv2_top_left_is_the_stated_entry_of_a_inverse_a() {
    let (kernel, p) = built();
    let ty = match kernel.environment().get(p.inv2_top_left).expect("declared") {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         ((x4 : Not (Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)) -> \
         Eq.{1} Rat (Rat.add (Rat.mul (Rat.mul (Rat.inv (Rat.det2 x0 x1 x2 x3)) x3) x0) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.det2 x0 x1 x2 x3)) (Rat.neg x1)) x2)) Rat.one)))))"
    );
}

/// `Rat.cramer_two_unique_x`'s statement, asserted verbatim — same discipline
/// as [`inv2_top_left_is_the_stated_entry_of_a_inverse_a`]: an empty axiom
/// footprint on a theorem named `cramer_two_unique_x` says nothing about
/// which statement it proves, and this is the FORWARD direction only (a
/// solution must have this form), never a bare existence claim.
#[test]
fn cramer_two_unique_x_is_the_stated_forward_direction() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cramer_two_unique_x)
        .expect("declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat) -> ((x6 : Rat) -> ((x7 : Rat) -> \
         ((x8 : Eq.{1} Rat (Rat.add (Rat.mul x0 x4) (Rat.mul x1 x5)) x6) -> \
         ((x9 : Eq.{1} Rat (Rat.add (Rat.mul x2 x4) (Rat.mul x3 x5)) x7) -> \
         ((x10 : Not (Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)) -> \
         Eq.{1} Rat x4 (Rat.div (Rat.det2 x6 x1 x7 x3) (Rat.det2 x0 x1 x2 x3)))))))))))))"
    );
}

/// ℚ is a model of the whole `Real` axiom package: every one of the 30
/// declarations is either an interpreted symbol or a law with a
/// kernel-checked, axiom-free witness.
#[test]
fn rationals_model_the_real_axioms() {
    let mut kernel = Kernel::new();
    let model = crate::build_rat_model_of_arith(&mut kernel).expect("ℚ must model the Real axioms");
    assert_eq!(model.laws.len(), 22);
    assert_eq!(model.symbols.len(), 8);
    for law in &model.laws {
        let footprint: Vec<String> = kernel
            .axiom_footprint(law.witness)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        let rendered = kernel.display_name(law.real).to_string();
        assert!(
            footprint.is_empty(),
            "the ℚ witness for {rendered} rests on {footprint:?}"
        );
    }
    // Completeness: no `Real` declaration escapes the interpretation.
    let interpreted: std::collections::HashSet<_> = model
        .symbols
        .iter()
        .map(|(real, _)| *real)
        .chain(model.laws.iter().map(|law| law.real))
        .collect();
    let missed: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => Some(*name),
            _ => None,
        })
        .filter(|name| !interpreted.contains(name))
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        missed.is_empty(),
        "these AxReal declarations have no ℚ interpretation: {missed:?}"
    );
}

// --- the Archimedean property (ADR-0512 phase R1) ---------------------------

/// Every declaration the Archimedean development adds is a **checked** theorem
/// (or definition) with an empty axiom footprint — read out of the kernel, not
/// off the diff.
#[test]
fn the_archimedean_development_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("natDivSucc", p.nat_div_succ, false),
        ("int_le_or_lt", p.int_le_or_lt, true),
        ("le_or_lt", p.le_or_lt, true),
        ("int_pos_of_pos", p.int_pos_of_pos, true),
        ("int_one_le_of_pos", p.int_one_le_of_pos, true),
        ("natDivSucc_lt_of_pos", p.nat_div_succ_lt_of_pos, true),
        ("le_of_le_add_natDivSucc", p.le_of_le_add_nat_div_succ, true),
        ("natDivSucc_antitone", p.nat_div_succ_antitone, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.natDivSucc_antitone` is antitonicity **exactly as briefed**: the
/// hypothesis is `Nat.le j j'` (not a fixed pair, not `Nat.lt`), and the
/// conclusion swaps `j`/`j'` on `Rat.natDivSucc 1 _` — the wider index gives
/// the smaller bound — rather than leaving the direction to an empty
/// footprint's word.
#[test]
fn nat_div_succ_antitone_is_the_statement_briefed() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.nat_div_succ_antitone)
        .expect("Rat.natDivSucc_antitone must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.natDivSucc_antitone must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat.le x0 x1) -> \
         Rat.le (Rat.natDivSucc (AxNat.succ AxNat.zero) x1) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) x0))))",
        "Rat.natDivSucc_antitone's statement drifted from the briefed one"
    );
}

/// The Archimedean statement is the one ADR-0512 asks for, **verbatim**.
///
/// A footprint of `[]` on a theorem that says something weaker than intended is
/// the failure mode this repository keeps hitting, so this asserts the rendered
/// type rather than the declaration's existence: the hypothesis has to be
/// universally quantified over the index (`∀ j`, not one fixed `j`), the bound
/// has to be `Rat.natDivSucc k j` under that quantifier, and the conclusion has
/// to be the *unweakened* `Rat.le a b`.
#[test]
fn the_archimedean_statement_is_the_one_adr_0468_needs() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.le_of_le_add_nat_div_succ)
        .expect("the Archimedean property must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("the Archimedean property must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : AxNat) -> \
         ((x3 : ((x3 : AxNat) -> Rat.le x0 (Rat.add x1 (Rat.natDivSucc x2 x3)))) -> \
         Rat.le x0 x1))))",
        "the Archimedean statement drifted from ADR-0512's"
    );
}

/// `Rat.natDivSucc k j` really is the rational `k/(j+1)` **in lowest terms**,
/// checked by the kernel's own reduction (`Eq.refl` only typechecks if the two
/// sides are definitionally equal).
///
/// This is the guard that stops the Archimedean property being vacuous. A
/// `natDivSucc` that collapsed to `0` — or that never renormalised — would leave
/// every theorem above provable and every one of them worthless, and neither an
/// empty footprint nor the rendered statement would notice. `6/(1+1)` is chosen
/// because it exercises the `gcd` reduction: the answer is `3/1`, not `6/2`.
///
/// **Measured 2026-08-18, so the redundancy is stated rather than assumed.**
/// Mutating the development to `k/(j+2)` — consistently, in both the definition
/// and the witness proof — does not reach this test: the *kernel* refuses the
/// witness lemma first, because `Int.lt (ofNat (k·q)) (ofNat (k·q+2))` is no
/// longer `Nat.le_refl`, and all ten tests in this module die on the build. So
/// today `Rat.natDivSucc`'s meaning is pinned by the proofs that consume it, and
/// this test is defence for the refactor that re-proves the witness lemma some
/// other way and no longer pins it. Its own discriminating power is measured by
/// [`nat_div_succ_reduction_check_can_fail`], which requires the kernel to
/// **reject** a wrong numerator through the same `Eq.refl` route.
#[test]
fn nat_div_succ_computes_the_reduced_fraction() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `Rat.num (Rat.natDivSucc 6 1) = Int.ofNat 3` and `Rat.den … = 1`.
    let cases: [(&str, u32, u32, u32, u32); 3] = [
        ("six_halves", 6, 1, 3, 1),
        ("one_quarter", 1, 3, 1, 4),
        ("four_sixths", 4, 5, 2, 3),
    ];
    for (label, k, j, expected_num, expected_den) in cases {
        let numerator_arg = d.num(k);
        let index = d.num(j);
        let value = d.const_app(p.nat_div_succ, &[numerator_arg, index]);

        let actual_num = super::ops::num(&mut d, value);
        let wanted = d.num(expected_num);
        let wanted_num = d.of_nat(wanted);
        let num_stmt = d.ieq(actual_num, wanted_num);
        let num_proof = d.irefl(actual_num);
        let num_name = d.kernel().name_str(anon, format!("Check.num_{label}"));
        d.declare_theorem(num_name, num_stmt, num_proof)
            .unwrap_or_else(|e| {
                panic!("Rat.natDivSucc {k} {j} did not reduce to numerator {expected_num}: {e:?}")
            });

        let actual_den = super::ops::den(&mut d, value);
        let wanted_den = d.num(expected_den);
        let den_stmt = NatOps::eq(&mut d, actual_den, wanted_den);
        let den_proof = NatOps::refl(&mut d, actual_den);
        let den_name = d.kernel().name_str(anon, format!("Check.den_{label}"));
        d.declare_theorem(den_name, den_stmt, den_proof)
            .unwrap_or_else(|e| {
                panic!("Rat.natDivSucc {k} {j} did not reduce to denominator {expected_den}: {e:?}")
            });
    }
}

/// The negative control for
/// [`nat_div_succ_computes_the_reduced_fraction`]: the same `Eq.refl` route,
/// pointed at a value `Rat.natDivSucc` does **not** take.
///
/// Without this, a kernel whose conversion checker accepted anything would make
/// the test above pass while measuring nothing. `6/(1+1)` is `3/1`, so asking it
/// to be `6/1` must be **refused**.
#[test]
fn nat_div_succ_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let six = d.num(6);
    let one = d.num(1);
    let value = d.const_app(p.nat_div_succ, &[six, one]);
    let actual_num = super::ops::num(&mut d, value);
    let wrong = d.num(6);
    let wrong_num = d.of_nat(wrong);
    let stmt = d.ieq(actual_num, wrong_num);
    let proof = d.irefl(actual_num);
    let name = d.kernel().name_str(anon, "Check.wrong_numerator");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.num (Rat.natDivSucc 6 1) = Int.ofNat 6`, \
         so the reduction check above proves nothing"
    );
}

/// The two `natDivSucc` lemmas `CReal.mul` will need, stated verbatim — and the
/// proof that the first genuinely **subsumes** `natDivSucc_halve` rather than
/// merely resembling it.
///
/// `natDivSucc_halve` is the `c = 1` instance *definitionally*: `Nat.add x
/// (succ y)` reduces to `succ (Nat.add x y)`, so `(1+1)·m + 1` is `succ (2·m)`
/// and `natDivSucc_scale 1` type-checks at `natDivSucc_halve`'s statement. The
/// kernel is asked to confirm that, because "the general lemma covers the
/// special case" is exactly the kind of claim that is usually asserted in a doc
/// comment and never checked.
#[test]
fn nat_div_succ_scale_subsumes_halve_and_is_monotone_in_the_numerator() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let render = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        render(&mut kernel, p.nat_div_succ_scale),
        "((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} Rat \
         (Rat.natDivSucc (AxNat.succ x0) (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) x1)))"
    );
    assert_eq!(
        render(&mut kernel, p.nat_div_succ_le_add_left),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Rat.le (Rat.natDivSucc x0 x2) (Rat.natDivSucc (AxNat.add x0 x1) x2))))"
    );

    // `natDivSucc_scale 1 m : natDivSucc 2 (2·m + 1) = natDivSucc 1 m`, which is
    // `natDivSucc_halve`'s statement. Admitting it proves the subsumption.
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let doubled = NatOps::mul(&mut d, two_nat, m);
    let shifted = d.succ(doubled);
    let left = d.const_app(p.nat_div_succ, &[two_nat, shifted]);
    let right = d.const_app(p.nat_div_succ, &[one_nat, m]);
    let stmt = crate::rat_prelude::ops::req(&mut d, left, right);
    let instance = d.lemma(p.nat_div_succ_scale, &[one_nat, m]);
    let nat = d.nat_ty();
    let ty = d.pi_fv(m_fv, nat, stmt);
    let value = d.lam_fv(m_fv, nat, instance);
    let name = d.kernel().name_str(anon, "Check.halve_from_scale");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "natDivSucc_scale at c = 1 must BE natDivSucc_halve — it did not \
         type-check, so the generalisation does not subsume the special case: \
         {admitted:?}"
    );
}

/// The multiplicative toolkit says what `CReal.mul` needs it to say.
///
/// Rendered verbatim, because an empty axiom footprint on a *weaker* statement
/// is this repository's standing failure mode and the product estimate is
/// exactly where a silently weakened bound would not be noticed: every one of
/// these is consumed inside a proof whose conclusion is checked only for
/// well-typedness.
#[test]
fn the_product_toolkit_has_the_statements_creal_mul_needs() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.mul_sub_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         Eq.{1} Rat (Rat.sub (Rat.mul x0 x1) (Rat.mul x2 x3)) \
         (Rat.add (Rat.mul x0 (Rat.sub x1 x3)) (Rat.mul (Rat.sub x0 x2) x3))))))"
    );
    // `bounds_mul` must bound the product by the product of the two bounds —
    // NOT by one of them, and not one-sidedly.
    assert_eq!(
        rendered(&mut kernel, p.bounds_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         ((x4 : Rat.le Rat.zero x1) -> ((x5 : Rat.le (Rat.neg x1) x0) -> \
         ((x6 : Rat.le x0 x1) -> ((x7 : Rat.le (Rat.neg x3) x2) -> \
         ((x8 : Rat.le x2 x3) -> \
         And (Rat.le (Rat.neg (Rat.mul x1 x3)) (Rat.mul x0 x2)) \
         (Rat.le (Rat.mul x0 x2) (Rat.mul x1 x3)))))))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_mul),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Eq.{1} Rat (Rat.mul (Rat.natDivSucc x0 AxNat.zero) (Rat.natDivSucc x1 x2)) \
         (Rat.natDivSucc (AxNat.mul x0 x1) x2))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_le_one),
        "((x0 : AxNat) -> Rat.le (Rat.natDivSucc (AxNat.succ AxNat.zero) x0) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) AxNat.zero))"
    );
    // The two that make nested sampling indices reducible. `nat_index_compose`
    // must say the COMPOSED index is a product index in `n` — a statement that
    // merely related the two shifts would be true and useless.
    assert_eq!(
        rendered(&mut kernel, p.nat_index_compose),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Eq.{1} AxNat \
         (AxNat.add (AxNat.mul (AxNat.succ x0) \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x2) x1)) x0) \
         (AxNat.add (AxNat.mul (AxNat.succ \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)) x2) \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_le_scaled),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Rat.le (Rat.natDivSucc x0 \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x2) x1)) \
         (Rat.natDivSucc x0 x2))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.bounds_num),
        "((x0 : Rat) -> \
         And (Rat.le (Rat.neg (Rat.natDivSucc (Int.natAbs (Rat.num x0)) AxNat.zero)) x0) \
         (Rat.le x0 (Rat.natDivSucc (Int.natAbs (Rat.num x0)) AxNat.zero)))"
    );
}

/// Every new multiplicative lemma is a **checked theorem** with an empty axiom
/// footprint.
#[test]
fn the_product_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let laws = [
        p.mul_neg,
        p.neg_mul,
        p.mul_le_mul_of_nonneg_right,
        p.mul_sub_mul,
        p.bounds_mul,
        p.neg_mul_le_of_bounds,
        p.nat_div_succ_mul,
        p.nat_div_succ_le_one,
        p.nat_div_succ_le_scaled,
        p.nat_index_compose,
        p.int_le_nat_abs,
        p.int_neg_nat_abs_le,
        p.bounds_num,
    ];
    for law in laws {
        let label = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("{label} is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{label} must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}

/// **`Rat.IsField`, and every leaf is asserted verbatim** — the curriculum
/// target (`fields.md`): a bundled `Prop` predicate in the
/// `nat_prelude::group::Nat.IsGroupOn` house style, with `Rat.rat_isField` the
/// worked instance and `Rat.mul_left_cancel_of_ne_zero` the consequence a
/// field gives that a ring does not.
#[test]
fn the_rationals_satisfy_is_field_and_cancel() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };

    assert_eq!(
        rendered(&mut kernel, p.one_ne_zero),
        "Not (Eq.{1} Rat Rat.one Rat.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.is_field),
        "((x0 : ((x0 : Rat) -> ((x1 : Rat) -> Rat))) -> ((x1 : ((x1 : Rat) -> \
         ((x2 : Rat) -> Rat))) -> ((x2 : ((x2 : Rat) -> Rat)) -> ((x3 : ((x3 : \
         Rat) -> Rat)) -> ((x4 : Rat) -> ((x5 : Rat) -> Prop))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.rat_is_field),
        "Rat.IsField Rat.add Rat.mul Rat.neg Rat.inv Rat.zero Rat.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_left_cancel_of_ne_zero),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Not (Eq.{1} Rat x0 \
         Rat.zero)) -> ((x4 : Eq.{1} Rat (Rat.mul x0 x1) (Rat.mul x0 x2)) -> \
         Eq.{1} Rat x1 x2)))))"
    );

    for (label, name, expect_definition) in [
        ("one_ne_zero", p.one_ne_zero, false),
        ("IsField", p.is_field, true),
        ("rat_isField", p.rat_is_field, false),
        (
            "mul_left_cancel_of_ne_zero",
            p.mul_left_cancel_of_ne_zero,
            false,
        ),
    ] {
        let decl = kernel.environment().get(name);
        if expect_definition {
            assert!(
                matches!(decl, Some(Declaration::Definition { .. })),
                "Rat.{label} must be a checked Definition"
            );
        } else {
            assert!(
                matches!(decl, Some(Declaration::Theorem { .. })),
                "Rat.{label} must be a checked Theorem"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **`Rat.IsOrderedField`, and every leaf is asserted verbatim** — `IsField`
/// extended with the two order axioms of an ordered field, COMPOSED rather
/// than restated: `Rat.rat_isOrderedField`'s field component is
/// `Rat.rat_isField` itself, not a re-derivation of the ten field leaves.
#[test]
fn the_rationals_satisfy_is_ordered_field() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };

    assert_eq!(
        rendered(&mut kernel, p.rat_is_ordered_field),
        "Rat.IsOrderedField Rat.add Rat.mul Rat.neg Rat.inv Rat.zero Rat.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.is_ordered_field),
        "((x0 : ((x0 : Rat) -> ((x1 : Rat) -> Rat))) -> ((x1 : ((x1 : Rat) -> \
         ((x2 : Rat) -> Rat))) -> ((x2 : ((x2 : Rat) -> Rat)) -> ((x3 : ((x3 : \
         Rat) -> Rat)) -> ((x4 : Rat) -> ((x5 : Rat) -> Prop))))))"
    );

    for (label, name, expect_definition) in [
        ("IsOrderedField", p.is_ordered_field, true),
        ("rat_isOrderedField", p.rat_is_ordered_field, false),
    ] {
        let decl = kernel.environment().get(name);
        if expect_definition {
            assert!(
                matches!(decl, Some(Declaration::Definition { .. })),
                "Rat.{label} must be a checked Definition"
            );
        } else {
            assert!(
                matches!(decl, Some(Declaration::Theorem { .. })),
                "Rat.{label} must be a checked Theorem"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **The two order axioms compute at `0` and `1`, and the kernel refuses the
/// UNRESTRICTED closure of the nonnegatives (`∀ a b, 0 ≤ a·b`, both
/// hypotheses dropped) built by reusing `Rat.mul_nonneg`'s own constant.**
///
/// This is the negative control `Rat.mul_nonneg`'s two hypotheses exist to
/// rule out, and — like the previous lane's `mul_inv_cancel` control — the
/// unrestricted claim is genuinely FALSE, not merely under-justified:
/// `1·(-1) = -1`, and `0 ≤ -1` does not hold.
#[test]
fn order_axioms_compute_at_zero_and_one_and_reject_the_unrestricted_closure() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_ty, rle, rmul, rone, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let zero = rzero(&mut d, p);
    let one = rone(&mut d, p);

    // Translation invariance at `x=0, y=1, z=1`: `0 ≤ 1 → 0+1 ≤ 1+1`.
    let zero_lt_one = d.lemma(p.zero_lt_one, &[]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zero_lt_one]);
    let refl_one = d.lemma(p.le_refl, &[one]);
    let translation_step = d.lemma(p.add_le_add, &[zero, one, one, one, zero_le_one, refl_one]);
    let zero_plus_one = radd(&mut d, zero, one);
    let one_plus_one = radd(&mut d, one, one);
    let translation_claim = rle(&mut d, p, zero_plus_one, one_plus_one);
    let translation_name = d.kernel().name_str(anon, "Check.translation_at_zero_one");
    let translation_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: translation_name,
        uparams: vec![],
        ty: translation_claim,
        value: translation_step,
    });
    assert!(
        translation_accepted.is_ok(),
        "translation invariance must compute at 0,1,1: {translation_accepted:?}"
    );

    // Closure of the nonnegatives at `a=1, b=1`: `0 ≤ 1 → 0 ≤ 1 → 0 ≤ 1·1`.
    let mul_nonneg_step = d.lemma(p.mul_nonneg, &[one, one, zero_le_one, zero_le_one]);
    let one_times_one = rmul(&mut d, one, one);
    let mul_nonneg_claim = rle(&mut d, p, zero, one_times_one);
    let mul_nonneg_name = d.kernel().name_str(anon, "Check.mul_nonneg_at_one_one");
    let mul_nonneg_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: mul_nonneg_name,
        uparams: vec![],
        ty: mul_nonneg_claim,
        value: mul_nonneg_step,
    });
    assert!(
        mul_nonneg_accepted.is_ok(),
        "closure of the nonnegatives must compute at 1,1: {mul_nonneg_accepted:?}"
    );

    // NEGATIVE CONTROL: `∀ a b, 0 ≤ a·b`, UNRESTRICTED — false at `a=1,
    // b=-1`. Reuse `Rat.mul_nonneg`'s own constant, applied to just `a, b`
    // (no nonnegativity proofs supplied) — its type is `le 0 a -> le 0 b ->
    // le 0 (a*b)`, not the bare `le 0 (a*b)` the unrestricted statement
    // needs, so the kernel must refuse.
    let carrier = rat_ty(&mut d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ab = rmul(&mut d, a, b);
    let bad_concl = rle(&mut d, p, zero, ab);
    let with_b_ty = d.pi_fv(b_fv, carrier, bad_concl);
    let bad_ty = d.pi_fv(a_fv, carrier, with_b_ty);

    let mul_nonneg_const = d.kernel().const_(p.mul_nonneg, vec![]);
    let bad_body = d.apply(mul_nonneg_const, &[a, b]); // : le 0 a -> le 0 b -> le 0 (a*b)
    let with_b_val = d.lam_fv(b_fv, carrier, bad_body);
    let bad_value = d.lam_fv(a_fv, carrier, with_b_val);

    let bad_name = d.kernel().name_str(anon, "Check.unrestricted_mul_nonneg");
    let bad_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: bad_value,
    });
    assert!(
        bad_accepted.is_err(),
        "the kernel accepted `∀ a b, 0 ≤ a·b` UNRESTRICTED — both \
         nonnegativity hypotheses were refused as if they were vacuous: \
         {bad_accepted:?}"
    );
}

/// **The field laws compute at an explicit rational, and the kernel refuses
/// the unrestricted `x·x⁻¹ = 1` when it is asked to reuse the real proof
/// without the `x ≠ 0` hypothesis.**
///
/// `Rat.inv`'s totality (`inv 0 = 0`) is exactly what makes `mul_inv_cancel`
/// need a hypothesis at all; the negative control here is the mistake that
/// hypothesis exists to rule out.
#[test]
fn field_laws_compute_at_one_half_and_reject_the_unrestricted_inverse() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_eq_rewrite, req, rlt, rmul, rone, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `1/2`, as `Rat.natDivSucc 1 1`, and its positivity (`1 ≤ 1`).
    let one_nat = d.num(1);
    let half = d.const_app(p.nat_div_succ, &[one_nat, one_nat]);
    let one_le_one = d.lemma(p.int.nat.le_refl, &[one_nat]);
    let half_pos = d.lemma(p.nat_div_succ_pos, &[one_nat, one_nat, one_le_one]); // 0 < 1/2

    // `1/2 ≠ 0`, by the same rewrite-to-`lt_irrefl` route as `Rat.one_ne_zero`.
    let zero = rzero(&mut d, p);
    let half_eq_zero = req(&mut d, half, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let rewritten = rat_eq_rewrite(&mut d, half, zero, h, half_pos, &|d, t| rlt(d, p, zero, t));
    let refuted = d.lemma(p.lt_irrefl, &[zero]);
    let false_proof = d.apply(refuted, &[rewritten]);
    let half_ne_zero = d.lam_fv(h_fv, half_eq_zero, false_proof);

    // Computation: `(1/2)⁻¹` REDUCES to `2/1` — `Eq.refl` alone must check.
    let two_nat = d.num(2);
    let zero_nat = d.zero();
    let doubled = d.const_app(p.nat_div_succ, &[two_nat, zero_nat]); // 2/1
    let reciprocal = d.const_app(p.inv, &[half]);
    let inv_computes = req(&mut d, reciprocal, doubled);
    let inv_proof = rrefl(&mut d, doubled);
    let inv_name = d.kernel().name_str(anon, "Check.half_inv_computes");
    let inv_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: inv_name,
        uparams: vec![],
        ty: inv_computes,
        value: inv_proof,
    });
    assert!(
        inv_accepted.is_ok(),
        "`(1/2)⁻¹` must REDUCE to `2/1`: {inv_accepted:?}"
    );

    // The field law itself, applied at this concrete `1/2`: `(1/2)·(1/2)⁻¹ = 1`.
    let one = rone(&mut d, p);
    let product = rmul(&mut d, half, reciprocal);
    let law_claim = req(&mut d, product, one);
    let law_proof = d.lemma(p.mul_inv_cancel_of_ne_zero, &[half, half_ne_zero]);
    let law_name = d.kernel().name_str(anon, "Check.half_mul_inv_cancel");
    let law_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: law_name,
        uparams: vec![],
        ty: law_claim,
        value: law_proof,
    });
    assert!(
        law_accepted.is_ok(),
        "the field law must apply at `1/2`: {law_accepted:?}"
    );

    // NEGATIVE CONTROL: `∀ x, mul x (inv x) = one`, UNRESTRICTED — false at
    // `x = 0` (`Rat.inv Rat.zero = Rat.zero`, so the claim there is `0 = 1`).
    // Reuse `Rat.mul_inv_cancel_of_ne_zero`'s own constant, applied to just
    // `x` (no `x ≠ 0` proof supplied) — its type is `Not (x=0) -> …`, not the
    // bare `Eq` the unrestricted statement needs, so the kernel must refuse.
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let one2 = rone(&mut d, p);
    let ix = d.const_app(p.inv, &[x]);
    let bad_product = rmul(&mut d, x, ix);
    let bad_concl = req(&mut d, bad_product, one2);
    let bad_ty = d.pi_fv(x_fv, carrier, bad_concl);

    let real_const = d.kernel().const_(p.mul_inv_cancel_of_ne_zero, vec![]);
    let bad_body = d.apply(real_const, &[x]); // : Not (x=0) -> mul x (inv x) = one
    let bad_value = d.lam_fv(x_fv, carrier, bad_body);
    let bad_name = d.kernel().name_str(anon, "Check.unrestricted_inv_cancel");
    let bad_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: bad_value,
    });
    assert!(
        bad_accepted.is_err(),
        "the kernel accepted `∀ x, x·x⁻¹ = 1` UNRESTRICTED — the `x ≠ 0` \
         hypothesis was refused as if it were vacuous: {bad_accepted:?}"
    );
}

/// **ℚ is a field, and the statement is asserted verbatim.**
///
/// `Rat.inv` was a definition with no law about it for the whole life of this
/// prelude; an empty footprint on a theorem *named* `mul_inv_cancel` says
/// nothing, so the rendered type is the assertion. `Rat.div` is `a · b⁻¹`, so
/// this is also the first law division has.
#[test]
fn the_rationals_are_a_field_and_the_inverse_is_positive() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_pos),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> Rat.lt Rat.zero (Rat.inv x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel_of_neg),
        "((x0 : Rat) -> ((x1 : Rat.lt x0 Rat.zero) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel_of_ne_zero),
        "((x0 : Rat) -> ((x1 : Not (Eq.{1} Rat x0 Rat.zero)) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    for (label, name) in [
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("inv_pos", p.inv_pos),
        ("mul_inv_cancel_of_neg", p.mul_inv_cancel_of_neg),
        ("mul_inv_cancel_of_ne_zero", p.mul_inv_cancel_of_ne_zero),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            ),
            "Rat.{label} must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **`Rat.inv` is the reciprocal, by computation.** `(2/1)⁻¹` reduces to `1/2`,
/// so `Eq.refl` proves it and the kernel checks the reduction.
///
/// `mul_inv_cancel` alone does not pin the operation as tightly as it looks:
/// its hypothesis is `0 < q`, so it says nothing at all about `inv` on the
/// non-positive rationals, and a "reciprocal" that agreed with the real one
/// only on the positives would satisfy it. This is the point check that fails
/// for the identity, for the constant, and for the negated reciprocal — the
/// paired negative control below runs the identity and is REFUSED.
#[test]
fn the_inverse_computes_the_reciprocal() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let two = d.num(2);
    let one = d.num(1);
    let zero = d.zero();
    // `2/1` and `1/2`, as `Rat.natDivSucc k j = k/(j+1)`.
    let doubled = d.const_app(p.nat_div_succ, &[two, zero]);
    let halved = d.const_app(p.nat_div_succ, &[one, one]);
    let reciprocal = d.const_app(p.inv, &[doubled]);
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, halved);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, halved);
    let name = d.kernel().name_str(anon, "Check.inv_two");
    let accepted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: proof,
    });
    assert!(
        accepted.is_ok(),
        "`Rat.inv (2/1)` must REDUCE to `1/2`; the kernel refused the reflexivity \
         proof, so the definition does not compute the reciprocal: {accepted:?}"
    );
}

/// The negative control: the identical `Eq.refl` script pointed at
/// `(2/1)⁻¹ = 2/1` is REFUSED, so the check above is a check.
#[test]
fn the_inverse_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.const_app(p.nat_div_succ, &[two, zero]);
    let reciprocal = d.const_app(p.inv, &[doubled]);
    // The one changed token: the claimed value is `2/1`, not `1/2`.
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, doubled);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, doubled);
    let name = d.kernel().name_str(anon, "Check.inv_two_is_two");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: proof,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(2/1)⁻¹ = 2/1`, so `Rat.inv` does not compute a \
         reciprocal and the reduction check above proves nothing"
    );
}

/// **The two lemmas `CReal.inv`'s index arithmetic is written in**, asserted
/// verbatim rather than by footprint.
///
/// `inv_natDivSucc` is the only lemma in this development that computes the
/// *value* of an inverse; `nat_index_symm` says Bishop's sampling index is
/// symmetric in its shift and its argument, which is what lets a bound read at
/// a product index come back to the **shift** without `Rat.natDivSucc` ever
/// having to be antitone in its index.
#[test]
fn the_inverse_index_toolkit_has_the_statements_creal_inv_needs() {
    let (mut kernel, p) = built();
    let render = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        render(&mut kernel, p.inv_nat_div_succ),
        "((x0 : AxNat) -> Eq.{1} Rat \
         (Rat.inv (Rat.natDivSucc (AxNat.succ AxNat.zero) x0)) \
         (Rat.natDivSucc (AxNat.succ x0) AxNat.zero))"
    );
    assert_eq!(
        render(&mut kernel, p.nat_index_symm),
        "((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} AxNat \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0) \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x0) x1)))"
    );
    for (label, name) in [
        ("inv_natDivSucc", p.inv_nat_div_succ),
        ("nat_index_symm", p.nat_index_symm),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// The negative control for
/// [`the_inverse_index_toolkit_has_the_statements_creal_inv_needs`]: the
/// **same proof term**, pointed at a statement one token away, is REFUSED.
///
/// `(1/(m+1))⁻¹ = m/1` is false at every `m ≥ 1` — at `m = 1` it claims
/// `(1/2)⁻¹ = 1` — and `nat_index_symm` with one argument left unswapped is
/// false at every `a ≠ b`. If either mutation were accepted, the statement
/// tests above would be pinning a shape rather than a fact.
#[test]
fn the_inverse_index_toolkit_cannot_prove_the_off_by_one_statements() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat_ty = d.nat_ty();

    // (1/(m+1))⁻¹ = m/1 — the numerator is `m`, not `m+1`.
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let modulus = d.const_app(p.nat_div_succ, &[one_nat, m]);
    let reciprocal = d.const_app(p.inv, &[modulus]);
    let short = d.const_app(p.nat_div_succ, &[m, zero_nat]);
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, short);
    let ty = d.pi_fv(m_fv, nat_ty, claim);
    let value = {
        let instance = d.lemma(p.inv_nat_div_succ, &[m]);
        d.lam_fv(m_fv, nat_ty, instance)
    };
    let name = d.kernel().name_str(anon, "Check.inv_off_by_one");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(1/(m+1))⁻¹ = m/1`, which is FALSE at m = 1"
    );

    // (a+1)·b + a = (b+1)·a + a — the trailing summand is not swapped.
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let sa = d.succ(a);
    let sb = d.succ(b);
    let start = {
        let scaled = NatOps::mul(&mut d, sa, b);
        NatOps::add(&mut d, scaled, a)
    };
    let unswapped = {
        let scaled = NatOps::mul(&mut d, sb, a);
        NatOps::add(&mut d, scaled, a)
    };
    let claim = d.eq(start, unswapped);
    let ty = {
        let inner = d.pi_fv(b_fv, nat_ty, claim);
        d.pi_fv(a_fv, nat_ty, inner)
    };
    let value = {
        let instance = d.lemma(p.nat_index_symm, &[a, b]);
        let inner = d.lam_fv(b_fv, nat_ty, instance);
        d.lam_fv(a_fv, nat_ty, inner)
    };
    let name = d.kernel().name_str(anon, "Check.index_half_swapped");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(a+1)·b + a = (b+1)·a + a`, which is FALSE at a = 0, b = 1"
    );
}

/// **The rational lattice computes**, and it is the *representation* that
/// decides.
///
/// The lattice laws are all one-sided consequences of `max_cases`, and every
/// one of them would hold, footprint-free, of a `max` that always returned its
/// first argument. This does not: it reduces `Rat.max` and `Rat.min` at four
/// concrete pairs by `Eq.refl` — including a pair whose gap lands in the
/// `Int.negSucc` branch, which is the branch no law exercises directly.
#[test]
fn the_rational_lattice_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // (label, a, b, negate_a, expected)
    let cases: [(&str, u32, u32, bool, bool); 4] = [
        // 3 vs 1 — the gap is `ofNat 2`, so `max = b`… no: `max a b` returns
        // `b` when `a ≤ b`, and `3 ≤ 1` is false, so the gap is `negSucc` and
        // `max` returns `a`.
        ("three_one", 3, 1, false, true),
        ("one_three", 1, 3, false, false),
        // −1 vs 1 — the `negSucc` sample on the ARGUMENT rather than the gap.
        ("neg_one_one", 1, 1, true, false),
        ("two_two", 2, 2, false, false),
    ];
    for (label, av, bv, negate_a, max_is_a) in cases {
        let raw_a = literal(&mut d, av);
        let a = if negate_a {
            crate::rat_prelude::ops::rneg(&mut d, raw_a)
        } else {
            raw_a
        };
        let b = literal(&mut d, bv);
        let joined = d.const_app(p.max, &[a, b]);
        let met = d.const_app(p.min, &[a, b]);
        let (max_expected, min_expected) = if max_is_a { (a, b) } else { (b, a) };

        let stmt = crate::rat_prelude::ops::req(&mut d, joined, max_expected);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, joined);
        let name = d.kernel().name_str(anon, format!("Check.max_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.max did not reduce for {label}: {e:?}"));

        let stmt = crate::rat_prelude::ops::req(&mut d, met, min_expected);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, met);
        let name = d.kernel().name_str(anon, format!("Check.min_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.min did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`the_rational_lattice_computes_on_both_branches`]:
/// the same `Eq.refl` route, pointed at the **other** argument.
///
/// `max 3 1` is `3`; asking it to be `1` must be REFUSED, or the reductions
/// above measure nothing.
#[test]
fn the_rational_lattice_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let zero_index = d.num(0);
    let three = d.num(3);
    let one = d.num(1);
    let a = d.const_app(p.nat_div_succ, &[three, zero_index]);
    let b = d.const_app(p.nat_div_succ, &[one, zero_index]);

    let joined = d.const_app(p.max, &[a, b]);
    let stmt = crate::rat_prelude::ops::req(&mut d, joined, b);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, joined);
    let name = d.kernel().name_str(anon, "Check.max_is_the_smaller");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.max 3 1 = 1`, so the lattice reduction check \
         proves nothing"
    );

    let met = d.const_app(p.min, &[a, b]);
    let stmt = crate::rat_prelude::ops::req(&mut d, met, a);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, met);
    let name = d.kernel().name_str(anon, "Check.min_is_the_larger");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.min 3 1 = 3`"
    );
}

/// The lattice's **case-analysis principle** and its one-Lipschitz estimate,
/// stated verbatim.
///
/// `max_cases` is the whole module: six of the nine lattice theorems are one
/// application of it. Its statement is asserted here because an `Or`-shaped
/// weakening of it (`Or (le a b) (le b a) → …`) would still let every law
/// through while quietly assuming a decision procedure at the use site.
#[test]
fn the_lattice_case_principle_has_the_statement_adr_0490_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.max),
        "((x0 : Rat) -> ((x1 : Rat) -> Rat))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_cases),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : ((x2 : Rat) -> Prop)) -> \
         ((x3 : ((x3 : Rat.le x0 x1) -> x2 x1)) -> \
         ((x4 : ((x4 : Rat.le x1 x0) -> x2 x0)) -> x2 (Rat.max x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_cases),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : ((x2 : Rat) -> Prop)) -> \
         ((x3 : ((x3 : Rat.le x0 x1) -> x2 x0)) -> \
         ((x4 : ((x4 : Rat.le x1 x0) -> x2 x1)) -> x2 (Rat.min x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.sub_max_le),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat.le (Rat.sub x0 x2) x4) -> ((x6 : Rat.le (Rat.sub x1 x3) x4) -> \
         Rat.le (Rat.sub (Rat.max x0 x1) (Rat.max x2 x3)) x4)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.zero_le_max_neg),
        "((x0 : Rat) -> Rat.le Rat.zero (Rat.max x0 (Rat.neg x0)))"
    );
}

/// Every lattice declaration is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel.
#[test]
fn the_rational_lattice_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("max", p.max),
        ("min", p.min),
        ("max_cases", p.max_cases),
        ("min_cases", p.min_cases),
        ("le_max_left", p.le_max_left),
        ("le_max_right", p.le_max_right),
        ("max_le", p.max_le),
        ("min_le_left", p.min_le_left),
        ("min_le_right", p.min_le_right),
        ("le_min", p.le_min),
        ("le_of_sub_le", p.le_of_sub_le),
        ("sub_le_of_le", p.sub_le_of_le),
        ("sub_max_le", p.sub_max_le),
        ("sub_min_le", p.sub_min_le),
        ("zero_le_max_neg", p.zero_le_max_neg),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "Rat.{label} is asserted, not derived"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

// --- `Rat.abs` and the triangle inequality -----------------------------

/// Every declaration [`super::abs::declare_abs`] adds — `Rat.abs` itself and
/// the eleven theorems built on it (the triangle-inequality group, plus
/// `abs_mul`, the `abs_le` introduction/elimination trio, and
/// `abs_sub_comm`) — is a **checked** definition or theorem with an empty
/// axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_absolute_value_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("abs", p.abs, false),
        ("abs_nonneg", p.abs_nonneg, true),
        ("le_abs_self", p.le_abs_self, true),
        ("neg_le_abs", p.neg_le_abs, true),
        ("abs_zero", p.abs_zero, true),
        ("abs_neg", p.abs_neg, true),
        ("abs_add", p.abs_add, true),
        ("abs_mul", p.abs_mul, true),
        ("abs_le_of_le_of_neg_le", p.abs_le_of_le_of_neg_le, true),
        ("le_of_abs_le", p.le_of_abs_le, true),
        ("neg_le_of_abs_le", p.neg_le_of_abs_le, true),
        ("abs_sub_comm", p.abs_sub_comm, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.abs_add` is the **unweakened** triangle inequality — `|a+b| ≤ |a| +
/// |b|` verbatim, not, say, an equality or a one-sided estimate that would
/// still have an empty footprint while proving something weaker.
#[test]
fn abs_add_is_the_triangle_inequality_unweakened() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.abs_add),
        "((x0 : Rat) -> ((x1 : Rat) -> Rat.le (Rat.abs (Rat.add x0 x1)) \
         (Rat.add (Rat.abs x0) (Rat.abs x1))))"
    );
}

/// **`Rat.abs` computes**, on both a positive and a negative literal, by
/// `Eq.refl` — not by trusting the spec theorems to be about the definition
/// this file actually declared. `|3| = 3` exercises the branch where `max`
/// returns its first argument outright; `|−3| = 3` additionally exercises
/// `Rat.neg` reducing twice (`neg (neg 3)` inside the gap computation).
#[test]
fn rat_abs_computes_on_both_signs() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // |3| = 3.
    {
        let three = literal(&mut d, 3);
        let magnitude = d.const_app(p.abs, &[three]);
        let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, three);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
        let name = d.kernel().name_str(anon, "Check.abs_three");
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.abs did not reduce on |3|: {e:?}"));
    }

    // |−3| = 3.
    {
        let three = literal(&mut d, 3);
        let negated = crate::rat_prelude::ops::rneg(&mut d, three);
        let magnitude = d.const_app(p.abs, &[negated]);
        let three_again = literal(&mut d, 3);
        let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, three_again);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
        let name = d.kernel().name_str(anon, "Check.abs_neg_three");
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.abs did not reduce on |-3|: {e:?}"));
    }
}

/// The negative control for [`rat_abs_computes_on_both_signs`]: `|3| = 1`
/// must be REFUSED, or the reduction checks above measure nothing.
#[test]
fn rat_abs_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let index = d.num(0);
    let three_num = d.num(3);
    let one_num = d.num(1);
    let three = d.const_app(p.nat_div_succ, &[three_num, index]);
    let one = d.const_app(p.nat_div_succ, &[one_num, index]);

    let magnitude = d.const_app(p.abs, &[three]);
    let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, one);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
    let name = d.kernel().name_str(anon, "Check.abs_three_is_not_one");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.abs 3 = 1`, so the abs reduction check proves nothing"
    );
}

// --- `Rat.ble`, the decidable `≤` -------------------------------------------

/// Every declaration `decide::declare_decide` adds — `Rat.ble` itself and the
/// five theorems built on it — is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_boolean_decision_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("ble", p.ble, false),
        ("ble_eq_true_of_le", p.ble_eq_true_of_le, true),
        ("le_of_ble_eq_true", p.le_of_ble_eq_true, true),
        ("ble_refl", p.ble_refl, true),
        ("ble_trans", p.ble_trans, true),
        ("ble_total", p.ble_total, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **`Rat.ble` computes**, and it is the *representation* that decides — the
/// same standard [`the_rational_lattice_computes_on_both_branches`] holds
/// `Rat.max`/`Rat.min` to. Checked at a pair whose gap lands in the
/// `Int.ofNat` branch (`1 ≤ 3`, and the reflexive `2 ≤ 2`) and one whose gap
/// lands in `Int.negSucc` (`3 ≤ 1` is `false`), by `Eq.refl` — not by trusting
/// the spec theorems to be about the definition this file actually declared.
#[test]
fn rat_ble_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // (label, a, b, ble a b expected)
    let cases: [(&str, u32, u32, bool); 3] = [
        ("one_le_three", 1, 3, true),
        ("three_le_one", 3, 1, false),
        ("two_le_two", 2, 2, true),
    ];
    for (label, av, bv, expected) in cases {
        let a = literal(&mut d, av);
        let b = literal(&mut d, bv);
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let expected_value = if expected {
            d.bool_true()
        } else {
            d.bool_false()
        };
        let stmt = d.bool_eq(ble_ab, expected_value);
        let proof = d.bool_refl(expected_value);
        let name = d.kernel().name_str(anon, format!("Check.ble_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.ble did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`rat_ble_computes_on_both_branches`]: the same
/// `Eq.refl` route, pointed at the **wrong** `Bool`.
///
/// `Rat.ble 3 1` is `false`; asking it to be `true` must be REFUSED, or the
/// computation check above measures nothing.
#[test]
fn rat_ble_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let zero_index = d.num(0);
    let three = d.num(3);
    let one = d.num(1);
    let a = d.const_app(p.nat_div_succ, &[three, zero_index]);
    let b = d.const_app(p.nat_div_succ, &[one, zero_index]);

    let ble_ab = d.const_app(p.ble, &[a, b]);
    let true_ = d.bool_true();
    let stmt = d.bool_eq(ble_ab, true_);
    let proof = d.bool_refl(true_);
    let name = d
        .kernel()
        .name_str(anon, "Check.ble_three_le_one_is_not_true");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.ble 3 1 = true`, so the computation check \
         proves nothing"
    );
}

/// `Rat.ble_refl`/`Rat.ble_trans`/`Rat.ble_total` each **use** the spec rather
/// than restating it: dropping `ble_eq_true_of_le` or `le_of_ble_eq_true`
/// would make every one of these fail to build, which is what makes them a
/// meaningful check on the spec rather than three more axiom-free theorems
/// that happen to sit beside it.
#[test]
fn ble_refl_trans_total_are_built_on_the_spec() {
    let (kernel, p) = built();
    for (label, name) in [
        ("ble_refl", p.ble_refl),
        ("ble_trans", p.ble_trans),
        ("ble_total", p.ble_total),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

// --- `Rat.sumRange` and its algebra (`rat_prelude::sum`) -------------------

/// Every declaration `sum::declare_sum` adds — `Rat.sumRange` itself and the
/// ten theorems built on it (counted from the list below, not carried over
/// from an earlier count) — is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_finite_sum_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("sumRange", p.sum_range, false),
        ("sumRange_zero", p.sum_range_zero, true),
        ("sumRange_succ", p.sum_range_succ, true),
        ("sumRange_congr", p.sum_range_congr, true),
        ("sumRange_add", p.sum_range_add, true),
        ("mul_sumRange", p.mul_sum_range, true),
        ("sumRange_le", p.sum_range_le, true),
        ("sumRange_nonneg", p.sum_range_nonneg, true),
        ("sumRange_congr_lt", p.sum_range_congr_lt, true),
        ("sumRange_eq_zero_of_lt", p.sum_range_eq_zero_of_lt, true),
        ("sumRange_swap", p.sum_range_swap, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.sumRange_zero`/`Rat.sumRange_succ` close by `Eq.refl` alone — checked
/// directly here, independent of [`super::sum`]'s own construction, over a
/// **symbolic** `f`/`n` (an opaque bound variable, not a concrete literal):
/// with a concrete `f` every subterm is ground and can fully compute, which
/// would hide whether the equation holds definitionally or only because
/// everything reduced to the same value regardless of shape (see
/// [`sum_range_succ_wrong_order_is_rejected`] for exactly that trap).
#[test]
fn sum_range_defining_equations_close_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // sumRange_zero : Eq Rat (sumRange f zero) zero, by Eq.refl.
    {
        let zero_n = d.zero();
        let lhs = rsum_range(&mut d, p, f, zero_n);
        let zero_r = crate::rat_prelude::ops::rzero(&mut d, p);
        let stmt = req(&mut d, lhs, zero_r);
        let zero_r2 = crate::rat_prelude::ops::rzero(&mut d, p);
        let proof = rrefl(&mut d, zero_r2);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let name = d.kernel().name_str(anon, "Check.sum_range_zero_refl");
        d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
            panic!(
                "sumRange_zero did not close by refl alone: {}",
                d.explain(&e)
            )
        });
    }

    // sumRange_succ : Eq Rat (sumRange f (succ n)) (sumRange f n + f n), by
    // Eq.refl — the addend order the definition actually produces.
    {
        let sn = d.succ(n);
        let lhs = rsum_range(&mut d, p, f, sn);
        let prior = rsum_range(&mut d, p, f, n);
        let fn_applied = d.apply(f, &[n]);
        let rhs = radd(&mut d, prior, fn_applied);
        let stmt = req(&mut d, lhs, rhs);
        let proof = rrefl(&mut d, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let name = d.kernel().name_str(anon, "Check.sum_range_succ_refl");
        d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
            panic!(
                "sumRange_succ did not close by refl alone: {}",
                d.explain(&e)
            )
        });
    }
}

/// The negative control for
/// [`sum_range_defining_equations_close_by_refl_alone`]: swapping the
/// addends in `sumRange_succ`'s RHS (`f n + sumRange f n` instead of
/// `sumRange f n + f n`) over the same symbolic `f`/`n` must be **REJECTED**
/// by `Eq.refl` — `Rat.add` is not definitionally commutative
/// (`Rat.add_comm` is a proved LAW, not a reduction rule, and for a
/// symbolic/opaque `f`/`n` neither addend reduces any further), so if this
/// succeeded the computation check above would prove nothing.
#[test]
fn sum_range_succ_wrong_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let lhs = rsum_range(&mut d, p, f, sn);
    let prior = rsum_range(&mut d, p, f, n);
    let fn_applied = d.apply(f, &[n]);
    let wrong_rhs = radd(&mut d, fn_applied, prior); // swapped
    let stmt = req(&mut d, lhs, wrong_rhs);
    let proof = rrefl(&mut d, wrong_rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, inner)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.sum_range_succ_wrong_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted the swapped-order sumRange_succ equation by \
         Eq.refl, so the computation check above proves nothing"
    );
}

// --- finite probability distributions (`rat_prelude::probability`) --------

/// Every declaration `probability::declare_probability` adds —
/// `Rat.IsDistribution` itself and the two theorems built on it — is a
/// **checked** definition or theorem with an empty axiom footprint, read out
/// of the kernel, not off the diff.
#[test]
fn the_probability_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("IsDistribution", p.is_distribution, false),
        ("prob_le_one", p.prob_le_one, true),
        ("prob_complement", p.prob_complement, true),
        ("expectation", p.expectation, false),
        ("expectation_add", p.expectation_add, true),
        ("expectation_smul", p.expectation_smul, true),
        ("expectation_const", p.expectation_const, true),
        ("uniform", p.uniform, false),
        ("uniform_is_distribution", p.uniform_is_distribution, true),
        ("expectation_nonneg", p.expectation_nonneg, true),
        ("expectation_le", p.expectation_le, true),
        ("markov_inequality", p.markov_inequality, true),
        (
            "expectation_indicator_le_one",
            p.expectation_indicator_le_one,
            true,
        ),
        ("variance", p.variance, false),
        ("variance_nonneg", p.variance_nonneg, true),
        ("variance_eq", p.variance_eq, true),
        ("variance_smul", p.variance_smul, true),
        ("covariance", p.covariance, false),
        ("variance_add_eq", p.variance_add_eq, true),
        (
            "variance_add_of_uncorrelated",
            p.variance_add_of_uncorrelated,
            true,
        ),
        ("indicator", p.indicator, false),
        ("indicator_nonneg", p.indicator_nonneg, true),
        ("indicator_le", p.indicator_le, true),
        ("variance_indicator", p.variance_indicator, true),
        (
            "variance_indicator_le_quarter",
            p.variance_indicator_le_quarter,
            true,
        ),
        ("markov_constructed", p.markov_constructed, true),
        ("chebyshev_inequality", p.chebyshev_inequality, true),
        ("covariance_comm", p.covariance_comm, true),
        ("covariance_add_right", p.covariance_add_right, true),
        ("covariance_smul_left", p.covariance_smul_left, true),
        ("sumVars", p.sum_vars, false),
        ("expectation_sumVars", p.expectation_sum_vars, true),
        ("covariance_sumVars_left", p.covariance_sum_vars_left, true),
        ("covariance_sumVars", p.covariance_sum_vars, true),
        ("PairwiseUncorrelated", p.pairwise_uncorrelated, false),
        ("variance_sumVars", p.variance_sum_vars, true),
        ("variance_scaled_mean", p.variance_scaled_mean, true),
        (
            "chebyshev_sampleMean_uncorrelated",
            p.chebyshev_sample_mean_uncorrelated,
            true,
        ),
        (
            "variance_sampleMean_uncorrelated",
            p.variance_sample_mean_uncorrelated,
            true,
        ),
        (
            "weak_law_of_large_numbers",
            p.weak_law_of_large_numbers,
            true,
        ),
        (
            "bernoulli_law_of_large_numbers",
            p.bernoulli_law_of_large_numbers,
            true,
        ),
        (
            "variance_scaled_add_nonneg",
            p.variance_scaled_add_nonneg,
            true,
        ),
        (
            "covariance_sq_le_variance_mul_of_pos",
            p.covariance_sq_le_variance_mul_of_pos,
            true,
        ),
        (
            "covariance_sq_le_variance_mul_of_zero_zero",
            p.covariance_sq_le_variance_mul_of_zero_zero,
            true,
        ),
        (
            "covariance_sq_le_variance_mul",
            p.covariance_sq_le_variance_mul,
            true,
        ),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// A CONCRETE instance of [`RatPrelude::covariance_sum_vars`], checked by
/// `Eq.refl` alone against the DEFINITIONS themselves (`Rat.covariance`,
/// `Rat.sumVars`, `Rat.sumRange`, `Rat.expectation`) — not against the
/// theorem's own proof, which could be internally consistent yet prove a
/// statement off by a factor this check would catch (exactly the class
/// [`bernoulli_variance_at_one_half_reduces_to_one_quarter`] guards against
/// for `Rat.variance_indicator`).
///
/// `pf k := 1` (no `IsDistribution` needed — `covariance_sumVars` carries no
/// such hypothesis), `n := 2`, `X i k := k` for every `i` (`m := 2`, so `X`
/// does not even need to vary across the family — `sumVars X 2 k = k+k =
/// 2k`), `Y j k := 1` for every `j` (`m' := 1`).
///
/// Hand computation (`E[h] := Σ_{k<2} h(k)·1`): `E[k] = 0+1 = 1`, `E[1] =
/// 1+1 = 2`, `E[2k] = 2`, `E[2k·1] = 2`. LHS: `Cov[2k, 1] = E[2k·1] −
/// E[2k]·E[1] = 2 − 2·2 = −2`. RHS: `Cov[k,1] = E[k·1] − E[k]·E[1] = 1 −
/// 1·2 = −1`, summed over `i<2, j<1` (both terms identical since `X`/`Y` do
/// not depend on their family index) `= 2·(−1) = −2`. Both sides `= −2`.
#[test]
fn covariance_sum_vars_computes_at_a_concrete_two_by_one_instance() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rneg, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    // x_body k := Rat.natDivSucc k 0  (= k as a rational)
    let x_body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    // X i k := x_body k, for every i (X does not depend on its family index)
    let x_family = {
        let i_fv = d.fresh_fvar();
        d.lam_fv(i_fv, nat, x_body)
    };
    // y_body k := Rat.one, for every k
    let y_body = {
        let k_fv = d.fresh_fvar();
        let one = rone(&mut d, p);
        d.lam_fv(k_fv, nat, one)
    };
    // Y j k := y_body k, for every j
    let y_family = {
        let j_fv = d.fresh_fvar();
        d.lam_fv(j_fv, nat, y_body)
    };
    // pf k := Rat.one
    let pf = {
        let k_fv = d.fresh_fvar();
        let one = rone(&mut d, p);
        d.lam_fv(k_fv, nat, one)
    };
    let n = d.num(2);
    let m = d.num(2);
    let m2 = d.num(1);

    let neg_two = {
        let numerator = d.num(2);
        let idx = d.num(0);
        let two = d.const_app(p.nat_div_succ, &[numerator, idx]);
        rneg(&mut d, two)
    };

    // LHS := covariance (sumVars X m) (sumVars Y m2) pf n
    let sv_x = d.const_app(p.sum_vars, &[x_family, m]);
    let sv_y = d.const_app(p.sum_vars, &[y_family, m2]);
    let lhs = d.const_app(p.covariance, &[sv_x, sv_y, pf, n]);
    let lhs_stmt = req(&mut d, lhs, neg_two);
    let lhs_proof = rrefl(&mut d, lhs);
    let lhs_name = d.kernel().name_str(anon, "Check.cov_sum_vars_lhs_computes");
    d.declare_theorem(lhs_name, lhs_stmt, lhs_proof)
        .unwrap_or_else(|e| {
            panic!(
                "covariance(sumVars X 2, sumVars Y 1) did not reduce to -2: {}",
                d.explain(&e)
            )
        });

    // RHS := sumRange (fun i => sumRange (fun j => covariance (X i) (Y j) pf n) m2) m
    let inner_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let xi = d.apply(x_family, &[i]);
        let per_j = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let yj = d.apply(y_family, &[j]);
            let cov = d.const_app(p.covariance, &[xi, yj, pf, n]);
            d.lam_fv(j_fv, nat, cov)
        };
        let inner_sum = d.const_app(p.sum_range, &[per_j, m2]);
        d.lam_fv(i_fv, nat, inner_sum)
    };
    let rhs = d.const_app(p.sum_range, &[inner_fn, m]);
    let rhs_stmt = req(&mut d, rhs, neg_two);
    let rhs_proof = rrefl(&mut d, rhs);
    let rhs_name = d.kernel().name_str(anon, "Check.cov_sum_vars_rhs_computes");
    d.declare_theorem(rhs_name, rhs_stmt, rhs_proof)
        .unwrap_or_else(|e| {
            panic!(
                "the double sum of covariances did not reduce to -2: {}",
                d.explain(&e)
            )
        });
}

/// The negative control for
/// [`covariance_sum_vars_computes_at_a_concrete_two_by_one_instance`]: the
/// SAME `covariance(sumVars X 2, sumVars Y 1, pf, n)` term is NOT `-1` — the
/// value a BROKEN `sumVars` that returned a single family member instead of
/// the sum of the family (`sumVars X 2 k = x_body k` instead of `x_body k +
/// x_body k`) would produce (`Cov[x_body, y_body] = -1`, computed in the
/// positive test's own doc comment). Must be REFUSED, or the positive check
/// above proves nothing about the family actually being summed.
#[test]
fn covariance_sum_vars_lhs_is_not_the_unsummed_single_member_value() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rneg, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let x_body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    let x_family = {
        let i_fv = d.fresh_fvar();
        d.lam_fv(i_fv, nat, x_body)
    };
    let y_body = {
        let k_fv = d.fresh_fvar();
        let one = rone(&mut d, p);
        d.lam_fv(k_fv, nat, one)
    };
    let y_family = {
        let j_fv = d.fresh_fvar();
        d.lam_fv(j_fv, nat, y_body)
    };
    let pf = {
        let k_fv = d.fresh_fvar();
        let one = rone(&mut d, p);
        d.lam_fv(k_fv, nat, one)
    };
    let n = d.num(2);
    let m = d.num(2);
    let m2 = d.num(1);

    let neg_one = {
        let one = rone(&mut d, p);
        rneg(&mut d, one)
    };

    let sv_x = d.const_app(p.sum_vars, &[x_family, m]);
    let sv_y = d.const_app(p.sum_vars, &[y_family, m2]);
    let lhs = d.const_app(p.covariance, &[sv_x, sv_y, pf, n]);
    let stmt = req(&mut d, lhs, neg_one);
    let proof = rrefl(&mut d, neg_one);
    let name = d
        .kernel()
        .name_str(anon, "Check.cov_sum_vars_lhs_is_not_unsummed");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted covariance(sumVars X 2, sumVars Y 1) = -1 (the \
         UNSUMMED single-member value, not the sum of the family), so the \
         reduction check above proves nothing"
    );
}

/// A CONCRETE Bernoulli instance, checked by `Eq.refl` alone against the
/// DEFINITIONS themselves — not against [`RatPrelude::variance_indicator`]'s
/// proof, which could be internally consistent yet prove a statement off by
/// a factor this check would catch. A fair coin: `a := 1`, `X k := k`, `p :=
/// const 1/2`, `n := 2` (`X 0 = 0 < 1`, `X 1 = 1 ≤ 1`, so the indicator
/// selects exactly outcome `1`). Hand computation: `E[𝟙] = 0·(1/2) +
/// 1·(1/2) = 1/2`; `Var[𝟙] = E[𝟙²] − E[𝟙]² = E[𝟙] − E[𝟙]² = 1/2 − 1/4 =
/// 1/4` (using `𝟙² = 𝟙`, [`indicator_sq_eq_self`](super::probability)).
#[test]
fn bernoulli_variance_at_one_half_reduces_to_one_quarter() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 1, 0); // 1
    let half = literal(&mut d, 1, 1); // 1/2
    let quarter = literal(&mut d, 1, 3); // 1/4

    let x = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    let ind = d.const_app(p.indicator, &[a, x]);

    let pf = {
        let k_fv = d.fresh_fvar();
        d.lam_fv(k_fv, nat, half)
    };
    let n = d.num(2);

    let mu = d.const_app(p.expectation, &[ind, pf, n]);
    let mu_stmt = req(&mut d, mu, half);
    let mu_proof = rrefl(&mut d, mu);
    let mu_name = d
        .kernel()
        .name_str(anon, "Check.bernoulli_half_expectation");
    d.declare_theorem(mu_name, mu_stmt, mu_proof)
        .unwrap_or_else(|e| panic!("expectation did not reduce to 1/2: {e:?}"));

    let variance = d.const_app(p.variance, &[ind, pf, n]);
    let var_stmt = req(&mut d, variance, quarter);
    let var_proof = rrefl(&mut d, variance);
    let var_name = d.kernel().name_str(anon, "Check.bernoulli_half_variance");
    d.declare_theorem(var_name, var_stmt, var_proof)
        .unwrap_or_else(|e| panic!("variance did not reduce to 1/4: {e:?}"));
}

/// The negative control for
/// [`bernoulli_variance_at_one_half_reduces_to_one_quarter`]: the SAME
/// variance is NOT `1/2` (the mean itself — the off-by-`p`-instead-of-
/// `p(1-p)` bug a wrong `variance` definition could have). Must be REFUSED,
/// or the positive check above proves nothing.
#[test]
fn bernoulli_variance_at_one_half_is_not_one_half() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 1, 0);
    let half = literal(&mut d, 1, 1);

    let x = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    let ind = d.const_app(p.indicator, &[a, x]);

    let pf = {
        let k_fv = d.fresh_fvar();
        d.lam_fv(k_fv, nat, half)
    };
    let n = d.num(2);

    let variance = d.const_app(p.variance, &[ind, pf, n]);
    let stmt = req(&mut d, variance, half);
    let proof = rrefl(&mut d, half);
    let name = d
        .kernel()
        .name_str(anon, "Check.bernoulli_variance_is_not_the_mean");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted Var[fair coin] = 1/2 (the MEAN, not p(1-p)=1/4), \
         so the reduction check above proves nothing"
    );
}

/// The quarter bound is TIGHT at `q = 1/2` — the fair coin is the unique
/// maximiser of `q(1-q)`: `4·(1/2)·(1/2) = 1` exactly, checked as an
/// EQUALITY by `Eq.refl` alone (not merely that
/// [`RatPrelude::variance_indicator_le_quarter`] admits `≤`, which would
/// also accept a bound that is off by a wide margin).
#[test]
fn quarter_bound_is_tight_at_one_half() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, req, rmul, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let half = literal(&mut d, 1, 1);
    let one_r = rone(&mut d, p);
    let two_r = radd(&mut d, one_r, one_r);
    let three_r = radd(&mut d, two_r, one_r);
    let four_r = radd(&mut d, three_r, one_r);

    let half_sq = rmul(&mut d, half, half);
    let four_half = rmul(&mut d, four_r, half);
    let four_half_sq = rmul(&mut d, four_r, half_sq);
    let bound_expr = rsub(&mut d, p, four_half, four_half_sq);

    let stmt = req(&mut d, bound_expr, one_r);
    let proof = rrefl(&mut d, bound_expr);
    let name = d
        .kernel()
        .name_str(anon, "Check.quarter_bound_tight_at_half");
    d.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("4*(1/2)*(1/2) did not reduce to 1: {e:?}"));
}

/// `Rat.chebyshev_sampleMean_uncorrelated`'s rendered type, verbatim — this
/// IS the weak law of large numbers in its standard finite-sample
/// Chebyshev-bound shape (a bound on the ε²-weighted probability mass where
/// the sample mean of `m` pairwise-uncorrelated variables deviates from its
/// expectation by at least `ε`), and this pin exists so a future edit that
/// weakens it (drops the `IsDistribution` hypothesis, drops
/// `PairwiseUncorrelated`, or changes which quantity the bound is against)
/// is caught by a rendered-type diff rather than an unread doc comment. See
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`]'s own doc for the full
/// reading.
#[test]
fn chebyshev_sample_mean_uncorrelated_is_the_weak_law_of_large_numbers() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.chebyshev_sample_mean_uncorrelated)
        .expect("Rat.chebyshev_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.chebyshev_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> ((x1 : Rat) -> \
         ((x2 : ((x2 : AxNat) -> Rat)) -> ((x3 : AxNat) -> ((x4 : AxNat) -> \
         ((x5 : Rat.IsDistribution x2 x3) -> ((x6 : Rat.PairwiseUncorrelated x0 x4 x2 x3) -> \
         ((x7 : Rat.lt Rat.zero x1) -> Rat.le (Rat.mul (Rat.mul x1 x1) \
         (Rat.expectation (Rat.indicator (Rat.mul x1 x1) (fun (x8 : AxNat) => Rat.mul \
         (Rat.sub ((fun (x9 : AxNat) => Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.sumVars x0 x4 x9)) x8) (Rat.expectation (fun (x9 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x9)) x2 x3)) \
         (Rat.sub ((fun (x9 : AxNat) => Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.sumVars x0 x4 x9)) x8) (Rat.expectation (fun (x9 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x9)) x2 x3)))) x2 x3)) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero))) (Rat.sumRange (fun (x8 : AxNat) => \
         Rat.variance (x0 x8) x2 x3) x4))))))))))",
        "Rat.chebyshev_sampleMean_uncorrelated's statement drifted from the weak-law reading"
    );
}

/// `Rat.weak_law_of_large_numbers` is a RENAMING, not a new result — its
/// rendered type must be BYTE-IDENTICAL to
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`]'s, checked directly
/// rather than trusted from the doc comment or the commit message.
#[test]
fn weak_law_of_large_numbers_is_byte_identical_to_the_theorem_it_renames() {
    let (kernel, p) = built();
    let cheb_ty = match kernel
        .environment()
        .get(p.chebyshev_sample_mean_uncorrelated)
        .expect("Rat.chebyshev_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.chebyshev_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let wlln_ty = match kernel
        .environment()
        .get(p.weak_law_of_large_numbers)
        .expect("Rat.weak_law_of_large_numbers must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.weak_law_of_large_numbers must be a Theorem, found {other:?}"),
    };
    assert_eq!(
        kernel.render_lean(cheb_ty),
        kernel.render_lean(wlln_ty),
        "Rat.weak_law_of_large_numbers must be the SAME statement as \
         Rat.chebyshev_sampleMean_uncorrelated, byte for byte — it is a \
         renaming for discoverability, not a new theorem"
    );
}

/// `Rat.variance_sampleMean_uncorrelated`'s rendered type, verbatim — the
/// quantitative heart of the weak law named on its own: `Var[sample mean] =
/// (1/m)² · Σ_{j<m} Var[X_j]` under `IsDistribution` and
/// `PairwiseUncorrelated`, composing
/// [`RatPrelude::variance_scaled_mean`] and [`RatPrelude::variance_sumVars`].
#[test]
fn variance_sample_mean_uncorrelated_is_the_statement_briefed() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.variance_sample_mean_uncorrelated)
        .expect("Rat.variance_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.variance_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         ((x1 : ((x1 : AxNat) -> Rat)) -> ((x2 : AxNat) -> \
         ((x3 : Rat.IsDistribution x1 x2) -> ((x4 : AxNat) -> \
         ((x5 : Rat.PairwiseUncorrelated x0 x4 x1 x2) -> \
         Eq.{1} Rat (Rat.variance (fun (x6 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x6)) x1 x2) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero))) (Rat.sumRange (fun (x6 : AxNat) => \
         Rat.variance (x0 x6) x1 x2) x4))))))))",
        "Rat.variance_sampleMean_uncorrelated's statement drifted from the briefed one"
    );
}

/// `Rat.expectation X p n` closes by `Eq.refl` alone against `sumRange (fun k
/// => X k * p k) n`, over a **symbolic** `X`/`p`/`n` — the same convention
/// [`sum_range_defining_equations_close_by_refl_alone`] follows, so this
/// checks the definition itself rather than a fully-computed instance.
#[test]
fn expectation_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = rmul(&mut d, xk, pk);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.expectation, &[x, pf, n]);
    let rhs = rsum_range(&mut d, p, summand, n);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d.kernel().name_str(anon, "Check.expectation_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.expectation did not reduce to its defining sum by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`expectation_defining_equation_closes_by_refl_alone`]: the same route
/// pointed at the summand with the multiplication **swapped**
/// (`p k * X k` instead of `X k * p k`), over the same symbolic `X`/`p`/`n`.
/// `Rat.mul` is not definitionally commutative (`Rat.mul_comm` is a proved
/// law, not a reduction rule), so this must be **REJECTED** — otherwise the
/// computation check above proves nothing.
#[test]
fn expectation_wrong_multiplication_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let swapped_summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = rmul(&mut d, pk, xk); // swapped
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.expectation, &[x, pf, n]);
    let rhs = rsum_range(&mut d, p, swapped_summand, n);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.expectation_swapped_mul_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.expectation's summand with the multiplication \
         swapped, so the computation check above proves nothing"
    );
}

/// `Rat.variance X p n` closes by `Eq.refl` alone against `expectation (fun k
/// => sub (X k) (expectation X p n) * sub (X k) (expectation X p n)) p n`,
/// over a **symbolic** `X`/`p`/`n` — the same convention
/// [`expectation_defining_equation_closes_by_refl_alone`] follows.
#[test]
fn variance_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = d.const_app(p.expectation, &[x, pf, n]);
    let summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let gap = rsub(&mut d, p, xk, mu);
        let body = rmul(&mut d, gap, gap);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.variance, &[x, pf, n]);
    let rhs = d.const_app(p.expectation, &[summand, pf, n]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d.kernel().name_str(anon, "Check.variance_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.variance did not reduce to its defining expectation by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`variance_defining_equation_closes_by_refl_alone`]: the same route with
/// the subtraction **swapped** (`sub (expectation X p n) (X k)` instead of
/// `sub (X k) (expectation X p n)`) inside the squared summand. `Rat.sub` is
/// not definitionally anti-commutative (`(a-b)² = (b-a)²` is a proved
/// identity, not a reduction rule), so this must be **REJECTED** — otherwise
/// the computation check above proves nothing.
#[test]
fn variance_swapped_subtraction_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = d.const_app(p.expectation, &[x, pf, n]);
    let swapped_summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let gap = rsub(&mut d, p, mu, xk); // swapped
        let body = rmul(&mut d, gap, gap);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.variance, &[x, pf, n]);
    let rhs = d.const_app(p.expectation, &[swapped_summand, pf, n]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.variance_swapped_sub_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.variance's summand with the subtraction \
         swapped, so the computation check above proves nothing"
    );
}

/// `Rat.covariance X Y p n` closes by `Eq.refl` alone against `sub
/// (expectation (fun k => X k * Y k) p n) (mul (expectation X p n)
/// (expectation Y p n))`, over **symbolic** `X`/`Y`/`p`/`n` — the same
/// convention [`variance_defining_equation_closes_by_refl_alone`] follows.
#[test]
fn covariance_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let body = rmul(&mut d, xk, yk);
        d.lam_fv(k_fv, nat, body)
    };
    let e_xy = d.const_app(p.expectation, &[xy, pf, n]);
    let ex = d.const_app(p.expectation, &[x, pf, n]);
    let ey = d.const_app(p.expectation, &[y, pf, n]);
    let exey = rmul(&mut d, ex, ey);

    let lhs = d.const_app(p.covariance, &[x, y, pf, n]);
    let rhs = rsub(&mut d, p, e_xy, exey);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let name = d.kernel().name_str(anon, "Check.covariance_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.covariance did not reduce to its defining sub-of-expectations \
             by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`covariance_defining_equation_closes_by_refl_alone`]: the same route with
/// the subtraction **swapped** (`sub (mul (expectation X p n) (expectation Y
/// p n)) (expectation (fun k => X k * Y k) p n)` instead of the defined
/// order). `Rat.sub` is not definitionally anti-commutative, so this must be
/// **REJECTED** — otherwise the computation check above proves nothing.
#[test]
fn covariance_swapped_subtraction_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let body = rmul(&mut d, xk, yk);
        d.lam_fv(k_fv, nat, body)
    };
    let e_xy = d.const_app(p.expectation, &[xy, pf, n]);
    let ex = d.const_app(p.expectation, &[x, pf, n]);
    let ey = d.const_app(p.expectation, &[y, pf, n]);
    let exey = rmul(&mut d, ex, ey);

    let lhs = d.const_app(p.covariance, &[x, y, pf, n]);
    let swapped_rhs = rsub(&mut d, p, exey, e_xy); // swapped
    let stmt = req(&mut d, lhs, swapped_rhs);
    let proof = rrefl(&mut d, swapped_rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.covariance_swapped_sub_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.covariance with the subtraction swapped, \
         so the computation check above proves nothing"
    );
}

// --- the constructed indicator (`rat_prelude::probability`) ----------------

/// Every declaration `probability::declare_probability` adds in its
/// indicator section — `Rat.indicator` itself and the six theorems built on
/// it — is a **checked** definition or theorem with an empty axiom footprint,
/// read out of the kernel, not off the diff.
#[test]
fn the_indicator_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("indicator", p.indicator, false),
        ("indicator_nonneg", p.indicator_nonneg, true),
        ("indicator_le", p.indicator_le, true),
        ("variance_indicator", p.variance_indicator, true),
        (
            "variance_indicator_le_quarter",
            p.variance_indicator_le_quarter,
            true,
        ),
        ("markov_constructed", p.markov_constructed, true),
        ("chebyshev_inequality", p.chebyshev_inequality, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.indicator` **computes**, on both branches of the `Rat.ble` it
/// dispatches on — the same standard [`rat_ble_computes_on_both_branches`]
/// holds `Rat.ble` itself to, checked by `Eq.refl` alone rather than by
/// trusting [`declare_indicator_nonneg`]/[`declare_indicator_le`] to be
/// about the definition this file actually declared.
#[test]
fn rat_indicator_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rone, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let const_x = |d: &mut IntDev<'_>, value: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, value)
    };

    // (label, a, X's constant value, ble a (X k) expected)
    let cases: [(&str, u32, u32, bool); 2] =
        [("selected", 3, 5, true), ("not_selected", 7, 5, false)];
    for (label, av, xv, expected) in cases {
        let a = literal(&mut d, av);
        let x_val = literal(&mut d, xv);
        let x = const_x(&mut d, x_val);
        let k = d.num(0);
        let indicator_val = d.const_app(p.indicator, &[a, x, k]);
        let expected_value = if expected {
            rone(&mut d, p)
        } else {
            rzero(&mut d, p)
        };
        let stmt = req(&mut d, indicator_val, expected_value);
        let proof = rrefl(&mut d, indicator_val);
        let name = d
            .kernel()
            .name_str(anon, format!("Check.indicator_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.indicator did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`rat_indicator_computes_on_both_branches`]:
/// `Rat.indicator 7 (fun _ => 5) 0` returning `Rat.one` on the **false**
/// branch (`Rat.ble 7 5 = false`). `Rat.indicator`'s whole point is
/// discharging `markov_inequality`'s pointwise hypothesis
/// ([`declare_indicator_le`]); a definition that quietly returned `1` when
/// `Rat.ble` is `false` would make that hypothesis false for any `a > X k`.
/// This must be REFUSED, or the computation check above proves nothing.
#[test]
fn rat_indicator_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let a = literal(&mut d, 7);
    let x_val = literal(&mut d, 5);
    let x = {
        let k_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, x_val)
    };
    let k = d.num(0);
    let indicator_val = d.const_app(p.indicator, &[a, x, k]);
    let one = rone(&mut d, p);
    let stmt = req(&mut d, indicator_val, one);
    let proof = rrefl(&mut d, one);
    let name = d
        .kernel()
        .name_str(anon, "Check.indicator_false_branch_is_not_one");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.indicator 7 (fun _ => 5) 0 = 1`, so the \
         computation check above proves nothing"
    );
}

#[test]
fn sum_vars_succ_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_ty, req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // sumVars X (succ m) k = sumVars X m k + X m k, by Eq.refl — the addend
    // order sumRange's own succ ι-reduction actually produces.
    let sm = d.succ(m);
    let lhs = d.const_app(p.sum_vars, &[x, sm, k]);
    let sv_m_k = d.const_app(p.sum_vars, &[x, m, k]);
    let x_m = d.apply(x, &[m]);
    let x_m_k = d.apply(x_m, &[k]);
    let rhs = radd(&mut d, sv_m_k, x_m_k);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, x_ty, with_m)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let name = d.kernel().name_str(anon, "Check.sum_vars_succ_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.sumVars did not reduce to sumVars X m k + X m k at succ m \
             by refl alone: {}",
            d.explain(&e)
        )
    });
}

#[test]
fn sum_vars_succ_wrong_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_ty, req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let sm = d.succ(m);
    let lhs = d.const_app(p.sum_vars, &[x, sm, k]);
    let sv_m_k = d.const_app(p.sum_vars, &[x, m, k]);
    let x_m = d.apply(x, &[m]);
    let x_m_k = d.apply(x_m, &[k]);
    let wrong_rhs = radd(&mut d, x_m_k, sv_m_k); // swapped
    let stmt = req(&mut d, lhs, wrong_rhs);
    let proof = rrefl(&mut d, wrong_rhs);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, x_ty, with_m)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let name = d.kernel().name_str(anon, "Check.sum_vars_succ_wrong_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted the swapped-order sumVars succ equation by \
         Eq.refl, so the computation check above proves nothing"
    );
}

// --- `Rat.sumRange` diagonal/rectangle reindexing (`rat_prelude::diagonal`) -

/// Every declaration `diagonal::declare_diagonal` adds — the three theorems
/// built on `Rat.sumRange` (counted from the list below, not carried over
/// from an earlier count) — is a **checked** theorem with an empty axiom
/// footprint, read out of the kernel, not off the diff.
#[test]
fn the_diagonal_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("sumRange_split", p.sum_range_split),
        ("sumRange_diagonal", p.sum_range_diagonal),
        (
            "sumRange_rect_eq_diag_add_corner",
            p.sum_range_rect_eq_diag_add_corner,
        ),
        ("sumRange_mul", p.sum_range_mul),
        ("sumRange_mul_double", p.sum_range_mul_double),
        (
            "sumRange_mul_eq_diag_add_corner",
            p.sum_range_mul_eq_diag_add_corner,
        ),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.sumRange_diagonal` at a concrete instance: `F i j := 1` (constant),
/// `n = 3`. Both the antidiagonal grouping (`Σ_{k<3} Σ_{i≤k} F i (k−i)`) and
/// the row grouping (`Σ_{i<3} Σ_{j<3−i} F i j`) COUNT the same 6-point
/// triangle `{(i,j) : i+j<3}` — `(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)` — and
/// both must independently reduce to `6`, so this is a genuine reindexing
/// check over `Rat` values, not just an admission. A constant summand (not
/// `add i j`, unlike `Nat`'s own version of this test) keeps the concrete
/// arithmetic to `Rat.add`/normalize alone, without also needing a `Nat →
/// Rat` conversion for the summand itself.
#[test]
fn sum_range_diagonal_computes_at_a_concrete_instance_over_rat() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // F := fun i j => 1 (constant Rat one).
    let one = literal(&mut d, 1);
    let ff = {
        let i_fv = d.fresh_fvar();
        let j_fv = d.fresh_fvar();
        let inner = d.lam_fv(j_fv, nat, one);
        d.lam_fv(i_fv, nat, inner)
    };
    let three = d.num(3);
    let six = literal(&mut d, 6);

    let proof = d.lemma(p.sum_range_diagonal, &[ff, three]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_diagonal(F,3) should infer: {e:?}"));

    // The antidiagonal (triangle) sum, built independently of
    // `diagonal.rs`'s own helpers.
    let triangle = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ki = d.sub(k, i);
        let fiki = d.apply(ff, &[i, ki]);
        let diag_inner = d.lam_fv(i_fv, nat, fiki);
        let sk = d.succ(k);
        let diag_sum = rsum_range(&mut d, p, diag_inner, sk);
        let t_fn = d.lam_fv(k_fv, nat, diag_sum);
        rsum_range(&mut d, p, t_fn, three)
    };
    // The row-major sum, likewise independently built.
    let rows = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let fij = d.apply(ff, &[i, j]);
        let row_inner = d.lam_fv(j_fv, nat, fij);
        let ni = d.sub(three, i);
        let row_sum_i = rsum_range(&mut d, p, row_inner, ni);
        let row_fn = d.lam_fv(i_fv, nat, row_sum_i);
        rsum_range(&mut d, p, row_fn, three)
    };

    let expected = req(&mut d, triangle, rows);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_diagonal(F,3) should state the antidiagonal sum equals the row-major sum"
    );
    assert!(
        d.kernel().def_eq(triangle, six),
        "the antidiagonal (triangle) sum of the constant 1 over {{(i,j):i+j<3}} \
         (6 points) must reduce to 6"
    );
    assert!(
        d.kernel().def_eq(rows, six),
        "the row-major sum of the constant 1 over {{(i,j):i+j<3}} (6 points) \
         must reduce to 6"
    );

    assert!(
        d.kernel().axiom_footprint(p.sum_range_diagonal).is_empty(),
        "sumRange_diagonal must rest on zero axioms"
    );
}

/// `Rat.sumRange_rect_eq_diag_add_corner` at a concrete instance: `F i j :=
/// 1`, `n = 2`. The rectangle `{i<2,j<2}` (4 points) splits into the
/// antidiagonal triangle `{i+j<2}` (3 points: `(0,0),(1,0),(0,1)`) and the
/// corner `{i<2,j<2,i+j≥2}` (the single point `(1,1)`) — `4 = 3 + 1`, checked
/// both as the theorem's own statement AND by independently reducing all
/// three sums.
#[test]
fn sum_range_rect_eq_diag_add_corner_computes_at_a_concrete_instance_over_rat() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let one = literal(&mut d, 1);
    let ff = {
        let i_fv = d.fresh_fvar();
        let j_fv = d.fresh_fvar();
        let inner = d.lam_fv(j_fv, nat, one);
        d.lam_fv(i_fv, nat, inner)
    };
    let two = d.num(2);

    let proof = d.lemma(p.sum_range_rect_eq_diag_add_corner, &[ff, two]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_rect_eq_diag_add_corner(F,2) should infer: {e:?}"));

    // The rectangle {(i,j): i<2, j<2} -- 4 points -- built independently.
    let rectangle = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let fij = d.apply(ff, &[i, j]);
        let row_inner = d.lam_fv(j_fv, nat, fij);
        let row_sum_i = rsum_range(&mut d, p, row_inner, two);
        let rect_row = d.lam_fv(i_fv, nat, row_sum_i);
        rsum_range(&mut d, p, rect_row, two)
    };
    // The antidiagonal triangle {(i,j): i+j<2} -- 3 points -- built
    // independently.
    let triangle = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ki = d.sub(k, i);
        let fiki = d.apply(ff, &[i, ki]);
        let diag_inner = d.lam_fv(i_fv, nat, fiki);
        let sk = d.succ(k);
        let diag_sum = rsum_range(&mut d, p, diag_inner, sk);
        let t_fn = d.lam_fv(k_fv, nat, diag_sum);
        rsum_range(&mut d, p, t_fn, two)
    };
    // The corner {(i,j): i<2, j<2, i+j>=2} -- the single point (1,1) --
    // built independently.
    let corner = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let k_fv = d.fresh_fvar();
        let sub_2i = d.sub(two, i);
        let shifted_idx = {
            let k = d.kernel().fvar(k_fv);
            d.add(sub_2i, k)
        };
        let fi_shifted = d.apply(ff, &[i, shifted_idx]);
        let corner_inner = d.lam_fv(k_fv, nat, fi_shifted);
        let corner_sum_i = rsum_range(&mut d, p, corner_inner, i);
        let corner_row = d.lam_fv(i_fv, nat, corner_sum_i);
        rsum_range(&mut d, p, corner_row, two)
    };

    let rhs = radd(&mut d, triangle, corner);
    let expected = req(&mut d, rectangle, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_rect_eq_diag_add_corner(F,2) should state rectangle = triangle + corner"
    );

    let four = literal(&mut d, 4);
    let three = literal(&mut d, 3);
    assert!(
        d.kernel().def_eq(rectangle, four),
        "the rectangle sum of the constant 1 over {{i<2,j<2}} (4 points) must reduce to 4"
    );
    assert!(
        d.kernel().def_eq(triangle, three),
        "the triangle sum of the constant 1 over {{i+j<2}} (3 points) must reduce to 3"
    );
    assert!(
        d.kernel().def_eq(corner, one),
        "the corner sum of the constant 1 over {{i<2,j<2,i+j>=2}} (1 point) must reduce to 1"
    );

    assert!(
        d.kernel()
            .axiom_footprint(p.sum_range_rect_eq_diag_add_corner)
            .is_empty(),
        "sumRange_rect_eq_diag_add_corner must rest on zero axioms"
    );
}

/// `Rat.sumRange_mul_double` at **two different bounds** — the generality the
/// same-bound square could not supply, and the reason this lemma carries `m`
/// and `n` separately.
///
/// `f i := 2^i`, `g j := 3^j`, `m = 2`, `n = 3`. Independently:
/// `(2^0+2^1)·(3^0+3^1+3^2) = 3·13 = 39`, and the double sum
/// `Σ_{i<2} Σ_{j<3} 2^i·3^j` is the same 39. Checked as the theorem's own
/// statement AND by reducing both sides to the numeral.
///
/// Index-DEPENDENT summands are the point: with `f` and `g` constant every
/// cell of the rectangle carries the same value, so a transposed bound
/// (`m` for `n`) would still balance. Here it does not — `3·13` and `13·3`
/// agree, but `Σ_{i<2}Σ_{j<3}` and `Σ_{i<3}Σ_{j<2}` are built from different
/// cells and the structural `def_eq` below separates them.
#[test]
fn sum_range_mul_double_computes_at_two_different_bounds() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rmul, rpow, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let base_two = literal(&mut d, 2);
    let base_three = literal(&mut d, 3);

    // f := fun i => 2^i,  g := fun j => 3^j.
    let f = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = rpow(&mut d, p, base_two, i);
        d.lam_fv(i_fv, nat, body)
    };
    let g = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = rpow(&mut d, p, base_three, j);
        d.lam_fv(j_fv, nat, body)
    };

    let two = d.num(2);
    let three = d.num(3);

    let proof = d.lemma(p.sum_range_mul_double, &[f, g, two, three]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_mul_double(f,g,2,3) should infer: {e:?}"));

    let sum_f = rsum_range(&mut d, p, f, two);
    let sum_g = rsum_range(&mut d, p, g, three);
    let lhs = rmul(&mut d, sum_f, sum_g);

    // Σ_{i<2} Σ_{j<3} f i * g j, rebuilt here from raw pieces.
    let double = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let gj = d.apply(g, &[j]);
        let cell = rmul(&mut d, fi, gj);
        let inner = d.lam_fv(j_fv, nat, cell);
        let row = rsum_range(&mut d, p, inner, three);
        d.lam_fv(i_fv, nat, row)
    };
    let rhs = rsum_range(&mut d, p, double, two);
    let expected = req(&mut d, lhs, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_mul_double(f,g,2,3) should state (Σ_{{i<2}} f i)·(Σ_{{j<3}} g j) \
         = Σ_{{i<2}} Σ_{{j<3}} f i · g j"
    );

    let thirty_nine = literal(&mut d, 39);
    assert!(
        d.kernel().def_eq(lhs, thirty_nine),
        "(2^0+2^1)·(3^0+3^1+3^2) must reduce to 3·13 = 39"
    );
    assert!(
        d.kernel().def_eq(rhs, thirty_nine),
        "the 2×3 rectangle of 2^i·3^j must reduce to the same 39"
    );

    assert!(
        d.kernel()
            .axiom_footprint(p.sum_range_mul_double)
            .is_empty(),
        "sumRange_mul_double must rest on zero axioms"
    );
}

/// `Rat.sumRange_mul_eq_diag_add_corner` at a concrete instance, **and the
/// naive corner-dropping identity refuted at that same instance**.
///
/// `f i := 2^i`, `g j := 3^j`, `n = 3`. By hand:
///
/// - product `(1+2+4)·(1+3+9) = 7·13 = 91`;
/// - antidiagonal triangle `Σ_{k<3} Σ_{i≤k} 2^i·3^(k−i)`
///   `= 1 + (3+2) + (9+6+4) = 1 + 5 + 19 = 25`;
/// - corner `Σ_{i<3} Σ_{k<i} 2^i·3^((3−i)+k)`
///   `= 0 + (2·3^2) + (4·3^1 + 4·3^2) = 18 + 48 = 66`;
/// - `25 + 66 = 91`.
///
/// **`n = 3` and not `n = 2`, deliberately.** At `n = 2` the corner is the
/// single cell `i = 1`, where `n − i = 1 = i` — so `g ((n−i)+k)` and
/// `g (i+k)` coincide there and the test cannot tell a transposed corner
/// index from the right one. That is exactly the vacuous-negative-control
/// trap: the "wrong" variant is literally the same term. At `n = 3` the
/// corner spans `i = 1` and `i = 2` with `n − i ∈ {2, 1}` against `i ∈
/// {1, 2}`, and the same transposition moves the corner from 66 to 150.
///
/// One symmetry no instance can break, stated so nobody looks for it:
/// `Σ_{i≤k} f i · g (k−i)` and `Σ_{i≤k} f (k−i) · g i` are the SAME sum
/// reindexed, so no choice of `f`, `g`, `n` separates them. That swap is
/// caught by reading the statement, not by computing it.
///
/// The corner is **most of the product** here, which is the point: the naive
/// finite Cauchy identity is not a small-error approximation, it is simply
/// false. The last assertion is that negative control — `91` and `25` are
/// distinct numerals, so it can be neither vacuous (the two sides are not the
/// same term) nor inverted (the dropped-corner identity is genuinely false at
/// this instance, not accidentally true).
#[test]
fn sum_range_mul_eq_diag_add_corner_computes_and_the_naive_identity_is_false() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rmul, rpow, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let base_two = literal(&mut d, 2);
    let base_three = literal(&mut d, 3);

    let f = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = rpow(&mut d, p, base_two, i);
        d.lam_fv(i_fv, nat, body)
    };
    let g = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = rpow(&mut d, p, base_three, j);
        d.lam_fv(j_fv, nat, body)
    };
    let three_n = d.num(3);

    let proof = d.lemma(p.sum_range_mul_eq_diag_add_corner, &[f, g, three_n]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_mul_eq_diag_add_corner(f,g,3) should infer: {e:?}"));

    let sum_f = rsum_range(&mut d, p, f, three_n);
    let sum_g = rsum_range(&mut d, p, g, three_n);
    let product = rmul(&mut d, sum_f, sum_g);

    // Σ_{k<2} Σ_{i<k+1} f i * g (k−i), rebuilt from raw pieces.
    let triangle = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let ki = d.sub(k, i);
        let gki = d.apply(g, &[ki]);
        let cell = rmul(&mut d, fi, gki);
        let inner = d.lam_fv(i_fv, nat, cell);
        let sk = d.succ(k);
        let row = rsum_range(&mut d, p, inner, sk);
        let t = d.lam_fv(k_fv, nat, row);
        rsum_range(&mut d, p, t, three_n)
    };
    // Σ_{i<2} Σ_{k<i} f i * g ((2−i)+k), rebuilt from raw pieces.
    let corner = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fi = d.apply(f, &[i]);
        let sub_ni = d.sub(three_n, i);
        let idx = d.add(sub_ni, k);
        let gidx = d.apply(g, &[idx]);
        let cell = rmul(&mut d, fi, gidx);
        let inner = d.lam_fv(k_fv, nat, cell);
        let row = rsum_range(&mut d, p, inner, i);
        let c = d.lam_fv(i_fv, nat, row);
        rsum_range(&mut d, p, c, three_n)
    };

    let rhs = radd(&mut d, triangle, corner);
    let expected = req(&mut d, product, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_mul_eq_diag_add_corner(f,g,3) should state product = triangle + corner"
    );

    let ninety_one = literal(&mut d, 91);
    let twenty_five = literal(&mut d, 25);
    let sixty_six = literal(&mut d, 66);
    assert!(
        d.kernel().def_eq(product, ninety_one),
        "(2^0+2^1+2^2)·(3^0+3^1+3^2) = 7·13 must reduce to 91"
    );
    assert!(
        d.kernel().def_eq(triangle, twenty_five),
        "the antidiagonal convolution Σ_{{k<3}} Σ_{{i≤k}} 2^i·3^(k−i) must reduce to 1+5+19 = 25"
    );
    assert!(
        d.kernel().def_eq(corner, sixty_six),
        "the corner Σ_{{i<3}} Σ_{{k<i}} 2^i·3^((3−i)+k) must reduce to 18+48 = 66"
    );

    // The negative control below is only worth anything if `def_eq` can tell
    // two distinct `Rat` numerals apart at all. Pin that here rather than
    // assuming it: a `def_eq` that said `true` for everything would make the
    // assertion after this one pass for the wrong reason.
    assert!(
        !d.kernel().def_eq(twenty_five, sixty_six),
        "def_eq must separate the distinct Rat numerals 25 and 66; if it does \
         not, the corner-dropping negative control below cannot fail either"
    );

    // THE NEGATIVE CONTROL. Dropping the corner -- the naive finite Cauchy
    // identity -- claims 91 = 25.
    assert!(
        !d.kernel().def_eq(product, triangle),
        "the corner-dropping identity must be FALSE here; if the product and the \
         convolution are def_eq at this instance then this test's f/g were chosen \
         badly and it proves nothing about the corner"
    );

    assert!(
        d.kernel()
            .axiom_footprint(p.sum_range_mul_eq_diag_add_corner)
            .is_empty(),
        "sumRange_mul_eq_diag_add_corner must rest on zero axioms"
    );
    assert!(
        d.kernel().axiom_footprint(p.sum_range_mul).is_empty(),
        "sumRange_mul must rest on zero axioms"
    );
}

/// `Rat.pow_add` and `Rat.pow_sub_add` at concrete arguments — the companion
/// the symbolic kernel acceptance does not give.
///
/// Both theorems are built over free `x`, `i`, `k`, so `add_declaration`
/// already checked them symbolically. Numerals reduce, and reduction hides
/// definitional-equality gaps; free variables get stuck, and stuck terms hide
/// transposed arguments and wrong hand-computed values. The two checks fail
/// on disjoint defect classes, so both are here.
///
/// `pow_add` at `x = 2, m = 2, n = 3`: `2^(2+3) = 32` and `2^2 · 2^3 = 4·8`.
/// A statement that had written `Nat.mul m n` where it means `Nat.add m n`
/// type-checks just as well and gives `2^6 = 64` — this separates them.
///
/// `pow_sub_add` at `x = 2, i = 1, k = 3`: `2^3 = 2^(3−1) · 2^1 = 4·2 = 8`.
/// Note `k − i = 2 ≠ i = 1` here, deliberately: at `i = 1, k = 2` the two
/// exponents would both be `1` and a transposed `sub k i` / `i` would be
/// invisible.
///
/// The `Nat.le i k` hypothesis is then shown to be load-bearing rather than
/// decorative: `Nat.sub` truncates, so at `i = 3 > k = 1` the conclusion
/// reads `2 = 2^(1−3) · 2^3 = 2^0 · 8 = 8`, and the kernel is asked to
/// confirm that `2` and `8` are NOT `def_eq`. A `pow_sub_add` stated without
/// the hypothesis would be unsound, and this is the instance that says so.
#[test]
fn pow_add_and_the_antidiagonal_cell_collapse_compute_at_concrete_arguments() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rmul, rpow};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let x = literal(&mut d, 2);
    let n1 = d.num(1);
    let n2 = d.num(2);
    let n3 = d.num(3);

    // --- pow_add(2, 2, 3) : 2^(2+3) = 2^2 * 2^3 -----------------------------
    let proof_add = d.lemma(p.pow_add, &[x, n2, n3]);
    let inferred_add = d
        .kernel()
        .infer(proof_add)
        .unwrap_or_else(|e| panic!("pow_add(2,2,3) should infer: {e:?}"));

    let sum_23 = d.add(n2, n3);
    let lhs_add = rpow(&mut d, p, x, sum_23);
    let pow_2 = rpow(&mut d, p, x, n2);
    let pow_3 = rpow(&mut d, p, x, n3);
    let rhs_add = rmul(&mut d, pow_2, pow_3);
    let expected_add = req(&mut d, lhs_add, rhs_add);
    assert!(
        d.kernel().def_eq(inferred_add, expected_add),
        "pow_add(2,2,3) should state 2^(2+3) = 2^2 · 2^3"
    );

    let thirty_two = literal(&mut d, 32);
    assert!(
        d.kernel().def_eq(lhs_add, thirty_two),
        "2^(2+3) must reduce to 32"
    );
    assert!(
        d.kernel().def_eq(rhs_add, thirty_two),
        "2^2 · 2^3 = 4·8 must reduce to the same 32"
    );
    // The exponent really is a SUM: 2^(2·3) would be 64, not 32.
    let sixty_four = literal(&mut d, 64);
    assert!(
        !d.kernel().def_eq(thirty_two, sixty_four),
        "def_eq must separate 32 from 64, or the check above cannot fail"
    );

    // --- pow_sub_add(2, 1, 3) : 1 <= 3 -> 2^3 = 2^(3-1) * 2^1 ---------------
    let nat = d.prelude();
    // `Nat.le 1 3`, built from the prelude's own order facts rather than
    // assumed: le_succ gives i <= succ i, le_trans chains two of them.
    let h_le = {
        let le_1_2 = d.lemma(nat.le_succ, &[n1]);
        let le_2_3 = d.lemma(nat.le_succ, &[n2]);
        d.lemma(nat.le_trans, &[n1, n2, n3, le_1_2, le_2_3])
    };
    let proof_sub = d.lemma(p.pow_sub_add, &[x, n1, n3, h_le]);
    let inferred_sub = d
        .kernel()
        .infer(proof_sub)
        .unwrap_or_else(|e| panic!("pow_sub_add(2,1,3,h) should infer: {e:?}"));

    let sub_31 = d.sub(n3, n1);
    let pow_k = rpow(&mut d, p, x, n3);
    let pow_sub = rpow(&mut d, p, x, sub_31);
    let pow_i = rpow(&mut d, p, x, n1);
    let rhs_sub = rmul(&mut d, pow_sub, pow_i);
    let expected_sub = req(&mut d, pow_k, rhs_sub);
    assert!(
        d.kernel().def_eq(inferred_sub, expected_sub),
        "pow_sub_add(2,1,3) should state 2^3 = 2^(3−1) · 2^1"
    );

    let eight = literal(&mut d, 8);
    assert!(d.kernel().def_eq(pow_k, eight), "2^3 must reduce to 8");
    assert!(
        d.kernel().def_eq(rhs_sub, eight),
        "2^(3−1) · 2^1 = 4·2 must reduce to the same 8"
    );

    // --- the hypothesis is load-bearing, not decoration ---------------------
    // At i = 3 > k = 1 truncated `Nat.sub` gives 1 − 3 = 0, so the
    // conclusion would read 2^1 = 2^0 · 2^3, i.e. 2 = 8.
    let sub_13 = d.sub(n1, n3);
    let pow_1 = rpow(&mut d, p, x, n1);
    let pow_trunc = rpow(&mut d, p, x, sub_13);
    let bad_rhs = rmul(&mut d, pow_trunc, pow_3);
    let two_r = literal(&mut d, 2);
    assert!(d.kernel().def_eq(pow_1, two_r), "2^1 must reduce to 2");
    assert!(
        d.kernel().def_eq(bad_rhs, eight),
        "truncation makes 2^(1−3) · 2^3 reduce to 2^0 · 8 = 8"
    );
    assert!(
        !d.kernel().def_eq(pow_1, bad_rhs),
        "pow_sub_add WITHOUT its `Nat.le i k` hypothesis would be false here \
         (2 = 8); if these are def_eq the hypothesis is not load-bearing and \
         this test proves nothing about it"
    );

    assert!(
        d.kernel().axiom_footprint(p.pow_add).is_empty(),
        "pow_add must rest on zero axioms"
    );
    assert!(
        d.kernel().axiom_footprint(p.pow_sub_add).is_empty(),
        "pow_sub_add must rest on zero axioms"
    );
}

// --- polynomials (`rat_prelude::polynomial`) --------------------------------

/// Every declaration `polynomial::declare_polynomial` adds — `Rat.pow`,
/// `Rat.polyEval`, and the six theorems built on them — is a **checked**
/// definition or theorem with an empty axiom footprint, read out of the
/// kernel, not off the diff. (`built()` already implies the kernel accepted
/// every one of these proofs — a failed `add_declaration` would have made
/// `build_rat_prelude` return `Err` and this helper's own `.expect` panic —
/// so this test's job is the *kind*/footprint check, not re-proving
/// acceptance.)
#[test]
fn the_polynomial_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("pow", p.pow, false),
        ("pow_zero", p.pow_zero, true),
        ("pow_succ", p.pow_succ, true),
        ("pow_add", p.pow_add, true),
        ("pow_sub_add", p.pow_sub_add, true),
        ("polyEval", p.poly_eval, false),
        ("polyEval_zero", p.poly_eval_zero, true),
        ("polyEval_succ", p.poly_eval_succ, true),
        ("polyEval_add", p.poly_eval_add, true),
        ("polyEval_smul", p.poly_eval_smul, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.pow` **computes**: `2^3 = 8`, by `Eq.refl` on concrete literals —
/// not by trusting `pow_succ`/`pow_zero` (proved symbolically, over opaque
/// `a`/`m`) to be about the definition this file actually declared.
#[test]
fn rat_pow_computes_on_a_concrete_literal() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let two = literal(&mut d, 2);
    let three_n = d.num(3);
    let power = rpow(&mut d, p, two, three_n);
    let eight = literal(&mut d, 8);
    let stmt = req(&mut d, power, eight);
    let proof = rrefl(&mut d, power);
    let name = d.kernel().name_str(anon, "Check.pow_two_cubed");
    d.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("Rat.pow did not reduce on 2^3: {}", d.explain(&e)));
}

/// The negative control for [`rat_pow_computes_on_a_concrete_literal`]:
/// `2^3 = 9` must be REFUSED, or the reduction check above measures nothing.
#[test]
fn rat_pow_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let two = literal(&mut d, 2);
    let three_n = d.num(3);
    let power = rpow(&mut d, p, two, three_n);
    let nine = literal(&mut d, 9);
    let stmt = req(&mut d, power, nine);
    let proof = rrefl(&mut d, power);
    let name = d.kernel().name_str(anon, "Check.pow_two_cubed_is_not_nine");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.pow 2 3 = 9`, so the pow reduction check proves nothing"
    );
}

/// **The mandatory concrete computation test.** `Rat.polyEval` evaluates the
/// linear polynomial `p(i) = 1 + 2i` (as the coefficient function `c 0 = 1`,
/// `c (succ _) = 2`, degree bound `n = 2`) at `x = 3`: `p(3) = 1·1 + 2·3 =
/// 7`, checked by `Eq.refl` alone — not by trusting `polyEval_zero`/
/// `polyEval_succ` (proved symbolically) to be about the definition this
/// file actually declared.
#[test]
fn rat_poly_eval_computes_a_concrete_polynomial() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rpoly_eval, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // c := fun i => Nat.rec (motive := fun _ => Rat) 1 (fun _ _ => 2) i,
    // i.e. c 0 = 1, c (succ _) = 2 — enough to fix c at the two indices
    // (0, 1) that a degree bound of 2 ever inspects.
    let coeffs = {
        let one_r = literal(&mut d, 1);
        let two_r = literal(&mut d, 2);
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, two_r);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, one_r, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let n = d.num(2);
    let x = literal(&mut d, 3);
    let evaluated = rpoly_eval(&mut d, p, coeffs, n, x);
    let seven = literal(&mut d, 7);
    let stmt = req(&mut d, evaluated, seven);
    let proof = rrefl(&mut d, evaluated);
    let name = d.kernel().name_str(anon, "Check.poly_eval_linear_at_three");
    d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
        panic!(
            "Rat.polyEval did not reduce to 7 on (1+2i) at x=3: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`rat_poly_eval_computes_a_concrete_polynomial`]: the same polynomial at
/// the same point evaluated against `8` instead of `7` must be REFUSED, or
/// the computation check above measures nothing.
#[test]
fn rat_poly_eval_computation_check_can_fail() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rpoly_eval, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let coeffs = {
        let one_r = literal(&mut d, 1);
        let two_r = literal(&mut d, 2);
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, two_r);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, one_r, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let n = d.num(2);
    let x = literal(&mut d, 3);
    let evaluated = rpoly_eval(&mut d, p, coeffs, n, x);
    let eight = literal(&mut d, 8);
    let stmt = req(&mut d, evaluated, eight);
    let proof = rrefl(&mut d, evaluated);
    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_linear_at_three_is_not_eight");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `polyEval (1+2i) 2 3 = 8`, so the polyEval computation \
         check proves nothing"
    );
}

// --- the finite Taylor expansion identity (`rat_prelude::taylor`) ----------

/// Every declaration `taylor::declare_taylor` adds — `Rat.pow_one`,
/// `Rat.add_sub_cancel_left`, `Rat.sq_sub_sq`, `Rat.polyEval_deg1`, and
/// `Rat.taylor_deg1` — is a checked `Theorem` with an empty axiom footprint,
/// read out of the kernel (`built()` already implies the kernel accepted
/// every one of these proofs — a rejection would have made
/// `build_rat_prelude` return `Err` and `built()`'s own `.expect` panic, so
/// this test's job is the *kind*/footprint check, not re-proving
/// acceptance).
#[test]
fn the_taylor_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("pow_one", p.pow_one),
        ("add_sub_cancel_left", p.add_sub_cancel_left),
        ("sq_sub_sq", p.sq_sub_sq),
        ("polyEval_deg1", p.poly_eval_deg1),
        ("taylor_deg1", p.taylor_deg1),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// A local `fun i => Nat.rec … i` two-term coefficient function, built the
/// same way [`super::taylor`]'s own (private) `coeff2` is — mirroring
/// [`rat_poly_eval_computes_a_concrete_polynomial`]'s own inline
/// construction rather than reaching across the module boundary for a
/// helper this file has no access to.
fn concrete_coeff2(d: &mut crate::int_prelude::ops::IntDev<'_>, c0: ExprId, c1: ExprId) -> ExprId {
    use crate::BinderInfo;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_ty;

    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let anon_binder = d.anon_name();
    let one_level = d.level_one();
    let motive = d
        .kernel()
        .lam(anon_binder, nat, carrier, BinderInfo::Default);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let inner = d.lam_fv(ih_fv, carrier, c1);
        d.lam_fv(j_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, c0, minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// **The mandatory concrete instantiation.** `Rat.taylor_deg1` applied at
/// `c0 = 2, c1 = 3, x = 7, a = 5` — the polynomial `p(t) = 2 + 3t` — must,
/// once every `Rat` operation in its conclusion reduces on these literals,
/// assert `Eq Rat 23 23`: `p(7) = 2 + 21 = 23` and `p(5) + 3·(7−5) = 17 + 6 =
/// 23`. This is not re-checking that the kernel accepted `taylor_deg1` (it
/// already did, or `built()` would have panicked) — it is checking that the
/// theorem's *content*, not just its shape, is the identity claimed: a
/// swapped `x`/`a` or a dropped factor of `c1` would still type-check
/// symbolically but would make this concrete instantiation reduce to a
/// wrong pair of numerals, which the declared `Eq Rat 23 23` statement below
/// would then fail to accept by defeq.
#[test]
fn taylor_deg1_computes_at_a_concrete_linear_polynomial() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let c0 = literal(&mut d, 2);
    let c1 = literal(&mut d, 3);
    let x = literal(&mut d, 7);
    let a = literal(&mut d, 5);
    let twenty_three = literal(&mut d, 23);

    let proof = d.lemma(p.taylor_deg1, &[c0, c1, x, a]);
    let stmt = req(&mut d, twenty_three, twenty_three);
    let name = d
        .kernel()
        .name_str(anon, "Check.taylor_deg1_two_plus_three_t_at_seven_and_five");
    d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
        panic!(
            "Rat.taylor_deg1 did not reduce to `23 = 23` on p(t)=2+3t, x=7, a=5: {}",
            d.explain(&e)
        )
    });

    // A pure sanity cross-check, independent of `taylor_deg1`: the same
    // polynomial computed directly via `polyEval` reduces to the same 23,
    // by `Eq.refl` alone (mirrors `rat_poly_eval_computes_a_concrete_polynomial`).
    let coeffs = concrete_coeff2(&mut d, c0, c1);
    let two_n = d.num(2);
    let evaluated = crate::rat_prelude::ops::rpoly_eval(&mut d, p, coeffs, two_n, x);
    let direct_stmt = req(&mut d, evaluated, twenty_three);
    let direct_proof = rrefl(&mut d, evaluated);
    let direct_name = d
        .kernel()
        .name_str(anon, "Check.taylor_deg1_direct_poly_eval_cross_check");
    d.declare_theorem(direct_name, direct_stmt, direct_proof)
        .unwrap_or_else(|e| {
            panic!(
                "direct polyEval(2+3t, 7) did not reduce to 23: {}",
                d.explain(&e)
            )
        });
}

/// **Negative control**, both ways at once, for
/// [`taylor_deg1_computes_at_a_concrete_linear_polynomial`]: swapping `x`
/// and `a` in the DECLARED statement (while leaving the proof — the genuine
/// `taylor_deg1` application at the ORIGINAL `x`, `a` — unchanged) must be
/// REFUSED. If this were accepted, the concrete check above would be
/// vacuous: it would mean the kernel accepts `Eq Rat 23 23` no matter which
/// literals were actually fed to the theorem, which is not what the
/// positive test is supposed to be measuring.
#[test]
fn taylor_deg1_concrete_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let c0 = literal(&mut d, 2);
    let c1 = literal(&mut d, 3);
    let x = literal(&mut d, 7);
    let a = literal(&mut d, 5);
    let twenty_three = literal(&mut d, 23);
    let seventeen = literal(&mut d, 17);

    // The real theorem, at the real point (x=7): concludes `... = 23`, not
    // `... = 17` (which is `p(5)` itself, the value at `a`, not at `x`).
    let proof = d.lemma(p.taylor_deg1, &[c0, c1, x, a]);
    let stmt = req(&mut d, twenty_three, seventeen);
    let name = d
        .kernel()
        .name_str(anon, "Check.taylor_deg1_twenty_three_is_not_seventeen");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `23 = 17` from `taylor_deg1`, so the concrete \
         instantiation check above proves nothing"
    );

    // And directly: `polyEval` of `2+3t` at `t=7` is not `17`.
    let coeffs = concrete_coeff2(&mut d, c0, c1);
    let two_n = d.num(2);
    let evaluated = crate::rat_prelude::ops::rpoly_eval(&mut d, p, coeffs, two_n, x);
    let direct_stmt = req(&mut d, evaluated, seventeen);
    let direct_proof = rrefl(&mut d, evaluated);
    let direct_name = d
        .kernel()
        .name_str(anon, "Check.taylor_deg1_direct_poly_eval_is_not_seventeen");
    assert!(
        d.declare_theorem(direct_name, direct_stmt, direct_proof)
            .is_err(),
        "the kernel accepted `polyEval(2+3t,7) = 17`, so the direct cross-check \
         above proves nothing"
    );
}

/// **Concrete check for [`RatPrelude::sq_sub_sq`].** `5² − 3² = (5−3)·(5+3)`:
/// `25 − 9 = 16` and `2·8 = 16`. Applying the general (symbolic) theorem at
/// these literals and asserting the result equals `Eq Rat 16 16` catches a
/// swapped `x`/`a` or a sign error that a symbolic-only check would miss.
#[test]
fn sq_sub_sq_computes_at_five_and_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::req;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let x = literal(&mut d, 5);
    let a = literal(&mut d, 3);
    let sixteen = literal(&mut d, 16);

    let proof = d.lemma(p.sq_sub_sq, &[x, a]);
    let stmt = req(&mut d, sixteen, sixteen);
    let name = d.kernel().name_str(anon, "Check.sq_sub_sq_five_three");
    d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
        panic!(
            "Rat.sq_sub_sq did not reduce to `16 = 16` at x=5, a=3: {}",
            d.explain(&e)
        )
    });
}

/// Negative control for [`sq_sub_sq_computes_at_five_and_three`]: `16` is
/// not `15`.
#[test]
fn sq_sub_sq_concrete_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::req;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let x = literal(&mut d, 5);
    let a = literal(&mut d, 3);
    let sixteen = literal(&mut d, 16);
    let fifteen = literal(&mut d, 15);

    let proof = d.lemma(p.sq_sub_sq, &[x, a]);
    let stmt = req(&mut d, sixteen, fifteen);
    let name = d
        .kernel()
        .name_str(anon, "Check.sq_sub_sq_sixteen_is_not_fifteen");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `16 = 15` from `sq_sub_sq`, so the concrete check above \
         proves nothing"
    );
}

// --- `Rat.pow_natDivSucc_two` (`rat_prelude::pow_bridge`) -------------------

/// `Rat.pow_natDivSucc_two` is a checked `Theorem` with an empty axiom
/// footprint, read out of the kernel (`built()` already implies the kernel
/// accepted the proof — a rejection would have made `build_rat_prelude`
/// return `Err` and `built()`'s own `.expect` panic, so this test's job is
/// the *kind*/footprint check, not re-proving acceptance).
#[test]
fn the_pow_bridge_is_axiom_free() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.pow_nat_div_succ_two)
        .expect("Rat.pow_natDivSucc_two was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Rat.pow_natDivSucc_two must be a checked Theorem, found a different kind"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.pow_nat_div_succ_two)
        .into_iter()
        .map(|entry| kernel.display_name(entry).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Rat.pow_natDivSucc_two rests on {footprint:?}"
    );
}

/// **The mandatory concrete computation test**, on BOTH sides of the bridge
/// independently: `Rat.pow (Rat.natDivSucc 1 1) 3` (repeated multiplication
/// of `1/2`) and `Rat.normalize 1 (2^3) _` (the direct `1/8`) each reduce,
/// by `Eq.refl` alone, to the SAME literal `Rat.natDivSucc 1 7` (`1/8`).
/// This does not use `Rat.pow_natDivSucc_two` at all, so it cannot be fooled
/// by a bridge that type-checks but relates the wrong two things.
#[test]
fn pow_nat_div_succ_two_sides_compute_to_one_eighth() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{normalize, req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let one_nat = d.num(1);
    let g = d.const_app(p.nat_div_succ, &[one_nat, one_nat]);
    let three_n = d.num(3);
    let pow_g_3 = rpow(&mut d, p, g, three_n);
    let seven_nat = d.num(7);
    let one_eighth = d.const_app(p.nat_div_succ, &[one_nat, seven_nat]);

    // Side 1: `pow g 3` reduces to `natDivSucc 1 7`.
    {
        let stmt = req(&mut d, pow_g_3, one_eighth);
        let proof = rrefl(&mut d, pow_g_3);
        let name = d
            .kernel()
            .name_str(anon, "Check.pow_half_cubed_is_one_eighth");
        d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
            panic!(
                "Rat.pow (natDivSucc 1 1) 3 did not reduce to 1/8: {}",
                d.explain(&e)
            )
        });
    }

    // Side 2: `normalize 1 (2^3) _` also reduces to `natDivSucc 1 7`.
    {
        let two = d.num(2);
        let pow2_3 = d.pow(two, three_n);
        let one_int = d.of_nat(one_nat);
        let nat = p.int.nat;
        let two_pos = d.lemma(nat.le_succ, &[one_nat]);
        let pow_pos_fn = d.lemma(nat.pow_pos, &[two, three_n]);
        let w = d.apply(pow_pos_fn, &[two_pos]);
        let target_3 = normalize(&mut d, one_int, pow2_3, w);
        let stmt = req(&mut d, target_3, one_eighth);
        let proof = rrefl(&mut d, target_3);
        let name = d
            .kernel()
            .name_str(anon, "Check.normalize_one_two_cubed_is_one_eighth");
        d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
            panic!(
                "Rat.normalize 1 (2^3) _ did not reduce to 1/8: {}",
                d.explain(&e)
            )
        });
    }
}

/// The negative control for the check above: `pow (natDivSucc 1 1) 3 =
/// natDivSucc 1 6` (i.e. `1/8 = 1/7`) must be REFUSED, or the reduction
/// check proves nothing.
#[test]
fn pow_nat_div_succ_two_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let one_nat = d.num(1);
    let g = d.const_app(p.nat_div_succ, &[one_nat, one_nat]);
    let three_n = d.num(3);
    let pow_g_3 = rpow(&mut d, p, g, three_n);
    let six_nat = d.num(6);
    let one_seventh = d.const_app(p.nat_div_succ, &[one_nat, six_nat]);
    let stmt = req(&mut d, pow_g_3, one_seventh);
    let proof = rrefl(&mut d, pow_g_3);
    let name = d
        .kernel()
        .name_str(anon, "Check.pow_half_cubed_is_not_one_seventh");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.pow (natDivSucc 1 1) 3 = natDivSucc 1 6`, so the \
         reduction check proves nothing"
    );
}

/// **The mandatory symbolic-construction cross-check.** `Rat.pow_natDivSucc_two`,
/// applied at the SAME concrete `n = 3` used above, must have exactly the type
/// `Eq Rat (pow g 3) (target 3)` built independently of the theorem's own
/// (symbolic) proof — confirming the general theorem is genuinely about this
/// value and not some other pair that merely happens to type-check for every
/// `n` it was tried at (the failure mode `creal/exponential.rs`'s own module
/// note in this crate's `CLAUDE.md` warns concrete-only testing can hide).
#[test]
fn pow_nat_div_succ_two_matches_its_general_theorem_at_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{normalize, req, rpow};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let one_nat = d.num(1);
    let g = d.const_app(p.nat_div_succ, &[one_nat, one_nat]);
    let three_n = d.num(3);
    let pow_g_3 = rpow(&mut d, p, g, three_n);

    let two = d.num(2);
    let pow2_3 = d.pow(two, three_n);
    let one_int = d.of_nat(one_nat);
    let nat = p.int.nat;
    let two_pos = d.lemma(nat.le_succ, &[one_nat]);
    let pow_pos_fn = d.lemma(nat.pow_pos, &[two, three_n]);
    let w = d.apply(pow_pos_fn, &[two_pos]);
    let target_3 = normalize(&mut d, one_int, pow2_3, w);

    let expected_ty = req(&mut d, pow_g_3, target_3);
    let instantiated = d.lemma(p.pow_nat_div_succ_two, &[three_n]);
    let name = d
        .kernel()
        .name_str(anon, "Check.pow_bridge_at_three_matches_expected_type");
    d.declare_theorem(name, expected_ty, instantiated)
        .unwrap_or_else(|e| {
            panic!(
                "Rat.pow_natDivSucc_two at n=3 has a different type than expected: {}",
                d.explain(&e)
            )
        });
}

/// `polyEval_mul` (the finite Cauchy product) is NOT attempted in this
/// prelude, and this test is the kernel-confirmed reason why: the natural
/// candidate statement `polyEval (conv a b) (m+n-1) x = polyEval a m x *
/// polyEval b n x`, with `conv a b k := sumRange (fun i => a i * b (k-i))
/// (k+1)` the plain (untruncated) antidiagonal formula, is FALSE for
/// `a`/`b` that are not required to vanish beyond their own bound.
///
/// Take `a 0 = 1`, `a (succ _) = 5` (so `m = 2` means "`a`'s declared
/// coefficients are `1, 5`"), and `b 0 = 3`, `b (succ _) = 100` (`n = 1`
/// means "`b`'s declared coefficient is `3`"; `b 1 = 100` is `b`'s value
/// PAST its declared bound — `polyEval b 1 x` never looks at it, but nothing
/// stops it being nonzero). The truncated rectangle product's `x^1`
/// coefficient is `a 1 * b 0 = 5*3 = 15`. But `conv a b 1` — the coefficient
/// `polyEval_mul` would need to equal `15` — is `a 0 * b 1 + a 1 * b 0 =
/// 1*100 + 5*3 = 115`: `conv` sums the FULL antidiagonal `{(i,j) : i+j=1}`,
/// which includes `(0,1)`, a point OUTSIDE the `m×n` rectangle `{i<2,j<1}`
/// (since `j=1 ≥ n=1`). `conv`'s own formula is correct (it is exactly the
/// infinite-power-series Cauchy product, confirmed positively below); the
/// gap is that it is not, by itself, the TRUNCATED product `polyEval_mul`
/// would need — that needs either an extra hypothesis (`a`/`b` vanish beyond
/// `m`/`n`) or a `conv` bounded by BOTH `m` and `n` (not the same-bound `n×n`
/// square `rat_prelude/diagonal.rs` supplies), neither built here.
#[test]
fn naive_conv_disagrees_with_the_truncated_rectangle_product() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // A step function `Nat -> Rat`, `f 0 = at_zero`, `f (succ _) = beyond`,
    // via `Nat.rec` -- exactly `rat_poly_eval_computes_a_concrete_polynomial`'s
    // own `coeffs` builder, reused for both `a` and `b`.
    let step = |d: &mut IntDev<'_>, at_zero: ExprId, beyond: ExprId| -> ExprId {
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, beyond);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, at_zero, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let one_r = literal(&mut d, 1);
    let five_r = literal(&mut d, 5);
    let a = step(&mut d, one_r, five_r); // a 0 = 1, a 1 = 5

    let three_r = literal(&mut d, 3);
    let hundred_r = literal(&mut d, 100);
    let b = step(&mut d, three_r, hundred_r); // b 0 = 3, b 1 = 100 (junk beyond n=1)

    // conv a b k := sumRange (fun i => a i * b (k-i)) (k+1), built inline
    // (not a named `Rat.conv` -- this test does not commit to that shape
    // being the right one, per the module doc above).
    let conv = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, k: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ai = d.apply(a, &[i]);
        let ki = d.sub(k, i);
        let bki = d.apply(b, &[ki]);
        let term = rmul(d, ai, bki);
        let inner = d.lam_fv(i_fv, nat, term);
        let sk = d.succ(k);
        rsum_range(d, p, inner, sk)
    };

    // Positive control: conv's OWN antidiagonal formula computes correctly
    // (the "re-verify i<=k, so no truncation fires" check the task asked
    // for, at a third concrete instance beyond k=0,1,2 symbolic hand-check).
    let zero_n = d.zero();
    let conv_0 = conv(&mut d, a, b, zero_n);
    let expected_0 = literal(&mut d, 3); // a0*b0 = 1*3
    let stmt0 = req(&mut d, conv_0, expected_0);
    let proof0 = rrefl(&mut d, conv_0);
    let name0 = d.kernel().name_str(anon, "Check.conv_k0_is_three");
    d.declare_theorem(name0, stmt0, proof0)
        .unwrap_or_else(|e| panic!("conv(a,b,0) did not reduce to 3: {}", d.explain(&e)));

    let one_n = d.num(1);
    let conv_1 = conv(&mut d, a, b, one_n);
    let expected_1 = literal(&mut d, 115); // a0*b1 + a1*b0 = 100 + 15
    let stmt1 = req(&mut d, conv_1, expected_1);
    let proof1 = rrefl(&mut d, conv_1);
    let name1 = d.kernel().name_str(anon, "Check.conv_k1_is_115");
    d.declare_theorem(name1, stmt1, proof1)
        .unwrap_or_else(|e| panic!("conv(a,b,1) did not reduce to 115: {}", d.explain(&e)));

    // Negative control -- THE FINDING: conv(a,b,1) is NOT the truncated
    // rectangle coefficient a1*b0 = 15. If it were, `polyEval_mul`'s naive
    // statement (no vanishing-beyond-bound hypotheses on a/b) would be
    // provable as stated; it is not.
    let conv_1_again = conv(&mut d, a, b, one_n);
    let fifteen = literal(&mut d, 15);
    let wrong_stmt = req(&mut d, conv_1_again, fifteen);
    let wrong_proof = rrefl(&mut d, conv_1_again);
    let wrong_name = d.kernel().name_str(anon, "Check.conv_k1_is_not_fifteen");
    assert!(
        d.declare_theorem(wrong_name, wrong_stmt, wrong_proof)
            .is_err(),
        "the kernel accepted conv(a,b,1) = 15 (the truncated rectangle \
         coefficient a1*b0), but conv(a,b,1) = 115 (a0*b1+a1*b0) since conv \
         sums the FULL antidiagonal including the out-of-rectangle point \
         (0,1) -- so the naive polyEval_mul statement is not merely \
         unattempted here, it is false as stated without extra hypotheses"
    );
}

/// `dotN_cauchy_schwarz`'s statement rendered verbatim — SQUARED, the
/// unweakened form: `(dotN u v n) * (dotN u v n) <= (dotN u u n) * (dotN v v
/// n)`, not `|dotN u v n| <= sqrt(...)` (ℚ has no square root). The same
/// pinning discipline
/// [`the_order_completeness_statements_are_the_unweakened_ones`] uses for
/// `le_antisymm`/`lt_trichotomy`.
#[test]
fn the_cauchy_schwarz_statement_is_squared() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.dot_n_cauchy_schwarz),
        "((x0 : ((x0 : AxNat) -> Rat)) -> ((x1 : ((x1 : AxNat) -> Rat)) -> ((x2 : AxNat) -> \
         Rat.le (Rat.mul (Rat.dotN x0 x1 x2) (Rat.dotN x0 x1 x2)) \
         (Rat.mul (Rat.dotN x0 x0 x2) (Rat.dotN x1 x1 x2)))))"
    );
}

// --- `Rat.dotN`: the n-dimensional dot product (`rat_prelude::vector`) ----

/// Every declaration `vector::declare_vector` adds — `Rat.dotN` itself and
/// the six theorems built on it — is a **checked** definition or theorem
/// with an empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_vector_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("dotN", p.dot_n, false),
        ("dotN_zero", p.dot_n_zero, true),
        ("dotN_succ", p.dot_n_succ, true),
        ("dotN_comm", p.dot_n_comm, true),
        ("dotN_add_left", p.dot_n_add_left, true),
        ("dotN_smul_left", p.dot_n_smul_left, true),
        ("dotN_self_nonneg", p.dot_n_self_nonneg, true),
        ("dotN_two", p.dot_n_two, true),
        ("dotN_cauchy_schwarz", p.dot_n_cauchy_schwarz, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

// --- Bernoulli's inequality and the harmonic power bound
// (`rat_prelude::bernoulli`) -------------------------------------------------

/// `Rat.bernoulli` and `Rat.bernoulli_harmonic_bound` are each a **checked**
/// theorem with an empty axiom footprint, read out of the kernel, not off
/// the diff.
#[test]
fn the_bernoulli_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("bernoulli", p.bernoulli),
        ("bernoulli_harmonic_bound", p.bernoulli_harmonic_bound),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **The mandatory concrete computation test.** Bernoulli at `t = 1, n = 3`:
/// `(1+1)^3 = 8 ≥ 1 + 3·1 = 4` -- `n = 3` (not `0` or `1`, where the
/// inequality holds with equality and cannot detect a wrong direction).
/// Applies `Rat.bernoulli` to concrete literals and checks the resulting
/// proof's INFERRED type against an independently built
/// `Rat.le (natDivSucc 4 0) (natDivSucc 8 0)` -- not by trusting the
/// induction (proved symbolically, over an opaque `t`/`n`) to be about the
/// definition this file actually declared.
#[test]
fn rat_bernoulli_holds_at_t_one_n_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rle;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let one = literal(&mut d, 1);
    let three = d.num(3);
    let one_nat = d.num(1);
    let zero_idx = d.num(0);
    let h = d.lemma(p.zero_le_nat_div_succ, &[one_nat, zero_idx]); // 0 ≤ 1
    let proof = d.lemma(p.bernoulli, &[one, h, three]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("Rat.bernoulli(1, _, 3) should infer: {e:?}"));

    let four = literal(&mut d, 4);
    let eight = literal(&mut d, 8);
    let expected = rle(&mut d, p, four, eight);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "Rat.bernoulli at t=1, n=3 should state `Rat.le 4 8` (companion `L 1 3` \
         reduces to 4, `pow 2 3` reduces to 8)"
    );
    assert!(
        !d.kernel().def_eq(four, eight),
        "4 and 8 must not be defeq, or this test cannot tell a wrong bound from a vacuous one"
    );
}

/// The harmonic bound at a concrete instance: `x = 1/2`, `t = 1` (so
/// `1/x = 1+t`, matching the task's own worked translation), `m = 3`:
/// `(1+3·1)·(1/2)³ = 4·(1/8) = 1/2 ≤ 1`. The hypothesis `x·(1+t) ≤ 1`
/// becomes `(1/2)·2 ≤ 1`, i.e. `Rat.le one one` up to ground reduction, so
/// [`RatPrelude::le_refl`] at `one` already has the needed type by `def_eq`
/// -- exactly the same reduction [`rat_bernoulli_holds_at_t_one_n_three`]
/// relies on, applied to the hypothesis instead of the conclusion.
#[test]
fn rat_bernoulli_harmonic_bound_holds_at_x_half_t_one_m_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rle;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32, j: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(j);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let half = literal(&mut d, 1, 1); // 1/2
    let one = literal(&mut d, 1, 0); // 1/1
    let three_n = d.num(3);

    let one_nat = d.num(1);
    let half_idx = d.num(1);
    let hx = d.lemma(p.zero_le_nat_div_succ, &[one_nat, half_idx]); // 0 ≤ 1/2
    let one_nat2 = d.num(1);
    let zero_idx = d.num(0);
    let ht = d.lemma(p.zero_le_nat_div_succ, &[one_nat2, zero_idx]); // 0 ≤ 1
    let hxt = d.lemma(p.le_refl, &[one]); // le one one, defeq to `le (half*(1+1)) one`

    let proof = d.lemma(
        p.bernoulli_harmonic_bound,
        &[half, one, hx, ht, hxt, three_n],
    );
    let inferred = d.kernel().infer(proof).unwrap_or_else(|e| {
        panic!("Rat.bernoulli_harmonic_bound(1/2, 1, _, _, _, 3) should infer: {e:?}")
    });

    let expected = rle(&mut d, p, half, one);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "Rat.bernoulli_harmonic_bound at x=1/2, t=1, m=3 should state `Rat.le 1/2 1` \
         (companion `L 1 3` reduces to 4, `pow (1/2) 3` reduces to 1/8, and 4*(1/8) \
         reduces to 1/2)"
    );
    assert!(
        !d.kernel().def_eq(one, half),
        "1/2 and 1 must not be defeq, or this test cannot tell a wrong bound from a vacuous one"
    );
}

// --- `Rat.matMul`: matrices at symbolic dimension (`rat_prelude::matrix_n`) --

/// Every declaration `matrix_n::declare_matrix_n` adds is a **checked**
/// definition or theorem with an empty axiom footprint, read out of the
/// kernel rather than off the diff.
#[test]
fn the_matrix_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("matMul", p.mat_mul, false),
        ("matMul_zero", p.mat_mul_zero, true),
        ("matMul_succ", p.mat_mul_succ, true),
        ("matMul_assoc", p.mat_mul_assoc, true),
        ("matMul_add_left", p.mat_mul_add_left, true),
        ("matMul_add_right", p.mat_mul_add_right, true),
        ("matMul_smul_left", p.mat_mul_smul_left, true),
        ("sumRange_delta", p.sum_range_delta, true),
        ("matId", p.mat_id, false),
        ("matId_diag", p.mat_id_diag, true),
        ("matId_off_diag", p.mat_id_off_diag, true),
        ("matMul_id_left", p.mat_mul_id_left, true),
        ("matMul_id_right", p.mat_mul_id_right, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `matMul_assoc`'s statement rendered verbatim, pinning that it is
/// **pointwise** — the conclusion is an `Eq` at `Rat` between two *applied*
/// products, never an `Eq` between two `AxNat -> AxNat -> Rat` values.
///
/// This kernel has no `funext`, so a function-valued equation would not be
/// provable; the pin exists so a later edit cannot quietly restate it that
/// way and leave the module doc's `funext` argument describing something that
/// is no longer true. Same discipline as
/// [`the_cauchy_schwarz_statement_is_squared`].
#[test]
fn the_matrix_associativity_statement_is_pointwise() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    let statement = rendered(&mut kernel, p.mat_mul_assoc);
    assert_eq!(
        statement,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         ((x1 : ((x1 : AxNat) -> ((x2 : AxNat) -> Rat))) -> \
         ((x2 : ((x2 : AxNat) -> ((x3 : AxNat) -> Rat))) -> \
         ((x3 : AxNat) -> ((x4 : AxNat) -> ((x5 : AxNat) -> ((x6 : AxNat) -> \
         Eq.{1} Rat (Rat.matMul (Rat.matMul x0 x1 x3) x2 x4 x5 x6) \
         (Rat.matMul x0 (Rat.matMul x1 x2 x4) x3 x5 x6))))))))"
    );
}

// --- `Rat.matTranspose`: matrix transpose at symbolic dimension
// (`rat_prelude::matrix_transpose`) -- graded family (ADR-0603, ADR-0716,
// ADR-0825): row 1 `matTranspose_mul` (general n), no row 2 (the statement
// has no comparison or search, ADR-0716), row 3 `matTranspose_mul_example`
// (the SAME declaration applied at concrete numerals, ADR-0825's collapse).

/// Every declaration `matrix_transpose::declare_matrix_transpose` adds is a
/// **checked** definition or theorem with an empty axiom footprint, read out
/// of the kernel rather than off the diff -- same discipline as
/// [`the_matrix_toolkit_is_axiom_free`].
#[test]
fn the_matrix_transpose_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("matTranspose", p.mat_transpose, false),
        ("matTranspose_transpose", p.mat_transpose_transpose, true),
        ("matTranspose_mul", p.mat_transpose_mul, true),
        (
            "matTranspose_eval_example",
            p.mat_transpose_eval_example,
            true,
        ),
        (
            "matTranspose_mul_example",
            p.mat_transpose_mul_example,
            true,
        ),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `matTranspose_transpose`'s statement rendered verbatim -- pins that the
/// involution law is stated pointwise too (`… i j = A i j`, `A` applied
/// directly, never an `Eq` between two matrices).
#[test]
fn the_matrix_transpose_involution_statement_is_pointwise() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    let statement = rendered(&mut kernel, p.mat_transpose_transpose);
    assert_eq!(
        statement,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Eq.{1} Rat (Rat.matTranspose (Rat.matTranspose x0) x1 x2) (x0 x1 x2))))"
    );
}

/// `matTranspose_mul`'s statement rendered verbatim, pinning that it is
/// **pointwise** -- the conclusion is an `Eq` at `Rat` between two *applied*
/// scalar entries, never an `Eq` between two `AxNat -> AxNat -> Rat` values.
/// Same discipline as [`the_matrix_associativity_statement_is_pointwise`],
/// for the same reason: this kernel has no `funext`.
#[test]
fn the_matrix_transpose_mul_statement_is_pointwise() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    let statement = rendered(&mut kernel, p.mat_transpose_mul);
    assert_eq!(
        statement,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         ((x1 : ((x1 : AxNat) -> ((x2 : AxNat) -> Rat))) -> \
         ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : AxNat) -> \
         Eq.{1} Rat (Rat.matTranspose (Rat.matMul x0 x1 x2) x3 x4) \
         (Rat.matMul (Rat.matTranspose x1) (Rat.matTranspose x0) x2 x3 x4))))))"
    );
}

/// The kernel's unary-`Nat` rendering of `succ^n zero`, e.g. `n = 2` renders
/// as `AxNat.succ (AxNat.succ AxNat.zero)` -- every numeral in this prelude
/// is unary (no `funext`, no binary literal fast path in the source
/// preludes), so a pinned numeral must be built the same way rather than as
/// a decimal string.
fn nat_succ_chain(n: u32) -> String {
    if n == 0 {
        "AxNat.zero".to_string()
    } else if n == 1 {
        "AxNat.succ AxNat.zero".to_string()
    } else {
        format!("AxNat.succ ({})", nat_succ_chain(n - 1))
    }
}

/// `(Rat.ofInt (Int.ofNat succ^n zero))`, as it appears when this expression
/// is itself a compound argument to a surrounding application (e.g. the RHS
/// of a top-level `Eq`) -- both examples below place it exactly there.
fn rat_of_int_numeral(n: u32) -> String {
    format!("(Rat.ofInt (Int.ofNat ({})))", nat_succ_chain(n))
}

/// `matTranspose_eval_example` and `matTranspose_mul_example` are admitted
/// with the CONCRETE numeral types their module doc claims -- catches a
/// silently-vacuous statement (e.g. an `expected` that got rewritten to
/// match whatever the term happens to reduce to) that a footprint check
/// cannot see, since a wrong concrete numeral has exactly the same empty
/// footprint as the right one.
#[test]
fn the_matrix_transpose_examples_state_the_expected_numerals() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    // `nat_succ_chain(k)` is a literal PREFIX of `nat_succ_chain(n)` for any
    // `k < n` (unary numerals nest), so the only sound discriminating check
    // is the POSITIVE one: if the kernel had reduced to the wrong value (3,
    // the un-swapped entry; 121, the wrong transpose-of-product order), the
    // LONGER correct chain (5; 174) could not appear as a substring of the
    // SHORTER wrong one. A `!contains(3)`-style negative check would be
    // unsound here (chain(3) is a genuine substring of chain(5)), which is
    // why there is no such assertion below.
    let eval_example = rendered(&mut kernel, p.mat_transpose_eval_example);
    let expected_five = rat_of_int_numeral(5);
    assert!(
        eval_example.contains(&expected_five),
        "matTranspose_eval_example must state its RHS as the numeral 5 \
         (A(1,0), not A(0,1) = 3 -- the discriminating pair): {eval_example}"
    );
    let mul_example = rendered(&mut kernel, p.mat_transpose_mul_example);
    let expected_174 = rat_of_int_numeral(174);
    assert!(
        mul_example.contains(&expected_174),
        "matTranspose_mul_example must state its RHS as the numeral 174, \
         independently computed as A(1,0)*B(0,0) + A(1,1)*B(1,0) = \
         5*11 + 7*17 (and not 121, A^T B^T's wrong-order (0,1) entry): \
         {mul_example}"
    );
}

/// **The mandatory concrete computation test for `Rat.matMul`.** The kernel
/// type-checks a `Definition` and cannot tell you it computes the wrong
/// value, so the product is evaluated at concrete `2 x 2` matrices and every
/// one of the four output cells is compared against a hand computation.
///
/// The two matrices are given by closed formulas in `i` and `j` so no case
/// split is needed, and they are chosen to DISCRIMINATE — neither is
/// symmetric, they are not equal, and the four product cells are pairwise
/// distinct, so a transposed index in either factor changes at least one
/// checked value:
///
/// ```text
///   A i j = (i + i + j + 1) / 1        B i j = (i + j + j) / 1
///   A = [ 1  2 ]                       B = [ 0  2 ]
///       [ 3  4 ]                           [ 1  3 ]
///
///   A*B (0,0) = 1*0 + 2*1 =  2   (0,1) = 1*2 + 2*3 =  8
///       (1,0) = 3*0 + 4*1 =  4   (1,1) = 3*2 + 4*3 = 18
/// ```
///
/// The three transposition bugs this separates, each at cell `(0,0)`:
/// `A^T B` gives `1*0 + 3*1 = 3`, `A B^T` gives `1*0 + 2*2 = 4`, and `B A`
/// gives `0*1 + 2*3 = 6` — none of them `2`. The last is pinned as an
/// explicit negative control below, because `A*B` and `B*A` happen to agree
/// at cell `(0,1)` (both `8`) and a control placed there would be vacuous.
///
/// Magnitudes are kept under 20: every `Rat` numeral in this kernel is a
/// unary `Nat`, so `Rat.normalize`'s gcd runs by unary recursion and a large
/// constant is expensive out of all proportion to its size.
#[test]
fn rat_mat_mul_computes_a_two_by_two_product() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `n / (index + 1)` — `index = 0` is the integer `n`.
    let literal = |d: &mut IntDev<'_>, n: u32, index: u32| -> ExprId {
        let numerator = d.num(n);
        let idx = d.num(index);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };

    // `fun i j => coeff(i, j)` as a `Nat -> Nat -> Rat`.
    let matrix =
        |d: &mut IntDev<'_>, coeff: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId| -> ExprId {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = coeff(d, i, j);
            let over_j = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, over_j)
        };

    // A i j = (2i + j + 1) / 1, written `((i + i) + j) + 1` so every literal
    // sits on `Nat.add`'s RIGHT (the argument it recurses on).
    let a = matrix(&mut d, &|d, i, j| {
        let two_i = d.add(i, i);
        let plus_j = d.add(two_i, j);
        let one = d.num(1);
        let numerator = d.add(plus_j, one);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });
    // B i j = (i + 2j) / 1.
    let b = matrix(&mut d, &|d, i, j| {
        let plus_j = d.add(i, j);
        let numerator = d.add(plus_j, j);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });

    let two_n = d.num(2);
    let cell = |d: &mut IntDev<'_>, i: u32, j: u32| -> ExprId {
        let iu = d.num(i);
        let ju = d.num(j);
        d.const_app(p.mat_mul, &[a, b, two_n, iu, ju])
    };

    // A itself, so a wrong entry formula is caught before the product is.
    for (i, j, want) in [(0, 0, 1), (0, 1, 2), (1, 0, 3), (1, 1, 4)] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.apply(a, &[iu, ju]);
        let expected = literal(&mut d, want, 0);
        assert!(
            d.kernel().def_eq(got, expected),
            "the test matrix A should have A[{i}][{j}] = {want}"
        );
    }
    for (i, j, want) in [(0, 0, 0), (0, 1, 2), (1, 0, 1), (1, 1, 3)] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.apply(b, &[iu, ju]);
        let expected = literal(&mut d, want, 0);
        assert!(
            d.kernel().def_eq(got, expected),
            "the test matrix B should have B[{i}][{j}] = {want}"
        );
    }

    // All four cells of the product, hand-computed above.
    for (i, j, want) in [(0, 0, 2), (0, 1, 8), (1, 0, 4), (1, 1, 18)] {
        let got = cell(&mut d, i, j);
        let expected = literal(&mut d, want, 0);
        assert!(
            d.kernel().def_eq(got, expected),
            "Rat.matMul A B 2 {i} {j} should reduce to {want}"
        );
    }

    // Negative control on the CHECK, not on the definition: the four expected
    // values must be pairwise distinct, or a wrong product could satisfy the
    // loop above by landing on a neighbouring cell's value.
    let values: Vec<ExprId> = [2u32, 8, 4, 18]
        .into_iter()
        .map(|v| literal(&mut d, v, 0))
        .collect();
    for (x, left) in values.iter().enumerate() {
        for right in values.iter().skip(x + 1) {
            assert!(
                !d.kernel().def_eq(*left, *right),
                "the four expected cell values must be pairwise distinct, or this \
                 test cannot tell a transposed index from a correct product"
            );
        }
    }

    // Negative control on the DEFINITION: matrix multiplication is not
    // commutative, and `matMul` must not be computing something symmetric.
    // Cell (0,0): A*B is 2 and B*A is 0*1 + 2*3 = 6.
    let ab_00 = cell(&mut d, 0, 0);
    let zero_n = d.num(0);
    let ba_00 = d.const_app(p.mat_mul, &[b, a, two_n, zero_n, zero_n]);
    let six = literal(&mut d, 6, 0);
    assert!(
        d.kernel().def_eq(ba_00, six),
        "Rat.matMul B A 2 0 0 should reduce to 6"
    );
    assert!(
        !d.kernel().def_eq(ab_00, ba_00),
        "A*B and B*A must differ at (0,0) -- if they agree, `matMul` is symmetric \
         in its two matrix arguments and is not matrix multiplication"
    );
}

/// The same product with a genuinely **fractional** entry, so the definition
/// is exercised over ℚ rather than over an integer sub-ring that a wrong
/// `Rat.mul` could still satisfy.
///
/// ```text
///   A i j = (i + i + j + 1) / 2        B i j = (i + j + j) / 1
///   A = [ 1/2   1  ]                   B = [ 0  2 ]
///       [ 3/2   2  ]                       [ 1  3 ]
///
///   A*B (0,0) = (1/2)*0 + 1*1     = 1   (0,1) = (1/2)*2 + 1*3     = 4
///       (1,0) = (3/2)*0 + 2*1     = 2   (1,1) = (3/2)*2 + 2*3     = 9
/// ```
///
/// Cell `(0,1)` is the load-bearing one: `(1/2)*2` must reduce to `1`, which
/// no integer-only reading of `Rat.mul` produces.
#[test]
fn rat_mat_mul_computes_over_fractional_entries() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, n: u32, index: u32| -> ExprId {
        let numerator = d.num(n);
        let idx = d.num(index);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let matrix =
        |d: &mut IntDev<'_>, coeff: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId| -> ExprId {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = coeff(d, i, j);
            let over_j = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, over_j)
        };

    // denominator index 1, i.e. `/ 2`.
    let a = matrix(&mut d, &|d, i, j| {
        let two_i = d.add(i, i);
        let plus_j = d.add(two_i, j);
        let one = d.num(1);
        let numerator = d.add(plus_j, one);
        let idx = d.num(1);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });
    let b = matrix(&mut d, &|d, i, j| {
        let plus_j = d.add(i, j);
        let numerator = d.add(plus_j, j);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });

    // A[0][0] = 1/2 exactly, and it is NOT the integer 1 or 0.
    let a00 = {
        let z = d.num(0);
        d.apply(a, &[z, z])
    };
    let half = literal(&mut d, 1, 1);
    assert!(
        d.kernel().def_eq(a00, half),
        "the fractional test matrix should have A[0][0] = 1/2"
    );
    let one_r = literal(&mut d, 1, 0);
    assert!(
        !d.kernel().def_eq(half, one_r),
        "1/2 and 1 must not be defeq, or this test proves nothing about ℚ"
    );

    let two_n = d.num(2);
    for (i, j, want) in [(0u32, 0u32, 1u32), (0, 1, 4), (1, 0, 2), (1, 1, 9)] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.const_app(p.mat_mul, &[a, b, two_n, iu, ju]);
        let expected = literal(&mut d, want, 0);
        assert!(
            d.kernel().def_eq(got, expected),
            "Rat.matMul A B 2 {i} {j} over fractional entries should reduce to {want}"
        );
    }
}

/// `matMul_assoc` at a concrete instance, applied rather than merely
/// declared: `(A*B)*C` and `A*(B*C)` at `2 x 2` with `k = m = 2`, cell
/// `(0,0)`, both reducing to the SAME hand-computed value.
///
/// This is the other half of the "concrete AND symbolic" pair. The theorem
/// itself is stated and proved at genuinely free `A B C k m i j`, which
/// numerals cannot hide a definitional-equality gap in; this instance checks
/// that the theorem is about the definition this file actually declared, and
/// that its two sides are not trivially the same expression.
#[test]
fn rat_mat_mul_assoc_holds_at_a_concrete_instance() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::req;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, n: u32| -> ExprId {
        let numerator = d.num(n);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let matrix =
        |d: &mut IntDev<'_>, coeff: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId| -> ExprId {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = coeff(d, i, j);
            let over_j = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, over_j)
        };

    // A = [[1,2],[3,4]], B = [[0,2],[1,3]], C = [[1,0],[0,1]] is a bad choice
    // (C would be the identity and hide a bug), so C i j = (j + 1) / 1:
    // C = [[1,2],[1,2]].
    let a = matrix(&mut d, &|d, i, j| {
        let two_i = d.add(i, i);
        let plus_j = d.add(two_i, j);
        let one = d.num(1);
        let numerator = d.add(plus_j, one);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });
    let b = matrix(&mut d, &|d, i, j| {
        let plus_j = d.add(i, j);
        let numerator = d.add(plus_j, j);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });
    let c = matrix(&mut d, &|d, _i, j| {
        let one = d.num(1);
        let numerator = d.add(j, one);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    });

    let two_n = d.num(2);
    let zero_n = d.num(0);
    let proof = d.lemma(p.mat_mul_assoc, &[a, b, c, two_n, two_n, zero_n, zero_n]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("Rat.matMul_assoc at a concrete instance should infer: {e:?}"));

    // A*B = [[2,8],[4,18]] (see `rat_mat_mul_computes_a_two_by_two_product`),
    // so ((A*B)*C)[0][0] = 2*1 + 8*1 = 10.
    let ten = literal(&mut d, 10);
    let expected = req(&mut d, ten, ten);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "at A=[[1,2],[3,4]], B=[[0,2],[1,3]], C=[[1,2],[1,2]] the (0,0) entry of \
         (A*B)*C and of A*(B*C) is 2*1 + 8*1 = 10"
    );

    // Non-vacuity: the two sides of the instantiated statement are DIFFERENT
    // expressions (they associate the product differently), so this is not a
    // reflexivity check dressed up as an associativity check.
    let ab = d.const_app(p.mat_mul, &[a, b, two_n]);
    let bc = d.const_app(p.mat_mul, &[b, c, two_n]);
    let left = d.const_app(p.mat_mul, &[ab, c, two_n, zero_n, zero_n]);
    let right = d.const_app(p.mat_mul, &[a, bc, two_n, zero_n, zero_n]);
    assert_ne!(
        left, right,
        "(A*B)*C and A*(B*C) must not be the same ExprId, or the instance is vacuous"
    );
    let eleven = literal(&mut d, 11);
    assert!(
        !d.kernel().def_eq(ten, eleven),
        "10 and 11 must not be defeq, or the value check above cannot fail"
    );
}

/// **The mandatory concrete computation test for `Rat.matId`.** The identity
/// matrix is a `Definition`, so the kernel admits it once it is well-formed
/// and cannot say it selects the wrong branch.
///
/// `matId i j = if Nat.beq i j then 1 else 0`, checked on and off the
/// diagonal, in both index orders, and past the `2 x 2` block the rest of
/// this file uses — a delta that got its two branches the wrong way round
/// would give `1` at `(0,1)` and `0` at `(0,0)`.
#[test]
fn rat_mat_id_computes_the_delta() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let one_r = {
        let numerator = d.num(1);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let zero_r = {
        let numerator = d.num(0);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    assert!(
        !d.kernel().def_eq(one_r, zero_r),
        "1 and 0 must not be defeq, or nothing below can fail"
    );

    let mat_id = d.kernel().const_(p.mat_id, vec![]);
    for (i, j, on_diagonal) in [
        (0u32, 0u32, true),
        (0, 1, false),
        (1, 0, false),
        (1, 1, true),
        (2, 1, false),
        (3, 3, true),
    ] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.apply(mat_id, &[iu, ju]);
        let expected = if on_diagonal { one_r } else { zero_r };
        assert!(
            d.kernel().def_eq(got, expected),
            "Rat.matId {i} {j} should be {}",
            u32::from(on_diagonal)
        );
    }
}

/// The identity's unit law **computed**, and — the part that carries the
/// argument — a demonstration that its `Lt i n` hypothesis is load-bearing
/// rather than decoration.
///
/// With `A i j = (i + i + j + 1) / 1` as elsewhere in this file:
///
/// ```text
///   A = [ 1  2 ]     matId(2x2) * A = A   at every (i, j) with i < 2
///       [ 3  4 ]
/// ```
///
/// but at `i = 2`, which is OUTSIDE the summation range, the delta never
/// fires: `matId 2 0 * A 0 0 + matId 2 1 * A 1 0 = 0*1 + 0*3 = 0`, while
/// `A 2 0 = 5`. So `matMul matId A 2 2 0` is `0` and not `A 2 0`, and a
/// version of `matMul_id_left` stated without the bound would be FALSE.
#[test]
fn rat_mat_mul_id_left_needs_its_bound() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, n: u32| -> ExprId {
        let numerator = d.num(n);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let a = {
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let two_i = d.add(i, i);
        let plus_j = d.add(two_i, j);
        let one = d.num(1);
        let numerator = d.add(plus_j, one);
        let idx = d.num(0);
        let body = d.const_app(p.nat_div_succ, &[numerator, idx]);
        let over_j = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, over_j)
    };
    let mat_id = d.kernel().const_(p.mat_id, vec![]);
    let two_n = d.num(2);

    // In range: `matId * A` agrees with `A` at every cell.
    for (i, j, want) in [(0u32, 0u32, 1u32), (0, 1, 2), (1, 0, 3), (1, 1, 4)] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.const_app(p.mat_mul, &[mat_id, a, two_n, iu, ju]);
        let expected = literal(&mut d, want);
        assert!(
            d.kernel().def_eq(got, expected),
            "Rat.matMul matId A 2 {i} {j} should reduce to A[{i}][{j}] = {want}"
        );
    }
    // And on the right.
    for (i, j, want) in [(0u32, 0u32, 1u32), (0, 1, 2), (1, 0, 3), (1, 1, 4)] {
        let iu = d.num(i);
        let ju = d.num(j);
        let got = d.const_app(p.mat_mul, &[a, mat_id, two_n, iu, ju]);
        let expected = literal(&mut d, want);
        assert!(
            d.kernel().def_eq(got, expected),
            "Rat.matMul A matId 2 {i} {j} should reduce to A[{i}][{j}] = {want}"
        );
    }

    // OUT of range: the bound in `matMul_id_left` is not decoration.
    let two_idx = d.num(2);
    let zero_idx = d.num(0);
    let out_of_range = d.const_app(p.mat_mul, &[mat_id, a, two_n, two_idx, zero_idx]);
    let zero_r = literal(&mut d, 0);
    let a_20 = {
        let iu = d.num(2);
        let ju = d.num(0);
        d.apply(a, &[iu, ju])
    };
    let five = literal(&mut d, 5);
    assert!(
        d.kernel().def_eq(a_20, five),
        "the test matrix should have A[2][0] = 5"
    );
    assert!(
        d.kernel().def_eq(out_of_range, zero_r),
        "with i = 2 outside the summation range the delta never fires, so \
         Rat.matMul matId A 2 2 0 is 0"
    );
    assert!(
        !d.kernel().def_eq(out_of_range, a_20),
        "0 and A[2][0] = 5 must differ -- if they agreed, `matMul_id_left` \
         would hold without its `Lt i n` hypothesis and the hypothesis would \
         be untested decoration"
    );
}

/// `matMul_id_left` and `matMul_id_right` APPLIED, not merely declared: the
/// bound is discharged by `Nat.zero_lt_succ` at `0 < 2` and the resulting
/// proof's inferred type is compared against an independently built equation
/// whose two sides both reduce to the hand-computed `A[0][1] = 2`.
#[test]
fn rat_mat_mul_id_laws_hold_at_a_concrete_instance() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::req;

    let (mut kernel, p) = built();
    let np = {
        let mut d = IntDev::new(&mut kernel, p.int);
        d.prelude()
    };
    let mut d = IntDev::new(&mut kernel, p.int);

    let a = {
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let two_i = d.add(i, i);
        let plus_j = d.add(two_i, j);
        let one = d.num(1);
        let numerator = d.add(plus_j, one);
        let idx = d.num(0);
        let body = d.const_app(p.nat_div_succ, &[numerator, idx]);
        let over_j = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, over_j)
    };

    let two_n = d.num(2);
    let zero_idx = d.num(0);
    let one_idx = d.num(1);
    // `Lt 0 2` = `Lt zero (succ 1)`.
    let hlt = d.lemma(np.zero_lt_succ, &[one_idx]);

    let two_r = {
        let numerator = d.num(2);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let expected = req(&mut d, two_r, two_r);

    let left = d.lemma(p.mat_mul_id_left, &[a, two_n, zero_idx, one_idx, hlt]);
    let inferred_left = d
        .kernel()
        .infer(left)
        .unwrap_or_else(|e| panic!("Rat.matMul_id_left at A, n=2, i=0, j=1 should infer: {e:?}"));
    assert!(
        d.kernel().def_eq(inferred_left, expected),
        "matId * A agrees with A at (0,1), where A[0][1] = 2"
    );

    // `matMul_id_right`'s bound is on `j`, and `j = 1 < 2` here, so the same
    // `Lt 0 2` proof does NOT serve -- `Lt 1 2` is `Nat.lt_succ_self 1`.
    let hlt_j = d.lemma(np.lt_succ_self, &[one_idx]);
    let right = d.lemma(p.mat_mul_id_right, &[a, two_n, zero_idx, one_idx, hlt_j]);
    let inferred_right = d
        .kernel()
        .infer(right)
        .unwrap_or_else(|e| panic!("Rat.matMul_id_right at A, n=2, i=0, j=1 should infer: {e:?}"));
    assert!(
        d.kernel().def_eq(inferred_right, expected),
        "A * matId agrees with A at (0,1), where A[0][1] = 2"
    );

    let three_r = {
        let numerator = d.num(3);
        let idx = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, idx])
    };
    let wrong = req(&mut d, two_r, three_r);
    assert!(
        !d.kernel().def_eq(inferred_left, wrong),
        "the inferred statement must not be defeq to a false equation, or the \
         two checks above cannot fail"
    );
}

// --- `Rat.det`: the determinant at general `n` (`rat_prelude::matrix_det`) ---

/// Every declaration `matrix_det::declare_matrix_det` adds is a **checked**
/// definition or theorem with an empty axiom footprint, read out of the
/// kernel rather than off the diff -- same discipline as
/// [`the_matrix_toolkit_is_axiom_free`].
#[test]
fn the_determinant_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("matSkip", p.mat_skip, false),
        ("matMinor", p.mat_minor, false),
        ("altSign", p.alt_sign, false),
        ("altSign_zero", p.alt_sign_zero, true),
        ("altSign_succ", p.alt_sign_succ, true),
        ("det", p.det, false),
        ("det_zero", p.det_zero, true),
        ("det_succ", p.det_succ, true),
        ("det_one", p.det_one, true),
        ("det_eq_det2", p.det_eq_det2, true),
        ("det_eq_det3", p.det_eq_det3, true),
        ("matMinor_eval_example", p.mat_minor_eval_example, true),
        ("det_eval_example", p.det_eval_example, true),
        ("det_eval_singular", p.det_eval_singular, true),
        ("det_eval_example4", p.det_eval_example4, true),
        (
            "sumRange_head_of_tail_zero",
            p.sum_range_head_of_tail_zero,
            true,
        ),
        ("det_congr", p.det_congr, true),
        ("matMinor_matId", p.mat_minor_mat_id, true),
        ("det_matId", p.det_mat_id, true),
        ("matSkip_zero", p.mat_skip_zero, true),
        ("matSkip_succ_succ", p.mat_skip_succ_succ, true),
        ("matSkip_comm", p.mat_skip_comm, true),
        ("matMinor_col_comm", p.mat_minor_col_comm, true),
        ("det_minor_col_comm", p.det_minor_col_comm, true),
        ("sumRange_peel_head", p.sum_range_peel_head, true),
        ("sumRange_matSkip", p.sum_range_mat_skip, true),
        ("unskip", p.unskip, false),
        ("unskip_zero", p.unskip_zero, true),
        ("unskip_succ_zero", p.unskip_succ_zero, true),
        ("unskip_succ_succ", p.unskip_succ_succ, true),
        ("unskip_matSkip", p.unskip_mat_skip, true),
        ("beq_matSkip", p.beq_mat_skip, true),
        ("beq_matSkip_left", p.beq_mat_skip_left, true),
        ("altSign_succ_add", p.alt_sign_succ_add, true),
        ("ble_flip_of_false", p.ble_flip_of_false, true),
        ("unskip_le", p.unskip_le, true),
        ("unskip_gt", p.unskip_gt, true),
        ("matMinor_double_comm_lo", p.mat_minor_double_comm_lo, true),
        ("matMinor_double_comm_hi", p.mat_minor_double_comm_hi, true),
        ("det_double_comm_lo", p.det_double_comm_lo, true),
        ("det_double_comm_hi", p.det_double_comm_hi, true),
        ("mul_perm4", p.mul_perm4, true),
        ("laplaceSummand", p.laplace_summand, false),
        ("laplaceSummand_rowZero", p.laplace_summand_row_zero, true),
        ("laplaceSummand_rowI", p.laplace_summand_row_i, true),
        ("laplaceSummand_diag", p.laplace_summand_diag, true),
        ("det_row_expansion", p.det_row_expansion, true),
        ("matMinor_row_col_comm", p.mat_minor_row_col_comm, true),
        ("det_minor_row_col_comm", p.det_minor_row_col_comm, true),
        ("det_col_expansion", p.det_col_expansion, true),
        ("matMinor_transpose", p.mat_minor_transpose, true),
        ("det_transpose", p.det_transpose, true),
        ("det_alternating", p.det_alternating, true),
        ("det_row_swap", p.det_row_swap, true),
        ("det_row_replaced", p.det_row_replaced, true),
        ("det_row_zero", p.det_row_zero, true),
        ("det_row_smul", p.det_row_smul, true),
        ("det_row_multilinear", p.det_row_multilinear, true),
        ("det_matMul_2", p.det_mat_mul_2, true),
        (
            "det_row_selection_of_duplicate",
            p.det_row_selection_of_duplicate,
            true,
        ),
        ("det_congr_lt", p.det_congr_lt, true),
        ("matSkip_lt_succ", p.mat_skip_lt_succ, true),
        ("det_congr_entry_lt", p.det_congr_entry_lt, true),
        (
            "det_row_selection_injective",
            p.det_row_selection_injective,
            true,
        ),
        ("det_row_selection", p.det_row_selection, true),
        ("prodRange", p.prod_range, false),
        ("prodRange_zero", p.prod_range_zero, true),
        ("prodRange_succ", p.prod_range_succ, true),
        ("prodRange_shiftFront", p.prod_range_shift_front, true),
        ("prodRange_congr", p.prod_range_congr, true),
        ("sumRange_mul_right", p.sum_range_mul_right, true),
        ("sumRange_mul_left", p.sum_range_mul_left, true),
        ("sumMaps", p.sum_maps, false),
        ("sumMaps_zero", p.sum_maps_zero, true),
        ("sumMaps_succ", p.sum_maps_succ, true),
        ("sumMaps_congr", p.sum_maps_congr, true),
        ("sumMaps_mul_left", p.sum_maps_mul_left, true),
        ("sumMaps_mul_right", p.sum_maps_mul_right, true),
        ("matSetRow", p.mat_set_row, false),
        ("matSetRow_at", p.mat_set_row_at, true),
        ("matSetRow_off", p.mat_set_row_off, true),
        ("matSubstRows", p.mat_subst_rows, false),
        ("matSubstRows_below", p.mat_subst_rows_below, true),
        ("matSubstRows_at", p.mat_subst_rows_at, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `det_eq_det2`'s statement rendered verbatim, plus the shape of
/// `det_eq_det3`.
///
/// The point of the pin is that the left-hand side is `Rat.det <A> <numeral>`
/// -- the dimension is an ARGUMENT -- and the right-hand side is the
/// fixed-dimension `Rat.det2`/`Rat.det3` applied to entries of the SAME
/// universally quantified `A`. An edit that quietly restated either at a
/// concrete matrix, or dropped the `∀ A`, would leave `matrix_det`'s module
/// doc describing something no longer true, and would turn this file's
/// strongest correctness evidence into an evaluation example. Same discipline
/// as [`the_matrix_associativity_statement_is_pointwise`].
#[test]
fn the_determinant_agreement_statements_quantify_over_the_matrix() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    let two = rendered(&mut kernel, p.det_eq_det2);
    assert_eq!(
        two,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         Eq.{1} Rat \
         (Rat.det x0 (AxNat.succ (AxNat.succ AxNat.zero))) \
         (Rat.det2 (x0 AxNat.zero AxNat.zero) \
         (x0 AxNat.zero (AxNat.succ AxNat.zero)) \
         (x0 (AxNat.succ AxNat.zero) AxNat.zero) \
         (x0 (AxNat.succ AxNat.zero) (AxNat.succ AxNat.zero))))"
    );
    let three = rendered(&mut kernel, p.det_eq_det3);
    assert!(
        three.starts_with(
            "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> Eq.{1} Rat (Rat.det x0 "
        ),
        "det_eq_det3 must still be `∀ (A : Nat → Nat → Rat), det A 3 = …`, got {three}"
    );
    assert!(
        three.contains("Rat.det3 (x0 AxNat.zero AxNat.zero)"),
        "det_eq_det3's right-hand side must be `Rat.det3` on entries of the same A, got {three}"
    );
}

/// The determinant recursion **computes**, and computes the right numbers --
/// with a negative control on every case, so the check can fail.
///
/// The trusted gate cannot tell you a `Definition` is wrong: it type-checks a
/// stated type, and `(Nat → Nat → Rat) → Nat → Rat` is that type whatever the
/// function returns. The four `*_eval_*` theorems are admitted only because
/// `Kernel::add_declaration` reduced `Rat.det` at a concrete matrix and
/// matched the normal form against a hand-computed numeral -- that is the
/// positive half, and it is already enforced by the prelude building at all.
///
/// This test adds the half that is easy to omit: it pulls each theorem's
/// left-hand side straight out of the checked statement and asserts it is
/// **not** `def_eq` to a deliberately wrong value. Without that, a
/// `Definition` returning a constant would still make every `Eq.refl` above
/// succeed at whatever constant it returns.
///
/// Two details that decide whether these controls are worth having:
///
/// - The wrong value differs in a **small** term (`Rat.neg` of the true one,
///   or `Rat.one`), never by transposing a determinant. A *failing* `def_eq`
///   has no early exit, so a large one is unbounded; here both sides are
///   closed and reduce to numerals.
/// - `det_eval_singular`'s true value is `0`, and `neg 0 = 0`, so negating it
///   would be a control that **cannot fail**. It uses `Rat.one` instead.
#[test]
fn the_determinant_evaluation_examples_reject_the_wrong_value() {
    // `Eq.{1} Rat lhs rhs` is `App(App(App(Eq, Rat), lhs), rhs)`.
    fn equation(kernel: &Kernel, ty: ExprId) -> (ExprId, ExprId) {
        let ExprNode::App(without_rhs, rhs) = *kernel.expr_node(ty) else {
            panic!("the statement must be an application")
        };
        let ExprNode::App(_, lhs) = *kernel.expr_node(without_rhs) else {
            panic!("the statement must be an `Eq` application")
        };
        (lhs, rhs)
    }

    let (mut kernel, p) = built();

    let one = kernel.const_(p.one, vec![]);
    let neg = kernel.const_(p.int.rat_neg, vec![]);

    for (label, name, negate) in [
        ("matMinor_eval_example", p.mat_minor_eval_example, true),
        ("det_eval_example", p.det_eval_example, true),
        // true value is `0`, and `neg 0` reduces to `0`: negating would be a
        // control that cannot fail, so this one is separated from `1`.
        ("det_eval_singular", p.det_eval_singular, false),
        ("det_eval_example4", p.det_eval_example4, true),
    ] {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!("Rat.{label}: {other:?} is not a theorem"),
        };
        let (lhs, rhs) = equation(&kernel, ty);

        // Positive: the checked statement is what it claims to be.
        assert!(
            kernel.def_eq(lhs, rhs),
            "Rat.{label}: the checked left- and right-hand sides must agree"
        );

        // Negative: a different value must NOT be reachable.
        let wrong = if negate { kernel.app(neg, rhs) } else { one };
        assert!(
            !kernel.def_eq(lhs, wrong),
            "Rat.{label}: the evaluation accepted a WRONG value, so it checks nothing"
        );
    }
}

/// The two determinant LAWS are stated at a **symbolic** dimension, and
/// `det_congr` still carries its pointwise hypothesis.
///
/// The whole point of `Rat.det_matId` over the existing `det_eval_*` theorems
/// is that its `n` is a bound variable rather than a numeral -- an edit that
/// quietly restated it at a fixed dimension would turn this file's first
/// general law back into an evaluation example while every axiom-footprint
/// check stayed green. And `Rat.det_congr` is only interesting *because* it
/// has a hypothesis: the unhypothesized `∀ n A B, det A n = det B n` is FALSE
/// (the control below exhibits two matrices that separate it), so a statement
/// that lost the premise would be unprovable rather than merely weaker --
/// which is why the shape is pinned here rather than trusted.
#[test]
fn the_determinant_laws_are_stated_at_a_symbolic_dimension() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };

    let identity = rendered(&mut kernel, p.det_mat_id);
    assert!(
        identity.contains("(x0 : AxNat)"),
        "det_matId must quantify over the dimension, got {identity}"
    );
    assert!(
        identity.contains("Rat.det Rat.matId x0"),
        "det_matId's dimension must be the BOUND VARIABLE, not a numeral, got {identity}"
    );
    assert!(
        identity.contains("Rat.one"),
        "det_matId must conclude at `Rat.one`, got {identity}"
    );
    assert!(
        !identity.contains("AxNat.succ"),
        "det_matId must not mention any numeral -- it is the general law, got {identity}"
    );

    let congr = rendered(&mut kernel, p.det_congr);
    assert!(
        congr.contains("Rat.det x1 x0") && congr.contains("Rat.det x2 x0"),
        "det_congr must compare `det A n` with `det B n` at the same bound `n`, got {congr}"
    );
    assert!(
        congr.contains("(x1 x"),
        "det_congr must carry the POINTWISE hypothesis `∀ r c, A r c = B r c`; without it \
         the statement is false, got {congr}"
    );
}

/// The three ingredients of `Rat.det_matId` each rest on a check that can
/// fail, and each control says which reading it rules out.
///
/// `Rat.matMinor_matId` is `Eq.refl`, so on its own it is exactly as strong as
/// the reductions behind it -- and it would be equally `refl` if `Rat.matSkip`
/// ignored its first argument, or if `Rat.matMinor` ignored the deleted
/// indices. Likewise `Rat.det_matId` would be trivial if `Rat.det` returned
/// `1` regardless of its matrix, and `Rat.sumRange_head_of_tail_zero`'s
/// premise would be discardable if `Rat.sumRange` collapsed to its head.
///
/// So each of the three is paired: a POSITIVE `def_eq` on the exact term the
/// proof relies on, and a NEGATIVE one differing in a **small**, ground term.
/// Every value here is `0` or `1` and every dimension is at most three, so
/// both directions reduce to closed `Rat` numerals -- a failing `def_eq` has
/// no early exit, and this file's existing evaluation controls are careful
/// about that for the same reason.
///
/// What each control rules out, and what it does NOT:
///
/// - **`matMinor matId 0 1 0 0 ≠ matId 0 0`** rules out a `matSkip` that
///   ignores the index being deleted (`matMinor matId 0 j` the identity for
///   EVERY `j`). It does not distinguish a sign error -- there are no signs
///   in `matMinor`.
/// - **`det (matMinor matId 0 1) 2 ≠ 1`** rules out `det` returning `1`
///   independently of its matrix, which is the reading that would make
///   `det_matId` vacuous. Its true value is `0`, so it would NOT separate a
///   sign flip (`neg 0 = 0`) -- `det_eval_example`, whose value is `13`, is
///   the theorem that does that, and this one deliberately does not duplicate
///   it.
/// - **`sumRange (fun _ => 1) 2 ≠ 1`** rules out a `sumRange` that returns its
///   first summand, which is the reading under which
///   `sumRange_head_of_tail_zero` would hold with no hypothesis at all. It
///   says nothing about the ORDER of summation.
#[test]
fn the_determinant_law_ingredients_reject_the_degenerate_reading() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rone, rsum_range};

    let (mut kernel, p) = built();

    let (leading, shifted, identity_at_origin, det_identity_3, det_shifted_2, sum_1, sum_2, one) = {
        let mut d = IntDev::new(&mut kernel, p.int);
        let nat = d.nat_ty();
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let two_n = d.num(2);
        let three_n = d.num(3);
        let one_r = rone(&mut d, p);
        let mat_id = d.kernel().const_(p.mat_id, vec![]);

        // (a) the LEADING minor of the identity is the identity at (0,0);
        //     deleting column 1 instead is not.
        let leading = d.const_app(p.mat_minor, &[mat_id, zero_n, zero_n, zero_n, zero_n]);
        let shifted = d.const_app(p.mat_minor, &[mat_id, zero_n, one_n, zero_n, zero_n]);
        let identity_at_origin = d.apply(mat_id, &[zero_n, zero_n]);

        // (b) `det matId 3` computes to `1`; the same recursion on the
        //     column-1 minor (a genuine matrix built by the SAME machinery)
        //     computes to `0`.
        let det_identity_3 = d.const_app(p.det, &[mat_id, three_n]);
        let shifted_matrix = d.const_app(p.mat_minor, &[mat_id, zero_n, one_n]);
        let det_shifted_2 = d.const_app(p.det, &[shifted_matrix, two_n]);

        // (c) the tail premise of `sumRange_head_of_tail_zero` is load-bearing.
        let constant_one = {
            let k_fv = d.fresh_fvar();
            d.lam_fv(k_fv, nat, one_r)
        };
        let sum_1 = rsum_range(&mut d, p, constant_one, one_n);
        let sum_2 = rsum_range(&mut d, p, constant_one, two_n);

        (
            leading,
            shifted,
            identity_at_origin,
            det_identity_3,
            det_shifted_2,
            sum_1,
            sum_2,
            one_r,
        )
    };

    assert!(
        kernel.def_eq(leading, identity_at_origin),
        "matMinor matId 0 0 0 0 must reduce to matId 0 0 -- this is exactly what \
         Rat.matMinor_matId asserts by Eq.refl"
    );
    assert!(
        !kernel.def_eq(shifted, identity_at_origin),
        "matMinor matId 0 1 0 0 accepted matId 0 0, so matSkip ignores the deleted index \
         and Rat.matMinor_matId holds for a degenerate reason"
    );

    assert!(
        kernel.def_eq(det_identity_3, one),
        "det matId 3 must compute to 1 -- the concrete instantiation of Rat.det_matId"
    );
    assert!(
        !kernel.def_eq(det_shifted_2, one),
        "det (matMinor matId 0 1) 2 accepted 1, so det returns 1 regardless of its matrix \
         and Rat.det_matId is vacuous"
    );

    assert!(
        kernel.def_eq(sum_1, one),
        "sumRange (fun _ => 1) 1 must compute to 1"
    );
    assert!(
        !kernel.def_eq(sum_2, one),
        "sumRange (fun _ => 1) 2 accepted 1, so sumRange collapses to its head and \
         Rat.sumRange_head_of_tail_zero's premise is discardable"
    );
}

/// The two HYPOTHESES the Laplace index layer carries are load-bearing, and
/// each control says what it rules out and what it does not.
///
/// `Rat.matSkip_comm` and `Rat.sumRange_matSkip` both take `Nat.ble j n =
/// true`. A premise that could be dropped is the cheapest way to ship a
/// theorem that reads stronger than it is, so each is paired here: a NEGATIVE
/// `def_eq` on a ground instance where the premise fails and the conclusion is
/// false, and a POSITIVE one on an instance differing in a SINGLE index where
/// the premise holds and the conclusion is true. The same `def_eq` call
/// returns both answers, which is what makes neither vacuous.
///
/// Every value formed here is `0`, `1`, or an index below `4`, so both
/// directions reduce to closed `Rat` numerals -- a FAILING `def_eq` has no
/// early exit, and this file's other controls are careful about that for the
/// same reason (ADR-1135).
///
/// What each control rules out, and what it does NOT:
///
/// - **`matSkip 1 (matSkip 0 0) != matSkip 1 (matSkip 1 0)`** (`2` against
///   `0`) rules out an unhypothesized `Rat.matSkip_comm`. It says nothing
///   about whether `matSkip`'s two branches are the right way round -- at
///   `a = 0` both readings agree, which is exactly ADR-1135's finding about
///   `matMinor_matId`, so the branch-swap mutation is separated by
///   `Rat.matSkip_zero` and by `det_eq_det2`, not by this.
/// - **`sumRange (matId 2 . matSkip 2) 1 + matId 2 2 != sumRange (matId 2) 2`**
///   (`1` against `0`) rules out an unhypothesized `Rat.sumRange_matSkip`:
///   with `j = 2` outside the range `[0, 1)` the deleted index is never
///   reached, so adding `f j` back over-counts. It does NOT check the
///   ORDER of summation, and it does not exercise `matSkip`'s shift on more
///   than one index.
/// - **`sumRange (matId 2) 3 != matId 2 0 + sumRange (matId 2) 2`** (`1`
///   against `0`) rules out a `Rat.sumRange_peel_head` that forgot to shift
///   the tail's index. It says nothing about the head itself, which is `0`
///   here.
#[test]
fn the_laplace_index_layer_hypotheses_are_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rsum_range};

    let (mut kernel, p) = built();

    let (
        unordered_left,
        unordered_right,
        ordered_left,
        ordered_right,
        in_range_reindexed,
        in_range_full,
        out_of_range_reindexed,
        out_of_range_full,
        peeled_shifted,
        peeled_unshifted,
        whole,
    ) = {
        let mut d = IntDev::new(&mut kernel, p.int);
        let nat = d.nat_ty();
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let two_n = d.num(2);
        let three_n = d.num(3);
        let mat_id = d.kernel().const_(p.mat_id, vec![]);

        // (a) `matSkip_comm` at `a = 1`, `b = 0`, where `ble 1 0 = false`.
        let unordered_left = {
            let inner = d.const_app(p.mat_skip, &[zero_n, zero_n]);
            d.const_app(p.mat_skip, &[one_n, inner])
        };
        let unordered_right = {
            let inner = d.const_app(p.mat_skip, &[one_n, zero_n]);
            d.const_app(p.mat_skip, &[one_n, inner])
        };

        // ... and at `a = 0`, `b = 1`, differing in one index, where it holds.
        let ordered_left = {
            let inner = d.const_app(p.mat_skip, &[one_n, zero_n]);
            d.const_app(p.mat_skip, &[zero_n, inner])
        };
        let ordered_right = {
            let inner = d.const_app(p.mat_skip, &[zero_n, zero_n]);
            d.const_app(p.mat_skip, &[two_n, inner])
        };

        // (b) `sumRange_matSkip` at `j = 2` against a row of the identity that
        //     is nonzero at exactly index 2.
        let row = d.apply(mat_id, &[two_n]);
        let at_two = d.apply(row, &[two_n]);
        let reindexed = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let idx = d.const_app(p.mat_skip, &[two_n, k]);
            let body = d.apply(row, &[idx]);
            d.lam_fv(k_fv, nat, body)
        };

        // `n = 2`: `ble 2 2 = true`, the premise holds and both sides are 1.
        let in_range_reindexed = {
            let partial = rsum_range(&mut d, p, reindexed, two_n);
            radd(&mut d, partial, at_two)
        };
        let in_range_full = rsum_range(&mut d, p, row, three_n);

        // `n = 1`: `ble 2 1 = false`, and the conclusion is 1 against 0.
        let out_of_range_reindexed = {
            let partial = rsum_range(&mut d, p, reindexed, one_n);
            radd(&mut d, partial, at_two)
        };
        let out_of_range_full = rsum_range(&mut d, p, row, two_n);

        // (c) `sumRange_peel_head`'s tail must be SHIFTED.
        let shifted_row = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let body = d.apply(row, &[sk]);
            d.lam_fv(k_fv, nat, body)
        };
        let head = d.apply(row, &[zero_n]);
        let peeled_shifted = {
            let tail = rsum_range(&mut d, p, shifted_row, two_n);
            radd(&mut d, head, tail)
        };
        let peeled_unshifted = {
            let tail = rsum_range(&mut d, p, row, two_n);
            radd(&mut d, head, tail)
        };
        let whole = rsum_range(&mut d, p, row, three_n);

        (
            unordered_left,
            unordered_right,
            ordered_left,
            ordered_right,
            in_range_reindexed,
            in_range_full,
            out_of_range_reindexed,
            out_of_range_full,
            peeled_shifted,
            peeled_unshifted,
            whole,
        )
    };

    assert!(
        !kernel.def_eq(unordered_left, unordered_right),
        "matSkip 1 (matSkip 0 0) accepted matSkip 1 (matSkip 1 0), so Rat.matSkip_comm \
         would hold with no hypothesis at all"
    );
    assert!(
        kernel.def_eq(ordered_left, ordered_right),
        "matSkip 0 (matSkip 1 0) must equal matSkip 2 (matSkip 0 0) -- the same def_eq \
         call, one index apart, so the negative above is not vacuous"
    );

    assert!(
        kernel.def_eq(in_range_reindexed, in_range_full),
        "sumRange_matSkip must hold at j = 2, n = 2, where ble 2 2 = true"
    );
    assert!(
        !kernel.def_eq(out_of_range_reindexed, out_of_range_full),
        "the same identity was accepted at j = 2, n = 1, where ble 2 1 = false, so \
         Rat.sumRange_matSkip's premise is discardable"
    );

    assert!(
        kernel.def_eq(peeled_shifted, whole),
        "sumRange_peel_head must hold at this row -- the positive instance"
    );
    assert!(
        !kernel.def_eq(peeled_unshifted, whole),
        "peeling the head without SHIFTING the tail was accepted, so \
         Rat.sumRange_peel_head's reindexing checks nothing"
    );
}

/// `Rat.unskip` and `Rat.laplaceSummand` are **`Definition`s**, so the trusted
/// gate says only that they are well-formed. `Nat → Nat → Nat` is that type
/// whatever the function returns. These reduce both at concrete arguments
/// chosen to DISCRIMINATE, against values computed independently in
/// `docs/research/09-decisions/adr-1185-laplace-summand-checks.py`.
///
/// What each check separates, and what it does not:
///
/// - `unskip 2 1 = 1` and `unskip 2 3 = 2` are one pair on purpose: the first
///   is the identity branch and the second the `Nat.pred` branch, so a
///   definition that took either branch everywhere fails one of them. Neither
///   alone would.
/// - `laplaceSummand` at `(1, 2)` is the only entry of the pinned matrix's
///   summand that is neither `0` nor `1`, and it carries TWO `Rat.altSign`
///   factors, so it is where a sign convention shows. Its value `12` is
///   asserted, and `-12` is asserted NOT to be it.
/// - The diagonal entries are `0` — the branch that makes both cofactor ranges
///   fillable to the whole square.
///
/// None of these separates a wrong `Nat.ble` **guard order** in `matSkip`;
/// `det_eval_example` (value `13`) and `det_eq_det2` do that, and
/// [`the_laplace_index_layer_hypotheses_are_load_bearing`] covers the
/// premises.
#[test]
fn the_laplace_summand_layer_computes() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::matrix_det::{const_matrix, rq};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // --- `Rat.unskip`, both branches ---------------------------------------
    let cases: [(u32, u32, u32); 5] = [(2, 1, 1), (2, 3, 2), (0, 3, 2), (3, 0, 0), (2, 2, 2)];
    for (at, q, expected) in cases {
        let at_n = d.num(at);
        let q_n = d.num(q);
        let lhs = d.const_app(p.unskip, &[at_n, q_n]);
        let rhs = d.num(expected);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "Rat.unskip {at} {q} must reduce to {expected}"
        );
    }
    {
        // The `Nat.pred` branch actually fires: without it `unskip 2 3` is `3`.
        let two_n = d.num(2);
        let three_n = d.num(3);
        let lhs = d.const_app(p.unskip, &[two_n, three_n]);
        assert!(
            !d.kernel().def_eq(lhs, three_n),
            "Rat.unskip 2 3 accepted 3, so the shift-down branch is unreachable \
             and `unskip` is the identity"
        );
    }

    // --- `Rat.laplaceSummand` over the pinned 3x3 --------------------------
    //
    //   A = [[1, 2, 0],
    //        [0, 1, 3],
    //        [2, 0, 1]]        det A 3 = 13   (`Rat.det_eval_example`)
    //
    // at `i = 0` (so the expansion row is `succ 0 = 1`) and `m = 1`.
    let mat = const_matrix(&mut d, p, 3, &[1, 2, 0, 0, 1, 3, 2, 0, 1]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    let entries: [(u32, u32, i64); 6] = [
        (0, 1, 1),
        (1, 2, 12),
        (1, 1, 0),
        (0, 0, 0),
        (1, 0, 0),
        (2, 1, 0),
    ];
    for (col0, coli, expected) in entries {
        let a = d.num(col0);
        let b = d.num(coli);
        let lhs = d.const_app(p.laplace_summand, &[mat, zero_n, one_n, a, b]);
        let rhs = rq(&mut d, p, expected);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "laplaceSummand A 0 1 {col0} {coli} must reduce to {expected}"
        );
    }
    {
        // The sign is real: `(1, 2)` carries `altSign 1` and `altSign (1 + 0)`.
        let lhs = d.const_app(p.laplace_summand, &[mat, zero_n, one_n, one_n, two_n]);
        let wrong = rq(&mut d, p, -12);
        assert!(
            !d.kernel().def_eq(lhs, wrong),
            "laplaceSummand A 0 1 1 2 accepted -12, so nothing here separates a \
             sign convention"
        );
    }
}

/// `Rat.det_row_expansion` is the cofactor expansion along a **general** row,
/// and this evaluates its right-hand side at EVERY row of the pinned 3x3 —
/// the check no index-layer statement can make, because no sign appears in any
/// of them.
///
/// Each row's expansion must come out at `13`, the value
/// `Rat.det_eval_example` pins for the same matrix. The negative control is the
/// same sum with the alternating sign shifted by one, which comes out at
/// `-13`; it is asserted POSITIVELY (`= -13`) rather than as a failed
/// `def_eq`, since a failing `def_eq` has no early exit.
///
/// Then the theorem itself is APPLIED at row `1` and its inferred type
/// compared against the statement built independently here — so this is not
/// only a check that the identity is true of `Rat.det`, but that the admitted
/// theorem says it.
#[test]
fn det_row_expansion_evaluates_at_every_row_and_pins_the_sign() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::matrix_det::{const_matrix, row_expansion_fn, rq};
    use crate::rat_prelude::ops::{req, rmul, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let mat = const_matrix(&mut d, p, 3, &[1, 2, 0, 0, 1, 3, 2, 0, 1]);
    let two_n = d.num(2);
    let three_n = d.num(3);
    let thirteen = rq(&mut d, p, 13);

    for row in 0..3u32 {
        let i = d.num(row);
        let summand = row_expansion_fn(&mut d, p, mat, i, two_n);
        let total = rsum_range(&mut d, p, summand, three_n);
        assert!(
            d.kernel().def_eq(total, thirteen),
            "expanding the pinned matrix along row {row} must give 13"
        );
    }

    {
        // The same sum with the sign shifted by one: `-13`, so the alternation
        // is load-bearing and this family of checks can fail.
        let nat = d.nat_ty();
        let one_n = d.num(1);
        let summand = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let index = {
                let base = d.add(q, one_n);
                d.succ(base)
            };
            let sign = d.const_app(p.alt_sign, &[index]);
            let entry = d.apply(mat, &[one_n, q]);
            let minor = d.const_app(p.mat_minor, &[mat, one_n, q]);
            let sub = d.const_app(p.det, &[minor, two_n]);
            let product = rmul(&mut d, entry, sub);
            let body = rmul(&mut d, sign, product);
            d.lam_fv(q_fv, nat, body)
        };
        let total = rsum_range(&mut d, p, summand, three_n);
        let negative = rq(&mut d, p, -13);
        assert!(
            d.kernel().def_eq(total, negative),
            "shifting the alternating sign by one must give -13, or the three \
             checks above hold for a reason other than the sign"
        );
    }

    {
        // The admitted theorem, applied at row 1 of a 3x3.
        let one_n = d.num(1);
        let true_ = d.bool_true();
        // `Nat.ble 1 2` iota-reduces to `true`.
        let hble = d.bool_refl(true_);
        let instance = d.const_app(p.det_row_expansion, &[two_n, mat, one_n, hble]);
        let inferred = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("det_row_expansion at row 1 should infer: {e:?}"));

        let summand = row_expansion_fn(&mut d, p, mat, one_n, two_n);
        let expected = {
            let lhs = d.const_app(p.det, &[mat, three_n]);
            let rhs = rsum_range(&mut d, p, summand, three_n);
            req(&mut d, lhs, rhs)
        };
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the admitted `det_row_expansion` does not state the row-1 expansion \
             this test built independently"
        );
    }
}

/// `Rat.det_transpose` and `Rat.det_col_expansion` evaluated at a pinned,
/// **non-symmetric** 3x3, with the two things a transpose test can be vacuous
/// about checked explicitly.
///
/// Vacuity hazard 1: **the matrix could be symmetric**, in which case
/// `matTranspose A` is `A` and `det Aᵀ = det A` says nothing. So the first
/// assertion is that `matTranspose A 0 1` is `0` while `A 0 1` is `2` — the
/// transpose really moves this matrix.
///
/// Vacuity hazard 2: **the column expansion could be the row expansion.** For
/// this matrix both total `13`, and the multiset of summands is `{1, 0, 12}`
/// either way, so a total alone cannot separate them. What does: the row
/// summand at index `1` is `12` and at index `2` is `0`, while the COLUMN
/// summand at those indices is `0` and `12`. Both directions are pinned, so
/// swapping the two builders fails this test rather than passing it.
///
/// The sign is separated the way
/// [`det_row_expansion_evaluates_at_every_row_and_pins_the_sign`] separates
/// it — by the same column sum with the alternation shifted by one, asserted
/// POSITIVELY at `-13` rather than as a failed `def_eq` (a failing `def_eq`
/// has no early exit and is a documented pathology here).
///
/// What this does NOT catch: a wrong `Nat.ble` **guard order** inside
/// `Rat.matSkip`. `det_eval_example` (value `13`) and `det_eq_det2` remain the
/// discriminators for that, exactly as ADR-1135 said.
#[test]
fn det_transpose_and_the_column_expansion_evaluate_and_pin_the_sign() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::matrix_det::{
        col_zero_expansion_fn, const_matrix, row_zero_expansion_fn, rq,
    };
    use crate::rat_prelude::ops::{req, rmul, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    //   A = [[1, 2, 0],
    //        [0, 1, 3],
    //        [2, 0, 1]]        det A 3 = 13   (`Rat.det_eval_example`)
    let mat = const_matrix(&mut d, p, 3, &[1, 2, 0, 0, 1, 3, 2, 0, 1]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let three_n = d.num(3);
    let thirteen = rq(&mut d, p, 13);

    // --- the transpose actually moves this matrix --------------------------
    {
        let transposed = d.const_app(p.mat_transpose, &[mat]);
        let at01 = d.apply(transposed, &[zero_n, one_n]);
        let zero_q = rq(&mut d, p, 0);
        let two_q = rq(&mut d, p, 2);
        assert!(
            d.kernel().def_eq(at01, zero_q),
            "matTranspose A 0 1 must be A 1 0 = 0"
        );
        assert!(
            !d.kernel().def_eq(at01, two_q),
            "matTranspose A 0 1 accepted 2 = A 0 1, so this matrix is symmetric \
             under the transpose and every check below is vacuous"
        );
    }

    // --- `det (matTranspose A) 3 = 13` -------------------------------------
    {
        let transposed = d.const_app(p.mat_transpose, &[mat]);
        let lhs = d.const_app(p.det, &[transposed, three_n]);
        assert!(
            d.kernel().def_eq(lhs, thirteen),
            "det (matTranspose A) 3 must be 13"
        );
    }

    // --- the column expansion totals 13, and is NOT the row expansion ------
    {
        let summand = col_zero_expansion_fn(&mut d, p, mat, two_n);
        let total = rsum_range(&mut d, p, summand, three_n);
        assert!(
            d.kernel().def_eq(total, thirteen),
            "expanding the pinned matrix along column 0 must give 13"
        );
    }
    {
        // Row summand: (1, 12, 0). Column summand: (1, 0, 12). The totals
        // agree and the per-index values do not, which is the only thing here
        // that separates the two builders.
        let col_fn = col_zero_expansion_fn(&mut d, p, mat, two_n);
        let row_fn = row_zero_expansion_fn(&mut d, p, mat, two_n);
        let pins: [(u32, i64, i64); 3] = [(0, 1, 1), (1, 0, 12), (2, 12, 0)];
        for (index, col_value, row_value) in pins {
            let i = d.num(index);
            let col_at = d.apply(col_fn, &[i]);
            let expected_col = rq(&mut d, p, col_value);
            assert!(
                d.kernel().def_eq(col_at, expected_col),
                "the column-0 summand at {index} must be {col_value}"
            );
            let row_at = d.apply(row_fn, &[i]);
            let expected_row = rq(&mut d, p, row_value);
            assert!(
                d.kernel().def_eq(row_at, expected_row),
                "the row-0 summand at {index} must be {row_value}"
            );
        }
    }

    // --- the sign is load-bearing ------------------------------------------
    {
        let nat = d.nat_ty();
        let summand = {
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let index = d.succ(row);
            let sign = d.const_app(p.alt_sign, &[index]);
            let entry = d.apply(mat, &[row, zero_n]);
            let minor = d.const_app(p.mat_minor, &[mat, row, zero_n]);
            let sub = d.const_app(p.det, &[minor, two_n]);
            let product = rmul(&mut d, entry, sub);
            let body = rmul(&mut d, sign, product);
            d.lam_fv(r_fv, nat, body)
        };
        let total = rsum_range(&mut d, p, summand, three_n);
        let negative = rq(&mut d, p, -13);
        assert!(
            d.kernel().def_eq(total, negative),
            "shifting the column expansion's alternating sign by one must give \
             -13, or the checks above hold for a reason other than the sign"
        );
    }

    // --- `Rat.matMinor_transpose`'s content, at a NON-symmetric submatrix ---
    {
        // `matMinor Aᵀ 0 2` is [[2, 1], [0, 3]], which is not symmetric, so a
        // transposed index here is visible. `matMinor Aᵀ 0 1` would be
        // [[2, 0], [0, 1]] and would NOT separate it.
        let transposed = d.const_app(p.mat_transpose, &[mat]);
        let minor = d.const_app(p.mat_minor, &[transposed, zero_n, two_n]);
        let pins: [(u32, u32, i64); 4] = [(0, 0, 2), (0, 1, 1), (1, 0, 0), (1, 1, 3)];
        for (r, c, expected) in pins {
            let r_n = d.num(r);
            let c_n = d.num(c);
            let lhs = d.apply(minor, &[r_n, c_n]);
            let rhs = rq(&mut d, p, expected);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "matMinor (matTranspose A) 0 2 {r} {c} must be {expected}"
            );
        }
    }

    // --- the admitted theorems say what this test built independently ------
    {
        let instance = d.const_app(p.det_col_expansion, &[two_n, mat]);
        let inferred = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("det_col_expansion at m = 2 should infer: {e:?}"));
        let summand = col_zero_expansion_fn(&mut d, p, mat, two_n);
        let expected = {
            let lhs = d.const_app(p.det, &[mat, three_n]);
            let rhs = rsum_range(&mut d, p, summand, three_n);
            req(&mut d, lhs, rhs)
        };
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the admitted `det_col_expansion` does not state the column-0 \
             expansion this test built independently"
        );
    }
    {
        let instance = d.const_app(p.det_transpose, &[three_n, mat]);
        let inferred = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("det_transpose at n = 3 should infer: {e:?}"));
        let expected = {
            let transposed = d.const_app(p.mat_transpose, &[mat]);
            let lhs = d.const_app(p.det, &[transposed, three_n]);
            let rhs = d.const_app(p.det, &[mat, three_n]);
            req(&mut d, lhs, rhs)
        };
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the admitted `det_transpose` does not state transpose invariance \
             at the dimension this test supplied"
        );
    }
}

/// `Rat.det_transpose` quantifies over the MATRIX and over the DIMENSION, and
/// the dimension is an argument of `Rat.det` rather than a numeral.
///
/// The pin that a later edit cannot quietly weaken: an instance at a concrete
/// matrix, or at a fixed dimension, would leave `matrix_det`'s module doc
/// describing a law it no longer proves — the same failure mode
/// [`the_determinant_agreement_statements_quantify_over_the_matrix`] guards
/// for `det_eq_det2`.
#[test]
fn the_transpose_and_column_statements_quantify_over_matrix_and_dimension() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel.render_lean(ty)
    };

    let transpose = rendered(&mut kernel, p.det_transpose);
    assert_eq!(
        transpose,
        "((x0 : AxNat) -> ((x1 : ((x1 : AxNat) -> ((x2 : AxNat) -> Rat))) -> \
         Eq.{1} Rat (Rat.det (Rat.matTranspose x1) x0) (Rat.det x1 x0)))",
        "Rat.det_transpose no longer states transpose invariance at a symbolic \
         dimension for an arbitrary matrix"
    );

    let column = rendered(&mut kernel, p.det_col_expansion);
    assert_eq!(
        column,
        "((x0 : AxNat) -> ((x1 : ((x1 : AxNat) -> ((x2 : AxNat) -> Rat))) -> \
         Eq.{1} Rat (Rat.det x1 (AxNat.succ x0)) \
         (Rat.sumRange (fun (x2 : AxNat) => Rat.mul (Rat.altSign x2) \
         (Rat.mul (x1 x2 AxNat.zero) \
         (Rat.det (Rat.matMinor x1 x2 AxNat.zero) x0))) (AxNat.succ x0))))",
        "Rat.det_col_expansion no longer states cofactor expansion along the \
         first column"
    );
}
