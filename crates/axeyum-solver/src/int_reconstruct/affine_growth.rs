use std::collections::BTreeMap;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_lean_kernel::{BinderInfo, ExprId};

use crate::quant_affine_growth_cert::{
    IntAffineGrowthRefutationCertificate, int_affine_growth_refutation,
};
use crate::reconstruct::ReconstructError;

use super::{DIO_UNIT_MAX, IntReconstructCtx, peel_closed_foralls};

/// Returns whether ADR-0097's independent checker recognizes a proof shape.
/// Certificate regeneration and kernel inference remain the authoritative
/// acceptance gates.
pub(crate) fn int_affine_growth_lean_shape(arena: &TermArena, assertions: &[TermId]) -> bool {
    int_affine_growth_refutation(arena, assertions).is_some()
}

#[derive(Debug, Clone, Copy)]
struct AffineGrowthProps {
    body: ExprId,
    equality: ExprId,
    then_implication: ExprId,
    else_guard: ExprId,
    else_implication: ExprId,
}

/// Reconstruct an ADR-0097 positive-slope affine-growth certificate through
/// ADR-0104's Euclidean decomposition theorem, guarded exact `ite` semantics,
/// and two consecutive universal instances.
///
/// Bound-variable-free parameter terms are represented by consistently shared
/// opaque integer constants. This is a denotational abstraction of their fixed
/// values, while every original quantified binder remains a genuine dependent
/// product. No query-specific witness/refuter axiom or additional arithmetic
/// theorem is introduced.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for an invalid certificate,
/// malformed universal prefix, or coefficient beyond the proof-size cap, and
/// [`ReconstructError::KernelRejected`] if any generated proof fails its kernel
/// gate.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_int_affine_growth_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntAffineGrowthRefutationCertificate,
) -> Result<String, ReconstructError> {
    if int_affine_growth_refutation(arena, assertions) != Some(*certificate) {
        return Err(affine_growth_decline("invalid refutation certificate"));
    }
    if certificate.coefficient <= 0 || certificate.coefficient.unsigned_abs() > DIO_UNIT_MAX as u128
    {
        return Err(affine_growth_decline(
            "coefficient is non-positive or exceeds proof-size cap",
        ));
    }
    let Some((binders, _)) = peel_closed_foralls(arena, certificate.assertion) else {
        return Err(affine_growth_decline(
            "certificate assertion is not a universal prefix",
        ));
    };
    if binders.is_empty()
        || binders
            .iter()
            .any(|&binder| arena.symbol(binder).1 != Sort::Int)
        || !binders.contains(&certificate.variable)
    {
        return Err(affine_growth_decline(
            "universal prefix is not the checked all-Int class",
        ));
    }

    let mut ctx = IntReconstructCtx::new();
    let mut parameter_indices = BTreeMap::new();
    for term in [
        certificate.pivot,
        certificate.then_value,
        certificate.else_value,
        certificate.threshold,
    ] {
        let next = parameter_indices.len();
        parameter_indices.entry(term).or_insert(next);
    }
    let pivot = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.pivot);
    let then_value = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.then_value);
    let else_value = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.else_value);
    let threshold = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.threshold);
    let coefficient = ctx.mk_intlit(certificate.coefficient);

    // Encode the complete universal. The integer `ite` is represented exactly
    // by its two guarded branch implications.
    let mut binder_fvars = BTreeMap::new();
    for &binder in &binders {
        let id = ctx.fresh_fvar();
        binder_fvars.insert(binder, id);
    }
    let active_id = binder_fvars[&certificate.variable];
    let active = ctx.kernel.fvar(active_id);
    let open_props = affine_growth_props(
        &mut ctx,
        active,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
    let anon = ctx.kernel.anon();
    let mut universal_ty = open_props.body;
    for &binder in binders.iter().rev() {
        universal_ty = ctx
            .kernel
            .abstract_fvars(universal_ty, &[binder_fvars[&binder]]);
        universal_ty = ctx.kernel.pi(anon, z_ty, universal_ty, BinderInfo::Default);
    }
    let universal = ctx.hyp_axiom(universal_ty)?;

    // Apply Euclidean decomposition to the fixed value `b+t`.
    let dividend = ctx.mk_add(else_value, threshold);
    let quotient_id = ctx.fresh_fvar();
    let remainder_id = ctx.fresh_fvar();
    let quotient = ctx.kernel.fvar(quotient_id);
    let remainder = ctx.kernel.fvar(remainder_id);
    let scaled_quotient = ctx.mk_mul(coefficient, quotient);
    let decomposition_sum = ctx.mk_add(scaled_quotient, remainder);
    let recomposition = ctx.mk_eq(dividend, decomposition_sum);
    let zero = ctx.mk_zero();
    let nonnegative = ctx.mk_le(zero, remainder);
    let below_coefficient = ctx.mk_lt(remainder, coefficient);
    let bounds = ctx.mk_and(nonnegative, below_coefficient);
    let facts = ctx.mk_and(recomposition, bounds);
    let r_body = ctx.kernel.abstract_fvars(facts, &[remainder_id]);
    let r_predicate = ctx.kernel.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists_r = ctx.mk_exists(r_predicate);
    let q_body = ctx.kernel.abstract_fvars(exists_r, &[quotient_id]);
    let q_predicate = ctx.kernel.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists_q = ctx.mk_exists(q_predicate);
    let positive = ctx.lt_zero_intlit(certificate.coefficient)?;
    let decomposition = ctx
        .kernel
        .const_(ctx.int.euclidean_decomposition, Vec::new());
    let decomposition = ctx.kernel.app(decomposition, dividend);
    let decomposition = ctx.kernel.app(decomposition, coefficient);
    let decomposition = ctx.kernel.app(decomposition, positive);
    ctx.require_affine_growth_type(decomposition, exists_q, "Euclidean decomposition")?;

    let q_major_id = ctx.fresh_fvar();
    let q_major = ctx.kernel.fvar(q_major_id);
    let facts_id = ctx.fresh_fvar();
    let facts_proof = ctx.kernel.fvar(facts_id);
    let recomposition_proof = ctx.and_project(recomposition, bounds, facts_proof, true);
    let bounds_proof = ctx.and_project(recomposition, bounds, facts_proof, false);
    let below_proof = ctx.and_project(nonnegative, below_coefficient, bounds_proof, false);

    let one = ctx.mk_one();
    let first = ctx.mk_add(quotient, one);
    let second = ctx.mk_add(first, one);
    let first_scaled = ctx.mk_mul(coefficient, first);
    let second_scaled = ctx.mk_mul(coefficient, second);
    let neg_else = ctx.mk_neg(else_value);
    let first_difference = ctx.mk_add(first_scaled, neg_else);
    let second_difference = ctx.mk_add(second_scaled, neg_else);

    // b+t = c*q+r and r<c imply b+t <= c*q+c = c*(q+1).
    let remainder_le_coefficient = ctx.le_of_lt_app(remainder, coefficient, below_proof);
    let scaled_refl = ctx.le_refl_app(scaled_quotient);
    let sum_le_sum = ctx.add_le_add_app(
        scaled_quotient,
        scaled_quotient,
        remainder,
        coefficient,
        scaled_refl,
        remainder_le_coefficient,
    );
    let scaled_plus_coefficient = ctx.mk_add(scaled_quotient, coefficient);
    let distributed = ctx.left_distrib_eq(coefficient, quotient, one);
    let coefficient_times_one = ctx.mk_mul(coefficient, one);
    let mul_one = ctx.mul_one_eq(coefficient);
    let collapse_one =
        ctx.congr_add_right(scaled_quotient, coefficient_times_one, coefficient, mul_one);
    let scaled_plus_times_one = ctx.mk_add(scaled_quotient, coefficient_times_one);
    let first_scaled_to_sum = ctx.eq_trans(
        first_scaled,
        scaled_plus_times_one,
        scaled_plus_coefficient,
        distributed,
        collapse_one,
    );
    let sum_to_first_scaled =
        ctx.eq_symm(first_scaled, scaled_plus_coefficient, first_scaled_to_sum);
    let sum_eq_dividend = ctx.eq_symm(dividend, decomposition_sum, recomposition_proof);
    let dividend_le_sum = ctx.le_cast_left(
        decomposition_sum,
        dividend,
        scaled_plus_coefficient,
        sum_le_sum,
        sum_eq_dividend,
    );
    let dividend_le_first_scaled = ctx.le_cast_right(
        dividend,
        scaled_plus_coefficient,
        first_scaled,
        dividend_le_sum,
        sum_to_first_scaled,
    );

    // Add `-b` to both sides and normalize `-b+(b+t)` to `t`.
    let neg_else_refl = ctx.le_refl_app(neg_else);
    let shifted = ctx.add_le_add_app(
        neg_else,
        neg_else,
        dividend,
        first_scaled,
        neg_else_refl,
        dividend_le_first_scaled,
    );
    let shifted_left = ctx.mk_add(neg_else, dividend);
    let shifted_right = ctx.mk_add(neg_else, first_scaled);
    let left_to_threshold = ctx.prove_neg_add_sum_eq(else_value, threshold);
    let threshold_le_shifted = ctx.le_cast_left(
        shifted_left,
        threshold,
        shifted_right,
        shifted,
        left_to_threshold,
    );
    let right_to_first_difference = ctx.add_comm_eq(neg_else, first_scaled);
    let first_inequality = ctx.le_cast_right(
        threshold,
        shifted_right,
        first_difference,
        threshold_le_shifted,
        right_to_first_difference,
    );

    // Positive slope makes the second consecutive candidate at least as large.
    let zero_le_coefficient = ctx.le_of_lt_app(zero, coefficient, positive);
    let first_lt_second = ctx.prove_successor_lt(first);
    let first_le_second = ctx.le_of_lt_app(first, second, first_lt_second);
    let scaled_monotone = ctx.mul_le_mul_left_app(
        coefficient,
        first,
        second,
        zero_le_coefficient,
        first_le_second,
    );
    let neg_else_refl = ctx.le_refl_app(neg_else);
    let difference_monotone = ctx.add_le_add_app(
        first_scaled,
        second_scaled,
        neg_else,
        neg_else,
        scaled_monotone,
        neg_else_refl,
    );
    let second_inequality = ctx.le_trans_app(
        threshold,
        first_difference,
        second_difference,
        first_inequality,
        difference_monotone,
    );

    let first_props = affine_growth_props(
        &mut ctx,
        first,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let second_props = affine_growth_props(
        &mut ctx,
        second,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let first_instance = instantiate_affine_growth_universal(
        &mut ctx,
        universal,
        &binders,
        certificate.variable,
        first,
    );
    let second_instance = instantiate_affine_growth_universal(
        &mut ctx,
        universal,
        &binders,
        certificate.variable,
        second,
    );

    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());

    // Each guarded else branch plus its positive affine comparison proves
    // `Not (Not (candidate = pivot))` constructively.
    let second_else = ctx.and_project(
        second_props.then_implication,
        second_props.else_implication,
        second_instance,
        false,
    );
    let second_guard_id = ctx.fresh_fvar();
    let second_guard = ctx.kernel.fvar(second_guard_id);
    let second_negated = ctx.kernel.app(second_else, second_guard);
    let second_guard_false = ctx.kernel.app(second_negated, second_inequality);
    let second_guard_body = ctx
        .kernel
        .abstract_fvars(second_guard_false, &[second_guard_id]);
    let double_neg_second = ctx.kernel.lam(
        anon,
        second_props.else_guard,
        second_guard_body,
        BinderInfo::Default,
    );

    let first_else = ctx.and_project(
        first_props.then_implication,
        first_props.else_implication,
        first_instance,
        false,
    );
    let first_guard_id = ctx.fresh_fvar();
    let first_guard = ctx.kernel.fvar(first_guard_id);
    let first_negated = ctx.kernel.app(first_else, first_guard);
    let first_guard_false = ctx.kernel.app(first_negated, first_inequality);
    let first_guard_body = ctx
        .kernel
        .abstract_fvars(first_guard_false, &[first_guard_id]);
    let double_neg_first = ctx.kernel.lam(
        anon,
        first_props.else_guard,
        first_guard_body,
        BinderInfo::Default,
    );

    // If the first candidate equals the pivot, strict consecutiveness makes
    // the second candidate unequal to it; that contradicts the second double
    // negation. Hence the first candidate is unequal, contradicting its own
    // double negation. No excluded middle is required.
    let first_eq_id = ctx.fresh_fvar();
    let first_eq_pivot = ctx.kernel.fvar(first_eq_id);
    let second_eq_id = ctx.fresh_fvar();
    let second_eq_pivot = ctx.kernel.fvar(second_eq_id);
    let pivot_eq_second = ctx.eq_symm(second, pivot, second_eq_pivot);
    let first_eq_second = ctx.eq_trans(first, pivot, second, first_eq_pivot, pivot_eq_second);
    let second_eq_first = ctx.eq_symm(first, second, first_eq_second);
    let first_self_lt = ctx.lt_cast_right(first, second, first, first_lt_second, second_eq_first);
    let first_irrefl = ctx.lt_irrefl_app(first);
    let distinct_false = ctx.kernel.app(first_irrefl, first_self_lt);
    let second_eq_body = ctx.kernel.abstract_fvars(distinct_false, &[second_eq_id]);
    let second_not_pivot = ctx.kernel.lam(
        anon,
        second_props.equality,
        second_eq_body,
        BinderInfo::Default,
    );
    let first_eq_false = ctx.kernel.app(double_neg_second, second_not_pivot);
    let first_eq_body = ctx.kernel.abstract_fvars(first_eq_false, &[first_eq_id]);
    let first_not_pivot = ctx.kernel.lam(
        anon,
        first_props.equality,
        first_eq_body,
        BinderInfo::Default,
    );
    let contradiction = ctx.kernel.app(double_neg_first, first_not_pivot);

    let facts_body = ctx.kernel.abstract_fvars(contradiction, &[facts_id]);
    let facts_minor = ctx.kernel.lam(anon, facts, facts_body, BinderInfo::Default);
    let r_minor_body = ctx.kernel.abstract_fvars(facts_minor, &[remainder_id]);
    let r_minor = ctx
        .kernel
        .lam(anon, z_ty, r_minor_body, BinderInfo::Default);
    let q_false = ctx.exists_elim_false(r_predicate, exists_r, r_minor, q_major);
    let q_major_body = ctx.kernel.abstract_fvars(q_false, &[q_major_id]);
    let q_major_minor = ctx
        .kernel
        .lam(anon, exists_r, q_major_body, BinderInfo::Default);
    let q_minor_body = ctx.kernel.abstract_fvars(q_major_minor, &[quotient_id]);
    let q_minor = ctx
        .kernel
        .lam(anon, z_ty, q_minor_body, BinderInfo::Default);
    let proof = ctx.exists_elim_false(q_predicate, exists_q, q_minor, decomposition);
    ctx.require_affine_growth_type(proof, false_, "final contradiction")?;
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

fn affine_growth_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("integer affine growth: {detail}"),
    }
}

fn affine_parameter_expr(
    ctx: &mut IntReconstructCtx,
    indices: &BTreeMap<TermId, usize>,
    term: TermId,
) -> ExprId {
    let name = ctx.var_const(indices[&term]);
    ctx.kernel.const_(name, Vec::new())
}

fn affine_growth_props(
    ctx: &mut IntReconstructCtx,
    variable: ExprId,
    coefficient: ExprId,
    pivot: ExprId,
    then_value: ExprId,
    else_value: ExprId,
    threshold: ExprId,
) -> AffineGrowthProps {
    let equality = ctx.mk_eq(variable, pivot);
    let not_equality = ctx.mk_not(equality);
    let scaled = ctx.mk_mul(coefficient, variable);
    let neg_then = ctx.mk_neg(then_value);
    let then_difference = ctx.mk_add(scaled, neg_then);
    let then_comparison = ctx.mk_le(threshold, then_difference);
    let then_negated = ctx.mk_not(then_comparison);
    let neg_else = ctx.mk_neg(else_value);
    let else_difference = ctx.mk_add(scaled, neg_else);
    let else_comparison = ctx.mk_le(threshold, else_difference);
    let else_negated = ctx.mk_not(else_comparison);
    let anon = ctx.kernel.anon();
    let then_implication = ctx
        .kernel
        .pi(anon, equality, then_negated, BinderInfo::Default);
    let else_implication = ctx
        .kernel
        .pi(anon, not_equality, else_negated, BinderInfo::Default);
    let body = ctx.mk_and(then_implication, else_implication);
    AffineGrowthProps {
        body,
        equality,
        then_implication,
        else_guard: not_equality,
        else_implication,
    }
}

fn instantiate_affine_growth_universal(
    ctx: &mut IntReconstructCtx,
    universal: ExprId,
    binders: &[SymbolId],
    active: SymbolId,
    candidate: ExprId,
) -> ExprId {
    let mut proof = universal;
    for &binder in binders {
        let witness = if binder == active {
            candidate
        } else {
            ctx.mk_zero()
        };
        proof = ctx.kernel.app(proof, witness);
    }
    proof
}
