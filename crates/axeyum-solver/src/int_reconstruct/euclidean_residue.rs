use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_lean_kernel::BinderInfo;

use crate::quant_residue_cert::{
    IntEuclideanResidueRefutationCertificate, int_euclidean_residue_refutation,
};
use crate::reconstruct::ReconstructError;

use super::{DIO_UNIT_MAX, IntReconstructCtx, peel_closed_foralls};

/// Returns whether `assertions` has the canonical ADR-0104 clock spelling.
/// This router predicate is intentionally narrower than ADR-0095's independent
/// evidence matcher: the Lean proof currently preserves one exact binder,
/// arithmetic, and parser-preserved disjunction orientation.
pub(crate) fn int_euclidean_residue_lean_shape(arena: &TermArena, assertions: &[TermId]) -> bool {
    canonical_int_euclidean_residue(arena, assertions).is_some()
}

/// Reconstruct the canonical ADR-0095 Euclidean-residue refutation using the
/// general ADR-0104 integer-prelude decomposition theorem.
///
/// The only query axiom is the original universal. The decomposition theorem
/// supplies existential quotient/remainder witnesses; `Exists.rec` exposes
/// their recomposition and bounds, and three `Or.rec` branches contradict those
/// facts. No query-specific witness or refuter axiom is introduced.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] if the certificate is invalid,
/// the assertion is outside the canonical Lean slice, or the modulus exceeds
/// the bounded literal representation. Returns
/// [`ReconstructError::KernelRejected`] if the assembled proof does not infer to
/// `False`.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_int_euclidean_residue_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntEuclideanResidueRefutationCertificate,
) -> Result<String, ReconstructError> {
    if int_euclidean_residue_refutation(arena, assertions) != Some(*certificate) {
        return Err(residue_decline("invalid refutation certificate"));
    }
    let Some(canonical) = canonical_int_euclidean_residue(arena, assertions) else {
        return Err(residue_decline(
            "assertion is outside the canonical clock proof shape",
        ));
    };
    if canonical != *certificate {
        return Err(residue_decline(
            "certificate does not match the canonical assertion",
        ));
    }
    if certificate.modulus.unsigned_abs() > DIO_UNIT_MAX as u128 {
        return Err(residue_decline("modulus exceeds proof-size cap"));
    }

    let mut ctx = IntReconstructCtx::new();
    let dividend_name = ctx.var_const(0);
    let dividend = ctx.kernel.const_(dividend_name, Vec::new());
    let modulus = ctx.mk_intlit(certificate.modulus);
    let zero = ctx.mk_zero();

    // Faithfully encode the canonical input theorem with open fvars, then
    // abstract quotient followed by remainder to recover binder order `s, m`.
    let remainder_id = ctx.fresh_fvar();
    let quotient_id = ctx.fresh_fvar();
    let remainder = ctx.kernel.fvar(remainder_id);
    let quotient = ctx.kernel.fvar(quotient_id);
    let scaled = ctx.mk_mul(modulus, quotient);
    let sum = ctx.mk_add(scaled, remainder);
    let sum_eq_dividend = ctx.mk_eq(sum, dividend);
    let recomposition_disjunct = ctx.mk_not(sum_eq_dividend);
    let lower_disjunct = ctx.mk_lt(remainder, zero);
    let upper_disjunct = ctx.mk_le(modulus, remainder);
    let disequality_or_lower = ctx.mk_or(recomposition_disjunct, lower_disjunct);
    let universal_body = ctx.mk_or(disequality_or_lower, upper_disjunct);
    let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
    let anon = ctx.kernel.anon();
    let quotient_body = ctx.kernel.abstract_fvars(universal_body, &[quotient_id]);
    let after_quotient = ctx
        .kernel
        .pi(anon, z_ty, quotient_body, BinderInfo::Default);
    let remainder_body = ctx.kernel.abstract_fvars(after_quotient, &[remainder_id]);
    let universal_ty = ctx
        .kernel
        .pi(anon, z_ty, remainder_body, BinderInfo::Default);
    let universal = ctx.hyp_axiom(universal_ty)?;

    // Build exactly the existential proposition exposed by the prelude theorem.
    let theorem_recomposition = ctx.mk_eq(dividend, sum);
    let nonnegative = ctx.mk_le(zero, remainder);
    let below_modulus = ctx.mk_lt(remainder, modulus);
    let bounds = ctx.mk_and(nonnegative, below_modulus);
    let facts = ctx.mk_and(theorem_recomposition, bounds);
    let r_body = ctx.kernel.abstract_fvars(facts, &[remainder_id]);
    let r_predicate = ctx.kernel.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists_r = ctx.mk_exists(r_predicate);
    let q_body = ctx.kernel.abstract_fvars(exists_r, &[quotient_id]);
    let q_predicate = ctx.kernel.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists_q = ctx.mk_exists(q_predicate);

    let positive = ctx.lt_zero_intlit(certificate.modulus)?;
    let decomposition = ctx
        .kernel
        .const_(ctx.int.euclidean_decomposition, Vec::new());
    let decomposition = ctx.kernel.app(decomposition, dividend);
    let decomposition = ctx.kernel.app(decomposition, modulus);
    let decomposition = ctx.kernel.app(decomposition, positive);

    // Open the quotient witness, then the remainder witness and its conjunction.
    let q_major_id = ctx.fresh_fvar();
    let q_major = ctx.kernel.fvar(q_major_id);
    let facts_id = ctx.fresh_fvar();
    let facts_proof = ctx.kernel.fvar(facts_id);
    let recomposition = ctx.and_project(theorem_recomposition, bounds, facts_proof, true);
    let bounds_proof = ctx.and_project(theorem_recomposition, bounds, facts_proof, false);
    let nonnegative_proof = ctx.and_project(nonnegative, below_modulus, bounds_proof, true);
    let below_modulus_proof = ctx.and_project(nonnegative, below_modulus, bounds_proof, false);
    let universal_instance = ctx.kernel.app(universal, remainder);
    let universal_instance = ctx.kernel.app(universal_instance, quotient);

    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());

    // Branch 1: `k*q+r != t`, contradicted by `t = k*q+r` symmetry.
    let disequality_id = ctx.fresh_fvar();
    let disequality = ctx.kernel.fvar(disequality_id);
    let sum_equals_dividend = ctx.eq_symm(dividend, sum, recomposition);
    let first_false = ctx.kernel.app(disequality, sum_equals_dividend);
    let first_body = ctx.kernel.abstract_fvars(first_false, &[disequality_id]);
    let first_case = ctx.kernel.lam(
        anon,
        recomposition_disjunct,
        first_body,
        BinderInfo::Default,
    );

    // Branch 2: `r < 0`, contradicted by `0 <= r`.
    let lower_id = ctx.fresh_fvar();
    let lower_proof = ctx.kernel.fvar(lower_id);
    let lower_self =
        ctx.lt_of_lt_of_le_app(remainder, zero, remainder, lower_proof, nonnegative_proof);
    let lower_irrefl = ctx.lt_irrefl_app(remainder);
    let lower_false = ctx.kernel.app(lower_irrefl, lower_self);
    let lower_body = ctx.kernel.abstract_fvars(lower_false, &[lower_id]);
    let lower_case = ctx
        .kernel
        .lam(anon, lower_disjunct, lower_body, BinderInfo::Default);

    // Branch 3: `k <= r`, contradicted by `r < k`.
    let upper_id = ctx.fresh_fvar();
    let upper_proof = ctx.kernel.fvar(upper_id);
    let upper_self = ctx.lt_of_lt_of_le_app(
        remainder,
        modulus,
        remainder,
        below_modulus_proof,
        upper_proof,
    );
    let upper_irrefl = ctx.lt_irrefl_app(remainder);
    let upper_false = ctx.kernel.app(upper_irrefl, upper_self);
    let upper_body = ctx.kernel.abstract_fvars(upper_false, &[upper_id]);
    let upper_case = ctx
        .kernel
        .lam(anon, upper_disjunct, upper_body, BinderInfo::Default);

    let left_id = ctx.fresh_fvar();
    let left_proof = ctx.kernel.fvar(left_id);
    let left_false = ctx.or_rec_prop(
        recomposition_disjunct,
        lower_disjunct,
        false_,
        first_case,
        lower_case,
        left_proof,
    );
    let left_body = ctx.kernel.abstract_fvars(left_false, &[left_id]);
    let left_case = ctx
        .kernel
        .lam(anon, disequality_or_lower, left_body, BinderInfo::Default);
    let contradiction = ctx.or_rec_prop(
        disequality_or_lower,
        upper_disjunct,
        false_,
        left_case,
        upper_case,
        universal_instance,
    );

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

    let inferred =
        ctx.kernel_mut()
            .infer(proof)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "int_euclidean_residue".to_owned(),
                detail: format!("infer failed: {error:?}"),
            })?;
    if !ctx.kernel_mut().def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "int_euclidean_residue".to_owned(),
            detail: "residue reconstruction did not infer to False".to_owned(),
        });
    }
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

fn residue_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("integer Euclidean residue: {detail}"),
    }
}

#[allow(clippy::too_many_lines)]
fn canonical_int_euclidean_residue(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntEuclideanResidueRefutationCertificate> {
    let [assertion] = assertions else {
        return None;
    };
    let certificate = int_euclidean_residue_refutation(arena, assertions)?;
    if certificate.assertion != *assertion {
        return None;
    }
    let (binders, body) = peel_closed_foralls(arena, *assertion)?;
    if binders != [certificate.remainder, certificate.quotient] {
        return None;
    }
    let TermNode::Symbol(dividend) = arena.node(certificate.dividend) else {
        return None;
    };
    if *dividend == certificate.remainder
        || *dividend == certificate.quotient
        || arena.symbol(*dividend).1 != Sort::Int
    {
        return None;
    }
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [disequality_or_lower, upper] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(*disequality_or_lower)
    else {
        return None;
    };
    let [disequality, lower] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(*disequality)
    else {
        return None;
    };
    let [equality] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*equality) else {
        return None;
    };
    let [sum, found_dividend] = &**args else {
        return None;
    };
    if *found_dividend != certificate.dividend {
        return None;
    }
    let TermNode::App {
        op: Op::IntAdd,
        args,
    } = arena.node(*sum)
    else {
        return None;
    };
    let [scaled, found_remainder] = &**args else {
        return None;
    };
    if !matches!(arena.node(*found_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(*scaled)
    else {
        return None;
    };
    let [found_modulus, found_quotient] = &**args else {
        return None;
    };
    if !matches!(arena.node(*found_modulus), TermNode::IntConst(found) if *found == certificate.modulus)
        || !matches!(arena.node(*found_quotient), TermNode::Symbol(found) if *found == certificate.quotient)
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntLt,
        args,
    } = arena.node(*lower)
    else {
        return None;
    };
    let [lower_remainder, lower_zero] = &**args else {
        return None;
    };
    if !matches!(arena.node(*lower_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
        || !matches!(arena.node(*lower_zero), TermNode::IntConst(0))
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(*upper)
    else {
        return None;
    };
    let [upper_remainder, upper_modulus] = &**args else {
        return None;
    };
    if !matches!(arena.node(*upper_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
        || !matches!(arena.node(*upper_modulus), TermNode::IntConst(found) if *found == certificate.modulus)
    {
        return None;
    }
    Some(certificate)
}
