use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId};

use crate::quant_bool_model_sat::admitted_free_booleans;
use crate::quant_counterexample_cover::{
    QuantifiedCounterexampleCoverCase, QuantifiedCounterexampleCoverCertificate,
    check_quantified_counterexample_cover,
};
use crate::reconstruct::ReconstructError;

use super::{
    IntReconstructCtx, ground_int_term_fits_proof_unit_budget, int_values_fit_proof_unit_budget,
    lin_to_canon_gens, source_int_literals_fit_proof_unit_budget,
};

// ---------------------------------------------------------------------------
// ADR-0108: source-instantiated quantified counterexample covers.

type CoverKernelEnv = BTreeMap<SymbolId, ExprId>;
type CoverFreeProps = BTreeMap<SymbolId, ExprId>;

#[derive(Debug, Clone, Copy)]
struct CoverSignedProof {
    truth: bool,
    proof: ExprId,
}

fn cover_decline(detail: impl Into<String>) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("quantified counterexample cover: {}", detail.into()),
    }
}

fn cover_bool_carrier(ctx: &mut IntReconstructCtx) -> ExprId {
    ctx.kernel.const_(ctx.int.logic.bool_, Vec::new())
}

fn cover_bool_literal(ctx: &mut IntReconstructCtx, value: bool) -> ExprId {
    ctx.kernel.const_(
        if value {
            ctx.int.logic.bool_true
        } else {
            ctx.int.logic.bool_false
        },
        Vec::new(),
    )
}

fn cover_bool_value_prop(ctx: &mut IntReconstructCtx, value: ExprId) -> ExprId {
    let true_value = cover_bool_literal(ctx, true);
    ctx.mk_bool_eq(value, true_value)
}

fn cover_bool_value(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    bool_env: &CoverKernelEnv,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Ok(cover_bool_literal(ctx, *value)),
        TermNode::Symbol(symbol) => bool_env
            .get(symbol)
            .copied()
            .ok_or_else(|| cover_decline("free Bool occurs in an integer ite condition")),
        _ => Err(cover_decline(
            "integer ite condition is not a bound Bool symbol or literal",
        )),
    }
}

fn cover_int_term(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: Option<&Assignment>,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::IntConst(value) => {
            if !int_values_fit_proof_unit_budget([*value]) {
                return Err(cover_decline("integer literal exceeds proof-size cap"));
            }
            Ok(ctx.mk_intlit(*value))
        }
        TermNode::Symbol(symbol) => int_env
            .get(symbol)
            .copied()
            .ok_or_else(|| cover_decline("free Int symbol in admitted cover")),
        TermNode::App { op, args } => match (op, &**args) {
            (Op::IntNeg, [argument]) => {
                let argument = cover_int_term(ctx, arena, *argument, int_env, bool_env, values)?;
                Ok(ctx.mk_neg(argument))
            }
            (Op::IntAdd, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_add(left, right))
            }
            (Op::IntSub, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                let right = ctx.mk_neg(right);
                Ok(ctx.mk_add(left, right))
            }
            (Op::IntMul, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_mul(left, right))
            }
            (Op::Ite, [condition, then_term, else_term]) => {
                if let Some(values) = values {
                    match eval(arena, *condition, values) {
                        Ok(Value::Bool(true)) => {
                            return cover_int_term(
                                ctx,
                                arena,
                                *then_term,
                                int_env,
                                bool_env,
                                Some(values),
                            );
                        }
                        Ok(Value::Bool(false)) => {
                            return cover_int_term(
                                ctx,
                                arena,
                                *else_term,
                                int_env,
                                bool_env,
                                Some(values),
                            );
                        }
                        _ => {}
                    }
                }
                let condition = cover_bool_value(ctx, arena, *condition, bool_env)?;
                let then_term = cover_int_term(ctx, arena, *then_term, int_env, bool_env, values)?;
                let else_term = cover_int_term(ctx, arena, *else_term, int_env, bool_env, values)?;
                let bool_ty = cover_bool_carrier(ctx);
                let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
                let anon = ctx.kernel.anon();
                let motive = ctx.kernel.lam(anon, bool_ty, z_ty, BinderInfo::Default);
                let zero = ctx.kernel.level_zero();
                let one = ctx.kernel.level_succ(zero);
                let rec = ctx.kernel.const_(ctx.int.logic.bool_rec, vec![one]);
                let rec = ctx.kernel.app(rec, motive);
                let rec = ctx.kernel.app(rec, then_term);
                let rec = ctx.kernel.app(rec, else_term);
                Ok(ctx.kernel.app(rec, condition))
            }
            _ => Err(cover_decline("unsupported integer operator")),
        },
        _ => Err(cover_decline("unsupported integer term")),
    }
}

#[allow(clippy::too_many_lines)]
fn cover_formula_prop(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: Option<&Assignment>,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(value) => {
            let value = cover_bool_literal(ctx, *value);
            Ok(cover_bool_value_prop(ctx, value))
        }
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            if let Some(value) = bool_env.get(symbol).copied() {
                Ok(cover_bool_value_prop(ctx, value))
            } else {
                free_props
                    .get(symbol)
                    .copied()
                    .ok_or_else(|| cover_decline("unregistered free Bool symbol"))
            }
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => {
                let argument = cover_formula_prop(
                    ctx, arena, *argument, int_env, bool_env, free_props, values,
                )?;
                Ok(ctx.mk_not(argument))
            }
            (Op::BoolAnd, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_and(left, right))
            }
            (Op::BoolOr, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_or(left, right))
            }
            (Op::BoolImplies, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                let anon = ctx.kernel.anon();
                Ok(ctx.kernel.pi(anon, left, right, BinderInfo::Default))
            }
            (Op::BoolXor, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                let iff = ctx.mk_iff(left, right);
                Ok(ctx.mk_not(iff))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_iff(left, right))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_eq(left, right))
            }
            (Op::IntLt, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_lt(left, right))
            }
            (Op::IntLe, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_le(left, right))
            }
            (Op::IntGt, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_lt(right, left))
            }
            (Op::IntGe, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_le(right, left))
            }
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                let condition = cover_formula_prop(
                    ctx, arena, *condition, int_env, bool_env, free_props, values,
                )?;
                let then_term = cover_formula_prop(
                    ctx, arena, *then_term, int_env, bool_env, free_props, values,
                )?;
                let else_term = cover_formula_prop(
                    ctx, arena, *else_term, int_env, bool_env, free_props, values,
                )?;
                let positive = ctx.mk_and(condition, then_term);
                let negative_condition = ctx.mk_not(condition);
                let negative = ctx.mk_and(negative_condition, else_term);
                Ok(ctx.mk_or(positive, negative))
            }
            (Op::Forall(symbol), [body]) => {
                let sort = arena.symbol(*symbol).1;
                let id = ctx.fresh_fvar();
                let variable = ctx.kernel.fvar(id);
                match sort {
                    Sort::Int => {
                        int_env.insert(*symbol, variable);
                    }
                    Sort::Bool => {
                        bool_env.insert(*symbol, variable);
                    }
                    _ => return Err(cover_decline("non-Bool/Int universal binder")),
                }
                let body =
                    cover_formula_prop(ctx, arena, *body, int_env, bool_env, free_props, values)?;
                int_env.remove(symbol);
                bool_env.remove(symbol);
                let body = ctx.kernel.abstract_fvars(body, &[id]);
                let carrier = match sort {
                    Sort::Int => ctx.kernel.const_(ctx.int.z, Vec::new()),
                    Sort::Bool => cover_bool_carrier(ctx),
                    _ => unreachable!(),
                };
                let anon = ctx.kernel.anon();
                Ok(ctx.kernel.pi(anon, carrier, body, BinderInfo::Default))
            }
            (Op::Exists(_), _) => Err(cover_decline("existential in cover proof")),
            _ => Err(cover_decline(format!(
                "unsupported Boolean operator {op:?}"
            ))),
        },
        _ => Err(cover_decline("expected a Boolean formula")),
    }
}

fn cover_formula_truth(arena: &TermArena, term: TermId, values: &Assignment) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            values.get(*symbol)?.as_bool()
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => Some(!cover_formula_truth(arena, *argument, values)?),
            (Op::BoolAnd, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            }
            (Op::BoolOr, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                }
            }
            (Op::BoolImplies, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }
            (Op::BoolXor, [left, right]) => Some(
                cover_formula_truth(arena, *left, values)?
                    != cover_formula_truth(arena, *right, values)?,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => Some(
                cover_formula_truth(arena, *left, values)?
                    == cover_formula_truth(arena, *right, values)?,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    == eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntLt, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    < eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntLe, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    <= eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntGt, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    > eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntGe, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    >= eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                if cover_formula_truth(arena, *condition, values)? {
                    cover_formula_truth(arena, *then_term, values)
                } else {
                    cover_formula_truth(arena, *else_term, values)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn cover_not_lambda(
    ctx: &mut IntReconstructCtx,
    proposition: ExprId,
    hypothesis_id: u64,
    false_proof: ExprId,
) -> ExprId {
    let body = ctx.kernel.abstract_fvars(false_proof, &[hypothesis_id]);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, proposition, body, BinderInfo::Default)
}

fn cover_int_value_proof(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: &Assignment,
) -> Result<(ExprId, i128, ExprId), ReconstructError> {
    if !ground_int_term_fits_proof_unit_budget(arena, term, values) {
        return Err(cover_decline(
            "ground integer normalization exceeds proof-size cap",
        ));
    }
    let expression = cover_int_term(ctx, arena, term, int_env, bool_env, Some(values))?;
    let value = eval(arena, term, values)
        .ok()
        .and_then(|value| value.as_int())
        .ok_or_else(|| cover_decline("ground integer term did not evaluate"))?;
    let (gens, _, normalized) = ctx
        .normalize_kernel(expression)
        .ok_or_else(|| cover_decline("ground integer normalization declined"))?;
    if gens != lin_to_canon_gens(&[], value) {
        return Err(cover_decline("integer normalizer disagrees with evaluator"));
    }
    let canonical = ctx.gens_to_expr(&gens);
    let literal = ctx.mk_intlit(value);
    let literal_to_canonical = ctx.intlit_eq_canon(value);
    let canonical_to_literal = ctx.eq_symm(literal, canonical, literal_to_canonical);
    let proof = ctx.eq_trans(
        expression,
        canonical,
        literal,
        normalized,
        canonical_to_literal,
    );
    Ok((expression, value, proof))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn cover_signed_int_atom(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    op: Op,
    left: TermId,
    right: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: &Assignment,
) -> Result<CoverSignedProof, ReconstructError> {
    let (left_expr, left_value, left_to_literal) =
        cover_int_value_proof(ctx, arena, left, int_env, bool_env, values)?;
    let (right_expr, right_value, right_to_literal) =
        cover_int_value_proof(ctx, arena, right, int_env, bool_env, values)?;
    let (left_expr, left_value, left_to_literal, right_expr, right_value, right_to_literal, op) =
        match op {
            Op::IntGt => (
                right_expr,
                right_value,
                right_to_literal,
                left_expr,
                left_value,
                left_to_literal,
                Op::IntLt,
            ),
            Op::IntGe => (
                right_expr,
                right_value,
                right_to_literal,
                left_expr,
                left_value,
                left_to_literal,
                Op::IntLe,
            ),
            op => (
                left_expr,
                left_value,
                left_to_literal,
                right_expr,
                right_value,
                right_to_literal,
                op,
            ),
        };
    let left_literal = ctx.mk_intlit(left_value);
    let right_literal = ctx.mk_intlit(right_value);
    let literal_to_left = ctx.eq_symm(left_expr, left_literal, left_to_literal);
    let literal_to_right = ctx.eq_symm(right_expr, right_literal, right_to_literal);

    match op {
        Op::Eq => {
            let proposition = ctx.mk_eq(left_expr, right_expr);
            if left_value == right_value {
                let literal_refl = ctx.eq_refl(left_literal);
                let literal_to_right_expr = ctx.eq_trans(
                    left_literal,
                    right_literal,
                    right_expr,
                    literal_refl,
                    literal_to_right,
                );
                let proof = ctx.eq_trans(
                    left_expr,
                    left_literal,
                    right_expr,
                    left_to_literal,
                    literal_to_right_expr,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let not_literal = ctx.prove_intlit_disequality(left_value, right_value)?;
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let literal_to_right_expr = ctx.eq_trans(
                    left_literal,
                    left_expr,
                    right_expr,
                    literal_to_left,
                    hypothesis,
                );
                let literal_equality = ctx.eq_trans(
                    left_literal,
                    right_expr,
                    right_literal,
                    literal_to_right_expr,
                    right_to_literal,
                );
                let false_proof = ctx.kernel.app(not_literal, literal_equality);
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        Op::IntLt => {
            let proposition = ctx.mk_lt(left_expr, right_expr);
            if left_value < right_value {
                let literal_lt = ctx.lt_lit_lit(left_value, right_value)?;
                let cast_left = ctx.lt_cast_left(
                    left_literal,
                    left_expr,
                    right_literal,
                    literal_lt,
                    literal_to_left,
                );
                let proof = ctx.lt_cast_right(
                    left_expr,
                    right_literal,
                    right_expr,
                    cast_left,
                    literal_to_right,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let cast_left = ctx.lt_cast_left(
                    left_expr,
                    left_literal,
                    right_expr,
                    hypothesis,
                    left_to_literal,
                );
                let literal_left_right = ctx.lt_cast_right(
                    left_literal,
                    right_expr,
                    right_literal,
                    cast_left,
                    right_to_literal,
                );
                let false_proof = if left_value == right_value {
                    let irrefl = ctx.lt_irrefl_app(left_literal);
                    ctx.kernel.app(irrefl, literal_left_right)
                } else {
                    let reverse = ctx.lt_lit_lit(right_value, left_value)?;
                    let cycle = ctx.lt_trans_app(
                        right_literal,
                        left_literal,
                        right_literal,
                        reverse,
                        literal_left_right,
                    );
                    let irrefl = ctx.lt_irrefl_app(right_literal);
                    ctx.kernel.app(irrefl, cycle)
                };
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        Op::IntLe => {
            let proposition = ctx.mk_le(left_expr, right_expr);
            if left_value <= right_value {
                let literal_le = if left_value == right_value {
                    ctx.le_refl_app(left_literal)
                } else {
                    let literal_lt = ctx.lt_lit_lit(left_value, right_value)?;
                    ctx.le_of_lt_app(left_literal, right_literal, literal_lt)
                };
                let cast_left = ctx.le_cast_left(
                    left_literal,
                    left_expr,
                    right_literal,
                    literal_le,
                    literal_to_left,
                );
                let proof = ctx.le_cast_right(
                    left_expr,
                    right_literal,
                    right_expr,
                    cast_left,
                    literal_to_right,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let cast_left = ctx.le_cast_left(
                    left_expr,
                    left_literal,
                    right_expr,
                    hypothesis,
                    left_to_literal,
                );
                let literal_le = ctx.le_cast_right(
                    left_literal,
                    right_expr,
                    right_literal,
                    cast_left,
                    right_to_literal,
                );
                let reverse = ctx.lt_lit_lit(right_value, left_value)?;
                let cycle = ctx.lt_of_lt_of_le_app(
                    right_literal,
                    left_literal,
                    right_literal,
                    reverse,
                    literal_le,
                );
                let irrefl = ctx.lt_irrefl_app(right_literal);
                let false_proof = ctx.kernel.app(irrefl, cycle);
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        _ => Err(cover_decline("unsupported integer atom")),
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn cover_signed_formula(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<CoverSignedProof, ReconstructError> {
    let truth = cover_formula_truth(arena, term, values)
        .ok_or_else(|| cover_decline("formula is not decided by the current cover branch"))?;
    match arena.node(term) {
        TermNode::BoolConst(value) => {
            let expression = cover_bool_literal(ctx, *value);
            let proof = if *value {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(CoverSignedProof { truth, proof })
        }
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            if let Some(proof) = facts.get(symbol) {
                if proof.truth != truth {
                    return Err(cover_decline("free Bool fact disagrees with assignment"));
                }
                return Ok(*proof);
            }
            let expression = bool_env
                .get(symbol)
                .copied()
                .ok_or_else(|| cover_decline("decided Bool atom has no proof fact"))?;
            let proof = if truth {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(CoverSignedProof { truth, proof })
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => {
                let child = cover_signed_formula(
                    ctx, arena, *argument, int_env, bool_env, free_props, values, facts,
                )?;
                if truth {
                    Ok(CoverSignedProof {
                        truth,
                        proof: child.proof,
                    })
                } else {
                    let child_prop = cover_formula_prop(
                        ctx,
                        arena,
                        *argument,
                        int_env,
                        bool_env,
                        free_props,
                        Some(values),
                    )?;
                    let not_child = ctx.mk_not(child_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let false_proof = ctx.kernel.app(hypothesis, child.proof);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, not_child, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolAnd, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                if truth {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    Ok(CoverSignedProof {
                        truth,
                        proof: ctx.and_intro(left_prop, right_prop, left.proof, right.proof),
                    })
                } else {
                    let (selected, select_left) = if left_truth == Some(false) {
                        (*left, true)
                    } else if right_truth == Some(false) {
                        (*right, false)
                    } else {
                        return Err(cover_decline("false conjunction lacks a false child"));
                    };
                    let child = cover_signed_formula(
                        ctx, arena, selected, int_env, bool_env, free_props, values, facts,
                    )?;
                    let conjunction = ctx.mk_and(left_prop, right_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let projected = ctx.and_project(left_prop, right_prop, hypothesis, select_left);
                    let false_proof = ctx.kernel.app(child.proof, projected);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, conjunction, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolOr, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                if truth {
                    if left_truth == Some(true) {
                        let left = cover_signed_formula(
                            ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                        )?;
                        Ok(CoverSignedProof {
                            truth,
                            proof: ctx.or_intro_left(left_prop, right_prop, left.proof),
                        })
                    } else if right_truth == Some(true) {
                        let right = cover_signed_formula(
                            ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                        )?;
                        Ok(CoverSignedProof {
                            truth,
                            proof: ctx.or_intro_right(left_prop, right_prop, right.proof),
                        })
                    } else {
                        Err(cover_decline("true disjunction lacks a true child"))
                    }
                } else {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    let disjunction = ctx.mk_or(left_prop, right_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let left_id = ctx.fresh_fvar();
                    let left_hypothesis = ctx.kernel.fvar(left_id);
                    let left_false = ctx.kernel.app(left.proof, left_hypothesis);
                    let left_case = cover_not_lambda(ctx, left_prop, left_id, left_false);
                    let right_id = ctx.fresh_fvar();
                    let right_hypothesis = ctx.kernel.fvar(right_id);
                    let right_false = ctx.kernel.app(right.proof, right_hypothesis);
                    let right_case = cover_not_lambda(ctx, right_prop, right_id, right_false);
                    let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
                    let false_proof = ctx.or_rec_prop(
                        left_prop, right_prop, false_prop, left_case, right_case, hypothesis,
                    );
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, disjunction, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolImplies, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let anon = ctx.kernel.anon();
                let implication = ctx
                    .kernel
                    .pi(anon, left_prop, right_prop, BinderInfo::Default);
                if truth {
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let result = if right_truth == Some(true) {
                        cover_signed_formula(
                            ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                        )?
                        .proof
                    } else if left_truth == Some(false) {
                        let left = cover_signed_formula(
                            ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                        )?;
                        let false_proof = ctx.kernel.app(left.proof, hypothesis);
                        ctx.ex_falso(right_prop, false_proof)
                    } else {
                        return Err(cover_decline("true implication is not decided"));
                    };
                    let body = ctx.kernel.abstract_fvars(result, &[hypothesis_id]);
                    Ok(CoverSignedProof {
                        truth,
                        proof: ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default),
                    })
                } else {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let result = ctx.kernel.app(hypothesis, left.proof);
                    let false_proof = ctx.kernel.app(right.proof, result);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, implication, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => cover_signed_iff(
                ctx, arena, *left, *right, false, int_env, bool_env, free_props, values, facts,
            ),
            (Op::BoolXor, [left, right]) => cover_signed_iff(
                ctx, arena, *left, *right, true, int_env, bool_env, free_props, values, facts,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                cover_signed_int_atom(ctx, arena, Op::Eq, *left, *right, int_env, bool_env, values)
            }
            (Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe, [left, right]) => {
                cover_signed_int_atom(ctx, arena, *op, *left, *right, int_env, bool_env, values)
            }
            (Op::Ite, _) if arena.sort_of(term) == Sort::Bool => Err(cover_decline(
                "Boolean ite proof is outside the first cover slice",
            )),
            _ => Err(cover_decline(format!(
                "unsupported signed Boolean operator {op:?}"
            ))),
        },
        _ => Err(cover_decline("expected a decided Boolean formula")),
    }
}

#[allow(clippy::too_many_arguments)]
fn cover_signed_iff(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    left: TermId,
    right: TermId,
    negate: bool,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<CoverSignedProof, ReconstructError> {
    let left_proof = cover_signed_formula(
        ctx, arena, left, int_env, bool_env, free_props, values, facts,
    )?;
    let right_proof = cover_signed_formula(
        ctx, arena, right, int_env, bool_env, free_props, values, facts,
    )?;
    let left_prop = cover_formula_prop(
        ctx,
        arena,
        left,
        int_env,
        bool_env,
        free_props,
        Some(values),
    )?;
    let right_prop = cover_formula_prop(
        ctx,
        arena,
        right,
        int_env,
        bool_env,
        free_props,
        Some(values),
    )?;
    let iff_truth = left_proof.truth == right_proof.truth;
    let iff_prop = ctx.mk_iff(left_prop, right_prop);
    let iff_proof = if iff_truth {
        let anon = ctx.kernel.anon();
        let forward = if left_proof.truth {
            ctx.const_implication(left_prop, right_prop, right_proof.proof)
        } else {
            let id = ctx.fresh_fvar();
            let hypothesis = ctx.kernel.fvar(id);
            let false_proof = ctx.kernel.app(left_proof.proof, hypothesis);
            let result = ctx.ex_falso(right_prop, false_proof);
            let body = ctx.kernel.abstract_fvars(result, &[id]);
            ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default)
        };
        let backward = if right_proof.truth {
            ctx.const_implication(right_prop, left_prop, left_proof.proof)
        } else {
            let id = ctx.fresh_fvar();
            let hypothesis = ctx.kernel.fvar(id);
            let false_proof = ctx.kernel.app(right_proof.proof, hypothesis);
            let result = ctx.ex_falso(left_prop, false_proof);
            let body = ctx.kernel.abstract_fvars(result, &[id]);
            ctx.kernel.lam(anon, right_prop, body, BinderInfo::Default)
        };
        ctx.iff_intro(left_prop, right_prop, forward, backward)
    } else {
        let hypothesis_id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(hypothesis_id);
        let false_proof = if left_proof.truth {
            let forward = ctx.iff_project(left_prop, right_prop, hypothesis, true);
            let right = ctx.kernel.app(forward, left_proof.proof);
            ctx.kernel.app(right_proof.proof, right)
        } else {
            let backward = ctx.iff_project(left_prop, right_prop, hypothesis, false);
            let left = ctx.kernel.app(backward, right_proof.proof);
            ctx.kernel.app(left_proof.proof, left)
        };
        cover_not_lambda(ctx, iff_prop, hypothesis_id, false_proof)
    };
    if !negate {
        Ok(CoverSignedProof {
            truth: iff_truth,
            proof: iff_proof,
        })
    } else if !iff_truth {
        Ok(CoverSignedProof {
            truth: true,
            proof: iff_proof,
        })
    } else {
        let not_iff = ctx.mk_not(iff_prop);
        let id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(id);
        let false_proof = ctx.kernel.app(hypothesis, iff_proof);
        Ok(CoverSignedProof {
            truth: false,
            proof: cover_not_lambda(ctx, not_iff, id, false_proof),
        })
    }
}

const COVER_LEAN_NODE_CAP: usize = 100_000;

fn cover_contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn cover_flatten_conjunction(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        cover_flatten_conjunction(arena, *left, out);
        cover_flatten_conjunction(arena, *right, out);
    } else {
        out.push(term);
    }
}

fn cover_forall_chain(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(symbol),
        args,
    } = arena.node(term)
    {
        let [body] = &**args else {
            return None;
        };
        if !matches!(arena.symbol(*symbol).1, Sort::Bool | Sort::Int) {
            return None;
        }
        binders.push(*symbol);
        term = *body;
    }
    (!binders.is_empty() && !cover_contains_quantifier(arena, term)).then_some((binders, term))
}

fn cover_lean_parts(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Vec<TermId>, usize, Vec<SymbolId>, TermId)> {
    let mut leaves = Vec::new();
    for &assertion in assertions {
        cover_flatten_conjunction(arena, assertion, &mut leaves);
    }
    let quantified = leaves
        .iter()
        .enumerate()
        .filter_map(|(index, term)| cover_contains_quantifier(arena, *term).then_some(index))
        .collect::<Vec<_>>();
    let [index] = &*quantified else {
        return None;
    };
    let index = *index;
    let (binders, body) = cover_forall_chain(arena, leaves[index])?;
    Some((leaves, index, binders, body))
}

/// Cheap router predicate for ADR-0108's first kernel reconstruction slice.
pub(crate) fn quantified_counterexample_cover_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    cover_lean_parts(arena, assertions).is_some()
        && admitted_free_booleans(arena, assertions).is_some_and(|free| !free.is_empty())
}

fn cover_declare_free_props(
    ctx: &mut IntReconstructCtx,
    symbols: &[SymbolId],
) -> Result<CoverFreeProps, ReconstructError> {
    let mut props = CoverFreeProps::new();
    for &symbol in symbols {
        let name = ctx.fresh_name("bool_atom");
        let prop = ctx.kernel.sort_zero();
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: Vec::new(),
                ty: prop,
            })
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "quantified_counterexample_cover".to_owned(),
                detail: format!("free proposition declaration failed: {error:?}"),
            })?;
        props.insert(symbol, ctx.kernel.const_(name, Vec::new()));
    }
    Ok(props)
}

fn cover_case_matches(case: &QuantifiedCounterexampleCoverCase, values: &Assignment) -> bool {
    case.cube.iter().all(|&(symbol, value)| {
        values.get(symbol).and_then(|assigned| assigned.as_bool()) == Some(value)
    })
}

fn cover_case_compatible(case: &QuantifiedCounterexampleCoverCase, values: &Assignment) -> bool {
    case.cube.iter().all(|&(symbol, value)| {
        values
            .get(symbol)
            .and_then(|assigned| assigned.as_bool())
            .is_none_or(|assigned| assigned == value)
    })
}

fn cover_score_unassigned(
    arena: &TermArena,
    term: TermId,
    values: &Assignment,
    scores: &mut BTreeMap<SymbolId, usize>,
) {
    if cover_formula_truth(arena, term, values).is_some() {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(symbol)
            if arena.symbol(*symbol).1 == Sort::Bool && values.get(*symbol).is_none() =>
        {
            *scores.entry(*symbol).or_default() += 4;
        }
        TermNode::App { args, .. } => {
            for &argument in args {
                cover_score_unassigned(arena, argument, values, scores);
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn cover_case_contradiction(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    case: &QuantifiedCounterexampleCoverCase,
    binders: &[SymbolId],
    body: TermId,
    universal_hypothesis: ExprId,
    free_props: &CoverFreeProps,
    branch_values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<ExprId, ReconstructError> {
    if case.bindings.len() != binders.len()
        || case
            .bindings
            .iter()
            .zip(binders)
            .any(|((symbol, _), expected)| symbol != expected)
    {
        return Err(cover_decline("case bindings do not match universal chain"));
    }
    let mut values = branch_values.clone();
    let mut int_env = CoverKernelEnv::new();
    let mut bool_env = CoverKernelEnv::new();
    let mut instance = universal_hypothesis;
    for &(symbol, ref value) in &case.bindings {
        values.set(symbol, value.clone());
        let witness = match value {
            Value::Int(value) => {
                if !int_values_fit_proof_unit_budget([*value]) {
                    return Err(cover_decline("integer witness exceeds proof-size cap"));
                }
                let witness = ctx.mk_intlit(*value);
                int_env.insert(symbol, witness);
                witness
            }
            Value::Bool(value) => {
                let witness = cover_bool_literal(ctx, *value);
                bool_env.insert(symbol, witness);
                witness
            }
            _ => return Err(cover_decline("non-Bool/Int case binding")),
        };
        instance = ctx.kernel.app(instance, witness);
    }
    let signed = cover_signed_formula(
        ctx,
        arena,
        body,
        &mut int_env,
        &mut bool_env,
        free_props,
        &values,
        facts,
    )?;
    if signed.truth {
        return Err(cover_decline(
            "matched case does not falsify universal body",
        ));
    }
    Ok(ctx.kernel.app(signed.proof, instance))
}

struct CoverTree<'a> {
    arena: &'a TermArena,
    ground_leaves: &'a [(TermId, ExprId)],
    universal_hypothesis: ExprId,
    binders: &'a [SymbolId],
    body: TermId,
    cases: &'a [QuantifiedCounterexampleCoverCase],
    free_symbols: &'a [SymbolId],
    free_props: &'a CoverFreeProps,
    nodes: usize,
}

impl CoverTree<'_> {
    #[allow(clippy::too_many_lines)]
    fn contradiction(
        &mut self,
        ctx: &mut IntReconstructCtx,
        values: &Assignment,
        facts: &BTreeMap<SymbolId, CoverSignedProof>,
    ) -> Result<ExprId, ReconstructError> {
        self.nodes += 1;
        if self.nodes > COVER_LEAN_NODE_CAP {
            return Err(cover_decline(
                "excluded-middle proof tree exceeded node cap",
            ));
        }

        for &(term, hypothesis) in self.ground_leaves {
            if cover_formula_truth(self.arena, term, values) == Some(false) {
                let signed = cover_signed_formula(
                    ctx,
                    self.arena,
                    term,
                    &mut CoverKernelEnv::new(),
                    &mut CoverKernelEnv::new(),
                    self.free_props,
                    values,
                    facts,
                )?;
                return Ok(ctx.kernel.app(signed.proof, hypothesis));
            }
        }

        if let Some(case) = self
            .cases
            .iter()
            .find(|case| cover_case_matches(case, values))
        {
            return cover_case_contradiction(
                ctx,
                self.arena,
                case,
                self.binders,
                self.body,
                self.universal_hypothesis,
                self.free_props,
                values,
                facts,
            );
        }

        let mut scores = BTreeMap::<SymbolId, usize>::new();
        for &(term, _) in self.ground_leaves {
            cover_score_unassigned(self.arena, term, values, &mut scores);
        }
        for case in self
            .cases
            .iter()
            .filter(|case| cover_case_compatible(case, values))
        {
            for &(symbol, _) in &case.cube {
                if values.get(symbol).is_none() {
                    *scores.entry(symbol).or_default() += 1;
                }
            }
        }
        let symbol = scores
            .into_iter()
            .max_by_key(|(symbol, score)| (*score, std::cmp::Reverse(*symbol)))
            .map(|(symbol, _)| symbol)
            .or_else(|| {
                self.free_symbols
                    .iter()
                    .copied()
                    .find(|symbol| values.get(*symbol).is_none())
            })
            .ok_or_else(|| cover_decline("complete Boolean branch is not covered"))?;
        let proposition = *self
            .free_props
            .get(&symbol)
            .ok_or_else(|| cover_decline("branch symbol has no proposition"))?;

        let true_id = ctx.fresh_fvar();
        let true_hypothesis = ctx.kernel.fvar(true_id);
        let mut true_values = values.clone();
        true_values.set(symbol, Value::Bool(true));
        let mut true_facts = facts.clone();
        true_facts.insert(
            symbol,
            CoverSignedProof {
                truth: true,
                proof: true_hypothesis,
            },
        );
        let true_false = self.contradiction(ctx, &true_values, &true_facts)?;
        let true_body = ctx.kernel.abstract_fvars(true_false, &[true_id]);
        let anon = ctx.kernel.anon();
        let true_case = ctx
            .kernel
            .lam(anon, proposition, true_body, BinderInfo::Default);

        let not_proposition = ctx.mk_not(proposition);
        let false_id = ctx.fresh_fvar();
        let false_hypothesis = ctx.kernel.fvar(false_id);
        let mut false_values = values.clone();
        false_values.set(symbol, Value::Bool(false));
        let mut false_facts = facts.clone();
        false_facts.insert(
            symbol,
            CoverSignedProof {
                truth: false,
                proof: false_hypothesis,
            },
        );
        let false_false = self.contradiction(ctx, &false_values, &false_facts)?;
        let false_body = ctx.kernel.abstract_fvars(false_false, &[false_id]);
        let false_case = ctx
            .kernel
            .lam(anon, not_proposition, false_body, BinderInfo::Default);

        let excluded_middle = ctx.classical_em(proposition)?;
        let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
        Ok(ctx.or_rec_prop(
            proposition,
            not_proposition,
            false_prop,
            true_case,
            false_case,
            excluded_middle,
        ))
    }
}

/// Reconstruct an ADR-0108 checked counterexample cover as a kernel-checked
/// contradiction over the original ground conjuncts and genuine universal.
///
/// The first slice admits exactly one positive top-level universal conjunct.
/// Each retained cube is used only to choose a concrete source instantiation;
/// a bounded excluded-middle tree proves that every free-Boolean branch either
/// violates an original ground conjunct or one instantiated universal body.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] when the certificate or formula
/// is outside the bounded slice, and [`ReconstructError::KernelRejected`] when
/// the assembled closed proof does not infer to `False`.
pub fn reconstruct_quantified_counterexample_cover_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &QuantifiedCounterexampleCoverCertificate,
) -> Result<String, ReconstructError> {
    if !check_quantified_counterexample_cover(arena, assertions, certificate) {
        return Err(cover_decline("invalid ADR-0108 certificate"));
    }
    let (leaves, universal_index, binders, body) = cover_lean_parts(arena, assertions)
        .ok_or_else(|| cover_decline("unsupported source shape"))?;
    let universal = leaves[universal_index];
    if certificate.cases.iter().any(|case| {
        let mut source_leaves = Vec::new();
        cover_flatten_conjunction(arena, case.assertion, &mut source_leaves);
        !source_leaves.contains(&universal)
    }) {
        return Err(cover_decline(
            "case source does not contain admitted universal",
        ));
    }
    let binding_values = certificate.cases.iter().flat_map(|case| {
        case.bindings.iter().filter_map(|(_, value)| match value {
            Value::Int(value) => Some(*value),
            _ => None,
        })
    });
    if !source_int_literals_fit_proof_unit_budget(arena, assertions.iter().copied())
        || !int_values_fit_proof_unit_budget(binding_values)
    {
        return Err(cover_decline(
            "integer literals or witnesses exceed proof-size cap",
        ));
    }
    let free_symbols = admitted_free_booleans(arena, assertions)
        .ok_or_else(|| cover_decline("source has inadmissible free symbols"))?;
    let mut ctx = IntReconstructCtx::new();
    let free_props = cover_declare_free_props(&mut ctx, &free_symbols)?;

    let mut hypotheses = Vec::with_capacity(leaves.len());
    for &leaf in &leaves {
        let proposition = cover_formula_prop(
            &mut ctx,
            arena,
            leaf,
            &mut CoverKernelEnv::new(),
            &mut CoverKernelEnv::new(),
            &free_props,
            None,
        )?;
        hypotheses.push(ctx.hyp_axiom(proposition)?);
    }
    let universal_hypothesis = hypotheses[universal_index];
    let ground_leaves = leaves
        .iter()
        .copied()
        .zip(hypotheses.iter().copied())
        .enumerate()
        .filter_map(|(index, pair)| (index != universal_index).then_some(pair))
        .collect::<Vec<_>>();
    let mut tree = CoverTree {
        arena,
        ground_leaves: &ground_leaves,
        universal_hypothesis,
        binders: &binders,
        body,
        cases: &certificate.cases,
        free_symbols: &free_symbols,
        free_props: &free_props,
        nodes: 0,
    };
    let proof = tree.contradiction(&mut ctx, &Assignment::new(), &BTreeMap::new())?;
    let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
    ctx.require_partition_type(proof, false_prop, "counterexample-cover contradiction")?;
    let bool_inductive = ctx.int.logic.bool_;
    Ok(ctx.kernel().render_lean_module_compact_with_inductives(
        "axeyum_refutation",
        false_prop,
        proof,
        &[bool_inductive],
    ))
}
