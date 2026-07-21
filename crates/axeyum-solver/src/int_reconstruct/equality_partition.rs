use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_lean_kernel::{BinderInfo, ExprId};

use crate::quant_eq_partition_cert::{
    EqualityPartitionRefutationCertificate, check_equality_partition_refutation,
};
use crate::reconstruct::ReconstructError;

use super::{IntReconstructCtx, int_values_fit_proof_unit_budget};

#[derive(Debug, Clone, PartialEq, Eq)]
enum PartitionFormula {
    True,
    False,
    BoolAtom(SymbolId),
    IntAtom(SymbolId, i128),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Implies(Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),
    Forall(SymbolId, Sort, Box<Self>),
    Exists(SymbolId, Sort, Box<Self>),
}

#[derive(Debug, Clone)]
enum PartitionInt {
    Literal(i128),
    Ite(Box<PartitionFormula>, Box<Self>, Box<Self>),
}

fn partition_ite(
    condition: PartitionFormula,
    then_formula: PartitionFormula,
    else_formula: PartitionFormula,
) -> PartitionFormula {
    PartitionFormula::Or(
        Box::new(PartitionFormula::And(
            Box::new(condition.clone()),
            Box::new(then_formula),
        )),
        Box::new(PartitionFormula::And(
            Box::new(PartitionFormula::Not(Box::new(condition))),
            Box::new(else_formula),
        )),
    )
}

fn lower_single_pivot_partition(
    arena: &TermArena,
    assertion: TermId,
) -> Result<PartitionFormula, ReconstructError> {
    let mut bound = BTreeMap::new();
    let formula = lower_partition_bool(arena, assertion, &mut bound)?;
    let mut symbols = BTreeSet::new();
    collect_partition_binders(&formula, &mut symbols);
    for symbol in symbols {
        let mut constants = BTreeSet::new();
        collect_partition_constants(&formula, symbol, &mut constants);
        if constants.len() > 1 {
            return Err(eq_partition_decline(
                "an Int binder is compared with multiple distinct literals",
            ));
        }
    }
    Ok(formula)
}

fn lower_partition_bool(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionFormula, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(true) => Ok(PartitionFormula::True),
        TermNode::BoolConst(false) => Ok(PartitionFormula::False),
        TermNode::Symbol(symbol)
            if bound.get(symbol) == Some(&Sort::Bool) && arena.sort_of(term) == Sort::Bool =>
        {
            Ok(PartitionFormula::BoolAtom(*symbol))
        }
        TermNode::App {
            op: Op::Forall(symbol) | Op::Exists(symbol),
            args,
        } => {
            let [body] = &**args else {
                return Err(eq_partition_decline("quantifier is not unary"));
            };
            let sort = arena.symbol(*symbol).1;
            if !matches!(sort, Sort::Bool | Sort::Int) || bound.insert(*symbol, sort).is_some() {
                return Err(eq_partition_decline(
                    "quantifier binder is unsupported or duplicated",
                ));
            }
            let body = lower_partition_bool(arena, *body, bound)?;
            bound.remove(symbol);
            if matches!(
                arena.node(term),
                TermNode::App {
                    op: Op::Forall(_),
                    ..
                }
            ) {
                Ok(PartitionFormula::Forall(*symbol, sort, Box::new(body)))
            } else {
                Ok(PartitionFormula::Exists(*symbol, sort, Box::new(body)))
            }
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [arg]) => Ok(PartitionFormula::Not(Box::new(lower_partition_bool(
                arena, *arg, bound,
            )?))),
            (Op::BoolAnd, [left, right]) => Ok(PartitionFormula::And(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolOr, [left, right]) => Ok(PartitionFormula::Or(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolImplies, [left, right]) => Ok(PartitionFormula::Implies(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolXor, [left, right]) => {
                Ok(PartitionFormula::Not(Box::new(PartitionFormula::Iff(
                    Box::new(lower_partition_bool(arena, *left, bound)?),
                    Box::new(lower_partition_bool(arena, *right, bound)?),
                ))))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => {
                Ok(PartitionFormula::Iff(
                    Box::new(lower_partition_bool(arena, *left, bound)?),
                    Box::new(lower_partition_bool(arena, *right, bound)?),
                ))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                lower_partition_int_equality(arena, *left, *right, bound)
            }
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                Ok(partition_ite(
                    lower_partition_bool(arena, *condition, bound)?,
                    lower_partition_bool(arena, *then_term, bound)?,
                    lower_partition_bool(arena, *else_term, bound)?,
                ))
            }
            _ => match eval(arena, term, &Assignment::new()) {
                Ok(Value::Bool(value)) => Ok(if value {
                    PartitionFormula::True
                } else {
                    PartitionFormula::False
                }),
                _ => Err(eq_partition_decline(
                    "Boolean term exceeds the proof-producing partition slice",
                )),
            },
        },
        _ => Err(eq_partition_decline("expected a Boolean partition term")),
    }
}

fn lower_partition_int_equality(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionFormula, ReconstructError> {
    if let TermNode::Symbol(symbol) = arena.node(left)
        && bound.get(symbol) == Some(&Sort::Int)
        && let Some(value) = partition_int_literal(arena, right)
    {
        return Ok(PartitionFormula::IntAtom(*symbol, value));
    }
    if let TermNode::Symbol(symbol) = arena.node(right)
        && bound.get(symbol) == Some(&Sort::Int)
        && let Some(value) = partition_int_literal(arena, left)
    {
        return Ok(PartitionFormula::IntAtom(*symbol, value));
    }
    let left = lower_partition_int(arena, left, bound)?;
    let right = lower_partition_int(arena, right, bound)?;
    Ok(partition_int_equality_formula(left, right))
}

fn lower_partition_int(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionInt, ReconstructError> {
    if let Some(value) = partition_int_literal(arena, term) {
        return Ok(PartitionInt::Literal(value));
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return Err(eq_partition_decline(
            "integer leaf is not a literal or guarded expression",
        ));
    };
    match (op, &**args) {
        (Op::Ite, [condition, then_term, else_term]) => Ok(PartitionInt::Ite(
            Box::new(lower_partition_bool(arena, *condition, bound)?),
            Box::new(lower_partition_int(arena, *then_term, bound)?),
            Box::new(lower_partition_int(arena, *else_term, bound)?),
        )),
        (Op::IntNeg, [arg]) => partition_int_map1(lower_partition_int(arena, *arg, bound)?, |x| {
            x.checked_neg()
        }),
        (Op::IntAdd, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_add,
        ),
        (Op::IntSub, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_sub,
        ),
        (Op::IntMul, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_mul,
        ),
        _ => Err(eq_partition_decline(
            "integer expression uses an unsupported partition operator",
        )),
    }
}

fn partition_int_map1(
    value: PartitionInt,
    operation: impl Copy + Fn(i128) -> Option<i128>,
) -> Result<PartitionInt, ReconstructError> {
    match value {
        PartitionInt::Literal(value) => operation(value)
            .map(PartitionInt::Literal)
            .ok_or_else(|| eq_partition_decline("integer leaf operation overflowed")),
        PartitionInt::Ite(condition, then_value, else_value) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map1(*then_value, operation)?),
            Box::new(partition_int_map1(*else_value, operation)?),
        )),
    }
}

fn partition_int_map2(
    left: PartitionInt,
    right: PartitionInt,
    operation: impl Copy + Fn(i128, i128) -> Option<i128>,
) -> Result<PartitionInt, ReconstructError> {
    match (left, right) {
        (PartitionInt::Literal(left), PartitionInt::Literal(right)) => operation(left, right)
            .map(PartitionInt::Literal)
            .ok_or_else(|| eq_partition_decline("integer leaf operation overflowed")),
        (PartitionInt::Ite(condition, then_value, else_value), right) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map2(*then_value, right.clone(), operation)?),
            Box::new(partition_int_map2(*else_value, right, operation)?),
        )),
        (left, PartitionInt::Ite(condition, then_value, else_value)) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map2(left.clone(), *then_value, operation)?),
            Box::new(partition_int_map2(left, *else_value, operation)?),
        )),
    }
}

fn partition_int_equality_formula(left: PartitionInt, right: PartitionInt) -> PartitionFormula {
    match (left, right) {
        (PartitionInt::Literal(left), PartitionInt::Literal(right)) => {
            if left == right {
                PartitionFormula::True
            } else {
                PartitionFormula::False
            }
        }
        (PartitionInt::Ite(condition, then_value, else_value), right) => partition_ite(
            *condition,
            partition_int_equality_formula(*then_value, right.clone()),
            partition_int_equality_formula(*else_value, right),
        ),
        (left, PartitionInt::Ite(condition, then_value, else_value)) => partition_ite(
            *condition,
            partition_int_equality_formula(left.clone(), *then_value),
            partition_int_equality_formula(left, *else_value),
        ),
    }
}

fn partition_int_literal(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } if args.len() == 1 => {
            let TermNode::IntConst(value) = arena.node(args[0]) else {
                return None;
            };
            value.checked_neg()
        }
        _ => None,
    }
}

fn collect_partition_binders(formula: &PartitionFormula, out: &mut BTreeSet<SymbolId>) {
    match formula {
        PartitionFormula::Forall(symbol, Sort::Int, body)
        | PartitionFormula::Exists(symbol, Sort::Int, body) => {
            out.insert(*symbol);
            collect_partition_binders(body, out);
        }
        PartitionFormula::Forall(_, _, body)
        | PartitionFormula::Exists(_, _, body)
        | PartitionFormula::Not(body) => collect_partition_binders(body, out),
        PartitionFormula::And(left, right)
        | PartitionFormula::Or(left, right)
        | PartitionFormula::Implies(left, right)
        | PartitionFormula::Iff(left, right) => {
            collect_partition_binders(left, out);
            collect_partition_binders(right, out);
        }
        _ => {}
    }
}

fn collect_partition_constants(
    formula: &PartitionFormula,
    symbol: SymbolId,
    out: &mut BTreeSet<i128>,
) {
    match formula {
        PartitionFormula::IntAtom(found, value) if *found == symbol => {
            out.insert(*value);
        }
        PartitionFormula::Forall(_, _, body)
        | PartitionFormula::Exists(_, _, body)
        | PartitionFormula::Not(body) => collect_partition_constants(body, symbol, out),
        PartitionFormula::And(left, right)
        | PartitionFormula::Or(left, right)
        | PartitionFormula::Implies(left, right)
        | PartitionFormula::Iff(left, right) => {
            collect_partition_constants(left, symbol, out);
            collect_partition_constants(right, symbol, out);
        }
        _ => {}
    }
}

fn partition_representatives(
    formula: &PartitionFormula,
    symbol: SymbolId,
    sort: Sort,
) -> Vec<Value> {
    match sort {
        Sort::Bool => vec![Value::Bool(false), Value::Bool(true)],
        Sort::Int => {
            let mut constants = BTreeSet::new();
            collect_partition_constants(formula, symbol, &mut constants);
            match constants.into_iter().next() {
                Some(value) => {
                    let other = value
                        .checked_add(1)
                        .or_else(|| value.checked_sub(1))
                        .unwrap();
                    vec![Value::Int(value), Value::Int(other)]
                }
                None => vec![Value::Int(0)],
            }
        }
        _ => Vec::new(),
    }
}

fn partition_formula_truth(formula: &PartitionFormula, assignment: &Assignment) -> Option<bool> {
    match formula {
        PartitionFormula::True => Some(true),
        PartitionFormula::False => Some(false),
        PartitionFormula::BoolAtom(symbol) => assignment.get(*symbol)?.as_bool(),
        PartitionFormula::IntAtom(symbol, value) => {
            Some(assignment.get(*symbol)?.as_int()? == *value)
        }
        PartitionFormula::Not(body) => Some(!partition_formula_truth(body, assignment)?),
        PartitionFormula::And(left, right) => Some(
            partition_formula_truth(left, assignment)?
                && partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Or(left, right) => Some(
            partition_formula_truth(left, assignment)?
                || partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Implies(left, right) => Some(
            !partition_formula_truth(left, assignment)?
                || partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Iff(left, right) => Some(
            partition_formula_truth(left, assignment)?
                == partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Forall(symbol, sort, body) => {
            for value in partition_representatives(body, *symbol, *sort) {
                let mut branch = assignment.clone();
                branch.set(*symbol, value);
                if !partition_formula_truth(body, &branch)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        PartitionFormula::Exists(symbol, sort, body) => {
            for value in partition_representatives(body, *symbol, *sort) {
                let mut branch = assignment.clone();
                branch.set(*symbol, value);
                if partition_formula_truth(body, &branch)? {
                    return Some(true);
                }
            }
            Some(false)
        }
    }
}

fn partition_literals_fit_proof_unit_budget(formula: &PartitionFormula) -> bool {
    fn collect(formula: &PartitionFormula, values: &mut Vec<i128>) {
        match formula {
            PartitionFormula::IntAtom(_, value) => {
                values.push(*value);
                values.push(
                    value
                        .checked_add(1)
                        .or_else(|| value.checked_sub(1))
                        .expect("every i128 has an adjacent representable value"),
                );
            }
            PartitionFormula::Forall(_, _, body)
            | PartitionFormula::Exists(_, _, body)
            | PartitionFormula::Not(body) => collect(body, values),
            PartitionFormula::And(left, right)
            | PartitionFormula::Or(left, right)
            | PartitionFormula::Implies(left, right)
            | PartitionFormula::Iff(left, right) => {
                collect(left, values);
                collect(right, values);
            }
            PartitionFormula::True | PartitionFormula::False | PartitionFormula::BoolAtom(_) => {}
        }
    }

    let mut values = Vec::new();
    collect(formula, &mut values);
    int_values_fit_proof_unit_budget(values)
}

#[derive(Debug, Clone, Copy)]
struct PartitionSignedProof {
    truth: bool,
    proof: ExprId,
}

type PartitionKernelEnv = BTreeMap<SymbolId, ExprId>;
type PartitionFactEnv = BTreeMap<(SymbolId, i128), PartitionSignedProof>;

fn partition_carrier(ctx: &mut IntReconstructCtx, sort: Sort) -> ExprId {
    match sort {
        Sort::Bool => ctx.kernel.const_(ctx.int.logic.bool_, Vec::new()),
        Sort::Int => ctx.kernel.const_(ctx.int.z, Vec::new()),
        _ => unreachable!("partition lowering admits only Bool/Int binders"),
    }
}

fn partition_value_expr(ctx: &mut IntReconstructCtx, value: &Value) -> ExprId {
    match value {
        Value::Bool(value) => {
            let name = if *value {
                ctx.int.logic.bool_true
            } else {
                ctx.int.logic.bool_false
            };
            ctx.kernel.const_(name, Vec::new())
        }
        Value::Int(value) => ctx.mk_intlit(*value),
        _ => unreachable!("partition representatives are Bool/Int"),
    }
}

fn partition_formula_prop(
    ctx: &mut IntReconstructCtx,
    formula: &PartitionFormula,
    environment: &mut PartitionKernelEnv,
) -> Result<ExprId, ReconstructError> {
    match formula {
        PartitionFormula::True => Ok(ctx.mk_true()),
        PartitionFormula::False => Ok(ctx.kernel.const_(ctx.int.logic.false_, Vec::new())),
        PartitionFormula::BoolAtom(symbol) => {
            let value = *environment
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("unbound Bool atom"))?;
            let true_value = ctx.kernel.const_(ctx.int.logic.bool_true, Vec::new());
            Ok(ctx.mk_bool_eq(value, true_value))
        }
        PartitionFormula::IntAtom(symbol, value) => {
            let variable = *environment
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("unbound Int atom"))?;
            let literal = ctx.mk_intlit(*value);
            Ok(ctx.mk_eq(variable, literal))
        }
        PartitionFormula::Not(body) => {
            let body = partition_formula_prop(ctx, body, environment)?;
            Ok(ctx.mk_not(body))
        }
        PartitionFormula::And(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_and(left, right))
        }
        PartitionFormula::Or(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_or(left, right))
        }
        PartitionFormula::Implies(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            let anon = ctx.kernel.anon();
            Ok(ctx.kernel.pi(anon, left, right, BinderInfo::Default))
        }
        PartitionFormula::Iff(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_iff(left, right))
        }
        PartitionFormula::Forall(symbol, sort, body) => {
            let id = ctx.fresh_fvar();
            let value = ctx.kernel.fvar(id);
            environment.insert(*symbol, value);
            let body = partition_formula_prop(ctx, body, environment)?;
            environment.remove(symbol);
            let body = ctx.kernel.abstract_fvars(body, &[id]);
            let carrier = partition_carrier(ctx, *sort);
            let anon = ctx.kernel.anon();
            Ok(ctx.kernel.pi(anon, carrier, body, BinderInfo::Default))
        }
        PartitionFormula::Exists(symbol, sort, body) => {
            let id = ctx.fresh_fvar();
            let value = ctx.kernel.fvar(id);
            environment.insert(*symbol, value);
            let body = partition_formula_prop(ctx, body, environment)?;
            environment.remove(symbol);
            let body = ctx.kernel.abstract_fvars(body, &[id]);
            let carrier = partition_carrier(ctx, *sort);
            let anon = ctx.kernel.anon();
            let predicate = ctx.kernel.lam(anon, carrier, body, BinderInfo::Default);
            Ok(ctx.mk_exists_for_carrier(carrier, predicate))
        }
    }
}

fn partition_not_lambda(
    ctx: &mut IntReconstructCtx,
    proposition: ExprId,
    hypothesis_id: u64,
    false_proof: ExprId,
) -> ExprId {
    let body = ctx.kernel.abstract_fvars(false_proof, &[hypothesis_id]);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, proposition, body, BinderInfo::Default)
}

#[allow(clippy::too_many_lines)]
fn prove_partition_formula(
    ctx: &mut IntReconstructCtx,
    formula: &PartitionFormula,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let truth = partition_formula_truth(formula, assignment)
        .ok_or_else(|| eq_partition_decline("proof search could not evaluate formula"))?;
    match formula {
        PartitionFormula::True => Ok(PartitionSignedProof {
            truth,
            proof: ctx.true_intro(),
        }),
        PartitionFormula::False => {
            let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
            let anon = ctx.kernel.anon();
            let hypothesis = ctx.kernel.bvar(0);
            let proof = ctx
                .kernel
                .lam(anon, false_prop, hypothesis, BinderInfo::Default);
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::BoolAtom(symbol) => {
            let value = assignment
                .get(*symbol)
                .and_then(|value| value.as_bool())
                .ok_or_else(|| eq_partition_decline("Bool atom lacks an assignment"))?;
            let expression = *kernel_env
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("Bool atom lacks a kernel binding"))?;
            let proof = if value {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::IntAtom(symbol, constant) => {
            if let Some(proof) = facts.get(&(*symbol, *constant)) {
                if proof.truth != truth {
                    return Err(eq_partition_decline(
                        "atom fact disagrees with representative",
                    ));
                }
                return Ok(*proof);
            }
            let value = assignment
                .get(*symbol)
                .and_then(|value| value.as_int())
                .ok_or_else(|| eq_partition_decline("Int atom lacks an assignment"))?;
            let expression = *kernel_env
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("Int atom lacks a kernel binding"))?;
            let proof = if truth {
                ctx.eq_refl(expression)
            } else {
                ctx.prove_adjacent_intlit_disequality(value, *constant)?
            };
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::Not(body) => {
            let body_proof = prove_partition_formula(ctx, body, assignment, kernel_env, facts)?;
            if truth {
                Ok(PartitionSignedProof {
                    truth,
                    proof: body_proof.proof,
                })
            } else {
                let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
                let not_body = ctx.mk_not(body_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let false_proof = ctx.kernel.app(hypothesis, body_proof.proof);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, not_body, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::And(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.and_intro(
                        left_prop,
                        right_prop,
                        left_proof.proof,
                        right_proof.proof,
                    ),
                })
            } else {
                let conjunction = ctx.mk_and(left_prop, right_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let (false_child, child_not) = if left_proof.truth {
                    (
                        ctx.and_project(left_prop, right_prop, hypothesis, false),
                        right_proof.proof,
                    )
                } else {
                    (
                        ctx.and_project(left_prop, right_prop, hypothesis, true),
                        left_proof.proof,
                    )
                };
                let false_proof = ctx.kernel.app(child_not, false_child);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, conjunction, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Or(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
                let proof = if left_proof.truth {
                    ctx.or_intro_left(left_prop, right_prop, left_proof.proof)
                } else {
                    ctx.or_intro_right(left_prop, right_prop, right_proof.proof)
                };
                Ok(PartitionSignedProof { truth, proof })
            } else {
                let disjunction = ctx.mk_or(left_prop, right_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let left_id = ctx.fresh_fvar();
                let left_hypothesis = ctx.kernel.fvar(left_id);
                let left_false = ctx.kernel.app(left_proof.proof, left_hypothesis);
                let left_case = partition_not_lambda(ctx, left_prop, left_id, left_false);
                let right_id = ctx.fresh_fvar();
                let right_hypothesis = ctx.kernel.fvar(right_id);
                let right_false = ctx.kernel.app(right_proof.proof, right_hypothesis);
                let right_case = partition_not_lambda(ctx, right_prop, right_id, right_false);
                let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
                let false_proof = ctx.or_rec_prop(
                    left_prop, right_prop, false_prop, left_case, right_case, hypothesis,
                );
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, disjunction, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Implies(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            let anon = ctx.kernel.anon();
            let implication = ctx
                .kernel
                .pi(anon, left_prop, right_prop, BinderInfo::Default);
            if truth {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let result = if left_proof.truth {
                    right_proof.proof
                } else {
                    let false_proof = ctx.kernel.app(left_proof.proof, hypothesis);
                    ctx.ex_falso(right_prop, false_proof)
                };
                let body = ctx.kernel.abstract_fvars(result, &[hypothesis_id]);
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default),
                })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let right = ctx.kernel.app(hypothesis, left_proof.proof);
                let false_proof = ctx.kernel.app(right_proof.proof, right);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, implication, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Iff(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
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
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.iff_intro(left_prop, right_prop, forward, backward),
                })
            } else {
                let iff_prop = ctx.mk_iff(left_prop, right_prop);
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
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, iff_prop, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Forall(symbol, sort, body) => prove_partition_forall(
            ctx, *symbol, *sort, body, truth, assignment, kernel_env, facts,
        ),
        PartitionFormula::Exists(symbol, sort, body) => prove_partition_exists(
            ctx, *symbol, *sort, body, truth, assignment, kernel_env, facts,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_partition_forall(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    truth: bool,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let carrier = partition_carrier(ctx, sort);
    let anon = ctx.kernel.anon();
    if truth {
        let witness_id = ctx.fresh_fvar();
        let witness = ctx.kernel.fvar(witness_id);
        kernel_env.insert(symbol, witness);
        let body_proof = prove_partition_for_arbitrary(
            ctx, symbol, sort, body, true, witness_id, witness, assignment, kernel_env, facts,
        )?;
        kernel_env.remove(&symbol);
        let proof_body = ctx.kernel.abstract_fvars(body_proof.proof, &[witness_id]);
        let proof = ctx
            .kernel
            .lam(anon, carrier, proof_body, BinderInfo::Default);
        Ok(PartitionSignedProof { truth, proof })
    } else {
        let representatives = partition_representatives(body, symbol, sort);
        let witness = representatives
            .into_iter()
            .find(|value| {
                let mut branch = assignment.clone();
                branch.set(symbol, value.clone());
                partition_formula_truth(body, &branch) == Some(false)
            })
            .ok_or_else(|| eq_partition_decline("false forall lacks a false representative"))?;
        let mut branch_assignment = assignment.clone();
        branch_assignment.set(symbol, witness.clone());
        let witness_expr = partition_value_expr(ctx, &witness);
        kernel_env.insert(symbol, witness_expr);
        let body_proof = prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
        kernel_env.remove(&symbol);
        if body_proof.truth {
            return Err(eq_partition_decline(
                "selected false-forall representative proved true",
            ));
        }
        let formula = PartitionFormula::Forall(symbol, sort, Box::new(body.clone()));
        let forall_prop = partition_formula_prop(ctx, &formula, kernel_env)?;
        let hypothesis_id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(hypothesis_id);
        let instance = ctx.kernel.app(hypothesis, witness_expr);
        let false_proof = ctx.kernel.app(body_proof.proof, instance);
        let proof = partition_not_lambda(ctx, forall_prop, hypothesis_id, false_proof);
        Ok(PartitionSignedProof { truth, proof })
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_partition_exists(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    truth: bool,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let carrier = partition_carrier(ctx, sort);
    let anon = ctx.kernel.anon();
    if truth {
        let representatives = partition_representatives(body, symbol, sort);
        let witness = representatives
            .into_iter()
            .find(|value| {
                let mut branch = assignment.clone();
                branch.set(symbol, value.clone());
                partition_formula_truth(body, &branch) == Some(true)
            })
            .ok_or_else(|| eq_partition_decline("true exists lacks a true representative"))?;
        let mut branch_assignment = assignment.clone();
        branch_assignment.set(symbol, witness.clone());
        let witness_expr = partition_value_expr(ctx, &witness);
        kernel_env.insert(symbol, witness_expr);
        let body_proof = prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
        kernel_env.remove(&symbol);
        if !body_proof.truth {
            return Err(eq_partition_decline(
                "selected true-exists representative proved false",
            ));
        }
        let predicate_id = ctx.fresh_fvar();
        let predicate_value = ctx.kernel.fvar(predicate_id);
        kernel_env.insert(symbol, predicate_value);
        let predicate_body = partition_formula_prop(ctx, body, kernel_env)?;
        kernel_env.remove(&symbol);
        let predicate_body = ctx.kernel.abstract_fvars(predicate_body, &[predicate_id]);
        let predicate = ctx
            .kernel
            .lam(anon, carrier, predicate_body, BinderInfo::Default);
        let proof = ctx.exists_intro(carrier, predicate, witness_expr, body_proof.proof);
        Ok(PartitionSignedProof { truth, proof })
    } else {
        let witness_id = ctx.fresh_fvar();
        let witness = ctx.kernel.fvar(witness_id);
        kernel_env.insert(symbol, witness);
        let body_proof = prove_partition_for_arbitrary(
            ctx, symbol, sort, body, false, witness_id, witness, assignment, kernel_env, facts,
        )?;
        let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
        let predicate_body = ctx.kernel.abstract_fvars(body_prop, &[witness_id]);
        let predicate = ctx
            .kernel
            .lam(anon, carrier, predicate_body, BinderInfo::Default);
        let exists_prop = ctx.mk_exists_for_carrier(carrier, predicate);
        let body_hypothesis_id = ctx.fresh_fvar();
        let body_hypothesis = ctx.kernel.fvar(body_hypothesis_id);
        let false_proof = ctx.kernel.app(body_proof.proof, body_hypothesis);
        let body_hypothesis_body = ctx
            .kernel
            .abstract_fvars(false_proof, &[body_hypothesis_id]);
        let body_minor = ctx
            .kernel
            .lam(anon, body_prop, body_hypothesis_body, BinderInfo::Default);
        let witness_minor_body = ctx.kernel.abstract_fvars(body_minor, &[witness_id]);
        let minor = ctx
            .kernel
            .lam(anon, carrier, witness_minor_body, BinderInfo::Default);
        kernel_env.remove(&symbol);
        let exists_hypothesis_id = ctx.fresh_fvar();
        let exists_hypothesis = ctx.kernel.fvar(exists_hypothesis_id);
        let eliminated = ctx.exists_elim_false_for_carrier(
            carrier,
            predicate,
            exists_prop,
            minor,
            exists_hypothesis,
        );
        let proof = partition_not_lambda(ctx, exists_prop, exists_hypothesis_id, eliminated);
        Ok(PartitionSignedProof { truth, proof })
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_partition_for_arbitrary(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    desired: bool,
    witness_id: u64,
    witness: ExprId,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    match sort {
        Sort::Bool => {
            let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
            let target = if desired {
                body_prop
            } else {
                ctx.mk_not(body_prop)
            };
            let target_body = ctx.kernel.abstract_fvars(target, &[witness_id]);
            let bool_ty = partition_carrier(ctx, Sort::Bool);
            let anon = ctx.kernel.anon();
            let motive = ctx
                .kernel
                .lam(anon, bool_ty, target_body, BinderInfo::Default);

            let true_value = Value::Bool(true);
            let true_expr = partition_value_expr(ctx, &true_value);
            let mut true_assignment = assignment.clone();
            true_assignment.set(symbol, true_value);
            kernel_env.insert(symbol, true_expr);
            let true_proof =
                prove_partition_formula(ctx, body, &true_assignment, kernel_env, facts)?;
            if true_proof.truth != desired {
                return Err(eq_partition_decline(
                    "Bool true cell disagrees with quantified result",
                ));
            }

            let false_value = Value::Bool(false);
            let false_expr = partition_value_expr(ctx, &false_value);
            let mut false_assignment = assignment.clone();
            false_assignment.set(symbol, false_value);
            kernel_env.insert(symbol, false_expr);
            let false_proof =
                prove_partition_formula(ctx, body, &false_assignment, kernel_env, facts)?;
            if false_proof.truth != desired {
                return Err(eq_partition_decline(
                    "Bool false cell disagrees with quantified result",
                ));
            }
            kernel_env.insert(symbol, witness);
            let zero = ctx.kernel.level_zero();
            let rec = ctx.kernel.const_(ctx.int.logic.bool_rec, vec![zero]);
            let rec = ctx.kernel.app(rec, motive);
            let rec = ctx.kernel.app(rec, true_proof.proof);
            let rec = ctx.kernel.app(rec, false_proof.proof);
            let proof = ctx.kernel.app(rec, witness);
            Ok(PartitionSignedProof {
                truth: desired,
                proof,
            })
        }
        Sort::Int => {
            let mut constants = BTreeSet::new();
            collect_partition_constants(body, symbol, &mut constants);
            let Some(constant) = constants.into_iter().next() else {
                let mut branch_assignment = assignment.clone();
                branch_assignment.set(symbol, Value::Int(0));
                let proof =
                    prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
                if proof.truth != desired {
                    return Err(eq_partition_decline(
                        "unused Int binder disagrees with quantified result",
                    ));
                }
                return Ok(proof);
            };
            let other = constant
                .checked_add(1)
                .or_else(|| constant.checked_sub(1))
                .ok_or_else(|| eq_partition_decline("could not choose adjacent other cell"))?;
            let literal = ctx.mk_intlit(constant);
            let equality = ctx.mk_eq(witness, literal);
            let not_equality = ctx.mk_not(equality);
            let em = ctx.int_eq_em_app(witness, literal);
            let target_prop = {
                let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
                if desired {
                    body_prop
                } else {
                    ctx.mk_not(body_prop)
                }
            };

            let equal_id = ctx.fresh_fvar();
            let equal_hypothesis = ctx.kernel.fvar(equal_id);
            let mut equal_assignment = assignment.clone();
            equal_assignment.set(symbol, Value::Int(constant));
            let mut equal_facts = facts.clone();
            equal_facts.insert(
                (symbol, constant),
                PartitionSignedProof {
                    truth: true,
                    proof: equal_hypothesis,
                },
            );
            let equal_proof =
                prove_partition_formula(ctx, body, &equal_assignment, kernel_env, &equal_facts)?;
            if equal_proof.truth != desired {
                return Err(eq_partition_decline(
                    "equal Int cell disagrees with quantified result",
                ));
            }
            let equal_body = ctx.kernel.abstract_fvars(equal_proof.proof, &[equal_id]);
            let anon = ctx.kernel.anon();
            let equal_case = ctx
                .kernel
                .lam(anon, equality, equal_body, BinderInfo::Default);

            let other_id = ctx.fresh_fvar();
            let other_hypothesis = ctx.kernel.fvar(other_id);
            let mut other_assignment = assignment.clone();
            other_assignment.set(symbol, Value::Int(other));
            let mut other_facts = facts.clone();
            other_facts.insert(
                (symbol, constant),
                PartitionSignedProof {
                    truth: false,
                    proof: other_hypothesis,
                },
            );
            let other_proof =
                prove_partition_formula(ctx, body, &other_assignment, kernel_env, &other_facts)?;
            if other_proof.truth != desired {
                return Err(eq_partition_decline(
                    "other Int cell disagrees with quantified result",
                ));
            }
            let other_body = ctx.kernel.abstract_fvars(other_proof.proof, &[other_id]);
            let anon = ctx.kernel.anon();
            let other_case = ctx
                .kernel
                .lam(anon, not_equality, other_body, BinderInfo::Default);
            let proof = ctx.or_rec_prop(
                equality,
                not_equality,
                target_prop,
                equal_case,
                other_case,
                em,
            );
            Ok(PartitionSignedProof {
                truth: desired,
                proof,
            })
        }
        _ => Err(eq_partition_decline(
            "arbitrary binder has unsupported sort",
        )),
    }
}

fn eq_partition_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("single-pivot equality partition: {detail}"),
    }
}

/// Cheap router predicate for ADR-0106's one-pivot-per-Int-binder proof slice.
pub(crate) fn single_pivot_equality_partition_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    let Some(certificate) =
        crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions)
    else {
        return false;
    };
    lower_single_pivot_partition(arena, certificate.assertion).is_ok()
}

/// Reconstruct an ADR-0101 certificate in the ADR-0106 single-pivot sub-class
/// as a kernel-checked proof over genuine Bool/Int quantifiers.
///
/// The executable equality-partition checker is rerun only to validate the
/// certificate and guide proof search. The generated proof recursively
/// introduces/eliminates every quantifier and connective; arbitrary Int
/// witnesses are split with [`IntPrelude::eq_em`](axeyum_lean_kernel::IntPrelude::eq_em),
/// while arbitrary Bool witnesses use the computational `Bool.rec` eliminator.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for an invalid certificate or
/// formula outside the one-pivot proof slice, and
/// [`ReconstructError::KernelRejected`] if the independently assembled closed
/// proof does not infer to `False`.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_single_pivot_equality_partition_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &EqualityPartitionRefutationCertificate,
) -> Result<String, ReconstructError> {
    if !check_equality_partition_refutation(arena, assertions, certificate) {
        return Err(eq_partition_decline("invalid ADR-0101 certificate"));
    }
    let formula = lower_single_pivot_partition(arena, certificate.assertion)?;
    if !partition_literals_fit_proof_unit_budget(&formula) {
        return Err(eq_partition_decline(
            "integer literals exceed proof-size cap",
        ));
    }
    if partition_formula_truth(&formula, &Assignment::new()) != Some(false) {
        return Err(eq_partition_decline(
            "lowered formula is not false under its exact partitions",
        ));
    }
    let mut ctx = IntReconstructCtx::new();
    let mut kernel_env = PartitionKernelEnv::new();
    let signed = prove_partition_formula(
        &mut ctx,
        &formula,
        &Assignment::new(),
        &mut kernel_env,
        &PartitionFactEnv::new(),
    )?;
    if signed.truth {
        return Err(eq_partition_decline(
            "proof search returned a positive top-level theorem",
        ));
    }
    let proposition = partition_formula_prop(&mut ctx, &formula, &mut kernel_env)?;
    let assertion = ctx.hyp_axiom(proposition)?;
    let proof = ctx.kernel.app(signed.proof, assertion);
    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
    ctx.require_partition_type(proof, false_, "final contradiction")?;
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}
