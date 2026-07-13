//! Lean reconstruction for ADR-0134 positive-universal Bool/BV instance sets.
//!
//! The residual SAT proof is not trusted to introduce its own assumptions.  Each
//! residual formula is proved from an axiom for the untouched source assertion:
//! conjunctions are projected, universal binders are applied to the certificate's
//! concrete values, and only then is the propositional Alethe tail reconstructed.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_aig::{AigLit, AigNode};
use axeyum_bv::{BitLowering, lower_terms};
use axeyum_cnf::{AletheCommand, AletheTerm};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_lean_kernel::{BinderInfo, Declaration};

use super::{
    Clause, DatatypeInductive, ExprId, LEAN_MODULE_THEOREM, ReconstructCtx, ReconstructError,
    and_project, check_against, check_false_prop, fresh_axiom, fresh_fvar_id,
    reconstruct_bitwise_step, require_infers_false,
};
use crate::{
    BvPositiveUniversalInstanceSetCertificate, BvPositiveUniversalSourceInstance,
    check_bv_positive_universal_instance_set,
};

const MAX_LEAN_BV_WIDTH: u32 = 64;

type CarriedBindings = Vec<(SymbolId, Value)>;
type SourceAssumption = (TermId, ExprId, Option<CarriedBindings>);

fn decline(detail: impl Into<String>) -> ReconstructError {
    ReconstructError::MalformedStep {
        rule: "bv_positive_universal_instance_set".to_owned(),
        detail: detail.into(),
    }
}

fn c(name: impl Into<String>) -> AletheTerm {
    AletheTerm::Const(name.into())
}

fn app(head: &str, args: impl IntoIterator<Item = AletheTerm>) -> AletheTerm {
    AletheTerm::App(head.to_owned(), args.into_iter().collect())
}

fn not(term: AletheTerm) -> AletheTerm {
    app("not", [term])
}

fn and(left: AletheTerm, right: AletheTerm) -> AletheTerm {
    app("and", [left, right])
}

fn or(left: AletheTerm, right: AletheTerm) -> AletheTerm {
    app("or", [left, right])
}

fn iff(left: AletheTerm, right: AletheTerm) -> AletheTerm {
    app("=", [left, right])
}

fn xor(left: AletheTerm, right: AletheTerm) -> AletheTerm {
    app("xor", [left, right])
}

fn ite(condition: AletheTerm, then_: AletheTerm, else_: AletheTerm) -> AletheTerm {
    or(and(condition.clone(), then_), and(not(condition), else_))
}

fn and_fold(mut terms: Vec<AletheTerm>) -> Result<AletheTerm, ReconstructError> {
    let Some(mut result) = terms.pop() else {
        return Err(decline("empty Boolean conjunction"));
    };
    while let Some(term) = terms.pop() {
        result = and(term, result);
    }
    Ok(result)
}

fn symbol_key(symbol: SymbolId, sort: Sort) -> String {
    match sort {
        Sort::Bool => format!("!quant_bv_bool_{}", symbol.index()),
        Sort::BitVec(_) => format!("!quant_bv_value_{}", symbol.index()),
        _ => format!("!quant_bv_unsupported_{}", symbol.index()),
    }
}

fn bit_of(operand: AletheTerm, index: usize) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(index).expect("bounded BV index fits i128")],
        args: vec![operand],
    }
}

fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
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

fn qf_bool_formula(arena: &TermArena, term: TermId) -> Result<AletheTerm, ReconstructError> {
    if arena.sort_of(term) != Sort::Bool {
        return Err(decline("expected a Boolean formula"));
    }
    match arena.node(term) {
        TermNode::BoolConst(value) => Ok(c(if *value { "true" } else { "false" })),
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            Ok(c(symbol_key(*symbol, Sort::Bool)))
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [inner]) => Ok(not(qf_bool_formula(arena, *inner)?)),
            (Op::BoolAnd, [left, right]) => Ok(and(
                qf_bool_formula(arena, *left)?,
                qf_bool_formula(arena, *right)?,
            )),
            (Op::BoolOr, [left, right]) => Ok(or(
                qf_bool_formula(arena, *left)?,
                qf_bool_formula(arena, *right)?,
            )),
            (Op::BoolXor, [left, right]) => Ok(xor(
                qf_bool_formula(arena, *left)?,
                qf_bool_formula(arena, *right)?,
            )),
            (Op::BoolImplies, [left, right]) => Ok(or(
                not(qf_bool_formula(arena, *left)?),
                qf_bool_formula(arena, *right)?,
            )),
            (Op::Ite, [condition, then_, else_]) => Ok(ite(
                qf_bool_formula(arena, *condition)?,
                qf_bool_formula(arena, *then_)?,
                qf_bool_formula(arena, *else_)?,
            )),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => Ok(iff(
                qf_bool_formula(arena, *left)?,
                qf_bool_formula(arena, *right)?,
            )),
            (Op::Eq, [left, right]) if matches!(arena.sort_of(*left), Sort::BitVec(_)) => {
                let left = qf_bv_bits(arena, *left)?;
                let right = qf_bv_bits(arena, *right)?;
                if left.len() != right.len() {
                    return Err(decline("bit-vector equality width mismatch"));
                }
                and_fold(
                    left.into_iter()
                        .zip(right)
                        .map(|(left, right)| iff(left, right))
                        .collect(),
                )
            }
            (Op::BvUlt, [left, right]) => bv_ult(arena, *left, *right),
            (Op::BvUle, [left, right]) => Ok(not(bv_ult(arena, *right, *left)?)),
            (Op::BvUgt, [left, right]) => bv_ult(arena, *right, *left),
            (Op::BvUge, [left, right]) => Ok(not(bv_ult(arena, *left, *right)?)),
            (Op::BvSlt, [left, right]) => bv_slt(arena, *left, *right),
            (Op::BvSle, [left, right]) => Ok(not(bv_slt(arena, *right, *left)?)),
            (Op::BvSgt, [left, right]) => bv_slt(arena, *right, *left),
            (Op::BvSge, [left, right]) => Ok(not(bv_slt(arena, *left, *right)?)),
            _ => Err(decline(format!(
                "unsupported quantified-BV Boolean op {op:?}"
            ))),
        },
        other => Err(decline(format!(
            "unsupported quantified-BV Boolean node {other:?}"
        ))),
    }
}

fn qf_bv_bits(arena: &TermArena, term: TermId) -> Result<Vec<AletheTerm>, ReconstructError> {
    let Sort::BitVec(width) = arena.sort_of(term) else {
        return Err(decline("expected a bit-vector term"));
    };
    if width == 0 || width > MAX_LEAN_BV_WIDTH {
        return Err(decline(format!(
            "Lean BV width {width} is outside 1..={MAX_LEAN_BV_WIDTH}"
        )));
    }
    let width_usize = usize::try_from(width).expect("u32 width fits usize");
    match arena.node(term) {
        TermNode::BvConst { value, .. } => Ok((0..width_usize)
            .map(|index| {
                c(if (value >> index) & 1 == 1 {
                    "true"
                } else {
                    "false"
                })
            })
            .collect()),
        TermNode::Symbol(symbol) => {
            let key = symbol_key(*symbol, Sort::BitVec(width));
            Ok((0..width_usize)
                .map(|index| bit_of(c(key.clone()), index))
                .collect())
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BvNot, [inner]) => Ok(qf_bv_bits(arena, *inner)?.into_iter().map(not).collect()),
            (Op::BvAnd, [left, right]) => bv_binary(arena, *left, *right, and),
            (Op::BvOr, [left, right]) => bv_binary(arena, *left, *right, or),
            (Op::BvXor, [left, right]) => bv_binary(arena, *left, *right, xor),
            (Op::BvXnor, [left, right]) => bv_binary(arena, *left, *right, iff),
            (Op::BvNand, [left, right]) => Ok(bv_binary(arena, *left, *right, and)?
                .into_iter()
                .map(not)
                .collect()),
            (Op::BvNor, [left, right]) => Ok(bv_binary(arena, *left, *right, or)?
                .into_iter()
                .map(not)
                .collect()),
            (Op::BvAdd, [left, right]) => bv_add(arena, *left, *right),
            (Op::BvNeg, [inner]) => {
                let bits = qf_bv_bits(arena, *inner)?;
                let one = (0..bits.len())
                    .map(|index| c(if index == 0 { "true" } else { "false" }))
                    .collect();
                Ok(add_bits(bits.into_iter().map(not).collect(), one))
            }
            (Op::BvSub, [left, right]) => {
                let left = qf_bv_bits(arena, *left)?;
                let right = qf_bv_bits(arena, *right)?;
                let one = (0..right.len())
                    .map(|index| c(if index == 0 { "true" } else { "false" }))
                    .collect();
                Ok(add_bits(
                    left,
                    add_bits(right.into_iter().map(not).collect(), one),
                ))
            }
            (Op::Ite, [condition, then_, else_]) => {
                let condition = qf_bool_formula(arena, *condition)?;
                let then_bits = qf_bv_bits(arena, *then_)?;
                let else_bits = qf_bv_bits(arena, *else_)?;
                Ok(then_bits
                    .into_iter()
                    .zip(else_bits)
                    .map(|(then_bit, else_bit)| ite(condition.clone(), then_bit, else_bit))
                    .collect())
            }
            (Op::Extract { hi, lo }, [inner]) => {
                let bits = qf_bv_bits(arena, *inner)?;
                Ok(bits[usize::try_from(*lo).expect("u32 fits usize")
                    ..=usize::try_from(*hi).expect("u32 fits usize")]
                    .to_vec())
            }
            (Op::Concat, [high, low]) => {
                let mut bits = qf_bv_bits(arena, *low)?;
                bits.extend(qf_bv_bits(arena, *high)?);
                Ok(bits)
            }
            (Op::ZeroExt { by }, [inner]) => {
                let mut bits = qf_bv_bits(arena, *inner)?;
                bits.extend((0..*by).map(|_| c("false")));
                Ok(bits)
            }
            (Op::SignExt { by }, [inner]) => {
                let mut bits = qf_bv_bits(arena, *inner)?;
                let sign = bits
                    .last()
                    .cloned()
                    .ok_or_else(|| decline("zero-width BV"))?;
                bits.extend((0..*by).map(|_| sign.clone()));
                Ok(bits)
            }
            _ => Err(decline(format!("unsupported quantified-BV term op {op:?}"))),
        },
        other => Err(decline(format!(
            "unsupported quantified-BV term node {other:?}"
        ))),
    }
}

fn bv_binary(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    combine: fn(AletheTerm, AletheTerm) -> AletheTerm,
) -> Result<Vec<AletheTerm>, ReconstructError> {
    let left = qf_bv_bits(arena, left)?;
    let right = qf_bv_bits(arena, right)?;
    if left.len() != right.len() {
        return Err(decline("bit-vector operand width mismatch"));
    }
    Ok(left
        .into_iter()
        .zip(right)
        .map(|(left, right)| combine(left, right))
        .collect())
}

fn add_bits(left: Vec<AletheTerm>, right: Vec<AletheTerm>) -> Vec<AletheTerm> {
    let mut carry = c("false");
    left.into_iter()
        .zip(right)
        .map(|(left, right)| {
            let sum = xor(xor(left.clone(), right.clone()), carry.clone());
            carry = or(
                and(left.clone(), right.clone()),
                and(carry.clone(), or(left, right)),
            );
            sum
        })
        .collect()
}

fn bv_add(
    arena: &TermArena,
    left: TermId,
    right: TermId,
) -> Result<Vec<AletheTerm>, ReconstructError> {
    let left = qf_bv_bits(arena, left)?;
    let right = qf_bv_bits(arena, right)?;
    if left.len() != right.len() {
        return Err(decline("bit-vector addition width mismatch"));
    }
    Ok(add_bits(left, right))
}

fn bv_ult(arena: &TermArena, left: TermId, right: TermId) -> Result<AletheTerm, ReconstructError> {
    let left = qf_bv_bits(arena, left)?;
    let right = qf_bv_bits(arena, right)?;
    if left.len() != right.len() || left.is_empty() {
        return Err(decline("unsigned comparison width mismatch"));
    }
    let mut result = and(not(left[0].clone()), right[0].clone());
    for index in 1..left.len() {
        result = or(
            and(iff(left[index].clone(), right[index].clone()), result),
            and(not(left[index].clone()), right[index].clone()),
        );
    }
    Ok(result)
}

fn bv_slt(arena: &TermArena, left: TermId, right: TermId) -> Result<AletheTerm, ReconstructError> {
    let left = qf_bv_bits(arena, left)?;
    let right = qf_bv_bits(arena, right)?;
    if left.len() != right.len() || left.is_empty() {
        return Err(decline("signed comparison width mismatch"));
    }
    if left.len() == 1 {
        return Ok(and(left[0].clone(), not(right[0].clone())));
    }
    let mut result = and(not(left[0].clone()), right[0].clone());
    for index in 1..left.len() - 1 {
        result = or(
            and(iff(left[index].clone(), right[index].clone()), result),
            and(not(left[index].clone()), right[index].clone()),
        );
    }
    let sign = left.len() - 1;
    Ok(or(
        and(iff(left[sign].clone(), right[sign].clone()), result),
        and(left[sign].clone(), not(right[sign].clone())),
    ))
}

impl ReconstructCtx {
    pub(super) fn typed_bool_value_prop(&mut self, value: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let bool_ty = self.kernel.const_(self.prelude.bool_, vec![]);
        let prop = self.kernel.sort_zero();
        let motive = self.kernel.lam(anon, bool_ty, prop, BinderInfo::Default);
        let true_prop = self.kernel.const_(self.prelude.true_, vec![]);
        let false_prop = self.kernel.const_(self.prelude.false_, vec![]);
        let rec = self.kernel.const_(self.prelude.bool_rec, vec![self.one]);
        let applied = self.kernel.app(rec, motive);
        let applied = self.kernel.app(applied, true_prop);
        let applied = self.kernel.app(applied, false_prop);
        self.kernel.app(applied, value)
    }

    fn typed_bv_type(&mut self, width: usize) -> Result<DatatypeInductive, ReconstructError> {
        if let Some(&datatype) = self.bv_value_types.get(&width) {
            return Ok(datatype);
        }
        let name = self.fresh_name(&format!("bv{width}"));
        let prop = self.kernel.sort_zero();
        let datatype = self
            .kernel
            .add_datatype_inductive(name, prop, self.one, width)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "quantified_bv_type".to_owned(),
                detail: format!("finite-bit datatype did not admit: {error:?}"),
            })?;
        self.bv_value_types.insert(width, datatype);
        Ok(datatype)
    }

    pub(super) fn typed_bv_projection(
        &mut self,
        operand: &AletheTerm,
        index: usize,
    ) -> Option<ExprId> {
        let AletheTerm::Const(symbol) = operand else {
            return None;
        };
        let (width, value) = if let Some(&(width, value)) = self.gate_bound_bvs.get(symbol) {
            (width, value)
        } else {
            let width = *self.bv_widths.get(symbol)?;
            if index >= width {
                return None;
            }
            let name = if let Some(&(_, name)) = self.bv_value_symbols.get(symbol) {
                name
            } else {
                let datatype = self.typed_bv_type(width).ok()?;
                let ty = self.kernel.const_(datatype.ind, vec![]);
                let name = self.fresh_name("bv_value");
                self.kernel
                    .add_declaration(Declaration::Axiom {
                        name,
                        uparams: vec![],
                        ty,
                    })
                    .ok()?;
                self.bv_value_symbols.insert(symbol.clone(), (width, name));
                name
            };
            (width, self.kernel.const_(name, vec![]))
        };
        if index >= width {
            return None;
        }
        let datatype = self.typed_bv_type(width).ok()?;
        let prop = self.kernel.sort_zero();
        let selector = self
            .kernel
            .datatype_selector(datatype, prop, self.one, index);
        Some(self.kernel.app(selector, value))
    }

    fn typed_bv_literal(&mut self, width: usize, value: u128) -> Result<ExprId, ReconstructError> {
        let datatype = self.typed_bv_type(width)?;
        let mut result = self.kernel.const_(datatype.ctor, vec![]);
        for index in 0..width {
            let proposition = if (value >> index) & 1 == 1 {
                self.kernel.const_(self.prelude.true_, vec![])
            } else {
                self.kernel.const_(self.prelude.false_, vec![])
            };
            result = self.kernel.app(result, proposition);
        }
        Ok(result)
    }
}

fn register_bv_widths(ctx: &mut ReconstructCtx, arena: &TermArena, root: TermId) {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                if let Sort::BitVec(width) = arena.symbol(*symbol).1 {
                    ctx.bv_widths.insert(
                        symbol_key(*symbol, Sort::BitVec(width)),
                        usize::try_from(width).expect("u32 width fits usize"),
                    );
                }
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

fn direct_ground_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    register_bv_widths(ctx, arena, term);
    let lowering = lower_terms(arena, &[term])
        .map_err(|error| decline(format!("AIG source lowering failed: {error}")))?;
    aig_root_prop(ctx, &lowering)
}

fn aig_root_prop(
    ctx: &mut ReconstructCtx,
    lowering: &BitLowering,
) -> Result<ExprId, ReconstructError> {
    let mut nodes = Vec::with_capacity(lowering.aig().node_count());
    for (node_id, node) in lowering.aig().nodes() {
        let proposition = match node {
            AigNode::ConstFalse => ctx.kernel.const_(ctx.prelude.false_, vec![]),
            AigNode::Input(input) => {
                let binding = lowering
                    .symbol_inputs()
                    .get(input.index())
                    .ok_or_else(|| decline("AIG input lacks a source binding"))?;
                match binding.sort {
                    Sort::Bool => {
                        let key = symbol_key(binding.symbol, Sort::Bool);
                        if let Some(&value) = ctx.gate_bound_bools.get(&key) {
                            ctx.typed_bool_value_prop(value)
                        } else {
                            let name = ctx.prop_atom_const(&key);
                            ctx.kernel.const_(name, vec![])
                        }
                    }
                    Sort::BitVec(width) => {
                        let key = symbol_key(binding.symbol, Sort::BitVec(width));
                        ctx.typed_bv_projection(
                            &c(key),
                            usize::try_from(binding.bit_index).expect("u32 bit index fits usize"),
                        )
                        .ok_or_else(|| decline("typed AIG BV projection failed"))?
                    }
                    sort => return Err(decline(format!("unsupported AIG input sort {sort:?}"))),
                }
            }
            AigNode::And(left, right) => {
                let left = aig_lit_prop(ctx, &nodes, left)?;
                let right = aig_lit_prop(ctx, &nodes, right)?;
                ctx.mk_and(left, right)
            }
        };
        debug_assert_eq!(node_id.index(), nodes.len());
        nodes.push(proposition);
    }
    let root = lowering
        .roots()
        .first()
        .and_then(|root| root.bits().first())
        .copied()
        .ok_or_else(|| decline("AIG lowering lacks a Boolean root"))?;
    aig_lit_prop(ctx, &nodes, root)
}

fn aig_lit_prop(
    ctx: &mut ReconstructCtx,
    nodes: &[ExprId],
    literal: AigLit,
) -> Result<ExprId, ReconstructError> {
    let proposition = *nodes
        .get(literal.node().index())
        .ok_or_else(|| decline("AIG literal references a future node"))?;
    Ok(if literal.is_inverted() {
        ctx.mk_not(proposition)
    } else {
        proposition
    })
}

fn ground_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    if contains_quantifier(arena, term) {
        return Err(decline("quantifier reached the ground translator"));
    }
    direct_ground_prop(ctx, arena, term)
}

fn collect_forall_chain(
    arena: &TermArena,
    mut term: TermId,
) -> Result<(Vec<SymbolId>, TermId), ReconstructError> {
    let mut binders = Vec::new();
    loop {
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(symbol),
                args,
            } if args.len() == 1 => {
                let sort = arena.symbol(*symbol).1;
                if !matches!(sort, Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)) {
                    return Err(decline(format!(
                        "unsupported universal binder sort {sort:?}"
                    )));
                }
                binders.push(*symbol);
                term = args[0];
            }
            _ => break,
        }
    }
    if binders.is_empty() || contains_quantifier(arena, term) {
        return Err(decline(
            "universals must form a direct chain with a quantifier-free body",
        ));
    }
    Ok((binders, term))
}

fn universal_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    let (binders, body) = collect_forall_chain(arena, term)?;
    register_bv_widths(ctx, arena, body);
    let mut fvars = Vec::with_capacity(binders.len());
    let mut domains = Vec::with_capacity(binders.len());
    for &binder in &binders {
        let id = fresh_fvar_id(ctx);
        let value = ctx.kernel.fvar(id);
        match arena.symbol(binder).1 {
            Sort::Bool => {
                ctx.gate_bound_bools
                    .insert(symbol_key(binder, Sort::Bool), value);
                domains.push(ctx.kernel.const_(ctx.prelude.bool_, vec![]));
            }
            Sort::BitVec(width) => {
                let width_usize = usize::try_from(width).expect("u32 width fits usize");
                ctx.gate_bound_bvs.insert(
                    symbol_key(binder, Sort::BitVec(width)),
                    (width_usize, value),
                );
                let datatype = ctx.typed_bv_type(width_usize)?;
                domains.push(ctx.kernel.const_(datatype.ind, vec![]));
            }
            _ => return Err(decline("non-Bool/BV universal binder")),
        }
        fvars.push(id);
    }
    let proposition = direct_ground_prop(ctx, arena, body)?;
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    let mut proposition = ctx.kernel.abstract_fvars(proposition, &fvars);
    for domain in domains.into_iter().rev() {
        let anon = ctx.kernel.anon();
        proposition = ctx
            .kernel
            .pi(anon, domain, proposition, BinderInfo::Default);
    }
    Ok(proposition)
}

fn source_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 && contains_quantifier(arena, term) => {
            let left = source_prop(ctx, arena, args[0])?;
            let right = source_prop(ctx, arena, args[1])?;
            Ok(ctx.mk_and(left, right))
        }
        TermNode::App {
            op: Op::Forall(_), ..
        } => universal_prop(ctx, arena, term),
        _ if !contains_quantifier(arena, term) => ground_prop(ctx, arena, term),
        _ => Err(decline("quantifier is not a top-level conjunction leaf")),
    }
}

fn collect_skeleton_assumptions(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proof: ExprId,
    out: &mut Vec<SourceAssumption>,
) -> Result<(), ReconstructError> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 && contains_quantifier(arena, term) => {
            let left_prop = source_prop(ctx, arena, args[0])?;
            let right_prop = source_prop(ctx, arena, args[1])?;
            let left = and_project(ctx, left_prop, right_prop, proof, true);
            let right = and_project(ctx, left_prop, right_prop, proof, false);
            collect_skeleton_assumptions(ctx, arena, args[0], left, out)?;
            collect_skeleton_assumptions(ctx, arena, args[1], right, out)
        }
        TermNode::App {
            op: Op::Forall(_), ..
        } => Ok(()),
        _ if !contains_quantifier(arena, term) => {
            out.push((term, proof, None));
            Ok(())
        }
        _ => Err(decline("unsupported skeleton conjunction context")),
    }
}

fn collect_instance_assumptions(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    source_term: TermId,
    residual_term: TermId,
    proof: ExprId,
    source: &BvPositiveUniversalSourceInstance,
    out: &mut Vec<SourceAssumption>,
) -> Result<(), ReconstructError> {
    match arena.node(source_term) {
        TermNode::App {
            op: Op::BoolAnd,
            args: source_args,
        } if source_args.len() == 2 && contains_quantifier(arena, source_term) => {
            let TermNode::App {
                op: Op::BoolAnd,
                args: residual_args,
            } = arena.node(residual_term)
            else {
                return Err(decline("instance residual lost conjunction shape"));
            };
            if residual_args.len() != 2 {
                return Err(decline("malformed instance residual conjunction"));
            }
            let left_prop = source_prop(ctx, arena, source_args[0])?;
            let right_prop = source_prop(ctx, arena, source_args[1])?;
            let left = and_project(ctx, left_prop, right_prop, proof, true);
            let right = and_project(ctx, left_prop, right_prop, proof, false);
            collect_instance_assumptions(
                ctx,
                arena,
                source_args[0],
                residual_args[0],
                left,
                source,
                out,
            )?;
            collect_instance_assumptions(
                ctx,
                arena,
                source_args[1],
                residual_args[1],
                right,
                source,
                out,
            )
        }
        TermNode::App {
            op: Op::Forall(_), ..
        } => {
            let applied = apply_instance(ctx, arena, source_term, proof, source)?;
            let (_, body) = collect_forall_chain(arena, source_term)?;
            out.push((body, applied, Some(source.bindings.clone())));
            Ok(())
        }
        _ if !contains_quantifier(arena, source_term) => {
            out.push((source_term, proof, None));
            Ok(())
        }
        _ => Err(decline("unsupported instance conjunction context")),
    }
}

fn binding_map(source: &BvPositiveUniversalSourceInstance) -> BTreeMap<SymbolId, &Value> {
    source
        .bindings
        .iter()
        .map(|(symbol, value)| (*symbol, value))
        .collect()
}

fn install_binding_environment(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    bindings: &[(SymbolId, Value)],
) -> Result<(), ReconstructError> {
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    for (symbol, value) in bindings {
        match value {
            Value::Bool(value) => {
                let witness = ctx.kernel.const_(
                    if *value {
                        ctx.prelude.bool_true
                    } else {
                        ctx.prelude.bool_false
                    },
                    vec![],
                );
                ctx.gate_bound_bools
                    .insert(symbol_key(*symbol, Sort::Bool), witness);
            }
            Value::Bv { width, value } => {
                if arena.symbol(*symbol).1 != Sort::BitVec(*width) {
                    return Err(decline("carried BV binding sort mismatch"));
                }
                let width_usize = usize::try_from(*width).expect("u32 width fits usize");
                let witness = ctx.typed_bv_literal(width_usize, *value)?;
                ctx.gate_bound_bvs.insert(
                    symbol_key(*symbol, Sort::BitVec(*width)),
                    (width_usize, witness),
                );
            }
            _ => return Err(decline("non-Bool/BV carried binding")),
        }
    }
    Ok(())
}

fn apply_instance(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    mut proof: ExprId,
    source: &BvPositiveUniversalSourceInstance,
) -> Result<ExprId, ReconstructError> {
    let (binders, _) = collect_forall_chain(arena, term)?;
    let bindings = binding_map(source);
    for binder in binders {
        let value = bindings
            .get(&binder)
            .ok_or_else(|| decline("instance omits a universal binder"))?;
        let witness = match (arena.symbol(binder).1, *value) {
            (Sort::Bool, Value::Bool(value)) => ctx.kernel.const_(
                if *value {
                    ctx.prelude.bool_true
                } else {
                    ctx.prelude.bool_false
                },
                vec![],
            ),
            (
                Sort::BitVec(width),
                Value::Bv {
                    width: carried,
                    value,
                },
            ) if width == *carried => ctx.typed_bv_literal(
                usize::try_from(width).expect("u32 width fits usize"),
                *value,
            )?,
            _ => return Err(decline("instance witness sort does not match binder")),
        };
        proof = ctx.kernel.app(proof, witness);
    }
    Ok(proof)
}

fn reconstruct_gate_tail(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
    assumption_proofs: &[ExprId],
) -> Result<ExprId, ReconstructError> {
    let _ = ctx.em_axiom();
    let mut proofs = assumption_proofs.iter();
    let mut env = BTreeMap::new();
    for command in commands {
        match command {
            AletheCommand::Assume { id, clause } => {
                let proof = *proofs
                    .next()
                    .ok_or_else(|| decline("Alethe tail has too many assumptions"))?;
                let proposition = ctx.clause_to_prop(clause);
                let proof = check_against(ctx, "source_instance_assume", proof, proposition)?;
                env.insert(
                    id.clone(),
                    Clause {
                        lits: clause.clone(),
                        proof,
                    },
                );
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                if let Some(recovered) =
                    reconstruct_bitwise_step(ctx, rule, clause, premises, &env)?
                {
                    if clause.is_empty() {
                        if proofs.next().is_some() {
                            return Err(decline("unused source-derived assumptions"));
                        }
                        return check_false_prop(ctx, recovered.proof);
                    }
                    env.insert(id.clone(), recovered);
                }
            }
        }
    }
    Err(ReconstructError::NoEmptyClause)
}

fn aig_gate_tail(
    arena: &TermArena,
    residual: &[(TermId, Option<CarriedBindings>)],
) -> Result<(Vec<AletheTerm>, BTreeMap<String, AletheTerm>), ReconstructError> {
    let mut formulas = Vec::with_capacity(residual.len());
    let mut definitions = BTreeMap::new();
    for (formula_index, (term, carried)) in residual.iter().enumerate() {
        let lowering = lower_terms(arena, &[*term])
            .map_err(|error| decline(format!("AIG residual lowering failed: {error}")))?;
        let carried = carried
            .as_ref()
            .map(|bindings| binding_map_owned(bindings))
            .unwrap_or_default();
        let mut nodes = Vec::with_capacity(lowering.aig().node_count());
        for (node_id, node) in lowering.aig().nodes() {
            let node_term = match node {
                AigNode::ConstFalse => c("false"),
                AigNode::Input(input) => {
                    let binding = lowering
                        .symbol_inputs()
                        .get(input.index())
                        .ok_or_else(|| decline("AIG tail input lacks a source binding"))?;
                    if let Some(value) = carried.get(&binding.symbol) {
                        let bit = match value {
                            Value::Bool(value) if binding.bit_index == 0 => *value,
                            Value::Bv { value, .. } => (value >> binding.bit_index) & 1 == 1,
                            _ => return Err(decline("carried AIG input value mismatch")),
                        };
                        c(if bit { "true" } else { "false" })
                    } else {
                        match binding.sort {
                            Sort::Bool => c(symbol_key(binding.symbol, Sort::Bool)),
                            Sort::BitVec(width) => bit_of(
                                c(symbol_key(binding.symbol, Sort::BitVec(width))),
                                usize::try_from(binding.bit_index)
                                    .expect("u32 bit index fits usize"),
                            ),
                            sort => {
                                return Err(decline(format!(
                                    "unsupported AIG tail input sort {sort:?}"
                                )));
                            }
                        }
                    }
                }
                AigNode::And(left, right) => {
                    let left = aig_lit_gate(&nodes, left)?;
                    let right = aig_lit_gate(&nodes, right)?;
                    let name = format!("!quant_bv_aig_{formula_index}_{}", node_id.index());
                    definitions.insert(name.clone(), app("and", [left, right]));
                    c(name)
                }
            };
            debug_assert_eq!(node_id.index(), nodes.len());
            nodes.push(node_term);
        }
        let root = lowering
            .roots()
            .first()
            .and_then(|root| root.bits().first())
            .copied()
            .ok_or_else(|| decline("AIG tail root is empty"))?;
        formulas.push(aig_lit_gate(&nodes, root)?);
    }
    Ok((formulas, definitions))
}

fn binding_map_owned(bindings: &[(SymbolId, Value)]) -> BTreeMap<SymbolId, &Value> {
    bindings
        .iter()
        .map(|(symbol, value)| (*symbol, value))
        .collect()
}

fn aig_lit_gate(nodes: &[AletheTerm], literal: AigLit) -> Result<AletheTerm, ReconstructError> {
    let term = nodes
        .get(literal.node().index())
        .cloned()
        .ok_or_else(|| decline("AIG gate literal references a future node"))?;
    Ok(if literal.is_inverted() {
        not(term)
    } else {
        term
    })
}

/// Cheap structural classification used by the public proof-fragment scanner.
pub(crate) fn bv_positive_universal_instance_set_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    !assertions.is_empty()
        && assertions
            .iter()
            .any(|&term| contains_quantifier(arena, term))
        && assertions.iter().all(|&term| source_shape(arena, term))
}

fn source_shape(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 && contains_quantifier(arena, term) => {
            source_shape(arena, args[0]) && source_shape(arena, args[1])
        }
        TermNode::App {
            op: Op::Forall(_), ..
        } => collect_forall_chain(arena, term)
            .and_then(|(_, body)| qf_bool_formula(arena, body))
            .is_ok(),
        _ if !contains_quantifier(arena, term) => qf_bool_formula(arena, term).is_ok(),
        _ => false,
    }
}

/// Reconstructs an ADR-0134 instance-set certificate to a kernel-checked Lean
/// module whose only source hypotheses are the untouched query assertions.
///
/// # Errors
///
/// Returns [`ReconstructError`] when the source is outside the admitted
/// positive-universal Bool/BV shape, certificate replay fails, a source
/// instance cannot be derived, or the reconstructed proof is rejected.
pub fn reconstruct_bv_positive_universal_instance_set_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPositiveUniversalInstanceSetCertificate,
) -> Result<String, ReconstructError> {
    if !bv_positive_universal_instance_set_lean_shape(arena, assertions) {
        return Err(decline("unsupported source shape"));
    }
    if !check_bv_positive_universal_instance_set(arena, assertions, certificate)
        .map_err(|error| decline(format!("certificate replay failed: {error}")))?
    {
        return Err(decline("invalid ADR-0134 certificate"));
    }
    let Some((scratch, residual)) =
        crate::quant_bv_instance_set_cert::rebuild_bv_positive_universal_instance_set(
            arena,
            assertions,
            certificate,
        )
        .map_err(|error| decline(format!("residual rebuild failed: {error}")))?
    else {
        return Err(decline("certificate does not rebuild"));
    };
    let mut ctx = ReconstructCtx::new();
    ctx.bridge = Some(BTreeMap::new());
    ctx.typed_bv_gates = true;
    let mut source_proofs = BTreeMap::new();
    for &assertion in assertions {
        let proposition = source_prop(&mut ctx, &scratch, assertion)?;
        let proof = fresh_axiom(&mut ctx, proposition, "quant-bv-source")?;
        source_proofs.insert(assertion, proof);
    }
    let mut source_assumptions = Vec::new();
    for &assertion in assertions {
        let proof = source_proofs[&assertion];
        collect_skeleton_assumptions(
            &mut ctx,
            &scratch,
            assertion,
            proof,
            &mut source_assumptions,
        )?;
    }
    for (source, &residual_term) in certificate
        .instances
        .iter()
        .zip(&residual[assertions.len()..])
    {
        let proof = *source_proofs
            .get(&source.assertion)
            .ok_or_else(|| decline("instance source is not a query assertion"))?;
        collect_instance_assumptions(
            &mut ctx,
            &scratch,
            source.assertion,
            residual_term,
            proof,
            source,
            &mut source_assumptions,
        )?;
    }
    let mut assumptions = Vec::with_capacity(source_assumptions.len());
    let mut tail_terms = Vec::with_capacity(source_assumptions.len());
    for (term, proof, bindings) in source_assumptions {
        if let Some(bindings) = &bindings {
            install_binding_environment(&mut ctx, &scratch, bindings)?;
        } else {
            ctx.gate_bound_bools.clear();
            ctx.gate_bound_bvs.clear();
        }
        let expected = ground_prop(&mut ctx, &scratch, term)?;
        ctx.gate_bound_bools.clear();
        ctx.gate_bound_bvs.clear();
        assumptions.push(check_against(
            &mut ctx,
            "quant_bv_source_instance",
            proof,
            expected,
        )?);
        tail_terms.push((term, bindings));
    }
    let (formulas, definitions) = aig_gate_tail(&scratch, &tail_terms)?;
    let (commands, gate_defs) =
        crate::qfbv_alethe::prove_bit_gate_unsat_alethe(&formulas, definitions)
            .ok_or_else(|| decline("propositional residual emitter declined"))?;
    ctx.bridge = Some(gate_defs);
    ctx.gate_memo.clear();
    let proof = reconstruct_gate_tail(&mut ctx, &commands, &assumptions)?;
    require_infers_false(&mut ctx, proof)?;
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let mut inductives = ctx
        .bv_value_types
        .values()
        .map(|datatype| datatype.ind)
        .collect::<Vec<_>>();
    // Bool.rec computes bound Bool witnesses; external Lean must retain the same
    // iota behavior as the in-tree kernel.
    inductives.push(ctx.prelude.bool_);
    Ok(ctx.kernel.render_lean_module_compact_with_inductives(
        LEAN_MODULE_THEOREM,
        false_,
        proof,
        &inductives,
    ))
}
