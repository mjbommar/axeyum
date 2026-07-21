//! Lean reconstruction for ADR-0134 positive-universal Bool/BV instance sets.
//!
//! The residual SAT proof is not trusted to introduce its own assumptions.  Each
//! residual formula is proved from an axiom for the untouched source assertion:
//! conjunctions are projected, universal binders are applied to the certificate's
//! concrete values, and only then is the propositional Alethe tail reconstructed.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use axeyum_aig::{AigLit, AigNode};
use axeyum_bv::{BitLowering, lower_terms};
use axeyum_cnf::{AletheCommand, AletheTerm};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_lean_kernel::{BinderInfo, Declaration, NameId, ReducibilityHint};

use super::{
    Clause, DatatypeInductive, ExprId, LEAN_MODULE_THEOREM, ReconstructCtx, ReconstructError,
    LocalDecl, and_intro, and_project, check_against, check_false_prop, double_negation_elim,
    fresh_axiom, fresh_fvar_id, reconstruct_bitwise_cps_tail, reconstruct_bitwise_step,
    render_ctx_module, require_infers_false,
};
use crate::{
    BvAlternationCounterexampleCertificate, BvPairedExistentialTransferCertificate,
    BvConjunctiveUniversalInstanceCertificate, BvPairedExistentialTransferJustification,
    BvPositiveUniversalInstanceSetCertificate, BvPositiveUniversalSourceInstance,
    ClosedUniversalCounterexampleCertificate, NegatedExistentialWitnessCertificate,
    VacuousExistsUniversalCounterexampleCertificate,
    check_bv_alternation_counterexample, check_bv_conjunctive_universal_instance,
    check_bv_paired_existential_transfer, check_bv_positive_universal_instance_set,
    check_closed_universal_counterexample, check_negated_existential_witness,
    check_vacuous_exists_universal_counterexample,
};

const MAX_LEAN_BV_WIDTH: u32 = 64;
const COMPUTATIONAL_WITNESS_AIG_THRESHOLD: usize = 512;
static NEXT_LEAN_MODULE_SPOOL: AtomicU64 = AtomicU64::new(0);

type CarriedBindings = Vec<(SymbolId, Value)>;
type SourceAssumption = (TermId, ExprId, Option<CarriedBindings>);

struct LeanModuleSpool {
    path: PathBuf,
}

impl LeanModuleSpool {
    fn create() -> std::io::Result<(Self, std::fs::File)> {
        for _ in 0..1024 {
            let suffix = NEXT_LEAN_MODULE_SPOOL.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "axeyum-lean-module-{}-{suffix}.lean",
                std::process::id()
            ));
            match std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(file) => return Ok((Self { path }, file)),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => return Err(error),
            }
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "could not allocate a unique Lean module spool",
        ))
    }

    fn read_to_string(&self) -> std::io::Result<String> {
        std::fs::read_to_string(&self.path)
    }
}

impl Drop for LeanModuleSpool {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn spool_compact_lean_module(
    ctx: &ReconstructCtx,
    goal: ExprId,
    proof: ExprId,
    inductives: &[NameId],
) -> Result<LeanModuleSpool, ReconstructError> {
    let (spool, file) = LeanModuleSpool::create()
        .map_err(|error| decline(format!("failed to create Lean module spool: {error}")))?;
    let mut writer = std::io::BufWriter::new(file);
    ctx.kernel
        .write_lean_module_compact_with_inductives(
            &mut writer,
            LEAN_MODULE_THEOREM,
            goal,
            proof,
            inductives,
        )
        .map_err(|error| decline(format!("failed to stream Lean module: {error}")))?;
    writer
        .flush()
        .map_err(|error| decline(format!("failed to flush Lean module spool: {error}")))?;
    Ok(spool)
}

fn decline(detail: impl Into<String>) -> ReconstructError {
    ReconstructError::MalformedStep {
        rule: "bv_positive_universal_instance_set".to_owned(),
        detail: detail.into(),
    }
}

fn trace_reconstruction(
    route: &str,
    stage: &str,
    started: std::time::Instant,
    count: Option<usize>,
) {
    if std::env::var_os("AXEYUM_LEAN_RECON_TRACE").is_none() {
        return;
    }
    let elapsed_ms = started.elapsed().as_secs_f64() * 1_000.0;
    if let Some(count) = count {
        eprintln!(
            "AXEYUM_LEAN_RECON_TRACE|route={route}|stage={stage}|elapsed_ms={elapsed_ms:.3}|count={count}"
        );
    } else {
        eprintln!("AXEYUM_LEAN_RECON_TRACE|route={route}|stage={stage}|elapsed_ms={elapsed_ms:.3}");
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

    fn computational_bv_type(&mut self, width: usize) -> Result<DatatypeInductive, ReconstructError> {
        if let Some(&datatype) = self.computational_bv_value_types.get(&width) {
            return Ok(datatype);
        }
        let name = self.fresh_name(&format!("computational_bv{width}"));
        let bool_ty = self.kernel.const_(self.prelude.bool_, vec![]);
        let datatype = self.kernel.add_datatype_inductive(name, bool_ty, self.one, width)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "computational_quantified_bv_type".to_owned(),
                detail: format!("finite computational-bit datatype did not admit: {error:?}"),
            })?;
        self.computational_bv_value_types.insert(width, datatype);
        Ok(datatype)
    }

    fn computational_bv_literal(&mut self, width: usize, value: u128) -> Result<ExprId, ReconstructError> {
        let datatype = self.computational_bv_type(width)?;
        let mut result = self.kernel.const_(datatype.ctor, vec![]);
        for index in 0..width {
            let bit = self.kernel.const_(
                if (value >> index) & 1 == 1 { self.prelude.bool_true } else { self.prelude.bool_false },
                vec![],
            );
            result = self.kernel.app(result, bit);
        }
        Ok(result)
    }

    fn ensure_computational_bool_ops(
        &mut self,
    ) -> Result<(axeyum_lean_kernel::NameId, axeyum_lean_kernel::NameId), ReconstructError> {
        if let (Some(not), Some(and)) = (self.computational_bool_not, self.computational_bool_and) {
            return Ok((not, and));
        }
        let bool_ty = self.kernel.const_(self.prelude.bool_, vec![]);
        let anon = self.kernel.anon();

        let not_name = self.fresh_name("computational_bool_not");
        let not_ty = self.kernel.pi(anon, bool_ty, bool_ty, BinderInfo::Default);
        let not_arg = self.kernel.bvar(0);
        let not_body = computational_bool_not_value(self, not_arg);
        let not_value = self.kernel.lam(anon, bool_ty, not_body, BinderInfo::Default);
        self.kernel.add_declaration(Declaration::Definition {
            name: not_name,
            uparams: vec![],
            ty: not_ty,
            value: not_value,
            hint: ReducibilityHint::Regular(0),
        }).map_err(|error| ReconstructError::KernelRejected {
            rule: "computational_bool_not".to_owned(),
            detail: format!("computational Bool not did not admit: {error:?}"),
        })?;

        let and_name = self.fresh_name("computational_bool_and");
        let inner_ty = self.kernel.pi(anon, bool_ty, bool_ty, BinderInfo::Default);
        let and_ty = self.kernel.pi(anon, bool_ty, inner_ty, BinderInfo::Default);
        let left = self.kernel.bvar(1);
        let right = self.kernel.bvar(0);
        let and_body = computational_bool_and_value(self, left, right);
        let and_inner = self.kernel.lam(anon, bool_ty, and_body, BinderInfo::Default);
        let and_value = self.kernel.lam(anon, bool_ty, and_inner, BinderInfo::Default);
        self.kernel.add_declaration(Declaration::Definition {
            name: and_name,
            uparams: vec![],
            ty: and_ty,
            value: and_value,
            hint: ReducibilityHint::Regular(0),
        }).map_err(|error| ReconstructError::KernelRejected {
            rule: "computational_bool_and".to_owned(),
            detail: format!("computational Bool and did not admit: {error:?}"),
        })?;
        self.computational_bool_not = Some(not_name);
        self.computational_bool_and = Some(and_name);
        Ok((not_name, and_name))
    }

}

fn computational_bv_projection(
    ctx: &mut ReconstructCtx,
    symbol: SymbolId,
    width: u32,
    index: usize,
) -> Result<ExprId, ReconstructError> {
    let width_usize = usize::try_from(width).expect("u32 fits usize");
    let &(bound_width, value) = ctx.gate_bound_bvs
        .get(&symbol_key(symbol, Sort::BitVec(width)))
        .ok_or_else(|| decline("computational BV binder is unbound"))?;
    if bound_width != width_usize || index >= width_usize {
        return Err(decline("computational BV projection width mismatch"));
    }
    let datatype = ctx.computational_bv_type(width_usize)?;
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let selector = ctx.kernel.datatype_selector(datatype, bool_ty, ctx.one, index);
    Ok(ctx.kernel.app(selector, value))
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

#[derive(Clone, Copy)]
struct EvaluatedProp {
    proposition: ExprId,
    proof: ExprId,
    value: bool,
}

fn false_elim_identity(ctx: &mut ReconstructCtx) -> ExprId {
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let body = ctx.kernel.bvar(0);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, false_, body, BinderInfo::Default)
}

fn refute_and(ctx: &mut ReconstructCtx, left: EvaluatedProp, right: EvaluatedProp) -> ExprId {
    let conjunction = ctx.mk_and(left.proposition, right.proposition);
    let hypothesis_id = fresh_fvar_id(ctx);
    let hypothesis = ctx.kernel.fvar(hypothesis_id);
    let (negative, projected) = if left.value {
        (
            right.proof,
            and_project(ctx, left.proposition, right.proposition, hypothesis, false),
        )
    } else {
        (
            left.proof,
            and_project(ctx, left.proposition, right.proposition, hypothesis, true),
        )
    };
    let contradiction = ctx.kernel.app(negative, projected);
    let body = ctx.kernel.abstract_fvars(contradiction, &[hypothesis_id]);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, conjunction, body, BinderInfo::Default)
}

fn invert_evaluated_prop(ctx: &mut ReconstructCtx, value: EvaluatedProp) -> EvaluatedProp {
    let proposition = ctx.mk_not(value.proposition);
    if value.value {
        let hypothesis_id = fresh_fvar_id(ctx);
        let hypothesis = ctx.kernel.fvar(hypothesis_id);
        let contradiction = ctx.kernel.app(hypothesis, value.proof);
        let body = ctx.kernel.abstract_fvars(contradiction, &[hypothesis_id]);
        let anon = ctx.kernel.anon();
        let proof = ctx.kernel.lam(anon, proposition, body, BinderInfo::Default);
        EvaluatedProp { proposition, proof, value: false }
    } else {
        EvaluatedProp { proposition, proof: value.proof, value: true }
    }
}

fn evaluated_lit(
    ctx: &mut ReconstructCtx,
    nodes: &[EvaluatedProp],
    literal: AigLit,
) -> Result<EvaluatedProp, ReconstructError> {
    let value = *nodes
        .get(literal.node().index())
        .ok_or_else(|| decline("AIG literal references a future evaluated node"))?;
    Ok(if literal.is_inverted() { invert_evaluated_prop(ctx, value) } else { value })
}

fn input_value(
    binding: &axeyum_bv::SymbolBitInput,
    bindings: &BTreeMap<SymbolId, &Value>,
) -> Result<bool, ReconstructError> {
    match bindings.get(&binding.symbol) {
        Some(Value::Bool(value)) if binding.bit_index == 0 => Ok(*value),
        Some(Value::Bv { width, value }) if binding.sort == Sort::BitVec(*width) => {
            Ok((*value >> binding.bit_index) & 1 == 1)
        }
        _ => Err(decline("ground witness AIG input sort mismatch")),
    }
}

fn evaluate_ground_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    bindings: &[(SymbolId, Value)],
) -> Result<EvaluatedProp, ReconstructError> {
    register_bv_widths(ctx, arena, term);
    let lowering = lower_terms(arena, &[term])
        .map_err(|error| decline(format!("AIG witness lowering failed: {error}")))?;
    let bindings = bindings.iter().map(|(s, v)| (*s, v)).collect();
    let mut nodes = Vec::with_capacity(lowering.aig().node_count());
    for (node_id, node) in lowering.aig().nodes() {
        let evaluated = match node {
            AigNode::ConstFalse => EvaluatedProp {
                proposition: ctx.kernel.const_(ctx.prelude.false_, vec![]),
                proof: false_elim_identity(ctx),
                value: false,
            },
            AigNode::Input(input) => {
                let binding = lowering.symbol_inputs().get(input.index())
                    .ok_or_else(|| decline("AIG input lacks a source binding"))?;
                let value = input_value(binding, &bindings)?;
                let proposition = match binding.sort {
                    Sort::Bool => {
                        let witness = *ctx.gate_bound_bools
                            .get(&symbol_key(binding.symbol, Sort::Bool))
                            .ok_or_else(|| decline("Bool witness environment is incomplete"))?;
                        ctx.typed_bool_value_prop(witness)
                    }
                    Sort::BitVec(width) => ctx.typed_bv_projection(
                        &c(symbol_key(binding.symbol, Sort::BitVec(width))),
                        usize::try_from(binding.bit_index).expect("u32 fits usize"),
                    ).ok_or_else(|| decline("typed witness BV projection failed"))?,
                    sort => return Err(decline(format!("unsupported witness AIG input sort {sort:?}"))),
                };
                EvaluatedProp {
                    proposition,
                    proof: if value { ctx.kernel.const_(ctx.prelude.true_intro, vec![]) } else { false_elim_identity(ctx) },
                    value,
                }
            }
            AigNode::And(left, right) => {
                let left = evaluated_lit(ctx, &nodes, left)?;
                let right = evaluated_lit(ctx, &nodes, right)?;
                let proposition = ctx.mk_and(left.proposition, right.proposition);
                let value = left.value && right.value;
                let proof = if value {
                    super::and_intro(ctx, left.proposition, right.proposition, left.proof, right.proof)
                } else {
                    refute_and(ctx, left, right)
                };
                EvaluatedProp { proposition, proof, value }
            }
        };
        debug_assert_eq!(node_id.index(), nodes.len());
        nodes.push(evaluated);
    }
    let root = lowering.roots().first().and_then(|root| root.bits().first()).copied()
        .ok_or_else(|| decline("AIG witness lowering lacks a Boolean root"))?;
    evaluated_lit(ctx, &nodes, root)
}

fn prove_ground_true(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    bindings: &[(SymbolId, Value)],
) -> Result<ExprId, ReconstructError> {
    let evaluated = evaluate_ground_prop(ctx, arena, term, bindings)?;
    if !evaluated.value {
        return Err(decline("certificate witness body evaluates false in Lean lowering"));
    }
    Ok(evaluated.proof)
}

fn computational_bool_not_value(ctx: &mut ReconstructCtx, value: ExprId) -> ExprId {
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let anon = ctx.kernel.anon();
    let motive = ctx.kernel.lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let rec = ctx.kernel.const_(ctx.prelude.bool_rec, vec![ctx.one]);
    let rec = ctx.kernel.app(rec, motive);
    let false_ = ctx.kernel.const_(ctx.prelude.bool_false, vec![]);
    let rec = ctx.kernel.app(rec, false_);
    let true_ = ctx.kernel.const_(ctx.prelude.bool_true, vec![]);
    let rec = ctx.kernel.app(rec, true_);
    ctx.kernel.app(rec, value)
}

fn computational_bool_and_value(ctx: &mut ReconstructCtx, left: ExprId, right: ExprId) -> ExprId {
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let anon = ctx.kernel.anon();
    let motive = ctx.kernel.lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let rec = ctx.kernel.const_(ctx.prelude.bool_rec, vec![ctx.one]);
    let rec = ctx.kernel.app(rec, motive);
    let rec = ctx.kernel.app(rec, right);
    let false_ = ctx.kernel.const_(ctx.prelude.bool_false, vec![]);
    let rec = ctx.kernel.app(rec, false_);
    ctx.kernel.app(rec, left)
}

fn computational_bool_not(
    ctx: &mut ReconstructCtx,
    value: ExprId,
) -> Result<ExprId, ReconstructError> {
    let (not, _) = ctx.ensure_computational_bool_ops()?;
    let function = ctx.kernel.const_(not, vec![]);
    Ok(ctx.kernel.app(function, value))
}

fn computational_bool_and(
    ctx: &mut ReconstructCtx,
    left: ExprId,
    right: ExprId,
) -> Result<ExprId, ReconstructError> {
    let (_, and) = ctx.ensure_computational_bool_ops()?;
    let function = ctx.kernel.const_(and, vec![]);
    let function = ctx.kernel.app(function, left);
    Ok(ctx.kernel.app(function, right))
}

fn computational_aig_lit(
    ctx: &mut ReconstructCtx,
    nodes: &[ExprId],
    literal: AigLit,
) -> Result<ExprId, ReconstructError> {
    let value = *nodes.get(literal.node().index())
        .ok_or_else(|| decline("computational AIG literal references a future node"))?;
    Ok(if literal.is_inverted() {
        computational_bool_not(ctx, value)?
    } else {
        value
    })
}

fn computational_ground_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    let lowering = lower_terms(arena, &[term])
        .map_err(|error| decline(format!("computational AIG lowering failed: {error}")))?;
    let mut nodes = Vec::with_capacity(lowering.aig().node_count());
    let mut gate_lets = Vec::new();
    for (node_id, node) in lowering.aig().nodes() {
        let value = match node {
            AigNode::ConstFalse => ctx.kernel.const_(ctx.prelude.bool_false, vec![]),
            AigNode::Input(input) => {
                let binding = lowering.symbol_inputs().get(input.index())
                    .ok_or_else(|| decline("computational AIG input lacks a source binding"))?;
                match binding.sort {
                    Sort::Bool => *ctx.gate_bound_bools
                        .get(&symbol_key(binding.symbol, Sort::Bool))
                        .ok_or_else(|| decline("computational Bool binder is unbound"))?,
                    Sort::BitVec(width) => computational_bv_projection(
                        ctx,
                        binding.symbol,
                        width,
                        usize::try_from(binding.bit_index).expect("u32 fits usize"),
                    )?,
                    sort => return Err(decline(format!("unsupported computational AIG input sort {sort:?}"))),
                }
            }
            AigNode::And(left, right) => {
                let left = computational_aig_lit(ctx, &nodes, left)?;
                let right = computational_aig_lit(ctx, &nodes, right)?;
                let value = computational_bool_and(ctx, left, right)?;
                let fvar = fresh_fvar_id(ctx);
                let name = ctx.fresh_name("computational_aig_gate");
                gate_lets.push((fvar, name, value));
                ctx.kernel.fvar(fvar)
            }
        };
        debug_assert_eq!(node_id.index(), nodes.len());
        nodes.push(value);
    }
    let root = lowering.roots().first().and_then(|root| root.bits().first()).copied()
        .ok_or_else(|| decline("computational AIG lowering lacks a Boolean root"))?;
    let value = computational_aig_lit(ctx, &nodes, root)?;
    let mut proposition = ctx.typed_bool_value_prop(value);
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    for (fvar, name, value) in gate_lets.into_iter().rev() {
        let body = ctx.kernel.abstract_fvars(proposition, &[fvar]);
        proposition = ctx.kernel.let_(name, bool_ty, value, body);
    }
    Ok(proposition)
}

fn aig_root_prop(
    ctx: &mut ReconstructCtx,
    lowering: &BitLowering,
) -> Result<ExprId, ReconstructError> {
    let mut nodes = Vec::with_capacity(lowering.aig().node_count());
    let mut gate_lets = Vec::new();
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
                let value = ctx.mk_and(left, right);
                let fvar = fresh_fvar_id(ctx);
                let name = ctx.fresh_name("logical_aig_gate");
                gate_lets.push((fvar, name, value));
                ctx.kernel.fvar(fvar)
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
    let mut proposition = aig_lit_prop(ctx, &nodes, root)?;
    let prop = ctx.kernel.sort_zero();
    for (fvar, name, value) in gate_lets.into_iter().rev() {
        let body = ctx.kernel.abstract_fvars(proposition, &[fvar]);
        proposition = ctx.kernel.let_(name, prop, value, body);
    }
    Ok(proposition)
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

fn collect_exists_chain(
    arena: &TermArena,
    mut term: TermId,
) -> Result<(Vec<SymbolId>, TermId), ReconstructError> {
    let mut binders = Vec::new();
    loop {
        match arena.node(term) {
            TermNode::App {
                op: Op::Exists(symbol),
                args,
            } if args.len() == 1 => {
                let sort = arena.symbol(*symbol).1;
                if !matches!(sort, Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)) {
                    return Err(decline(format!(
                        "unsupported existential binder sort {sort:?}"
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
            "existentials must form a direct chain with a quantifier-free body",
        ));
    }
    Ok((binders, term))
}

fn collect_vacuous_exists_forall_chain(
    arena: &TermArena,
    mut term: TermId,
) -> Result<(Vec<SymbolId>, TermId, Vec<SymbolId>, TermId), ReconstructError> {
    let mut existential_binders = Vec::new();
    loop {
        match arena.node(term) {
            TermNode::App {
                op: Op::Exists(symbol),
                args,
            } if args.len() == 1 => {
                let sort = arena.symbol(*symbol).1;
                if !matches!(sort, Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)) {
                    return Err(decline(format!(
                        "unsupported existential binder sort {sort:?}"
                    )));
                }
                existential_binders.push(*symbol);
                term = args[0];
            }
            _ => break,
        }
    }
    if existential_binders.is_empty() {
        return Err(decline("expected a nonempty leading existential block"));
    }
    let universal_term = term;
    let (universal_binders, body) = collect_forall_chain(arena, universal_term)?;
    Ok((
        existential_binders,
        universal_term,
        universal_binders,
        body,
    ))
}

fn universal_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    universal_prop_with_encoding(ctx, arena, term, WitnessLeanEncoding::Logical)
}

fn universal_prop_with_encoding(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    let (binders, body) = collect_forall_chain(arena, term)?;
    register_bv_widths(ctx, arena, body);
    let mut fvars = Vec::with_capacity(binders.len());
    let mut domains = Vec::with_capacity(binders.len());
    for &binder in &binders {
        let id = fresh_fvar_id(ctx);
        let value = ctx.kernel.fvar(id);
        let sort = arena.symbol(binder).1;
        bind_symbol(ctx, binder, sort, value);
        domains.push(binder_domain(ctx, sort, encoding)?);
        fvars.push(id);
    }
    let proposition = match encoding {
        WitnessLeanEncoding::Logical => direct_ground_prop(ctx, arena, body)?,
        WitnessLeanEncoding::Computational => computational_ground_prop(ctx, arena, body)?,
    };
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

fn forall_exists_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    outer: &[SymbolId],
    inner: &[SymbolId],
    antecedent: TermId,
    consequent: TermId,
) -> Result<ExprId, ReconstructError> {
    register_bv_widths(ctx, arena, antecedent);
    register_bv_widths(ctx, arena, consequent);
    let mut fvars = Vec::with_capacity(outer.len());
    let mut domains = Vec::with_capacity(outer.len());
    for &binder in outer {
        let sort = arena.symbol(binder).1;
        let domain = binder_domain(ctx, sort, WitnessLeanEncoding::Logical)?;
        let id = fresh_fvar_id(ctx);
        let variable = ctx.kernel.fvar(id);
        bind_symbol(ctx, binder, sort, variable);
        fvars.push(id);
        domains.push(domain);
    }
    let mut proposition = alternation_exists_suffix_prop(
        ctx,
        arena,
        inner,
        antecedent,
        consequent,
        0,
    )?;
    for &binder in outer.iter().rev() {
        unbind_symbol(ctx, binder, arena.symbol(binder).1);
    }
    proposition = ctx.kernel.abstract_fvars(proposition, &fvars);
    for domain in domains.into_iter().rev() {
        let anon = ctx.kernel.anon();
        proposition = ctx
            .kernel
            .pi(anon, domain, proposition, BinderInfo::Default);
    }
    Ok(proposition)
}

fn alternation_exists_suffix_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    binders: &[SymbolId],
    antecedent: TermId,
    consequent: TermId,
    index: usize,
) -> Result<ExprId, ReconstructError> {
    let Some(&binder) = binders.get(index) else {
        let premise = direct_ground_prop(ctx, arena, antecedent)?;
        let conclusion = direct_ground_prop(ctx, arena, consequent)?;
        let anon = ctx.kernel.anon();
        return Ok(ctx
            .kernel
            .pi(anon, premise, conclusion, BinderInfo::Default));
    };
    let sort = arena.symbol(binder).1;
    let domain = binder_domain(ctx, sort, WitnessLeanEncoding::Logical)?;
    let binder_id = fresh_fvar_id(ctx);
    let binder_variable = ctx.kernel.fvar(binder_id);
    bind_symbol(ctx, binder, sort, binder_variable);
    let suffix = alternation_exists_suffix_prop(
        ctx,
        arena,
        binders,
        antecedent,
        consequent,
        index + 1,
    )?;
    unbind_symbol(ctx, binder, sort);
    let predicate_body = ctx.kernel.abstract_fvars(suffix, &[binder_id]);
    let anon = ctx.kernel.anon();
    let predicate = ctx
        .kernel
        .lam(anon, domain, predicate_body, BinderInfo::Default);
    let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
    let exists = ctx.kernel.app(exists, domain);
    Ok(ctx.kernel.app(exists, predicate))
}

#[derive(Clone, Copy)]
struct VacuousExistsLayer {
    domain: ExprId,
    predicate: ExprId,
    proposition: ExprId,
}

#[derive(Clone, Copy)]
struct AlternationExistsLayer {
    binder: SymbolId,
    sort: Sort,
    witness_id: u64,
    domain: ExprId,
    suffix: ExprId,
    predicate: ExprId,
    proposition: ExprId,
}

fn build_alternation_exists_layers(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    binders: &[SymbolId],
    antecedent: TermId,
    consequent: TermId,
) -> Result<(ExprId, Vec<AlternationExistsLayer>), ReconstructError> {
    let mut pending = Vec::with_capacity(binders.len());
    for &binder in binders {
        let sort = arena.symbol(binder).1;
        let domain = binder_domain(ctx, sort, WitnessLeanEncoding::Logical)?;
        let witness_id = fresh_fvar_id(ctx);
        let witness = ctx.kernel.fvar(witness_id);
        bind_symbol(ctx, binder, sort, witness);
        pending.push((binder, sort, witness_id, domain));
    }

    let premise = direct_ground_prop(ctx, arena, antecedent)?;
    let conclusion = direct_ground_prop(ctx, arena, consequent)?;
    let anon = ctx.kernel.anon();
    let mut suffix = ctx
        .kernel
        .pi(anon, premise, conclusion, BinderInfo::Default);
    let mut layers = Vec::with_capacity(pending.len());
    for &(binder, sort, witness_id, domain) in pending.iter().rev() {
        let predicate_body = ctx.kernel.abstract_fvars(suffix, &[witness_id]);
        let anon = ctx.kernel.anon();
        let predicate = ctx
            .kernel
            .lam(anon, domain, predicate_body, BinderInfo::Default);
        let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
        let exists = ctx.kernel.app(exists, domain);
        let proposition = ctx.kernel.app(exists, predicate);
        layers.push(AlternationExistsLayer {
            binder,
            sort,
            witness_id,
            domain,
            suffix,
            predicate,
            proposition,
        });
        suffix = proposition;
    }
    layers.reverse();
    for &(binder, sort, _, _) in pending.iter().rev() {
        unbind_symbol(ctx, binder, sort);
    }
    Ok((suffix, layers))
}

fn wrap_vacuous_exists_prefix(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    binders: &[SymbolId],
    universal: ExprId,
    encoding: WitnessLeanEncoding,
) -> Result<(ExprId, Vec<VacuousExistsLayer>), ReconstructError> {
    let mut proposition = universal;
    let mut layers = Vec::with_capacity(binders.len());
    for &binder in binders.iter().rev() {
        let domain = binder_domain(ctx, arena.symbol(binder).1, encoding)?;
        let anon = ctx.kernel.anon();
        let predicate =
            ctx.kernel
                .lam(anon, domain, proposition, BinderInfo::Default);
        let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
        let exists = ctx.kernel.app(exists, domain);
        let exists = ctx.kernel.app(exists, predicate);
        layers.push(VacuousExistsLayer {
            domain,
            predicate,
            proposition: exists,
        });
        proposition = exists;
    }
    layers.reverse();
    Ok((proposition, layers))
}

fn exists_elim_false(
    ctx: &mut ReconstructCtx,
    layer: VacuousExistsLayer,
    minor: ExprId,
    major: ExprId,
) -> ExprId {
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let anon = ctx.kernel.anon();
    let motive =
        ctx.kernel
            .lam(anon, layer.proposition, false_, BinderInfo::Default);
    let rec = ctx
        .kernel
        .const_(ctx.prelude.exists_rec, vec![ctx.one]);
    let rec = ctx.kernel.app(rec, layer.domain);
    let rec = ctx.kernel.app(rec, layer.predicate);
    let rec = ctx.kernel.app(rec, motive);
    let rec = ctx.kernel.app(rec, minor);
    ctx.kernel.app(rec, major)
}

#[allow(clippy::too_many_arguments)]
fn refute_vacuous_exists_suffix(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    universal_term: TermId,
    bindings: &[(SymbolId, Value)],
    negative: ExprId,
    encoding: WitnessLeanEncoding,
    layers: &[VacuousExistsLayer],
    index: usize,
    major: ExprId,
) -> Result<ExprId, ReconstructError> {
    let Some(&layer) = layers.get(index) else {
        let source = BvPositiveUniversalSourceInstance {
            assertion: universal_term,
            bindings: bindings.to_vec(),
        };
        let positive =
            apply_instance_with_encoding(ctx, arena, universal_term, major, &source, encoding)?;
        return Ok(ctx.kernel.app(negative, positive));
    };

    let witness_id = fresh_fvar_id(ctx);
    let hypothesis_id = fresh_fvar_id(ctx);
    let hypothesis = ctx.kernel.fvar(hypothesis_id);
    let contradiction = refute_vacuous_exists_suffix(
        ctx,
        arena,
        universal_term,
        bindings,
        negative,
        encoding,
        layers,
        index + 1,
        hypothesis,
    )?;
    let body = ctx
        .kernel
        .abstract_fvars(contradiction, &[witness_id, hypothesis_id]);
    let witness = ctx.kernel.bvar(0);
    let hypothesis_type = ctx.kernel.app(layer.predicate, witness);
    let anon = ctx.kernel.anon();
    let minor = ctx
        .kernel
        .lam(anon, hypothesis_type, body, BinderInfo::Default);
    let minor = ctx
        .kernel
        .lam(anon, layer.domain, minor, BinderInfo::Default);
    Ok(exists_elim_false(ctx, layer, minor, major))
}

#[allow(clippy::too_many_arguments)]
fn refute_alternation_exists_suffix(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    layers: &[AlternationExistsLayer],
    antecedent: TermId,
    consequent: TermId,
    outer_bindings: &[(SymbolId, Value)],
    started: std::time::Instant,
    scoped_binders: &mut Vec<(ExprId, u64)>,
    index: usize,
    major: ExprId,
) -> Result<ExprId, ReconstructError> {
    let Some(&layer) = layers.get(index) else {
        let evaluated = evaluate_ground_prop(ctx, arena, antecedent, outer_bindings)?;
        if !evaluated.value {
            return Err(decline("alternation outer tuple falsifies its antecedent"));
        }
        let consequent_proof = ctx.kernel.app(major, evaluated.proof);
        let (formulas, definitions) = aig_gate_tail(
            arena,
            &[(consequent, Some(outer_bindings.to_vec()))],
        )?;
        let (commands, gate_defs) =
            crate::qfbv_alethe::prove_bit_gate_unsat_alethe(&formulas, definitions)
                .ok_or_else(|| decline("alternation residual emitter declined"))?;
        ctx.bridge = Some(gate_defs);
        ctx.gate_memo.clear();
        trace_reconstruction(
            "bv-alternation",
            "tail-reconstruct-start",
            started,
            Some(commands.len()),
        );
        let proof = reconstruct_gate_tail_with_local_lets(ctx, &commands, &[consequent_proof]);
        trace_reconstruction(
            "bv-alternation",
            "tail-reconstruct-end",
            started,
            Some(commands.len()),
        );
        return proof;
    };
    let binder = layer.binder;
    let sort = layer.sort;
    let domain = layer.domain;
    let witness_id = layer.witness_id;
    let witness = ctx.kernel.fvar(witness_id);
    let witness_name = ctx.kernel.anon();
    ctx.local_ctx.push(LocalDecl {
        fvar: witness_id,
        name: witness_name,
        ty: domain,
        info: BinderInfo::Default,
    });
    bind_symbol(ctx, binder, sort, witness);
    let suffix = layer.suffix;

    let hypothesis_id = fresh_fvar_id(ctx);
    let hypothesis = ctx.kernel.fvar(hypothesis_id);
    let hypothesis_name = ctx.kernel.anon();
    ctx.local_ctx.push(LocalDecl {
        fvar: hypothesis_id,
        name: hypothesis_name,
        ty: suffix,
        info: BinderInfo::Default,
    });
    let contradiction = refute_alternation_exists_suffix(
        ctx,
        arena,
        layers,
        antecedent,
        consequent,
        outer_bindings,
        started,
        scoped_binders,
        index + 1,
        hypothesis,
    )?;
    unbind_symbol(ctx, binder, sort);
    let popped_hypothesis = ctx.local_ctx.pop();
    let popped_witness = ctx.local_ctx.pop();
    debug_assert_eq!(popped_hypothesis.map(|decl| decl.fvar), Some(hypothesis_id));
    debug_assert_eq!(popped_witness.map(|decl| decl.fvar), Some(witness_id));

    let hypothesis_type = ctx.kernel.app(layer.predicate, witness);
    let anon = ctx.kernel.anon();
    let minor = ctx
        .kernel
        .lam(anon, hypothesis_type, contradiction, BinderInfo::Default);
    scoped_binders.push((minor, hypothesis_id));
    let minor = ctx
        .kernel
        .lam(anon, domain, minor, BinderInfo::Default);
    scoped_binders.push((minor, witness_id));
    Ok(exists_elim_false(
        ctx,
        VacuousExistsLayer {
            domain,
            predicate: layer.predicate,
            proposition: layer.proposition,
        },
        minor,
        major,
    ))
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
        TermNode::App {
            op: Op::Exists(_), ..
        } => {
            let (binders, body) = collect_exists_chain(arena, term)?;
            exists_suffix_prop(
                ctx,
                arena,
                &binders,
                body,
                0,
                WitnessLeanEncoding::Logical,
            )
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 && contains_quantifier(arena, args[0]) => {
            let inner = source_prop(ctx, arena, args[0])?;
            Ok(ctx.mk_not(inner))
        }
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
    install_binding_environment_with_encoding(
        ctx,
        arena,
        bindings,
        WitnessLeanEncoding::Logical,
    )
}

fn install_binding_environment_with_encoding(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    bindings: &[(SymbolId, Value)],
    encoding: WitnessLeanEncoding,
) -> Result<(), ReconstructError> {
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    for (symbol, value) in bindings {
        let sort = arena.symbol(*symbol).1;
        let witness = binder_witness(ctx, sort, value, encoding)?;
        bind_symbol(ctx, *symbol, sort, witness);
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum WitnessLeanEncoding {
    Logical,
    Computational,
}

fn binder_domain(
    ctx: &mut ReconstructCtx,
    sort: Sort,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    match sort {
        Sort::Bool => Ok(ctx.kernel.const_(ctx.prelude.bool_, vec![])),
        Sort::BitVec(width @ 1..=MAX_LEAN_BV_WIDTH) => {
            let width = usize::try_from(width).expect("u32 fits usize");
            let datatype = match encoding {
                WitnessLeanEncoding::Logical => ctx.typed_bv_type(width)?,
                WitnessLeanEncoding::Computational => ctx.computational_bv_type(width)?,
            };
            Ok(ctx.kernel.const_(datatype.ind, vec![]))
        }
        _ => Err(decline(format!(
            "unsupported negated-existential binder sort {sort:?}"
        ))),
    }
}

fn binder_witness(
    ctx: &mut ReconstructCtx,
    sort: Sort,
    value: &Value,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    match (sort, value) {
        (Sort::Bool, Value::Bool(value)) => Ok(ctx.kernel.const_(
            if *value {
                ctx.prelude.bool_true
            } else {
                ctx.prelude.bool_false
            },
            vec![],
        )),
        (
            Sort::BitVec(width @ 1..=MAX_LEAN_BV_WIDTH),
            Value::Bv {
                width: carried,
                value,
            },
        ) if width == *carried => {
            let width = usize::try_from(width).expect("u32 fits usize");
            match encoding {
                WitnessLeanEncoding::Logical => ctx.typed_bv_literal(width, *value),
                WitnessLeanEncoding::Computational => ctx.computational_bv_literal(width, *value),
            }
        }
        _ => Err(decline("negated-existential witness sort mismatch")),
    }
}

fn bind_symbol(ctx: &mut ReconstructCtx, symbol: SymbolId, sort: Sort, value: ExprId) {
    match sort {
        Sort::Bool => {
            ctx.gate_bound_bools
                .insert(symbol_key(symbol, Sort::Bool), value);
        }
        Sort::BitVec(width) => {
            ctx.gate_bound_bvs.insert(
                symbol_key(symbol, Sort::BitVec(width)),
                (usize::try_from(width).expect("u32 fits usize"), value),
            );
        }
        _ => unreachable!("binder sort is checked before installation"),
    }
}

fn unbind_symbol(ctx: &mut ReconstructCtx, symbol: SymbolId, sort: Sort) {
    match sort {
        Sort::Bool => {
            ctx.gate_bound_bools
                .remove(&symbol_key(symbol, Sort::Bool));
        }
        Sort::BitVec(width) => {
            ctx.gate_bound_bvs
                .remove(&symbol_key(symbol, Sort::BitVec(width)));
        }
        _ => unreachable!("binder sort is checked before removal"),
    }
}

fn exists_suffix_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    binders: &[SymbolId],
    body: TermId,
    index: usize,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    let Some(&binder) = binders.get(index) else {
        return match encoding {
            WitnessLeanEncoding::Logical => direct_ground_prop(ctx, arena, body),
            WitnessLeanEncoding::Computational => computational_ground_prop(ctx, arena, body),
        };
    };
    let sort = arena.symbol(binder).1;
    let domain = binder_domain(ctx, sort, encoding)?;
    let binder_id = fresh_fvar_id(ctx);
    let binder_variable = ctx.kernel.fvar(binder_id);
    bind_symbol(ctx, binder, sort, binder_variable);
    let suffix = exists_suffix_prop(ctx, arena, binders, body, index + 1, encoding)?;
    unbind_symbol(ctx, binder, sort);
    let predicate_body = ctx.kernel.abstract_fvars(suffix, &[binder_id]);
    let anon = ctx.kernel.anon();
    let predicate = ctx
        .kernel
        .lam(anon, domain, predicate_body, BinderInfo::Default);
    let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
    let exists = ctx.kernel.app(exists, domain);
    Ok(ctx.kernel.app(exists, predicate))
}

fn prove_exists_suffix(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    binders: &[SymbolId],
    body: TermId,
    bindings: &[(SymbolId, Value)],
    index: usize,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    let Some(&binder) = binders.get(index) else {
        return match encoding {
            WitnessLeanEncoding::Logical => prove_ground_true(ctx, arena, body, bindings),
            WitnessLeanEncoding::Computational => {
                Ok(ctx.kernel.const_(ctx.prelude.true_intro, vec![]))
            }
        };
    };
    let sort = arena.symbol(binder).1;
    let domain = binder_domain(ctx, sort, encoding)?;
    let binder_id = fresh_fvar_id(ctx);
    let binder_variable = ctx.kernel.fvar(binder_id);
    bind_symbol(ctx, binder, sort, binder_variable);
    let suffix = exists_suffix_prop(ctx, arena, binders, body, index + 1, encoding)?;
    unbind_symbol(ctx, binder, sort);
    let predicate_body = ctx.kernel.abstract_fvars(suffix, &[binder_id]);
    let anon = ctx.kernel.anon();
    let predicate = ctx
        .kernel
        .lam(anon, domain, predicate_body, BinderInfo::Default);

    let (carried_binder, value) = bindings
        .get(index)
        .ok_or_else(|| decline("negated-existential witness omits a binder"))?;
    if *carried_binder != binder {
        return Err(decline("negated-existential witness binder order mismatch"));
    }
    let witness = binder_witness(ctx, sort, value, encoding)?;
    bind_symbol(ctx, binder, sort, witness);
    let suffix_proof = prove_exists_suffix(
        ctx,
        arena,
        binders,
        body,
        bindings,
        index + 1,
        encoding,
    )?;
    unbind_symbol(ctx, binder, sort);

    let intro = ctx
        .kernel
        .const_(ctx.prelude.exists_intro, vec![ctx.one]);
    let intro = ctx.kernel.app(intro, domain);
    let intro = ctx.kernel.app(intro, predicate);
    let intro = ctx.kernel.app(intro, witness);
    Ok(ctx.kernel.app(intro, suffix_proof))
}

fn apply_instance(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proof: ExprId,
    source: &BvPositiveUniversalSourceInstance,
) -> Result<ExprId, ReconstructError> {
    apply_instance_with_encoding(
        ctx,
        arena,
        term,
        proof,
        source,
        WitnessLeanEncoding::Logical,
    )
}

fn apply_instance_with_encoding(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    mut proof: ExprId,
    source: &BvPositiveUniversalSourceInstance,
    encoding: WitnessLeanEncoding,
) -> Result<ExprId, ReconstructError> {
    let (binders, _) = collect_forall_chain(arena, term)?;
    let bindings = binding_map(source);
    for binder in binders {
        let value = bindings
            .get(&binder)
            .ok_or_else(|| decline("instance omits a universal binder"))?;
        let witness = binder_witness(ctx, arena.symbol(binder).1, value, encoding)?;
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

fn reconstruct_gate_tail_with_local_lets(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
    assumption_proofs: &[ExprId],
) -> Result<ExprId, ReconstructError> {
    reconstruct_gate_tail_with_chunked_local_lets(ctx, commands, assumption_proofs, 4)
}

#[allow(clippy::too_many_lines)]
fn reconstruct_gate_tail_with_chunked_local_lets(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
    assumption_proofs: &[ExprId],
    local_let_chunk: usize,
) -> Result<ExprId, ReconstructError> {
    debug_assert!(local_let_chunk > 0);
    let _ = ctx.em_axiom();
    let mut dependencies = BTreeMap::<String, Vec<String>>::new();
    let mut empty_step = None;
    for command in commands {
        if let AletheCommand::Step {
            id,
            clause,
            premises,
            ..
        } = command
        {
            dependencies.insert(id.clone(), premises.clone());
            if clause.is_empty() {
                empty_step = Some(id.clone());
            }
        }
    }
    let mut live_steps = BTreeSet::new();
    let mut live_stack = empty_step.into_iter().collect::<Vec<_>>();
    while let Some(id) = live_stack.pop() {
        if !live_steps.insert(id.clone()) {
            continue;
        }
        if let Some(premises) = dependencies.get(&id) {
            live_stack.extend(premises.iter().cloned());
        }
    }
    if live_steps.is_empty() {
        return Err(ReconstructError::NoEmptyClause);
    }
    let mut premise_uses = BTreeMap::<String, usize>::new();
    for command in commands {
        if let AletheCommand::Step { id, premises, .. } = command
            && live_steps.contains(id)
        {
            for premise in premises {
                *premise_uses.entry(premise.clone()).or_default() += 1;
            }
        }
    }
    let mut proofs = assumption_proofs.iter();
    let mut env = BTreeMap::new();
    let mut lets = Vec::new();
    let mut reconstructed_steps = 0_usize;
    for command in commands {
        match command {
            AletheCommand::Assume { id, clause } => {
                let proof = *proofs
                    .next()
                    .ok_or_else(|| decline("Alethe tail has too many assumptions"))?;
                if !live_steps.contains(id) {
                    continue;
                }
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
                if !live_steps.contains(id) {
                    continue;
                }
                let Some(mut recovered) =
                    reconstruct_bitwise_step(ctx, rule, clause, premises, &env)?
                else {
                    continue;
                };
                if clause.is_empty() {
                    if proofs.next().is_some() {
                        return Err(decline("unused source-derived assumptions"));
                    }
                    let proof = check_false_prop(ctx, recovered.proof)?;
                    let fvars = lets
                        .iter()
                        .map(|(fvar, _, _, _)| *fvar)
                        .collect::<Vec<_>>();
                    let mut proof = ctx.kernel.abstract_fvars(proof, &fvars);
                    for (index, (_, name, ty, value)) in lets.into_iter().enumerate().rev() {
                        let ty = ctx.kernel.abstract_fvars(ty, &fvars[..index]);
                        let value = ctx.kernel.abstract_fvars(value, &fvars[..index]);
                        proof = ctx.kernel.let_(name, ty, value, proof);
                    }
                    return Ok(proof);
                }
                let should_alias = premise_uses.get(id).copied().unwrap_or_default() > 1
                    || reconstructed_steps.is_multiple_of(local_let_chunk);
                reconstructed_steps += 1;
                if should_alias {
                    let ty = ctx.clause_to_prop(clause);
                    let fvar = fresh_fvar_id(ctx);
                    let name = ctx.fresh_name("alternation_clause");
                    lets.push((fvar, name, ty, recovered.proof));
                    recovered.proof = ctx.kernel.fvar(fvar);
                }
                env.insert(id.clone(), recovered);
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

#[derive(Clone, Copy)]
struct PairedExistsLayer {
    positive_binder: SymbolId,
    negative_binder: SymbolId,
    aligned_binder: SymbolId,
    sort: Sort,
    witness_id: u64,
    domain: ExprId,
    positive_predicate: ExprId,
    positive_proposition: ExprId,
    negative_predicate: ExprId,
    negative_proposition: ExprId,
}

fn paired_ground_conjunction_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
) -> Result<ExprId, ReconstructError> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        let left = paired_ground_conjunction_prop(ctx, arena, *left)?;
        let right = paired_ground_conjunction_prop(ctx, arena, *right)?;
        return Ok(ctx.mk_and(left, right));
    }
    direct_ground_prop(ctx, arena, term)
}

fn paired_source_prop(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    existential: TermId,
    existential_prop: ExprId,
) -> Result<ExprId, ReconstructError> {
    if term == existential {
        return Ok(existential_prop);
    }
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 && contains_quantifier(arena, term) => {
            let left = paired_source_prop(
                ctx,
                arena,
                args[0],
                existential,
                existential_prop,
            )?;
            let right = paired_source_prop(
                ctx,
                arena,
                args[1],
                existential,
                existential_prop,
            )?;
            Ok(ctx.mk_and(left, right))
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 && contains_quantifier(arena, args[0]) => {
            let inner = paired_source_prop(
                ctx,
                arena,
                args[0],
                existential,
                existential_prop,
            )?;
            Ok(ctx.mk_not(inner))
        }
        _ => source_prop(ctx, arena, term),
    }
}

#[allow(clippy::too_many_arguments)]
fn project_paired_source_conjunction(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proof: ExprId,
    existential: TermId,
    existential_prop: ExprId,
    out: &mut BTreeMap<TermId, ExprId>,
) -> Result<(), ReconstructError> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        let left_prop =
            paired_source_prop(ctx, arena, *left, existential, existential_prop)?;
        let right_prop =
            paired_source_prop(ctx, arena, *right, existential, existential_prop)?;
        let left_proof = and_project(ctx, left_prop, right_prop, proof, true);
        let right_proof = and_project(ctx, left_prop, right_prop, proof, false);
        project_paired_source_conjunction(
            ctx,
            arena,
            *left,
            left_proof,
            existential,
            existential_prop,
            out,
        )?;
        return project_paired_source_conjunction(
            ctx,
            arena,
            *right,
            right_proof,
            existential,
            existential_prop,
            out,
        );
    }
    out.insert(term, proof);
    Ok(())
}

fn project_ground_conjunction(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proof: ExprId,
    out: &mut BTreeMap<TermId, ExprId>,
) -> Result<(), ReconstructError> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        let left_prop = direct_ground_prop(ctx, arena, *left)?;
        let right_prop = direct_ground_prop(ctx, arena, *right)?;
        let left_proof = and_project(ctx, left_prop, right_prop, proof, true);
        let right_proof = and_project(ctx, left_prop, right_prop, proof, false);
        project_ground_conjunction(ctx, arena, *left, left_proof, out)?;
        return project_ground_conjunction(ctx, arena, *right, right_proof, out);
    }
    out.insert(term, proof);
    Ok(())
}

fn rebuild_paired_source_conjunction(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proofs: &BTreeMap<TermId, ExprId>,
    existential: TermId,
    existential_prop: ExprId,
) -> Result<ExprId, ReconstructError> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        let left_prop =
            paired_source_prop(ctx, arena, *left, existential, existential_prop)?;
        let right_prop =
            paired_source_prop(ctx, arena, *right, existential, existential_prop)?;
        let left_proof = rebuild_paired_source_conjunction(
            ctx,
            arena,
            *left,
            proofs,
            existential,
            existential_prop,
        )?;
        let right_proof = rebuild_paired_source_conjunction(
            ctx,
            arena,
            *right,
            proofs,
            existential,
            existential_prop,
        )?;
        return Ok(and_intro(
            ctx,
            left_prop,
            right_prop,
            left_proof,
            right_proof,
        ));
    }
    proofs
        .get(&term)
        .copied()
        .ok_or_else(|| decline("paired-existential conjunction proof is missing a source leaf"))
}

fn rebuild_ground_conjunction(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    proofs: &BTreeMap<TermId, ExprId>,
) -> Result<ExprId, ReconstructError> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        let left_prop = direct_ground_prop(ctx, arena, *left)?;
        let right_prop = direct_ground_prop(ctx, arena, *right)?;
        let left_proof = rebuild_ground_conjunction(ctx, arena, *left, proofs)?;
        let right_proof = rebuild_ground_conjunction(ctx, arena, *right, proofs)?;
        return Ok(and_intro(
            ctx,
            left_prop,
            right_prop,
            left_proof,
            right_proof,
        ));
    }
    proofs
        .get(&term)
        .copied()
        .ok_or_else(|| decline("paired-existential body proof is missing a conjunct"))
}

fn build_paired_exists_layers(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    scratch: &TermArena,
    admitted: &crate::quant_bv_paired_exists_cert::AdmittedPairedExistentials,
    aligned_binders: &[(SymbolId, Sort)],
) -> Result<Vec<PairedExistsLayer>, ReconstructError> {
    if admitted.positive_binders.len() != aligned_binders.len() {
        return Err(decline("paired-existential alpha alignment length changed"));
    }
    let mut pending = Vec::with_capacity(aligned_binders.len());
    for (((&positive, &negative), &(aligned, aligned_sort)), index) in admitted
        .positive_binders
        .iter()
        .zip(&admitted.negative_binders)
        .zip(aligned_binders)
        .zip(0..)
    {
        let sort = arena.symbol(positive).1;
        if sort != arena.symbol(negative).1 || sort != aligned_sort {
            return Err(decline(format!(
                "paired-existential alpha alignment sort changed at binder {index}"
            )));
        }
        let domain = binder_domain(ctx, sort, WitnessLeanEncoding::Logical)?;
        let witness_id = fresh_fvar_id(ctx);
        let witness = ctx.kernel.fvar(witness_id);
        bind_symbol(ctx, positive, sort, witness);
        bind_symbol(ctx, negative, sort, witness);
        bind_symbol(ctx, aligned, sort, witness);
        pending.push((positive, negative, aligned, sort, witness_id, domain));
    }

    let mut positive_suffix =
        paired_ground_conjunction_prop(ctx, arena, admitted.positive_body)?;
    let mut negative_suffix =
        paired_ground_conjunction_prop(ctx, arena, admitted.negative_body)?;
    let mut layers = Vec::with_capacity(pending.len());
    for &(positive, negative, aligned, sort, witness_id, domain) in pending.iter().rev() {
        let anon = ctx.kernel.anon();
        let positive_body = ctx.kernel.abstract_fvars(positive_suffix, &[witness_id]);
        let positive_predicate =
            ctx.kernel
                .lam(anon, domain, positive_body, BinderInfo::Default);
        let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
        let exists = ctx.kernel.app(exists, domain);
        let positive_proposition = ctx.kernel.app(exists, positive_predicate);

        let negative_body = ctx.kernel.abstract_fvars(negative_suffix, &[witness_id]);
        let negative_predicate =
            ctx.kernel
                .lam(anon, domain, negative_body, BinderInfo::Default);
        let exists = ctx.kernel.const_(ctx.prelude.exists_, vec![ctx.one]);
        let exists = ctx.kernel.app(exists, domain);
        let negative_proposition = ctx.kernel.app(exists, negative_predicate);
        layers.push(PairedExistsLayer {
            positive_binder: positive,
            negative_binder: negative,
            aligned_binder: aligned,
            sort,
            witness_id,
            domain,
            positive_predicate,
            positive_proposition,
            negative_predicate,
            negative_proposition,
        });
        positive_suffix = positive_proposition;
        negative_suffix = negative_proposition;
    }
    layers.reverse();
    for &(positive, negative, aligned, sort, _, _) in pending.iter().rev() {
        unbind_symbol(ctx, aligned, sort);
        unbind_symbol(ctx, negative, sort);
        unbind_symbol(ctx, positive, sort);
    }
    register_bv_widths(ctx, scratch, admitted.positive_body);
    register_bv_widths(ctx, scratch, admitted.negative_body);
    Ok(layers)
}

fn introduce_paired_negative_exists(
    ctx: &mut ReconstructCtx,
    layers: &[PairedExistsLayer],
    mut proof: ExprId,
) -> ExprId {
    for layer in layers.iter().rev() {
        let intro = ctx
            .kernel
            .const_(ctx.prelude.exists_intro, vec![ctx.one]);
        let intro = ctx.kernel.app(intro, layer.domain);
        let intro = ctx.kernel.app(intro, layer.negative_predicate);
        let witness = ctx.kernel.fvar(layer.witness_id);
        let intro = ctx.kernel.app(intro, witness);
        proof = ctx.kernel.app(intro, proof);
    }
    proof
}

fn prove_paired_consequent(
    ctx: &mut ReconstructCtx,
    replay: &mut crate::quant_bv_paired_exists_cert::InstantiatedPairedTransfer,
    certificate: &BvPairedExistentialTransferCertificate,
    consequent_source: TermId,
    available_proofs: &BTreeMap<TermId, ExprId>,
) -> Result<ExprId, ReconstructError> {
    let obligation = certificate
        .obligations
        .iter()
        .find(|obligation| obligation.consequent == consequent_source)
        .ok_or_else(|| decline("paired-existential transfer obligation is missing"))?;
    let assumption_sources = match &obligation.justification {
        BvPairedExistentialTransferJustification::SignedAddMonotonicity { strong, bound } => {
            vec![*strong, *bound]
        }
        BvPairedExistentialTransferJustification::QfProof { assumptions, .. } => {
            assumptions.clone()
        }
    };
    let consequent = *replay
        .consequents
        .get(&consequent_source)
        .ok_or_else(|| decline("paired-existential consequent lost its alpha instance"))?;
    let target = direct_ground_prop(ctx, &replay.arena, consequent)?;
    let not_consequent = replay
        .arena
        .not(consequent)
        .map_err(|error| decline(format!("failed to negate paired consequent: {error}")))?;

    let mut tail = Vec::with_capacity(assumption_sources.len() + 1);
    let mut assumption_proofs = Vec::with_capacity(assumption_sources.len() + 1);
    for source in assumption_sources {
        let instantiated = *replay
            .available
            .get(&source)
            .ok_or_else(|| decline("paired-existential assumption lost its alpha instance"))?;
        tail.push((instantiated, None));
        assumption_proofs.push(
            available_proofs
                .get(&source)
                .copied()
                .ok_or_else(|| decline("paired-existential assumption lacks a source proof"))?,
        );
    }
    tail.push((not_consequent, None));
    let not_target = ctx.mk_not(target);
    let not_target_id = fresh_fvar_id(ctx);
    assumption_proofs.push(ctx.kernel.fvar(not_target_id));

    let (formulas, definitions) = aig_gate_tail(&replay.arena, &tail)?;
    let (commands, gate_defs) =
        crate::qfbv_alethe::prove_bit_gate_unsat_alethe(&formulas, definitions)
            .ok_or_else(|| decline("paired-existential implication emitter declined"))?;
    ctx.bridge = Some(gate_defs);
    ctx.gate_memo.clear();
    ctx.begin_gate_prop_aliases();
    let contradiction = reconstruct_bitwise_cps_tail(ctx, &commands, &assumption_proofs)?;
    let contradiction = ctx.finish_gate_prop_aliases(contradiction);
    let body = ctx.kernel.abstract_fvars(contradiction, &[not_target_id]);
    let anon = ctx.kernel.anon();
    let double_negation = ctx
        .kernel
        .lam(anon, not_target, body, BinderInfo::Default);
    Ok(double_negation_elim(ctx, target, double_negation))
}

#[allow(clippy::too_many_arguments)]
fn refute_paired_exists_suffix(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    replay: &mut crate::quant_bv_paired_exists_cert::InstantiatedPairedTransfer,
    admitted: &crate::quant_bv_paired_exists_cert::AdmittedPairedExistentials,
    certificate: &BvPairedExistentialTransferCertificate,
    layers: &[PairedExistsLayer],
    premise_proofs: &BTreeMap<TermId, ExprId>,
    negative_source: ExprId,
    negative_inner: TermId,
    scoped_binders: &mut Vec<(ExprId, u64)>,
    index: usize,
    major: ExprId,
) -> Result<ExprId, ReconstructError> {
    let Some(&layer) = layers.get(index) else {
        let mut available_proofs = premise_proofs.clone();
        project_ground_conjunction(
            ctx,
            arena,
            admitted.positive_body,
            major,
            &mut available_proofs,
        )?;
        let available_instances = replay
            .available
            .iter()
            .map(|(&source, &instantiated)| (instantiated, source))
            .collect::<BTreeMap<_, _>>();
        let mut consequent_proofs = BTreeMap::new();
        for &source in &admitted.negative_conjuncts {
            let instantiated = replay.consequents[&source];
            let proof = if let Some(available_source) = available_instances.get(&instantiated) {
                available_proofs[available_source]
            } else {
                prove_paired_consequent(
                    ctx,
                    replay,
                    certificate,
                    source,
                    &available_proofs,
                )?
            };
            consequent_proofs.insert(source, proof);
        }
        let negative_body = rebuild_ground_conjunction(
            ctx,
            arena,
            admitted.negative_body,
            &consequent_proofs,
        )?;
        let negative_exists = introduce_paired_negative_exists(ctx, layers, negative_body);
        let mut negative_inner_proofs = premise_proofs.clone();
        negative_inner_proofs.insert(certificate.negative_existential, negative_exists);
        let negative_existential_prop = layers
            .first()
            .map(|layer| layer.negative_proposition)
            .ok_or_else(|| decline("paired-existential layer stack is empty"))?;
        let negative_inner_proof = rebuild_paired_source_conjunction(
            ctx,
            arena,
            negative_inner,
            &negative_inner_proofs,
            certificate.negative_existential,
            negative_existential_prop,
        )?;
        return Ok(ctx.kernel.app(negative_source, negative_inner_proof));
    };

    let witness = ctx.kernel.fvar(layer.witness_id);
    bind_symbol(ctx, layer.positive_binder, layer.sort, witness);
    bind_symbol(ctx, layer.negative_binder, layer.sort, witness);
    bind_symbol(ctx, layer.aligned_binder, layer.sort, witness);
    let hypothesis_id = fresh_fvar_id(ctx);
    let hypothesis = ctx.kernel.fvar(hypothesis_id);
    let contradiction = refute_paired_exists_suffix(
        ctx,
        arena,
        replay,
        admitted,
        certificate,
        layers,
        premise_proofs,
        negative_source,
        negative_inner,
        scoped_binders,
        index + 1,
        hypothesis,
    )?;
    unbind_symbol(ctx, layer.aligned_binder, layer.sort);
    unbind_symbol(ctx, layer.negative_binder, layer.sort);
    unbind_symbol(ctx, layer.positive_binder, layer.sort);

    let hypothesis_type = ctx.kernel.app(layer.positive_predicate, witness);
    let anon = ctx.kernel.anon();
    let minor = ctx
        .kernel
        .lam(anon, hypothesis_type, contradiction, BinderInfo::Default);
    scoped_binders.push((minor, hypothesis_id));
    let minor = ctx
        .kernel
        .lam(anon, layer.domain, minor, BinderInfo::Default);
    scoped_binders.push((minor, layer.witness_id));
    Ok(exists_elim_false(
        ctx,
        VacuousExistsLayer {
            domain: layer.domain,
            predicate: layer.positive_predicate,
            proposition: layer.positive_proposition,
        },
        minor,
        major,
    ))
}


/// Cheap structural classification used by the public proof-fragment scanner.
pub(crate) fn bv_paired_existential_transfer_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().copied().any(|positive| {
        assertions.iter().copied().any(|negative| {
            let Some((positive_exists, negative_exists)) =
                crate::quant_bv_paired_exists_cert::paired_existential_terms(
                    arena, positive, negative,
                )
            else {
                return false;
            };
            crate::quant_bv_paired_exists_cert::admitted_paired_existentials(
                arena,
                positive,
                negative,
                positive_exists,
                negative_exists,
            )
            .is_some_and(|admitted| {
                admitted
                    .positive_binders
                    .iter()
                    .chain(&admitted.negative_binders)
                    .all(|&binder| {
                        matches!(
                            arena.symbol(binder).1,
                            Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
                        )
                    })
            })
        })
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

/// Cheap structural classification for ADR-0127's source-bound conjunctive
/// universal-instance route.
pub(crate) fn bv_conjunctive_universal_instance_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().any(|&assertion| {
        crate::quant_bv_conjunctive_cert::conjunctive_universals(arena, assertion)
            .into_iter()
            .any(|universal| {
                universal != assertion
                    && crate::quant_bv_conjunctive_cert::admitted_conjunctive_universal(
                        arena, assertion, universal,
                    )
                    .is_some_and(|admitted| {
                        admitted.binders.iter().all(|&binder| {
                            matches!(
                                arena.symbol(binder).1,
                                Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
                            )
                        })
                    })
            })
    })
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

/// Cheap structural classification for ADR-0126's genuine typed Lean route.
pub(crate) fn negated_existential_witness_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().any(|&assertion| {
        crate::quant_negated_exists_cert::admitted_negated_existential(arena, assertion)
            .is_some_and(|(binders, _)| {
                binders.iter().all(|&binder| {
                    matches!(
                        arena.symbol(binder).1,
                        Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
                    )
                })
            })
    })
}

/// Cheap structural classification for an evaluator-replayed closed Bool/BV
/// universal counterexample.
pub(crate) fn bv_closed_universal_counterexample_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().any(|&assertion| {
        collect_forall_chain(arena, assertion)
            .is_ok_and(|(binders, body)| {
                let bound = binders.into_iter().collect::<BTreeSet<_>>();
                let mut seen = BTreeSet::new();
                let mut stack = vec![body];
                while let Some(term) = stack.pop() {
                    if !seen.insert(term) {
                        continue;
                    }
                    match arena.node(term) {
                        TermNode::Symbol(symbol) if !bound.contains(symbol) => return false,
                        TermNode::App { args, .. } => stack.extend(args.iter().copied()),
                        _ => {}
                    }
                }
                true
            })
    })
}

/// Cheap structural classification for an ADR-0128 closed Bool/BV universal
/// counterexample below a syntactically vacuous existential prefix.
pub(crate) fn bv_vacuous_exists_universal_counterexample_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().any(|&assertion| {
        crate::quant_vacuous_exists_counterexample_cert::admitted_vacuous_exists_universal(
            arena, assertion,
        )
        .is_some()
            && collect_vacuous_exists_forall_chain(arena, assertion).is_ok()
    })
}

/// Cheap structural classification for ADR-0124/0125's closed Bool/BV
/// `forall+ exists+` counterexample route.
pub(crate) fn bv_alternation_counterexample_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    assertions.iter().any(|&assertion| {
        crate::quant_bv_alternation_cert::admitted_alternation(arena, assertion).is_some_and(
            |admitted| {
                admitted.outer.iter().chain(&admitted.inner).all(|&binder| {
                    matches!(
                        arena.symbol(binder).1,
                        Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
                    )
                })
            },
        )
    })
}

/// Reconstructs ADR-0129 paired-existential witness transfer from the two
/// untouched source assertions. The positive witness is eliminated with
/// genuine `Exists.rec`, every transferred `QF_BV` consequence is regenerated as
/// a bit-level proof, and the same typed witness is introduced into the
/// negative existential with `Exists.intro`.
///
/// # Errors
///
/// Returns [`ReconstructError`] if certificate replay fails, the admitted
/// source shape exceeds the typed Lean boundary, an implication proof cannot be
/// regenerated, or the scoped final proof does not kernel-check to `False`.
pub fn reconstruct_bv_paired_existential_transfer_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPairedExistentialTransferCertificate,
) -> Result<String, ReconstructError> {
    const RECONSTRUCTION_STACK_BYTES: usize = 64 * 1024 * 1024;
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("axeyum-adr0129-lean".to_owned())
            .stack_size(RECONSTRUCTION_STACK_BYTES)
            .spawn_scoped(scope, || {
                reconstruct_bv_paired_existential_transfer_to_lean_module_impl(
                    arena,
                    assertions,
                    certificate,
                )
            })
            .map_err(|error| decline(format!("failed to start reconstruction worker: {error}")))?;
        worker
            .join()
            .map_err(|_| decline("paired-existential reconstruction worker panicked"))?
    })
}

#[allow(clippy::too_many_lines)]
fn reconstruct_bv_paired_existential_transfer_to_lean_module_impl(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPairedExistentialTransferCertificate,
) -> Result<String, ReconstructError> {
    if !check_bv_paired_existential_transfer(arena, assertions, certificate)
        .map_err(|error| decline(format!("certificate replay failed: {error}")))?
    {
        return Err(decline("invalid ADR-0129 certificate"));
    }
    let admitted = crate::quant_bv_paired_exists_cert::admitted_paired_existentials(
        arena,
        certificate.positive_assertion,
        certificate.negative_assertion,
        certificate.positive_existential,
        certificate.negative_existential,
    )
    .ok_or_else(|| decline("certificate assertions lost their paired-existential shape"))?;
    let mut replay = crate::quant_bv_paired_exists_cert::instantiate_transfer_terms(
        arena,
        certificate.positive_assertion,
        certificate.negative_assertion,
        &admitted,
    )
    .map_err(|error| decline(format!("alpha-aligned replay failed: {error}")))?;
    let negative_inner = match arena.node(certificate.negative_assertion) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => args[0],
        _ => return Err(decline("negative source lost its outer negation")),
    };

    let mut ctx = ReconstructCtx::new();
    ctx.typed_bv_gates = true;
    register_bv_widths(&mut ctx, arena, certificate.positive_assertion);
    register_bv_widths(&mut ctx, arena, certificate.negative_assertion);
    let layers = build_paired_exists_layers(
        &mut ctx,
        arena,
        &replay.arena,
        &admitted,
        &replay.aligned_binders,
    )?;
    let outer_layer = layers
        .first()
        .ok_or_else(|| decline("paired-existential layer stack is empty"))?;
    let positive_prop = paired_source_prop(
        &mut ctx,
        arena,
        certificate.positive_assertion,
        certificate.positive_existential,
        outer_layer.positive_proposition,
    )?;
    let negative_prop = paired_source_prop(
        &mut ctx,
        arena,
        certificate.negative_assertion,
        certificate.negative_existential,
        outer_layer.negative_proposition,
    )?;
    let positive_source = fresh_axiom(&mut ctx, positive_prop, "bv-paired-exists-positive")?;
    let negative_source = fresh_axiom(&mut ctx, negative_prop, "bv-paired-exists-negative")?;

    let mut positive_leaves = BTreeMap::new();
    project_paired_source_conjunction(
        &mut ctx,
        arena,
        certificate.positive_assertion,
        positive_source,
        certificate.positive_existential,
        outer_layer.positive_proposition,
        &mut positive_leaves,
    )?;
    let positive_exists = positive_leaves
        .get(&certificate.positive_existential)
        .copied()
        .ok_or_else(|| decline("positive source projection lost its existential leaf"))?;
    let premise_proofs = admitted
        .premises
        .iter()
        .map(|&premise| {
            positive_leaves
                .get(&premise)
                .copied()
                .map(|proof| (premise, proof))
                .ok_or_else(|| decline("positive source projection lost a shared premise"))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;

    ctx.defer_open_step_checks = true;
    let mut scoped_binders = Vec::with_capacity(layers.len() * 2);
    let open_proof = refute_paired_exists_suffix(
        &mut ctx,
        arena,
        &mut replay,
        &admitted,
        certificate,
        &layers,
        &premise_proofs,
        negative_source,
        negative_inner,
        &mut scoped_binders,
        0,
        positive_exists,
    )?;
    let (proof, inferred) = ctx
        .kernel
        .infer_and_close_scoped_fvars(open_proof, &scoped_binders)
        .map_err(|error| ReconstructError::KernelRejected {
            rule: "bv_paired_exists_scoped_closure".to_owned(),
            detail: format!("infer failed: {error:?}"),
        })?;
    ctx.defer_open_step_checks = false;
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    if !ctx.kernel.def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "bv_paired_exists_scoped_closure".to_owned(),
            detail: "scoped paired-existential proof did not infer to False".to_owned(),
        });
    }
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    let mut inductives = ctx
        .bv_value_types
        .values()
        .map(|datatype| datatype.ind)
        .collect::<Vec<_>>();
    inductives.push(ctx.prelude.bool_);
    let spool = spool_compact_lean_module(&ctx, false_, proof, &inductives)?;
    ctx.kernel.release_transient_tables_for_export();
    drop(ctx);
    let module = spool
        .read_to_string()
        .map_err(|error| decline(format!("failed to read paired Lean module spool: {error}")))?;
    Ok(module)
}

/// Reconstructs a concrete Bool/BV counterexample to one closed universal as a
/// genuine typed source application followed by a kernel-checked AIG refutation.
///
/// # Errors
///
/// Returns [`ReconstructError`] when certificate replay fails, the source leaves
/// the Bool/BV typed encoding, or the carried body does not reduce to false.
pub fn reconstruct_bv_closed_universal_counterexample_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &ClosedUniversalCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    if !check_closed_universal_counterexample(arena, assertions, certificate) {
        return Err(decline("invalid closed-universal counterexample certificate"));
    }
    let (binders, body) = collect_forall_chain(arena, certificate.assertion)?;
    if binders.len() != certificate.bindings.len() {
        return Err(decline("closed-universal counterexample omits a binder"));
    }

    let mut ctx = ReconstructCtx::new();
    ctx.typed_bv_gates = true;
    register_bv_widths(&mut ctx, arena, body);
    let proposition = universal_prop(&mut ctx, arena, certificate.assertion)?;
    let source = fresh_axiom(&mut ctx, proposition, "closed-bv-universal-source")?;
    let instance = BvPositiveUniversalSourceInstance {
        assertion: certificate.assertion,
        bindings: certificate.bindings.clone(),
    };
    let positive = apply_instance(
        &mut ctx,
        arena,
        certificate.assertion,
        source,
        &instance,
    )?;
    install_binding_environment(&mut ctx, arena, &certificate.bindings)?;
    let evaluated = evaluate_ground_prop(&mut ctx, arena, body, &certificate.bindings)?;
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    if evaluated.value {
        return Err(decline("counterexample body evaluates true in Lean lowering"));
    }
    let positive = check_against(
        &mut ctx,
        "closed_bv_universal_instance",
        positive,
        evaluated.proposition,
    )?;
    let proof = ctx.kernel.app(evaluated.proof, positive);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

/// Reconstructs an ADR-0128 Bool/BV universal counterexample below a vacuous
/// existential prefix by eliminating the untouched source existentials and
/// applying the surviving universal to the exact carried values.
///
/// # Errors
///
/// Returns [`ReconstructError`] when certificate replay fails, the source leaves
/// the typed Bool/BV encoding, existential vacuity is lost, or the final
/// `Exists.rec`/universal application does not kernel-check to `False`.
pub fn reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &VacuousExistsUniversalCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    const RECONSTRUCTION_STACK_BYTES: usize = 64 * 1024 * 1024;
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("axeyum-adr0128-lean".to_owned())
            .stack_size(RECONSTRUCTION_STACK_BYTES)
            .spawn_scoped(scope, || {
                reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module_impl(
                    arena,
                    assertions,
                    certificate,
                )
            })
            .map_err(|error| decline(format!("failed to start reconstruction worker: {error}")))?;
        worker
            .join()
            .map_err(|_| decline("vacuous-existential reconstruction worker panicked"))?
    })
}

fn reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module_impl(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &VacuousExistsUniversalCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    if !check_vacuous_exists_universal_counterexample(arena, assertions, certificate) {
        return Err(decline(
            "invalid vacuous-existential universal counterexample certificate",
        ));
    }
    let (existential_binders, universal_term, universal_binders, body) =
        collect_vacuous_exists_forall_chain(arena, certificate.assertion)?;
    if universal_binders.len() != certificate.bindings.len() {
        return Err(decline(
            "vacuous-existential counterexample omits a universal binder",
        ));
    }

    let body_lowering = lower_terms(arena, &[body])
        .map_err(|error| decline(format!("counterexample encoding selection failed: {error}")))?;
    let encoding = if body_lowering.aig().node_count() > COMPUTATIONAL_WITNESS_AIG_THRESHOLD {
        WitnessLeanEncoding::Computational
    } else {
        WitnessLeanEncoding::Logical
    };

    let mut ctx = ReconstructCtx::new();
    ctx.typed_bv_gates = true;
    register_bv_widths(&mut ctx, arena, body);
    let universal = universal_prop_with_encoding(&mut ctx, arena, universal_term, encoding)?;
    let (source_prop, layers) = wrap_vacuous_exists_prefix(
        &mut ctx,
        arena,
        &existential_binders,
        universal,
        encoding,
    )?;
    let source = fresh_axiom(
        &mut ctx,
        source_prop,
        "vacuous-exists-bv-universal-source",
    )?;

    install_binding_environment_with_encoding(
        &mut ctx,
        arena,
        &certificate.bindings,
        encoding,
    )?;
    let negative = match encoding {
        WitnessLeanEncoding::Logical => {
            let evaluated =
                evaluate_ground_prop(&mut ctx, arena, body, &certificate.bindings)?;
            if evaluated.value {
                return Err(decline(
                    "vacuous-existential counterexample body evaluates true in Lean lowering",
                ));
            }
            evaluated.proof
        }
        WitnessLeanEncoding::Computational => {
            // The independent ADR-0128 checker already evaluated the exact
            // source body to false.  The final kernel application reduces the
            // source-instantiated computational proposition itself to `False`;
            // rebuilding a second alpha-equivalent gate-let chain here would
            // force an unnecessary quadratic definitional-equality walk.
            false_elim_identity(&mut ctx)
        }
    };
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    let proof = refute_vacuous_exists_suffix(
        &mut ctx,
        arena,
        universal_term,
        &certificate.bindings,
        negative,
        encoding,
        &layers,
        0,
        source,
    )?;
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

/// Reconstructs an ADR-0124/0125 source-bound counterexample to a closed
/// `forall+ exists+` Bool/BV assertion. The exact outer tuple is applied to the
/// untouched theorem, every existential is eliminated by `Exists.rec`, and a
/// regenerated bit-level proof refutes the matrix for arbitrary inner values.
///
/// # Errors
///
/// Returns [`ReconstructError`] when certificate replay fails, a binder exceeds
/// the typed Lean encoding, the residual emitter declines, or the final proof
/// is not accepted as `False` by the in-tree kernel.
pub fn reconstruct_bv_alternation_counterexample_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvAlternationCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    const RECONSTRUCTION_STACK_BYTES: usize = 64 * 1024 * 1024;
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("axeyum-adr0124-lean".to_owned())
            .stack_size(RECONSTRUCTION_STACK_BYTES)
            .spawn_scoped(scope, || {
                reconstruct_bv_alternation_counterexample_to_lean_module_impl(
                    arena,
                    assertions,
                    certificate,
                )
            })
            .map_err(|error| decline(format!("failed to start reconstruction worker: {error}")))?;
        worker
            .join()
            .map_err(|_| decline("BV alternation reconstruction worker panicked"))?
    })
}

fn reconstruct_bv_alternation_counterexample_to_lean_module_impl(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvAlternationCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    let started = std::time::Instant::now();
    trace_reconstruction("bv-alternation", "start", started, None);
    if !check_bv_alternation_counterexample(arena, assertions, certificate)
        .map_err(|error| decline(format!("certificate replay failed: {error}")))?
    {
        return Err(decline("invalid ADR-0124/0125 certificate"));
    }
    trace_reconstruction("bv-alternation", "certificate-checked", started, None);
    let admitted = crate::quant_bv_alternation_cert::admitted_alternation(
        arena,
        certificate.assertion,
    )
    .ok_or_else(|| decline("certificate assertion lost its alternation shape"))?;
    if admitted.outer.iter().chain(&admitted.inner).any(|&binder| {
        !matches!(
            arena.symbol(binder).1,
            Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
        )
    }) {
        return Err(decline("alternation binder exceeds the Lean BV width cap"));
    }
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(admitted.body)
    else {
        return Err(decline("alternation body lost its implication shape"));
    };
    let [antecedent, consequent] = &**args else {
        return Err(decline("malformed alternation implication"));
    };
    if *antecedent != admitted.antecedent {
        return Err(decline("alternation antecedent changed after admission"));
    }

    let mut ctx = ReconstructCtx::new();
    ctx.typed_bv_gates = true;
    register_bv_widths(&mut ctx, arena, admitted.body);
    let proposition = forall_exists_prop(
        &mut ctx,
        arena,
        &admitted.outer,
        &admitted.inner,
        *antecedent,
        *consequent,
    )?;
    trace_reconstruction("bv-alternation", "source-built", started, None);
    let source = fresh_axiom(&mut ctx, proposition, "bv-alternation-source")?;
    let mut instantiated = source;
    for (&binder, (carried, value)) in admitted.outer.iter().zip(&certificate.outer_bindings) {
        if binder != *carried {
            return Err(decline("alternation outer binding order mismatch"));
        }
        let witness = binder_witness(
            &mut ctx,
            arena.symbol(binder).1,
            value,
            WitnessLeanEncoding::Logical,
        )?;
        instantiated = ctx.kernel.app(instantiated, witness);
    }
    install_binding_environment(&mut ctx, arena, &certificate.outer_bindings)?;
    let (_instantiated_suffix, layers) = build_alternation_exists_layers(
        &mut ctx,
        arena,
        &admitted.inner,
        *antecedent,
        *consequent,
    )?;
    ctx.defer_open_step_checks = true;
    let mut scoped_binders = Vec::with_capacity(layers.len() * 2);
    let open_proof = refute_alternation_exists_suffix(
        &mut ctx,
        arena,
        &layers,
        *antecedent,
        *consequent,
        &certificate.outer_bindings,
        started,
        &mut scoped_binders,
        0,
        instantiated,
    )?;
    let (proof, inferred) = ctx
        .kernel
        .infer_and_close_scoped_fvars(open_proof, &scoped_binders)
        .map_err(|error| ReconstructError::KernelRejected {
            rule: "bv_alternation_scoped_closure".to_owned(),
            detail: format!("infer failed: {error:?}"),
        })?;
    ctx.defer_open_step_checks = false;
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    if !ctx.kernel.def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "bv_alternation_scoped_closure".to_owned(),
            detail: "scoped reconstruction did not infer to False".to_owned(),
        });
    }
    trace_reconstruction("bv-alternation", "kernel-closed", started, None);
    finish_bv_alternation_module(ctx, proof, started)
}

fn finish_bv_alternation_module(
    mut ctx: ReconstructCtx,
    proof: ExprId,
    started: std::time::Instant,
) -> Result<String, ReconstructError> {
    ctx.gate_bound_bools.clear();
    ctx.gate_bound_bvs.clear();
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let mut inductives = ctx
        .bv_value_types
        .values()
        .map(|datatype| datatype.ind)
        .collect::<Vec<_>>();
    inductives.push(ctx.prelude.bool_);

    let spool = spool_compact_lean_module(&ctx, false_, proof, &inductives)?;
    let spool_bytes = std::fs::metadata(&spool.path)
        .ok()
        .and_then(|metadata| usize::try_from(metadata.len()).ok());
    trace_reconstruction("bv-alternation", "module-spooled", started, spool_bytes);

    ctx.kernel.release_transient_tables_for_export();
    drop(ctx);
    let module = spool
        .read_to_string()
        .map_err(|error| decline(format!("failed to read Lean module spool: {error}")))?;
    trace_reconstruction("bv-alternation", "module-read", started, Some(module.len()));
    Ok(module)
}

/// Reconstructs an evaluator-replayed negated-existential witness as a genuine
/// typed `Exists.intro` proof, then closes it against the untouched source
/// assertion `Not (Exists ...)`.
///
/// # Errors
///
/// Returns [`ReconstructError`] when replay fails, the source is outside the
/// Bool/BV Lean encoding, AIG lowering/evaluation diverges from the carried
/// witness, or the final proof does not kernel-check to `False`.
pub fn reconstruct_negated_existential_witness_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &NegatedExistentialWitnessCertificate,
) -> Result<String, ReconstructError> {
    if !check_negated_existential_witness(arena, assertions, certificate) {
        return Err(decline("invalid ADR-0126 certificate"));
    }
    let (binders, body) =
        crate::quant_negated_exists_cert::admitted_negated_existential(
            arena,
            certificate.assertion,
        )
        .ok_or_else(|| decline("certificate assertion lost its negated existential shape"))?;
    if binders.iter().any(|&binder| {
        !matches!(
            arena.symbol(binder).1,
            Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
        )
    }) {
        return Err(decline("existential binder exceeds the Lean BV width cap"));
    }

    let witness_lowering = lower_terms(arena, &[body])
        .map_err(|error| decline(format!("witness encoding selection failed: {error}")))?;
    let encoding = if witness_lowering.aig().node_count() > COMPUTATIONAL_WITNESS_AIG_THRESHOLD {
        WitnessLeanEncoding::Computational
    } else {
        WitnessLeanEncoding::Logical
    };
    let mut ctx = ReconstructCtx::new();
    ctx.typed_bv_gates = true;
    register_bv_widths(&mut ctx, arena, body);
    let existential = exists_suffix_prop(&mut ctx, arena, &binders, body, 0, encoding)?;
    let negated = ctx.mk_not(existential);
    let source = fresh_axiom(&mut ctx, negated, "negated-existential-source")?;
    let witness = prove_exists_suffix(
        &mut ctx,
        arena,
        &binders,
        body,
        &certificate.bindings,
        0,
        encoding,
    )?;
    let proof = ctx.kernel.app(source, witness);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
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

/// Reconstructs an ADR-0127 source-bound conjunctive universal instance to a
/// kernel-checked Lean module whose only hypothesis is the untouched source
/// assertion.
///
/// The source conjunction is projected structurally, the selected universal is
/// applied to the certificate's concrete Bool/BV values, and the resulting
/// ground assumptions enter the compact CPS RUP boundary. The residual proof is
/// rechecked before this independent proof reconstruction begins.
///
/// # Errors
///
/// Returns [`ReconstructError`] when certificate replay fails, the source no
/// longer has the admitted conjunctive shape, a typed source instance cannot be
/// derived, or the compact bit-level proof is rejected by the kernel.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_bv_conjunctive_universal_instance_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvConjunctiveUniversalInstanceCertificate,
) -> Result<String, ReconstructError> {
    const RECONSTRUCTION_STACK_BYTES: usize = 64 * 1024 * 1024;
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("axeyum-adr0127-lean".to_owned())
            .stack_size(RECONSTRUCTION_STACK_BYTES)
            .spawn_scoped(scope, || {
                reconstruct_bv_conjunctive_universal_instance_to_lean_module_impl(
                    arena,
                    assertions,
                    certificate,
                )
            })
            .map_err(|error| decline(format!("failed to start reconstruction worker: {error}")))?;
        worker
            .join()
            .map_err(|_| decline("conjunctive-instance reconstruction worker panicked"))?
    })
}

#[allow(clippy::too_many_lines)]
fn reconstruct_bv_conjunctive_universal_instance_to_lean_module_impl(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvConjunctiveUniversalInstanceCertificate,
) -> Result<String, ReconstructError> {
    let started = std::time::Instant::now();
    trace_reconstruction("bv-conjunctive", "start", started, None);
    if !check_bv_conjunctive_universal_instance(arena, assertions, certificate)
        .map_err(|error| decline(format!("certificate replay failed: {error}")))?
    {
        return Err(decline("invalid ADR-0127 certificate"));
    }
    trace_reconstruction("bv-conjunctive", "certificate-checked", started, None);
    let admitted = crate::quant_bv_conjunctive_cert::admitted_conjunctive_universal(
        arena,
        certificate.assertion,
        certificate.universal,
    )
    .ok_or_else(|| decline("certificate source lost its conjunctive universal"))?;
    if admitted.binders.iter().any(|&binder| {
        !matches!(
            arena.symbol(binder).1,
            Sort::Bool | Sort::BitVec(1..=MAX_LEAN_BV_WIDTH)
        )
    }) {
        return Err(decline("universal binder exceeds the Lean BV width cap"));
    }
    let Some((scratch, residual)) =
        crate::quant_bv_conjunctive_cert::instantiate_conjunctive_universal(
            arena,
            certificate.assertion,
            certificate.universal,
            &admitted,
            &certificate.bindings,
        )
        .map_err(|error| decline(format!("residual rebuild failed: {error}")))?
    else {
        return Err(decline("certificate does not rebuild"));
    };
    trace_reconstruction("bv-conjunctive", "residual-rebuilt", started, None);

    let mut ctx = ReconstructCtx::new();
    ctx.bridge = Some(BTreeMap::new());
    ctx.typed_bv_gates = true;
    let proposition = source_prop(&mut ctx, &scratch, certificate.assertion)?;
    let source_proof = fresh_axiom(&mut ctx, proposition, "quant-bv-conjunctive-source")?;
    let source = BvPositiveUniversalSourceInstance {
        assertion: certificate.assertion,
        bindings: certificate.bindings.clone(),
    };
    let mut source_assumptions = Vec::new();
    collect_instance_assumptions(
        &mut ctx,
        &scratch,
        certificate.assertion,
        residual,
        source_proof,
        &source,
        &mut source_assumptions,
    )?;
    trace_reconstruction(
        "bv-conjunctive",
        "source-assumptions-built",
        started,
        Some(source_assumptions.len()),
    );

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
            "quant_bv_conjunctive_source_instance",
            proof,
            expected,
        )?);
        tail_terms.push((term, bindings));
    }

    let (formulas, definitions) = aig_gate_tail(&scratch, &tail_terms)?;
    let (commands, gate_defs) =
        crate::qfbv_alethe::prove_bit_gate_unsat_alethe(&formulas, definitions)
            .ok_or_else(|| decline("propositional residual emitter declined"))?;
    trace_reconstruction(
        "bv-conjunctive",
        "tail-emitted",
        started,
        Some(commands.len()),
    );
    ctx.bridge = Some(gate_defs);
    ctx.gate_memo.clear();
    ctx.defer_open_step_checks = true;
    ctx.closed_aliases.cps_clauses = true;
    ctx.begin_global_gate_prop_aliases();
    let proof = reconstruct_bitwise_cps_tail(&mut ctx, &commands, &assumptions)?;
    trace_reconstruction(
        "bv-conjunctive",
        "tail-reconstructed",
        started,
        Some(commands.len()),
    );
    ctx.finish_global_gate_prop_aliases()?;
    ctx.closed_aliases.cps_clauses = false;
    ctx.defer_open_step_checks = false;
    require_infers_false(&mut ctx, proof)?;
    trace_reconstruction("bv-conjunctive", "kernel-closed", started, None);

    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let mut inductives = ctx
        .bv_value_types
        .values()
        .map(|datatype| datatype.ind)
        .collect::<Vec<_>>();
    inductives.push(ctx.prelude.bool_);
    let spool = spool_compact_lean_module(&ctx, false_, proof, &inductives)?;
    let spool_bytes = std::fs::metadata(&spool.path)
        .ok()
        .and_then(|metadata| usize::try_from(metadata.len()).ok());
    trace_reconstruction("bv-conjunctive", "module-spooled", started, spool_bytes);
    ctx.kernel.release_transient_tables_for_export();
    drop(ctx);
    let module = spool.read_to_string().map_err(|error| {
        decline(format!(
            "failed to read conjunctive-instance Lean module spool: {error}"
        ))
    })?;
    trace_reconstruction("bv-conjunctive", "module-read", started, Some(module.len()));
    Ok(module)
}
