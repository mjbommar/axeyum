//! Definedness-aware reflection for the typed straight-line LLVM scalar slice.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::error::Error;
use std::fmt;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};

use super::syntax::{
    BinaryOpcode, BlockId, CastOpcode, Function, IntPredicate, Intrinsic, Operand, ParseError,
    ScalarCfg, ScalarInstructionKind, SemanticFlag, SourceSpan, TerminatorKind, parse_function,
    parse_scalar_cfg, parse_scalar_instruction,
};

const MAX_ACYCLIC_BLOCK_EXECUTIONS: usize = 4_096;

/// One reflected scalar value and the condition under which it is well-defined.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefinedValue {
    /// Modular `QF_BV`/Boolean value term.
    pub value: TermId,
    /// Boolean LLVM-definedness predicate for the supported scalar slice.
    pub defined: TermId,
    /// LLVM integer width (`1` is represented by Axeyum `Bool`).
    pub width: u32,
}

/// A checked reflection in its owned arena.
#[derive(Debug)]
pub struct CheckedReflected {
    /// Arena owning every term in the reflection.
    pub arena: TermArena,
    /// `(name, symbol, width)` for source parameters.
    pub params: Vec<(String, SymbolId, u32)>,
    /// Every typed SSA binding, including its definedness predicate.
    pub env: HashMap<String, DefinedValue>,
    /// Returned value and whole-function definedness.
    pub result: DefinedValue,
}

/// A checked acyclic CFG reflection in its owned arena.
#[derive(Debug)]
pub struct CheckedCfgReflected {
    /// Arena owning every term in the reflection.
    pub arena: TermArena,
    /// `(name, symbol, width)` for source parameters.
    pub params: Vec<(String, SymbolId, u32)>,
    /// Joined return value and the condition under which it is defined.
    pub result: DefinedValue,
}

impl CheckedReflected {
    /// The checked SSA value for a named parameter.
    #[must_use]
    pub fn param(&self, name: &str) -> Option<DefinedValue> {
        self.env.get(name).copied()
    }
}

/// Stable checked-reflection failure classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReflectErrorKind {
    /// Structured syntax or typed-instruction parsing failed.
    Syntax,
    /// More than one basic block requires the later typed CFG slice.
    UnsupportedControlFlow,
    /// The checked CFG contains a cycle and belongs on the transition-system path.
    CyclicControlFlow,
    /// Acyclic path expansion exceeds the fixed checked-execution bound.
    ExecutionLimit,
    /// A parameter or constant width is outside the scalar `QF_BV` slice.
    UnsupportedWidth,
    /// Caller parameter count differs from the LLVM signature.
    ParameterCount,
    /// Caller parameter sort differs from the LLVM signature.
    ParameterSort,
    /// An SSA value was referenced before definition.
    UndefinedValue,
    /// An SSA destination was defined more than once.
    DuplicateValue,
    /// An operand or result width conflicts with its typed declaration.
    WidthMismatch,
    /// No scalar return, or more than one return, was present.
    InvalidReturn,
    /// Axeyum IR construction rejected an operation.
    IrConstruction,
}

/// Located checked-reflection failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectError {
    kind: ReflectErrorKind,
    span: Option<SourceSpan>,
    detail: String,
}

impl ReflectError {
    /// Stable error class.
    #[must_use]
    pub fn kind(&self) -> ReflectErrorKind {
        self.kind
    }

    /// Source span when the failure belongs to textual LLVM input.
    #[must_use]
    pub fn span(&self) -> Option<SourceSpan> {
        self.span
    }
}

impl fmt::Display for ReflectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(span) = self.span {
            write!(f, "{} at {}:{}", self.detail, span.line, span.column)
        } else {
            f.write_str(&self.detail)
        }
    }
}

impl Error for ReflectError {}

impl From<ParseError> for ReflectError {
    fn from(error: ParseError) -> Self {
        Self {
            kind: ReflectErrorKind::Syntax,
            span: Some(error.span()),
            detail: error.to_string(),
        }
    }
}

/// Reflect exactly one straight-line scalar function into a fresh arena.
///
/// # Errors
///
/// Returns a located error for unsupported/malformed syntax, parameter/sort
/// mismatch, undefined SSA references, or rejected IR construction.
pub fn reflect_scalar_checked(ll: &str) -> Result<CheckedReflected, ReflectError> {
    let function = parse_function(ll)?;
    let mut arena = TermArena::new();
    let mut params = Vec::with_capacity(function.params.len());
    let mut terms = Vec::with_capacity(function.params.len());
    for parameter in &function.params {
        let width = parse_width(&parameter.ty, parameter.span)?;
        let sort = sort_for_width(width);
        let symbol = arena
            .declare(&parameter.name, sort)
            .map_err(|error| ir_error(parameter.span, &error.to_string()))?;
        params.push((parameter.name.clone(), symbol, width));
        terms.push(arena.var(symbol));
    }
    let (result, env) = reflect_parsed_into(&mut arena, &terms, &function)?;
    Ok(CheckedReflected {
        arena,
        params,
        env,
        result,
    })
}

/// Reflect exactly one straight-line scalar function into an existing arena.
///
/// The i-th supplied term binds the i-th LLVM parameter. The result retains an
/// explicit predicate for poison and immediate-undefined-behavior obligations.
///
/// # Errors
///
/// Returns [`ReflectError`] when parsing, binding, or lowering fails.
pub fn reflect_scalar_into_checked(
    arena: &mut TermArena,
    params: &[TermId],
    ll: &str,
) -> Result<DefinedValue, ReflectError> {
    let function = parse_function(ll)?;
    reflect_parsed_into(arena, params, &function).map(|(result, _)| result)
}

/// Reflect one validated acyclic scalar CFG into a fresh arena.
///
/// The modular value on a path where `result.defined` is false is a
/// deterministic placeholder, not an LLVM result. Callers must prove or assume
/// definedness before using the value as executable semantics.
///
/// # Errors
///
/// Returns a located error for malformed syntax, duplicate/non-dominating SSA,
/// cycles, excessive path expansion, parameter mismatch, or rejected IR
/// construction.
pub fn reflect_cfg_checked(ll: &str) -> Result<CheckedCfgReflected, ReflectError> {
    let function = parse_function(ll)?;
    let cfg = parse_scalar_cfg(&function)?;
    let mut arena = TermArena::new();
    let mut params = Vec::with_capacity(function.params.len());
    let mut terms = Vec::with_capacity(function.params.len());
    for parameter in &function.params {
        let width = parse_width(&parameter.ty, parameter.span)?;
        let symbol = arena
            .declare(&parameter.name, sort_for_width(width))
            .map_err(|error| ir_error(parameter.span, &error.to_string()))?;
        params.push((parameter.name.clone(), symbol, width));
        terms.push(arena.var(symbol));
    }
    let result = reflect_cfg_parsed_into(&mut arena, &terms, &function, &cfg)?;
    Ok(CheckedCfgReflected {
        arena,
        params,
        result,
    })
}

/// Reflect one validated acyclic scalar CFG into an existing arena.
///
/// # Errors
///
/// Returns [`ReflectError`] when parsing, graph admission, parameter binding,
/// or lowering fails.
pub fn reflect_cfg_into_checked(
    arena: &mut TermArena,
    params: &[TermId],
    ll: &str,
) -> Result<DefinedValue, ReflectError> {
    let function = parse_function(ll)?;
    let cfg = parse_scalar_cfg(&function)?;
    reflect_cfg_parsed_into(arena, params, &function, &cfg)
}

fn reflect_cfg_parsed_into(
    arena: &mut TermArena,
    params: &[TermId],
    function: &Function,
    cfg: &ScalarCfg,
) -> Result<DefinedValue, ReflectError> {
    if params.len() != function.params.len() {
        return Err(ReflectError {
            kind: ReflectErrorKind::ParameterCount,
            span: Some(function.span),
            detail: format!(
                "parameter count mismatch: LLVM declares {}, caller supplied {}",
                function.params.len(),
                params.len()
            ),
        });
    }
    validate_cfg_for_execution(function, cfg)?;

    let always = arena.bool_const(true);
    let mut env = HashMap::new();
    for (parameter, term) in function.params.iter().zip(params.iter().copied()) {
        let width = parse_width(&parameter.ty, parameter.span)?;
        let expected = sort_for_width(width);
        let actual = arena.sort_of(term);
        if actual != expected {
            return Err(ReflectError {
                kind: ReflectErrorKind::ParameterSort,
                span: Some(parameter.span),
                detail: format!(
                    "parameter `%{}` expects {expected:?}, caller supplied {actual:?}",
                    parameter.name
                ),
            });
        }
        env.insert(
            parameter.name.clone(),
            DefinedValue {
                value: term,
                defined: always,
                width,
            },
        );
    }
    execute_cfg_block(arena, cfg, &cfg.entry, None, env, always)
}

fn validate_cfg_for_execution(function: &Function, cfg: &ScalarCfg) -> Result<(), ReflectError> {
    let mut definitions = BTreeMap::<String, SourceSpan>::new();
    for parameter in &function.params {
        insert_definition(&mut definitions, &parameter.name, parameter.span)?;
    }
    for block in &cfg.blocks {
        for phi in &block.phis {
            insert_definition(&mut definitions, &phi.dest, phi.span)?;
        }
        for instruction in &block.instructions {
            let dest = instruction
                .kind
                .destination()
                .expect("CFG body instructions are assignments");
            insert_definition(&mut definitions, dest, instruction.span)?;
        }
    }

    let mut colors = BTreeMap::<BlockId, u8>::new();
    for block in &cfg.blocks {
        detect_cycle(cfg, &block.id, &mut colors)?;
    }

    let mut reachable = BTreeSet::<BlockId>::new();
    collect_reachable(cfg, &cfg.entry, &mut reachable);
    if reachable.len() != cfg.blocks.len() {
        return Err(ReflectError {
            kind: ReflectErrorKind::UnsupportedControlFlow,
            span: Some(function.span),
            detail: "checked CFG execution requires every block to be reachable from entry"
                .to_owned(),
        });
    }

    let executions = count_block_executions(cfg, &cfg.entry, 0)?;
    if executions > MAX_ACYCLIC_BLOCK_EXECUTIONS {
        return Err(ReflectError {
            kind: ReflectErrorKind::ExecutionLimit,
            span: Some(function.span),
            detail: format!(
                "checked CFG expands to {executions} block executions; limit is {MAX_ACYCLIC_BLOCK_EXECUTIONS}"
            ),
        });
    }
    Ok(())
}

fn insert_definition(
    definitions: &mut BTreeMap<String, SourceSpan>,
    name: &str,
    span: SourceSpan,
) -> Result<(), ReflectError> {
    if definitions.insert(name.to_owned(), span).is_some() {
        return Err(ReflectError {
            kind: ReflectErrorKind::DuplicateValue,
            span: Some(span),
            detail: format!("duplicate SSA definition `%{name}`"),
        });
    }
    Ok(())
}

fn detect_cycle(
    cfg: &ScalarCfg,
    block: &BlockId,
    colors: &mut BTreeMap<BlockId, u8>,
) -> Result<(), ReflectError> {
    match colors.get(block).copied() {
        Some(2) => return Ok(()),
        Some(1) => {
            let source = cfg_block(cfg, block);
            return Err(ReflectError {
                kind: ReflectErrorKind::CyclicControlFlow,
                span: Some(source.terminator.span),
                detail: "cyclic LLVM CFG belongs on the TransitionSystem path".to_owned(),
            });
        }
        _ => {}
    }
    colors.insert(block.clone(), 1);
    for successor in &cfg_block(cfg, block).successors {
        detect_cycle(cfg, successor, colors)?;
    }
    colors.insert(block.clone(), 2);
    Ok(())
}

fn collect_reachable(cfg: &ScalarCfg, block: &BlockId, seen: &mut BTreeSet<BlockId>) {
    if !seen.insert(block.clone()) {
        return;
    }
    for successor in &cfg_block(cfg, block).successors {
        collect_reachable(cfg, successor, seen);
    }
}

fn count_block_executions(
    cfg: &ScalarCfg,
    block: &BlockId,
    accumulated: usize,
) -> Result<usize, ReflectError> {
    let next = accumulated.saturating_add(1);
    if next > MAX_ACYCLIC_BLOCK_EXECUTIONS {
        return Ok(next);
    }
    let source = cfg_block(cfg, block);
    let mut count = next;
    for target in terminator_targets(&source.terminator.kind) {
        count = count_block_executions(cfg, target, count)?;
        if count > MAX_ACYCLIC_BLOCK_EXECUTIONS {
            break;
        }
    }
    Ok(count)
}

fn terminator_targets(kind: &TerminatorKind) -> Vec<&BlockId> {
    match kind {
        TerminatorKind::Return { .. } | TerminatorKind::Unreachable => Vec::new(),
        TerminatorKind::Branch { target } => vec![target],
        TerminatorKind::CondBranch {
            true_target,
            false_target,
            ..
        } => vec![true_target, false_target],
        TerminatorKind::Switch {
            default_target,
            cases,
            ..
        } => std::iter::once(default_target)
            .chain(cases.iter().map(|case| &case.target))
            .collect(),
    }
}

fn cfg_block<'a>(cfg: &'a ScalarCfg, id: &BlockId) -> &'a super::syntax::CfgBlock {
    cfg.blocks
        .iter()
        .find(|block| &block.id == id)
        .expect("validated CFG target exists")
}

fn execute_cfg_block(
    arena: &mut TermArena,
    cfg: &ScalarCfg,
    block_id: &BlockId,
    predecessor: Option<&BlockId>,
    mut env: HashMap<String, DefinedValue>,
    mut execution_defined: TermId,
) -> Result<DefinedValue, ReflectError> {
    let block = cfg_block(cfg, block_id);
    let before_phis = env.clone();
    let mut phi_values = Vec::with_capacity(block.phis.len());
    for phi in &block.phis {
        let predecessor = predecessor.ok_or_else(|| ReflectError {
            kind: ReflectErrorKind::UndefinedValue,
            span: Some(phi.span),
            detail: "entry block cannot select a PHI incoming".to_owned(),
        })?;
        let incoming = phi
            .incomings
            .iter()
            .find(|incoming| &incoming.predecessor == predecessor)
            .expect("validated PHI has one incoming for every predecessor");
        let value = resolve(arena, &before_phis, &incoming.value, phi.width, phi.span)?;
        phi_values.push((phi.dest.clone(), value));
    }
    for (dest, value) in phi_values {
        env.insert(dest, value);
    }

    for instruction in &block.instructions {
        let (dest, value, immediate) =
            lower_assignment(arena, &env, instruction.kind.clone(), instruction.span)?;
        execution_defined = bool_and(arena, execution_defined, immediate, instruction.span)?;
        env.insert(dest, value);
    }

    execute_terminator(arena, cfg, block_id, block, env, execution_defined)
}

fn execute_terminator(
    arena: &mut TermArena,
    cfg: &ScalarCfg,
    block_id: &BlockId,
    block: &super::syntax::CfgBlock,
    env: HashMap<String, DefinedValue>,
    execution_defined: TermId,
) -> Result<DefinedValue, ReflectError> {
    match &block.terminator.kind {
        TerminatorKind::Return { width, value } => {
            let returned = resolve(arena, &env, value, *width, block.terminator.span)?;
            let defined = bool_and(
                arena,
                execution_defined,
                returned.defined,
                block.terminator.span,
            )?;
            Ok(DefinedValue {
                defined,
                ..returned
            })
        }
        TerminatorKind::Branch { target } => {
            execute_cfg_block(arena, cfg, target, Some(block_id), env, execution_defined)
        }
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } => {
            let condition = resolve(arena, &env, condition, 1, block.terminator.span)?;
            let when_true = execute_cfg_block(
                arena,
                cfg,
                true_target,
                Some(block_id),
                env.clone(),
                execution_defined,
            )?;
            let when_false = execute_cfg_block(
                arena,
                cfg,
                false_target,
                Some(block_id),
                env,
                execution_defined,
            )?;
            join_selected(
                arena,
                condition,
                when_true,
                when_false,
                block.terminator.span,
            )
        }
        TerminatorKind::Switch {
            width,
            value,
            default_target,
            cases,
        } => {
            let scrutinee = resolve(arena, &env, value, *width, block.terminator.span)?;
            let mut joined = execute_cfg_block(
                arena,
                cfg,
                default_target,
                Some(block_id),
                env.clone(),
                execution_defined,
            )?;
            for case in cases.iter().rev() {
                let case_result = execute_cfg_block(
                    arena,
                    cfg,
                    &case.target,
                    Some(block_id),
                    env.clone(),
                    execution_defined,
                )?;
                let constant = scalar_constant(arena, *width, case.value, block.terminator.span)?;
                let matches = arena
                    .eq(scrutinee.value, constant)
                    .map_err(|error| ir_error(block.terminator.span, &error.to_string()))?;
                let condition = DefinedValue {
                    value: matches,
                    defined: arena.bool_const(true),
                    width: 1,
                };
                joined =
                    join_selected(arena, condition, case_result, joined, block.terminator.span)?;
            }
            joined.defined = bool_and(
                arena,
                scrutinee.defined,
                joined.defined,
                block.terminator.span,
            )?;
            Ok(joined)
        }
        TerminatorKind::Unreachable => Ok(DefinedValue {
            value: scalar_constant(arena, cfg.return_width, 0, block.terminator.span)?,
            defined: arena.bool_const(false),
            width: cfg.return_width,
        }),
    }
}

fn join_selected(
    arena: &mut TermArena,
    condition: DefinedValue,
    when_true: DefinedValue,
    when_false: DefinedValue,
    span: SourceSpan,
) -> Result<DefinedValue, ReflectError> {
    if when_true.width != when_false.width {
        return Err(ReflectError {
            kind: ReflectErrorKind::InvalidReturn,
            span: Some(span),
            detail: "control-flow arms return different widths".to_owned(),
        });
    }
    let value = arena
        .ite(condition.value, when_true.value, when_false.value)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let selected_defined = arena
        .ite(condition.value, when_true.defined, when_false.defined)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let defined = bool_and(arena, condition.defined, selected_defined, span)?;
    Ok(DefinedValue {
        value,
        defined,
        width: when_true.width,
    })
}

fn scalar_constant(
    arena: &mut TermArena,
    width: u32,
    value: u128,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if width == 1 {
        Ok(arena.bool_const(value != 0))
    } else {
        arena
            .bv_const(width, value)
            .map_err(|error| ir_error(span, &error.to_string()))
    }
}

fn reflect_parsed_into(
    arena: &mut TermArena,
    params: &[TermId],
    function: &Function,
) -> Result<(DefinedValue, HashMap<String, DefinedValue>), ReflectError> {
    if params.len() != function.params.len() {
        return Err(ReflectError {
            kind: ReflectErrorKind::ParameterCount,
            span: Some(function.span),
            detail: format!(
                "parameter count mismatch: LLVM declares {}, caller supplied {}",
                function.params.len(),
                params.len()
            ),
        });
    }
    if function.blocks.len() != 1 {
        return Err(ReflectError {
            kind: ReflectErrorKind::UnsupportedControlFlow,
            span: Some(function.span),
            detail: "checked scalar reflection requires exactly one basic block".to_owned(),
        });
    }

    let always = arena.bool_const(true);
    let mut env = HashMap::new();
    for (parameter, term) in function.params.iter().zip(params.iter().copied()) {
        let width = parse_width(&parameter.ty, parameter.span)?;
        let expected = sort_for_width(width);
        let actual = arena.sort_of(term);
        if actual != expected {
            return Err(ReflectError {
                kind: ReflectErrorKind::ParameterSort,
                span: Some(parameter.span),
                detail: format!(
                    "parameter `%{}` expects {expected:?}, caller supplied {actual:?}",
                    parameter.name
                ),
            });
        }
        env.insert(
            parameter.name.clone(),
            DefinedValue {
                value: term,
                defined: always,
                width,
            },
        );
    }

    let mut execution_defined = always;
    let mut result = None;
    for instruction in &function.blocks[0].instructions {
        if result.is_some() {
            return Err(ReflectError {
                kind: ReflectErrorKind::InvalidReturn,
                span: Some(instruction.span),
                detail: "instruction appears after scalar return".to_owned(),
            });
        }
        let typed = parse_scalar_instruction(instruction)?;
        match typed.kind {
            ScalarInstructionKind::Return { width, value } => {
                let returned = resolve(arena, &env, &value, width, typed.span)?;
                let defined = bool_and(arena, execution_defined, returned.defined, typed.span)?;
                result = Some(DefinedValue {
                    defined,
                    ..returned
                });
            }
            kind => {
                let (dest, value, immediate) = lower_assignment(arena, &env, kind, typed.span)?;
                if env.contains_key(&dest) {
                    return Err(ReflectError {
                        kind: ReflectErrorKind::DuplicateValue,
                        span: Some(typed.span),
                        detail: format!("duplicate SSA definition `%{dest}`"),
                    });
                }
                execution_defined = bool_and(arena, execution_defined, immediate, typed.span)?;
                env.insert(dest, value);
            }
        }
    }
    let result = result.ok_or_else(|| ReflectError {
        kind: ReflectErrorKind::InvalidReturn,
        span: Some(function.blocks[0].span),
        detail: "straight-line scalar function has no return".to_owned(),
    })?;
    Ok((result, env))
}

fn lower_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    kind: ScalarInstructionKind,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    match kind {
        ScalarInstructionKind::Binary {
            dest,
            opcode,
            flags,
            width,
            lhs,
            rhs,
        } => lower_binary_assignment(arena, env, dest, opcode, &flags, width, &lhs, &rhs, span),
        ScalarInstructionKind::Icmp {
            dest,
            predicate,
            width,
            lhs,
            rhs,
        } => lower_icmp_assignment(arena, env, dest, predicate, width, &lhs, &rhs, span),
        ScalarInstructionKind::Select {
            dest,
            condition,
            width,
            then_value,
            else_value,
        } => lower_select_assignment(
            arena,
            env,
            dest,
            &condition,
            width,
            &then_value,
            &else_value,
            span,
        ),
        ScalarInstructionKind::Cast {
            dest,
            opcode,
            flags,
            source_width,
            operand,
            target_width,
        } => lower_cast_assignment(
            arena,
            env,
            dest,
            opcode,
            &flags,
            source_width,
            &operand,
            target_width,
            span,
        ),
        ScalarInstructionKind::Intrinsic {
            dest,
            intrinsic,
            width,
            lhs,
            rhs,
        } => lower_intrinsic_assignment(arena, env, dest, intrinsic, width, &lhs, &rhs, span),
        ScalarInstructionKind::Return { .. } => unreachable!("return handled by caller"),
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "typed binary fields are explicit parser output"
)]
fn lower_binary_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    dest: String,
    opcode: BinaryOpcode,
    flags: &[SemanticFlag],
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    let lhs = resolve(arena, env, lhs, width, span)?;
    let rhs = resolve(arena, env, rhs, width, span)?;
    let value = binary_value(arena, opcode, lhs.value, rhs.value, width, span)?;
    let operands_defined = bool_and(arena, lhs.defined, rhs.defined, span)?;
    let poison_free = binary_poison_free(
        arena, opcode, flags, lhs.value, rhs.value, value, width, span,
    )?;
    let defined = bool_and(arena, operands_defined, poison_free, span)?;
    let immediate = binary_immediate_defined(arena, opcode, lhs, rhs, width, span)?;
    Ok((
        dest,
        DefinedValue {
            value,
            defined,
            width,
        },
        immediate,
    ))
}

#[expect(
    clippy::too_many_arguments,
    reason = "typed comparison fields are explicit parser output"
)]
fn lower_icmp_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    dest: String,
    predicate: IntPredicate,
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    let lhs = resolve(arena, env, lhs, width, span)?;
    let rhs = resolve(arena, env, rhs, width, span)?;
    let value = compare_value(arena, predicate, lhs.value, rhs.value, span)?;
    let defined = bool_and(arena, lhs.defined, rhs.defined, span)?;
    Ok((
        dest,
        DefinedValue {
            value,
            defined,
            width: 1,
        },
        arena.bool_const(true),
    ))
}

#[expect(
    clippy::too_many_arguments,
    reason = "typed select fields are explicit parser output"
)]
fn lower_select_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    dest: String,
    condition: &Operand,
    width: u32,
    then_value: &Operand,
    else_value: &Operand,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    let condition = resolve(arena, env, condition, 1, span)?;
    let then_value = resolve(arena, env, then_value, width, span)?;
    let else_value = resolve(arena, env, else_value, width, span)?;
    let value = arena
        .ite(condition.value, then_value.value, else_value.value)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let selected_defined = arena
        .ite(condition.value, then_value.defined, else_value.defined)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let defined = bool_and(arena, condition.defined, selected_defined, span)?;
    Ok((
        dest,
        DefinedValue {
            value,
            defined,
            width,
        },
        arena.bool_const(true),
    ))
}

#[expect(
    clippy::too_many_arguments,
    reason = "typed cast fields are explicit parser output"
)]
fn lower_cast_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    dest: String,
    opcode: CastOpcode,
    flags: &[SemanticFlag],
    source_width: u32,
    operand: &Operand,
    target_width: u32,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    let operand = resolve(arena, env, operand, source_width, span)?;
    let value = cast_value(
        arena,
        opcode,
        operand.value,
        source_width,
        target_width,
        span,
    )?;
    let flag_defined = cast_flag_defined(
        arena,
        opcode,
        flags,
        operand.value,
        value,
        source_width,
        target_width,
        span,
    )?;
    let defined = bool_and(arena, operand.defined, flag_defined, span)?;
    Ok((
        dest,
        DefinedValue {
            value,
            defined,
            width: target_width,
        },
        arena.bool_const(true),
    ))
}

#[expect(
    clippy::too_many_arguments,
    reason = "typed intrinsic fields are explicit parser output"
)]
fn lower_intrinsic_assignment(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    dest: String,
    intrinsic: Intrinsic,
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
    span: SourceSpan,
) -> Result<(String, DefinedValue, TermId), ReflectError> {
    let lhs = resolve(arena, env, lhs, width, span)?;
    let rhs = resolve(arena, env, rhs, width, span)?;
    let condition = match intrinsic {
        Intrinsic::UnsignedMin => arena.bv_ule(lhs.value, rhs.value),
        Intrinsic::UnsignedMax => arena.bv_uge(lhs.value, rhs.value),
    }
    .map_err(|error| ir_error(span, &error.to_string()))?;
    let value = arena
        .ite(condition, lhs.value, rhs.value)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let defined = bool_and(arena, lhs.defined, rhs.defined, span)?;
    Ok((
        dest,
        DefinedValue {
            value,
            defined,
            width,
        },
        arena.bool_const(true),
    ))
}

fn resolve(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    operand: &Operand,
    width: u32,
    span: SourceSpan,
) -> Result<DefinedValue, ReflectError> {
    match operand {
        Operand::Local(name) => {
            let value = env.get(name).copied().ok_or_else(|| ReflectError {
                kind: ReflectErrorKind::UndefinedValue,
                span: Some(span),
                detail: format!("undefined SSA value `%{name}`"),
            })?;
            if value.width != width {
                return Err(ReflectError {
                    kind: ReflectErrorKind::WidthMismatch,
                    span: Some(span),
                    detail: format!(
                        "SSA value `%{name}` has width {}, used as i{width}",
                        value.width
                    ),
                });
            }
            Ok(value)
        }
        Operand::Constant(raw) => {
            let value = constant(arena, raw, width, span)?;
            Ok(DefinedValue {
                value,
                defined: arena.bool_const(true),
                width,
            })
        }
    }
}

fn constant(
    arena: &mut TermArena,
    raw: &str,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if width == 1 {
        return match raw {
            "0" | "false" => Ok(arena.bool_const(false)),
            "1" | "true" => Ok(arena.bool_const(true)),
            _ => Err(ReflectError {
                kind: ReflectErrorKind::WidthMismatch,
                span: Some(span),
                detail: format!("constant `{raw}` does not fit i1"),
            }),
        };
    }
    if width > 128 {
        return Err(ReflectError {
            kind: ReflectErrorKind::UnsupportedWidth,
            span: Some(span),
            detail: format!(
                "checked scalar constants wider than 128 bits are not yet supported: i{width}"
            ),
        });
    }
    let value = if raw.starts_with('-') {
        let signed = raw.parse::<i128>().map_err(|_| ReflectError {
            kind: ReflectErrorKind::WidthMismatch,
            span: Some(span),
            detail: format!("invalid signed i{width} constant `{raw}`"),
        })?;
        let minimum = if width == 128 {
            i128::MIN
        } else {
            -(1_i128 << (width - 1))
        };
        if signed < minimum {
            return Err(ReflectError {
                kind: ReflectErrorKind::WidthMismatch,
                span: Some(span),
                detail: format!("constant `{raw}` does not fit i{width}"),
            });
        }
        let twos_complement = signed.cast_unsigned();
        if width == 128 {
            twos_complement
        } else {
            twos_complement & ((1_u128 << width) - 1)
        }
    } else {
        let unsigned = raw.parse::<u128>().map_err(|_| ReflectError {
            kind: ReflectErrorKind::WidthMismatch,
            span: Some(span),
            detail: format!("invalid unsigned i{width} constant `{raw}`"),
        })?;
        if width < 128 && unsigned >= (1_u128 << width) {
            return Err(ReflectError {
                kind: ReflectErrorKind::WidthMismatch,
                span: Some(span),
                detail: format!("constant `{raw}` does not fit i{width}"),
            });
        }
        unsigned
    };
    arena
        .bv_const(width, value)
        .map_err(|error| ir_error(span, &error.to_string()))
}

fn binary_value(
    arena: &mut TermArena,
    opcode: BinaryOpcode,
    lhs: TermId,
    rhs: TermId,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let built = if width == 1 {
        match opcode {
            BinaryOpcode::And => arena.and(lhs, rhs),
            BinaryOpcode::Or => arena.or(lhs, rhs),
            BinaryOpcode::Xor => arena.xor(lhs, rhs),
            _ => {
                return Err(ReflectError {
                    kind: ReflectErrorKind::UnsupportedWidth,
                    span: Some(span),
                    detail: format!("{opcode:?} over i1 is outside this scalar slice"),
                });
            }
        }
    } else {
        match opcode {
            BinaryOpcode::Add => arena.bv_add(lhs, rhs),
            BinaryOpcode::Sub => arena.bv_sub(lhs, rhs),
            BinaryOpcode::Mul => arena.bv_mul(lhs, rhs),
            BinaryOpcode::And => arena.bv_and(lhs, rhs),
            BinaryOpcode::Or => arena.bv_or(lhs, rhs),
            BinaryOpcode::Xor => arena.bv_xor(lhs, rhs),
            BinaryOpcode::Shl => arena.bv_shl(lhs, rhs),
            BinaryOpcode::Lshr => arena.bv_lshr(lhs, rhs),
            BinaryOpcode::Ashr => arena.bv_ashr(lhs, rhs),
            BinaryOpcode::Udiv => arena.bv_udiv(lhs, rhs),
            BinaryOpcode::Sdiv => arena.bv_sdiv(lhs, rhs),
            BinaryOpcode::Urem => arena.bv_urem(lhs, rhs),
            BinaryOpcode::Srem => arena.bv_srem(lhs, rhs),
        }
    };
    built.map_err(|error| ir_error(span, &error.to_string()))
}

#[expect(
    clippy::too_many_arguments,
    reason = "LLVM flag semantics require opcode/value context"
)]
fn binary_poison_free(
    arena: &mut TermArena,
    opcode: BinaryOpcode,
    flags: &[SemanticFlag],
    lhs: TermId,
    rhs: TermId,
    value: TermId,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let mut conditions = vec![arena.bool_const(true)];
    if matches!(
        opcode,
        BinaryOpcode::Shl | BinaryOpcode::Lshr | BinaryOpcode::Ashr
    ) {
        let width_term = arena
            .bv_const(width, u128::from(width))
            .map_err(|error| ir_error(span, &error.to_string()))?;
        conditions.push(
            arena
                .bv_ult(rhs, width_term)
                .map_err(|error| ir_error(span, &error.to_string()))?,
        );
    }
    for flag in flags {
        let condition = match (opcode, flag) {
            (BinaryOpcode::Add, SemanticFlag::Nuw) => {
                let overflow = arena.bv_uaddo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Add, SemanticFlag::Nsw) => {
                let overflow = arena.bv_saddo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Sub, SemanticFlag::Nuw) => {
                let overflow = arena.bv_usubo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Sub, SemanticFlag::Nsw) => {
                let overflow = arena.bv_ssubo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Mul, SemanticFlag::Nuw) => {
                let overflow = arena.bv_umulo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Mul, SemanticFlag::Nsw) => {
                let overflow = arena.bv_smulo(lhs, rhs);
                negate_ir(arena, overflow, span)?
            }
            (BinaryOpcode::Shl, SemanticFlag::Nuw) => {
                let reverse = arena
                    .bv_lshr(value, rhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?;
                arena
                    .eq(reverse, lhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (BinaryOpcode::Shl, SemanticFlag::Nsw) => {
                let reverse = arena
                    .bv_ashr(value, rhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?;
                arena
                    .eq(reverse, lhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (BinaryOpcode::Lshr | BinaryOpcode::Ashr, SemanticFlag::Exact) => {
                let reverse = arena
                    .bv_shl(value, rhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?;
                arena
                    .eq(reverse, lhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (BinaryOpcode::Udiv | BinaryOpcode::Sdiv, SemanticFlag::Exact) => {
                let reverse = arena
                    .bv_mul(value, rhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?;
                arena
                    .eq(reverse, lhs)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (BinaryOpcode::Or, SemanticFlag::Disjoint) => {
                disjoint_defined(arena, lhs, rhs, width, span)?
            }
            _ => {
                return Err(ReflectError {
                    kind: ReflectErrorKind::Syntax,
                    span: Some(span),
                    detail: format!("invalid {flag:?} flag on {opcode:?}"),
                });
            }
        };
        conditions.push(condition);
    }
    bool_all(arena, &conditions, span)
}

fn disjoint_defined(
    arena: &mut TermArena,
    lhs: TermId,
    rhs: TermId,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if width == 1 {
        let overlap = arena
            .and(lhs, rhs)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        return negate_ir(arena, Ok(overlap), span);
    }
    let overlap = arena
        .bv_and(lhs, rhs)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let zero = arena
        .bv_const(width, 0)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    arena
        .eq(overlap, zero)
        .map_err(|error| ir_error(span, &error.to_string()))
}

fn binary_immediate_defined(
    arena: &mut TermArena,
    opcode: BinaryOpcode,
    lhs: DefinedValue,
    rhs: DefinedValue,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if !matches!(
        opcode,
        BinaryOpcode::Udiv | BinaryOpcode::Sdiv | BinaryOpcode::Urem | BinaryOpcode::Srem
    ) {
        return Ok(arena.bool_const(true));
    }
    let zero = arena
        .bv_const(width, 0)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let divisor_zero = arena
        .eq(rhs.value, zero)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let divisor_nonzero = arena
        .not(divisor_zero)
        .map_err(|error| ir_error(span, &error.to_string()))?;
    let mut conditions = vec![rhs.defined, divisor_nonzero];
    if matches!(opcode, BinaryOpcode::Sdiv | BinaryOpcode::Srem) {
        let min = arena
            .bv_const(width, 1_u128 << (width - 1))
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let minus_one = arena
            .bv_const(
                width,
                if width == 128 {
                    u128::MAX
                } else {
                    (1_u128 << width) - 1
                },
            )
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let lhs_min = arena
            .eq(lhs.value, min)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let rhs_minus_one = arena
            .eq(rhs.value, minus_one)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let overflow = arena
            .and(lhs_min, rhs_minus_one)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let no_overflow = arena
            .not(overflow)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        let dividend_poison = arena
            .not(lhs.defined)
            .map_err(|error| ir_error(span, &error.to_string()))?;
        conditions.push(
            arena
                .or(dividend_poison, no_overflow)
                .map_err(|error| ir_error(span, &error.to_string()))?,
        );
    }
    bool_all(arena, &conditions, span)
}

fn compare_value(
    arena: &mut TermArena,
    predicate: IntPredicate,
    lhs: TermId,
    rhs: TermId,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let result = match predicate {
        IntPredicate::Eq => arena.eq(lhs, rhs),
        IntPredicate::Ne => {
            let equal = arena
                .eq(lhs, rhs)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            return arena
                .not(equal)
                .map_err(|error| ir_error(span, &error.to_string()));
        }
        IntPredicate::Ult => arena.bv_ult(lhs, rhs),
        IntPredicate::Ule => arena.bv_ule(lhs, rhs),
        IntPredicate::Ugt => arena.bv_ugt(lhs, rhs),
        IntPredicate::Uge => arena.bv_uge(lhs, rhs),
        IntPredicate::Slt => arena.bv_slt(lhs, rhs),
        IntPredicate::Sle => arena.bv_sle(lhs, rhs),
        IntPredicate::Sgt => arena.bv_sgt(lhs, rhs),
        IntPredicate::Sge => arena.bv_sge(lhs, rhs),
    };
    result.map_err(|error| ir_error(span, &error.to_string()))
}

fn cast_value(
    arena: &mut TermArena,
    opcode: CastOpcode,
    operand: TermId,
    source_width: u32,
    target_width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let result = match (opcode, source_width, target_width) {
        (CastOpcode::Zext, 1, target) => {
            let one = arena
                .bv_const(target, 1)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            let zero = arena
                .bv_const(target, 0)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            return arena
                .ite(operand, one, zero)
                .map_err(|error| ir_error(span, &error.to_string()));
        }
        (CastOpcode::Sext, 1, target) => {
            let ones = arena
                .bv_const(
                    target,
                    if target == 128 {
                        u128::MAX
                    } else {
                        (1_u128 << target) - 1
                    },
                )
                .map_err(|error| ir_error(span, &error.to_string()))?;
            let zero = arena
                .bv_const(target, 0)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            return arena
                .ite(operand, ones, zero)
                .map_err(|error| ir_error(span, &error.to_string()));
        }
        (CastOpcode::Trunc, _, 1) => {
            let bit = arena
                .extract(0, 0, operand)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            let one = arena
                .bv_const(1, 1)
                .map_err(|error| ir_error(span, &error.to_string()))?;
            return arena
                .eq(bit, one)
                .map_err(|error| ir_error(span, &error.to_string()));
        }
        (CastOpcode::Zext, source, target) => arena.zero_ext(target - source, operand),
        (CastOpcode::Sext, source, target) => arena.sign_ext(target - source, operand),
        (CastOpcode::Trunc, _, target) => arena.extract(target - 1, 0, operand),
    };
    result.map_err(|error| ir_error(span, &error.to_string()))
}

#[expect(
    clippy::too_many_arguments,
    reason = "cast flag semantics require both widths and values"
)]
fn cast_flag_defined(
    arena: &mut TermArena,
    opcode: CastOpcode,
    flags: &[SemanticFlag],
    operand: TermId,
    value: TermId,
    source_width: u32,
    target_width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let mut conditions = vec![arena.bool_const(true)];
    for flag in flags {
        let condition = match (opcode, flag) {
            (CastOpcode::Zext, SemanticFlag::Nneg) if source_width == 1 => {
                negate_ir(arena, Ok(operand), span)?
            }
            (CastOpcode::Zext, SemanticFlag::Nneg) => {
                let zero = arena
                    .bv_const(source_width, 0)
                    .map_err(|error| ir_error(span, &error.to_string()))?;
                arena
                    .bv_sge(operand, zero)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (CastOpcode::Trunc, SemanticFlag::Nuw) => {
                let restored = if target_width == 1 {
                    cast_value(arena, CastOpcode::Zext, value, 1, source_width, span)?
                } else {
                    arena
                        .zero_ext(source_width - target_width, value)
                        .map_err(|error| ir_error(span, &error.to_string()))?
                };
                arena
                    .eq(restored, operand)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            (CastOpcode::Trunc, SemanticFlag::Nsw) => {
                let restored = if target_width == 1 {
                    cast_value(arena, CastOpcode::Sext, value, 1, source_width, span)?
                } else {
                    arena
                        .sign_ext(source_width - target_width, value)
                        .map_err(|error| ir_error(span, &error.to_string()))?
                };
                arena
                    .eq(restored, operand)
                    .map_err(|error| ir_error(span, &error.to_string()))?
            }
            _ => {
                return Err(ReflectError {
                    kind: ReflectErrorKind::Syntax,
                    span: Some(span),
                    detail: format!("invalid {flag:?} flag on {opcode:?}"),
                });
            }
        };
        conditions.push(condition);
    }
    bool_all(arena, &conditions, span)
}

fn bool_all(
    arena: &mut TermArena,
    conditions: &[TermId],
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let mut result = arena.bool_const(true);
    for condition in conditions {
        result = bool_and(arena, result, *condition, span)?;
    }
    Ok(result)
}

fn bool_and(
    arena: &mut TermArena,
    lhs: TermId,
    rhs: TermId,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    arena
        .and(lhs, rhs)
        .map_err(|error| ir_error(span, &error.to_string()))
}

fn negate_ir(
    arena: &mut TermArena,
    term: Result<TermId, axeyum_ir::IrError>,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let term = term.map_err(|error| ir_error(span, &error.to_string()))?;
    arena
        .not(term)
        .map_err(|error| ir_error(span, &error.to_string()))
}

fn parse_width(ty: &str, span: SourceSpan) -> Result<u32, ReflectError> {
    let Some(digits) = ty.strip_prefix('i') else {
        return Err(ReflectError {
            kind: ReflectErrorKind::UnsupportedWidth,
            span: Some(span),
            detail: format!("checked scalar reflection does not support type `{ty}`"),
        });
    };
    let width = digits.parse::<u32>().map_err(|_| ReflectError {
        kind: ReflectErrorKind::UnsupportedWidth,
        span: Some(span),
        detail: format!("invalid scalar integer type `{ty}`"),
    })?;
    if width == 0 || width > 128 {
        return Err(ReflectError {
            kind: ReflectErrorKind::UnsupportedWidth,
            span: Some(span),
            detail: format!("checked scalar reflection supports i1 through i128, found `{ty}`"),
        });
    }
    Ok(width)
}

fn sort_for_width(width: u32) -> Sort {
    if width == 1 {
        Sort::Bool
    } else {
        Sort::BitVec(width)
    }
}

fn ir_error(span: SourceSpan, detail: &str) -> ReflectError {
    ReflectError {
        kind: ReflectErrorKind::IrConstruction,
        span: Some(span),
        detail: format!("LLVM scalar IR construction failed: {detail}"),
    }
}
