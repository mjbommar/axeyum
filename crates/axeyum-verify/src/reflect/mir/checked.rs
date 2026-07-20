//! Non-panicking symbolic execution for the authenticated MIR byte-memory slice.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::error::Error;
use std::fmt;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};

use super::syntax::{
    BinaryOpcode, Function, IntegerConstant, MirType, Operand, ParseError, Rvalue, SourceSpan,
    StatementKind, TerminatorKind, parse_function,
};

const MAX_MEMORY_BYTES: usize = 256;
const MAX_BLOCK_EXECUTIONS: usize = 4_096;
const REGISTERED_USIZE_WIDTH: u32 = 64;

/// Named-function and target configuration for checked MIR reflection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirMemoryConfig {
    /// Function selected from the complete raw compiler MIR module.
    pub function: String,
    /// Target width used to interpret `usize` and `isize`.
    pub target_usize_width: u32,
}

impl MirMemoryConfig {
    /// Creates a checked reflection configuration.
    #[must_use]
    pub fn new(function: impl Into<String>, target_usize_width: u32) -> Self {
        Self {
            function: function.into(),
            target_usize_width,
        }
    }
}

/// One declared scalar MIR parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarParameter {
    /// MIR local number.
    pub local: u32,
    /// Fresh Axeyum symbol.
    pub symbol: SymbolId,
    /// Scalar width (`1` denotes `Bool`).
    pub width: u32,
    /// Signedness used by comparisons.
    pub signed: bool,
}

/// Input and final state of the single admitted byte array.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedByteRegion {
    /// MIR local containing the by-value array.
    pub local: u32,
    /// Fresh BV8 symbols for the initialized input bytes.
    pub input: Vec<SymbolId>,
    /// Path-joined final byte values, meaningful when `panic` is false.
    pub output: Vec<TermId>,
}

/// One reflected scalar result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MirValue {
    /// Boolean or bit-vector result term.
    pub value: TermId,
    /// Scalar width (`1` denotes `Bool`).
    pub width: u32,
    /// Signedness used by comparisons.
    pub signed: bool,
}

/// Checked bounded MIR reflection in its owned arena.
#[derive(Debug)]
pub struct CheckedMirMemory {
    /// Arena owning all reflected terms.
    pub arena: TermArena,
    /// Scalar parameters in source order.
    pub params: Vec<ScalarParameter>,
    /// The single initialized bounded byte region.
    pub region: CheckedByteRegion,
    /// Joined return value, meaningful when `panic` is false.
    pub result: MirValue,
    /// Path-conditioned panic predicate, including every memory access.
    pub panic: TermId,
}

/// Stable checked-MIR reflection failure classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReflectErrorKind {
    /// Located typed syntax parsing failed.
    Syntax,
    /// The registered fixture target width was not selected.
    TargetWidth,
    /// The function does not have exactly one byte-array parameter.
    RegionCount,
    /// The byte-array length is outside `1..=256`.
    RegionSize,
    /// A parameter or local type is outside the semantic slice.
    UnsupportedType,
    /// A referenced local has no declaration or value.
    UndefinedLocal,
    /// A local is declared or assigned more than once on one path.
    DuplicateDefinition,
    /// Operand and destination types disagree.
    TypeMismatch,
    /// The entry block or a referenced successor is absent.
    UndefinedBlock,
    /// The CFG contains a cycle.
    CyclicControlFlow,
    /// Bounded acyclic path expansion exceeded the fixed limit.
    ExecutionLimit,
    /// A return did not produce the declared `_0` value.
    InvalidReturn,
    /// Axeyum IR construction rejected an operation.
    IrConstruction,
}

/// Located checked-MIR reflection failure.
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

    /// Source span when the failure belongs to textual MIR.
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScalarTy {
    width: u32,
    signed: bool,
    boolean: bool,
}

impl ScalarTy {
    fn sort(self) -> Sort {
        if self.boolean {
            Sort::Bool
        } else {
            Sort::BitVec(self.width)
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ScalarValue {
    term: TermId,
    ty: ScalarTy,
}

#[derive(Clone)]
struct State {
    scalars: HashMap<u32, ScalarValue>,
    bytes: Vec<TermId>,
    panic: TermId,
}

struct Outcome {
    result: ScalarValue,
    bytes: Vec<TermId>,
    panic: TermId,
}

struct Context<'a> {
    function: &'a Function,
    blocks: BTreeMap<&'a str, usize>,
    types: BTreeMap<u32, MirType>,
    array_local: u32,
    array_bytes: usize,
    target_width: u32,
}

/// Reflect one named function from authenticated raw compiler MIR.
///
/// Every array read and write independently contributes `index >= len` to the
/// returned panic predicate. Compiler-emitted `assert` terminators add evidence
/// but are never trusted to establish access safety.
///
/// # Errors
///
/// Returns a stable, located error for malformed syntax, unsupported types,
/// invalid CFGs, or rejected IR construction.
pub fn reflect_bounded_memory_checked(
    input: &str,
    config: &MirMemoryConfig,
) -> Result<CheckedMirMemory, ReflectError> {
    if config.target_usize_width != REGISTERED_USIZE_WIDTH {
        return Err(ReflectError {
            kind: ReflectErrorKind::TargetWidth,
            span: None,
            detail: format!(
                "registered MIR profile requires {REGISTERED_USIZE_WIDTH}-bit usize; found {}",
                config.target_usize_width
            ),
        });
    }
    let function = parse_function(input, &config.function)?;
    let context = validate_function(&function, config.target_usize_width)?;
    let mut arena = TermArena::new();
    let never = arena.bool_const(false);
    let mut scalars = HashMap::new();
    let mut params = Vec::new();
    for parameter in &function.params {
        if parameter.local == context.array_local {
            continue;
        }
        let ty = scalar_type(parameter.ty, context.target_width, parameter.span)?;
        let name = format!("mir.local._{}.scope", parameter.local);
        let symbol = arena
            .declare(&name, ty.sort())
            .map_err(|error| ir_error(parameter.span, error.to_string()))?;
        scalars.insert(
            parameter.local,
            ScalarValue {
                term: arena.var(symbol),
                ty,
            },
        );
        params.push(ScalarParameter {
            local: parameter.local,
            symbol,
            width: ty.width,
            signed: ty.signed,
        });
    }

    let mut input_symbols = Vec::with_capacity(context.array_bytes);
    let mut bytes = Vec::with_capacity(context.array_bytes);
    for index in 0..context.array_bytes {
        let name = format!("mir.array._{}.byte.{index}", context.array_local);
        let symbol = arena
            .declare(&name, Sort::BitVec(8))
            .map_err(|error| ir_error(function.span, error.to_string()))?;
        input_symbols.push(symbol);
        bytes.push(arena.var(symbol));
    }
    let outcome = execute_block(
        &mut arena,
        &context,
        "bb0",
        State {
            scalars,
            bytes,
            panic: never,
        },
        &mut 0,
    )?;
    Ok(CheckedMirMemory {
        arena,
        params,
        region: CheckedByteRegion {
            local: context.array_local,
            input: input_symbols,
            output: outcome.bytes,
        },
        result: MirValue {
            value: outcome.result.term,
            width: outcome.result.ty.width,
            signed: outcome.result.ty.signed,
        },
        panic: outcome.panic,
    })
}

fn validate_function(function: &Function, target_width: u32) -> Result<Context<'_>, ReflectError> {
    let (types, array_local, array_bytes) = validate_types_and_region(function, target_width)?;
    let blocks = validate_blocks(function)?;
    let context = Context {
        function,
        blocks,
        types,
        array_local,
        array_bytes,
        target_width,
    };
    validate_acyclic(&context)?;
    Ok(context)
}

fn validate_types_and_region(
    function: &Function,
    target_width: u32,
) -> Result<(BTreeMap<u32, MirType>, u32, usize), ReflectError> {
    let arrays = function
        .params
        .iter()
        .filter_map(|parameter| match parameter.ty {
            MirType::ByteArray { bytes } => Some((parameter, bytes)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [(array, array_bytes)] = arrays.as_slice() else {
        return Err(ReflectError {
            kind: ReflectErrorKind::RegionCount,
            span: Some(function.span),
            detail: format!(
                "checked MIR memory requires exactly one byte-array parameter; found {}",
                arrays.len()
            ),
        });
    };
    if !(1..=MAX_MEMORY_BYTES).contains(array_bytes) {
        return Err(ReflectError {
            kind: ReflectErrorKind::RegionSize,
            span: Some(array.span),
            detail: format!(
                "bounded MIR region must contain 1 through {MAX_MEMORY_BYTES} bytes; found {array_bytes}"
            ),
        });
    }

    let mut types = BTreeMap::new();
    for parameter in &function.params {
        if types.insert(parameter.local, parameter.ty).is_some() {
            return Err(reflect_error(
                ReflectErrorKind::DuplicateDefinition,
                parameter.span,
                format!("local _{} is declared more than once", parameter.local),
            ));
        }
        if !matches!(parameter.ty, MirType::ByteArray { .. }) {
            scalar_type(parameter.ty, target_width, parameter.span)?;
        }
    }
    for local in &function.locals {
        if matches!(local.ty, MirType::ByteArray { .. }) {
            return Err(reflect_error(
                ReflectErrorKind::UnsupportedType,
                local.span,
                "only the by-value parameter may have byte-array type",
            ));
        }
        scalar_type(local.ty, target_width, local.span)?;
        if types.insert(local.local, local.ty).is_some() {
            return Err(reflect_error(
                ReflectErrorKind::DuplicateDefinition,
                local.span,
                format!("local _{} is declared more than once", local.local),
            ));
        }
    }
    let return_local = types.get(&0).copied().ok_or_else(|| {
        reflect_error(
            ReflectErrorKind::InvalidReturn,
            function.span,
            "MIR function has no `_0` return local",
        )
    })?;
    if return_local != function.return_ty {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            function.span,
            "`_0` type differs from the declared return type",
        ));
    }

    Ok((types, array.local, *array_bytes))
}

fn validate_blocks(function: &Function) -> Result<BTreeMap<&str, usize>, ReflectError> {
    let mut blocks = BTreeMap::new();
    for (index, block) in function.blocks.iter().enumerate() {
        blocks.insert(block.label.as_str(), index);
    }
    if !blocks.contains_key("bb0") {
        return Err(reflect_error(
            ReflectErrorKind::UndefinedBlock,
            function.span,
            "checked MIR function has no `bb0` entry",
        ));
    }
    for block in &function.blocks {
        for target in targets(&block.terminator.kind) {
            if !blocks.contains_key(target) {
                return Err(reflect_error(
                    ReflectErrorKind::UndefinedBlock,
                    block.terminator.span,
                    format!("block {} targets absent block {target}", block.label),
                ));
            }
        }
    }
    Ok(blocks)
}

fn validate_acyclic(context: &Context<'_>) -> Result<(), ReflectError> {
    fn visit(
        context: &Context<'_>,
        label: &str,
        colors: &mut BTreeMap<String, u8>,
    ) -> Result<(), ReflectError> {
        match colors.get(label).copied() {
            Some(2) => return Ok(()),
            Some(1) => {
                let block = block(context, label)?;
                return Err(reflect_error(
                    ReflectErrorKind::CyclicControlFlow,
                    block.terminator.span,
                    "cyclic MIR CFG belongs on the TransitionSystem path",
                ));
            }
            _ => {}
        }
        colors.insert(label.to_owned(), 1);
        let source = block(context, label)?;
        for target in targets(&source.terminator.kind) {
            visit(context, target, colors)?;
        }
        colors.insert(label.to_owned(), 2);
        Ok(())
    }
    let mut colors = BTreeMap::new();
    for block in &context.function.blocks {
        visit(context, &block.label, &mut colors)?;
    }
    Ok(())
}

fn targets(kind: &TerminatorKind) -> Vec<&str> {
    match kind {
        TerminatorKind::Return => Vec::new(),
        TerminatorKind::Goto { target } => vec![target],
        TerminatorKind::Assert { success, .. } => vec![success],
        TerminatorKind::Switch {
            cases, otherwise, ..
        } => cases
            .iter()
            .map(|case| case.target.as_str())
            .chain(std::iter::once(otherwise.as_str()))
            .collect(),
    }
}

fn block<'a>(
    context: &'a Context<'_>,
    label: &str,
) -> Result<&'a super::syntax::Block, ReflectError> {
    context
        .blocks
        .get(label)
        .and_then(|index| context.function.blocks.get(*index))
        .ok_or_else(|| {
            reflect_error(
                ReflectErrorKind::UndefinedBlock,
                context.function.span,
                format!("referenced block {label} is absent"),
            )
        })
}

fn execute_block(
    arena: &mut TermArena,
    context: &Context<'_>,
    label: &str,
    mut state: State,
    executions: &mut usize,
) -> Result<Outcome, ReflectError> {
    *executions = executions.saturating_add(1);
    if *executions > MAX_BLOCK_EXECUTIONS {
        return Err(reflect_error(
            ReflectErrorKind::ExecutionLimit,
            context.function.span,
            format!("checked MIR expands beyond {MAX_BLOCK_EXECUTIONS} block executions"),
        ));
    }
    let source = block(context, label)?;
    execute_statements(arena, context, &mut state, source)?;
    execute_terminator(arena, context, state, source, executions)
}

fn execute_statements(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &mut State,
    source: &super::syntax::Block,
) -> Result<(), ReflectError> {
    for statement in &source.statements {
        match &statement.kind {
            StatementKind::StorageMarker { local } => {
                if !context.types.contains_key(local) {
                    return Err(reflect_error(
                        ReflectErrorKind::UndefinedLocal,
                        statement.span,
                        format!("storage marker references undeclared local _{local}"),
                    ));
                }
            }
            StatementKind::Assign { destination, value } => {
                if *destination == context.array_local {
                    return Err(reflect_error(
                        ReflectErrorKind::TypeMismatch,
                        statement.span,
                        "whole-array assignment is outside the checked memory slice",
                    ));
                }
                if state.scalars.contains_key(destination) {
                    return Err(reflect_error(
                        ReflectErrorKind::DuplicateDefinition,
                        statement.span,
                        format!("local _{destination} is assigned more than once on one path"),
                    ));
                }
                let expected = local_scalar_type(context, *destination, statement.span)?;
                let actual = lower_rvalue(arena, context, state, value, statement.span)?;
                require_type(actual.ty, expected, statement.span)?;
                state.scalars.insert(*destination, actual);
            }
            StatementKind::ArrayStore {
                array,
                index,
                value,
            } => {
                require_array(context, *array, statement.span)?;
                let index = local_scalar(state, *index, statement.span)?;
                require_integer(index.ty, statement.span, "array index")?;
                let value = lower_operand(arena, context, state, value, statement.span)?;
                let byte_ty = ScalarTy {
                    width: 8,
                    signed: false,
                    boolean: false,
                };
                require_type(value.ty, byte_ty, statement.span)?;
                let in_bounds =
                    access_in_bounds(arena, index, context.array_bytes, statement.span)?;
                add_access_panic(arena, state, in_bounds, statement.span)?;
                for (offset, byte) in state.bytes.iter_mut().enumerate() {
                    let selected = index_equals(arena, index, offset, statement.span)?;
                    *byte = arena
                        .ite(selected, value.term, *byte)
                        .map_err(|error| ir_error(statement.span, error.to_string()))?;
                }
            }
        }
    }
    Ok(())
}

fn execute_terminator(
    arena: &mut TermArena,
    context: &Context<'_>,
    mut state: State,
    source: &super::syntax::Block,
    executions: &mut usize,
) -> Result<Outcome, ReflectError> {
    match &source.terminator.kind {
        TerminatorKind::Return => {
            let result = state.scalars.get(&0).copied().ok_or_else(|| {
                reflect_error(
                    ReflectErrorKind::InvalidReturn,
                    source.terminator.span,
                    "return reached before `_0` was assigned",
                )
            })?;
            let expected = scalar_type(
                context.function.return_ty,
                context.target_width,
                source.terminator.span,
            )?;
            require_type(result.ty, expected, source.terminator.span)?;
            Ok(Outcome {
                result,
                bytes: state.bytes,
                panic: state.panic,
            })
        }
        TerminatorKind::Goto { target } => execute_block(arena, context, target, state, executions),
        TerminatorKind::Assert {
            condition,
            expected,
            success,
        } => {
            let condition =
                lower_operand(arena, context, &state, condition, source.terminator.span)?;
            require_bool(condition.ty, source.terminator.span, "assert condition")?;
            let failure = if *expected {
                arena
                    .not(condition.term)
                    .map_err(|error| ir_error(source.terminator.span, error.to_string()))?
            } else {
                condition.term
            };
            state.panic = arena
                .or(state.panic, failure)
                .map_err(|error| ir_error(source.terminator.span, error.to_string()))?;
            execute_block(arena, context, success, state, executions)
        }
        TerminatorKind::Switch {
            discriminator,
            cases,
            otherwise,
        } => {
            let discriminator = lower_operand(
                arena,
                context,
                &state,
                discriminator,
                source.terminator.span,
            )?;
            let mut seen = BTreeSet::new();
            for case in cases {
                if !seen.insert(case.value) {
                    return Err(reflect_error(
                        ReflectErrorKind::TypeMismatch,
                        source.terminator.span,
                        format!("switch repeats case {}", case.value),
                    ));
                }
            }
            let mut joined = execute_block(arena, context, otherwise, state.clone(), executions)?;
            for case in cases.iter().rev() {
                let selected =
                    switch_case(arena, discriminator, case.value, source.terminator.span)?;
                let branch =
                    execute_block(arena, context, &case.target, state.clone(), executions)?;
                joined = join_outcomes(arena, selected, branch, joined, source.terminator.span)?;
            }
            Ok(joined)
        }
    }
}

fn lower_rvalue(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &mut State,
    value: &Rvalue,
    span: SourceSpan,
) -> Result<ScalarValue, ReflectError> {
    match value {
        Rvalue::Use(operand) => lower_operand(arena, context, state, operand, span),
        Rvalue::ArrayRead { array, index } => {
            require_array(context, *array, span)?;
            let index = local_scalar(state, *index, span)?;
            require_integer(index.ty, span, "array index")?;
            let in_bounds = access_in_bounds(arena, index, context.array_bytes, span)?;
            add_access_panic(arena, state, in_bounds, span)?;
            let mut result = arena
                .bv_const(8, 0)
                .map_err(|error| ir_error(span, error.to_string()))?;
            for (offset, byte) in state.bytes.iter().copied().enumerate().rev() {
                let selected = index_equals(arena, index, offset, span)?;
                result = arena
                    .ite(selected, byte, result)
                    .map_err(|error| ir_error(span, error.to_string()))?;
            }
            Ok(ScalarValue {
                term: result,
                ty: ScalarTy {
                    width: 8,
                    signed: false,
                    boolean: false,
                },
            })
        }
        Rvalue::Binary { op, left, right } => {
            let left = lower_operand(arena, context, state, left, span)?;
            let right = lower_operand(arena, context, state, right, span)?;
            require_type(left.ty, right.ty, span)?;
            let term = match op {
                BinaryOpcode::Eq => arena.eq(left.term, right.term),
                BinaryOpcode::Lt => {
                    require_integer(left.ty, span, "less-than operand")?;
                    if left.ty.signed {
                        arena.bv_slt(left.term, right.term)
                    } else {
                        arena.bv_ult(left.term, right.term)
                    }
                }
                BinaryOpcode::BitAnd if left.ty.boolean => arena.and(left.term, right.term),
                BinaryOpcode::BitAnd => arena.bv_and(left.term, right.term),
            }
            .map_err(|error| ir_error(span, error.to_string()))?;
            let ty = match op {
                BinaryOpcode::Eq | BinaryOpcode::Lt => ScalarTy {
                    width: 1,
                    signed: false,
                    boolean: true,
                },
                BinaryOpcode::BitAnd => left.ty,
            };
            Ok(ScalarValue { term, ty })
        }
    }
}

fn lower_operand(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &State,
    operand: &Operand,
    span: SourceSpan,
) -> Result<ScalarValue, ReflectError> {
    match operand {
        Operand::Local { local, .. } => local_scalar(state, *local, span),
        Operand::Bool(value) => Ok(ScalarValue {
            term: arena.bool_const(*value),
            ty: ScalarTy {
                width: 1,
                signed: false,
                boolean: true,
            },
        }),
        Operand::Integer(constant) => lower_integer(arena, context, *constant, span),
    }
}

fn lower_integer(
    arena: &mut TermArena,
    context: &Context<'_>,
    constant: IntegerConstant,
    span: SourceSpan,
) -> Result<ScalarValue, ReflectError> {
    let ty = scalar_type(constant.ty, context.target_width, span)?;
    require_integer(ty, span, "integer constant")?;
    let mask = if ty.width == 128 {
        u128::MAX
    } else {
        (1_u128 << ty.width) - 1
    };
    let positive_limit = if ty.signed {
        (1_u128 << (ty.width - 1)) - 1
    } else {
        mask
    };
    if !constant.negative && constant.magnitude > positive_limit {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            "integer constant does not fit its declared width",
        ));
    }
    if constant.negative && !ty.signed {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            "negative constant has unsigned MIR type",
        ));
    }
    let signed_limit = if ty.width == 128 {
        1_u128 << 127
    } else {
        1_u128 << (ty.width - 1)
    };
    if constant.negative && constant.magnitude > signed_limit {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            "negative constant does not fit its declared width",
        ));
    }
    let bits = if constant.negative {
        0_u128.wrapping_sub(constant.magnitude) & mask
    } else {
        constant.magnitude
    };
    let term = arena
        .bv_const(ty.width, bits)
        .map_err(|error| ir_error(span, error.to_string()))?;
    Ok(ScalarValue { term, ty })
}

fn add_access_panic(
    arena: &mut TermArena,
    state: &mut State,
    in_bounds: TermId,
    span: SourceSpan,
) -> Result<(), ReflectError> {
    let out_of_bounds = arena
        .not(in_bounds)
        .map_err(|error| ir_error(span, error.to_string()))?;
    state.panic = arena
        .or(state.panic, out_of_bounds)
        .map_err(|error| ir_error(span, error.to_string()))?;
    Ok(())
}

fn access_in_bounds(
    arena: &mut TermArena,
    index: ScalarValue,
    bytes: usize,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if index.ty.width < 128 && bytes as u128 == (1_u128 << index.ty.width) {
        return Ok(arena.bool_const(true));
    }
    let limit = usize_constant(arena, index.ty, bytes, span)?;
    arena
        .bv_ult(index.term, limit)
        .map_err(|error| ir_error(span, error.to_string()))
}

fn index_equals(
    arena: &mut TermArena,
    index: ScalarValue,
    offset: usize,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    let value = usize_constant(arena, index.ty, offset, span)?;
    arena
        .eq(index.term, value)
        .map_err(|error| ir_error(span, error.to_string()))
}

fn usize_constant(
    arena: &mut TermArena,
    ty: ScalarTy,
    value: usize,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    arena
        .bv_const(ty.width, value as u128)
        .map_err(|error| ir_error(span, error.to_string()))
}

fn switch_case(
    arena: &mut TermArena,
    discriminator: ScalarValue,
    value: u128,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    if discriminator.ty.boolean {
        return match value {
            0 => arena
                .not(discriminator.term)
                .map_err(|error| ir_error(span, error.to_string())),
            1 => Ok(discriminator.term),
            _ => Err(reflect_error(
                ReflectErrorKind::TypeMismatch,
                span,
                format!("Boolean switch has non-Boolean case {value}"),
            )),
        };
    }
    let mask = if discriminator.ty.width == 128 {
        u128::MAX
    } else {
        (1_u128 << discriminator.ty.width) - 1
    };
    if value > mask {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("switch case {value} exceeds discriminator width"),
        ));
    }
    let constant = arena
        .bv_const(discriminator.ty.width, value)
        .map_err(|error| ir_error(span, error.to_string()))?;
    arena
        .eq(discriminator.term, constant)
        .map_err(|error| ir_error(span, error.to_string()))
}

fn join_outcomes(
    arena: &mut TermArena,
    condition: TermId,
    then_outcome: Outcome,
    else_outcome: Outcome,
    span: SourceSpan,
) -> Result<Outcome, ReflectError> {
    require_type(then_outcome.result.ty, else_outcome.result.ty, span)?;
    if then_outcome.bytes.len() != else_outcome.bytes.len() {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            "branch memory lengths differ",
        ));
    }
    let result = arena
        .ite(
            condition,
            then_outcome.result.term,
            else_outcome.result.term,
        )
        .map_err(|error| ir_error(span, error.to_string()))?;
    let panic = arena
        .ite(condition, then_outcome.panic, else_outcome.panic)
        .map_err(|error| ir_error(span, error.to_string()))?;
    let bytes = then_outcome
        .bytes
        .into_iter()
        .zip(else_outcome.bytes)
        .map(|(then_byte, else_byte)| {
            arena
                .ite(condition, then_byte, else_byte)
                .map_err(|error| ir_error(span, error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Outcome {
        result: ScalarValue {
            term: result,
            ty: then_outcome.result.ty,
        },
        bytes,
        panic,
    })
}

fn local_scalar(state: &State, local: u32, span: SourceSpan) -> Result<ScalarValue, ReflectError> {
    state.scalars.get(&local).copied().ok_or_else(|| {
        reflect_error(
            ReflectErrorKind::UndefinedLocal,
            span,
            format!("local _{local} is read before definition"),
        )
    })
}

fn local_scalar_type(
    context: &Context<'_>,
    local: u32,
    span: SourceSpan,
) -> Result<ScalarTy, ReflectError> {
    let ty = context.types.get(&local).copied().ok_or_else(|| {
        reflect_error(
            ReflectErrorKind::UndefinedLocal,
            span,
            format!("local _{local} has no declaration"),
        )
    })?;
    scalar_type(ty, context.target_width, span)
}

fn scalar_type(ty: MirType, target_width: u32, span: SourceSpan) -> Result<ScalarTy, ReflectError> {
    match ty {
        MirType::Bool => Ok(ScalarTy {
            width: 1,
            signed: false,
            boolean: true,
        }),
        MirType::Integer { width, signed } => Ok(ScalarTy {
            width,
            signed,
            boolean: false,
        }),
        MirType::Usize => Ok(ScalarTy {
            width: target_width,
            signed: false,
            boolean: false,
        }),
        MirType::Isize => Ok(ScalarTy {
            width: target_width,
            signed: true,
            boolean: false,
        }),
        MirType::ByteArray { .. } => Err(reflect_error(
            ReflectErrorKind::UnsupportedType,
            span,
            "byte array used where a scalar type is required",
        )),
    }
}

fn require_array(context: &Context<'_>, local: u32, span: SourceSpan) -> Result<(), ReflectError> {
    if local == context.array_local {
        Ok(())
    } else {
        Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("local _{local} is not the configured byte array"),
        ))
    }
}

fn require_type(
    actual: ScalarTy,
    expected: ScalarTy,
    span: SourceSpan,
) -> Result<(), ReflectError> {
    if actual == expected {
        Ok(())
    } else {
        Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("scalar type mismatch: found {actual:?}, expected {expected:?}"),
        ))
    }
}

fn require_bool(ty: ScalarTy, span: SourceSpan, what: &str) -> Result<(), ReflectError> {
    if ty.boolean {
        Ok(())
    } else {
        Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("{what} must be Boolean"),
        ))
    }
}

fn require_integer(ty: ScalarTy, span: SourceSpan, what: &str) -> Result<(), ReflectError> {
    if ty.boolean {
        Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("{what} must be an integer"),
        ))
    } else {
        Ok(())
    }
}

fn reflect_error(
    kind: ReflectErrorKind,
    span: SourceSpan,
    detail: impl Into<String>,
) -> ReflectError {
    ReflectError {
        kind,
        span: Some(span),
        detail: detail.into(),
    }
}

fn ir_error(span: SourceSpan, detail: impl Into<String>) -> ReflectError {
    reflect_error(ReflectErrorKind::IrConstruction, span, detail)
}
