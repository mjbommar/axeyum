//! Non-panicking symbolic execution for authenticated MIR scalar and byte-memory slices.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::error::Error;
use std::fmt;
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::SolverConfig;

use super::syntax::{
    BinaryOpcode, Function, IntegerConstant, MirType, Operand, ParseError, Rvalue, SourceSpan,
    StatementKind, TerminatorKind, parse_function,
};
use crate::reflect::llvm::loops::contracts::{
    instantiate_mir_relational_contract, verify_mir_relational_contract_against_body,
};
use crate::reflect::llvm::loops::{LoopReflectErrorKind, ScalarCallContract};

const MAX_MEMORY_BYTES: usize = 256;
const MAX_BLOCK_EXECUTIONS: usize = 4_096;
const REGISTERED_USIZE_WIDTH: u32 = 64;
const DEFAULT_CONTRACT_VERIFICATION_TIMEOUT: Duration = Duration::from_secs(2);
const U8_WRAPPING_ADD_INTRINSIC: &str = "core::num::<impl u8>::wrapping_add";

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

/// Named-function and target configuration for checked scalar MIR reflection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirScalarConfig {
    /// Function selected from the complete raw compiler MIR module.
    pub function: String,
    /// Target width used to interpret `usize` and `isize`.
    pub target_usize_width: u32,
}

impl MirScalarConfig {
    /// Creates a checked scalar reflection configuration.
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

/// Checked call-free scalar MIR reflection in a caller-owned arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckedMirScalar {
    /// Returned scalar value, meaningful when `panic` is false.
    pub result: MirValue,
    /// Path-conditioned Rust panic predicate.
    pub panic: TermId,
}

/// One source-attributed fresh result introduced by checked MIR call lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirRelationalCallSite {
    callee: String,
    span: SourceSpan,
    result_symbol: SymbolId,
    callee_panic: TermId,
    relation: TermId,
}

impl MirRelationalCallSite {
    /// Contracted MIR callee name.
    #[must_use]
    pub fn callee(&self) -> &str {
        &self.callee
    }

    /// Exact source span of the assigned direct call.
    #[must_use]
    pub const fn span(&self) -> SourceSpan {
        self.span
    }

    /// Fresh internal bit-vector symbol chosen for this call result.
    #[must_use]
    pub const fn result_symbol(&self) -> SymbolId {
        self.result_symbol
    }

    /// Instantiated checked callee panic predicate at this call site.
    #[must_use]
    pub const fn callee_panic(&self) -> TermId {
        self.callee_panic
    }

    /// Path-guarded instantiated relation for this call.
    #[must_use]
    pub const fn relation(&self) -> TermId {
        self.relation
    }
}

/// Checked scalar MIR reflection with one body-independent relational call.
#[derive(Debug)]
pub struct CheckedMirRelationalScalar {
    /// Returned modular value, meaningful when `panic` is false.
    pub result: MirValue,
    /// Caller panic predicate, including every separately verified callee
    /// panic summary.
    pub panic: TermId,
    /// Path-conditioned conjunction of verified call relations.
    pub assumptions: TermId,
    call_sites: Vec<MirRelationalCallSite>,
}

impl CheckedMirRelationalScalar {
    /// Ordered source call sites contributing relational assumptions.
    #[must_use]
    pub fn call_sites(&self) -> &[MirRelationalCallSite] {
        &self.call_sites
    }
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
    /// A direct call has no compatible opt-in verified contract.
    UnsupportedCall,
    /// A scalar contract is malformed, ill-sorted, or non-total for this slice.
    InvalidContract,
    /// A body, panic-summary, or postcondition claim was refuted.
    ContractDisproved,
    /// Contract verification exhausted its deterministic resource policy.
    ContractUnknown,
    /// Contract verification failed before producing a verdict.
    ContractSolver,
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

#[derive(Debug, Clone)]
struct VerifiedMirContract {
    contract: ScalarCallContract,
    argument_types: Vec<ScalarTy>,
    result_type: ScalarTy,
}

/// Deterministic inventory of relational scalar contracts proved against MIR.
///
/// Successful construction independently reflects each checked MIR body,
/// proves its declared panic predicate exactly, verifies the normal-return
/// relation, and then retains no body text or body terms.
#[derive(Debug, Clone)]
pub struct MirVerifiedContractResolver {
    contracts: BTreeMap<String, VerifiedMirContract>,
}

impl MirVerifiedContractResolver {
    /// Verifies relational contracts against exact checked MIR bodies.
    ///
    /// # Errors
    ///
    /// Fails closed for duplicate or malformed contracts, body/signature drift,
    /// a panic or relation counterexample, `Unknown`, or solver failure.
    pub fn from_contracts(entries: &[(ScalarCallContract, &str)]) -> Result<Self, ReflectError> {
        let config = SolverConfig::default().with_timeout(DEFAULT_CONTRACT_VERIFICATION_TIMEOUT);
        Self::from_contracts_with_config(entries, &config)
    }

    /// Verifies contracts with an explicit deterministic solver policy.
    ///
    /// # Errors
    ///
    /// Returns the same fail-closed classes as [`Self::from_contracts`].
    pub fn from_contracts_with_config(
        entries: &[(ScalarCallContract, &str)],
        config: &SolverConfig,
    ) -> Result<Self, ReflectError> {
        let mut contracts = BTreeMap::new();
        for (contract, body) in entries {
            if contracts.contains_key(contract.name()) {
                return Err(unlocated_error(
                    ReflectErrorKind::InvalidContract,
                    format!(
                        "duplicate verified MIR scalar contract `{}`",
                        contract.name()
                    ),
                ));
            }
            let verified = verify_mir_contract(contract, body, config)?;
            contracts.insert(contract.name().to_owned(), verified);
        }
        Ok(Self { contracts })
    }

    /// Ordered callee names owned by this verified MIR contract inventory.
    #[must_use]
    pub fn contract_names(&self) -> Vec<&str> {
        self.contracts.keys().map(String::as_str).collect()
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
    assumptions: TermId,
}

struct Outcome {
    result: ScalarValue,
    bytes: Vec<TermId>,
    panic: TermId,
    assumptions: TermId,
}

#[derive(Debug, Clone, Copy)]
struct MemoryRegion {
    local: u32,
    bytes: usize,
}

struct Context<'a> {
    function: &'a Function,
    blocks: BTreeMap<&'a str, usize>,
    types: BTreeMap<u32, MirType>,
    memory: Option<MemoryRegion>,
    allow_reassignment: bool,
    target_width: u32,
}

enum CallMode<'a> {
    Reject,
    Relational {
        resolver: &'a MirVerifiedContractResolver,
        function: &'a str,
        call_sites: Vec<MirRelationalCallSite>,
    },
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
    let context = validate_memory_function(&function, config.target_usize_width)?;
    let memory = context.memory.ok_or_else(|| {
        unlocated_error(
            ReflectErrorKind::RegionCount,
            "validated memory profile did not retain its bounded region",
        )
    })?;
    let mut arena = TermArena::new();
    let never = arena.bool_const(false);
    let always = arena.bool_const(true);
    let mut scalars = HashMap::new();
    let mut params = Vec::new();
    for parameter in &function.params {
        if parameter.local == memory.local {
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

    let mut input_symbols = Vec::with_capacity(memory.bytes);
    let mut bytes = Vec::with_capacity(memory.bytes);
    for index in 0..memory.bytes {
        let name = format!("mir.array._{}.byte.{index}", memory.local);
        let symbol = arena
            .declare(&name, Sort::BitVec(8))
            .map_err(|error| ir_error(function.span, error.to_string()))?;
        input_symbols.push(symbol);
        bytes.push(arena.var(symbol));
    }
    let mut calls = CallMode::Reject;
    let outcome = execute_block(
        &mut arena,
        &context,
        "bb0",
        State {
            scalars,
            bytes,
            panic: never,
            assumptions: always,
        },
        &mut 0,
        &mut calls,
    )?;
    Ok(CheckedMirMemory {
        arena,
        params,
        region: CheckedByteRegion {
            local: memory.local,
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

/// Reflects one call-free scalar MIR function into a caller-owned term arena.
///
/// This ordinary route intentionally rejects every parsed call terminator. Use
/// [`reflect_scalar_into_checked_with_contracts`] only after constructing a
/// [`MirVerifiedContractResolver`].
///
/// # Errors
///
/// Returns a stable located error for syntax, signature/type drift, calls,
/// cycles, invalid returns, or rejected IR construction.
pub fn reflect_scalar_into_checked(
    arena: &mut TermArena,
    params: &[TermId],
    input: &str,
    config: &MirScalarConfig,
) -> Result<CheckedMirScalar, ReflectError> {
    require_registered_target(config.target_usize_width)?;
    let function = parse_function(input, &config.function)?;
    let mut calls = CallMode::Reject;
    let outcome = reflect_scalar_parsed(
        arena,
        params,
        &function,
        config.target_usize_width,
        &mut calls,
    )?;
    Ok(CheckedMirScalar {
        result: mir_value(outcome.result),
        panic: outcome.panic,
    })
}

/// Reflects one scalar MIR caller through one independently MIR-verified
/// relational contract.
///
/// The resolver retains no callee body. This route introduces one fresh
/// internal result, propagates the verified callee panic summary, and returns
/// the normal-return relation separately.
///
/// # Errors
///
/// Fails closed for malformed callers, incompatible or absent contracts,
/// anything other than exactly one executed direct call, or rejected IR.
pub fn reflect_scalar_into_checked_with_contracts(
    arena: &mut TermArena,
    params: &[TermId],
    input: &str,
    config: &MirScalarConfig,
    resolver: &MirVerifiedContractResolver,
) -> Result<CheckedMirRelationalScalar, ReflectError> {
    require_registered_target(config.target_usize_width)?;
    let function = parse_function(input, &config.function)?;
    let mut calls = CallMode::Relational {
        resolver,
        function: &function.name,
        call_sites: Vec::new(),
    };
    let outcome = reflect_scalar_parsed(
        arena,
        params,
        &function,
        config.target_usize_width,
        &mut calls,
    )?;
    let CallMode::Relational { call_sites, .. } = calls else {
        unreachable!("relational MIR reflection constructed the relational call mode");
    };
    if call_sites.len() != 1 {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            function.span,
            format!(
                "checked relational MIR reflection requires exactly one direct call; found {}",
                call_sites.len()
            ),
        ));
    }
    Ok(CheckedMirRelationalScalar {
        result: mir_value(outcome.result),
        panic: outcome.panic,
        assumptions: outcome.assumptions,
        call_sites,
    })
}

fn require_registered_target(target_width: u32) -> Result<(), ReflectError> {
    if target_width == REGISTERED_USIZE_WIDTH {
        Ok(())
    } else {
        Err(unlocated_error(
            ReflectErrorKind::TargetWidth,
            format!(
                "registered MIR profile requires {REGISTERED_USIZE_WIDTH}-bit usize; found {target_width}"
            ),
        ))
    }
}

fn reflect_scalar_parsed(
    arena: &mut TermArena,
    params: &[TermId],
    function: &Function,
    target_width: u32,
    calls: &mut CallMode<'_>,
) -> Result<Outcome, ReflectError> {
    validate_call_inventory(function, calls)?;
    let context = validate_scalar_function(function, target_width)?;
    if params.len() != function.params.len() {
        return Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            function.span,
            format!(
                "checked MIR function expects {} parameters; received {}",
                function.params.len(),
                params.len()
            ),
        ));
    }
    let mut scalars = HashMap::new();
    for (parameter, term) in function.params.iter().zip(params.iter().copied()) {
        let ty = scalar_type(parameter.ty, target_width, parameter.span)?;
        let actual = arena.sort_of(term);
        if actual != ty.sort() {
            return Err(reflect_error(
                ReflectErrorKind::TypeMismatch,
                parameter.span,
                format!(
                    "parameter _{} expects {:?}; received {actual:?}",
                    parameter.local,
                    ty.sort()
                ),
            ));
        }
        scalars.insert(parameter.local, ScalarValue { term, ty });
    }
    let never = arena.bool_const(false);
    let always = arena.bool_const(true);
    execute_block(
        arena,
        &context,
        "bb0",
        State {
            scalars,
            bytes: Vec::new(),
            panic: never,
            assumptions: always,
        },
        &mut 0,
        calls,
    )
}

fn validate_call_inventory(function: &Function, calls: &CallMode<'_>) -> Result<(), ReflectError> {
    let call_spans = function
        .blocks
        .iter()
        .filter_map(|block| {
            matches!(
                &block.terminator.kind,
                TerminatorKind::Call { callee, .. } if callee != U8_WRAPPING_ADD_INTRINSIC
            )
            .then_some(block.terminator.span)
        })
        .collect::<Vec<_>>();
    match calls {
        CallMode::Reject => call_spans.first().copied().map_or(Ok(()), |span| {
            Err(reflect_error(
                ReflectErrorKind::UnsupportedCall,
                span,
                "checked scalar MIR is call-free unless an explicit verified resolver is supplied",
            ))
        }),
        CallMode::Relational { .. } if call_spans.len() != 1 => Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            function.span,
            format!(
                "checked relational MIR reflection requires exactly one static direct call; found {}",
                call_spans.len()
            ),
        )),
        CallMode::Relational { .. } => Ok(()),
    }
}

const fn mir_value(value: ScalarValue) -> MirValue {
    MirValue {
        value: value.term,
        width: value.ty.width,
        signed: value.ty.signed,
    }
}

fn validate_memory_function(
    function: &Function,
    target_width: u32,
) -> Result<Context<'_>, ReflectError> {
    let (types, array_local, array_bytes) = validate_types_and_region(function, target_width)?;
    let blocks = validate_blocks(function)?;
    let context = Context {
        function,
        blocks,
        types,
        memory: Some(MemoryRegion {
            local: array_local,
            bytes: array_bytes,
        }),
        allow_reassignment: false,
        target_width,
    };
    validate_acyclic(&context)?;
    Ok(context)
}

fn validate_scalar_function(
    function: &Function,
    target_width: u32,
) -> Result<Context<'_>, ReflectError> {
    let mut types = BTreeMap::new();
    for (local, ty, span) in function
        .params
        .iter()
        .map(|parameter| (parameter.local, parameter.ty, parameter.span))
        .chain(
            function
                .locals
                .iter()
                .map(|local| (local.local, local.ty, local.span)),
        )
    {
        if matches!(ty, MirType::ByteArray { .. }) {
            return Err(reflect_error(
                ReflectErrorKind::UnsupportedType,
                span,
                "byte arrays are outside the checked scalar MIR slice",
            ));
        }
        scalar_type(ty, target_width, span)?;
        if types.insert(local, ty).is_some() {
            return Err(reflect_error(
                ReflectErrorKind::DuplicateDefinition,
                span,
                format!("local _{local} is declared more than once"),
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
    let blocks = validate_blocks(function)?;
    let context = Context {
        function,
        blocks,
        types,
        memory: None,
        allow_reassignment: true,
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
        TerminatorKind::Call { return_target, .. } => vec![return_target],
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
    calls: &mut CallMode<'_>,
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
    execute_terminator(arena, context, state, source, executions, calls)
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
                if context
                    .memory
                    .is_some_and(|memory| *destination == memory.local)
                {
                    return Err(reflect_error(
                        ReflectErrorKind::TypeMismatch,
                        statement.span,
                        "whole-array assignment is outside the checked memory slice",
                    ));
                }
                if !context.allow_reassignment && state.scalars.contains_key(destination) {
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
                let in_bounds = access_in_bounds(
                    arena,
                    index,
                    memory_region(context, statement.span)?.bytes,
                    statement.span,
                )?;
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
    calls: &mut CallMode<'_>,
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
                assumptions: state.assumptions,
            })
        }
        TerminatorKind::Goto { target } => {
            execute_block(arena, context, target, state, executions, calls)
        }
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
            execute_block(arena, context, success, state, executions, calls)
        }
        TerminatorKind::Switch {
            discriminator,
            cases,
            otherwise,
        } => execute_switch(
            arena,
            context,
            &state,
            discriminator,
            cases,
            otherwise,
            source.terminator.span,
            executions,
            calls,
        ),
        TerminatorKind::Call {
            destination,
            callee,
            args,
            return_target,
        } => {
            lower_call(
                arena,
                context,
                &mut state,
                *destination,
                callee,
                args,
                source.terminator.span,
                calls,
            )?;
            execute_block(arena, context, return_target, state, executions, calls)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn execute_switch(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &State,
    discriminator: &Operand,
    cases: &[super::syntax::SwitchCase],
    otherwise: &str,
    span: SourceSpan,
    executions: &mut usize,
    calls: &mut CallMode<'_>,
) -> Result<Outcome, ReflectError> {
    let discriminator = lower_operand(arena, context, state, discriminator, span)?;
    let mut seen = BTreeSet::new();
    for case in cases {
        if !seen.insert(case.value) {
            return Err(reflect_error(
                ReflectErrorKind::TypeMismatch,
                span,
                format!("switch repeats case {}", case.value),
            ));
        }
    }
    let mut joined = execute_block(arena, context, otherwise, state.clone(), executions, calls)?;
    for case in cases.iter().rev() {
        let selected = switch_case(arena, discriminator, case.value, span)?;
        let branch = execute_block(
            arena,
            context,
            &case.target,
            state.clone(),
            executions,
            calls,
        )?;
        joined = join_outcomes(arena, selected, branch, joined, span)?;
    }
    Ok(joined)
}

#[allow(clippy::too_many_arguments)]
fn lower_call(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &mut State,
    destination: u32,
    callee: &str,
    args: &[Operand],
    span: SourceSpan,
    calls: &mut CallMode<'_>,
) -> Result<(), ReflectError> {
    if callee == U8_WRAPPING_ADD_INTRINSIC {
        return lower_u8_wrapping_add_call(arena, context, state, destination, args, span);
    }
    lower_verified_relational_call(
        arena,
        context,
        state,
        destination,
        callee,
        args,
        span,
        calls,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_verified_relational_call(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &mut State,
    destination: u32,
    callee: &str,
    args: &[Operand],
    span: SourceSpan,
    calls: &mut CallMode<'_>,
) -> Result<(), ReflectError> {
    let CallMode::Relational {
        resolver,
        function,
        call_sites,
    } = calls
    else {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            format!("direct call `{callee}` requires an opt-in verified MIR contract"),
        ));
    };
    if !call_sites.is_empty() {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            "checked relational MIR reflection admits exactly one direct call",
        ));
    }
    let verified = resolver.contracts.get(callee).ok_or_else(|| {
        reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            format!("direct call `{callee}` has no supplied MIR-verified contract"),
        )
    })?;
    if args.len() != verified.argument_types.len() {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            format!(
                "direct call `{callee}` supplies {} arguments; contract expects {}",
                args.len(),
                verified.argument_types.len()
            ),
        ));
    }
    let mut arguments = Vec::with_capacity(args.len());
    for (index, (argument, expected)) in args
        .iter()
        .zip(verified.argument_types.iter().copied())
        .enumerate()
    {
        let actual = lower_operand(arena, context, state, argument, span)?;
        if actual.ty != expected {
            return Err(reflect_error(
                ReflectErrorKind::UnsupportedCall,
                span,
                format!(
                    "direct call `{callee}` argument {index} has type {:?}; expected {expected:?}",
                    actual.ty
                ),
            ));
        }
        arguments.push(actual.term);
    }
    let destination_type = local_scalar_type(context, destination, span)?;
    if destination_type != verified.result_type {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            format!(
                "direct call `{callee}` destination _{destination} has type {destination_type:?}; expected {:?}",
                verified.result_type
            ),
        ));
    }
    let result_symbol =
        fresh_mir_result_symbol(arena, function, callee, span, verified.result_type.sort())?;
    let result = arena.var(result_symbol);
    let terms = instantiate_mir_relational_contract(arena, &verified.contract, &arguments, result)
        .map_err(|error| map_loop_contract_error(&error, Some(span)))?;
    let callee_panic = terms.panic_when;
    let combined_panic = arena
        .or(state.panic, callee_panic)
        .map_err(|error| ir_error(span, error.to_string()))?;
    let relation = arena
        .or(combined_panic, terms.ensures)
        .map_err(|error| ir_error(span, error.to_string()))?;
    state.assumptions = arena
        .and(state.assumptions, relation)
        .map_err(|error| ir_error(span, error.to_string()))?;
    state.scalars.insert(
        destination,
        ScalarValue {
            term: result,
            ty: verified.result_type,
        },
    );
    state.panic = combined_panic;
    call_sites.push(MirRelationalCallSite {
        callee: callee.to_owned(),
        span,
        result_symbol,
        callee_panic,
        relation,
    });
    Ok(())
}

fn lower_u8_wrapping_add_call(
    arena: &mut TermArena,
    context: &Context<'_>,
    state: &mut State,
    destination: u32,
    args: &[Operand],
    span: SourceSpan,
) -> Result<(), ReflectError> {
    let [left, right] = args else {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            format!(
                "registered u8 wrapping-add requires two arguments; found {}",
                args.len()
            ),
        ));
    };
    let byte = ScalarTy {
        width: 8,
        signed: false,
        boolean: false,
    };
    let left = lower_operand(arena, context, state, left, span)?;
    let right = lower_operand(arena, context, state, right, span)?;
    let destination_type = local_scalar_type(context, destination, span)?;
    if left.ty != byte || right.ty != byte || destination_type != byte {
        return Err(reflect_error(
            ReflectErrorKind::UnsupportedCall,
            span,
            "registered wrapping-add intrinsic requires two u8 arguments and a u8 destination",
        ));
    }
    let value = arena
        .bv_add(left.term, right.term)
        .map_err(|error| ir_error(span, error.to_string()))?;
    state.scalars.insert(
        destination,
        ScalarValue {
            term: value,
            ty: byte,
        },
    );
    Ok(())
}

fn fresh_mir_result_symbol(
    arena: &mut TermArena,
    function: &str,
    callee: &str,
    span: SourceSpan,
    sort: Sort,
) -> Result<SymbolId, ReflectError> {
    let stem = format!(
        "mir.contract.havoc.{function}.{callee}@{}.{}.result",
        span.line, span.column
    );
    let mut suffix = 0_usize;
    loop {
        let name = if suffix == 0 {
            stem.clone()
        } else {
            format!("{stem}.{suffix}")
        };
        if arena.find_internal_symbol(&name).is_none() {
            return arena
                .declare_internal(&name, sort)
                .map_err(|error| ir_error(span, error.to_string()));
        }
        suffix = suffix.checked_add(1).ok_or_else(|| {
            reflect_error(
                ReflectErrorKind::IrConstruction,
                span,
                "relational MIR result suffix overflowed",
            )
        })?;
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
        Rvalue::Cast { operand, target } => {
            let source = lower_operand(arena, context, state, operand, span)?;
            require_integer(source.ty, span, "cast source")?;
            let target = scalar_type(*target, context.target_width, span)?;
            require_integer(target, span, "cast destination")?;
            let term = match target.width.cmp(&source.ty.width) {
                std::cmp::Ordering::Greater if source.ty.signed => arena
                    .sign_ext(target.width - source.ty.width, source.term)
                    .map_err(|error| ir_error(span, error.to_string()))?,
                std::cmp::Ordering::Greater => arena
                    .zero_ext(target.width - source.ty.width, source.term)
                    .map_err(|error| ir_error(span, error.to_string()))?,
                std::cmp::Ordering::Less => arena
                    .extract(target.width - 1, 0, source.term)
                    .map_err(|error| ir_error(span, error.to_string()))?,
                std::cmp::Ordering::Equal => source.term,
            };
            Ok(ScalarValue { term, ty: target })
        }
        Rvalue::Not(operand) => {
            let operand = lower_operand(arena, context, state, operand, span)?;
            let term = if operand.ty.boolean {
                arena.not(operand.term)
            } else {
                arena.bv_not(operand.term)
            }
            .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue {
                term,
                ty: operand.ty,
            })
        }
        Rvalue::ArrayRead { array, index } => {
            require_array(context, *array, span)?;
            let index = local_scalar(state, *index, span)?;
            require_integer(index.ty, span, "array index")?;
            let in_bounds =
                access_in_bounds(arena, index, memory_region(context, span)?.bytes, span)?;
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
            lower_binary(arena, *op, left, right, span)
        }
    }
}

fn lower_binary(
    arena: &mut TermArena,
    op: BinaryOpcode,
    left: ScalarValue,
    right: ScalarValue,
    span: SourceSpan,
) -> Result<ScalarValue, ReflectError> {
    match op {
        BinaryOpcode::Add => {
            require_type(left.ty, right.ty, span)?;
            require_integer(left.ty, span, "addition operand")?;
            let term = arena
                .bv_add(left.term, right.term)
                .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue { term, ty: left.ty })
        }
        BinaryOpcode::Eq => {
            require_type(left.ty, right.ty, span)?;
            let term = arena
                .eq(left.term, right.term)
                .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue {
                term,
                ty: bool_type(),
            })
        }
        BinaryOpcode::Lt => {
            require_type(left.ty, right.ty, span)?;
            require_integer(left.ty, span, "less-than operand")?;
            let term = if left.ty.signed {
                arena.bv_slt(left.term, right.term)
            } else {
                arena.bv_ult(left.term, right.term)
            }
            .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue {
                term,
                ty: bool_type(),
            })
        }
        BinaryOpcode::BitAnd => {
            require_type(left.ty, right.ty, span)?;
            let term = if left.ty.boolean {
                arena.and(left.term, right.term)
            } else {
                arena.bv_and(left.term, right.term)
            }
            .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue { term, ty: left.ty })
        }
        BinaryOpcode::Shr => {
            require_integer(left.ty, span, "shifted operand")?;
            require_integer(right.ty, span, "shift amount")?;
            if left.ty.signed {
                return Err(reflect_error(
                    ReflectErrorKind::TypeMismatch,
                    span,
                    "the checked checksum slice admits only unsigned logical `Shr`",
                ));
            }
            let amount = resize_shift_amount(arena, right, left.ty.width, span)?;
            let term = arena
                .bv_lshr(left.term, amount)
                .map_err(|error| ir_error(span, error.to_string()))?;
            Ok(ScalarValue { term, ty: left.ty })
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

fn resize_shift_amount(
    arena: &mut TermArena,
    amount: ScalarValue,
    width: u32,
    span: SourceSpan,
) -> Result<TermId, ReflectError> {
    match amount.ty.width.cmp(&width) {
        std::cmp::Ordering::Greater => arena
            .extract(width - 1, 0, amount.term)
            .map_err(|error| ir_error(span, error.to_string())),
        std::cmp::Ordering::Less => arena
            .zero_ext(width - amount.ty.width, amount.term)
            .map_err(|error| ir_error(span, error.to_string())),
        std::cmp::Ordering::Equal => Ok(amount.term),
    }
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
    let assumptions = arena
        .ite(
            condition,
            then_outcome.assumptions,
            else_outcome.assumptions,
        )
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
        assumptions,
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

const fn bool_type() -> ScalarTy {
    ScalarTy {
        width: 1,
        signed: false,
        boolean: true,
    }
}

fn require_array(context: &Context<'_>, local: u32, span: SourceSpan) -> Result<(), ReflectError> {
    if context.memory.is_some_and(|memory| local == memory.local) {
        Ok(())
    } else {
        Err(reflect_error(
            ReflectErrorKind::TypeMismatch,
            span,
            format!("local _{local} is not the configured byte array"),
        ))
    }
}

fn memory_region(context: &Context<'_>, span: SourceSpan) -> Result<MemoryRegion, ReflectError> {
    context.memory.ok_or_else(|| {
        reflect_error(
            ReflectErrorKind::UnsupportedType,
            span,
            "memory operation is outside the checked scalar MIR slice",
        )
    })
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

fn verify_mir_contract(
    contract: &ScalarCallContract,
    body: &str,
    config: &SolverConfig,
) -> Result<VerifiedMirContract, ReflectError> {
    let function = parse_function(body, contract.name())?;
    if function.name != contract.name() {
        return Err(reflect_error(
            ReflectErrorKind::InvalidContract,
            function.span,
            format!(
                "MIR scalar contract `{}` was paired with body `{}`",
                contract.name(),
                function.name
            ),
        ));
    }
    let argument_types = function
        .params
        .iter()
        .map(|parameter| scalar_type(parameter.ty, REGISTERED_USIZE_WIDTH, parameter.span))
        .collect::<Result<Vec<_>, _>>()?;
    let argument_widths = argument_types
        .iter()
        .map(|argument| argument.width)
        .collect::<Vec<_>>();
    if argument_widths != contract.argument_widths() {
        return Err(reflect_error(
            ReflectErrorKind::InvalidContract,
            function.span,
            format!(
                "MIR scalar contract `{}` argument widths {:?} do not match body widths {argument_widths:?}",
                contract.name(),
                contract.argument_widths()
            ),
        ));
    }
    let result_type = scalar_type(function.return_ty, REGISTERED_USIZE_WIDTH, function.span)?;
    if result_type.width != contract.result_width() {
        return Err(reflect_error(
            ReflectErrorKind::InvalidContract,
            function.span,
            format!(
                "MIR scalar contract `{}` result width {} does not match body width {}",
                contract.name(),
                contract.result_width(),
                result_type.width
            ),
        ));
    }

    let mut arena = TermArena::new();
    let mut arguments = Vec::with_capacity(argument_types.len());
    for (index, ty) in argument_types.iter().copied().enumerate() {
        let symbol = arena
            .declare_internal(
                &format!("mir.contract.{}.arg{index}", contract.name()),
                ty.sort(),
            )
            .map_err(|error| ir_error(function.span, error.to_string()))?;
        arguments.push(arena.var(symbol));
    }
    let mut calls = CallMode::Reject;
    let body_terms = reflect_scalar_parsed(
        &mut arena,
        &arguments,
        &function,
        REGISTERED_USIZE_WIDTH,
        &mut calls,
    )?;
    verify_mir_relational_contract_against_body(
        &mut arena,
        contract,
        &arguments,
        body_terms.result.term,
        body_terms.panic,
        config,
    )
    .map_err(|error| map_loop_contract_error(&error, Some(function.span)))?;
    Ok(VerifiedMirContract {
        contract: contract.clone(),
        argument_types,
        result_type,
    })
}

fn map_loop_contract_error(
    error: &crate::reflect::llvm::loops::LoopReflectError,
    span: Option<SourceSpan>,
) -> ReflectError {
    let kind = match error.kind() {
        LoopReflectErrorKind::ContractDisproved => ReflectErrorKind::ContractDisproved,
        LoopReflectErrorKind::ContractUnknown => ReflectErrorKind::ContractUnknown,
        LoopReflectErrorKind::ContractSolver => ReflectErrorKind::ContractSolver,
        LoopReflectErrorKind::IrConstruction => ReflectErrorKind::IrConstruction,
        _ => ReflectErrorKind::InvalidContract,
    };
    ReflectError {
        kind,
        span,
        detail: error.to_string(),
    }
}

fn unlocated_error(kind: ReflectErrorKind, detail: impl Into<String>) -> ReflectError {
    ReflectError {
        kind,
        span: None,
        detail: detail.into(),
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
