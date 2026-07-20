//! Verified exact and relational scalar contracts for checked LLVM calls.

use std::collections::{BTreeMap, HashMap};
use std::time::Duration;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use super::{
    BuildError, BuildPhase, CallRequirementSite, CallRequirementTerms, DirectCallResolver,
    LoopReflectError, LoopReflectErrorKind, LoweredCall, loop_error, scalar_width, sort_for_width,
    validate_direct_callee,
};
use crate::reflect::llvm::checked::{
    DefinedValue, LoweredCheckedCall, ReflectError, ReflectErrorKind, ScalarCallLowerer,
    located_reflect_error, reflect_parsed_components_into,
    reflect_parsed_components_into_with_calls, resolve,
};
use crate::reflect::llvm::syntax::{
    DirectCallArgument, ScalarInstruction, ScalarInstructionKind, SourceSpan, parse_function,
};

const MAX_CONTRACT_EXPRESSION_NODES: usize = 256;
const DEFAULT_CONTRACT_VERIFICATION_TIMEOUT: Duration = Duration::from_secs(2);

/// One bounded expression in the scalar LLVM contract language.
///
/// The language is intentionally smaller than the checked LLVM instruction
/// surface. It owns only the Boolean/BV operations needed by ADR-0296's exact
/// `leaf` contract and ADR-0298's relational checksum contract. Every
/// expression is independently lowered and sort-checked before verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarContractExpr {
    /// One formal scalar argument by zero-based signature position.
    Argument(usize),
    /// The fresh scalar result of a relational contract call.
    ///
    /// This is accepted only in relational `ensures` and relational result
    /// definedness. Exact contracts and preconditions cannot refer to it.
    Result,
    /// A Boolean constant.
    Bool(bool),
    /// A bit-vector constant (`width` must be in `2..=128`).
    BitVec {
        /// Bit-vector width in `2..=128`.
        width: u32,
        /// Unsigned value, rejected if it does not fit `width`.
        value: u128,
    },
    /// Boolean negation.
    Not(Box<Self>),
    /// Boolean conjunction.
    And(Box<Self>, Box<Self>),
    /// Strict same-sort equality.
    Eq(Box<Self>, Box<Self>),
    /// Strict Boolean-guarded, same-sort conditional.
    Ite {
        /// Boolean selection condition.
        condition: Box<Self>,
        /// Value selected when `condition` is true.
        when_true: Box<Self>,
        /// Value selected when `condition` is false.
        when_false: Box<Self>,
    },
    /// Modular bit-vector addition.
    BvAdd(Box<Self>, Box<Self>),
    /// Modular bit-vector multiplication.
    BvMul(Box<Self>, Box<Self>),
    /// Signed-addition overflow predicate.
    BvSignedAddOverflow(Box<Self>, Box<Self>),
    /// Unsigned-addition overflow predicate.
    BvUnsignedAddOverflow(Box<Self>, Box<Self>),
    /// Signed-multiplication overflow predicate.
    BvSignedMulOverflow(Box<Self>, Box<Self>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ScalarContractResult {
    Exact(ScalarContractExpr),
    Relational { ensures: ScalarContractExpr },
}

/// An explicit exact or relational contract for one scalar LLVM callee.
///
/// ADR-0296 supplies exact functional results, ADR-0297 adds guarded body
/// verification and explicit loop-call requirement obligations, and ADR-0298
/// adds an opt-in relational result for checked straight-line callers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCallContract {
    name: String,
    argument_widths: Vec<u32>,
    result_width: u32,
    requires: ScalarContractExpr,
    immediate_defined: ScalarContractExpr,
    result: ScalarContractResult,
    result_defined: ScalarContractExpr,
}

impl ScalarCallContract {
    /// Creates one exact scalar contract declaration.
    ///
    /// Expression sorts are checked when the contract is verified in a term
    /// arena. This constructor checks the source-independent signature and
    /// bounded-expression inventory without executing solver work.
    ///
    /// # Errors
    ///
    /// Returns [`LoopReflectErrorKind::InvalidContract`] for an empty name,
    /// unsupported scalar width, or an expression inventory larger than the
    /// ADR-0296 bound.
    pub fn new(
        name: impl Into<String>,
        argument_widths: Vec<u32>,
        result_width: u32,
        requires: ScalarContractExpr,
        immediate_defined: ScalarContractExpr,
        result: ScalarContractExpr,
        result_defined: ScalarContractExpr,
    ) -> Result<Self, LoopReflectError> {
        Self::new_with_result(
            name,
            argument_widths,
            result_width,
            requires,
            immediate_defined,
            ScalarContractResult::Exact(result),
            result_defined,
        )
    }

    /// Creates one relational scalar contract declaration.
    ///
    /// `ensures` may refer to [`ScalarContractExpr::Result`]. The actual call
    /// result is a fresh internal symbol constrained by that Boolean relation;
    /// it is not replaced by the verified body result.
    ///
    /// # Errors
    ///
    /// Returns [`LoopReflectErrorKind::InvalidContract`] for the same bounded
    /// signature/expression failures as [`Self::new`], for a forbidden
    /// `Result` reference, or when later strict sort checking rejects a
    /// component during resolver construction.
    pub fn new_relational(
        name: impl Into<String>,
        argument_widths: Vec<u32>,
        result_width: u32,
        requires: ScalarContractExpr,
        immediate_defined: ScalarContractExpr,
        ensures: ScalarContractExpr,
        result_defined: ScalarContractExpr,
    ) -> Result<Self, LoopReflectError> {
        Self::new_with_result(
            name,
            argument_widths,
            result_width,
            requires,
            immediate_defined,
            ScalarContractResult::Relational { ensures },
            result_defined,
        )
    }

    fn new_with_result(
        name: impl Into<String>,
        argument_widths: Vec<u32>,
        result_width: u32,
        requires: ScalarContractExpr,
        immediate_defined: ScalarContractExpr,
        result: ScalarContractResult,
        result_defined: ScalarContractExpr,
    ) -> Result<Self, LoopReflectError> {
        let name = name.into();
        if name.is_empty() {
            return Err(contract_error("scalar contract name cannot be empty"));
        }
        for (index, width) in argument_widths.iter().copied().enumerate() {
            if !(1..=128).contains(&width) {
                return Err(contract_error(&format!(
                    "scalar contract `@{name}` argument {index} has unsupported i{width} width"
                )));
            }
        }
        if !(1..=128).contains(&result_width) {
            return Err(contract_error(&format!(
                "scalar contract `@{name}` has unsupported i{result_width} result width"
            )));
        }
        let contract = Self {
            name,
            argument_widths,
            result_width,
            requires,
            immediate_defined,
            result,
            result_defined,
        };
        let relational = matches!(contract.result, ScalarContractResult::Relational { .. });
        let result_expression = match &contract.result {
            ScalarContractResult::Exact(result) => result,
            ScalarContractResult::Relational { ensures } => ensures,
        };
        let expressions = [
            (&contract.requires, false, "requires"),
            (&contract.immediate_defined, false, "immediate definedness"),
            (
                result_expression,
                relational,
                if relational {
                    "ensures"
                } else {
                    "result value"
                },
            ),
            (&contract.result_defined, relational, "result definedness"),
        ];
        let total_nodes = expressions.into_iter().try_fold(
            0_usize,
            |total, (expression, allow_result, component)| {
                let nodes = validate_contract_expression(
                    expression,
                    contract.argument_widths.len(),
                    &contract.name,
                    allow_result,
                    component,
                )?;
                total
                    .checked_add(nodes)
                    .ok_or_else(|| contract_error("scalar contract expression count overflowed"))
            },
        )?;
        if total_nodes > MAX_CONTRACT_EXPRESSION_NODES {
            return Err(contract_error(&format!(
                "scalar contract `@{}` has {total_nodes} expression nodes, limit is {MAX_CONTRACT_EXPRESSION_NODES}",
                contract.name
            )));
        }
        Ok(contract)
    }

    /// Contracted LLVM callee name without `@`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Ordered scalar argument widths.
    #[must_use]
    pub fn argument_widths(&self) -> &[u32] {
        &self.argument_widths
    }

    /// Scalar result width.
    #[must_use]
    pub fn result_width(&self) -> u32 {
        self.result_width
    }
}

#[derive(Debug, Clone)]
struct VerifiedScalarContract {
    contract: ScalarCallContract,
}

/// Deterministic inventory of scalar contracts proved against exact bodies.
///
/// Successful construction discards every parsed callee body. Callers using
/// this resolver can instantiate only the verified explicit contract, making
/// the modular boundary observable rather than selecting a second body path.
#[derive(Debug, Clone)]
pub struct VerifiedContractResolver {
    contracts: BTreeMap<String, VerifiedScalarContract>,
}

impl VerifiedContractResolver {
    /// Verifies exact or relational scalar contracts against checked bodies.
    ///
    /// Requirements must be satisfiable. Exact term/conjunction matches use the
    /// bounded structural checker; other body/contract equalities are proved
    /// under `requires` with a two-second default timeout so a difficult
    /// contract cannot turn construction into an unbounded query.
    ///
    /// # Errors
    ///
    /// Fails closed for malformed or duplicate contracts, body/signature drift,
    /// a replayed counterexample, a classified `Unknown`, or a solver error.
    pub fn from_contracts(
        entries: &[(ScalarCallContract, &str)],
    ) -> Result<Self, LoopReflectError> {
        let config = SolverConfig::default().with_timeout(DEFAULT_CONTRACT_VERIFICATION_TIMEOUT);
        Self::from_contracts_with_config(entries, &config)
    }

    /// Verifies contracts with an explicit solver resource policy.
    ///
    /// This entry point exists so callers can make undecided verification
    /// reproducible. An exhausted budget is
    /// [`LoopReflectErrorKind::ContractUnknown`], never acceptance.
    ///
    /// # Errors
    ///
    /// Returns the same fail-closed errors as [`Self::from_contracts`].
    pub fn from_contracts_with_config(
        entries: &[(ScalarCallContract, &str)],
        config: &SolverConfig,
    ) -> Result<Self, LoopReflectError> {
        let mut contracts = BTreeMap::new();
        for (contract, body) in entries {
            if contracts.contains_key(contract.name()) {
                return Err(contract_error(&format!(
                    "duplicate verified scalar contract `@{}`",
                    contract.name()
                )));
            }
            verify_scalar_contract(contract, body, config)?;
            contracts.insert(
                contract.name.clone(),
                VerifiedScalarContract {
                    contract: contract.clone(),
                },
            );
        }
        Ok(Self { contracts })
    }

    /// Ordered callee names owned by this verified contract inventory.
    #[must_use]
    pub fn contract_names(&self) -> Vec<&str> {
        self.contracts.keys().map(String::as_str).collect()
    }

    fn validate_call(&self, instruction: &ScalarInstruction) -> Result<(), LoopReflectError> {
        let ScalarInstructionKind::DirectCall {
            result_width,
            callee,
            args,
            ..
        } = &instruction.kind
        else {
            return Ok(());
        };
        let verified = self.contracts.get(callee).ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!("direct call `@{callee}` has no supplied verified scalar contract"),
            )
        })?;
        let contract = &verified.contract;
        if *result_width != contract.result_width {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!(
                    "direct call `@{callee}` declares i{result_width}, contract returns i{}",
                    contract.result_width
                ),
            ));
        }
        if args.len() != contract.argument_widths.len() {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!(
                    "direct call `@{callee}` supplies {} arguments, contract declares {}",
                    args.len(),
                    contract.argument_widths.len()
                ),
            ));
        }
        for (index, (argument, expected)) in args.iter().zip(&contract.argument_widths).enumerate()
        {
            if argument.width != *expected {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(instruction.span),
                    &format!(
                        "direct call `@{callee}` argument {index} declares i{}, contract expects i{expected}",
                        argument.width
                    ),
                ));
            }
            if !argument.noundef {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(instruction.span),
                    &format!(
                        "direct call `@{callee}` argument {index} must retain the `noundef` boundary"
                    ),
                ));
            }
        }
        Ok(())
    }

    pub(super) fn lower_call(
        &self,
        arena: &mut TermArena,
        env: &HashMap<String, DefinedValue>,
        instruction: &ScalarInstruction,
    ) -> Result<LoweredCall, BuildError> {
        self.validate_call(instruction).map_err(BuildError::call)?;
        let ScalarInstructionKind::DirectCall {
            dest, callee, args, ..
        } = &instruction.kind
        else {
            return Err(BuildError::call(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                "contract resolver received a non-call instruction",
            )));
        };
        let contract = &self.contracts[callee].contract;
        if matches!(contract.result, ScalarContractResult::Relational { .. }) {
            return Err(BuildError::call(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!(
                    "relational contract `@{callee}` requires the checked straight-line havoc route; loop havoc is not admitted"
                ),
            )));
        }
        let mut values = Vec::with_capacity(args.len());
        let mut argument_defined = arena.bool_const(true);
        for argument in args {
            let resolved = resolve(
                arena,
                env,
                &argument.value,
                argument.width,
                instruction.span,
            )
            .map_err(BuildError::reflection)?;
            values.push(resolved.value);
            argument_defined = arena
                .and(argument_defined, resolved.defined)
                .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
        }
        let terms = instantiate_scalar_contract(arena, contract, &values, None)
            .map_err(BuildError::call)?;
        let InstantiatedContractResult::Exact(result) = terms.result else {
            unreachable!("relational contracts were rejected before exact loop lowering");
        };
        let result_defined = arena
            .and(argument_defined, terms.result_defined)
            .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
        let immediate = arena
            .and(argument_defined, terms.immediate_defined)
            .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
        let requirement = if matches!(contract.requires, ScalarContractExpr::Bool(true)) {
            None
        } else {
            let requirement_satisfied = arena
                .and(argument_defined, terms.requires)
                .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
            let requirement_negated = arena
                .not(terms.requires)
                .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
            let requirement_violated = arena
                .and(argument_defined, requirement_negated)
                .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
            Some(CallRequirementTerms {
                satisfied: requirement_satisfied,
                violated: requirement_violated,
            })
        };
        Ok(LoweredCall {
            destination: dest.clone(),
            value: DefinedValue {
                defined: result_defined,
                value: result,
                width: contract.result_width,
            },
            immediate_defined: immediate,
            requirement,
        })
    }
}

/// One source-attributed fresh result introduced by relational call lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationalScalarCallSite {
    callee: String,
    span: SourceSpan,
    result_symbol: SymbolId,
    requirement: TermId,
    relation: TermId,
}

impl RelationalScalarCallSite {
    /// Contracted LLVM callee name without `@`.
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

    /// Instantiated callee requirement over the actual arguments.
    #[must_use]
    pub const fn requirement(&self) -> TermId {
        self.requirement
    }

    /// Guarded per-call relational assumption over arguments and result.
    #[must_use]
    pub const fn relation(&self) -> TermId {
        self.relation
    }
}

/// One checked straight-line scalar reflection with explicit relational calls.
///
/// `assumptions` is a distinct logical channel: supply it as a hypothesis when
/// proving a property of `result`. It is not LLVM poison or immediate undefined
/// behavior, both of which remain in `result.defined`.
#[derive(Debug)]
pub struct CheckedRelationalScalarReflected {
    /// Returned modular value plus LLVM definedness.
    pub result: DefinedValue,
    /// Conjunction of every verified relational call assumption.
    pub assumptions: TermId,
    call_sites: Vec<RelationalScalarCallSite>,
}

impl CheckedRelationalScalarReflected {
    /// Ordered source call sites contributing relational assumptions.
    #[must_use]
    pub fn call_sites(&self) -> &[RelationalScalarCallSite] {
        &self.call_sites
    }
}

/// Reflects one straight-line scalar LLVM caller through one verified
/// relational contract.
///
/// The callee body was checked and discarded when `resolver` was constructed.
/// This function introduces a fresh internal result symbol and returns its
/// verified postcondition separately in
/// [`CheckedRelationalScalarReflected::assumptions`]. The ordinary checked
/// reflector remains call-free.
///
/// # Errors
///
/// Returns a located [`LoopReflectError`] for malformed caller syntax,
/// missing/incompatible contracts, exact rather than relational contracts,
/// non-literal-true requirements, more or fewer than one call, or rejected IR
/// construction. Calls in loops, multi-block CFGs, memory, and nested callees
/// remain outside this entry point.
pub fn reflect_scalar_into_checked_with_contracts(
    arena: &mut TermArena,
    params: &[TermId],
    ll: &str,
    resolver: &VerifiedContractResolver,
) -> Result<CheckedRelationalScalarReflected, LoopReflectError> {
    let function = parse_function(ll)?;
    let mut lowerer = RelationalScalarCallLowerer::new(resolver, &function.name);
    let components =
        reflect_parsed_components_into_with_calls(arena, params, &function, &mut lowerer).map_err(
            |error| super::loop_build_error(BuildError::reflection(error), BuildPhase::Transition),
        )?;
    if lowerer.call_sites.len() != 1 {
        return Err(loop_error(
            LoopReflectErrorKind::UnsupportedCall,
            Some(function.span),
            &format!(
                "checked relational scalar reflection requires exactly one direct call; found {}",
                lowerer.call_sites.len()
            ),
        ));
    }
    let defined = arena
        .and(components.immediate_defined, components.result.defined)
        .map_err(|error| {
            loop_error(
                LoopReflectErrorKind::IrConstruction,
                Some(function.span),
                &format!("relational scalar caller IR construction failed: {error}"),
            )
        })?;
    Ok(CheckedRelationalScalarReflected {
        result: DefinedValue {
            defined,
            ..components.result
        },
        assumptions: components.assumptions,
        call_sites: lowerer.call_sites,
    })
}

struct RelationalScalarCallLowerer<'a> {
    resolver: &'a VerifiedContractResolver,
    function: String,
    call_sites: Vec<RelationalScalarCallSite>,
}

impl<'a> RelationalScalarCallLowerer<'a> {
    fn new(resolver: &'a VerifiedContractResolver, function: &str) -> Self {
        Self {
            resolver,
            function: function.to_owned(),
            call_sites: Vec::new(),
        }
    }

    fn fresh_result_symbol(
        &self,
        arena: &mut TermArena,
        callee: &str,
        span: SourceSpan,
        width: u32,
    ) -> Result<SymbolId, ReflectError> {
        let stem = format!(
            "llvm.contract.havoc.{}.{}@{}.{}.result",
            self.function, callee, span.line, span.column
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
                    .declare_internal(&name, sort_for_width(width))
                    .map_err(|error| {
                        located_reflect_error(
                            ReflectErrorKind::IrConstruction,
                            Some(span),
                            format!("relational call result declaration failed: {error}"),
                        )
                    });
            }
            suffix = suffix.checked_add(1).ok_or_else(|| {
                located_reflect_error(
                    ReflectErrorKind::IrConstruction,
                    Some(span),
                    "relational call result suffix overflowed",
                )
            })?;
        }
    }
}

fn relational_ir_error(span: SourceSpan, error: &impl ToString) -> ReflectError {
    located_reflect_error(
        ReflectErrorKind::IrConstruction,
        Some(span),
        error.to_string(),
    )
}

fn resolve_relational_arguments(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    args: &[DirectCallArgument],
    span: SourceSpan,
) -> Result<(Vec<TermId>, TermId), ReflectError> {
    let mut values = Vec::with_capacity(args.len());
    let mut argument_defined = arena.bool_const(true);
    for argument in args {
        let resolved = resolve(arena, env, &argument.value, argument.width, span)?;
        values.push(resolved.value);
        argument_defined = arena
            .and(argument_defined, resolved.defined)
            .map_err(|error| relational_ir_error(span, &error))?;
    }
    Ok((values, argument_defined))
}

struct LoweredRelationalTerms {
    result_defined: TermId,
    immediate_defined: TermId,
    relation: TermId,
}

fn lower_relational_terms(
    arena: &mut TermArena,
    argument_defined: TermId,
    contract: &InstantiatedScalarContract,
    ensures: TermId,
    span: SourceSpan,
) -> Result<LoweredRelationalTerms, ReflectError> {
    let result_defined = arena
        .and(argument_defined, contract.result_defined)
        .map_err(|error| relational_ir_error(span, &error))?;
    let immediate_defined = arena
        .and(argument_defined, contract.immediate_defined)
        .map_err(|error| relational_ir_error(span, &error))?;
    let arguments_undefined = arena
        .not(argument_defined)
        .map_err(|error| relational_ir_error(span, &error))?;
    let immediate_undefined = arena
        .not(contract.immediate_defined)
        .map_err(|error| relational_ir_error(span, &error))?;
    let result_undefined = arena
        .not(contract.result_defined)
        .map_err(|error| relational_ir_error(span, &error))?;
    let result_relation = arena
        .or(result_undefined, ensures)
        .map_err(|error| relational_ir_error(span, &error))?;
    let after_immediate = arena
        .or(immediate_undefined, result_relation)
        .map_err(|error| relational_ir_error(span, &error))?;
    let required_relation = arena
        .and(contract.requires, after_immediate)
        .map_err(|error| relational_ir_error(span, &error))?;
    let relation = arena
        .or(arguments_undefined, required_relation)
        .map_err(|error| relational_ir_error(span, &error))?;
    Ok(LoweredRelationalTerms {
        result_defined,
        immediate_defined,
        relation,
    })
}

impl ScalarCallLowerer for RelationalScalarCallLowerer<'_> {
    fn lower_call(
        &mut self,
        arena: &mut TermArena,
        env: &HashMap<String, DefinedValue>,
        instruction: &ScalarInstruction,
    ) -> Result<LoweredCheckedCall, ReflectError> {
        self.resolver.validate_call(instruction).map_err(|error| {
            located_reflect_error(
                ReflectErrorKind::UnsupportedCall,
                error.span().or(Some(instruction.span)),
                error.to_string(),
            )
        })?;
        let ScalarInstructionKind::DirectCall {
            dest, callee, args, ..
        } = &instruction.kind
        else {
            return Err(located_reflect_error(
                ReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                "relational contract resolver received a non-call instruction",
            ));
        };
        let contract = &self.resolver.contracts[callee].contract;
        if !matches!(contract.requires, ScalarContractExpr::Bool(true)) {
            return Err(located_reflect_error(
                ReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                format!(
                    "relational straight-line call `@{callee}` requires a literal-true requirement in ADR-0298"
                ),
            ));
        }
        if matches!(contract.result, ScalarContractResult::Exact(_)) {
            return Err(located_reflect_error(
                ReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                format!(
                    "exact contract `@{callee}` belongs to the exact loop route, not relational havoc"
                ),
            ));
        }

        let (values, argument_defined) =
            resolve_relational_arguments(arena, env, args, instruction.span)?;
        let result_symbol =
            self.fresh_result_symbol(arena, callee, instruction.span, contract.result_width)?;
        let result = arena.var(result_symbol);
        let terms = instantiate_scalar_contract(arena, contract, &values, Some(result))
            .map_err(|error| relational_ir_error(instruction.span, &error))?;
        let InstantiatedContractResult::Relational { ensures } = terms.result else {
            unreachable!("exact contracts were rejected before relational lowering");
        };
        let lowered =
            lower_relational_terms(arena, argument_defined, &terms, ensures, instruction.span)?;

        self.call_sites.push(RelationalScalarCallSite {
            callee: callee.clone(),
            span: instruction.span,
            result_symbol,
            requirement: terms.requires,
            relation: lowered.relation,
        });
        Ok(LoweredCheckedCall {
            destination: dest.clone(),
            value: DefinedValue {
                value: result,
                defined: lowered.result_defined,
                width: contract.result_width,
            },
            immediate_defined: lowered.immediate_defined,
            assumption: lowered.relation,
        })
    }
}

#[derive(Debug, Clone)]
pub(super) enum CallResolver {
    DirectBody(DirectCallResolver),
    VerifiedContract(VerifiedContractResolver),
}

impl CallResolver {
    pub(super) fn validate_call(
        &self,
        instruction: &ScalarInstruction,
    ) -> Result<(), LoopReflectError> {
        match self {
            Self::DirectBody(resolver) => resolver.validate_call(instruction),
            Self::VerifiedContract(resolver) => resolver.validate_call(instruction),
        }
    }

    pub(super) fn lower_call(
        &self,
        arena: &mut TermArena,
        env: &HashMap<String, DefinedValue>,
        instruction: &ScalarInstruction,
    ) -> Result<LoweredCall, BuildError> {
        match self {
            Self::DirectBody(resolver) => resolver.lower_call(arena, env, instruction),
            Self::VerifiedContract(resolver) => resolver.lower_call(arena, env, instruction),
        }
    }

    pub(super) fn requirement_site(
        &self,
        instruction: &ScalarInstruction,
    ) -> Option<CallRequirementSite> {
        let Self::VerifiedContract(resolver) = self else {
            return None;
        };
        let ScalarInstructionKind::DirectCall { callee, .. } = &instruction.kind else {
            return None;
        };
        let verified = resolver.contracts.get(callee)?;
        if matches!(verified.contract.requires, ScalarContractExpr::Bool(true)) {
            return None;
        }
        Some(CallRequirementSite {
            callee: callee.clone(),
            span: instruction.span,
        })
    }
}

#[derive(Clone, Copy)]
enum InstantiatedContractResult {
    Exact(TermId),
    Relational { ensures: TermId },
}

#[derive(Clone, Copy)]
struct InstantiatedScalarContract {
    requires: TermId,
    immediate_defined: TermId,
    result: InstantiatedContractResult,
    result_defined: TermId,
}

fn verify_scalar_contract(
    contract: &ScalarCallContract,
    body: &str,
    config: &SolverConfig,
) -> Result<(), LoopReflectError> {
    let function = parse_function(body)?;
    validate_direct_callee(&function)?;
    if function.name != contract.name {
        return Err(contract_error(&format!(
            "scalar contract `@{}` was paired with body `@{}`",
            contract.name, function.name
        )));
    }
    let body_widths = function
        .params
        .iter()
        .map(|parameter| scalar_width(&parameter.ty))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| contract_error("validated scalar body has a non-scalar parameter"))?;
    if body_widths != contract.argument_widths {
        return Err(contract_error(&format!(
            "scalar contract `@{}` argument widths {:?} do not match body widths {body_widths:?}",
            contract.name, contract.argument_widths
        )));
    }
    let body_result_width = scalar_width(&function.return_ty)
        .ok_or_else(|| contract_error("validated scalar body has a non-scalar result"))?;
    if body_result_width != contract.result_width {
        return Err(contract_error(&format!(
            "scalar contract `@{}` result i{} does not match body result i{body_result_width}",
            contract.name, contract.result_width
        )));
    }

    let mut arena = TermArena::new();
    let mut params = Vec::with_capacity(body_widths.len());
    for (index, width) in body_widths.iter().copied().enumerate() {
        let symbol = arena
            .declare(
                &format!("llvm.contract.{}.arg{index}", contract.name),
                sort_for_width(width),
            )
            .map_err(|error| contract_error(&error.to_string()))?;
        params.push(arena.var(symbol));
    }
    let body_terms = reflect_parsed_components_into(&mut arena, &params, &function)
        .map_err(|error| contract_error(&format!("contract body is not executable: {error}")))?;
    let body_result = matches!(contract.result, ScalarContractResult::Relational { .. })
        .then_some(body_terms.result.value);
    let contract_terms = instantiate_scalar_contract(&mut arena, contract, &params, body_result)?;

    verify_contract_satisfiable(&mut arena, contract_terms.requires, config, &contract.name)?;
    verify_contract_equal_under(
        &mut arena,
        contract_terms.requires,
        contract_terms.immediate_defined,
        body_terms.immediate_defined,
        config,
        &contract.name,
        "immediate definedness",
    )?;
    verify_contract_equal_under(
        &mut arena,
        contract_terms.requires,
        contract_terms.result_defined,
        body_terms.result.defined,
        config,
        &contract.name,
        "result definedness",
    )?;
    match contract_terms.result {
        InstantiatedContractResult::Exact(result) => verify_contract_equal_under(
            &mut arena,
            contract_terms.requires,
            result,
            body_terms.result.value,
            config,
            &contract.name,
            "result value",
        ),
        InstantiatedContractResult::Relational { ensures } => verify_contract_postcondition(
            &mut arena,
            contract_terms.requires,
            body_terms.result.defined,
            ensures,
            config,
            &contract.name,
        ),
    }
}

fn verify_contract_postcondition(
    arena: &mut TermArena,
    requires: TermId,
    body_result_defined: TermId,
    ensures: TermId,
    config: &SolverConfig,
    name: &str,
) -> Result<(), LoopReflectError> {
    let outside_domain = arena
        .not(requires)
        .map_err(|error| contract_error(&error.to_string()))?;
    let undefined_result = arena
        .not(body_result_defined)
        .map_err(|error| contract_error(&error.to_string()))?;
    let outside_defined_result = arena
        .or(outside_domain, undefined_result)
        .map_err(|error| contract_error(&error.to_string()))?;
    let guarded = arena
        .or(outside_defined_result, ensures)
        .map_err(|error| contract_error(&error.to_string()))?;
    prove_contract_goal(arena, guarded, config, name, "relational ensures")
}

fn verify_contract_satisfiable(
    arena: &mut TermArena,
    requires: TermId,
    config: &SolverConfig,
    name: &str,
) -> Result<(), LoopReflectError> {
    match arena.node(requires) {
        TermNode::BoolConst(true) => return Ok(()),
        TermNode::BoolConst(false) => {
            return Err(loop_error(
                LoopReflectErrorKind::ContractDisproved,
                None,
                &format!("scalar contract `@{name}` requires is unsatisfiable"),
            ));
        }
        _ => {}
    }
    let impossible = arena
        .not(requires)
        .map_err(|error| contract_error(&error.to_string()))?;
    match prove(arena, &[], impossible, config) {
        Ok(ProofOutcome::Disproved(_)) => Ok(()),
        Ok(ProofOutcome::Proved(_)) => Err(loop_error(
            LoopReflectErrorKind::ContractDisproved,
            None,
            &format!("scalar contract `@{name}` requires is unsatisfiable"),
        )),
        Ok(ProofOutcome::Unknown(reason)) => Err(loop_error(
            LoopReflectErrorKind::ContractUnknown,
            None,
            &format!(
                "scalar contract `@{name}` requirement satisfiability is undecided: {reason:?}"
            ),
        )),
        Err(error) => Err(loop_error(
            LoopReflectErrorKind::ContractSolver,
            None,
            &format!(
                "scalar contract `@{name}` solver failure for requirement satisfiability: {error}"
            ),
        )),
    }
}

fn verify_contract_equal_under(
    arena: &mut TermArena,
    requires: TermId,
    left: TermId,
    right: TermId,
    config: &SolverConfig,
    name: &str,
    component: &str,
) -> Result<(), LoopReflectError> {
    if left == right
        || (arena.sort_of(left) == Sort::Bool
            && arena.sort_of(right) == Sort::Bool
            && boolean_conjunction_equal(arena, left, right))
    {
        return Ok(());
    }
    if arena.sort_of(left) == Sort::Bool && arena.sort_of(right) == Sort::Bool {
        if matches!(arena.node(left), TermNode::BoolConst(true))
            && boolean_conjunction_implies(arena, requires, right)
        {
            return Ok(());
        }
        if matches!(arena.node(right), TermNode::BoolConst(true))
            && boolean_conjunction_implies(arena, requires, left)
        {
            return Ok(());
        }
    }
    let equal = arena
        .eq(left, right)
        .map_err(|error| contract_error(&error.to_string()))?;
    let outside_domain = arena
        .not(requires)
        .map_err(|error| contract_error(&error.to_string()))?;
    let guarded = arena
        .or(outside_domain, equal)
        .map_err(|error| contract_error(&error.to_string()))?;
    prove_contract_goal(arena, guarded, config, name, component)
}

fn boolean_conjunction_equal(arena: &TermArena, left: TermId, right: TermId) -> bool {
    boolean_conjunction_atoms(arena, left) == boolean_conjunction_atoms(arena, right)
}

fn boolean_conjunction_implies(arena: &TermArena, premise: TermId, conclusion: TermId) -> bool {
    let premise_atoms = boolean_conjunction_atoms(arena, premise);
    boolean_conjunction_atoms(arena, conclusion)
        .iter()
        .all(|atom| premise_atoms.binary_search(atom).is_ok())
}

fn boolean_conjunction_atoms(arena: &TermArena, term: TermId) -> Vec<TermId> {
    fn collect(arena: &TermArena, term: TermId, atoms: &mut Vec<TermId>) {
        match arena.node(term) {
            TermNode::BoolConst(true) => {}
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } => {
                for argument in args.iter().copied() {
                    collect(arena, argument, atoms);
                }
            }
            _ => atoms.push(term),
        }
    }

    let mut atoms = Vec::new();
    collect(arena, term, &mut atoms);
    atoms.sort_unstable();
    atoms
}

fn prove_contract_goal(
    arena: &mut TermArena,
    goal: TermId,
    config: &SolverConfig,
    name: &str,
    component: &str,
) -> Result<(), LoopReflectError> {
    match prove(arena, &[], goal, config) {
        Ok(ProofOutcome::Proved(_)) => Ok(()),
        Ok(ProofOutcome::Disproved(_)) => Err(loop_error(
            LoopReflectErrorKind::ContractDisproved,
            None,
            &format!("scalar contract `@{name}` disproved for {component}"),
        )),
        Ok(ProofOutcome::Unknown(reason)) => Err(loop_error(
            LoopReflectErrorKind::ContractUnknown,
            None,
            &format!("scalar contract `@{name}` undecided for {component}: {reason:?}"),
        )),
        Err(error) => Err(loop_error(
            LoopReflectErrorKind::ContractSolver,
            None,
            &format!("scalar contract `@{name}` solver failure for {component}: {error}"),
        )),
    }
}

fn instantiate_scalar_contract(
    arena: &mut TermArena,
    contract: &ScalarCallContract,
    arguments: &[TermId],
    result: Option<TermId>,
) -> Result<InstantiatedScalarContract, LoopReflectError> {
    if arguments.len() != contract.argument_widths.len() {
        return Err(contract_error(&format!(
            "scalar contract `@{}` expected {} arguments, received {}",
            contract.name,
            contract.argument_widths.len(),
            arguments.len()
        )));
    }
    for (index, (term, width)) in arguments
        .iter()
        .copied()
        .zip(&contract.argument_widths)
        .enumerate()
    {
        let actual = arena.sort_of(term);
        let expected = sort_for_width(*width);
        if actual != expected {
            return Err(contract_error(&format!(
                "scalar contract `@{}` argument {index} expects {expected:?}, received {actual:?}",
                contract.name
            )));
        }
    }
    if let Some(result) = result {
        require_contract_sort(
            arena,
            result,
            sort_for_width(contract.result_width),
            &contract.name,
            "relational result",
        )?;
    }
    let requires = lower_contract_expression(arena, &contract.requires, arguments, None)?;
    require_contract_sort(arena, requires, Sort::Bool, &contract.name, "requires")?;
    let immediate_defined =
        lower_contract_expression(arena, &contract.immediate_defined, arguments, None)?;
    require_contract_sort(
        arena,
        immediate_defined,
        Sort::Bool,
        &contract.name,
        "immediate definedness",
    )?;
    let instantiated_result = match &contract.result {
        ScalarContractResult::Exact(expression) => {
            let value = lower_contract_expression(arena, expression, arguments, None)?;
            require_contract_sort(
                arena,
                value,
                sort_for_width(contract.result_width),
                &contract.name,
                "result value",
            )?;
            InstantiatedContractResult::Exact(value)
        }
        ScalarContractResult::Relational { ensures } => {
            let result = result.ok_or_else(|| {
                contract_error(&format!(
                    "scalar contract `@{}` requires a relational result term",
                    contract.name
                ))
            })?;
            let ensures = lower_contract_expression(arena, ensures, arguments, Some(result))?;
            require_contract_sort(arena, ensures, Sort::Bool, &contract.name, "ensures")?;
            InstantiatedContractResult::Relational { ensures }
        }
    };
    let result_defined =
        lower_contract_expression(arena, &contract.result_defined, arguments, result)?;
    require_contract_sort(
        arena,
        result_defined,
        Sort::Bool,
        &contract.name,
        "result definedness",
    )?;
    Ok(InstantiatedScalarContract {
        requires,
        immediate_defined,
        result: instantiated_result,
        result_defined,
    })
}

fn require_contract_sort(
    arena: &TermArena,
    term: TermId,
    expected: Sort,
    name: &str,
    component: &str,
) -> Result<(), LoopReflectError> {
    let actual = arena.sort_of(term);
    if actual == expected {
        Ok(())
    } else {
        Err(contract_error(&format!(
            "scalar contract `@{name}` {component} expects {expected:?}, received {actual:?}"
        )))
    }
}

fn lower_contract_expression(
    arena: &mut TermArena,
    expression: &ScalarContractExpr,
    arguments: &[TermId],
    result: Option<TermId>,
) -> Result<TermId, LoopReflectError> {
    match expression {
        ScalarContractExpr::Argument(index) => arguments.get(*index).copied().ok_or_else(|| {
            contract_error(&format!(
                "scalar contract references missing argument {index}; signature has {}",
                arguments.len()
            ))
        }),
        ScalarContractExpr::Result => result.ok_or_else(|| {
            contract_error("scalar contract `Result` is unavailable in this component")
        }),
        ScalarContractExpr::Bool(value) => Ok(arena.bool_const(*value)),
        ScalarContractExpr::BitVec { width, value } => {
            if !(2..=128).contains(width) {
                return Err(contract_error(&format!(
                    "scalar contract bit-vector constant has unsupported width {width}"
                )));
            }
            if *width < 128 && *value >= (1_u128 << width) {
                return Err(contract_error(&format!(
                    "scalar contract bit-vector constant value {value} does not fit width {width}"
                )));
            }
            arena
                .bv_const(*width, *value)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::Not(value) => {
            let value = lower_contract_expression(arena, value, arguments, result)?;
            arena
                .not(value)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::And(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .and(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::Eq(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .eq(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::Ite {
            condition,
            when_true,
            when_false,
        } => {
            let condition = lower_contract_expression(arena, condition, arguments, result)?;
            let when_true = lower_contract_expression(arena, when_true, arguments, result)?;
            let when_false = lower_contract_expression(arena, when_false, arguments, result)?;
            arena
                .ite(condition, when_true, when_false)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvAdd(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .bv_add(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvMul(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .bv_mul(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvSignedAddOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .bv_saddo(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvUnsignedAddOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .bv_uaddo(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvSignedMulOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments, result)?;
            let right = lower_contract_expression(arena, right, arguments, result)?;
            arena
                .bv_smulo(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
    }
}

fn validate_contract_expression(
    expression: &ScalarContractExpr,
    argument_count: usize,
    name: &str,
    allow_result: bool,
    component: &str,
) -> Result<usize, LoopReflectError> {
    let nodes = match expression {
        ScalarContractExpr::Argument(index) => {
            if *index >= argument_count {
                return Err(contract_error(&format!(
                    "scalar contract `@{name}` references argument {index}, signature has {argument_count}"
                )));
            }
            1
        }
        ScalarContractExpr::Result => {
            if !allow_result {
                return Err(contract_error(&format!(
                    "scalar contract `@{name}` {component} cannot reference `Result`"
                )));
            }
            1
        }
        ScalarContractExpr::Bool(_) => 1,
        ScalarContractExpr::BitVec { width, value } => {
            if !(2..=128).contains(width) {
                return Err(contract_error(&format!(
                    "scalar contract `@{name}` bit-vector constant has unsupported width {width}"
                )));
            }
            if *width < 128 && *value >= (1_u128 << width) {
                return Err(contract_error(&format!(
                    "scalar contract `@{name}` bit-vector constant value {value} does not fit width {width}"
                )));
            }
            1
        }
        ScalarContractExpr::Not(value) => 1_usize
            .checked_add(validate_contract_expression(
                value,
                argument_count,
                name,
                allow_result,
                component,
            )?)
            .ok_or_else(|| contract_error("scalar contract expression count overflowed"))?,
        ScalarContractExpr::And(left, right)
        | ScalarContractExpr::Eq(left, right)
        | ScalarContractExpr::BvAdd(left, right)
        | ScalarContractExpr::BvMul(left, right)
        | ScalarContractExpr::BvSignedAddOverflow(left, right)
        | ScalarContractExpr::BvUnsignedAddOverflow(left, right)
        | ScalarContractExpr::BvSignedMulOverflow(left, right) => {
            let left =
                validate_contract_expression(left, argument_count, name, allow_result, component)?;
            let right =
                validate_contract_expression(right, argument_count, name, allow_result, component)?;
            1_usize
                .checked_add(left)
                .and_then(|nodes| nodes.checked_add(right))
                .ok_or_else(|| contract_error("scalar contract expression count overflowed"))?
        }
        ScalarContractExpr::Ite {
            condition,
            when_true,
            when_false,
        } => {
            let condition = validate_contract_expression(
                condition,
                argument_count,
                name,
                allow_result,
                component,
            )?;
            let when_true = validate_contract_expression(
                when_true,
                argument_count,
                name,
                allow_result,
                component,
            )?;
            let when_false = validate_contract_expression(
                when_false,
                argument_count,
                name,
                allow_result,
                component,
            )?;
            1_usize
                .checked_add(condition)
                .and_then(|nodes| nodes.checked_add(when_true))
                .and_then(|nodes| nodes.checked_add(when_false))
                .ok_or_else(|| contract_error("scalar contract expression count overflowed"))?
        }
    };
    Ok(nodes)
}

fn contract_error(detail: &str) -> LoopReflectError {
    loop_error(LoopReflectErrorKind::InvalidContract, None, detail)
}
