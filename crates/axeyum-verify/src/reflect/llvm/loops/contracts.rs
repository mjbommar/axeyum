//! Verified exact scalar contracts for checked LLVM loop calls.

use std::collections::{BTreeMap, HashMap};
use std::time::Duration;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use super::{
    BuildError, CallRequirementSite, CallRequirementTerms, DirectCallResolver, LoopReflectError,
    LoopReflectErrorKind, LoweredCall, loop_error, scalar_width, sort_for_width,
    validate_direct_callee,
};
use crate::reflect::llvm::checked::{DefinedValue, reflect_parsed_components_into, resolve};
use crate::reflect::llvm::syntax::{ScalarInstruction, ScalarInstructionKind, parse_function};

const MAX_CONTRACT_EXPRESSION_NODES: usize = 256;
const DEFAULT_CONTRACT_VERIFICATION_TIMEOUT: Duration = Duration::from_secs(2);

/// One bounded expression in the first exact scalar LLVM contract language.
///
/// The language is intentionally smaller than the checked LLVM instruction
/// surface. It owns only the Boolean/BV operations needed to state and mutate
/// ADR-0296's exact `leaf` contract. Every expression is independently lowered
/// and sort-checked before its contract can be verified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarContractExpr {
    /// One formal scalar argument by zero-based signature position.
    Argument(usize),
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

/// An explicit exact functional contract for one scalar LLVM callee.
///
/// ADR-0296 admitted only a universally true requirement. ADR-0297 extends the
/// same representation with guarded body verification and explicit call-site
/// obligations; general relational `ensures` remains outside this type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCallContract {
    name: String,
    argument_widths: Vec<u32>,
    result_width: u32,
    requires: ScalarContractExpr,
    immediate_defined: ScalarContractExpr,
    result: ScalarContractExpr,
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
        let total_nodes = [
            &contract.requires,
            &contract.immediate_defined,
            &contract.result,
            &contract.result_defined,
        ]
        .into_iter()
        .try_fold(0_usize, |total, expression| {
            let nodes = validate_contract_expression(
                expression,
                contract.argument_widths.len(),
                &contract.name,
            )?;
            total
                .checked_add(nodes)
                .ok_or_else(|| contract_error("scalar contract expression count overflowed"))
        })?;
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
    /// Verifies exact scalar contracts against their supplied checked bodies.
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
        let terms =
            instantiate_scalar_contract(arena, contract, &values).map_err(BuildError::call)?;
        let result_defined = arena
            .and(argument_defined, terms.result.defined)
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
                ..terms.result
            },
            immediate_defined: immediate,
            requirement,
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

struct InstantiatedScalarContract {
    requires: TermId,
    immediate_defined: TermId,
    result: DefinedValue,
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
    let contract_terms = instantiate_scalar_contract(&mut arena, contract, &params)?;

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
        contract_terms.result.defined,
        body_terms.result.defined,
        config,
        &contract.name,
        "result definedness",
    )?;
    verify_contract_equal_under(
        &mut arena,
        contract_terms.requires,
        contract_terms.result.value,
        body_terms.result.value,
        config,
        &contract.name,
        "result value",
    )
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
    let requires = lower_contract_expression(arena, &contract.requires, arguments)?;
    require_contract_sort(arena, requires, Sort::Bool, &contract.name, "requires")?;
    let immediate_defined =
        lower_contract_expression(arena, &contract.immediate_defined, arguments)?;
    require_contract_sort(
        arena,
        immediate_defined,
        Sort::Bool,
        &contract.name,
        "immediate definedness",
    )?;
    let result = lower_contract_expression(arena, &contract.result, arguments)?;
    require_contract_sort(
        arena,
        result,
        sort_for_width(contract.result_width),
        &contract.name,
        "result value",
    )?;
    let result_defined = lower_contract_expression(arena, &contract.result_defined, arguments)?;
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
        result: DefinedValue {
            value: result,
            defined: result_defined,
            width: contract.result_width,
        },
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
) -> Result<TermId, LoopReflectError> {
    match expression {
        ScalarContractExpr::Argument(index) => arguments.get(*index).copied().ok_or_else(|| {
            contract_error(&format!(
                "scalar contract references missing argument {index}; signature has {}",
                arguments.len()
            ))
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
            let value = lower_contract_expression(arena, value, arguments)?;
            arena
                .not(value)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::And(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
            arena
                .and(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvAdd(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
            arena
                .bv_add(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvMul(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
            arena
                .bv_mul(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvSignedAddOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
            arena
                .bv_saddo(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvUnsignedAddOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
            arena
                .bv_uaddo(left, right)
                .map_err(|error| contract_error(&error.to_string()))
        }
        ScalarContractExpr::BvSignedMulOverflow(left, right) => {
            let left = lower_contract_expression(arena, left, arguments)?;
            let right = lower_contract_expression(arena, right, arguments)?;
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
            .checked_add(validate_contract_expression(value, argument_count, name)?)
            .ok_or_else(|| contract_error("scalar contract expression count overflowed"))?,
        ScalarContractExpr::And(left, right)
        | ScalarContractExpr::BvAdd(left, right)
        | ScalarContractExpr::BvMul(left, right)
        | ScalarContractExpr::BvSignedAddOverflow(left, right)
        | ScalarContractExpr::BvUnsignedAddOverflow(left, right)
        | ScalarContractExpr::BvSignedMulOverflow(left, right) => {
            let left = validate_contract_expression(left, argument_count, name)?;
            let right = validate_contract_expression(right, argument_count, name)?;
            1_usize
                .checked_add(left)
                .and_then(|nodes| nodes.checked_add(right))
                .ok_or_else(|| contract_error("scalar contract expression count overflowed"))?
        }
    };
    Ok(nodes)
}

fn contract_error(detail: &str) -> LoopReflectError {
    loop_error(LoopReflectErrorKind::InvalidContract, None, detail)
}
