//! Checked reflection of canonical scalar LLVM loops.
//!
//! The first T5.1.4 profile recognizes a single-block self-loop. The second
//! admits one single-latch natural loop whose internal region is acyclic. Both
//! abstract the exit decision: the returned recurrence may continue after the
//! source loop exits. This is a sound over-approximation for state-invariant
//! proofs, while a reachable recurrence state is not a source counterexample
//! until it is separately replayed against the original program.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::error::Error;
use std::fmt;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{SolverError, TransitionSystem};

/// Verified exact and relational scalar call contracts.
pub mod contracts;

use contracts::CallResolver;
pub use contracts::{
    CheckedRelationalScalarReflected, RelationalScalarCallSite, ScalarCallContract,
    ScalarContractExpr, VerifiedContractResolver, reflect_scalar_into_checked_with_contracts,
};

use super::checked::{
    DefinedValue, ReflectError, ReflectErrorKind, lower_assignment, reflect_parsed_components_into,
    reflect_parsed_into, resolve,
};
use super::syntax::{
    BlockId, CfgBlock, Function, Operand, ParseError, Phi, ScalarCfg, ScalarInstruction,
    ScalarInstructionKind, SourceSpan, TerminatorKind, parse_function, parse_scalar_cfg,
};

const MAX_ITERATION_PATHS: usize = 64;
const MAX_PATH_BLOCK_EXECUTIONS: usize = 4_096;

type LoopParameterInventory = (BTreeMap<String, (u32, SourceSpan)>, BTreeSet<String>);

#[derive(Debug, Clone, Copy)]
pub(super) struct CallRequirementTerms {
    pub(super) satisfied: TermId,
    pub(super) violated: TermId,
}

#[derive(Debug)]
pub(super) struct LoweredCall {
    pub(super) destination: String,
    pub(super) value: DefinedValue,
    pub(super) immediate_defined: TermId,
    pub(super) requirement: Option<CallRequirementTerms>,
}

/// Stable failure classes for the canonical LLVM loop profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopReflectErrorKind {
    /// Structured LLVM parsing or CFG validation failed.
    Syntax,
    /// The CFG contains no cycle.
    NoCycle,
    /// More than one admitted loop candidate exists.
    MultipleCycles,
    /// A cycle exists, but it is not an admitted self-loop or natural-loop shape.
    NonCanonicalCycle,
    /// A multi-block loop violates the admitted single-header/single-latch region.
    NonCanonicalLoopRegion,
    /// Deterministic path enumeration exceeded the admitted resource bound.
    PathLimit,
    /// Loop PHIs do not have the exact entry/back-edge structure.
    InvalidPhi,
    /// A PHI initializer is not a constant or scalar function parameter.
    UnsupportedInitializer,
    /// A typed scalar loop-body operation is outside the admitted profile.
    UnsupportedBody,
    /// The loop reaches memory, which this scalar profile does not model.
    UnsupportedMemory,
    /// A direct call lacks explicit eligible body/contract semantics or has an
    /// incompatible call boundary.
    UnsupportedCall,
    /// A scalar contract is malformed, ill-sorted, or exceeds its resource bound.
    InvalidContract,
    /// A scalar contract claim was refuted by a replay-checked countermodel.
    ContractDisproved,
    /// Scalar contract verification returned a classified undecided result.
    ContractUnknown,
    /// The contract-verification solver failed before producing a verdict.
    ContractSolver,
    /// The recurrence depends on SSA state outside PHIs and function parameters.
    ExternalSsaDependency,
    /// The requested unsigned bound does not name a compatible loop PHI.
    InvalidProperty,
    /// Axeyum IR construction rejected the validated recurrence.
    IrConstruction,
}

/// Located failure from canonical LLVM loop reflection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopReflectError {
    kind: LoopReflectErrorKind,
    span: Option<SourceSpan>,
    detail: String,
}

impl LoopReflectError {
    /// Stable failure class.
    #[must_use]
    pub fn kind(&self) -> LoopReflectErrorKind {
        self.kind
    }

    /// Source span when the failure belongs to textual LLVM input.
    #[must_use]
    pub fn span(&self) -> Option<SourceSpan> {
        self.span
    }
}

impl fmt::Display for LoopReflectError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(span) = self.span {
            write!(
                formatter,
                "{} at {}:{}",
                self.detail, span.line, span.column
            )
        } else {
            formatter.write_str(&self.detail)
        }
    }
}

impl Error for LoopReflectError {}

impl From<ParseError> for LoopReflectError {
    fn from(error: ParseError) -> Self {
        Self {
            kind: LoopReflectErrorKind::Syntax,
            span: Some(error.span()),
            detail: error.to_string(),
        }
    }
}

/// An explicit bad-state predicate `phi > bound` using unsigned BV order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedPhiUpperBound {
    /// Loop PHI name without `%`.
    pub phi: String,
    /// Largest permitted unsigned value.
    pub bound: u128,
}

impl UnsignedPhiUpperBound {
    /// Creates an unsigned upper-bound property for one named PHI.
    #[must_use]
    pub fn new(phi: impl Into<String>, bound: u128) -> Self {
        Self {
            phi: phi.into(),
            bound,
        }
    }
}

/// Deterministic inventory of exact straight-line scalar LLVM callee bodies.
///
/// Merely parsing a [`ScalarInstructionKind::DirectCall`] does not give it
/// semantics. A caller must construct this resolver explicitly and use the
/// opt-in direct-call reflection entry point. Nested calls, memory, control
/// flow, and non-scalar signatures fail closed during construction.
#[derive(Debug, Clone)]
pub struct DirectCallResolver {
    callees: BTreeMap<String, Function>,
}

impl DirectCallResolver {
    /// Parses and validates exact checked callee bodies.
    ///
    /// # Errors
    ///
    /// Returns a stable located failure for malformed input, duplicate names,
    /// non-scalar signatures, control flow, memory, nested calls, or rejected
    /// checked value/definedness semantics.
    pub fn from_bodies(bodies: &[&str]) -> Result<Self, LoopReflectError> {
        let mut callees = BTreeMap::new();
        for body in bodies {
            let function = parse_function(body)?;
            if callees.contains_key(&function.name) {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(function.name_span),
                    &format!("duplicate direct callee body `@{}`", function.name),
                ));
            }
            validate_direct_callee(&function)?;
            callees.insert(function.name.clone(), function);
        }
        Ok(Self { callees })
    }

    /// Ordered callee names accepted by this resolver.
    #[must_use]
    pub fn callee_names(&self) -> Vec<&str> {
        self.callees.keys().map(String::as_str).collect()
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
        let function = self.callees.get(callee).ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!("direct call `@{callee}` has no supplied checked callee body"),
            )
        })?;
        let callee_result = scalar_width(&function.return_ty).ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(function.name_span),
                &format!(
                    "direct callee `@{callee}` has non-scalar result `{}`",
                    function.return_ty
                ),
            )
        })?;
        if callee_result != *result_width {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!(
                    "direct call `@{callee}` declares i{result_width}, callee returns i{callee_result}"
                ),
            ));
        }
        if args.len() != function.params.len() {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(instruction.span),
                &format!(
                    "direct call `@{callee}` supplies {} arguments, callee declares {}",
                    args.len(),
                    function.params.len()
                ),
            ));
        }
        for (index, (argument, parameter)) in args.iter().zip(&function.params).enumerate() {
            let parameter_width = scalar_width(&parameter.ty).ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(parameter.span),
                    &format!(
                        "direct callee `@{callee}` parameter {} has non-scalar type `{}`",
                        index, parameter.ty
                    ),
                )
            })?;
            if argument.width != parameter_width {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(instruction.span),
                    &format!(
                        "direct call `@{callee}` argument {index} declares i{}, callee expects i{parameter_width}",
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

    fn lower_call(
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
                "direct-call resolver received a non-call instruction",
            )));
        };
        let function = &self.callees[callee];
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
        let components = reflect_parsed_components_into(arena, &values, function)
            .map_err(BuildError::reflection)?;
        let mut result = components.result;
        result.defined = arena
            .and(argument_defined, result.defined)
            .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
        let immediate = arena
            .and(argument_defined, components.immediate_defined)
            .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
        Ok(LoweredCall {
            destination: dest.clone(),
            value: result,
            immediate_defined: immediate,
            requirement: None,
        })
    }
}

/// Role of one deterministic transition-system state component.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopStateRole {
    /// A loop-carried PHI updated on the self edge.
    Phi,
    /// A referenced function parameter preserved by every transition.
    Parameter,
}

/// Public metadata for one transition-system state component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopStateComponent {
    /// LLVM local name without `%`.
    pub name: String,
    /// LLVM integer width (`i1` is represented by Axeyum `Bool`).
    pub width: u32,
    /// Whether the component is loop-carried or immutable input state.
    pub role: LoopStateRole,
}

/// Deterministic block inventory for one header-to-latch iteration path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopIterationPath {
    blocks: Vec<BlockId>,
}

/// Source identity for one verified scalar call requirement in the recurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallRequirementSite {
    callee: String,
    span: SourceSpan,
}

impl CallRequirementSite {
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
}

impl LoopIterationPath {
    /// Blocks executed by this path, from the loop header through the latch.
    #[must_use]
    pub fn blocks(&self) -> &[BlockId] {
        &self.blocks
    }
}

#[derive(Debug, Clone)]
struct LoopPhi {
    init: Operand,
    back: Operand,
    span: SourceSpan,
}

#[derive(Debug, Clone)]
struct LoopParameter {
    component: usize,
    span: SourceSpan,
}

#[derive(Debug, Clone)]
struct CompiledPath {
    blocks: Vec<CfgBlock>,
}

#[derive(Debug, Clone)]
enum LoopBody {
    SelfLoop {
        instructions: Vec<ScalarInstruction>,
        branch_condition: Operand,
    },
    NaturalLoop {
        paths: Vec<CompiledPath>,
        latch_condition: Operand,
    },
}

/// One owned, typed recurrence from an admitted canonical LLVM loop profile.
///
/// This system intentionally over-approximates the source exit edge. Use it to
/// prove invariants. Treat [`axeyum_solver::BmcOutcome::Reachable`] as an
/// abstract recurrence witness until the same state is replayed in source code.
/// Verified-contract requirements are additional source-attributed bad states,
/// evaluated under the exact instruction/selected-edge prefix reaching each
/// call.
#[derive(Debug, Clone)]
pub struct CanonicalLoopSystem {
    function: String,
    loop_block: BlockId,
    latch_block: BlockId,
    exit_block: BlockId,
    iteration_paths: Vec<LoopIterationPath>,
    state: Vec<LoopStateComponent>,
    phis: Vec<LoopPhi>,
    parameters: Vec<LoopParameter>,
    body: LoopBody,
    direct_calls: Option<CallResolver>,
    call_requirement_sites: Vec<CallRequirementSite>,
    branch_span: SourceSpan,
    bad_component: usize,
    bad_bound: u128,
}

impl CanonicalLoopSystem {
    /// Reflected function name.
    #[must_use]
    pub fn function_name(&self) -> &str {
        &self.function
    }

    /// Identity of the loop header (and of the latch for a self-loop).
    #[must_use]
    pub fn loop_block(&self) -> &BlockId {
        &self.loop_block
    }

    /// Identity of the unique loop latch.
    #[must_use]
    pub fn latch_block(&self) -> &BlockId {
        &self.latch_block
    }

    /// Deterministic header-to-latch path inventory.
    #[must_use]
    pub fn iteration_paths(&self) -> &[LoopIterationPath] {
        &self.iteration_paths
    }

    /// Identity of the source exit edge omitted by the recurrence.
    #[must_use]
    pub fn exit_block(&self) -> &BlockId {
        &self.exit_block
    }

    /// Deterministic PHI-then-parameter state layout.
    #[must_use]
    pub fn state_components(&self) -> &[LoopStateComponent] {
        &self.state
    }

    /// State index for a named LLVM local.
    #[must_use]
    pub fn state_component_index(&self, name: &str) -> Option<usize> {
        self.state
            .iter()
            .position(|component| component.name == name)
    }

    /// Ordered verified-contract call sites contributing requirement bad states.
    #[must_use]
    pub fn call_requirement_sites(&self) -> &[CallRequirementSite] {
        &self.call_requirement_sites
    }

    /// Whether the source exit decision is abstracted by this system.
    #[must_use]
    pub const fn exit_is_overapproximated(&self) -> bool {
        true
    }

    fn declare_state(
        &self,
        arena: &mut TermArena,
        step: usize,
    ) -> Result<Vec<SymbolId>, BuildError> {
        self.state
            .iter()
            .map(|component| {
                arena
                    .declare(
                        &format!("llvm.loop.{}.{}@{step}", self.function, component.name),
                        sort_for_width(component.width),
                    )
                    .map_err(|error| BuildError::ir(None, error.to_string()))
            })
            .collect()
    }

    fn build_init(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, BuildError> {
        self.require_state_arity(state)?;
        let always = arena.bool_const(true);
        let mut env = HashMap::new();
        for parameter in &self.parameters {
            let component = &self.state[parameter.component];
            env.insert(
                component.name.clone(),
                DefinedValue {
                    value: arena.var(state[parameter.component]),
                    defined: always,
                    width: component.width,
                },
            );
        }

        let mut conditions = Vec::with_capacity(self.phis.len() * 2);
        for (index, phi) in self.phis.iter().enumerate() {
            let component = &self.state[index];
            let initial = resolve(arena, &env, &phi.init, component.width, phi.span)
                .map_err(BuildError::reflection)?;
            conditions.push(initial.defined);
            let current = arena.var(state[index]);
            conditions.push(
                arena
                    .eq(current, initial.value)
                    .map_err(|error| BuildError::ir(Some(phi.span), error.to_string()))?,
            );
        }
        conjoin(arena, &conditions, self.branch_span)
    }

    fn build_trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, BuildError> {
        self.require_state_arity(pre)?;
        self.require_state_arity(post)?;
        let env = self.state_environment(arena, pre);

        match &self.body {
            LoopBody::SelfLoop {
                instructions,
                branch_condition,
            } => self.build_self_loop_trans(arena, post, env, instructions, branch_condition),
            LoopBody::NaturalLoop {
                paths,
                latch_condition,
            } => {
                let mut path_relations = Vec::with_capacity(paths.len());
                for path in paths {
                    path_relations.push(self.build_path_trans(
                        arena,
                        post,
                        env.clone(),
                        path,
                        latch_condition,
                    )?);
                }
                disjoin(arena, &path_relations, self.branch_span)
            }
        }
    }

    fn build_self_loop_trans(
        &self,
        arena: &mut TermArena,
        post: &[SymbolId],
        mut env: HashMap<String, DefinedValue>,
        instructions: &[ScalarInstruction],
        branch_condition: &Operand,
    ) -> Result<TermId, BuildError> {
        let mut conditions = Vec::new();
        lower_instructions(
            arena,
            &mut env,
            instructions,
            &mut conditions,
            self.direct_calls.as_ref(),
            None,
        )?;
        let branch = resolve(arena, &env, branch_condition, 1, self.branch_span)
            .map_err(BuildError::reflection)?;
        conditions.push(branch.defined);
        self.bind_post_state(arena, post, &env, &mut conditions)?;
        conjoin(arena, &conditions, self.branch_span)
    }

    fn build_path_trans(
        &self,
        arena: &mut TermArena,
        post: &[SymbolId],
        mut env: HashMap<String, DefinedValue>,
        path: &CompiledPath,
        latch_condition: &Operand,
    ) -> Result<TermId, BuildError> {
        let mut conditions = Vec::new();
        for (index, block) in path.blocks.iter().enumerate() {
            if index > 0 {
                let predecessor = &path.blocks[index - 1].id;
                lower_selected_phis(arena, &mut env, &block.phis, predecessor)?;
            }
            lower_instructions(
                arena,
                &mut env,
                &block.instructions,
                &mut conditions,
                self.direct_calls.as_ref(),
                None,
            )?;

            if index + 1 == path.blocks.len() {
                let branch = resolve(arena, &env, latch_condition, 1, block.terminator.span)
                    .map_err(BuildError::reflection)?;
                conditions.push(branch.defined);
            } else {
                let next = &path.blocks[index + 1].id;
                lower_selected_edge(arena, &env, block, next, &mut conditions)?;
            }
        }
        self.bind_post_state(arena, post, &env, &mut conditions)?;
        conjoin(arena, &conditions, self.branch_span)
    }

    fn bind_post_state(
        &self,
        arena: &mut TermArena,
        post: &[SymbolId],
        env: &HashMap<String, DefinedValue>,
        conditions: &mut Vec<TermId>,
    ) -> Result<(), BuildError> {
        for (index, phi) in self.phis.iter().enumerate() {
            let component = &self.state[index];
            let next = resolve(arena, env, &phi.back, component.width, phi.span)
                .map_err(BuildError::reflection)?;
            conditions.push(next.defined);
            let post_value = arena.var(post[index]);
            conditions.push(
                arena
                    .eq(post_value, next.value)
                    .map_err(|error| BuildError::ir(Some(phi.span), error.to_string()))?,
            );
        }
        for parameter in &self.parameters {
            let post_value = arena.var(post[parameter.component]);
            let component = &self.state[parameter.component];
            let pre_value = env
                .get(&component.name)
                .ok_or_else(|| {
                    BuildError::ir(
                        Some(parameter.span),
                        format!(
                            "validated immutable parameter `%{}` disappeared from loop state",
                            component.name
                        ),
                    )
                })?
                .value;
            conditions.push(
                arena
                    .eq(post_value, pre_value)
                    .map_err(|error| BuildError::ir(Some(parameter.span), error.to_string()))?,
            );
        }
        Ok(())
    }

    fn state_environment(
        &self,
        arena: &mut TermArena,
        state: &[SymbolId],
    ) -> HashMap<String, DefinedValue> {
        let always = arena.bool_const(true);
        self.state
            .iter()
            .enumerate()
            .map(|(index, component)| {
                (
                    component.name.clone(),
                    DefinedValue {
                        value: arena.var(state[index]),
                        defined: always,
                        width: component.width,
                    },
                )
            })
            .collect()
    }

    fn build_property_bad(
        &self,
        arena: &mut TermArena,
        state: &[SymbolId],
    ) -> Result<TermId, BuildError> {
        let component = &self.state[self.bad_component];
        let bound = arena
            .bv_const(component.width, self.bad_bound)
            .map_err(|error| {
                BuildError::ir(Some(self.phis[self.bad_component].span), error.to_string())
            })?;
        let value = arena.var(state[self.bad_component]);
        arena.bv_ugt(value, bound).map_err(|error| {
            BuildError::ir(Some(self.phis[self.bad_component].span), error.to_string())
        })
    }

    fn build_call_requirement_bad(
        &self,
        arena: &mut TermArena,
        state: &[SymbolId],
    ) -> Result<TermId, BuildError> {
        if self.call_requirement_sites.is_empty() {
            return Ok(arena.bool_const(false));
        }
        let initial_env = self.state_environment(arena, state);
        let mut violations = Vec::new();
        match &self.body {
            LoopBody::SelfLoop { instructions, .. } => {
                let mut env = initial_env;
                let mut prefix = Vec::new();
                lower_instructions(
                    arena,
                    &mut env,
                    instructions,
                    &mut prefix,
                    self.direct_calls.as_ref(),
                    Some(&mut violations),
                )?;
            }
            LoopBody::NaturalLoop { paths, .. } => {
                for path in paths {
                    let mut env = initial_env.clone();
                    let mut prefix = Vec::new();
                    for (index, block) in path.blocks.iter().enumerate() {
                        if index > 0 {
                            let predecessor = &path.blocks[index - 1].id;
                            lower_selected_phis(arena, &mut env, &block.phis, predecessor)?;
                        }
                        lower_instructions(
                            arena,
                            &mut env,
                            &block.instructions,
                            &mut prefix,
                            self.direct_calls.as_ref(),
                            Some(&mut violations),
                        )?;
                        if let Some(next) = path.blocks.get(index + 1) {
                            lower_selected_edge(arena, &env, block, &next.id, &mut prefix)?;
                        }
                    }
                }
            }
        }
        disjoin(arena, &violations, self.branch_span)
    }

    fn build_bad(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, BuildError> {
        self.require_state_arity(state)?;
        let property = self.build_property_bad(arena, state)?;
        let call_requirement = self.build_call_requirement_bad(arena, state)?;
        arena
            .or(property, call_requirement)
            .map_err(|error| BuildError::ir(Some(self.branch_span), error.to_string()))
    }

    fn require_state_arity(&self, state: &[SymbolId]) -> Result<(), BuildError> {
        if state.len() == self.state.len() {
            Ok(())
        } else {
            Err(BuildError::state(format!(
                "canonical LLVM loop expects {} state components, found {}",
                self.state.len(),
                state.len()
            )))
        }
    }

    fn validate_terms(&self) -> Result<(), LoopReflectError> {
        let mut arena = TermArena::new();
        let pre = self
            .declare_state(&mut arena, 0)
            .map_err(|error| loop_build_error(error, BuildPhase::State))?;
        let post = self
            .declare_state(&mut arena, 1)
            .map_err(|error| loop_build_error(error, BuildPhase::State))?;
        self.build_init(&mut arena, &pre)
            .map_err(|error| loop_build_error(error, BuildPhase::Init))?;
        self.build_trans(&mut arena, &pre, &post)
            .map_err(|error| loop_build_error(error, BuildPhase::Transition))?;
        self.build_bad(&mut arena, &pre)
            .map_err(|error| loop_build_error(error, BuildPhase::Property))?;
        Ok(())
    }
}

impl TransitionSystem for CanonicalLoopSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        self.declare_state(arena, step).map_err(solver_build_error)
    }

    fn init(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, SolverError> {
        self.build_init(arena, state).map_err(solver_build_error)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        self.build_trans(arena, pre, post)
            .map_err(solver_build_error)
    }

    fn bad(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, SolverError> {
        self.build_bad(arena, state).map_err(solver_build_error)
    }
}

/// Reflects one typed canonical scalar LLVM self-loop into a transition system.
///
/// # Errors
///
/// Returns a stable, located failure for malformed syntax, any cycle outside
/// the one-block profile, invalid PHIs/properties, memory, external SSA state,
/// or rejected checked semantics. Source input is never handled with a panic.
pub fn reflect_canonical_loop_checked(
    llvm: &str,
    property: UnsignedPhiUpperBound,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    reflect_canonical_loop_with_resolver(llvm, property, None)
}

#[expect(
    clippy::too_many_lines,
    reason = "the canonical profile keeps every fail-closed structural gate visible in source order"
)]
fn reflect_canonical_loop_with_resolver(
    llvm: &str,
    property: UnsignedPhiUpperBound,
    direct_calls: Option<&CallResolver>,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    let UnsignedPhiUpperBound {
        phi: property_phi,
        bound: property_bound,
    } = property;
    let function = parse_function(llvm)?;
    let cfg = parse_scalar_cfg(&function)?;
    let loop_index = canonical_loop_index(&cfg)?;
    let block = &cfg.blocks[loop_index];

    let (branch_condition, exit_block) = match &block.terminator.kind {
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } if true_target == &block.id && false_target != &block.id => {
            (condition.clone(), false_target.clone())
        }
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } if false_target == &block.id && true_target != &block.id => {
            (condition.clone(), true_target.clone())
        }
        _ => {
            return Err(loop_error(
                LoopReflectErrorKind::NonCanonicalCycle,
                Some(block.terminator.span),
                "canonical loop requires one conditional self edge and one distinct exit edge",
            ));
        }
    };

    let (parameter_widths, parameter_names) = loop_parameter_inventory(&function.params)?;
    validate_unique_definitions(&cfg, &parameter_names)?;

    let expected_predecessors = BTreeSet::from([cfg.entry.clone(), block.id.clone()]);
    let actual_predecessors = block.predecessors.iter().cloned().collect::<BTreeSet<_>>();
    if actual_predecessors != expected_predecessors {
        return Err(loop_error(
            LoopReflectErrorKind::NonCanonicalCycle,
            Some(block.span),
            "canonical loop must have exactly the entry edge and its self back-edge",
        ));
    }
    if block.phis.is_empty() {
        return Err(loop_error(
            LoopReflectErrorKind::InvalidPhi,
            Some(block.span),
            "canonical loop requires at least one loop-carried PHI",
        ));
    }

    let mut state = Vec::new();
    let mut phis = Vec::new();
    let mut referenced_parameters = BTreeSet::new();
    for phi in &block.phis {
        if phi.incomings.len() != 2 {
            return Err(loop_error(
                LoopReflectErrorKind::InvalidPhi,
                Some(phi.span),
                "canonical loop PHI must have exactly one entry and one self incoming",
            ));
        }
        let entry = phi
            .incomings
            .iter()
            .find(|incoming| incoming.predecessor == cfg.entry)
            .ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::InvalidPhi,
                    Some(phi.span),
                    "canonical loop PHI is missing its entry incoming",
                )
            })?;
        let back = phi
            .incomings
            .iter()
            .find(|incoming| incoming.predecessor == block.id)
            .ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::InvalidPhi,
                    Some(phi.span),
                    "canonical loop PHI is missing its self-edge incoming",
                )
            })?;
        if let Operand::Local(name) = &entry.value {
            if !parameter_widths.contains_key(name) {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedInitializer,
                    Some(phi.span),
                    &format!("entry PHI value `%{name}` is not a scalar function parameter"),
                ));
            }
            referenced_parameters.insert(name.clone());
        }
        collect_parameter_operand(&back.value, &parameter_widths, &mut referenced_parameters);
        state.push(LoopStateComponent {
            name: phi.dest.clone(),
            width: phi.width,
            role: LoopStateRole::Phi,
        });
        phis.push(LoopPhi {
            init: entry.value.clone(),
            back: back.value.clone(),
            span: phi.span,
        });
    }

    let mut call_requirement_sites = Vec::new();
    for instruction in &block.instructions {
        validate_call_instruction(instruction, direct_calls)?;
        if let Some(site) = direct_calls.and_then(|resolver| resolver.requirement_site(instruction))
        {
            call_requirement_sites.push(site);
        }
        if matches!(
            instruction.kind,
            ScalarInstructionKind::GetElementPtr { .. }
                | ScalarInstructionKind::Load { .. }
                | ScalarInstructionKind::Store { .. }
        ) {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedMemory,
                Some(instruction.span),
                "canonical scalar loop does not admit memory instructions",
            ));
        }
        collect_instruction_parameters(
            &instruction.kind,
            &parameter_widths,
            &mut referenced_parameters,
        );
    }
    collect_parameter_operand(
        &branch_condition,
        &parameter_widths,
        &mut referenced_parameters,
    );

    let phi_count = state.len();
    let mut parameters = Vec::new();
    for parameter in &function.params {
        if !referenced_parameters.contains(&parameter.name) {
            continue;
        }
        let (width, span) = parameter_widths
            .get(&parameter.name)
            .copied()
            .ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::IrConstruction,
                    Some(parameter.span),
                    "validated parameter disappeared from the loop state layout",
                )
            })?;
        let component = state.len();
        state.push(LoopStateComponent {
            name: parameter.name.clone(),
            width,
            role: LoopStateRole::Parameter,
        });
        parameters.push(LoopParameter { component, span });
    }

    let bad_component = state[..phi_count]
        .iter()
        .position(|component| component.name == property_phi)
        .ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::InvalidProperty,
                Some(block.span),
                &format!("unsigned-bound target `%{property_phi}` is not a loop PHI"),
            )
        })?;
    let bad_width = state[bad_component].width;
    if bad_width == 1 || (bad_width < 128 && property_bound >= (1_u128 << bad_width)) {
        return Err(loop_error(
            LoopReflectErrorKind::InvalidProperty,
            Some(block.phis[bad_component].span),
            &format!(
                "unsigned bound {property_bound} does not fit non-Boolean i{bad_width} PHI `%{property_phi}`"
            ),
        ));
    }

    let system = CanonicalLoopSystem {
        function: cfg.name,
        loop_block: block.id.clone(),
        latch_block: block.id.clone(),
        exit_block,
        iteration_paths: vec![LoopIterationPath {
            blocks: vec![block.id.clone()],
        }],
        state,
        phis,
        parameters,
        body: LoopBody::SelfLoop {
            instructions: block.instructions.clone(),
            branch_condition,
        },
        direct_calls: direct_calls.cloned(),
        call_requirement_sites,
        branch_span: block.terminator.span,
        bad_component,
        bad_bound: property_bound,
    };
    system.validate_terms()?;
    Ok(system)
}

/// Reflects one admitted scalar LLVM self-loop or single-latch natural loop.
///
/// The multi-block profile requires an acyclic header-to-latch region and
/// builds one path-conditioned relation per deterministic CFG path. Only the
/// selected path contributes instruction UB and branch polarity. The latch
/// exit choice remains over-approximated exactly as in the self-loop profile.
///
/// # Errors
///
/// Returns a stable, located failure for malformed syntax, ambiguous/multiple
/// loops, early exits, unsupported terminators or instructions, path-resource
/// overflow, invalid PHIs/properties, or rejected checked semantics. Source
/// input is never handled with a panic.
pub fn reflect_single_latch_loop_checked(
    llvm: &str,
    property: UnsignedPhiUpperBound,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    reflect_single_latch_loop_with_resolver(llvm, property, None)
}

/// Reflects one admitted loop while resolving assigned direct scalar calls
/// through explicitly supplied exact checked callee bodies.
///
/// The ordinary [`reflect_single_latch_loop_checked`] entry point deliberately
/// remains fail-closed for every direct call. This opt-in route is an exact
/// inlining baseline for later modular-contract comparison, not an external or
/// uninterpreted call model.
///
/// # Errors
///
/// Returns the ordinary stable loop failures plus [`LoopReflectErrorKind::UnsupportedCall`]
/// for a missing/incompatible body, a non-`noundef` argument boundary, or
/// direct-call syntax outside the admitted resolver profile.
pub fn reflect_single_latch_loop_with_direct_calls_checked(
    llvm: &str,
    property: UnsignedPhiUpperBound,
    resolver: &DirectCallResolver,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    reflect_single_latch_loop_with_resolver(
        llvm,
        property,
        Some(&CallResolver::DirectBody(resolver.clone())),
    )
}

/// Reflects one admitted loop by composing assigned direct scalar calls with
/// explicitly verified contracts.
///
/// Every contract in `resolver` was proved against an exact checked body when
/// the resolver was constructed, but the body is not retained. This route
/// supplies ADR-0296's modular side. ADR-0297 requirements constrain the
/// transition only after their reached complement becomes an explicit bad
/// state. The exact-body route
/// [`reflect_single_latch_loop_with_direct_calls_checked`] remains the inlined
/// comparison baseline.
///
/// # Errors
///
/// Returns the ordinary stable loop failures plus
/// [`LoopReflectErrorKind::UnsupportedCall`] for a missing/incompatible
/// contract or direct-call syntax outside the admitted profile.
pub fn reflect_single_latch_loop_with_contracts_checked(
    llvm: &str,
    property: UnsignedPhiUpperBound,
    resolver: &VerifiedContractResolver,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    reflect_single_latch_loop_with_resolver(
        llvm,
        property,
        Some(&CallResolver::VerifiedContract(resolver.clone())),
    )
}

fn reflect_single_latch_loop_with_resolver(
    llvm: &str,
    property: UnsignedPhiUpperBound,
    direct_calls: Option<&CallResolver>,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    let function = parse_function(llvm)?;
    let cfg = parse_scalar_cfg(&function)?;
    match canonical_loop_index(&cfg) {
        Ok(_) => return reflect_canonical_loop_with_resolver(llvm, property, direct_calls),
        Err(error) if error.kind() == LoopReflectErrorKind::MultipleCycles => return Err(error),
        Err(_) => {}
    }
    let profile = single_latch_profile(&cfg)?;
    build_natural_loop_system(cfg, profile, property, direct_calls)
}

#[derive(Debug)]
struct NaturalLoopProfile {
    header: usize,
    latch: usize,
    exit: BlockId,
    latch_condition: Operand,
    paths: Vec<Vec<usize>>,
}

fn single_latch_profile(cfg: &ScalarCfg) -> Result<NaturalLoopProfile, LoopReflectError> {
    let positions = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut candidates = Vec::new();
    for (source_index, source) in cfg.blocks.iter().enumerate() {
        for target in &source.successors {
            if target == &source.id || target == &cfg.entry {
                continue;
            }
            let target_index = positions[target];
            let header = &cfg.blocks[target_index];
            let expected = BTreeSet::from([cfg.entry.clone(), source.id.clone()]);
            let actual = header.predecessors.iter().cloned().collect::<BTreeSet<_>>();
            if actual != expected
                || !graph_is_acyclic_without(cfg, Some((&source.id, target)))
                || !reachable_from_entry(cfg, &source.id)
            {
                continue;
            }
            let Some((condition, exit)) = latch_edge(source, target) else {
                continue;
            };
            candidates.push((target_index, source_index, condition, exit));
        }
    }

    let (header, latch, latch_condition, exit) = match candidates.as_slice() {
        [] if graph_is_acyclic_without(cfg, None) => {
            return Err(loop_error(
                LoopReflectErrorKind::NoCycle,
                cfg.blocks.first().map(|block| block.span),
                "LLVM CFG contains no cycle",
            ));
        }
        [] => {
            return Err(loop_error(
                LoopReflectErrorKind::NonCanonicalCycle,
                cfg.blocks.first().map(|block| block.span),
                "LLVM CFG cycle has no unique admitted single-latch back-edge",
            ));
        }
        [(header, latch, condition, exit)] => (*header, *latch, condition.clone(), exit.clone()),
        [_, second, ..] => {
            return Err(loop_error(
                LoopReflectErrorKind::MultipleCycles,
                Some(cfg.blocks[second.1].terminator.span),
                "LLVM CFG contains more than one admitted loop back-edge",
            ));
        }
    };

    let paths = enumerate_iteration_paths(cfg, &positions, header, latch)?;
    if paths.is_empty() {
        return Err(loop_error(
            LoopReflectErrorKind::NonCanonicalLoopRegion,
            Some(cfg.blocks[header].span),
            "natural-loop header has no path to its latch",
        ));
    }

    let region = paths
        .iter()
        .flat_map(|path| path.iter().copied())
        .collect::<BTreeSet<_>>();
    for index in &region {
        let block = &cfg.blocks[*index];
        if *index == header {
            continue;
        }
        if block
            .predecessors
            .iter()
            .any(|predecessor| !region.contains(&positions[predecessor]))
        {
            return Err(loop_error(
                LoopReflectErrorKind::NonCanonicalLoopRegion,
                Some(block.span),
                "natural-loop internal block has a predecessor outside the admitted region",
            ));
        }
    }

    Ok(NaturalLoopProfile {
        header,
        latch,
        exit,
        latch_condition,
        paths,
    })
}

fn latch_edge(block: &CfgBlock, header: &BlockId) -> Option<(Operand, BlockId)> {
    match &block.terminator.kind {
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } if true_target == header && false_target != header => {
            Some((condition.clone(), false_target.clone()))
        }
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } if false_target == header && true_target != header => {
            Some((condition.clone(), true_target.clone()))
        }
        _ => None,
    }
}

fn enumerate_iteration_paths(
    cfg: &ScalarCfg,
    positions: &BTreeMap<BlockId, usize>,
    header: usize,
    latch: usize,
) -> Result<Vec<Vec<usize>>, LoopReflectError> {
    let mut paths = Vec::new();
    let mut total_executions = 0_usize;
    let mut stack = vec![(header, 0_usize)];
    while let Some((current, next_successor)) = stack.last_mut() {
        let current_index = *current;
        let block = &cfg.blocks[current_index];
        if current_index == latch {
            if paths.len() == MAX_ITERATION_PATHS {
                return Err(loop_error(
                    LoopReflectErrorKind::PathLimit,
                    Some(block.span),
                    "natural-loop iteration path count exceeds 64",
                ));
            }
            total_executions = total_executions
                .checked_add(stack.len())
                .filter(|total| *total <= MAX_PATH_BLOCK_EXECUTIONS)
                .ok_or_else(|| {
                    loop_error(
                        LoopReflectErrorKind::PathLimit,
                        Some(block.span),
                        "natural-loop path block executions exceed 4096",
                    )
                })?;
            paths.push(stack.iter().map(|(index, _)| *index).collect());
            stack.pop();
            continue;
        }

        if *next_successor == 0 {
            match &block.terminator.kind {
                TerminatorKind::Branch { .. } => {}
                TerminatorKind::CondBranch {
                    true_target,
                    false_target,
                    ..
                } if true_target != false_target => {}
                TerminatorKind::CondBranch { .. } => {
                    return Err(loop_error(
                        LoopReflectErrorKind::UnsupportedBody,
                        Some(block.terminator.span),
                        "natural-loop conditional branch must have distinct destinations",
                    ));
                }
                TerminatorKind::Switch { .. } => {
                    return Err(loop_error(
                        LoopReflectErrorKind::UnsupportedBody,
                        Some(block.terminator.span),
                        "natural-loop internal switch is outside the admitted profile",
                    ));
                }
                TerminatorKind::Return { .. } | TerminatorKind::Unreachable => {
                    return Err(loop_error(
                        LoopReflectErrorKind::NonCanonicalLoopRegion,
                        Some(block.terminator.span),
                        "natural-loop path exits before reaching the unique latch",
                    ));
                }
            }
        }
        let Some(successor) = block.successors.get(*next_successor) else {
            stack.pop();
            continue;
        };
        *next_successor += 1;
        let next = positions[successor];
        if stack.iter().any(|(index, _)| *index == next) {
            return Err(loop_error(
                LoopReflectErrorKind::NonCanonicalLoopRegion,
                Some(cfg.blocks[next].span),
                "natural-loop internal region contains a nested or irreducible cycle",
            ));
        }
        if stack.len() == MAX_PATH_BLOCK_EXECUTIONS {
            return Err(loop_error(
                LoopReflectErrorKind::PathLimit,
                Some(cfg.blocks[next].span),
                "natural-loop path block executions exceed 4096",
            ));
        }
        stack.push((next, 0));
    }
    Ok(paths)
}

#[expect(
    clippy::too_many_lines,
    reason = "the natural-loop profile keeps structural, typing, state, and property gates together"
)]
fn build_natural_loop_system(
    cfg: ScalarCfg,
    profile: NaturalLoopProfile,
    property: UnsignedPhiUpperBound,
    direct_calls: Option<&CallResolver>,
) -> Result<CanonicalLoopSystem, LoopReflectError> {
    let UnsignedPhiUpperBound {
        phi: property_phi,
        bound: property_bound,
    } = property;
    let header = &cfg.blocks[profile.header];
    let latch = &cfg.blocks[profile.latch];
    let (parameter_widths, parameter_names) = loop_parameter_inventory(&cfg.params)?;
    validate_unique_definitions(&cfg, &parameter_names)?;

    if header.phis.is_empty() {
        return Err(loop_error(
            LoopReflectErrorKind::InvalidPhi,
            Some(header.span),
            "single-latch natural loop requires at least one loop-carried header PHI",
        ));
    }
    let mut state = Vec::new();
    let mut phis = Vec::new();
    let mut referenced_parameters = BTreeSet::new();
    for phi in &header.phis {
        if phi.incomings.len() != 2 {
            return Err(loop_error(
                LoopReflectErrorKind::InvalidPhi,
                Some(phi.span),
                "natural-loop header PHI must have exactly one entry and one latch incoming",
            ));
        }
        let entry = phi
            .incomings
            .iter()
            .find(|incoming| incoming.predecessor == cfg.entry)
            .ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::InvalidPhi,
                    Some(phi.span),
                    "natural-loop header PHI is missing its entry incoming",
                )
            })?;
        let back = phi
            .incomings
            .iter()
            .find(|incoming| incoming.predecessor == latch.id)
            .ok_or_else(|| {
                loop_error(
                    LoopReflectErrorKind::InvalidPhi,
                    Some(phi.span),
                    "natural-loop header PHI is missing its latch incoming",
                )
            })?;
        if let Operand::Local(name) = &entry.value {
            if !parameter_widths.contains_key(name) {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedInitializer,
                    Some(phi.span),
                    &format!("entry PHI value `%{name}` is not a scalar function parameter"),
                ));
            }
            referenced_parameters.insert(name.clone());
        }
        collect_parameter_operand(&back.value, &parameter_widths, &mut referenced_parameters);
        state.push(LoopStateComponent {
            name: phi.dest.clone(),
            width: phi.width,
            role: LoopStateRole::Phi,
        });
        phis.push(LoopPhi {
            init: entry.value.clone(),
            back: back.value.clone(),
            span: phi.span,
        });
    }

    let region = profile
        .paths
        .iter()
        .flat_map(|path| path.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut call_requirement_sites = Vec::new();
    for index in &region {
        let block = &cfg.blocks[*index];
        for phi in &block.phis {
            for incoming in &phi.incomings {
                collect_parameter_operand(
                    &incoming.value,
                    &parameter_widths,
                    &mut referenced_parameters,
                );
            }
        }
        for instruction in &block.instructions {
            validate_call_instruction(instruction, direct_calls)?;
            if let Some(site) =
                direct_calls.and_then(|resolver| resolver.requirement_site(instruction))
            {
                call_requirement_sites.push(site);
            }
            if matches!(
                instruction.kind,
                ScalarInstructionKind::GetElementPtr { .. }
                    | ScalarInstructionKind::Load { .. }
                    | ScalarInstructionKind::Store { .. }
            ) {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedMemory,
                    Some(instruction.span),
                    "canonical scalar loop does not admit memory instructions",
                ));
            }
            collect_instruction_parameters(
                &instruction.kind,
                &parameter_widths,
                &mut referenced_parameters,
            );
        }
        collect_terminator_parameters(
            &block.terminator.kind,
            &parameter_widths,
            &mut referenced_parameters,
        );
    }

    let phi_count = state.len();
    let mut parameters = Vec::new();
    for parameter in &cfg.params {
        if !referenced_parameters.contains(&parameter.name) {
            continue;
        }
        let (width, span) = parameter_widths[&parameter.name];
        let component = state.len();
        state.push(LoopStateComponent {
            name: parameter.name.clone(),
            width,
            role: LoopStateRole::Parameter,
        });
        parameters.push(LoopParameter { component, span });
    }

    let bad_component = state[..phi_count]
        .iter()
        .position(|component| component.name == property_phi)
        .ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::InvalidProperty,
                Some(header.span),
                &format!("unsigned-bound target `%{property_phi}` is not a loop PHI"),
            )
        })?;
    let bad_width = state[bad_component].width;
    if bad_width == 1 || (bad_width < 128 && property_bound >= (1_u128 << bad_width)) {
        return Err(loop_error(
            LoopReflectErrorKind::InvalidProperty,
            Some(header.phis[bad_component].span),
            &format!(
                "unsigned bound {property_bound} does not fit non-Boolean i{bad_width} PHI `%{property_phi}`"
            ),
        ));
    }

    let iteration_paths = profile
        .paths
        .iter()
        .map(|path| LoopIterationPath {
            blocks: path
                .iter()
                .map(|index| cfg.blocks[*index].id.clone())
                .collect(),
        })
        .collect::<Vec<_>>();
    let compiled_paths = profile
        .paths
        .iter()
        .map(|path| CompiledPath {
            blocks: path
                .iter()
                .map(|index| cfg.blocks[*index].clone())
                .collect(),
        })
        .collect::<Vec<_>>();
    let system = CanonicalLoopSystem {
        function: cfg.name,
        loop_block: header.id.clone(),
        latch_block: latch.id.clone(),
        exit_block: profile.exit,
        iteration_paths,
        state,
        phis,
        parameters,
        body: LoopBody::NaturalLoop {
            paths: compiled_paths,
            latch_condition: profile.latch_condition,
        },
        direct_calls: direct_calls.cloned(),
        call_requirement_sites,
        branch_span: latch.terminator.span,
        bad_component,
        bad_bound: property_bound,
    };
    system.validate_terms()?;
    Ok(system)
}

fn canonical_loop_index(cfg: &ScalarCfg) -> Result<usize, LoopReflectError> {
    let candidates = cfg
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, block)| block.successors.contains(&block.id))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let loop_index = match candidates.as_slice() {
        [] if graph_is_acyclic_without(cfg, None) => {
            return Err(loop_error(
                LoopReflectErrorKind::NoCycle,
                cfg.blocks.first().map(|block| block.span),
                "LLVM CFG contains no cycle",
            ));
        }
        [] => {
            return Err(loop_error(
                LoopReflectErrorKind::NonCanonicalCycle,
                cfg.blocks.first().map(|block| block.span),
                "LLVM CFG cycle is not a single-block self-loop",
            ));
        }
        [index] => *index,
        _ => {
            return Err(loop_error(
                LoopReflectErrorKind::MultipleCycles,
                Some(cfg.blocks[candidates[1]].span),
                "LLVM CFG contains more than one self-loop candidate",
            ));
        }
    };
    let block = &cfg.blocks[loop_index];
    if block.successors.len() != 2
        || !graph_is_acyclic_without(cfg, Some((&block.id, &block.id)))
        || !reachable_from_entry(cfg, &block.id)
    {
        return Err(loop_error(
            LoopReflectErrorKind::NonCanonicalCycle,
            Some(block.terminator.span),
            "LLVM cycle is not one reachable self-loop with one distinct exit",
        ));
    }
    Ok(loop_index)
}

fn graph_is_acyclic_without(cfg: &ScalarCfg, skipped: Option<(&BlockId, &BlockId)>) -> bool {
    let positions = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut indegree = vec![0_usize; cfg.blocks.len()];
    for block in &cfg.blocks {
        for successor in &block.successors {
            if skipped.is_some_and(|(source, target)| source == &block.id && target == successor) {
                continue;
            }
            indegree[positions[successor]] += 1;
        }
    }
    let mut queue = indegree
        .iter()
        .enumerate()
        .filter_map(|(index, degree)| (*degree == 0).then_some(index))
        .collect::<VecDeque<_>>();
    let mut visited = 0;
    while let Some(index) = queue.pop_front() {
        visited += 1;
        let block = &cfg.blocks[index];
        for successor in &block.successors {
            if skipped.is_some_and(|(source, target)| source == &block.id && target == successor) {
                continue;
            }
            let target = positions[successor];
            indegree[target] -= 1;
            if indegree[target] == 0 {
                queue.push_back(target);
            }
        }
    }
    visited == cfg.blocks.len()
}

fn reachable_from_entry(cfg: &ScalarCfg, target: &BlockId) -> bool {
    let positions = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut pending = vec![cfg.entry.clone()];
    let mut seen = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if &block == target {
            return true;
        }
        if !seen.insert(block.clone()) {
            continue;
        }
        pending.extend(cfg.blocks[positions[&block]].successors.iter().cloned());
    }
    false
}

fn validate_unique_definitions(
    cfg: &ScalarCfg,
    parameters: &BTreeSet<String>,
) -> Result<(), LoopReflectError> {
    let mut definitions = parameters.clone();
    for block in &cfg.blocks {
        for phi in &block.phis {
            if !definitions.insert(phi.dest.clone()) {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedBody,
                    Some(phi.span),
                    &format!("duplicate LLVM SSA definition `%{}`", phi.dest),
                ));
            }
        }
        for instruction in &block.instructions {
            if let Some(dest) = instruction.kind.destination()
                && !definitions.insert(dest.to_owned())
            {
                return Err(loop_error(
                    LoopReflectErrorKind::UnsupportedBody,
                    Some(instruction.span),
                    &format!("duplicate LLVM SSA definition `%{dest}`"),
                ));
            }
        }
    }
    Ok(())
}

fn loop_parameter_inventory(
    parameters: &[super::syntax::Parameter],
) -> Result<LoopParameterInventory, LoopReflectError> {
    let mut widths = BTreeMap::new();
    let mut names = BTreeSet::new();
    for parameter in parameters {
        if !names.insert(parameter.name.clone()) {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedBody,
                Some(parameter.span),
                &format!("duplicate LLVM parameter `%{}`", parameter.name),
            ));
        }
        if let Some(width) = scalar_width(&parameter.ty) {
            widths.insert(parameter.name.clone(), (width, parameter.span));
        }
    }
    Ok((widths, names))
}

fn validate_direct_callee(function: &Function) -> Result<(), LoopReflectError> {
    if scalar_width(&function.return_ty).is_none() {
        return Err(loop_error(
            LoopReflectErrorKind::UnsupportedCall,
            Some(function.name_span),
            &format!(
                "direct callee `@{}` requires an i1 through i128 result; found `{}`",
                function.name, function.return_ty
            ),
        ));
    }
    for (index, parameter) in function.params.iter().enumerate() {
        if scalar_width(&parameter.ty).is_none() {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedCall,
                Some(parameter.span),
                &format!(
                    "direct callee `@{}` parameter {index} requires i1 through i128; found `{}`",
                    function.name, parameter.ty
                ),
            ));
        }
    }
    if function.blocks.len() != 1 {
        return Err(loop_error(
            LoopReflectErrorKind::UnsupportedCall,
            Some(function.span),
            &format!(
                "direct callee `@{}` must contain exactly one straight-line block",
                function.name
            ),
        ));
    }
    let cfg = parse_scalar_cfg(function)?;
    for block in &cfg.blocks {
        for instruction in &block.instructions {
            match instruction.kind {
                ScalarInstructionKind::DirectCall { ref callee, .. } => {
                    return Err(loop_error(
                        LoopReflectErrorKind::UnsupportedCall,
                        Some(instruction.span),
                        &format!(
                            "direct callee `@{}` contains unsupported nested call `@{callee}`",
                            function.name
                        ),
                    ));
                }
                ScalarInstructionKind::GetElementPtr { .. }
                | ScalarInstructionKind::Load { .. }
                | ScalarInstructionKind::Store { .. } => {
                    return Err(loop_error(
                        LoopReflectErrorKind::UnsupportedCall,
                        Some(instruction.span),
                        &format!(
                            "direct callee `@{}` contains memory outside the scalar call profile",
                            function.name
                        ),
                    ));
                }
                _ => {}
            }
        }
    }

    let mut arena = TermArena::new();
    let mut params = Vec::with_capacity(function.params.len());
    for (index, parameter) in function.params.iter().enumerate() {
        let width = scalar_width(&parameter.ty).expect("scalar signature checked above");
        let symbol = arena
            .declare(
                &format!("llvm.direct.{}.arg{index}", function.name),
                sort_for_width(width),
            )
            .map_err(|error| {
                loop_error(
                    LoopReflectErrorKind::IrConstruction,
                    Some(parameter.span),
                    &error.to_string(),
                )
            })?;
        params.push(arena.var(symbol));
    }
    reflect_parsed_into(&mut arena, &params, function).map_err(|error| {
        loop_error(
            match error.kind() {
                ReflectErrorKind::UnsupportedMemory => LoopReflectErrorKind::UnsupportedMemory,
                ReflectErrorKind::IrConstruction => LoopReflectErrorKind::IrConstruction,
                _ => LoopReflectErrorKind::UnsupportedCall,
            },
            error.span(),
            &format!(
                "direct callee `@{}` is not executable: {error}",
                function.name
            ),
        )
    })?;
    Ok(())
}

fn validate_call_instruction(
    instruction: &ScalarInstruction,
    resolver: Option<&CallResolver>,
) -> Result<(), LoopReflectError> {
    let ScalarInstructionKind::DirectCall { callee, .. } = &instruction.kind else {
        return Ok(());
    };
    let Some(resolver) = resolver else {
        return Err(loop_error(
            LoopReflectErrorKind::UnsupportedCall,
            Some(instruction.span),
            &format!("direct call `@{callee}` requires an explicit checked callee body"),
        ));
    };
    resolver.validate_call(instruction)
}

fn collect_instruction_parameters(
    instruction: &ScalarInstructionKind,
    parameters: &BTreeMap<String, (u32, SourceSpan)>,
    referenced: &mut BTreeSet<String>,
) {
    match instruction {
        ScalarInstructionKind::Binary { lhs, rhs, .. }
        | ScalarInstructionKind::Icmp { lhs, rhs, .. }
        | ScalarInstructionKind::Intrinsic { lhs, rhs, .. } => {
            collect_parameter_operand(lhs, parameters, referenced);
            collect_parameter_operand(rhs, parameters, referenced);
        }
        ScalarInstructionKind::Select {
            condition,
            then_value,
            else_value,
            ..
        } => {
            collect_parameter_operand(condition, parameters, referenced);
            collect_parameter_operand(then_value, parameters, referenced);
            collect_parameter_operand(else_value, parameters, referenced);
        }
        ScalarInstructionKind::Cast { operand, .. } => {
            collect_parameter_operand(operand, parameters, referenced);
        }
        ScalarInstructionKind::DirectCall { args, .. } => {
            for argument in args {
                collect_parameter_operand(&argument.value, parameters, referenced);
            }
        }
        ScalarInstructionKind::GetElementPtr { index, .. } => {
            collect_parameter_operand(index, parameters, referenced);
        }
        ScalarInstructionKind::Load { .. }
        | ScalarInstructionKind::Store { .. }
        | ScalarInstructionKind::Return { .. } => {}
    }
}

fn collect_terminator_parameters(
    terminator: &TerminatorKind,
    parameters: &BTreeMap<String, (u32, SourceSpan)>,
    referenced: &mut BTreeSet<String>,
) {
    match terminator {
        TerminatorKind::Return { value, .. }
        | TerminatorKind::CondBranch {
            condition: value, ..
        }
        | TerminatorKind::Switch { value, .. } => {
            collect_parameter_operand(value, parameters, referenced);
        }
        TerminatorKind::Branch { .. } | TerminatorKind::Unreachable => {}
    }
}

fn collect_parameter_operand(
    operand: &Operand,
    parameters: &BTreeMap<String, (u32, SourceSpan)>,
    referenced: &mut BTreeSet<String>,
) {
    if let Operand::Local(name) = operand
        && parameters.contains_key(name)
    {
        referenced.insert(name.clone());
    }
}

fn scalar_width(ty: &str) -> Option<u32> {
    let bytes = ty.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'i' {
        return None;
    }
    let mut index = 1;
    let mut width = 0_u32;
    while index < bytes.len() {
        let byte = bytes[index];
        if !byte.is_ascii_digit() {
            return None;
        }
        width = width.checked_mul(10)?;
        width = width.checked_add(u32::from(byte - b'0'))?;
        index += 1;
    }
    if width == 0 || width > 128 {
        None
    } else {
        Some(width)
    }
}

const fn sort_for_width(width: u32) -> Sort {
    if width == 1 {
        Sort::Bool
    } else {
        Sort::BitVec(width)
    }
}

fn lower_instructions(
    arena: &mut TermArena,
    env: &mut HashMap<String, DefinedValue>,
    instructions: &[ScalarInstruction],
    conditions: &mut Vec<TermId>,
    direct_calls: Option<&CallResolver>,
    mut requirement_violations: Option<&mut Vec<TermId>>,
) -> Result<(), BuildError> {
    for instruction in instructions {
        let lowered = if matches!(instruction.kind, ScalarInstructionKind::DirectCall { .. }) {
            let resolver = direct_calls.ok_or_else(|| {
                BuildError::call(loop_error(
                    LoopReflectErrorKind::UnsupportedCall,
                    Some(instruction.span),
                    "direct call reached transition lowering without a checked resolver",
                ))
            })?;
            resolver.lower_call(arena, env, instruction)?
        } else {
            let (destination, value, immediate_defined) =
                lower_assignment(arena, env, instruction.kind.clone(), instruction.span)
                    .map_err(BuildError::reflection)?;
            LoweredCall {
                destination,
                value,
                immediate_defined,
                requirement: None,
            }
        };
        if let Some(requirement) = lowered.requirement {
            if let Some(violations) = requirement_violations.as_deref_mut() {
                let prefix = conjoin(arena, conditions, instruction.span)?;
                let violation = arena
                    .and(prefix, requirement.violated)
                    .map_err(|error| BuildError::ir(Some(instruction.span), error.to_string()))?;
                violations.push(violation);
            }
            conditions.push(requirement.satisfied);
        }
        conditions.push(lowered.immediate_defined);
        env.insert(lowered.destination, lowered.value);
    }
    Ok(())
}

fn lower_selected_phis(
    arena: &mut TermArena,
    env: &mut HashMap<String, DefinedValue>,
    phis: &[Phi],
    predecessor: &BlockId,
) -> Result<(), BuildError> {
    let before = env.clone();
    let mut bindings = Vec::with_capacity(phis.len());
    for phi in phis {
        let incoming = phi
            .incomings
            .iter()
            .find(|incoming| &incoming.predecessor == predecessor)
            .ok_or_else(|| {
                BuildError::ir(
                    Some(phi.span),
                    format!(
                        "validated loop PHI `%{}` has no selected predecessor",
                        phi.dest
                    ),
                )
            })?;
        let value = resolve(arena, &before, &incoming.value, phi.width, phi.span)
            .map_err(BuildError::reflection)?;
        bindings.push((phi.dest.clone(), value));
    }
    env.extend(bindings);
    Ok(())
}

fn lower_selected_edge(
    arena: &mut TermArena,
    env: &HashMap<String, DefinedValue>,
    block: &CfgBlock,
    next: &BlockId,
    conditions: &mut Vec<TermId>,
) -> Result<(), BuildError> {
    match &block.terminator.kind {
        TerminatorKind::Branch { target } if target == next => Ok(()),
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } if true_target != false_target && (true_target == next || false_target == next) => {
            let branch = resolve(arena, env, condition, 1, block.terminator.span)
                .map_err(BuildError::reflection)?;
            conditions.push(branch.defined);
            if true_target == next {
                conditions.push(branch.value);
            } else {
                conditions.push(arena.not(branch.value).map_err(|error| {
                    BuildError::ir(Some(block.terminator.span), error.to_string())
                })?);
            }
            Ok(())
        }
        _ => Err(BuildError::ir(
            Some(block.terminator.span),
            "validated natural-loop path does not match its selected CFG edge".to_owned(),
        )),
    }
}

fn conjoin(
    arena: &mut TermArena,
    conditions: &[TermId],
    span: SourceSpan,
) -> Result<TermId, BuildError> {
    let mut result = arena.bool_const(true);
    for condition in conditions {
        result = arena
            .and(result, *condition)
            .map_err(|error| BuildError::ir(Some(span), error.to_string()))?;
    }
    Ok(result)
}

fn disjoin(
    arena: &mut TermArena,
    conditions: &[TermId],
    span: SourceSpan,
) -> Result<TermId, BuildError> {
    let mut result = arena.bool_const(false);
    for condition in conditions {
        result = arena
            .or(result, *condition)
            .map_err(|error| BuildError::ir(Some(span), error.to_string()))?;
    }
    Ok(result)
}

#[derive(Debug)]
enum BuildError {
    Reflection(ReflectError),
    Call(LoopReflectError),
    Ir {
        span: Option<SourceSpan>,
        detail: String,
    },
    State(String),
}

impl BuildError {
    fn reflection(error: ReflectError) -> Self {
        Self::Reflection(error)
    }

    fn call(error: LoopReflectError) -> Self {
        Self::Call(error)
    }

    fn ir(span: Option<SourceSpan>, detail: String) -> Self {
        Self::Ir { span, detail }
    }

    fn state(detail: String) -> Self {
        Self::State(detail)
    }
}

#[derive(Debug, Clone, Copy)]
enum BuildPhase {
    State,
    Init,
    Transition,
    Property,
}

fn loop_build_error(error: BuildError, phase: BuildPhase) -> LoopReflectError {
    match error {
        BuildError::Call(error) => error,
        BuildError::Reflection(error) => {
            let kind = match error.kind() {
                ReflectErrorKind::UnsupportedMemory => LoopReflectErrorKind::UnsupportedMemory,
                ReflectErrorKind::UnsupportedCall => LoopReflectErrorKind::UnsupportedCall,
                ReflectErrorKind::UndefinedValue => LoopReflectErrorKind::ExternalSsaDependency,
                ReflectErrorKind::IrConstruction => LoopReflectErrorKind::IrConstruction,
                _ => match phase {
                    BuildPhase::Init => LoopReflectErrorKind::UnsupportedInitializer,
                    BuildPhase::Transition => LoopReflectErrorKind::UnsupportedBody,
                    BuildPhase::Property => LoopReflectErrorKind::InvalidProperty,
                    BuildPhase::State => LoopReflectErrorKind::IrConstruction,
                },
            };
            LoopReflectError {
                kind,
                span: error.span(),
                detail: error.to_string(),
            }
        }
        BuildError::Ir { span, detail } => loop_error(
            LoopReflectErrorKind::IrConstruction,
            span,
            &format!("canonical LLVM loop IR construction failed: {detail}"),
        ),
        BuildError::State(detail) => {
            loop_error(LoopReflectErrorKind::IrConstruction, None, &detail)
        }
    }
}

fn solver_build_error(error: BuildError) -> SolverError {
    let detail = match error {
        BuildError::Reflection(error) => error.to_string(),
        BuildError::Call(error) => error.to_string(),
        BuildError::Ir { detail, .. } | BuildError::State(detail) => detail,
    };
    SolverError::Backend(format!("validated canonical LLVM loop: {detail}"))
}

fn loop_error(
    kind: LoopReflectErrorKind,
    span: Option<SourceSpan>,
    detail: &str,
) -> LoopReflectError {
    LoopReflectError {
        kind,
        span,
        detail: detail.to_owned(),
    }
}
