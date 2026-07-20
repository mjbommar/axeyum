//! Checked reflection of one canonical scalar LLVM self-loop.
//!
//! The first T5.1.4 profile deliberately recognizes only a single block with
//! one self back-edge, one exit edge, and two-incoming PHIs. The exit decision
//! is abstracted: the returned recurrence may continue after the source loop
//! exits. This is a sound over-approximation for state-invariant proofs, while
//! a reachable recurrence state is not a source counterexample until it is
//! separately replayed against the original program.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::error::Error;
use std::fmt;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{SolverError, TransitionSystem};

use super::checked::{DefinedValue, ReflectError, ReflectErrorKind, lower_assignment, resolve};
use super::syntax::{
    BlockId, Operand, ParseError, ScalarCfg, ScalarInstruction, ScalarInstructionKind, SourceSpan,
    TerminatorKind, parse_function, parse_scalar_cfg,
};

/// Stable failure classes for the canonical LLVM loop profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopReflectErrorKind {
    /// Structured LLVM parsing or CFG validation failed.
    Syntax,
    /// The CFG contains no cycle.
    NoCycle,
    /// More than one self-loop candidate exists.
    MultipleCycles,
    /// A cycle exists, but it is not the admitted single-block shape.
    NonCanonicalCycle,
    /// Loop PHIs do not have the exact entry/back-edge structure.
    InvalidPhi,
    /// A PHI initializer is not a constant or scalar function parameter.
    UnsupportedInitializer,
    /// A typed scalar loop-body operation is outside the admitted profile.
    UnsupportedBody,
    /// The loop reaches memory, which this scalar profile does not model.
    UnsupportedMemory,
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

/// One owned, typed canonical LLVM recurrence.
///
/// This system intentionally over-approximates the source exit edge. Use it to
/// prove invariants. Treat [`axeyum_solver::BmcOutcome::Reachable`] as an
/// abstract recurrence witness until the same state is replayed in source code.
#[derive(Debug, Clone)]
pub struct CanonicalLoopSystem {
    function: String,
    loop_block: BlockId,
    exit_block: BlockId,
    state: Vec<LoopStateComponent>,
    phis: Vec<LoopPhi>,
    parameters: Vec<LoopParameter>,
    instructions: Vec<ScalarInstruction>,
    branch_condition: Operand,
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

    /// Identity of the unique self-looping block.
    #[must_use]
    pub fn loop_block(&self) -> &BlockId {
        &self.loop_block
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
        let always = arena.bool_const(true);
        let mut env = HashMap::new();
        for (index, component) in self.state.iter().enumerate() {
            env.insert(
                component.name.clone(),
                DefinedValue {
                    value: arena.var(pre[index]),
                    defined: always,
                    width: component.width,
                },
            );
        }

        let mut conditions = Vec::new();
        for instruction in &self.instructions {
            let (dest, value, immediate) =
                lower_assignment(arena, &env, instruction.kind.clone(), instruction.span)
                    .map_err(BuildError::reflection)?;
            conditions.push(immediate);
            env.insert(dest, value);
        }

        let branch = resolve(arena, &env, &self.branch_condition, 1, self.branch_span)
            .map_err(BuildError::reflection)?;
        conditions.push(branch.defined);

        for (index, phi) in self.phis.iter().enumerate() {
            let component = &self.state[index];
            let next = resolve(arena, &env, &phi.back, component.width, phi.span)
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
            let pre_value = arena.var(pre[parameter.component]);
            conditions.push(
                arena
                    .eq(post_value, pre_value)
                    .map_err(|error| BuildError::ir(Some(parameter.span), error.to_string()))?,
            );
        }
        conjoin(arena, &conditions, self.branch_span)
    }

    fn build_bad(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, BuildError> {
        self.require_state_arity(state)?;
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
#[expect(
    clippy::too_many_lines,
    reason = "the canonical profile keeps every fail-closed structural gate visible in source order"
)]
pub fn reflect_canonical_loop_checked(
    llvm: &str,
    property: UnsignedPhiUpperBound,
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

    let mut parameter_widths = BTreeMap::new();
    for parameter in &function.params {
        let width = scalar_width(&parameter.ty).ok_or_else(|| {
            loop_error(
                LoopReflectErrorKind::UnsupportedBody,
                Some(parameter.span),
                &format!(
                    "canonical scalar loop requires i1 through i128 parameters; `%{}` has `{}`",
                    parameter.name, parameter.ty
                ),
            )
        })?;
        if parameter_widths
            .insert(parameter.name.clone(), (width, parameter.span))
            .is_some()
        {
            return Err(loop_error(
                LoopReflectErrorKind::UnsupportedBody,
                Some(parameter.span),
                &format!("duplicate LLVM parameter `%{}`", parameter.name),
            ));
        }
    }
    validate_unique_definitions(&cfg, &parameter_widths)?;

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

    for instruction in &block.instructions {
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
        exit_block,
        state,
        phis,
        parameters,
        instructions: block.instructions.clone(),
        branch_condition,
        branch_span: block.terminator.span,
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
    parameters: &BTreeMap<String, (u32, SourceSpan)>,
) -> Result<(), LoopReflectError> {
    let mut definitions = parameters.keys().cloned().collect::<BTreeSet<_>>();
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
        ScalarInstructionKind::GetElementPtr { index, .. } => {
            collect_parameter_operand(index, parameters, referenced);
        }
        ScalarInstructionKind::Load { .. }
        | ScalarInstructionKind::Store { .. }
        | ScalarInstructionKind::Return { .. } => {}
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

#[derive(Debug)]
enum BuildError {
    Reflection(ReflectError),
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
        BuildError::Reflection(error) => {
            let kind = match error.kind() {
                ReflectErrorKind::UnsupportedMemory => LoopReflectErrorKind::UnsupportedMemory,
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
