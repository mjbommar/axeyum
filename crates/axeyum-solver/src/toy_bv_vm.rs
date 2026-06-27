//! A tiny bit-vector register-machine frontend for symbolic execution.
//!
//! This module is intentionally small: it is a reusable library version of the
//! toy target used by the symbolic-execution tests, not a production binary
//! lifter. Its purpose is to make the P4.2 frontend contract concrete:
//! validate a program, lift each instruction into axeyum terms, explore the CFG
//! through [`SymbolicExecutor`], extract concrete model witnesses, and confirm
//! those witnesses by independent concrete replay.

use std::collections::BTreeMap;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};

use crate::backend::SolverError;
use crate::model::Model;
use crate::symexec::{
    CfgCheckedOutcome, CfgExploreConfig, CfgStep, SymbolicExecutor, SymbolicMemory,
};

/// A fixed-width bit-vector register-machine instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinyBvInsn {
    /// Write a constant to a register. `value` is truncated to the program
    /// width.
    Const {
        /// Destination register.
        dst: usize,
        /// Constant value before width truncation.
        value: u128,
    },
    /// Add two registers modulo `2^width`.
    Add {
        /// Destination register.
        dst: usize,
        /// Left input register.
        a: usize,
        /// Right input register.
        b: usize,
    },
    /// Subtract two registers modulo `2^width`.
    Sub {
        /// Destination register.
        dst: usize,
        /// Left input register.
        a: usize,
        /// Right input register.
        b: usize,
    },
    /// Multiply two registers modulo `2^width`.
    Mul {
        /// Destination register.
        dst: usize,
        /// Left input register.
        a: usize,
        /// Right input register.
        b: usize,
    },
    /// Bitwise XOR two registers.
    Xor {
        /// Destination register.
        dst: usize,
        /// Left input register.
        a: usize,
        /// Right input register.
        b: usize,
    },
    /// Load `memory[regs[addr]]` into `dst`.
    Load {
        /// Destination register.
        dst: usize,
        /// Register containing the memory address.
        addr: usize,
    },
    /// Store `regs[src]` at `memory[regs[addr]]`.
    Store {
        /// Register containing the memory address.
        addr: usize,
        /// Register containing the value to store.
        src: usize,
    },
    /// Branch on equality between a register and a constant.
    BranchEq {
        /// Register being tested.
        reg: usize,
        /// Constant value before width truncation.
        value: u128,
        /// Program counter to use when the equality is true.
        then_pc: usize,
        /// Program counter to use when the equality is false.
        else_pc: usize,
    },
    /// Branch on equality between two registers.
    BranchRegEq {
        /// Left register being tested.
        a: usize,
        /// Right register being tested.
        b: usize,
        /// Program counter to use when the equality is true.
        then_pc: usize,
        /// Program counter to use when the equality is false.
        else_pc: usize,
    },
    /// Target block reported as a successful reachability hit.
    Win,
    /// Terminal non-target block.
    Lose,
}

/// A validated tiny bit-vector register program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvProgram {
    width: u32,
    reg_count: usize,
    input_count: usize,
    max_steps: usize,
    code: Vec<TinyBvInsn>,
    labels: BTreeMap<String, usize>,
}

/// Symbolic frontend state for [`TinyBvProgram`] exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvState {
    /// Current program counter.
    pub pc: usize,
    /// Current symbolic register terms.
    pub regs: Vec<TermId>,
    /// Current symbolic memory term, present only when the program contains
    /// memory instructions.
    pub memory: Option<SymbolicMemory>,
    /// Remaining symbolic execution fuel.
    pub fuel: usize,
}

/// Concrete input words extracted from a model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvWitness {
    /// Concrete input values in register/input order, width-truncated.
    pub inputs: Vec<u128>,
}

/// Result of concrete replay for a [`TinyBvWitness`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinyBvConcreteOutcome {
    /// Concrete execution reached a [`TinyBvInsn::Win`] instruction.
    Win,
    /// Concrete execution reached [`TinyBvInsn::Lose`] or fell off the program.
    Lose,
    /// Concrete execution exhausted the program's fuel.
    OutOfFuel,
    /// The witness did not provide exactly the program's input count.
    InvalidInputCount,
}

/// One concrete instruction step in a replay trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvConcreteStep {
    /// Program counter executed by this step.
    pub pc: usize,
    /// Instruction executed at `pc`.
    pub instruction: TinyBvInsn,
    /// Register values before executing this instruction.
    pub regs_before: Vec<u128>,
}

/// Concrete replay trace for a [`TinyBvWitness`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvConcreteTrace {
    /// Executed instruction steps, in order.
    pub steps: Vec<TinyBvConcreteStep>,
    /// Terminal replay outcome.
    pub outcome: TinyBvConcreteOutcome,
    /// Program counter where replay stopped, when it is still inside the
    /// program. `None` means replay fell off the program or the witness shape was
    /// invalid.
    pub final_pc: Option<usize>,
    /// Register values at replay termination.
    pub final_regs: Vec<u128>,
    /// Explicit non-default memory cells at replay termination, sorted by
    /// address. Unlisted cells read as zero.
    pub final_memory: Vec<(u128, u128)>,
}

impl TinyBvConcreteTrace {
    /// Whether this trace executed `pc`.
    pub fn reaches_pc(&self, pc: usize) -> bool {
        self.steps.iter().any(|step| step.pc == pc)
    }
}

/// Checked symbolic-execution result for the tiny BV frontend.
pub type TinyBvExploreOutcome = CfgCheckedOutcome<TinyBvState, TinyBvWitness>;

/// Bounded reachability status for a tiny BV program counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinyBvReachabilityStatus {
    /// At least one solver-witnessed path reached the target and concrete replay
    /// accepted the extracted input.
    Reachable,
    /// Exploration exhausted the configured finite search without a target and
    /// without unknown branches, undecided targets, witness extraction failures,
    /// concrete mismatches, or truncation.
    Unreachable,
    /// The target was not verified reachable, but the search was incomplete or
    /// produced diagnostics that prevent a sound unreachable claim.
    Unknown,
}

/// Bounded reachability report for a tiny BV program counter.
#[derive(Debug, Clone)]
pub struct TinyBvReachabilityReport {
    /// Program counter being queried.
    pub target_pc: usize,
    /// Checked CFG exploration result for the target query.
    pub outcome: TinyBvExploreOutcome,
}

impl TinyBvReachabilityReport {
    /// Classifies this bounded reachability report.
    pub fn status(&self) -> TinyBvReachabilityStatus {
        if !self.outcome.verified.is_empty() {
            TinyBvReachabilityStatus::Reachable
        } else if self.outcome.missing_witnesses.is_empty()
            && self.outcome.mismatches.is_empty()
            && self.outcome.unknown_branches == 0
            && self.outcome.undecided_targets == 0
            && !self.outcome.truncated
        {
            TinyBvReachabilityStatus::Unreachable
        } else {
            TinyBvReachabilityStatus::Unknown
        }
    }

    /// Whether the target has at least one concrete-replayed witness.
    pub fn is_reachable(&self) -> bool {
        self.status() == TinyBvReachabilityStatus::Reachable
    }

    /// Whether the target was exhaustively ruled out within the configured
    /// bounds.
    pub fn is_unreachable(&self) -> bool {
        self.status() == TinyBvReachabilityStatus::Unreachable
    }
}

/// Bounded safety status for a forbidden tiny BV program counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinyBvSafetyStatus {
    /// The forbidden program counter was not reachable within the exhaustive
    /// bounded search.
    Safe,
    /// The forbidden program counter was reached by a concrete-replayed witness.
    Unsafe,
    /// The bounded search was incomplete or diagnostically inconclusive.
    Unknown,
}

/// Bounded safety report for a forbidden tiny BV program counter.
#[derive(Debug, Clone)]
pub struct TinyBvSafetyReport {
    /// Forbidden program counter.
    pub forbidden_pc: usize,
    /// Underlying reachability query for the forbidden counter.
    pub reachability: TinyBvReachabilityReport,
}

impl TinyBvSafetyReport {
    /// Classifies this bounded safety report.
    pub fn status(&self) -> TinyBvSafetyStatus {
        match self.reachability.status() {
            TinyBvReachabilityStatus::Reachable => TinyBvSafetyStatus::Unsafe,
            TinyBvReachabilityStatus::Unreachable => TinyBvSafetyStatus::Safe,
            TinyBvReachabilityStatus::Unknown => TinyBvSafetyStatus::Unknown,
        }
    }

    /// Whether the forbidden counter is proven unreachable within the configured
    /// bounds.
    pub fn is_safe(&self) -> bool {
        self.status() == TinyBvSafetyStatus::Safe
    }

    /// Whether the forbidden counter has a concrete-replayed counterexample.
    pub fn is_unsafe(&self) -> bool {
        self.status() == TinyBvSafetyStatus::Unsafe
    }
}

impl TinyBvProgram {
    /// Creates and validates a tiny bit-vector register program.
    ///
    /// The concrete replay layer stores register words in `u128`, so this
    /// frontend intentionally supports widths `1..=128` even though the core IR
    /// can represent wider bit-vectors.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] when the program shape is invalid:
    /// an unsupported width, no registers, too many input registers, no fuel, an
    /// empty program, an out-of-range register reference, or an out-of-range
    /// branch target.
    pub fn new(
        width: u32,
        reg_count: usize,
        input_count: usize,
        max_steps: usize,
        code: Vec<TinyBvInsn>,
    ) -> Result<Self, SolverError> {
        if !(1..=128).contains(&width) {
            return Err(tiny_bv_error(format!(
                "width must be in 1..=128, got {width}"
            )));
        }
        if reg_count == 0 {
            return Err(tiny_bv_error("register count must be nonzero"));
        }
        if input_count > reg_count {
            return Err(tiny_bv_error(format!(
                "input count {input_count} exceeds register count {reg_count}"
            )));
        }
        if max_steps == 0 {
            return Err(tiny_bv_error("max steps must be nonzero"));
        }
        if code.is_empty() {
            return Err(tiny_bv_error(
                "program must contain at least one instruction",
            ));
        }
        validate_code(&code, reg_count)?;
        Ok(Self {
            width,
            reg_count,
            input_count,
            max_steps,
            code,
            labels: BTreeMap::new(),
        })
    }

    /// Parses and validates a tiny bit-vector assembly program.
    ///
    /// The accepted format is intentionally small and line-oriented:
    ///
    /// - `const rD VALUE`
    /// - `add|sub|mul|xor rD rA rB`
    /// - `load rD rADDR`
    /// - `store rADDR rSRC`
    /// - `beq rREG VALUE|rOTHER THEN ELSE`
    /// - `win`
    /// - `lose`
    ///
    /// Registers must be written as `r0`, `r1`, etc. Values and branch targets
    /// accept decimal or `0x` hexadecimal notation. Branch targets may also be
    /// labels declared as `name:` on their own line or before an instruction
    /// (`name: win`). Blank lines and text after `#` or `;` are ignored.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Parse`] for malformed text and the same
    /// validation errors as [`Self::new`] for invalid program shapes.
    pub fn from_assembly(
        width: u32,
        reg_count: usize,
        input_count: usize,
        max_steps: usize,
        text: &str,
    ) -> Result<Self, SolverError> {
        let (code, labels) = parse_tiny_bv_assembly(text)?;
        let mut program = Self::new(width, reg_count, input_count, max_steps, code)?;
        program.labels = labels;
        Ok(program)
    }

    /// Program bit-vector width.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Number of registers in each symbolic and concrete state.
    pub fn reg_count(&self) -> usize {
        self.reg_count
    }

    /// Number of input registers initialized from symbolic variables.
    pub fn input_count(&self) -> usize {
        self.input_count
    }

    /// Maximum number of concrete or symbolic target steps.
    pub fn max_steps(&self) -> usize {
        self.max_steps
    }

    /// Program instructions.
    pub fn code(&self) -> &[TinyBvInsn] {
        &self.code
    }

    /// Label-to-program-counter map imported from assembly.
    ///
    /// Hand-built programs have no labels. Assembly labels always name an
    /// instruction inside [`Self::code`].
    pub fn labels(&self) -> &BTreeMap<String, usize> {
        &self.labels
    }

    /// Program counter for an assembly label.
    pub fn label_pc(&self, label: &str) -> Option<usize> {
        self.labels.get(label).copied()
    }

    /// Whether this program contains memory instructions.
    pub fn uses_memory(&self) -> bool {
        self.code
            .iter()
            .any(|insn| matches!(insn, TinyBvInsn::Load { .. } | TinyBvInsn::Store { .. }))
    }

    /// Declares this program's symbolic inputs in `arena`.
    ///
    /// Inputs are named `{prefix}{i}` for `i` in `0..input_count`; repeated calls
    /// with the same prefix reuse matching existing declarations.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if a generated name is already declared with a
    /// different sort.
    pub fn declare_inputs(
        &self,
        arena: &mut TermArena,
        prefix: &str,
    ) -> Result<Vec<SymbolId>, SolverError> {
        (0..self.input_count)
            .map(|i| {
                arena
                    .declare(&format!("{prefix}{i}"), Sort::BitVec(self.width))
                    .map_err(Into::into)
            })
            .collect()
    }

    /// Builds the symbolic initial state from declared input symbols.
    ///
    /// The first `input_count` registers are input variables; all remaining
    /// registers are initialized to zero.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the number of inputs is wrong, an input symbol
    /// has the wrong sort, or zero construction fails.
    pub fn initial_state(
        &self,
        arena: &mut TermArena,
        inputs: &[SymbolId],
    ) -> Result<TinyBvState, SolverError> {
        if inputs.len() != self.input_count {
            return Err(tiny_bv_error(format!(
                "expected {} inputs, got {}",
                self.input_count,
                inputs.len()
            )));
        }
        for &symbol in inputs {
            let (_, sort) = arena.symbol(symbol);
            if sort != Sort::BitVec(self.width) {
                return Err(tiny_bv_error(format!(
                    "input symbol #{} has sort {sort}, expected (_ BitVec {})",
                    symbol.index(),
                    self.width
                )));
            }
        }

        let mut regs: Vec<TermId> = inputs.iter().map(|&symbol| arena.var(symbol)).collect();
        let zero = arena.bv_const(self.width, 0)?;
        while regs.len() < self.reg_count {
            regs.push(zero);
        }
        let memory = if self.uses_memory() {
            let array = arena.const_array(self.width, zero)?;
            Some(SymbolicMemory::from_array(arena, array)?)
        } else {
            None
        };
        Ok(TinyBvState {
            pc: 0,
            regs,
            memory,
            fuel: self.max_steps,
        })
    }

    /// Explores this program symbolically and checks each target by concrete
    /// replay.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from input declaration, symbolic instruction
    /// lifting, solver exploration, witness extraction, or concrete checking.
    pub fn explore_checked(
        &self,
        arena: &mut TermArena,
        input_prefix: &str,
        config: CfgExploreConfig,
    ) -> Result<TinyBvExploreOutcome, SolverError> {
        let inputs = self.declare_inputs(arena, input_prefix)?;
        let initial = self.initial_state(arena, &inputs)?;
        let config = self.effective_config(config);
        let mut executor = SymbolicExecutor::new();
        executor.explore_cfg_checked(
            arena,
            initial,
            config,
            |arena, state| self.symbolic_step(arena, state),
            |model, _state| Ok(self.witness_from_model(model, &inputs)),
            |state, witness| {
                Ok(matches!(self.code.get(state.pc), Some(TinyBvInsn::Win))
                    && self.concrete_reaches_win(witness))
            },
        )
    }

    /// Checks whether a program counter is reachable and concrete-replays every
    /// reported witness.
    ///
    /// A [`TinyBvReachabilityStatus::Unreachable`] report is bounded: it means
    /// the configured DFS and this program's `max_steps` fuel exhaustively ruled
    /// out the target without unknowns, witness failures, concrete mismatches, or
    /// truncation. It is not an unbounded inductive proof.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `target_pc` is outside the program, or from
    /// input declaration, symbolic instruction lifting, solver exploration,
    /// witness extraction, or concrete checking.
    pub fn reach_pc_checked(
        &self,
        arena: &mut TermArena,
        input_prefix: &str,
        target_pc: usize,
        config: CfgExploreConfig,
    ) -> Result<TinyBvReachabilityReport, SolverError> {
        self.validate_target_pc(target_pc)?;
        let inputs = self.declare_inputs(arena, input_prefix)?;
        let initial = self.initial_state(arena, &inputs)?;
        let config = self.effective_config(config);
        let mut executor = SymbolicExecutor::new();
        let outcome = executor.explore_cfg_checked(
            arena,
            initial,
            config,
            |arena, state| self.symbolic_step_for_pc(arena, state, target_pc),
            |model, _state| Ok(self.witness_from_model(model, &inputs)),
            |state, witness| {
                Ok(state.pc == target_pc && self.concrete_reaches_pc(witness, target_pc))
            },
        )?;
        Ok(TinyBvReachabilityReport { target_pc, outcome })
    }

    /// Checks whether an assembly label is reachable and concrete-replays every
    /// reported witness.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if `label` is not known, or the same
    /// errors as [`Self::reach_pc_checked`] after resolving the label.
    pub fn reach_label_checked(
        &self,
        arena: &mut TermArena,
        input_prefix: &str,
        label: &str,
        config: CfgExploreConfig,
    ) -> Result<TinyBvReachabilityReport, SolverError> {
        let target_pc = self.resolve_label_pc(label)?;
        self.reach_pc_checked(arena, input_prefix, target_pc, config)
    }

    /// Checks bounded safety for a forbidden program counter.
    ///
    /// [`TinyBvSafetyStatus::Safe`] means the forbidden counter is unreachable
    /// under the same bounded/exhaustive conditions as
    /// [`TinyBvReachabilityStatus::Unreachable`]. [`TinyBvSafetyStatus::Unsafe`]
    /// carries concrete-replayed counterexamples in
    /// [`TinyBvSafetyReport::reachability`].
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] under the same conditions as
    /// [`Self::reach_pc_checked`].
    pub fn check_pc_safety_checked(
        &self,
        arena: &mut TermArena,
        input_prefix: &str,
        forbidden_pc: usize,
        config: CfgExploreConfig,
    ) -> Result<TinyBvSafetyReport, SolverError> {
        let reachability = self.reach_pc_checked(arena, input_prefix, forbidden_pc, config)?;
        Ok(TinyBvSafetyReport {
            forbidden_pc,
            reachability,
        })
    }

    /// Checks bounded safety for a forbidden assembly label.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if `label` is not known, or the same
    /// errors as [`Self::check_pc_safety_checked`] after resolving the label.
    pub fn check_label_safety_checked(
        &self,
        arena: &mut TermArena,
        input_prefix: &str,
        label: &str,
        config: CfgExploreConfig,
    ) -> Result<TinyBvSafetyReport, SolverError> {
        let forbidden_pc = self.resolve_label_pc(label)?;
        self.check_pc_safety_checked(arena, input_prefix, forbidden_pc, config)
    }

    /// Replays a concrete witness and returns the full executed trace.
    pub fn concrete_trace(&self, witness: &TinyBvWitness) -> TinyBvConcreteTrace {
        if witness.inputs.len() != self.input_count {
            return TinyBvConcreteTrace {
                steps: Vec::new(),
                outcome: TinyBvConcreteOutcome::InvalidInputCount,
                final_pc: None,
                final_regs: Vec::new(),
                final_memory: Vec::new(),
            };
        }

        let mut regs = vec![0; self.reg_count];
        for (reg, value) in regs.iter_mut().zip(witness.inputs.iter()) {
            *reg = self.normalize(*value);
        }
        let mut memory = BTreeMap::new();
        let mut steps = Vec::new();
        let mut pc = 0usize;
        for _ in 0..self.max_steps {
            let Some(&instruction) = self.code.get(pc) else {
                return TinyBvConcreteTrace {
                    steps,
                    outcome: TinyBvConcreteOutcome::Lose,
                    final_pc: None,
                    final_regs: regs,
                    final_memory: memory.into_iter().collect(),
                };
            };
            steps.push(TinyBvConcreteStep {
                pc,
                instruction,
                regs_before: regs.clone(),
            });
            if let Some(outcome) =
                self.execute_concrete_instruction(instruction, &mut regs, &mut memory, &mut pc)
            {
                return finish_concrete_trace(steps, outcome, Some(pc), regs, memory);
            }
        }
        finish_concrete_trace(
            steps,
            TinyBvConcreteOutcome::OutOfFuel,
            self.code.get(pc).map(|_| pc),
            regs,
            memory,
        )
    }

    fn execute_concrete_instruction(
        &self,
        instruction: TinyBvInsn,
        regs: &mut [u128],
        memory: &mut BTreeMap<u128, u128>,
        pc: &mut usize,
    ) -> Option<TinyBvConcreteOutcome> {
        match instruction {
            TinyBvInsn::Const { dst, value } => {
                regs[dst] = self.normalize(value);
                *pc += 1;
            }
            TinyBvInsn::Add { dst, a, b } => {
                regs[dst] = self.normalize(regs[a].wrapping_add(regs[b]));
                *pc += 1;
            }
            TinyBvInsn::Sub { dst, a, b } => {
                regs[dst] = self.normalize(regs[a].wrapping_sub(regs[b]));
                *pc += 1;
            }
            TinyBvInsn::Mul { dst, a, b } => {
                regs[dst] = self.normalize(regs[a].wrapping_mul(regs[b]));
                *pc += 1;
            }
            TinyBvInsn::Xor { dst, a, b } => {
                regs[dst] = self.normalize(regs[a] ^ regs[b]);
                *pc += 1;
            }
            TinyBvInsn::Load { dst, addr } => {
                regs[dst] = *memory.get(&regs[addr]).unwrap_or(&0);
                *pc += 1;
            }
            TinyBvInsn::Store { addr, src } => {
                memory.insert(regs[addr], regs[src]);
                *pc += 1;
            }
            TinyBvInsn::BranchEq {
                reg,
                value,
                then_pc,
                else_pc,
            } => {
                *pc = if regs[reg] == self.normalize(value) {
                    then_pc
                } else {
                    else_pc
                };
            }
            TinyBvInsn::BranchRegEq {
                a,
                b,
                then_pc,
                else_pc,
            } => {
                *pc = if regs[a] == regs[b] { then_pc } else { else_pc };
            }
            TinyBvInsn::Win => return Some(TinyBvConcreteOutcome::Win),
            TinyBvInsn::Lose => return Some(TinyBvConcreteOutcome::Lose),
        }
        None
    }

    /// Replays a concrete witness under this program's concrete semantics.
    pub fn concrete_run(&self, witness: &TinyBvWitness) -> TinyBvConcreteOutcome {
        self.concrete_trace(witness).outcome
    }

    /// Returns whether a witness concretely reaches [`TinyBvInsn::Win`].
    pub fn concrete_reaches_win(&self, witness: &TinyBvWitness) -> bool {
        self.concrete_run(witness) == TinyBvConcreteOutcome::Win
    }

    /// Returns whether a witness concretely reaches `target_pc` before
    /// termination or fuel exhaustion.
    pub fn concrete_reaches_pc(&self, witness: &TinyBvWitness, target_pc: usize) -> bool {
        if target_pc >= self.code.len() {
            return false;
        }
        self.concrete_trace(witness).reaches_pc(target_pc)
    }

    fn symbolic_step(
        &self,
        arena: &mut TermArena,
        state: TinyBvState,
    ) -> Result<CfgStep<TinyBvState>, SolverError> {
        if state.fuel == 0 || state.pc >= self.code.len() {
            return Ok(CfgStep::Stop);
        }
        let next_fuel = state.fuel - 1;
        match self.code[state.pc] {
            TinyBvInsn::Const { dst, value } => {
                let mut next = state;
                next.regs[dst] = arena.bv_const(self.width, self.normalize(value))?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Add { dst, a, b } => {
                let mut next = state;
                next.regs[dst] = arena.bv_add(next.regs[a], next.regs[b])?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Sub { dst, a, b } => {
                let mut next = state;
                next.regs[dst] = arena.bv_sub(next.regs[a], next.regs[b])?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Mul { dst, a, b } => {
                let mut next = state;
                next.regs[dst] = arena.bv_mul(next.regs[a], next.regs[b])?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Xor { dst, a, b } => {
                let mut next = state;
                next.regs[dst] = arena.bv_xor(next.regs[a], next.regs[b])?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Load { dst, addr } => {
                let mut next = state;
                let memory = next
                    .memory
                    .ok_or_else(|| tiny_bv_error("load requires initialized memory"))?;
                next.regs[dst] = memory.load(arena, next.regs[addr])?;
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::Store { addr, src } => {
                let mut next = state;
                let mut memory = next
                    .memory
                    .ok_or_else(|| tiny_bv_error("store requires initialized memory"))?;
                memory.store(arena, next.regs[addr], next.regs[src])?;
                next.memory = Some(memory);
                next.pc += 1;
                next.fuel = next_fuel;
                Ok(CfgStep::Continue(next))
            }
            TinyBvInsn::BranchEq {
                reg,
                value,
                then_pc,
                else_pc,
            } => {
                let value_term = arena.bv_const(self.width, self.normalize(value))?;
                let condition = arena.eq(state.regs[reg], value_term)?;
                Ok(symbolic_branch(
                    condition, state, next_fuel, then_pc, else_pc,
                ))
            }
            TinyBvInsn::BranchRegEq {
                a,
                b,
                then_pc,
                else_pc,
            } => {
                let condition = arena.eq(state.regs[a], state.regs[b])?;
                Ok(symbolic_branch(
                    condition, state, next_fuel, then_pc, else_pc,
                ))
            }
            TinyBvInsn::Win => Ok(CfgStep::Target(state)),
            TinyBvInsn::Lose => Ok(CfgStep::Stop),
        }
    }

    fn symbolic_step_for_pc(
        &self,
        arena: &mut TermArena,
        state: TinyBvState,
        target_pc: usize,
    ) -> Result<CfgStep<TinyBvState>, SolverError> {
        if state.pc == target_pc {
            Ok(CfgStep::Target(state))
        } else {
            self.symbolic_step(arena, state)
        }
    }

    fn witness_from_model(&self, model: &Model, inputs: &[SymbolId]) -> Option<TinyBvWitness> {
        let mut values = Vec::with_capacity(inputs.len());
        for &symbol in inputs {
            let (width, value) = match model.get(symbol) {
                Some(Value::Bv { width, value }) => (width, value),
                None => (self.width, 0),
                Some(_) => return None,
            };
            if width != self.width {
                return None;
            }
            values.push(self.normalize(value));
        }
        Some(TinyBvWitness { inputs: values })
    }

    fn normalize(&self, value: u128) -> u128 {
        value & self.mask()
    }

    fn mask(&self) -> u128 {
        if self.width == 128 {
            u128::MAX
        } else {
            (1u128 << self.width) - 1
        }
    }

    fn validate_target_pc(&self, target_pc: usize) -> Result<(), SolverError> {
        if target_pc < self.code.len() {
            Ok(())
        } else {
            Err(tiny_bv_error(format!(
                "target pc {target_pc} is outside program length {}",
                self.code.len()
            )))
        }
    }

    fn resolve_label_pc(&self, label: &str) -> Result<usize, SolverError> {
        self.label_pc(label)
            .ok_or_else(|| tiny_bv_error(format!("unknown assembly label `{label}`")))
    }

    fn effective_config(&self, mut config: CfgExploreConfig) -> CfgExploreConfig {
        if self.uses_memory() {
            config.memory_aware = true;
        }
        config
    }
}

fn finish_concrete_trace(
    steps: Vec<TinyBvConcreteStep>,
    outcome: TinyBvConcreteOutcome,
    final_pc: Option<usize>,
    regs: Vec<u128>,
    memory: BTreeMap<u128, u128>,
) -> TinyBvConcreteTrace {
    TinyBvConcreteTrace {
        steps,
        outcome,
        final_pc,
        final_regs: regs,
        final_memory: memory.into_iter().collect(),
    }
}

fn symbolic_branch(
    condition: TermId,
    state: TinyBvState,
    next_fuel: usize,
    then_pc: usize,
    else_pc: usize,
) -> CfgStep<TinyBvState> {
    let mut if_true = state.clone();
    if_true.pc = then_pc;
    if_true.fuel = next_fuel;
    let mut if_false = state;
    if_false.pc = else_pc;
    if_false.fuel = next_fuel;
    CfgStep::Branch {
        condition,
        if_true,
        if_false,
    }
}

fn validate_code(code: &[TinyBvInsn], reg_count: usize) -> Result<(), SolverError> {
    for (pc, insn) in code.iter().enumerate() {
        match *insn {
            TinyBvInsn::Const { dst, .. } => validate_reg(pc, dst, reg_count)?,
            TinyBvInsn::Add { dst, a, b }
            | TinyBvInsn::Sub { dst, a, b }
            | TinyBvInsn::Mul { dst, a, b }
            | TinyBvInsn::Xor { dst, a, b } => {
                validate_reg(pc, dst, reg_count)?;
                validate_reg(pc, a, reg_count)?;
                validate_reg(pc, b, reg_count)?;
            }
            TinyBvInsn::Load { dst, addr } => {
                validate_reg(pc, dst, reg_count)?;
                validate_reg(pc, addr, reg_count)?;
            }
            TinyBvInsn::Store { addr, src } => {
                validate_reg(pc, addr, reg_count)?;
                validate_reg(pc, src, reg_count)?;
            }
            TinyBvInsn::BranchEq {
                reg,
                then_pc,
                else_pc,
                ..
            } => {
                validate_reg(pc, reg, reg_count)?;
                validate_pc(pc, then_pc, code.len())?;
                validate_pc(pc, else_pc, code.len())?;
            }
            TinyBvInsn::BranchRegEq {
                a,
                b,
                then_pc,
                else_pc,
            } => {
                validate_reg(pc, a, reg_count)?;
                validate_reg(pc, b, reg_count)?;
                validate_pc(pc, then_pc, code.len())?;
                validate_pc(pc, else_pc, code.len())?;
            }
            TinyBvInsn::Win | TinyBvInsn::Lose => {}
        }
    }
    Ok(())
}

fn validate_reg(pc: usize, reg: usize, reg_count: usize) -> Result<(), SolverError> {
    if reg < reg_count {
        Ok(())
    } else {
        Err(tiny_bv_error(format!(
            "instruction {pc} references register {reg}, but register count is {reg_count}"
        )))
    }
}

fn validate_pc(pc: usize, target: usize, code_len: usize) -> Result<(), SolverError> {
    if target < code_len {
        Ok(())
    } else {
        Err(tiny_bv_error(format!(
            "instruction {pc} branches to pc {target}, but program length is {code_len}"
        )))
    }
}

fn parse_tiny_bv_assembly(
    text: &str,
) -> Result<(Vec<TinyBvInsn>, BTreeMap<String, usize>), SolverError> {
    let mut labels = BTreeMap::new();
    let mut lines = Vec::new();
    for (line_index, raw_line) in text.lines().enumerate() {
        let line_no = line_index + 1;
        let Some(line) = clean_assembly_line(raw_line) else {
            continue;
        };
        let (label, instruction) = split_assembly_label(line_no, line)?;
        if let Some(label) = label {
            if let Some((_, first_line)) = labels.insert(label.to_owned(), (lines.len(), line_no)) {
                return Err(tiny_bv_parse_error(
                    line_no,
                    format!("duplicate label `{label}` first declared on line {first_line}"),
                ));
            }
        }
        if let Some(instruction) = instruction {
            lines.push((line_no, instruction));
        }
    }

    for (label, (pc, line_no)) in &labels {
        if *pc >= lines.len() {
            return Err(tiny_bv_parse_error(
                *line_no,
                format!("label `{label}` does not name an instruction"),
            ));
        }
    }

    let mut code = Vec::with_capacity(lines.len());
    for (line_no, line) in lines {
        code.push(parse_tiny_bv_instruction(line_no, line, &labels)?);
    }
    let label_pcs = labels
        .into_iter()
        .map(|(label, (pc, _))| (label, pc))
        .collect();
    Ok((code, label_pcs))
}

fn clean_assembly_line(raw_line: &str) -> Option<&str> {
    let before_hash = raw_line
        .split_once('#')
        .map_or(raw_line, |(before, _)| before);
    let before_semicolon = before_hash
        .split_once(';')
        .map_or(before_hash, |(before, _)| before);
    let trimmed = before_semicolon.trim();
    (!trimmed.is_empty()).then_some(trimmed)
}

fn split_assembly_label(
    line_no: usize,
    line: &str,
) -> Result<(Option<&str>, Option<&str>), SolverError> {
    let Some((label, rest)) = line.split_once(':') else {
        return Ok((None, Some(line)));
    };
    if label.split_whitespace().count() != 1 {
        return Ok((None, Some(line)));
    }
    validate_label(line_no, label)?;
    let instruction = rest.trim();
    Ok((
        Some(label),
        (!instruction.is_empty()).then_some(instruction),
    ))
}

fn parse_tiny_bv_instruction(
    line_no: usize,
    line: &str,
    labels: &BTreeMap<String, (usize, usize)>,
) -> Result<TinyBvInsn, SolverError> {
    let tokens = line
        .split(|ch: char| ch.is_ascii_whitespace() || ch == ',')
        .filter(|token| !token.is_empty())
        .collect::<Vec<_>>();
    let Some((opcode, args)) = tokens.split_first() else {
        return Err(tiny_bv_parse_error(line_no, "empty instruction"));
    };
    let opcode = opcode.to_ascii_lowercase();
    match opcode.as_str() {
        "const" => match args {
            [dst, value] => Ok(TinyBvInsn::Const {
                dst: parse_register(line_no, dst)?,
                value: parse_u128_literal(line_no, "constant", value)?,
            }),
            _ => Err(tiny_bv_arity_error(line_no, "const", "rD VALUE")),
        },
        "add" | "sub" | "mul" | "xor" => parse_three_register_instruction(line_no, &opcode, args),
        "load" => match args {
            [dst, addr] => Ok(TinyBvInsn::Load {
                dst: parse_register(line_no, dst)?,
                addr: parse_register(line_no, addr)?,
            }),
            _ => Err(tiny_bv_arity_error(line_no, "load", "rD rADDR")),
        },
        "store" => match args {
            [addr, src] => Ok(TinyBvInsn::Store {
                addr: parse_register(line_no, addr)?,
                src: parse_register(line_no, src)?,
            }),
            _ => Err(tiny_bv_arity_error(line_no, "store", "rADDR rSRC")),
        },
        "beq" | "brancheq" => match args {
            [reg, value_or_reg, then_pc, else_pc] => {
                parse_branch_eq_instruction(line_no, reg, value_or_reg, then_pc, else_pc, labels)
            }
            _ => Err(tiny_bv_arity_error(
                line_no,
                "beq",
                "rREG VALUE|rOTHER THEN ELSE",
            )),
        },
        "win" => parse_no_args(line_no, "win", args, TinyBvInsn::Win),
        "lose" => parse_no_args(line_no, "lose", args, TinyBvInsn::Lose),
        other => Err(tiny_bv_parse_error(
            line_no,
            format!("unknown opcode `{other}`"),
        )),
    }
}

fn parse_branch_eq_instruction(
    line_no: usize,
    reg: &str,
    value_or_reg: &str,
    then_pc: &str,
    else_pc: &str,
    labels: &BTreeMap<String, (usize, usize)>,
) -> Result<TinyBvInsn, SolverError> {
    let reg = parse_register(line_no, reg)?;
    let then_pc = parse_pc_target(line_no, "then target", then_pc, labels)?;
    let else_pc = parse_pc_target(line_no, "else target", else_pc, labels)?;
    if value_or_reg.starts_with('r') {
        Ok(TinyBvInsn::BranchRegEq {
            a: reg,
            b: parse_register(line_no, value_or_reg)?,
            then_pc,
            else_pc,
        })
    } else {
        Ok(TinyBvInsn::BranchEq {
            reg,
            value: parse_u128_literal(line_no, "branch constant", value_or_reg)?,
            then_pc,
            else_pc,
        })
    }
}

fn validate_label(line_no: usize, label: &str) -> Result<(), SolverError> {
    let mut chars = label.chars();
    let Some(first) = chars.next() else {
        return Err(tiny_bv_parse_error(line_no, "empty label"));
    };
    if !(first == '_' || first == '.' || first.is_ascii_alphabetic()) {
        return Err(tiny_bv_parse_error(
            line_no,
            format!("invalid label `{label}`: labels must start with ASCII letter, `_`, or `.`"),
        ));
    }
    if chars.all(is_label_tail_char) {
        Ok(())
    } else {
        Err(tiny_bv_parse_error(
            line_no,
            format!(
                "invalid label `{label}`: labels may contain only ASCII letters, digits, `_`, `.`, or `$`"
            ),
        ))
    }
}

fn is_label_tail_char(ch: char) -> bool {
    ch == '_' || ch == '.' || ch == '$' || ch.is_ascii_alphanumeric()
}

fn parse_three_register_instruction(
    line_no: usize,
    opcode: &str,
    args: &[&str],
) -> Result<TinyBvInsn, SolverError> {
    let [dst, a, b] = args else {
        return Err(tiny_bv_arity_error(line_no, opcode, "rD rA rB"));
    };
    let dst = parse_register(line_no, dst)?;
    let a = parse_register(line_no, a)?;
    let b = parse_register(line_no, b)?;
    match opcode {
        "add" => Ok(TinyBvInsn::Add { dst, a, b }),
        "sub" => Ok(TinyBvInsn::Sub { dst, a, b }),
        "mul" => Ok(TinyBvInsn::Mul { dst, a, b }),
        "xor" => Ok(TinyBvInsn::Xor { dst, a, b }),
        _ => unreachable!("caller restricts opcode"),
    }
}

fn parse_no_args(
    line_no: usize,
    opcode: &str,
    args: &[&str],
    instruction: TinyBvInsn,
) -> Result<TinyBvInsn, SolverError> {
    if args.is_empty() {
        Ok(instruction)
    } else {
        Err(tiny_bv_arity_error(line_no, opcode, ""))
    }
}

fn parse_register(line_no: usize, token: &str) -> Result<usize, SolverError> {
    let Some(index) = token.strip_prefix('r') else {
        return Err(tiny_bv_parse_error(
            line_no,
            format!("expected register like `r0`, got `{token}`"),
        ));
    };
    if index.is_empty() {
        return Err(tiny_bv_parse_error(line_no, "empty register index"));
    }
    index
        .parse::<usize>()
        .map_err(|_| tiny_bv_parse_error(line_no, format!("invalid register index `{index}`")))
}

fn parse_pc_target(
    line_no: usize,
    name: &str,
    token: &str,
    labels: &BTreeMap<String, (usize, usize)>,
) -> Result<usize, SolverError> {
    if is_numeric_literal(token) {
        parse_usize_literal(line_no, name, token)
    } else {
        labels
            .get(token)
            .map(|(pc, _)| *pc)
            .ok_or_else(|| tiny_bv_parse_error(line_no, format!("unknown {name} label `{token}`")))
    }
}

fn is_numeric_literal(token: &str) -> bool {
    token
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_digit())
}

fn parse_usize_literal(line_no: usize, name: &str, token: &str) -> Result<usize, SolverError> {
    let value = parse_u128_literal(line_no, name, token)?;
    value.try_into().map_err(|_| {
        tiny_bv_parse_error(line_no, format!("{name} `{token}` does not fit in usize"))
    })
}

fn parse_u128_literal(line_no: usize, name: &str, token: &str) -> Result<u128, SolverError> {
    if let Some(hex) = token
        .strip_prefix("0x")
        .or_else(|| token.strip_prefix("0X"))
    {
        if hex.is_empty() {
            return Err(tiny_bv_parse_error(
                line_no,
                format!("empty {name} literal"),
            ));
        }
        u128::from_str_radix(hex, 16)
    } else {
        token.parse::<u128>()
    }
    .map_err(|_| tiny_bv_parse_error(line_no, format!("invalid {name} literal `{token}`")))
}

fn tiny_bv_arity_error(line_no: usize, opcode: &str, expected: &str) -> SolverError {
    let detail = if expected.is_empty() {
        format!("`{opcode}` takes no operands")
    } else {
        format!("`{opcode}` expects {expected}")
    };
    tiny_bv_parse_error(line_no, detail)
}

fn tiny_bv_parse_error(line_no: usize, message: impl Into<String>) -> SolverError {
    SolverError::Parse(format!(
        "tiny BV assembly line {line_no}: {}",
        message.into()
    ))
}

fn tiny_bv_error(message: impl Into<String>) -> SolverError {
    let message = message.into();
    SolverError::Unsupported(format!("tiny BV VM: {message}"))
}
