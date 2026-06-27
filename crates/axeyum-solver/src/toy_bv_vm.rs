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
        })
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
            match instruction {
                TinyBvInsn::Const { dst, value } => {
                    regs[dst] = self.normalize(value);
                    pc += 1;
                }
                TinyBvInsn::Add { dst, a, b } => {
                    regs[dst] = self.normalize(regs[a].wrapping_add(regs[b]));
                    pc += 1;
                }
                TinyBvInsn::Sub { dst, a, b } => {
                    regs[dst] = self.normalize(regs[a].wrapping_sub(regs[b]));
                    pc += 1;
                }
                TinyBvInsn::Mul { dst, a, b } => {
                    regs[dst] = self.normalize(regs[a].wrapping_mul(regs[b]));
                    pc += 1;
                }
                TinyBvInsn::Xor { dst, a, b } => {
                    regs[dst] = self.normalize(regs[a] ^ regs[b]);
                    pc += 1;
                }
                TinyBvInsn::Load { dst, addr } => {
                    regs[dst] = *memory.get(&regs[addr]).unwrap_or(&0);
                    pc += 1;
                }
                TinyBvInsn::Store { addr, src } => {
                    memory.insert(regs[addr], regs[src]);
                    pc += 1;
                }
                TinyBvInsn::BranchEq {
                    reg,
                    value,
                    then_pc,
                    else_pc,
                } => {
                    pc = if regs[reg] == self.normalize(value) {
                        then_pc
                    } else {
                        else_pc
                    };
                }
                TinyBvInsn::Win => {
                    return TinyBvConcreteTrace {
                        steps,
                        outcome: TinyBvConcreteOutcome::Win,
                        final_pc: Some(pc),
                        final_regs: regs,
                        final_memory: memory.into_iter().collect(),
                    };
                }
                TinyBvInsn::Lose => {
                    return TinyBvConcreteTrace {
                        steps,
                        outcome: TinyBvConcreteOutcome::Lose,
                        final_pc: Some(pc),
                        final_regs: regs,
                        final_memory: memory.into_iter().collect(),
                    };
                }
            }
        }
        TinyBvConcreteTrace {
            steps,
            outcome: TinyBvConcreteOutcome::OutOfFuel,
            final_pc: self.code.get(pc).map(|_| pc),
            final_regs: regs,
            final_memory: memory.into_iter().collect(),
        }
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
                let mut if_true = state.clone();
                if_true.pc = then_pc;
                if_true.fuel = next_fuel;
                let mut if_false = state;
                if_false.pc = else_pc;
                if_false.fuel = next_fuel;
                Ok(CfgStep::Branch {
                    condition,
                    if_true,
                    if_false,
                })
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

    fn effective_config(&self, mut config: CfgExploreConfig) -> CfgExploreConfig {
        if self.uses_memory() {
            config.memory_aware = true;
        }
        config
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

fn tiny_bv_error(message: impl Into<String>) -> SolverError {
    let message = message.into();
    SolverError::Unsupported(format!("tiny BV VM: {message}"))
}
