//! A tiny bit-vector register-machine frontend for symbolic execution.
//!
//! This module is intentionally small: it is a reusable library version of the
//! toy target used by the symbolic-execution tests, not a production binary
//! lifter. Its purpose is to make the P4.2 frontend contract concrete:
//! validate a program, lift each instruction into axeyum terms, explore the CFG
//! through [`SymbolicExecutor`], extract concrete model witnesses, and confirm
//! those witnesses by independent concrete replay.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

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
    source_lines: BTreeMap<usize, usize>,
}

/// Control-flow edge kind in a [`TinyBvProgram`] CFG.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinyBvCfgEdgeKind {
    /// Ordinary instruction fallthrough to the next program counter.
    Fallthrough,
    /// True branch of [`TinyBvInsn::BranchEq`] or [`TinyBvInsn::BranchRegEq`].
    BranchTrue,
    /// False branch of [`TinyBvInsn::BranchEq`] or [`TinyBvInsn::BranchRegEq`].
    BranchFalse,
}

/// One static CFG edge in a [`TinyBvProgram`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TinyBvCfgEdge {
    /// Source program counter.
    pub from: usize,
    /// Destination program counter.
    pub to: usize,
    /// Edge classification.
    pub kind: TinyBvCfgEdgeKind,
}

/// One static basic block in a [`TinyBvProgram`] CFG.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvBasicBlock {
    /// First program counter in the block.
    pub start_pc: usize,
    /// Program counter immediately after the block.
    pub end_pc: usize,
    /// Assembly labels attached to `start_pc`, in deterministic label order.
    pub labels: Vec<String>,
    /// One source-line entry per instruction in `[start_pc, end_pc)`.
    ///
    /// Hand-built programs have no imported source metadata, so these entries
    /// are `None`.
    pub source_lines: Vec<Option<usize>>,
    /// Outgoing CFG edges from the block's final instruction.
    pub outgoing: Vec<TinyBvCfgEdge>,
}

/// Block-aware view of a contiguous concrete replay segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvTraceBlockStep {
    /// Static basic block that contains the executed PCs.
    pub block: TinyBvBasicBlock,
    /// Executed instruction PCs in this contiguous visit to `block`.
    pub executed_pcs: Vec<usize>,
}

/// Source-aware view of one concrete CFG edge taken by replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvTraceEdgeStep {
    /// Static CFG edge taken between two consecutive replay steps.
    pub edge: TinyBvCfgEdge,
    /// One-based source line for `edge.from`, when imported from assembly.
    pub from_source_line: Option<usize>,
    /// One-based source line for `edge.to`, when imported from assembly.
    pub to_source_line: Option<usize>,
    /// Assembly labels attached to `edge.from`, in deterministic order.
    pub from_labels: Vec<String>,
    /// Assembly labels attached to `edge.to`, in deterministic order.
    pub to_labels: Vec<String>,
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

/// Source-aware view of one concrete replay step.
///
/// This is derived from a [`TinyBvConcreteTrace`] and a [`TinyBvProgram`].
/// Hand-built programs have no imported source metadata, so `source_line` is
/// `None` and `labels` is empty for those traces.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvTraceSourceStep {
    /// Program counter executed by this step.
    pub pc: usize,
    /// One-based assembly source line for `pc`, when the program was imported
    /// from assembly.
    pub source_line: Option<usize>,
    /// Assembly labels attached to `pc`, in deterministic label order.
    pub labels: Vec<String>,
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

/// Complete concrete witness report for a tiny BV replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinyBvTraceReport {
    /// Concrete input witness being replayed.
    pub witness: TinyBvWitness,
    /// Canonical concrete replay trace.
    pub trace: TinyBvConcreteTrace,
    /// Source-aware instruction-step rows derived from `trace`.
    pub source_steps: Vec<TinyBvTraceSourceStep>,
    /// Contiguous basic-block visits derived from `trace`.
    pub block_steps: Vec<TinyBvTraceBlockStep>,
    /// Static CFG edges taken by `trace`.
    pub edge_steps: Vec<TinyBvTraceEdgeStep>,
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
            source_lines: BTreeMap::new(),
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
        let parsed = parse_tiny_bv_assembly(text)?;
        let mut program = Self::new(width, reg_count, input_count, max_steps, parsed.code)?;
        program.labels = parsed.labels;
        program.source_lines = parsed.source_lines;
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

    /// Static CFG successors for a program counter.
    ///
    /// Fallthrough instructions have at most one edge to `pc + 1`; if the
    /// instruction is the final instruction, falling off the program is a
    /// terminal condition and no edge is returned. Branch instructions return
    /// two edges in deterministic true-then-false order, even if both edges
    /// target the same PC. Terminal `win`/`lose` instructions have no
    /// successors.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if `pc` is outside the program.
    pub fn successors(&self, pc: usize) -> Result<Vec<TinyBvCfgEdge>, SolverError> {
        let Some(&instruction) = self.code.get(pc) else {
            return Err(tiny_bv_error(format!(
                "source pc {pc} is outside program length {}",
                self.code.len()
            )));
        };
        Ok(self.instruction_successors(pc, instruction))
    }

    /// All static CFG edges in program-counter order.
    pub fn cfg_edges(&self) -> Vec<TinyBvCfgEdge> {
        self.code
            .iter()
            .enumerate()
            .flat_map(|(pc, &instruction)| self.instruction_successors(pc, instruction))
            .collect()
    }

    /// Static basic blocks in deterministic program-counter order.
    ///
    /// Block leaders are: entry PC 0, assembly labels, branch targets, and the
    /// instruction after a branch or terminal instruction when it exists. Each
    /// block covers a contiguous instruction range, carries source/label
    /// metadata for frontend reporting, and exposes outgoing edges from its
    /// final instruction.
    pub fn basic_blocks(&self) -> Vec<TinyBvBasicBlock> {
        let leaders = self.basic_block_leaders().into_iter().collect::<Vec<_>>();
        leaders
            .iter()
            .enumerate()
            .map(|(index, &start_pc)| {
                let end_pc = leaders.get(index + 1).copied().unwrap_or(self.code.len());
                let outgoing = self.instruction_successors(end_pc - 1, self.code[end_pc - 1]);
                TinyBvBasicBlock {
                    start_pc,
                    end_pc,
                    labels: self
                        .labels_at_pc(start_pc)
                        .into_iter()
                        .map(ToOwned::to_owned)
                        .collect(),
                    source_lines: (start_pc..end_pc).map(|pc| self.source_line(pc)).collect(),
                    outgoing,
                }
            })
            .collect()
    }

    /// Deterministic Graphviz DOT for the static basic-block CFG.
    ///
    /// Nodes are the blocks returned by [`Self::basic_blocks`], in
    /// program-counter order. Edges are the outgoing edges from each block's
    /// terminator, mapped to the destination block, and are labelled as
    /// `fallthrough`, `true`, or `false`. Source-line and label metadata is
    /// included in node labels when present, so frontend tools can render the
    /// same graph that trace reports reference without rebuilding the CFG.
    pub fn cfg_dot(&self) -> String {
        let blocks = self.basic_blocks();
        let block_start_by_pc = blocks
            .iter()
            .flat_map(|block| (block.start_pc..block.end_pc).map(|pc| (pc, block.start_pc)))
            .collect::<BTreeMap<_, _>>();
        let mut dot = String::from("digraph tiny_bv_cfg {\n");
        dot.push_str("  rankdir=TB;\n");
        for block in &blocks {
            writeln!(
                &mut dot,
                "  bb_{} [label=\"{}\"];",
                block.start_pc,
                tiny_bv_dot_escape_label(&tiny_bv_basic_block_dot_label(block))
            )
            .expect("writing DOT into a String cannot fail");
        }
        for block in &blocks {
            for edge in &block.outgoing {
                if let Some(target_start_pc) = block_start_by_pc.get(&edge.to) {
                    writeln!(
                        &mut dot,
                        "  bb_{} -> bb_{} [label=\"{}\"];",
                        block.start_pc,
                        target_start_pc,
                        tiny_bv_cfg_edge_kind_dot_label(edge.kind)
                    )
                    .expect("writing DOT into a String cannot fail");
                }
            }
        }
        dot.push_str("}\n");
        dot
    }

    /// Static basic block containing `pc`.
    pub fn basic_block_containing_pc(&self, pc: usize) -> Option<TinyBvBasicBlock> {
        self.basic_blocks()
            .into_iter()
            .find(|block| (block.start_pc..block.end_pc).contains(&pc))
    }

    /// Groups a concrete instruction trace into contiguous static basic-block
    /// visits.
    ///
    /// Consecutive executed PCs in the same block are compressed into one row.
    /// If execution leaves and later re-enters the same block, that re-entry is
    /// reported as a new row. Public traces can be constructed manually; any
    /// step whose PC does not belong to this program is ignored.
    pub fn trace_basic_blocks(&self, trace: &TinyBvConcreteTrace) -> Vec<TinyBvTraceBlockStep> {
        let blocks = self.basic_blocks();
        let mut path: Vec<TinyBvTraceBlockStep> = Vec::new();
        for step in &trace.steps {
            let Some(block) = blocks
                .iter()
                .find(|block| (block.start_pc..block.end_pc).contains(&step.pc))
            else {
                continue;
            };
            if let Some(last) = path.last_mut()
                && last.block.start_pc == block.start_pc
            {
                last.executed_pcs.push(step.pc);
            } else {
                path.push(TinyBvTraceBlockStep {
                    block: block.clone(),
                    executed_pcs: vec![step.pc],
                });
            }
        }
        path
    }

    /// Derives source-aware CFG edges taken by a concrete replay trace.
    ///
    /// The method looks at each pair of consecutive executed PCs and keeps the
    /// matching static successor edge. Public traces can be constructed
    /// manually; invalid or cross-program transitions are ignored. If a branch's
    /// true and false arms both target the same PC, the deterministic
    /// true-then-false successor order makes the edge ambiguous and the true
    /// edge is reported.
    pub fn trace_cfg_edges(&self, trace: &TinyBvConcreteTrace) -> Vec<TinyBvTraceEdgeStep> {
        trace
            .steps
            .windows(2)
            .filter_map(|steps| {
                let from_pc = steps[0].pc;
                let to_pc = steps[1].pc;
                let edge = self
                    .successors(from_pc)
                    .ok()?
                    .into_iter()
                    .find(|edge| edge.to == to_pc)?;
                Some(TinyBvTraceEdgeStep {
                    edge,
                    from_source_line: self.source_line(edge.from),
                    to_source_line: self.source_line(edge.to),
                    from_labels: self
                        .labels_at_pc(edge.from)
                        .into_iter()
                        .map(ToOwned::to_owned)
                        .collect(),
                    to_labels: self
                        .labels_at_pc(edge.to)
                        .into_iter()
                        .map(ToOwned::to_owned)
                        .collect(),
                })
            })
            .collect()
    }

    /// Builds a complete concrete witness report.
    ///
    /// The report keeps the canonical concrete replay trace and derives the
    /// source-step, block-path, and taken-edge views from that single trace, so
    /// frontend diagnostics cannot accidentally mix rows from different
    /// witnesses.
    pub fn trace_report(&self, witness: &TinyBvWitness) -> TinyBvTraceReport {
        let trace = self.concrete_trace(witness);
        TinyBvTraceReport {
            witness: witness.clone(),
            source_steps: self.trace_source_steps(&trace),
            block_steps: self.trace_basic_blocks(&trace),
            edge_steps: self.trace_cfg_edges(&trace),
            trace,
        }
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

    /// Assembly labels attached to a program counter, in deterministic label
    /// order.
    ///
    /// Hand-built programs have no labels. Multiple labels may name the same
    /// instruction.
    pub fn labels_at_pc(&self, pc: usize) -> Vec<&str> {
        self.labels
            .iter()
            .filter_map(|(label, &label_pc)| (label_pc == pc).then_some(label.as_str()))
            .collect()
    }

    /// Program-counter-to-source-line map imported from assembly.
    ///
    /// Hand-built programs have no source lines. Imported source lines are
    /// one-based line numbers from the original assembly text.
    pub fn source_lines(&self) -> &BTreeMap<usize, usize> {
        &self.source_lines
    }

    /// One-based assembly source line for a program counter.
    pub fn source_line(&self, pc: usize) -> Option<usize> {
        self.source_lines.get(&pc).copied()
    }

    /// Derives source-aware replay rows from a concrete trace.
    ///
    /// The returned rows copy the step data and attach imported assembly
    /// metadata. This is intended for diagnostics and frontend reports: the
    /// original trace remains the canonical concrete replay artifact.
    pub fn trace_source_steps(&self, trace: &TinyBvConcreteTrace) -> Vec<TinyBvTraceSourceStep> {
        trace
            .steps
            .iter()
            .map(|step| TinyBvTraceSourceStep {
                pc: step.pc,
                source_line: self.source_line(step.pc),
                labels: self
                    .labels_at_pc(step.pc)
                    .into_iter()
                    .map(ToOwned::to_owned)
                    .collect(),
                instruction: step.instruction,
                regs_before: step.regs_before.clone(),
            })
            .collect()
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

    fn instruction_successors(&self, pc: usize, instruction: TinyBvInsn) -> Vec<TinyBvCfgEdge> {
        match instruction {
            TinyBvInsn::Const { .. }
            | TinyBvInsn::Add { .. }
            | TinyBvInsn::Sub { .. }
            | TinyBvInsn::Mul { .. }
            | TinyBvInsn::Xor { .. }
            | TinyBvInsn::Load { .. }
            | TinyBvInsn::Store { .. } => self.fallthrough_successor(pc),
            TinyBvInsn::BranchEq {
                then_pc, else_pc, ..
            }
            | TinyBvInsn::BranchRegEq {
                then_pc, else_pc, ..
            } => vec![
                TinyBvCfgEdge {
                    from: pc,
                    to: then_pc,
                    kind: TinyBvCfgEdgeKind::BranchTrue,
                },
                TinyBvCfgEdge {
                    from: pc,
                    to: else_pc,
                    kind: TinyBvCfgEdgeKind::BranchFalse,
                },
            ],
            TinyBvInsn::Win | TinyBvInsn::Lose => Vec::new(),
        }
    }

    fn fallthrough_successor(&self, pc: usize) -> Vec<TinyBvCfgEdge> {
        let next_pc = pc + 1;
        if next_pc < self.code.len() {
            vec![TinyBvCfgEdge {
                from: pc,
                to: next_pc,
                kind: TinyBvCfgEdgeKind::Fallthrough,
            }]
        } else {
            Vec::new()
        }
    }

    fn basic_block_leaders(&self) -> BTreeSet<usize> {
        let mut leaders = BTreeSet::from([0]);
        leaders.extend(self.labels.values().copied());
        for (pc, instruction) in self.code.iter().copied().enumerate() {
            match instruction {
                TinyBvInsn::BranchEq {
                    then_pc, else_pc, ..
                }
                | TinyBvInsn::BranchRegEq {
                    then_pc, else_pc, ..
                } => {
                    leaders.insert(then_pc);
                    leaders.insert(else_pc);
                    if pc + 1 < self.code.len() {
                        leaders.insert(pc + 1);
                    }
                }
                TinyBvInsn::Win | TinyBvInsn::Lose => {
                    if pc + 1 < self.code.len() {
                        leaders.insert(pc + 1);
                    }
                }
                TinyBvInsn::Const { .. }
                | TinyBvInsn::Add { .. }
                | TinyBvInsn::Sub { .. }
                | TinyBvInsn::Mul { .. }
                | TinyBvInsn::Xor { .. }
                | TinyBvInsn::Load { .. }
                | TinyBvInsn::Store { .. } => {}
            }
        }
        leaders
    }
}

fn tiny_bv_basic_block_dot_label(block: &TinyBvBasicBlock) -> String {
    let mut rows = Vec::new();
    if block.labels.is_empty() {
        rows.push(format!("bb_{}", block.start_pc));
    } else {
        rows.push(block.labels.join(", "));
    }
    rows.push(format!("pc {}..{}", block.start_pc, block.end_pc));
    let source_lines = block
        .source_lines
        .iter()
        .flatten()
        .map(usize::to_string)
        .collect::<Vec<_>>();
    if !source_lines.is_empty() {
        rows.push(format!("lines {}", source_lines.join(",")));
    }
    rows.join("\n")
}

fn tiny_bv_cfg_edge_kind_dot_label(kind: TinyBvCfgEdgeKind) -> &'static str {
    match kind {
        TinyBvCfgEdgeKind::Fallthrough => "fallthrough",
        TinyBvCfgEdgeKind::BranchTrue => "true",
        TinyBvCfgEdgeKind::BranchFalse => "false",
    }
}

fn tiny_bv_dot_escape_label(label: &str) -> String {
    let mut escaped = String::new();
    for ch in label.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            _ => escaped.push(ch),
        }
    }
    escaped
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

struct TinyBvAssembly {
    code: Vec<TinyBvInsn>,
    labels: BTreeMap<String, usize>,
    source_lines: BTreeMap<usize, usize>,
}

fn parse_tiny_bv_assembly(text: &str) -> Result<TinyBvAssembly, SolverError> {
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

    let source_lines = lines
        .iter()
        .enumerate()
        .map(|(pc, (line_no, _))| (pc, *line_no))
        .collect();
    let mut code = Vec::with_capacity(lines.len());
    for (line_no, line) in lines {
        code.push(parse_tiny_bv_instruction(line_no, line, &labels)?);
    }
    let label_pcs = labels
        .into_iter()
        .map(|(label, (pc, _))| (label, pc))
        .collect();
    Ok(TinyBvAssembly {
        code,
        labels: label_pcs,
        source_lines,
    })
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
