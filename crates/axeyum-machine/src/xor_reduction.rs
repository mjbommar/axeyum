//! Typed three-machine relation for the Chapter 15 scalar XOR reduction.
//!
//! The exact printed A0, RV64I, and x86-64 byte images execute through their
//! separate concrete semantics. Relations compare only declared logical cut
//! points and preserve architectural differences such as x86-64's fused
//! memory-source XOR and the three different terminal conventions.

use crate::{a0, rv64, x64};

/// Exact 44-byte A0 listing printed in Chapter 15.
pub const A0_XOR_REDUCTION_BYTES: [u8; 44] = [
    0x01, 0x00, 0x00, 0x00, 0x01, 0x04, 0x00, 0x08, 0x01, 0x05, 0x00, 0x01, 0x20, 0x10, 0x00, 0x00,
    0x30, 0x00, 0x00, 0x05, 0x02, 0x0b, 0x00, 0x00, 0x14, 0x00, 0x03, 0x00, 0x10, 0x09, 0x04, 0x00,
    0x11, 0x12, 0x05, 0x00, 0x30, 0x00, 0x08, 0xfb, 0xff, 0x00, 0x00, 0x00,
];

/// Exact 36-byte RV64I listing printed in Chapter 15.
pub const RV64_XOR_REDUCTION_BYTES: [u8; 36] = [
    0x93, 0x02, 0x05, 0x00, 0x13, 0x05, 0x00, 0x00, 0x63, 0x8c, 0x05, 0x00, 0x03, 0xb3, 0x02, 0x00,
    0x33, 0x45, 0x65, 0x00, 0x93, 0x82, 0x82, 0x00, 0x93, 0x85, 0xf5, 0xff, 0xe3, 0x98, 0x05, 0xfe,
    0x67, 0x80, 0x00, 0x00,
];

/// Exact 21-byte x86-64 listing printed in Chapter 15.
pub const X64_XOR_REDUCTION_BYTES: [u8; 21] = [
    0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0d, 0x48, 0x33, 0x07, 0x48, 0x83, 0xc7, 0x08, 0x48, 0x83,
    0xee, 0x01, 0x75, 0xf3, 0xc3,
];

const DATA_BASE: u64 = 0x100;
const STACK_ADDRESS: u64 = 0x400;
const CONTINUATION: u64 = 0x800;
const MAX_WORDS: usize = ((STACK_ADDRESS - DATA_BASE) / 8) as usize;

/// One logical synchronization point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum XorReductionPoint {
    /// Harness entry before setup.
    Entry,
    /// Before loading one indexed word.
    LoopHead {
        /// Zero-based word index about to be loaded.
        iteration: usize,
    },
    /// After incorporating one indexed word.
    AfterCombine {
        /// Zero-based word index just incorporated.
        iteration: usize,
    },
    /// After the architecture-specific halt or return.
    Terminal,
}

/// One independently reported relation clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum XorReductionClause {
    /// Machine program counters name the same logical point.
    ControlPoint,
    /// Each machine has the expected running, halted, or returned outcome.
    Outcomes,
    /// Harness registers encode the shared pointer and count.
    InputMapping,
    /// All accumulator registers equal the same prefix fold.
    Accumulator,
    /// All pointer registers encode the same logical address.
    Pointer,
    /// All count registers encode the same remaining length.
    RemainingCount,
    /// A0's helper registers retain eight and one.
    A0Helpers,
    /// No machine changes the finite entry memory.
    MemoryFrame,
    /// Halt, continuation, and stack effects satisfy their harness contracts.
    TerminalConvention,
}

/// Result of one clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct XorReductionClauseResult {
    /// Evaluated clause.
    pub clause: XorReductionClause,
    /// Whether the clause holds.
    pub holds: bool,
}

/// Complete relation check at one cut point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorReductionRelation {
    /// Logical point being compared.
    pub point: XorReductionPoint,
    /// Stable ordered clause results.
    pub clauses: Vec<XorReductionClauseResult>,
}

impl XorReductionRelation {
    /// Whether every clause holds.
    #[must_use]
    pub fn holds(&self) -> bool {
        self.clauses.iter().all(|result| result.holds)
    }

    /// First failed clause.
    #[must_use]
    pub fn first_failure(&self) -> Option<XorReductionClause> {
        self.clauses
            .iter()
            .find_map(|result| (!result.holds).then_some(result.clause))
    }
}

/// Three concrete states at one logical cut point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorReductionStates {
    /// Complete A0 state.
    pub a0: a0::State,
    /// Complete RV64I state.
    pub rv64: rv64::State,
    /// Complete x86-64 state.
    pub x64: x64::State,
}

/// Retained states and relation at one cut point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorReductionSnapshot {
    /// Three concrete states.
    pub states: XorReductionStates,
    /// Relation checked over those states.
    pub relation: XorReductionRelation,
}

/// Exact code images consumed by the three executors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorReductionPrograms {
    /// Exact A0 image.
    pub a0: a0::Program,
    /// Exact RV64I image.
    pub rv64: rv64::Program,
    /// Exact x86-64 image.
    pub x64: x64::Program,
}

impl XorReductionPrograms {
    /// Constructs the exact printed programs.
    ///
    /// # Errors
    ///
    /// Returns an error if a fixed semantic program cannot be constructed.
    pub fn book() -> Result<Self, XorReductionError> {
        Self::with_rv64_pointer_step(8)
    }

    /// Changes only the RV64I pointer step for evidence controls.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid A0 program or RV64I immediate.
    pub fn with_rv64_pointer_step(step: i16) -> Result<Self, XorReductionError> {
        let mut rv64_bytes = RV64_XOR_REDUCTION_BYTES.to_vec();
        let word = rv64::encode(rv64::Instruction::AddImmediate {
            rd: 5,
            rs1: 5,
            immediate: step,
        })
        .map_err(XorReductionError::Rv64Encoding)?;
        rv64_bytes[20..24].copy_from_slice(&word.to_le_bytes());
        Ok(Self {
            a0: a0::Program::new(64, a0::Word::new(64, 0)?, A0_XOR_REDUCTION_BYTES.to_vec())?,
            rv64: rv64::Program::new(0, rv64_bytes),
            x64: x64::Program::new(0, X64_XOR_REDUCTION_BYTES.to_vec()),
        })
    }
}

/// Complete bounded replay through all three exact programs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorReductionSimulation {
    /// Input words in address order.
    pub words: Vec<u64>,
    /// Direct XOR fold of the input.
    pub expected: u64,
    /// Entry, loop-head, combine, and terminal snapshots.
    pub snapshots: Vec<XorReductionSnapshot>,
    /// Dynamic A0 instruction count.
    pub a0_steps: u64,
    /// Dynamic RV64I instruction count.
    pub rv64_steps: u64,
    /// Dynamic x86-64 instruction count.
    pub x64_steps: u64,
}

/// Failure to construct, execute, or relate the bounded routine.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XorReductionError {
    A0(a0::A0Error),
    Rv64Encoding(rv64::EncodingError),
    InputTooLong {
        words: usize,
        maximum: usize,
    },
    FailedClause {
        point: XorReductionPoint,
        clause: XorReductionClause,
    },
}

impl From<a0::A0Error> for XorReductionError {
    fn from(error: a0::A0Error) -> Self {
        Self::A0(error)
    }
}

/// Executes and relates the exact printed programs on one finite word list.
///
/// # Errors
///
/// Returns the first failed clause in stable point and clause order.
pub fn simulate_xor_reduction(words: &[u64]) -> Result<XorReductionSimulation, XorReductionError> {
    simulate_xor_reduction_with_programs(words, &XorReductionPrograms::book()?)
}

/// Executes and relates explicitly supplied programs.
///
/// # Errors
///
/// Returns the first failed relation clause.
pub fn simulate_xor_reduction_with_programs(
    words: &[u64],
    programs: &XorReductionPrograms,
) -> Result<XorReductionSimulation, XorReductionError> {
    if words.len() > MAX_WORDS {
        return Err(XorReductionError::InputTooLong {
            words: words.len(),
            maximum: MAX_WORDS,
        });
    }
    let memory = input_memory(words)?;
    let zero = a0::Word::new(64, 0)?;
    let mut a0_state = a0::State::new(64, memory.clone(), zero)?;
    a0_state.registers[1] = a0::Word::new(64, DATA_BASE)?;
    a0_state.registers[2] = a0::Word::new(64, words.len() as u64)?;
    let mut rv64_state = rv64::State::new(memory.clone(), 0);
    rv64_state.registers[10] = DATA_BASE;
    rv64_state.registers[11] = words.len() as u64;
    rv64_state.registers[1] = CONTINUATION;
    let mut x64_state = x64::State::new(memory, 0);
    x64_state.registers[7] = DATA_BASE;
    x64_state.registers[6] = words.len() as u64;
    x64_state.registers[4] = STACK_ADDRESS;
    let entry = states(&a0_state, &rv64_state, &x64_state);
    let mut snapshots = Vec::new();
    push_checked(
        &mut snapshots,
        XorReductionPoint::Entry,
        words,
        &entry,
        entry.clone(),
    )?;

    step_a0(&mut a0_state, &programs.a0, 5);
    step_rv64(&mut rv64_state, &programs.rv64, 3);
    step_x64(&mut x64_state, &programs.x64, 3);

    for iteration in 0..words.len() {
        push_checked(
            &mut snapshots,
            XorReductionPoint::LoopHead { iteration },
            words,
            &entry,
            states(&a0_state, &rv64_state, &x64_state),
        )?;
        step_a0(&mut a0_state, &programs.a0, 2);
        step_rv64(&mut rv64_state, &programs.rv64, 2);
        step_x64(&mut x64_state, &programs.x64, 1);
        push_checked(
            &mut snapshots,
            XorReductionPoint::AfterCombine { iteration },
            words,
            &entry,
            states(&a0_state, &rv64_state, &x64_state),
        )?;
        step_a0(&mut a0_state, &programs.a0, 3);
        step_rv64(&mut rv64_state, &programs.rv64, 3);
        step_x64(&mut x64_state, &programs.x64, 3);
    }

    step_a0(&mut a0_state, &programs.a0, 1);
    step_rv64(&mut rv64_state, &programs.rv64, 1);
    step_x64(&mut x64_state, &programs.x64, 1);
    push_checked(
        &mut snapshots,
        XorReductionPoint::Terminal,
        words,
        &entry,
        states(&a0_state, &rv64_state, &x64_state),
    )?;

    let count = words.len() as u64;
    Ok(XorReductionSimulation {
        words: words.to_vec(),
        expected: fold(words),
        snapshots,
        a0_steps: 6 + 5 * count,
        rv64_steps: 4 + 5 * count,
        x64_steps: 4 + 4 * count,
    })
}

fn states(a: &a0::State, r: &rv64::State, x: &x64::State) -> XorReductionStates {
    XorReductionStates {
        a0: a.clone(),
        rv64: r.clone(),
        x64: x.clone(),
    }
}

fn input_memory(words: &[u64]) -> Result<a0::Memory, a0::A0Error> {
    let mut entries = Vec::with_capacity(words.len() * 8 + 8);
    for (index, word) in words.iter().enumerate() {
        let address = DATA_BASE + 8 * index as u64;
        entries.extend(
            word.to_le_bytes()
                .into_iter()
                .enumerate()
                .map(|(offset, byte)| (address + offset as u64, byte)),
        );
    }
    entries.extend(
        CONTINUATION
            .to_le_bytes()
            .into_iter()
            .enumerate()
            .map(|(offset, byte)| (STACK_ADDRESS + offset as u64, byte)),
    );
    a0::Memory::from_entries(entries)
}

fn step_a0(state: &mut a0::State, program: &a0::Program, count: usize) {
    for _ in 0..count {
        *state = a0::step(program, state);
    }
}

fn step_rv64(state: &mut rv64::State, program: &rv64::Program, count: usize) {
    for _ in 0..count {
        *state = rv64::step(program, state);
    }
}

fn step_x64(state: &mut x64::State, program: &x64::Program, count: usize) {
    for _ in 0..count {
        *state = x64::step(program, state);
    }
}

fn push_checked(
    snapshots: &mut Vec<XorReductionSnapshot>,
    point: XorReductionPoint,
    words: &[u64],
    entry: &XorReductionStates,
    states: XorReductionStates,
) -> Result<(), XorReductionError> {
    let relation = check_xor_reduction_relation(point, words, entry, &states);
    if let Some(clause) = relation.first_failure() {
        return Err(XorReductionError::FailedClause { point, clause });
    }
    snapshots.push(XorReductionSnapshot { states, relation });
    Ok(())
}

/// Checks one typed cut-point relation.
#[must_use]
pub fn check_xor_reduction_relation(
    point: XorReductionPoint,
    words: &[u64],
    entry: &XorReductionStates,
    states: &XorReductionStates,
) -> XorReductionRelation {
    let n = words.len();
    let completed = match point {
        XorReductionPoint::Entry => 0,
        XorReductionPoint::LoopHead { iteration } => iteration,
        XorReductionPoint::AfterCombine { iteration } => iteration + 1,
        XorReductionPoint::Terminal => n,
    };
    let position = match point {
        XorReductionPoint::AfterCombine { iteration } => iteration,
        _ => completed,
    };
    let expected_accumulator = fold(&words[..completed.min(n)]);
    let expected_pointer = DATA_BASE + 8 * position as u64;
    let expected_count = (n - position.min(n)) as u64;
    let (a0_pc, rv64_pc, x64_pc) = point_pcs(point);
    let terminal = point == XorReductionPoint::Terminal;
    let outcomes_hold = if terminal {
        states.a0.outcome == a0::Outcome::Halted
            && states.rv64.outcome == rv64::Outcome::Running
            && states.x64.outcome == x64::Outcome::Running
    } else {
        states.a0.outcome == a0::Outcome::Running
            && states.rv64.outcome == rv64::Outcome::Running
            && states.x64.outcome == x64::Outcome::Running
    };
    let input_mapping = point != XorReductionPoint::Entry
        || (states.a0.registers[1].unsigned() == DATA_BASE
            && states.a0.registers[2].unsigned() == n as u64
            && states.rv64.register(10) == DATA_BASE
            && states.rv64.register(11) == n as u64
            && states.x64.register(7) == DATA_BASE
            && states.x64.register(6) == n as u64);
    let after_entry = point != XorReductionPoint::Entry;
    let accumulator = !after_entry
        || (states.a0.registers[0].unsigned() == expected_accumulator
            && states.rv64.register(10) == expected_accumulator
            && states.x64.register(0) == expected_accumulator);
    let pointer = !after_entry
        || (states.a0.registers[1].unsigned() == expected_pointer
            && states.rv64.register(5) == expected_pointer
            && states.x64.register(7) == expected_pointer);
    let remaining = !after_entry
        || (states.a0.registers[2].unsigned() == expected_count
            && states.rv64.register(11) == expected_count
            && states.x64.register(6) == expected_count);
    let helpers = !after_entry
        || (states.a0.registers[4].unsigned() == 8 && states.a0.registers[5].unsigned() == 1);
    let terminal_convention = !terminal
        || (states.a0.pc.unsigned() == 40
            && states.rv64.pc == CONTINUATION
            && states.x64.rip == CONTINUATION
            && states.x64.register(4) == STACK_ADDRESS + 8);
    let clauses = vec![
        result(
            XorReductionClause::ControlPoint,
            states.a0.pc.unsigned() == a0_pc
                && states.rv64.pc == rv64_pc
                && states.x64.rip == x64_pc,
        ),
        result(XorReductionClause::Outcomes, outcomes_hold),
        result(XorReductionClause::InputMapping, input_mapping),
        result(XorReductionClause::Accumulator, accumulator),
        result(XorReductionClause::Pointer, pointer),
        result(XorReductionClause::RemainingCount, remaining),
        result(XorReductionClause::A0Helpers, helpers),
        result(
            XorReductionClause::MemoryFrame,
            states.a0.memory == entry.a0.memory
                && states.rv64.memory == entry.rv64.memory
                && states.x64.memory == entry.x64.memory,
        ),
        result(XorReductionClause::TerminalConvention, terminal_convention),
    ];
    XorReductionRelation { point, clauses }
}

const fn result(clause: XorReductionClause, holds: bool) -> XorReductionClauseResult {
    XorReductionClauseResult { clause, holds }
}

const fn point_pcs(point: XorReductionPoint) -> (u64, u64, u64) {
    match point {
        XorReductionPoint::Entry => (0, 0, 0),
        XorReductionPoint::LoopHead { .. } => (20, 12, 7),
        XorReductionPoint::AfterCombine { .. } => (28, 20, 10),
        XorReductionPoint::Terminal => (40, CONTINUATION, CONTINUATION),
    }
}

fn fold(words: &[u64]) -> u64 {
    words.iter().copied().fold(0, core::ops::BitXor::bitxor)
}
