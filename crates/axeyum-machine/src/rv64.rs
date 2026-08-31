//! Source-pinned executable semantics for the book's RV64I teaching slice.
//!
//! The architectural source is the RISC-V Instruction Set Manual, Volume I,
//! Unprivileged Architecture, official release 20260120. The retrieved PDF has
//! SHA-256 `06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc`;
//! RV64I is ratified version 2.1. This module deliberately implements only the
//! twelve base forms printed by the book, with no compressed or other extension.

use crate::a0::{Memory, MemoryDomain, memory_load, memory_store};

/// Official upstream document release pinned by this slice.
pub const SOURCE_RELEASE: &str = "20260120";
/// SHA-256 of the official unprivileged-architecture PDF retrieved 2026-08-30.
pub const SOURCE_SHA256: &str = "06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc";
/// Ratified RV64I module version.
pub const RV64I_VERSION: &str = "2.1";
/// Exact selected base-instruction forms in canonical order.
pub const SELECTED_FORMS: [&str; 12] = [
    "ADDI", "ADD", "SUB", "OR", "XOR", "LD", "SD", "BEQ", "BNE", "BGE", "JAL", "JALR",
];

/// One decoded instruction from the source-pinned teaching slice.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    AddImmediate { rd: u8, rs1: u8, immediate: i16 },
    Add { rd: u8, rs1: u8, rs2: u8 },
    Sub { rd: u8, rs1: u8, rs2: u8 },
    Or { rd: u8, rs1: u8, rs2: u8 },
    Xor { rd: u8, rs1: u8, rs2: u8 },
    LoadDouble { rd: u8, rs1: u8, immediate: i16 },
    StoreDouble { rs1: u8, rs2: u8, immediate: i16 },
    BranchEqual { rs1: u8, rs2: u8, offset: i16 },
    BranchNotEqual { rs1: u8, rs2: u8, offset: i16 },
    BranchGreaterEqual { rs1: u8, rs2: u8, offset: i16 },
    JumpAndLink { rd: u8, offset: i32 },
    JumpAndLinkRegister { rd: u8, rs1: u8, immediate: i16 },
}

/// Decoder or encoder rejection for a word outside the selected slice.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodingError {
    IllegalInstruction(u32),
    InvalidRegister(u8),
    ImmediateOutOfRange,
    MisalignedImmediate,
}

/// Decodes one 32-bit word under RV64I-without-extensions selection rules.
///
/// # Errors
///
/// Returns [`EncodingError::IllegalInstruction`] when the word does not select
/// one of the twelve declared base forms.
pub fn decode(word: u32) -> Result<Instruction, EncodingError> {
    let opcode = word & 0x7f;
    let rd = field(word, 7, 5);
    let funct3 = field(word, 12, 3);
    let rs1 = field(word, 15, 5);
    let rs2 = field(word, 20, 5);
    let funct7 = field(word, 25, 7);
    match (opcode, funct3, funct7) {
        (0x33, 0b000, 0) => Ok(Instruction::Add { rd, rs1, rs2 }),
        (0x33, 0b000, 0x20) => Ok(Instruction::Sub { rd, rs1, rs2 }),
        (0x33, 0b110, 0) => Ok(Instruction::Or { rd, rs1, rs2 }),
        (0x33, 0b100, 0) => Ok(Instruction::Xor { rd, rs1, rs2 }),
        (0x13, 0b000, _) => Ok(Instruction::AddImmediate {
            rd,
            rs1,
            immediate: signed_12(word >> 20),
        }),
        (0x03, 0b011, _) => Ok(Instruction::LoadDouble {
            rd,
            rs1,
            immediate: signed_12(word >> 20),
        }),
        (0x23, 0b011, _) => Ok(Instruction::StoreDouble {
            rs1,
            rs2,
            immediate: decode_s_immediate(word),
        }),
        (0x63, 0b000, _) => Ok(Instruction::BranchEqual {
            rs1,
            rs2,
            offset: decode_b_immediate(word),
        }),
        (0x63, 0b001, _) => Ok(Instruction::BranchNotEqual {
            rs1,
            rs2,
            offset: decode_b_immediate(word),
        }),
        (0x63, 0b101, _) => Ok(Instruction::BranchGreaterEqual {
            rs1,
            rs2,
            offset: decode_b_immediate(word),
        }),
        (0x6f, _, _) => Ok(Instruction::JumpAndLink {
            rd,
            offset: decode_j_immediate(word),
        }),
        (0x67, 0b000, _) => Ok(Instruction::JumpAndLinkRegister {
            rd,
            rs1,
            immediate: signed_12(word >> 20),
        }),
        _ => Err(EncodingError::IllegalInstruction(word)),
    }
}

/// Encodes one selected instruction into its canonical 32-bit base form.
///
/// # Errors
///
/// Rejects invalid registers, out-of-range immediates, and branch/jump
/// displacements not divisible by two.
pub fn encode(instruction: Instruction) -> Result<u32, EncodingError> {
    use Instruction::{
        Add, AddImmediate, BranchEqual, BranchGreaterEqual, BranchNotEqual, JumpAndLink,
        JumpAndLinkRegister, LoadDouble, Or, StoreDouble, Sub, Xor,
    };
    match instruction {
        Add { rd, rs1, rs2 } => encode_r(rd, rs1, rs2, 0b000, 0),
        Sub { rd, rs1, rs2 } => encode_r(rd, rs1, rs2, 0b000, 0x20),
        Or { rd, rs1, rs2 } => encode_r(rd, rs1, rs2, 0b110, 0),
        Xor { rd, rs1, rs2 } => encode_r(rd, rs1, rs2, 0b100, 0),
        AddImmediate { rd, rs1, immediate } => encode_i(rd, rs1, immediate, 0b000, 0x13),
        LoadDouble { rd, rs1, immediate } => encode_i(rd, rs1, immediate, 0b011, 0x03),
        JumpAndLinkRegister { rd, rs1, immediate } => encode_i(rd, rs1, immediate, 0b000, 0x67),
        StoreDouble {
            rs1,
            rs2,
            immediate,
        } => encode_s(rs1, rs2, immediate),
        BranchEqual { rs1, rs2, offset } => encode_b(rs1, rs2, offset, 0b000),
        BranchNotEqual { rs1, rs2, offset } => encode_b(rs1, rs2, offset, 0b001),
        BranchGreaterEqual { rs1, rs2, offset } => encode_b(rs1, rs2, offset, 0b101),
        JumpAndLink { rd, offset } => encode_j(rd, offset),
    }
}

/// Declared exceptional outcome in the book's RV64I execution profile.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trap {
    InstructionAddressMisaligned { pc: u64 },
    IncompleteInstructionFetch { pc: u64 },
    IllegalInstruction { pc: u64, word: u32 },
    DataAddressMisaligned { address: u64 },
    DataAccessFault { address: u64, bytes: usize },
}

/// Whether this teaching machine can take another instruction step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// A selected instruction may execute.
    Running,
    /// The profile stopped at a declared exception.
    Trapped(Trap),
}

/// Complete state exposed by the RV64I teaching slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// Integer registers `x0` through `x31`; `x0` is canonicalized to zero.
    pub registers: [u64; 32],
    /// Finite byte memory.
    pub memory: Memory,
    /// Address of the next instruction.
    pub pc: u64,
    /// Running or trapped outcome.
    pub outcome: Outcome,
}

impl State {
    /// Constructs a zero-register running state.
    #[must_use]
    pub fn new(memory: Memory, pc: u64) -> Self {
        Self {
            registers: [0; 32],
            memory,
            pc,
            outcome: Outcome::Running,
        }
    }

    /// Reads an architectural integer register, enforcing the `x0` rule.
    #[must_use]
    pub fn register(&self, index: u8) -> u64 {
        if index == 0 {
            0
        } else {
            self.registers[usize::from(index)]
        }
    }

    fn write_register(&mut self, index: u8, value: u64) {
        if index != 0 {
            self.registers[usize::from(index)] = value;
        }
        self.registers[0] = 0;
    }
}

/// Canonical projection used by later refinement and cross-ISA relations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateProjection {
    /// Selected architectural registers in increasing index order.
    pub registers: Vec<(u8, u64)>,
    /// Complete finite memory in increasing address order.
    pub memory: Vec<(u64, u8)>,
    /// Program counter.
    pub pc: u64,
    /// Running or trapped outcome.
    pub outcome: Outcome,
}

/// Projection construction error.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectionError {
    InvalidRegister(u8),
    DuplicateRegister(u8),
}

/// Projects selected registers and the complete memory into one canonical
/// refinement-facing value without changing the source state.
///
/// Register indices are sorted. Duplicates and indices outside `x0..x31` are
/// rejected so one observation has one serialized spelling.
///
/// # Errors
///
/// Returns [`ProjectionError`] for an invalid or duplicate register index.
pub fn project_state(
    state: &State,
    mut registers: Vec<u8>,
) -> Result<StateProjection, ProjectionError> {
    registers.sort_unstable();
    if let Some(index) = registers.iter().copied().find(|index| *index >= 32) {
        return Err(ProjectionError::InvalidRegister(index));
    }
    if let Some(index) = registers
        .windows(2)
        .find_map(|pair| (pair[0] == pair[1]).then_some(pair[0]))
    {
        return Err(ProjectionError::DuplicateRegister(index));
    }
    Ok(StateProjection {
        registers: registers
            .into_iter()
            .map(|index| (index, state.register(index)))
            .collect(),
        memory: state.memory.entries().collect(),
        pc: state.pc,
        outcome: state.outcome.clone(),
    })
}

/// Immutable instruction image used by the selected executor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    base: u64,
    code: Vec<u8>,
}

impl Program {
    /// Constructs a program image at `base`.
    #[must_use]
    pub fn new(base: u64, code: Vec<u8>) -> Self {
        Self { base, code }
    }

    fn fetch(&self, pc: u64) -> Result<u32, Trap> {
        if !pc.is_multiple_of(4) {
            return Err(Trap::InstructionAddressMisaligned { pc });
        }
        let offset = pc.wrapping_sub(self.base);
        let start = usize::try_from(offset).map_err(|_| Trap::IncompleteInstructionFetch { pc })?;
        let end = start
            .checked_add(4)
            .filter(|end| *end <= self.code.len())
            .ok_or(Trap::IncompleteInstructionFetch { pc })?;
        let bytes: [u8; 4] = self.code[start..end]
            .try_into()
            .map_err(|_| Trap::IncompleteInstructionFetch { pc })?;
        Ok(u32::from_le_bytes(bytes))
    }
}

/// Executes one complete selected RV64I transition.
#[must_use]
pub fn step(program: &Program, state: &State) -> State {
    if state.outcome != Outcome::Running {
        return state.clone();
    }
    let word = match program.fetch(state.pc) {
        Ok(word) => word,
        Err(trap) => return trapped(state, trap),
    };
    let Ok(instruction) = decode(word) else {
        return trapped(state, Trap::IllegalInstruction { pc: state.pc, word });
    };
    execute(instruction, state)
}

#[allow(clippy::too_many_lines)]
fn execute(instruction: Instruction, state: &State) -> State {
    use Instruction::{
        Add, AddImmediate, BranchEqual, BranchGreaterEqual, BranchNotEqual, JumpAndLink,
        JumpAndLinkRegister, LoadDouble, Or, StoreDouble, Sub, Xor,
    };
    let sequential = state.pc.wrapping_add(4);
    let mut next = state.clone();
    next.pc = sequential;
    match instruction {
        AddImmediate { rd, rs1, immediate } => next.write_register(
            rd,
            state
                .register(rs1)
                .wrapping_add_signed(i64::from(immediate)),
        ),
        Add { rd, rs1, rs2 } => {
            next.write_register(rd, state.register(rs1).wrapping_add(state.register(rs2)));
        }
        Sub { rd, rs1, rs2 } => {
            next.write_register(rd, state.register(rs1).wrapping_sub(state.register(rs2)));
        }
        Or { rd, rs1, rs2 } => {
            next.write_register(rd, state.register(rs1) | state.register(rs2));
        }
        Xor { rd, rs1, rs2 } => {
            next.write_register(rd, state.register(rs1) ^ state.register(rs2));
        }
        LoadDouble { rd, rs1, immediate } => {
            let address = state
                .register(rs1)
                .wrapping_add_signed(i64::from(immediate));
            if !address.is_multiple_of(8) {
                return trapped(state, Trap::DataAddressMisaligned { address });
            }
            let access = memory_load(&mut RvMemoryDomain, &state.memory, address);
            if !access.valid {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            }
            next.write_register(rd, access.value);
        }
        StoreDouble {
            rs1,
            rs2,
            immediate,
        } => {
            let address = state
                .register(rs1)
                .wrapping_add_signed(i64::from(immediate));
            if !address.is_multiple_of(8) {
                return trapped(state, Trap::DataAddressMisaligned { address });
            }
            let access = memory_store(
                &mut RvMemoryDomain,
                &state.memory,
                address,
                state.register(rs2),
            );
            if !access.valid {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            }
            next.memory = access.memory;
        }
        BranchEqual { rs1, rs2, offset } => {
            if let Err(trap) = branch(
                state,
                &mut next,
                state.register(rs1) == state.register(rs2),
                offset,
            ) {
                return trapped(state, trap);
            }
        }
        BranchNotEqual { rs1, rs2, offset } => {
            if let Err(trap) = branch(
                state,
                &mut next,
                state.register(rs1) != state.register(rs2),
                offset,
            ) {
                return trapped(state, trap);
            }
        }
        BranchGreaterEqual { rs1, rs2, offset } => {
            if let Err(trap) = branch(
                state,
                &mut next,
                state.register(rs1).cast_signed() >= state.register(rs2).cast_signed(),
                offset,
            ) {
                return trapped(state, trap);
            }
        }
        JumpAndLink { rd, offset } => {
            let target = state.pc.wrapping_add_signed(i64::from(offset));
            if let Err(trap) = require_instruction_alignment(target) {
                return trapped(state, trap);
            }
            next.write_register(rd, sequential);
            next.pc = target;
        }
        JumpAndLinkRegister { rd, rs1, immediate } => {
            let target = state
                .register(rs1)
                .wrapping_add_signed(i64::from(immediate))
                & !1;
            if let Err(trap) = require_instruction_alignment(target) {
                return trapped(state, trap);
            }
            next.write_register(rd, sequential);
            next.pc = target;
        }
    }
    next.registers[0] = 0;
    next
}

fn branch(state: &State, next: &mut State, taken: bool, offset: i16) -> Result<(), Trap> {
    if taken {
        let target = state.pc.wrapping_add_signed(i64::from(offset));
        require_instruction_alignment(target)?;
        next.pc = target;
    }
    Ok(())
}

fn require_instruction_alignment(target: u64) -> Result<(), Trap> {
    if target.is_multiple_of(4) {
        Ok(())
    } else {
        Err(Trap::InstructionAddressMisaligned { pc: target })
    }
}

fn trapped(state: &State, trap: Trap) -> State {
    let mut trapped = state.clone();
    trapped.registers[0] = 0;
    trapped.outcome = Outcome::Trapped(trap);
    trapped
}

struct RvMemoryDomain;

impl MemoryDomain for RvMemoryDomain {
    type Memory = Memory;
    type Address = u64;
    type Byte = u8;
    type Word = u64;
    type Bit = bool;

    fn word_bytes(&self) -> usize {
        8
    }
    fn true_bit(&mut self) -> bool {
        true
    }
    fn and(&mut self, lhs: bool, rhs: bool) -> bool {
        lhs && rhs
    }
    fn address_offset(&mut self, base: u64, offset: usize) -> u64 {
        base.wrapping_add(u64::try_from(offset).expect("word byte offset fits u64"))
    }
    fn present(&mut self, memory: &Memory, address: u64) -> bool {
        memory.byte_at(address).is_some()
    }
    fn read_byte(&mut self, memory: &Memory, address: u64) -> u8 {
        memory.byte_at(address).unwrap_or(0)
    }
    fn join_little_endian(&mut self, bytes: &[u8]) -> u64 {
        u64::from_le_bytes(bytes.try_into().expect("RV64 doubleword has eight bytes"))
    }
    fn split_little_endian(&mut self, word: u64) -> Vec<u8> {
        word.to_le_bytes().to_vec()
    }
    fn write_byte(&mut self, memory: Memory, address: u64, byte: u8) -> Memory {
        let entries = memory
            .entries()
            .map(|(candidate, old)| (candidate, if candidate == address { byte } else { old }))
            .collect();
        Memory::from_entries(entries).expect("updating preserves unique addresses")
    }
    fn choose_memory(&mut self, valid: bool, success: Memory, failure: Memory) -> Memory {
        if valid { success } else { failure }
    }
}

fn field(word: u32, low: u32, width: u32) -> u8 {
    u8::try_from((word >> low) & ((1_u32 << width) - 1)).expect("selected field fits u8")
}

fn sign_extend(value: u64, bits: u32) -> i64 {
    let shift = 64 - bits;
    (value << shift).cast_signed() >> shift
}

fn signed_12(value: u32) -> i16 {
    ((u16::try_from(value & 0x0fff).expect("twelve bits fit u16")) << 4).cast_signed() >> 4
}

fn decode_s_immediate(word: u32) -> i16 {
    let bits = u64::from(((word >> 25) << 5) | ((word >> 7) & 0x1f));
    i16::try_from(sign_extend(bits, 12)).expect("12-bit signed immediate fits i16")
}

fn decode_b_immediate(word: u32) -> i16 {
    let bits = u64::from(
        ((word >> 31) & 1) << 12
            | ((word >> 7) & 1) << 11
            | ((word >> 25) & 0x3f) << 5
            | ((word >> 8) & 0x0f) << 1,
    );
    i16::try_from(sign_extend(bits, 13)).expect("13-bit signed immediate fits i16")
}

fn decode_j_immediate(word: u32) -> i32 {
    let bits = u64::from(
        ((word >> 31) & 1) << 20
            | ((word >> 12) & 0xff) << 12
            | ((word >> 20) & 1) << 11
            | ((word >> 21) & 0x3ff) << 1,
    );
    i32::try_from(sign_extend(bits, 21)).expect("21-bit signed immediate fits i32")
}

fn register_field(index: u8) -> Result<u32, EncodingError> {
    (index < 32)
        .then_some(u32::from(index))
        .ok_or(EncodingError::InvalidRegister(index))
}

fn encode_r(rd: u8, rs1: u8, rs2: u8, funct3: u32, funct7: u32) -> Result<u32, EncodingError> {
    Ok(funct7 << 25
        | register_field(rs2)? << 20
        | register_field(rs1)? << 15
        | funct3 << 12
        | register_field(rd)? << 7
        | 0x33)
}

fn encode_i(
    rd: u8,
    rs1: u8,
    immediate: i16,
    funct3: u32,
    opcode: u32,
) -> Result<u32, EncodingError> {
    if !(-2048..=2047).contains(&immediate) {
        return Err(EncodingError::ImmediateOutOfRange);
    }
    let immediate = u32::from(u16::from_ne_bytes(immediate.to_ne_bytes())) & 0x0fff;
    Ok(immediate << 20
        | register_field(rs1)? << 15
        | funct3 << 12
        | register_field(rd)? << 7
        | opcode)
}

fn encode_s(rs1: u8, rs2: u8, immediate: i16) -> Result<u32, EncodingError> {
    if !(-2048..=2047).contains(&immediate) {
        return Err(EncodingError::ImmediateOutOfRange);
    }
    let immediate = u32::from(u16::from_ne_bytes(immediate.to_ne_bytes())) & 0x0fff;
    Ok((immediate >> 5) << 25
        | register_field(rs2)? << 20
        | register_field(rs1)? << 15
        | 0b011 << 12
        | (immediate & 0x1f) << 7
        | 0x23)
}

fn encode_b(rs1: u8, rs2: u8, offset: i16, funct3: u32) -> Result<u32, EncodingError> {
    if !(-4096..=4094).contains(&offset) {
        return Err(EncodingError::ImmediateOutOfRange);
    }
    if offset % 2 != 0 {
        return Err(EncodingError::MisalignedImmediate);
    }
    let immediate = u32::from(u16::from_ne_bytes(offset.to_ne_bytes())) & 0x1fff;
    Ok(((immediate >> 12) & 1) << 31
        | ((immediate >> 5) & 0x3f) << 25
        | register_field(rs2)? << 20
        | register_field(rs1)? << 15
        | funct3 << 12
        | ((immediate >> 1) & 0x0f) << 8
        | ((immediate >> 11) & 1) << 7
        | 0x63)
}

fn encode_j(rd: u8, offset: i32) -> Result<u32, EncodingError> {
    if !(-1_048_576..=1_048_574).contains(&offset) {
        return Err(EncodingError::ImmediateOutOfRange);
    }
    if offset % 2 != 0 {
        return Err(EncodingError::MisalignedImmediate);
    }
    let immediate = u32::from_ne_bytes(offset.to_ne_bytes()) & 0x1f_ffff;
    Ok(((immediate >> 20) & 1) << 31
        | ((immediate >> 1) & 0x03ff) << 21
        | ((immediate >> 11) & 1) << 20
        | ((immediate >> 12) & 0xff) << 12
        | register_field(rd)? << 7
        | 0x6f)
}
