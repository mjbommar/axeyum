//! Source-pinned executable semantics for the book's x86-64 teaching slice.
//!
//! The architectural source is Intel's combined Instruction Set Reference,
//! order number 325383-092US, June 2026. The retrieved PDF has SHA-256
//! `db01e5918a710c16487e27a9e71a19af201f39b3311c55550559baaf0805160b`.
//! This module accepts only the legacy and REX.W forms printed by the book.

use crate::a0::Memory;

/// Intel instruction-reference revision pinned by this slice.
pub const SOURCE_REVISION: &str = "325383-092US";
/// SHA-256 of Intel's combined Volume 2 PDF retrieved 2026-08-30.
pub const SOURCE_SHA256: &str = "db01e5918a710c16487e27a9e71a19af201f39b3311c55550559baaf0805160b";
/// Exact selected form families.
pub const SELECTED_FORMS: [&str; 17] = [
    "XOR r32,r32",
    "MOV r32,imm32",
    "TEST r64,r64",
    "JE rel8",
    "JNE rel8",
    "JNS rel8",
    "XOR r64,m64",
    "ADD r64,imm8",
    "SUB r64,imm8",
    "MOV r64,r64",
    "NEG r64",
    "LEA r64,[r64+disp8]",
    "PUSH r64",
    "POP r64",
    "CALL rel32",
    "ADD r64,r64",
    "RET",
];

/// Low-eight general-purpose register index in Intel encoding order.
pub type Register = u8;

/// Selected condition for a short conditional jump.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Condition {
    /// Zero flag is set.
    Equal,
    /// Zero flag is clear.
    NotEqual,
    /// Sign flag is clear.
    NotSign,
}

/// One decoded instruction in the selected x86-64 slice.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    Xor32 {
        destination: Register,
        source: Register,
    },
    MoveImmediate32 {
        destination: Register,
        immediate: u32,
    },
    Test64 {
        lhs: Register,
        rhs: Register,
    },
    JumpShort {
        condition: Condition,
        displacement: i8,
    },
    Xor64Memory {
        destination: Register,
        base: Register,
    },
    AddImmediate64 {
        destination: Register,
        immediate: i8,
    },
    SubImmediate64 {
        destination: Register,
        immediate: i8,
    },
    Move64 {
        destination: Register,
        source: Register,
    },
    Negate64 {
        destination: Register,
    },
    LoadEffectiveAddress64 {
        destination: Register,
        base: Register,
        displacement: i8,
    },
    Push64 {
        source: Register,
    },
    Pop64 {
        destination: Register,
    },
    CallRelative {
        displacement: i32,
    },
    Add64 {
        destination: Register,
        source: Register,
    },
    Return,
}

/// Decoder or canonical-encoder rejection.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodingError {
    IncompleteInstruction,
    IllegalInstruction,
    InvalidRegister(Register),
}

/// A flag can be architecturally known or explicitly undefined.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagValue {
    /// The flag is clear.
    Clear,
    /// The flag is set.
    Set,
    /// The selected instruction leaves the flag architecturally undefined.
    Undefined,
}

impl FlagValue {
    fn from_bool(value: bool) -> Self {
        if value { Self::Set } else { Self::Clear }
    }
}

/// Selected arithmetic status visible to the teaching slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct Flags {
    pub carry: FlagValue,
    pub parity: FlagValue,
    pub auxiliary: FlagValue,
    pub zero: FlagValue,
    pub sign: FlagValue,
    pub overflow: FlagValue,
}

impl Default for Flags {
    fn default() -> Self {
        Self {
            carry: FlagValue::Clear,
            parity: FlagValue::Clear,
            auxiliary: FlagValue::Clear,
            zero: FlagValue::Clear,
            sign: FlagValue::Clear,
            overflow: FlagValue::Clear,
        }
    }
}

/// Declared exceptional outcome.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trap {
    IncompleteInstructionFetch { rip: u64 },
    IllegalInstruction { rip: u64 },
    DataAccessFault { address: u64, bytes: usize },
}

/// Whether another instruction can execute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The machine may take another step.
    Running,
    /// Execution stopped at a declared fault.
    Trapped(Trap),
}

/// Complete state exposed by the teaching slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// RAX, RCX, RDX, RBX, RSP, RBP, RSI, and RDI.
    pub registers: [u64; 8],
    /// Selected arithmetic flags.
    pub flags: Flags,
    /// Finite byte-addressed memory.
    pub memory: Memory,
    /// Address of the next instruction.
    pub rip: u64,
    /// Running or trapped outcome.
    pub outcome: Outcome,
}

impl State {
    /// Constructs a zero-register running state.
    #[must_use]
    pub fn new(memory: Memory, rip: u64) -> Self {
        Self {
            registers: [0; 8],
            flags: Flags::default(),
            memory,
            rip,
            outcome: Outcome::Running,
        }
    }

    /// Reads one selected general-purpose register.
    #[must_use]
    pub fn register(&self, index: Register) -> u64 {
        self.registers[usize::from(index)]
    }
}

/// Immutable instruction image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    base: u64,
    code: Vec<u8>,
}

impl Program {
    /// Constructs an instruction image at `base`.
    #[must_use]
    pub fn new(base: u64, code: Vec<u8>) -> Self {
        Self { base, code }
    }

    fn remaining(&self, rip: u64) -> Option<&[u8]> {
        let offset = usize::try_from(rip.wrapping_sub(self.base)).ok()?;
        self.code.get(offset..)
    }
}

/// Canonical refinement-facing state projection.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct StateProjection {
    pub registers: Vec<(Register, u64)>,
    pub flags: Flags,
    pub memory: Vec<(u64, u8)>,
    pub rip: u64,
    pub outcome: Outcome,
}

/// Projection construction error.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectionError {
    InvalidRegister(Register),
    DuplicateRegister(Register),
}

/// Projects selected registers and complete memory canonically.
///
/// # Errors
///
/// Rejects invalid or duplicate selected register indices.
pub fn project_state(
    state: &State,
    mut registers: Vec<Register>,
) -> Result<StateProjection, ProjectionError> {
    registers.sort_unstable();
    if let Some(index) = registers.iter().copied().find(|index| *index >= 8) {
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
        flags: state.flags,
        memory: state.memory.entries().collect(),
        rip: state.rip,
        outcome: state.outcome.clone(),
    })
}

/// Decodes one selected instruction and returns its byte length.
///
/// # Errors
///
/// Distinguishes an incomplete selected prefix from a byte sequence outside
/// the declared slice.
pub fn decode(bytes: &[u8]) -> Result<(Instruction, usize), EncodingError> {
    let first = *bytes.first().ok_or(EncodingError::IncompleteInstruction)?;
    match first {
        0x31 => decode_modrm(bytes, 2, |rm, reg| Instruction::Xor32 {
            destination: rm,
            source: reg,
        }),
        0xb8..=0xbf => {
            require_len(bytes, 5)?;
            let immediate = read_u32(&bytes[1..5])?;
            Ok((
                Instruction::MoveImmediate32 {
                    destination: first - 0xb8,
                    immediate,
                },
                5,
            ))
        }
        0x74 | 0x75 | 0x79 => {
            require_len(bytes, 2)?;
            let condition = match first {
                0x74 => Condition::Equal,
                0x75 => Condition::NotEqual,
                0x79 => Condition::NotSign,
                _ => unreachable!(),
            };
            Ok((
                Instruction::JumpShort {
                    condition,
                    displacement: i8::from_ne_bytes([bytes[1]]),
                },
                2,
            ))
        }
        0x50..=0x57 => Ok((
            Instruction::Push64 {
                source: first - 0x50,
            },
            1,
        )),
        0x58..=0x5f => Ok((
            Instruction::Pop64 {
                destination: first - 0x58,
            },
            1,
        )),
        0xe8 => {
            require_len(bytes, 5)?;
            Ok((
                Instruction::CallRelative {
                    displacement: i32::from_le_bytes(read_u32(&bytes[1..5])?.to_le_bytes()),
                },
                5,
            ))
        }
        0xc3 => Ok((Instruction::Return, 1)),
        0x48 => decode_rex_w(bytes),
        _ => Err(EncodingError::IllegalInstruction),
    }
}

fn decode_rex_w(bytes: &[u8]) -> Result<(Instruction, usize), EncodingError> {
    require_len(bytes, 2)?;
    match bytes[1] {
        0x85 => decode_modrm(&bytes[1..], 3, |rm, reg| Instruction::Test64 {
            lhs: rm,
            rhs: reg,
        }),
        0x33 => decode_memory_modrm(&bytes[1..], 3, |base, reg| Instruction::Xor64Memory {
            destination: reg,
            base,
        }),
        0x83 => {
            require_len(bytes, 4)?;
            let (mode, group, destination) = modrm(bytes[2]);
            if mode != 3 {
                return Err(EncodingError::IllegalInstruction);
            }
            let immediate = i8::from_ne_bytes([bytes[3]]);
            match group {
                0 => Ok((
                    Instruction::AddImmediate64 {
                        destination,
                        immediate,
                    },
                    4,
                )),
                5 => Ok((
                    Instruction::SubImmediate64 {
                        destination,
                        immediate,
                    },
                    4,
                )),
                _ => Err(EncodingError::IllegalInstruction),
            }
        }
        0x89 => decode_modrm(&bytes[1..], 3, |rm, reg| Instruction::Move64 {
            destination: rm,
            source: reg,
        }),
        0x01 => decode_modrm(&bytes[1..], 3, |rm, reg| Instruction::Add64 {
            destination: rm,
            source: reg,
        }),
        0xf7 => {
            require_len(bytes, 3)?;
            let (mode, group, destination) = modrm(bytes[2]);
            if mode == 3 && group == 3 {
                Ok((Instruction::Negate64 { destination }, 3))
            } else {
                Err(EncodingError::IllegalInstruction)
            }
        }
        0x8d => {
            require_len(bytes, 4)?;
            let (mode, destination, base) = modrm(bytes[2]);
            if mode == 1 && base != 4 {
                Ok((
                    Instruction::LoadEffectiveAddress64 {
                        destination,
                        base,
                        displacement: i8::from_ne_bytes([bytes[3]]),
                    },
                    4,
                ))
            } else {
                Err(EncodingError::IllegalInstruction)
            }
        }
        _ => Err(EncodingError::IllegalInstruction),
    }
}

fn decode_modrm(
    bytes: &[u8],
    total_len: usize,
    build: impl FnOnce(Register, Register) -> Instruction,
) -> Result<(Instruction, usize), EncodingError> {
    require_len(bytes, 2)?;
    let (mode, reg, rm) = modrm(bytes[1]);
    if mode != 3 {
        return Err(EncodingError::IllegalInstruction);
    }
    Ok((build(rm, reg), total_len))
}

fn decode_memory_modrm(
    bytes: &[u8],
    total_len: usize,
    build: impl FnOnce(Register, Register) -> Instruction,
) -> Result<(Instruction, usize), EncodingError> {
    require_len(bytes, 2)?;
    let (mode, reg, base) = modrm(bytes[1]);
    if mode != 0 || base == 4 || base == 5 {
        return Err(EncodingError::IllegalInstruction);
    }
    Ok((build(base, reg), total_len))
}

fn modrm(byte: u8) -> (u8, Register, Register) {
    (byte >> 6, (byte >> 3) & 7, byte & 7)
}

fn require_len(bytes: &[u8], length: usize) -> Result<(), EncodingError> {
    if bytes.len() < length {
        Err(EncodingError::IncompleteInstruction)
    } else {
        Ok(())
    }
}

fn read_u32(bytes: &[u8]) -> Result<u32, EncodingError> {
    let bytes: [u8; 4] = bytes
        .try_into()
        .map_err(|_| EncodingError::IncompleteInstruction)?;
    Ok(u32::from_le_bytes(bytes))
}

/// Encodes one selected instruction canonically.
///
/// # Errors
///
/// Rejects registers outside the selected low-eight register set.
pub fn encode(instruction: Instruction) -> Result<Vec<u8>, EncodingError> {
    use Instruction::{
        Add64, AddImmediate64, CallRelative, JumpShort, LoadEffectiveAddress64, Move64,
        MoveImmediate32, Negate64, Pop64, Push64, Return, SubImmediate64, Test64, Xor32,
        Xor64Memory,
    };
    let bytes = match instruction {
        Xor32 {
            destination,
            source,
        } => vec![0x31, register_modrm(source, destination)?],
        MoveImmediate32 {
            destination,
            immediate,
        } => {
            check_register(destination)?;
            let mut bytes = vec![0xb8 + destination];
            bytes.extend(immediate.to_le_bytes());
            bytes
        }
        Test64 { lhs, rhs } => vec![0x48, 0x85, register_modrm(rhs, lhs)?],
        JumpShort {
            condition,
            displacement,
        } => vec![
            match condition {
                Condition::Equal => 0x74,
                Condition::NotEqual => 0x75,
                Condition::NotSign => 0x79,
            },
            displacement.to_ne_bytes()[0],
        ],
        Xor64Memory { destination, base } => {
            check_register(destination)?;
            check_memory_base(base)?;
            vec![0x48, 0x33, (destination << 3) | base]
        }
        AddImmediate64 {
            destination,
            immediate,
        } => vec![
            0x48,
            0x83,
            register_modrm(0, destination)?,
            immediate.to_ne_bytes()[0],
        ],
        SubImmediate64 {
            destination,
            immediate,
        } => vec![
            0x48,
            0x83,
            register_modrm(5, destination)?,
            immediate.to_ne_bytes()[0],
        ],
        Move64 {
            destination,
            source,
        } => vec![0x48, 0x89, register_modrm(source, destination)?],
        Negate64 { destination } => vec![0x48, 0xf7, register_modrm(3, destination)?],
        LoadEffectiveAddress64 {
            destination,
            base,
            displacement,
        } => {
            check_register(destination)?;
            check_memory_base(base)?;
            vec![
                0x48,
                0x8d,
                0x40 | (destination << 3) | base,
                displacement.to_ne_bytes()[0],
            ]
        }
        Push64 { source } => {
            check_register(source)?;
            vec![0x50 + source]
        }
        Pop64 { destination } => {
            check_register(destination)?;
            vec![0x58 + destination]
        }
        CallRelative { displacement } => {
            let mut bytes = vec![0xe8];
            bytes.extend(displacement.to_le_bytes());
            bytes
        }
        Add64 {
            destination,
            source,
        } => vec![0x48, 0x01, register_modrm(source, destination)?],
        Return => vec![0xc3],
    };
    Ok(bytes)
}

fn register_modrm(reg: Register, rm: Register) -> Result<u8, EncodingError> {
    check_register(reg)?;
    check_register(rm)?;
    Ok(0xc0 | (reg << 3) | rm)
}

fn check_register(register: Register) -> Result<(), EncodingError> {
    if register < 8 {
        Ok(())
    } else {
        Err(EncodingError::InvalidRegister(register))
    }
}

fn check_memory_base(register: Register) -> Result<(), EncodingError> {
    check_register(register)?;
    if register == 4 || register == 5 {
        Err(EncodingError::IllegalInstruction)
    } else {
        Ok(())
    }
}

/// Executes one selected x86-64 transition.
#[must_use]
pub fn step(program: &Program, state: &State) -> State {
    if state.outcome != Outcome::Running {
        return state.clone();
    }
    let Some(bytes) = program.remaining(state.rip) else {
        return trapped(state, Trap::IncompleteInstructionFetch { rip: state.rip });
    };
    let (instruction, length) = match decode(bytes) {
        Ok(decoded) => decoded,
        Err(EncodingError::IncompleteInstruction) => {
            return trapped(state, Trap::IncompleteInstructionFetch { rip: state.rip });
        }
        Err(_) => return trapped(state, Trap::IllegalInstruction { rip: state.rip }),
    };
    execute(instruction, length, state)
}

#[allow(clippy::too_many_lines)]
fn execute(instruction: Instruction, length: usize, state: &State) -> State {
    use Instruction::{
        Add64, AddImmediate64, CallRelative, JumpShort, LoadEffectiveAddress64, Move64,
        MoveImmediate32, Negate64, Pop64, Push64, Return, SubImmediate64, Test64, Xor32,
        Xor64Memory,
    };
    let sequential = state
        .rip
        .wrapping_add(u64::try_from(length).expect("instruction length fits"));
    let mut next = state.clone();
    next.rip = sequential;
    match instruction {
        Xor32 {
            destination,
            source,
        } => {
            let result =
                u64::from(low_u32(state.register(destination)) ^ low_u32(state.register(source)));
            next.registers[usize::from(destination)] = result;
            next.flags = logic_flags(result, 32);
        }
        MoveImmediate32 {
            destination,
            immediate,
        } => next.registers[usize::from(destination)] = u64::from(immediate),
        Test64 { lhs, rhs } => {
            next.flags = logic_flags(state.register(lhs) & state.register(rhs), 64);
        }
        JumpShort {
            condition,
            displacement,
        } => {
            let taken = match condition {
                Condition::Equal => state.flags.zero == FlagValue::Set,
                Condition::NotEqual => state.flags.zero == FlagValue::Clear,
                Condition::NotSign => state.flags.sign == FlagValue::Clear,
            };
            if taken {
                next.rip = sequential.wrapping_add_signed(i64::from(displacement));
            }
        }
        Xor64Memory { destination, base } => {
            let address = state.register(base);
            let Some(value) = read_u64(&state.memory, address) else {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            };
            let result = state.register(destination) ^ value;
            next.registers[usize::from(destination)] = result;
            next.flags = logic_flags(result, 64);
        }
        AddImmediate64 {
            destination,
            immediate,
        } => {
            let lhs = state.register(destination);
            let rhs = u64::from_ne_bytes(i64::from(immediate).to_ne_bytes());
            let result = lhs.wrapping_add(rhs);
            next.registers[usize::from(destination)] = result;
            next.flags = add_flags(lhs, rhs, result);
        }
        SubImmediate64 {
            destination,
            immediate,
        } => {
            let lhs = state.register(destination);
            let rhs = u64::from_ne_bytes(i64::from(immediate).to_ne_bytes());
            let result = lhs.wrapping_sub(rhs);
            next.registers[usize::from(destination)] = result;
            next.flags = sub_flags(lhs, rhs, result);
        }
        Move64 {
            destination,
            source,
        } => next.registers[usize::from(destination)] = state.register(source),
        Negate64 { destination } => {
            let value = state.register(destination);
            let result = 0_u64.wrapping_sub(value);
            next.registers[usize::from(destination)] = result;
            next.flags = sub_flags(0, value, result);
            next.flags.carry = FlagValue::from_bool(value != 0);
        }
        LoadEffectiveAddress64 {
            destination,
            base,
            displacement,
        } => {
            next.registers[usize::from(destination)] = state
                .register(base)
                .wrapping_add_signed(i64::from(displacement));
        }
        Push64 { source } => {
            let address = state.register(4).wrapping_sub(8);
            let Some(memory) = write_u64(&state.memory, address, state.register(source)) else {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            };
            next.registers[4] = address;
            next.memory = memory;
        }
        Pop64 { destination } => {
            let address = state.register(4);
            let Some(value) = read_u64(&state.memory, address) else {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            };
            next.registers[4] = address.wrapping_add(8);
            next.registers[usize::from(destination)] = value;
        }
        CallRelative { displacement } => {
            let address = state.register(4).wrapping_sub(8);
            let Some(memory) = write_u64(&state.memory, address, sequential) else {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            };
            next.registers[4] = address;
            next.memory = memory;
            next.rip = sequential.wrapping_add_signed(i64::from(displacement));
        }
        Add64 {
            destination,
            source,
        } => {
            let lhs = state.register(destination);
            let rhs = state.register(source);
            let result = lhs.wrapping_add(rhs);
            next.registers[usize::from(destination)] = result;
            next.flags = add_flags(lhs, rhs, result);
        }
        Return => {
            let address = state.register(4);
            let Some(target) = read_u64(&state.memory, address) else {
                return trapped(state, Trap::DataAccessFault { address, bytes: 8 });
            };
            next.registers[4] = address.wrapping_add(8);
            next.rip = target;
        }
    }
    next
}

fn logic_flags(result: u64, width: u32) -> Flags {
    let sign_bit = 1_u64 << (width - 1);
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    };
    let result = result & mask;
    Flags {
        carry: FlagValue::Clear,
        parity: FlagValue::from_bool(low_u8(result).count_ones().is_multiple_of(2)),
        auxiliary: FlagValue::Undefined,
        zero: FlagValue::from_bool(result == 0),
        sign: FlagValue::from_bool(result & sign_bit != 0),
        overflow: FlagValue::Clear,
    }
}

fn add_flags(lhs: u64, rhs: u64, result: u64) -> Flags {
    Flags {
        carry: FlagValue::from_bool(lhs.overflowing_add(rhs).1),
        parity: FlagValue::from_bool(low_u8(result).count_ones().is_multiple_of(2)),
        auxiliary: FlagValue::from_bool((lhs ^ rhs ^ result) & 0x10 != 0),
        zero: FlagValue::from_bool(result == 0),
        sign: FlagValue::from_bool(result >> 63 != 0),
        overflow: FlagValue::from_bool((!(lhs ^ rhs) & (lhs ^ result)) >> 63 != 0),
    }
}

fn sub_flags(lhs: u64, rhs: u64, result: u64) -> Flags {
    Flags {
        carry: FlagValue::from_bool(lhs < rhs),
        parity: FlagValue::from_bool(low_u8(result).count_ones().is_multiple_of(2)),
        auxiliary: FlagValue::from_bool((lhs ^ rhs ^ result) & 0x10 != 0),
        zero: FlagValue::from_bool(result == 0),
        sign: FlagValue::from_bool(result >> 63 != 0),
        overflow: FlagValue::from_bool(((lhs ^ rhs) & (lhs ^ result)) >> 63 != 0),
    }
}

fn read_u64(memory: &Memory, address: u64) -> Option<u64> {
    let bytes: Option<Vec<u8>> = (0..8)
        .map(|offset| memory.byte_at(address.wrapping_add(offset)))
        .collect();
    Some(u64::from_le_bytes(bytes?.try_into().ok()?))
}

fn low_u32(value: u64) -> u32 {
    u32::from_le_bytes(
        value.to_le_bytes()[..4]
            .try_into()
            .expect("four-byte slice"),
    )
}

fn low_u8(value: u64) -> u8 {
    value.to_le_bytes()[0]
}

fn write_u64(memory: &Memory, address: u64, value: u64) -> Option<Memory> {
    let addresses: Vec<u64> = (0..8).map(|offset| address.wrapping_add(offset)).collect();
    if addresses
        .iter()
        .any(|candidate| memory.byte_at(*candidate).is_none())
    {
        return None;
    }
    let bytes = value.to_le_bytes();
    let entries = memory
        .entries()
        .map(|(candidate, old)| {
            let byte = addresses
                .iter()
                .position(|address| *address == candidate)
                .map_or(old, |index| bytes[index]);
            (candidate, byte)
        })
        .collect();
    Memory::from_entries(entries).ok()
}

fn trapped(state: &State, trap: Trap) -> State {
    let mut trapped = state.clone();
    trapped.outcome = Outcome::Trapped(trap);
    trapped
}
