//! Complete executable semantics for the A0 teaching instruction set.
//!
//! A0 has eight registers, a separate immutable code image, finite byte data
//! memory, four arithmetic condition bits, and explicit halted/trapped states.
//! Every instruction is four bytes and must be four-byte aligned.

use core::fmt;

const REGISTER_COUNT: usize = 8;
const INSTRUCTION_BYTES: u64 = 4;

/// A fixed-width unsigned word with arithmetic modulo `2^width`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Word {
    width: u8,
    value: u64,
}

impl Word {
    /// Constructs a word, reducing `value` modulo `2^width`.
    ///
    /// # Errors
    ///
    /// Returns [`A0Error::InvalidWordWidth`] unless the width is a positive
    /// multiple of eight no greater than 64.
    pub fn new(width: u8, value: u64) -> Result<Self, A0Error> {
        validate_width(width)?;
        Ok(Self {
            width,
            value: value & mask(width),
        })
    }

    /// Returns this word's width in bits.
    #[must_use]
    pub const fn width(self) -> u8 {
        self.width
    }

    /// Returns the unsigned reading.
    #[must_use]
    pub const fn unsigned(self) -> u64 {
        self.value
    }

    /// Returns the signed two's-complement reading.
    #[must_use]
    pub fn signed(self) -> i128 {
        let modulus = 1_i128 << self.width;
        let value = i128::from(self.value);
        if self.high_bit() {
            value - modulus
        } else {
            value
        }
    }

    /// Returns the most significant bit.
    #[must_use]
    pub fn high_bit(self) -> bool {
        self.value & (1_u64 << (self.width - 1)) != 0
    }

    /// Splits the word into bytes from least significant to most significant.
    #[must_use]
    pub fn little_endian_bytes(self) -> Vec<u8> {
        (0..usize::from(self.width / 8))
            .map(|index| ((self.value >> (8 * index)) & 0xff) as u8)
            .collect()
    }

    /// Joins little-endian bytes into a word.
    ///
    /// # Errors
    ///
    /// Returns an error when `bytes` is empty or longer than eight bytes.
    pub fn from_little_endian(bytes: &[u8]) -> Result<Self, A0Error> {
        let width = u8::try_from(bytes.len() * 8).map_err(|_| A0Error::InvalidWordWidth(0))?;
        validate_width(width)?;
        let value = bytes.iter().enumerate().fold(0_u64, |word, (index, byte)| {
            word | (u64::from(*byte) << (8 * index))
        });
        Self::new(width, value)
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        debug_assert_eq!(self.width, rhs.width);
        Self {
            width: self.width,
            value: self.value.wrapping_add(rhs.value) & mask(self.width),
        }
    }

    fn wrapping_add_signed(self, rhs: i128) -> Self {
        let modulus = 1_i128 << self.width;
        let value = u64::try_from((i128::from(self.value) + rhs).rem_euclid(modulus))
            .expect("reduced word value fits u64");
        Self {
            width: self.width,
            value,
        }
    }
}

impl fmt::Debug for Word {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "Word{}({:#x})", self.width, self.value)
    }
}

/// The arithmetic condition state visible to A0 programs.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)]
pub struct Conditions {
    /// Result is zero.
    pub zero: bool,
    /// Result's high bit is set.
    pub negative: bool,
    /// Carry for addition, or no-borrow for subtraction.
    pub carry: bool,
    /// Signed arithmetic overflow.
    pub overflow: bool,
}

/// A reason that a running A0 machine trapped.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trap {
    /// The program counter was not divisible by four.
    MisalignedProgramCounter { pc: u64 },
    /// Four instruction bytes were not available at the program counter.
    IncompleteCodeFetch { pc: u64 },
    /// The four fetched bytes are not a legal A0 encoding.
    IllegalEncoding { pc: u64, bytes: [u8; 4] },
    /// A data access named a byte outside finite memory.
    DataRange {
        address: u64,
        bytes: usize,
        memory_len: usize,
    },
}

/// Whether the machine can take another step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// An instruction may be fetched and executed.
    Running,
    /// A `halt` instruction executed.
    Halted,
    /// Execution stopped at a declared trap.
    Trapped(Trap),
}

/// Finite byte-addressed data memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Memory {
    bytes: Vec<u8>,
}

impl Memory {
    /// Constructs zero-filled memory of `len` bytes.
    #[must_use]
    pub fn zeroed(len: usize) -> Self {
        Self {
            bytes: vec![0; len],
        }
    }

    /// Constructs memory from its bytes.
    #[must_use]
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    /// Returns the byte length.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns whether memory has no bytes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Reads a byte.
    #[must_use]
    pub fn byte(&self, address: usize) -> Option<u8> {
        self.bytes.get(address).copied()
    }

    fn checked_range(&self, address: Word, bytes: usize) -> Result<core::ops::Range<usize>, Trap> {
        let start = usize::try_from(address.unsigned()).map_err(|_| Trap::DataRange {
            address: address.unsigned(),
            bytes,
            memory_len: self.len(),
        })?;
        let end = start
            .checked_add(bytes)
            .filter(|end| *end <= self.len())
            .ok_or(Trap::DataRange {
                address: address.unsigned(),
                bytes,
                memory_len: self.len(),
            })?;
        Ok(start..end)
    }

    fn load(&self, address: Word) -> Result<Word, Trap> {
        let bytes = usize::from(address.width() / 8);
        let range = self.checked_range(address, bytes)?;
        Word::from_little_endian(&self.bytes[range]).map_err(|_| Trap::DataRange {
            address: address.unsigned(),
            bytes,
            memory_len: self.len(),
        })
    }

    fn store(&mut self, address: Word, value: Word) -> Result<(), Trap> {
        let bytes = value.little_endian_bytes();
        let range = self.checked_range(address, bytes.len())?;
        self.bytes[range].copy_from_slice(&bytes);
        Ok(())
    }
}

/// Immutable instruction bytes and their word-valued base address.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    base: Word,
    code: Vec<u8>,
}

impl Program {
    /// Constructs a code image.
    ///
    /// # Errors
    ///
    /// Returns an error if the base word and supplied width differ.
    pub fn new(width: u8, base: Word, code: Vec<u8>) -> Result<Self, A0Error> {
        validate_width(width)?;
        if base.width() != width {
            return Err(A0Error::WidthMismatch {
                expected: width,
                actual: base.width(),
            });
        }
        Ok(Self { base, code })
    }

    /// Returns the entry/base address.
    #[must_use]
    pub const fn entry(&self) -> Word {
        self.base
    }

    fn fetch(&self, pc: Word) -> Result<[u8; 4], Trap> {
        if !pc.unsigned().is_multiple_of(INSTRUCTION_BYTES) {
            return Err(Trap::MisalignedProgramCounter { pc: pc.unsigned() });
        }
        let offset = pc.unsigned().wrapping_sub(self.base.unsigned()) & mask(pc.width());
        let start =
            usize::try_from(offset).map_err(|_| Trap::IncompleteCodeFetch { pc: pc.unsigned() })?;
        let end = start
            .checked_add(4)
            .filter(|end| *end <= self.code.len())
            .ok_or(Trap::IncompleteCodeFetch { pc: pc.unsigned() })?;
        self.code[start..end]
            .try_into()
            .map_err(|_| Trap::IncompleteCodeFetch { pc: pc.unsigned() })
    }
}

/// Complete architectural state of an A0 machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    width: u8,
    /// General registers `r0` through `r7`.
    pub registers: [Word; REGISTER_COUNT],
    /// Mutable data memory.
    pub memory: Memory,
    /// Program counter.
    pub pc: Word,
    /// Arithmetic conditions.
    pub conditions: Conditions,
    /// Running, halted, or trapped outcome.
    pub outcome: Outcome,
}

impl State {
    /// Constructs a zero-register running state at `pc`.
    ///
    /// # Errors
    ///
    /// Returns an error when the width is invalid or `pc` has another width.
    pub fn new(width: u8, memory: Memory, pc: Word) -> Result<Self, A0Error> {
        validate_width(width)?;
        if pc.width() != width {
            return Err(A0Error::WidthMismatch {
                expected: width,
                actual: pc.width(),
            });
        }
        let zero = Word::new(width, 0)?;
        Ok(Self {
            width,
            registers: [zero; REGISTER_COUNT],
            memory,
            pc,
            conditions: Conditions::default(),
            outcome: Outcome::Running,
        })
    }

    /// Returns the configured word width.
    #[must_use]
    pub const fn width(&self) -> u8 {
        self.width
    }
}

/// A decoded A0 instruction.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    /// Copy a register.
    Mov { rd: u8, rs1: u8 },
    /// Load a sign-extended eight-bit immediate.
    MovImmediate { rd: u8, immediate: i8 },
    /// Load one word from memory.
    Load { rd: u8, base: u8, offset: i8 },
    /// Store one word to memory.
    Store { base: u8, source: u8, offset: i8 },
    /// Three-register addition.
    Add { rd: u8, rs1: u8, rs2: u8 },
    /// Three-register subtraction.
    Sub { rd: u8, rs1: u8, rs2: u8 },
    /// Bitwise AND.
    And { rd: u8, rs1: u8, rs2: u8 },
    /// Bitwise OR.
    Or { rd: u8, rs1: u8, rs2: u8 },
    /// Bitwise XOR.
    Xor { rd: u8, rs1: u8, rs2: u8 },
    /// Bitwise complement.
    Not { rd: u8, rs1: u8 },
    /// Logical left shift.
    ShiftLeft { rd: u8, rs1: u8, rs2: u8 },
    /// Logical right shift.
    ShiftRight { rd: u8, rs1: u8, rs2: u8 },
    /// Arithmetic right shift.
    ArithmeticShiftRight { rd: u8, rs1: u8, rs2: u8 },
    /// Compare by subtraction without storing the result.
    Compare { rs1: u8, rs2: u8 },
    /// Conditional PC-relative branch.
    Branch {
        condition: BranchCondition,
        offset: i8,
    },
    /// Unconditional PC-relative jump.
    Jump { offset: i8 },
    /// Stop normally.
    Halt,
}

/// A0's eight condition-code predicates.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchCondition {
    Eq,
    Ne,
    Lt,
    Ge,
    Lo,
    Hs,
    Hi,
    Ls,
}

impl BranchCondition {
    fn decode(value: u8) -> Self {
        match value {
            0 => Self::Eq,
            1 => Self::Ne,
            2 => Self::Lt,
            3 => Self::Ge,
            4 => Self::Lo,
            5 => Self::Hs,
            6 => Self::Hi,
            _ => Self::Ls,
        }
    }

    fn holds(self, flags: Conditions) -> bool {
        match self {
            Self::Eq => flags.zero,
            Self::Ne => !flags.zero,
            Self::Lt => flags.negative != flags.overflow,
            Self::Ge => flags.negative == flags.overflow,
            Self::Lo => !flags.carry,
            Self::Hs => flags.carry,
            Self::Hi => flags.carry && !flags.zero,
            Self::Ls => !flags.carry || flags.zero,
        }
    }
}

/// Decodes one four-byte A0 encoding, rejecting reserved or unused fields.
///
/// # Errors
///
/// Returns [`A0Error::IllegalEncoding`] when the opcode is unknown or any
/// reserved or instruction-unused field is nonzero.
pub fn decode(bytes: [u8; 4]) -> Result<Instruction, A0Error> {
    let [opcode, b1, b2, imm] = bytes;
    if b1 & 0xc0 != 0 || b2 & 0xc0 != 0 {
        return Err(A0Error::IllegalEncoding(bytes));
    }
    let rd = b1 & 7;
    let rs1 = (b1 >> 3) & 7;
    let rs2 = b2 & 7;
    let condition = (b2 >> 3) & 7;
    let no_condition = condition == 0;
    let no_immediate = imm == 0;
    let no_b2 = b2 == 0;
    let decoded = match opcode {
        0x00 if no_b2 && no_immediate => Instruction::Mov { rd, rs1 },
        0x01 if rs1 == 0 && no_b2 => Instruction::MovImmediate {
            rd,
            immediate: imm.cast_signed(),
        },
        0x02 if no_b2 => Instruction::Load {
            rd,
            base: rs1,
            offset: imm.cast_signed(),
        },
        0x03 if rd == 0 && no_condition => Instruction::Store {
            base: rs1,
            source: rs2,
            offset: imm.cast_signed(),
        },
        0x10 if no_condition && no_immediate => Instruction::Add { rd, rs1, rs2 },
        0x11 if no_condition && no_immediate => Instruction::Sub { rd, rs1, rs2 },
        0x12 if no_condition && no_immediate => Instruction::And { rd, rs1, rs2 },
        0x13 if no_condition && no_immediate => Instruction::Or { rd, rs1, rs2 },
        0x14 if no_condition && no_immediate => Instruction::Xor { rd, rs1, rs2 },
        0x15 if no_b2 && no_immediate => Instruction::Not { rd, rs1 },
        0x18 if no_condition && no_immediate => Instruction::ShiftLeft { rd, rs1, rs2 },
        0x19 if no_condition && no_immediate => Instruction::ShiftRight { rd, rs1, rs2 },
        0x1a if no_condition && no_immediate => Instruction::ArithmeticShiftRight { rd, rs1, rs2 },
        0x20 if rd == 0 && no_condition && no_immediate => Instruction::Compare { rs1, rs2 },
        0x30 if b1 == 0 && rs2 == 0 => Instruction::Branch {
            condition: BranchCondition::decode(condition),
            offset: imm.cast_signed(),
        },
        0x31 if b1 == 0 && b2 == 0 => Instruction::Jump {
            offset: imm.cast_signed(),
        },
        0xff if b1 == 0 && b2 == 0 && imm == 0 => Instruction::Halt,
        _ => return Err(A0Error::IllegalEncoding(bytes)),
    };
    Ok(decoded)
}

/// Advances one running state according to the immutable program.
#[must_use]
pub fn step(program: &Program, state: &State) -> State {
    if state.outcome != Outcome::Running {
        return state.clone();
    }
    let bytes = match program.fetch(state.pc) {
        Ok(bytes) => bytes,
        Err(trap) => return trapped(state, trap),
    };
    let instruction = match decode(bytes) {
        Ok(instruction) => instruction,
        Err(A0Error::IllegalEncoding(_)) => {
            return trapped(
                state,
                Trap::IllegalEncoding {
                    pc: state.pc.unsigned(),
                    bytes,
                },
            );
        }
        Err(_) => unreachable!("decode returns only illegal encoding"),
    };
    execute(instruction, state)
}

fn execute(instruction: Instruction, state: &State) -> State {
    let mut next = state.clone();
    let sequential = state.pc.wrapping_add_signed(i128::from(INSTRUCTION_BYTES));
    next.pc = sequential;
    let reg = |index: u8| state.registers[usize::from(index)];
    match instruction {
        Instruction::Mov { rd, rs1 } => next.registers[usize::from(rd)] = reg(rs1),
        Instruction::MovImmediate { rd, immediate } => {
            next.registers[usize::from(rd)] =
                Word::new(state.width, i64::from(immediate).cast_unsigned())
                    .expect("state width is valid");
        }
        Instruction::Load { rd, base, offset } => {
            let address = reg(base).wrapping_add_signed(i128::from(offset));
            match state.memory.load(address) {
                Ok(value) => next.registers[usize::from(rd)] = value,
                Err(trap) => return trapped(state, trap),
            }
        }
        Instruction::Store {
            base,
            source,
            offset,
        } => {
            let address = reg(base).wrapping_add_signed(i128::from(offset));
            if let Err(trap) = next.memory.store(address, reg(source)) {
                return trapped(state, trap);
            }
        }
        Instruction::Add { rd, rs1, rs2 } => {
            let (result, flags) = add_flags(reg(rs1), reg(rs2));
            next.registers[usize::from(rd)] = result;
            next.conditions = flags;
        }
        Instruction::Sub { rd, rs1, rs2 } => {
            let (result, flags) = sub_flags(reg(rs1), reg(rs2));
            next.registers[usize::from(rd)] = result;
            next.conditions = flags;
        }
        Instruction::And { rd, rs1, rs2 } => {
            logic(&mut next, rd, reg(rs1).unsigned() & reg(rs2).unsigned());
        }
        Instruction::Or { rd, rs1, rs2 } => {
            logic(&mut next, rd, reg(rs1).unsigned() | reg(rs2).unsigned());
        }
        Instruction::Xor { rd, rs1, rs2 } => {
            logic(&mut next, rd, reg(rs1).unsigned() ^ reg(rs2).unsigned());
        }
        Instruction::Not { rd, rs1 } => logic(&mut next, rd, !reg(rs1).unsigned()),
        Instruction::ShiftLeft { rd, rs1, rs2 } => {
            shift(&mut next, rd, reg(rs1), reg(rs2), Shift::Left);
        }
        Instruction::ShiftRight { rd, rs1, rs2 } => {
            shift(&mut next, rd, reg(rs1), reg(rs2), Shift::Right);
        }
        Instruction::ArithmeticShiftRight { rd, rs1, rs2 } => {
            shift(&mut next, rd, reg(rs1), reg(rs2), Shift::ArithmeticRight);
        }
        Instruction::Compare { rs1, rs2 } => next.conditions = sub_flags(reg(rs1), reg(rs2)).1,
        Instruction::Branch { condition, offset } => {
            if condition.holds(state.conditions) {
                next.pc = sequential.wrapping_add_signed(i128::from(offset) * 4);
            }
        }
        Instruction::Jump { offset } => {
            next.pc = sequential.wrapping_add_signed(i128::from(offset) * 4);
        }
        Instruction::Halt => next.outcome = Outcome::Halted,
    }
    next
}

fn logic(state: &mut State, rd: u8, value: u64) {
    let result = Word::new(state.width, value).expect("state width is valid");
    state.registers[usize::from(rd)] = result;
    state.conditions = Conditions {
        zero: result.unsigned() == 0,
        negative: result.high_bit(),
        carry: false,
        overflow: false,
    };
}

#[derive(Clone, Copy)]
enum Shift {
    Left,
    Right,
    ArithmeticRight,
}

fn shift(state: &mut State, rd: u8, source: Word, count_word: Word, direction: Shift) {
    let count = u32::try_from(count_word.unsigned() % u64::from(source.width()))
        .expect("shift count is below 64");
    let (value, carry) = if count == 0 {
        (source.unsigned(), false)
    } else {
        match direction {
            Shift::Left => (
                source.unsigned() << count,
                (source.unsigned() >> (u32::from(source.width()) - count)) & 1 != 0,
            ),
            Shift::Right => (
                source.unsigned() >> count,
                (source.unsigned() >> (count - 1)) & 1 != 0,
            ),
            Shift::ArithmeticRight => {
                let extended = if source.high_bit() {
                    source.unsigned() | !mask(source.width())
                } else {
                    source.unsigned()
                };
                (
                    extended >> count,
                    (source.unsigned() >> (count - 1)) & 1 != 0,
                )
            }
        }
    };
    let result = Word::new(source.width(), value).expect("source width is valid");
    state.registers[usize::from(rd)] = result;
    state.conditions = Conditions {
        zero: result.unsigned() == 0,
        negative: result.high_bit(),
        carry,
        overflow: false,
    };
}

fn add_flags(lhs: Word, rhs: Word) -> (Word, Conditions) {
    let full = u128::from(lhs.unsigned()) + u128::from(rhs.unsigned());
    let result = lhs.wrapping_add(rhs);
    let carry = full >= (1_u128 << lhs.width());
    let overflow = lhs.high_bit() == rhs.high_bit() && result.high_bit() != lhs.high_bit();
    (
        result,
        Conditions {
            zero: result.unsigned() == 0,
            negative: result.high_bit(),
            carry,
            overflow,
        },
    )
}

fn sub_flags(lhs: Word, rhs: Word) -> (Word, Conditions) {
    let result =
        Word::new(lhs.width(), lhs.unsigned().wrapping_sub(rhs.unsigned())).expect("width valid");
    let overflow = lhs.high_bit() != rhs.high_bit() && result.high_bit() != lhs.high_bit();
    (
        result,
        Conditions {
            zero: result.unsigned() == 0,
            negative: result.high_bit(),
            carry: lhs.unsigned() >= rhs.unsigned(),
            overflow,
        },
    )
}

fn trapped(state: &State, trap: Trap) -> State {
    let mut next = state.clone();
    next.outcome = Outcome::Trapped(trap);
    next
}

/// Why a bounded execution stopped.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    Halted,
    Trapped,
    BoundExhausted,
}

/// A replayable bounded state trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace {
    /// States including the initial state.
    pub states: Vec<State>,
    /// Classification of the final state.
    pub stop: StopReason,
}

/// Runs at most `max_steps` transitions and retains every state.
#[must_use]
pub fn run(program: &Program, initial: State, max_steps: usize) -> Trace {
    let mut current = initial;
    let mut states = vec![current.clone()];
    for _ in 0..max_steps {
        if current.outcome != Outcome::Running {
            break;
        }
        current = step(program, &current);
        states.push(current.clone());
    }
    let stop = match &current.outcome {
        Outcome::Halted => StopReason::Halted,
        Outcome::Trapped(_) => StopReason::Trapped,
        Outcome::Running => StopReason::BoundExhausted,
    };
    Trace { states, stop }
}

/// Construction or decoding failure outside machine execution.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A0Error {
    /// Width is not 8, 16, ..., or 64.
    InvalidWordWidth(u8),
    /// Two values that must share a width do not.
    WidthMismatch { expected: u8, actual: u8 },
    /// Reserved or unused encoding fields were nonzero, or opcode was unknown.
    IllegalEncoding([u8; 4]),
}

fn validate_width(width: u8) -> Result<(), A0Error> {
    if width == 0 || width > 64 || !width.is_multiple_of(8) {
        Err(A0Error::InvalidWordWidth(width))
    } else {
        Ok(())
    }
}

const fn mask(width: u8) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    }
}
