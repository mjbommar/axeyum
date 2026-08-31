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

    /// Extends this word with zero high bits to `new_width`.
    ///
    /// # Errors
    ///
    /// Returns [`A0Error::InvalidWordWidth`] when `new_width` is not a
    /// supported A0 width, and [`A0Error::InvalidWidthConversion`] when it is
    /// narrower than the source word.
    pub fn zero_extend(self, new_width: u8) -> Result<Self, A0Error> {
        validate_width(new_width)?;
        if new_width < self.width {
            return Err(A0Error::InvalidWidthConversion {
                from: self.width,
                to: new_width,
            });
        }
        Self::new(new_width, self.value)
    }

    /// Extends this word by repeating its sign bit to `new_width`.
    ///
    /// # Errors
    ///
    /// Returns [`A0Error::InvalidWordWidth`] when `new_width` is not a
    /// supported A0 width, and [`A0Error::InvalidWidthConversion`] when it is
    /// narrower than the source word.
    pub fn sign_extend(self, new_width: u8) -> Result<Self, A0Error> {
        validate_width(new_width)?;
        if new_width < self.width {
            return Err(A0Error::InvalidWidthConversion {
                from: self.width,
                to: new_width,
            });
        }
        let value = if self.high_bit() {
            self.value | (mask(new_width) & !mask(self.width))
        } else {
            self.value
        };
        Self::new(new_width, value)
    }

    /// Truncates this word to its `new_width` least-significant bits.
    ///
    /// # Errors
    ///
    /// Returns [`A0Error::InvalidWordWidth`] when `new_width` is not a
    /// supported A0 width, and [`A0Error::InvalidWidthConversion`] when it is
    /// wider than the source word.
    pub fn truncate(self, new_width: u8) -> Result<Self, A0Error> {
        validate_width(new_width)?;
        if new_width > self.width {
            return Err(A0Error::InvalidWidthConversion {
                from: self.width,
                to: new_width,
            });
        }
        Self::new(new_width, self.value)
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

/// Result and condition bits produced by the shared A0 addition definition.
///
/// The type parameters allow evidence producers to instantiate the same
/// orchestration with concrete words and Booleans or with symbolic terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Addition<W, B> {
    /// Sum reduced to the architectural word width.
    pub result: W,
    /// Whether the reduced result is zero.
    pub zero: B,
    /// Most-significant bit of the reduced result.
    pub negative: B,
    /// Unsigned carry out of the architectural word width.
    pub carry: B,
    /// Signed two's-complement overflow.
    pub overflow: B,
}

/// Primitive operations used by the shared A0 addition definition.
///
/// Implementations are the explicit trust boundary between the A0 operation
/// structure and a concrete or symbolic word domain.
pub trait AdditionDomain {
    /// Domain representation of an architectural word.
    type Word: Copy;
    /// Domain representation of a condition bit.
    type Bit: Copy;

    /// Computes the reduced sum.
    fn sum(&mut self, lhs: Self::Word, rhs: Self::Word) -> Self::Word;
    /// Tests a word for zero.
    fn is_zero(&mut self, word: Self::Word) -> Self::Bit;
    /// Extracts the most-significant bit.
    fn high_bit(&mut self, word: Self::Word) -> Self::Bit;
    /// Computes unsigned carry out.
    fn carry(&mut self, lhs: Self::Word, rhs: Self::Word, sum: Self::Word) -> Self::Bit;
    /// Computes signed two's-complement overflow.
    fn overflow(&mut self, lhs: Self::Word, rhs: Self::Word, sum: Self::Word) -> Self::Bit;
}

/// Applies the single A0 addition orchestration to a supplied word domain.
pub fn addition<D: AdditionDomain>(
    domain: &mut D,
    lhs: D::Word,
    rhs: D::Word,
) -> Addition<D::Word, D::Bit> {
    let result = domain.sum(lhs, rhs);
    Addition {
        result,
        zero: domain.is_zero(result),
        negative: domain.high_bit(result),
        carry: domain.carry(lhs, rhs, result),
        overflow: domain.overflow(lhs, rhs, result),
    }
}

/// Result of one shared A0 memory load orchestration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryLoad<W, B> {
    /// Whether every byte address required by the access is present.
    pub valid: B,
    /// Little-endian reconstruction of the addressed bytes.
    ///
    /// The value is meaningful only when [`Self::valid`] holds.
    pub value: W,
}

/// Result of one shared A0 memory store orchestration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryStore<M, B> {
    /// Whether every byte address required by the access is present.
    pub valid: B,
    /// Successful updated memory, or the complete original memory on failure.
    pub memory: M,
}

/// Primitive operations used by the shared A0 load/store definitions.
///
/// Implementations form the explicit boundary between the architecture's
/// address-by-address orchestration and a concrete or symbolic memory domain.
pub trait MemoryDomain {
    /// Complete memory representation.
    type Memory: Clone;
    /// Word-valued byte address.
    type Address: Copy;
    /// One stored byte.
    type Byte: Copy;
    /// One architectural word.
    type Word: Copy;
    /// Boolean validity result.
    type Bit: Copy;

    /// Number of bytes in one architectural word.
    fn word_bytes(&self) -> usize;
    /// Boolean truth.
    fn true_bit(&mut self) -> Self::Bit;
    /// Boolean conjunction.
    fn and(&mut self, lhs: Self::Bit, rhs: Self::Bit) -> Self::Bit;
    /// Modular address addition by a nonnegative byte offset.
    fn address_offset(&mut self, base: Self::Address, offset: usize) -> Self::Address;
    /// Tests whether one byte address belongs to the finite memory domain.
    fn present(&mut self, memory: &Self::Memory, address: Self::Address) -> Self::Bit;
    /// Reads one byte, returning a domain-defined placeholder when absent.
    fn read_byte(&mut self, memory: &Self::Memory, address: Self::Address) -> Self::Byte;
    /// Joins bytes in increasing address order into one little-endian word.
    fn join_little_endian(&mut self, bytes: &[Self::Byte]) -> Self::Word;
    /// Splits one word into bytes from least to most significant.
    fn split_little_endian(&mut self, word: Self::Word) -> Vec<Self::Byte>;
    /// Returns memory with one byte updated. An absent address may remain
    /// unchanged because the final validity choice discards the tentative map.
    fn write_byte(
        &mut self,
        memory: Self::Memory,
        address: Self::Address,
        byte: Self::Byte,
    ) -> Self::Memory;
    /// Chooses the complete success or failure memory from the validity bit.
    fn choose_memory(
        &mut self,
        valid: Self::Bit,
        success: Self::Memory,
        failure: Self::Memory,
    ) -> Self::Memory;
}

/// Applies the A0 address, validity, byte-order, and reconstruction rules for a
/// word-sized load in any concrete or symbolic memory domain.
pub fn memory_load<D: MemoryDomain>(
    domain: &mut D,
    memory: &D::Memory,
    address: D::Address,
) -> MemoryLoad<D::Word, D::Bit> {
    let mut valid = domain.true_bit();
    let mut bytes = Vec::with_capacity(domain.word_bytes());
    for offset in 0..domain.word_bytes() {
        let candidate = domain.address_offset(address, offset);
        let present = domain.present(memory, candidate);
        valid = domain.and(valid, present);
        bytes.push(domain.read_byte(memory, candidate));
    }
    MemoryLoad {
        valid,
        value: domain.join_little_endian(&bytes),
    }
}

/// Applies the A0 address, validity, byte-order, atomic-failure, and update
/// rules for a word-sized store in any concrete or symbolic memory domain.
pub fn memory_store<D: MemoryDomain>(
    domain: &mut D,
    memory: &D::Memory,
    address: D::Address,
    value: D::Word,
) -> MemoryStore<D::Memory, D::Bit> {
    let bytes = domain.split_little_endian(value);
    debug_assert_eq!(bytes.len(), domain.word_bytes());
    let mut valid = domain.true_bit();
    let mut updated = memory.clone();
    for (offset, byte) in bytes.into_iter().enumerate() {
        let candidate = domain.address_offset(address, offset);
        let present = domain.present(memory, candidate);
        valid = domain.and(valid, present);
        updated = domain.write_byte(updated, candidate, byte);
    }
    MemoryStore {
        valid,
        memory: domain.choose_memory(valid, updated, memory.clone()),
    }
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
    entries: Vec<(u64, u8)>,
}

impl Memory {
    /// Constructs zero-filled memory of `len` bytes.
    #[must_use]
    pub fn zeroed(len: usize) -> Self {
        Self::from_bytes(vec![0; len])
    }

    /// Constructs memory from its bytes.
    ///
    /// # Panics
    ///
    /// Panics only on a platform whose address-sized integer can represent a
    /// vector index greater than `u64::MAX`.
    #[must_use]
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        let entries = bytes
            .into_iter()
            .enumerate()
            .map(|(address, byte)| {
                (
                    u64::try_from(address).expect("allocated memory index fits u64"),
                    byte,
                )
            })
            .collect();
        Self { entries }
    }

    /// Constructs memory from arbitrary address-byte pairs.
    ///
    /// Entries are sorted into canonical address order. Duplicate addresses
    /// are rejected rather than silently choosing one stored byte.
    ///
    /// # Errors
    ///
    /// Returns [`A0Error::DuplicateMemoryAddress`] for the first duplicate.
    pub fn from_entries(mut entries: Vec<(u64, u8)>) -> Result<Self, A0Error> {
        entries.sort_unstable_by_key(|(address, _)| *address);
        if let Some(address) = entries
            .windows(2)
            .find_map(|pair| (pair[0].0 == pair[1].0).then_some(pair[0].0))
        {
            return Err(A0Error::DuplicateMemoryAddress(address));
        }
        Ok(Self { entries })
    }

    /// Returns the byte length.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns whether memory has no bytes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Reads a byte.
    #[must_use]
    pub fn byte(&self, address: usize) -> Option<u8> {
        u64::try_from(address)
            .ok()
            .and_then(|address| self.byte_at(address))
    }

    /// Reads one mapped byte by its complete word-valued address.
    #[must_use]
    pub fn byte_at(&self, address: u64) -> Option<u8> {
        self.entries
            .binary_search_by_key(&address, |(candidate, _)| *candidate)
            .ok()
            .map(|index| self.entries[index].1)
    }

    /// Iterates mapped address-byte pairs in canonical address order.
    pub fn entries(&self) -> impl ExactSizeIterator<Item = (u64, u8)> + '_ {
        self.entries.iter().copied()
    }

    fn load(&self, address: Word) -> Result<Word, Trap> {
        let bytes = usize::from(address.width() / 8);
        let access = memory_load(
            &mut ConcreteMemoryDomain {
                width: address.width(),
            },
            self,
            address,
        );
        access.valid.then_some(access.value).ok_or(Trap::DataRange {
            address: address.unsigned(),
            bytes,
            memory_len: self.len(),
        })
    }

    fn store(&mut self, address: Word, value: Word) -> Result<(), Trap> {
        let bytes = usize::from(value.width() / 8);
        let access = memory_store(
            &mut ConcreteMemoryDomain {
                width: value.width(),
            },
            self,
            address,
            value,
        );
        if access.valid {
            *self = access.memory;
            Ok(())
        } else {
            Err(Trap::DataRange {
                address: address.unsigned(),
                bytes,
                memory_len: self.len(),
            })
        }
    }
}

struct ConcreteMemoryDomain {
    width: u8,
}

impl MemoryDomain for ConcreteMemoryDomain {
    type Memory = Memory;
    type Address = Word;
    type Byte = u8;
    type Word = Word;
    type Bit = bool;

    fn word_bytes(&self) -> usize {
        usize::from(self.width / 8)
    }

    fn true_bit(&mut self) -> bool {
        true
    }

    fn and(&mut self, lhs: bool, rhs: bool) -> bool {
        lhs && rhs
    }

    fn address_offset(&mut self, base: Word, offset: usize) -> Word {
        base.wrapping_add_signed(i128::try_from(offset).expect("word byte count fits i128"))
    }

    fn present(&mut self, memory: &Memory, address: Word) -> bool {
        memory.byte_at(address.unsigned()).is_some()
    }

    fn read_byte(&mut self, memory: &Memory, address: Word) -> u8 {
        memory.byte_at(address.unsigned()).unwrap_or(0)
    }

    fn join_little_endian(&mut self, bytes: &[u8]) -> Word {
        Word::from_little_endian(bytes).expect("one A0 word has a supported byte width")
    }

    fn split_little_endian(&mut self, word: Word) -> Vec<u8> {
        word.little_endian_bytes()
    }

    fn write_byte(&mut self, mut memory: Memory, address: Word, byte: u8) -> Memory {
        if let Ok(index) = memory
            .entries
            .binary_search_by_key(&address.unsigned(), |(entry, _)| *entry)
        {
            memory.entries[index].1 = byte;
        }
        memory
    }

    fn choose_memory(&mut self, valid: bool, success: Memory, failure: Memory) -> Memory {
        if valid { success } else { failure }
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
        if let Some((address, _)) = memory
            .entries()
            .find(|(address, _)| *address & !mask(width) != 0)
        {
            return Err(A0Error::InvalidMemoryAddress { width, address });
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

const STATE_MAGIC: [u8; 4] = *b"A0ST";
const STATE_ENCODING_VERSION: u8 = 1;

/// Encodes one well-formed A0 state in the canonical binary artifact format.
///
/// The format fixes field order, integer width and byte order. It includes the
/// complete finite memory domain and rejects a state containing a register,
/// program counter, or trap address outside the state's declared word width.
///
/// # Errors
///
/// Returns a categorized [`A0Error`] when the state is not well formed or its
/// memory length cannot be represented by the format.
pub fn encode_state(state: &State) -> Result<Vec<u8>, A0Error> {
    validate_width(state.width)?;
    for register in state.registers {
        if register.width() != state.width {
            return Err(A0Error::StateWidthMismatch {
                component: "register",
                expected: state.width,
                actual: register.width(),
            });
        }
    }
    if state.pc.width() != state.width {
        return Err(A0Error::StateWidthMismatch {
            component: "program-counter",
            expected: state.width,
            actual: state.pc.width(),
        });
    }
    let memory_len = u64::try_from(state.memory.len())
        .map_err(|_| A0Error::InvalidStateEncoding("memory length exceeds u64"))?;
    let mut encoded =
        Vec::with_capacity(90_usize.saturating_add(state.memory.len().saturating_mul(9)));
    encoded.extend_from_slice(&STATE_MAGIC);
    encoded.push(STATE_ENCODING_VERSION);
    encoded.push(state.width);
    encoded.extend_from_slice(&memory_len.to_le_bytes());
    for register in state.registers {
        encoded.extend_from_slice(&register.unsigned().to_le_bytes());
    }
    for (address, byte) in state.memory.entries() {
        validate_state_value(state.width, address, "memory address")?;
        encoded.extend_from_slice(&address.to_le_bytes());
        encoded.push(byte);
    }
    encoded.extend_from_slice(&state.pc.unsigned().to_le_bytes());
    encoded.push(
        u8::from(state.conditions.zero)
            | (u8::from(state.conditions.negative) << 1)
            | (u8::from(state.conditions.carry) << 2)
            | (u8::from(state.conditions.overflow) << 3),
    );
    encode_outcome(
        &mut encoded,
        state.width,
        state.memory.len(),
        &state.outcome,
    )?;
    Ok(encoded)
}

fn encode_outcome(
    encoded: &mut Vec<u8>,
    width: u8,
    memory_len: usize,
    outcome: &Outcome,
) -> Result<(), A0Error> {
    match outcome {
        Outcome::Running => encoded.push(0),
        Outcome::Halted => encoded.push(1),
        Outcome::Trapped(trap) => {
            encoded.push(2);
            match trap {
                Trap::MisalignedProgramCounter { pc } => {
                    validate_state_value(width, *pc, "trap program-counter")?;
                    encoded.push(0);
                    encoded.extend_from_slice(&pc.to_le_bytes());
                }
                Trap::IncompleteCodeFetch { pc } => {
                    validate_state_value(width, *pc, "trap program-counter")?;
                    encoded.push(1);
                    encoded.extend_from_slice(&pc.to_le_bytes());
                }
                Trap::IllegalEncoding { pc, bytes } => {
                    validate_state_value(width, *pc, "trap program-counter")?;
                    encoded.push(2);
                    encoded.extend_from_slice(&pc.to_le_bytes());
                    encoded.extend_from_slice(bytes);
                }
                Trap::DataRange {
                    address,
                    bytes,
                    memory_len: trapped_memory_len,
                } => {
                    validate_state_value(width, *address, "trap data address")?;
                    if *trapped_memory_len != memory_len {
                        return Err(A0Error::InvalidStateEncoding(
                            "data-range trap memory length differs from state memory",
                        ));
                    }
                    encoded.push(3);
                    encoded.extend_from_slice(&address.to_le_bytes());
                    encoded.extend_from_slice(
                        &u64::try_from(*bytes)
                            .map_err(|_| {
                                A0Error::InvalidStateEncoding("trap byte count exceeds u64")
                            })?
                            .to_le_bytes(),
                    );
                    encoded.extend_from_slice(
                        &u64::try_from(*trapped_memory_len)
                            .map_err(|_| {
                                A0Error::InvalidStateEncoding("trap memory length exceeds u64")
                            })?
                            .to_le_bytes(),
                    );
                }
            }
        }
    }
    Ok(())
}

fn validate_state_value(width: u8, value: u64, component: &'static str) -> Result<(), A0Error> {
    if value & !mask(width) != 0 {
        Err(A0Error::InvalidStateEncoding(component))
    } else {
        Ok(())
    }
}

struct StateDecoder<'a> {
    remaining: &'a [u8],
}

impl<'a> StateDecoder<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8], A0Error> {
        if self.remaining.len() < len {
            return Err(A0Error::InvalidStateEncoding("truncated state encoding"));
        }
        let (taken, remaining) = self.remaining.split_at(len);
        self.remaining = remaining;
        Ok(taken)
    }

    fn byte(&mut self) -> Result<u8, A0Error> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, A0Error> {
        let bytes: [u8; 8] = self
            .take(8)?
            .try_into()
            .map_err(|_| A0Error::InvalidStateEncoding("invalid u64 field"))?;
        Ok(u64::from_le_bytes(bytes))
    }
}

/// Decodes one canonical binary A0 state encoding.
///
/// # Errors
///
/// Rejects bad magic or version, unsupported widths, out-of-width values,
/// reserved condition bits, unknown outcome or trap tags, inconsistent trap
/// memory lengths, truncation, and trailing bytes.
pub fn decode_state(encoded: &[u8]) -> Result<State, A0Error> {
    let mut decoder = StateDecoder { remaining: encoded };
    if decoder.take(4)? != STATE_MAGIC {
        return Err(A0Error::InvalidStateEncoding("bad state magic"));
    }
    if decoder.byte()? != STATE_ENCODING_VERSION {
        return Err(A0Error::InvalidStateEncoding(
            "unsupported state encoding version",
        ));
    }
    let width = decoder.byte()?;
    validate_width(width)?;
    let memory_len = usize::try_from(decoder.u64()?)
        .map_err(|_| A0Error::InvalidStateEncoding("memory length exceeds usize"))?;
    let mut register_values = [0_u64; REGISTER_COUNT];
    for value in &mut register_values {
        *value = decoder.u64()?;
        validate_state_value(width, *value, "register exceeds state width")?;
    }
    let mut memory_entries = Vec::with_capacity(memory_len);
    for _ in 0..memory_len {
        let address = decoder.u64()?;
        validate_state_value(width, address, "memory address exceeds state width")?;
        memory_entries.push((address, decoder.byte()?));
    }
    let memory = Memory::from_entries(memory_entries)?;
    let pc_value = decoder.u64()?;
    validate_state_value(width, pc_value, "program-counter exceeds state width")?;
    let condition_bits = decoder.byte()?;
    if condition_bits & !0x0f != 0 {
        return Err(A0Error::InvalidStateEncoding(
            "reserved condition bits are nonzero",
        ));
    }
    let outcome_tag = decoder.byte()?;
    let outcome = match outcome_tag {
        0 => Outcome::Running,
        1 => Outcome::Halted,
        2 => Outcome::Trapped(decode_trap(&mut decoder, width, memory_len)?),
        _ => return Err(A0Error::InvalidStateEncoding("unknown outcome tag")),
    };
    if !decoder.remaining.is_empty() {
        return Err(A0Error::InvalidStateEncoding("trailing state bytes"));
    }
    let zero = Word::new(width, 0)?;
    let mut registers = [zero; REGISTER_COUNT];
    for (register, value) in registers.iter_mut().zip(register_values) {
        *register = Word::new(width, value)?;
    }
    Ok(State {
        width,
        registers,
        memory,
        pc: Word::new(width, pc_value)?,
        conditions: Conditions {
            zero: condition_bits & 1 != 0,
            negative: condition_bits & 2 != 0,
            carry: condition_bits & 4 != 0,
            overflow: condition_bits & 8 != 0,
        },
        outcome,
    })
}

fn decode_trap(
    decoder: &mut StateDecoder<'_>,
    width: u8,
    state_memory_len: usize,
) -> Result<Trap, A0Error> {
    let tag = decoder.byte()?;
    let first = decoder.u64()?;
    validate_state_value(
        width,
        first,
        if tag == 3 {
            "trap data address exceeds state width"
        } else {
            "trap program-counter exceeds state width"
        },
    )?;
    match tag {
        0 => Ok(Trap::MisalignedProgramCounter { pc: first }),
        1 => Ok(Trap::IncompleteCodeFetch { pc: first }),
        2 => Ok(Trap::IllegalEncoding {
            pc: first,
            bytes: decoder
                .take(4)?
                .try_into()
                .map_err(|_| A0Error::InvalidStateEncoding("invalid instruction bytes"))?,
        }),
        3 => {
            let bytes = usize::try_from(decoder.u64()?)
                .map_err(|_| A0Error::InvalidStateEncoding("trap byte count exceeds usize"))?;
            let memory_len = usize::try_from(decoder.u64()?)
                .map_err(|_| A0Error::InvalidStateEncoding("trap memory length exceeds usize"))?;
            if memory_len != state_memory_len {
                return Err(A0Error::InvalidStateEncoding(
                    "data-range trap memory length differs from state memory",
                ));
            }
            Ok(Trap::DataRange {
                address: first,
                bytes,
                memory_len,
            })
        }
        _ => Err(A0Error::InvalidStateEncoding("unknown trap tag")),
    }
}

/// One finite half-open byte range selected by an observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemorySpan {
    /// First selected byte address.
    pub start: usize,
    /// Number of selected bytes.
    pub len: usize,
}

/// A declared projection from complete A0 state to visible components.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observation {
    registers: Vec<u8>,
    memory: Vec<MemorySpan>,
    include_pc: bool,
    include_conditions: bool,
    include_outcome: bool,
}

impl Observation {
    /// Constructs a canonical register-and-memory observation.
    ///
    /// Register indices and memory spans are sorted. Duplicate registers,
    /// empty spans, and overlapping spans are rejected rather than normalized
    /// to a second spelling of the same observation.
    ///
    /// # Errors
    ///
    /// Returns a categorized error for an invalid register or memory span.
    pub fn new(
        mut registers: Vec<u8>,
        mut memory: Vec<MemorySpan>,
    ) -> Result<Self, ObservationError> {
        registers.sort_unstable();
        if let Some(index) = registers.iter().copied().find(|index| *index >= 8) {
            return Err(ObservationError::InvalidRegister(index));
        }
        if let Some(index) = registers
            .windows(2)
            .find_map(|pair| (pair[0] == pair[1]).then_some(pair[0]))
        {
            return Err(ObservationError::DuplicateRegister(index));
        }
        memory.sort_unstable_by_key(|span| span.start);
        for span in &memory {
            if span.len == 0 {
                return Err(ObservationError::EmptyMemorySpan { start: span.start });
            }
            if span.start.checked_add(span.len).is_none() {
                return Err(ObservationError::MemorySpanOverflow {
                    start: span.start,
                    len: span.len,
                });
            }
        }
        for pair in memory.windows(2) {
            let previous_end = pair[0].start.saturating_add(pair[0].len);
            if previous_end > pair[1].start {
                return Err(ObservationError::OverlappingMemorySpans {
                    first: pair[0],
                    second: pair[1],
                });
            }
        }
        Ok(Self {
            registers,
            memory,
            include_pc: false,
            include_conditions: false,
            include_outcome: false,
        })
    }

    /// Includes the program counter.
    #[must_use]
    pub const fn with_program_counter(mut self) -> Self {
        self.include_pc = true;
        self
    }

    /// Includes all four arithmetic conditions.
    #[must_use]
    pub const fn with_conditions(mut self) -> Self {
        self.include_conditions = true;
        self
    }

    /// Includes the running, halted, or trapped outcome.
    #[must_use]
    pub const fn with_outcome(mut self) -> Self {
        self.include_outcome = true;
        self
    }

    /// Applies this observation without changing the complete state.
    ///
    /// # Errors
    ///
    /// Returns [`ObservationError::MemoryRange`] if a selected span is not
    /// contained in the state's finite memory.
    pub fn apply(&self, state: &State) -> Result<ObservedState, ObservationError> {
        let registers = self
            .registers
            .iter()
            .map(|index| RegisterObservation {
                index: *index,
                value: state.registers[usize::from(*index)],
            })
            .collect();
        let mut memory = Vec::with_capacity(self.memory.len());
        for span in &self.memory {
            span.start
                .checked_add(span.len)
                .ok_or(ObservationError::MemoryRange {
                    start: span.start,
                    len: span.len,
                    memory_len: state.memory.len(),
                })?;
            let bytes: Option<Vec<u8>> = (span.start..span.start + span.len)
                .map(|address| state.memory.byte(address))
                .collect();
            let bytes = bytes.ok_or(ObservationError::MemoryRange {
                start: span.start,
                len: span.len,
                memory_len: state.memory.len(),
            })?;
            memory.push(MemoryObservation {
                start: span.start,
                bytes,
            });
        }
        Ok(ObservedState {
            width: state.width,
            registers,
            memory,
            pc: self.include_pc.then_some(state.pc),
            conditions: self.include_conditions.then_some(state.conditions),
            outcome: self.include_outcome.then_some(state.outcome.clone()),
        })
    }
}

/// One register retained by an observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegisterObservation {
    /// Register index in canonical order.
    pub index: u8,
    /// Retained word.
    pub value: Word,
}

/// One memory span retained by an observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryObservation {
    /// First retained byte address.
    pub start: usize,
    /// Retained bytes in increasing address order.
    pub bytes: Vec<u8>,
}

/// Canonical visible result of applying an [`Observation`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservedState {
    /// Architectural word width.
    pub width: u8,
    /// Selected registers, sorted by index.
    pub registers: Vec<RegisterObservation>,
    /// Selected nonoverlapping memory spans, sorted by start address.
    pub memory: Vec<MemoryObservation>,
    /// Program counter when requested.
    pub pc: Option<Word>,
    /// Arithmetic conditions when requested.
    pub conditions: Option<Conditions>,
    /// Machine outcome when requested.
    pub outcome: Option<Outcome>,
}

/// Construction or application failure for an A0 observation.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObservationError {
    InvalidRegister(u8),
    DuplicateRegister(u8),
    EmptyMemorySpan {
        start: usize,
    },
    MemorySpanOverflow {
        start: usize,
        len: usize,
    },
    OverlappingMemorySpans {
        first: MemorySpan,
        second: MemorySpan,
    },
    MemoryRange {
        start: usize,
        len: usize,
        memory_len: usize,
    },
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

/// One architectural state component in an instruction footprint.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateComponent {
    Register(u8),
    Memory { address: Word, bytes: usize },
    ProgramCounter,
    Conditions,
    Outcome,
}

/// Dynamic architectural read and write footprints for one instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Effects {
    /// Components whose old values determine the successor.
    pub reads: Vec<StateComponent>,
    /// Components that may differ after success or a declared trap.
    pub writes: Vec<StateComponent>,
}

impl Instruction {
    /// Returns the complete dynamic architectural footprint in `state`.
    ///
    /// Memory operands name the wrapped effective address and word-sized byte
    /// count even when the later range check traps.
    #[must_use]
    pub fn effects(self, state: &State) -> Effects {
        use StateComponent::{Conditions, Memory, Outcome, ProgramCounter, Register};
        let mut reads = vec![ProgramCounter, Outcome];
        let mut writes = vec![ProgramCounter];
        let bytes = usize::from(state.width / 8);
        match self {
            Self::Mov { rd, rs1 } => {
                reads.push(Register(rs1));
                writes.push(Register(rd));
            }
            Self::MovImmediate { rd, .. } => writes.push(Register(rd)),
            Self::Load { rd, base, offset } => {
                let address =
                    state.registers[usize::from(base)].wrapping_add_signed(i128::from(offset));
                reads.extend([Register(base), Memory { address, bytes }]);
                writes.extend([Register(rd), Outcome]);
            }
            Self::Store {
                base,
                source,
                offset,
            } => {
                let address =
                    state.registers[usize::from(base)].wrapping_add_signed(i128::from(offset));
                reads.extend([Register(base), Register(source)]);
                writes.extend([Memory { address, bytes }, Outcome]);
            }
            Self::Add { rd, rs1, rs2 }
            | Self::Sub { rd, rs1, rs2 }
            | Self::And { rd, rs1, rs2 }
            | Self::Or { rd, rs1, rs2 }
            | Self::Xor { rd, rs1, rs2 }
            | Self::ShiftLeft { rd, rs1, rs2 }
            | Self::ShiftRight { rd, rs1, rs2 }
            | Self::ArithmeticShiftRight { rd, rs1, rs2 } => {
                reads.extend([Register(rs1), Register(rs2)]);
                writes.extend([Register(rd), Conditions]);
            }
            Self::Not { rd, rs1 } => {
                reads.push(Register(rs1));
                writes.extend([Register(rd), Conditions]);
            }
            Self::Compare { rs1, rs2 } => {
                reads.extend([Register(rs1), Register(rs2)]);
                writes.push(Conditions);
            }
            Self::Branch { .. } => reads.push(Conditions),
            Self::Jump { .. } => {}
            Self::Halt => {
                reads.clear();
                reads.push(Outcome);
                writes.clear();
                writes.push(Outcome);
            }
        }
        Effects {
            reads: unique_components(reads),
            writes: unique_components(writes),
        }
    }
}

fn unique_components(components: Vec<StateComponent>) -> Vec<StateComponent> {
    let mut unique = Vec::with_capacity(components.len());
    for component in components {
        if !unique.contains(&component) {
            unique.push(component);
        }
    }
    unique
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

    const fn encoding(self) -> u8 {
        match self {
            Self::Eq => 0,
            Self::Ne => 1,
            Self::Lt => 2,
            Self::Ge => 3,
            Self::Lo => 4,
            Self::Hs => 5,
            Self::Hi => 6,
            Self::Ls => 7,
        }
    }
}

/// Encodes one structured A0 instruction in its unique four-byte form.
///
/// # Errors
///
/// Returns [`A0Error::InvalidRegister`] when a register field is outside
/// A0's range `r0` through `r7`.
pub fn encode(instruction: Instruction) -> Result<[u8; 4], A0Error> {
    let pair = |rd: u8, rs1: u8| -> Result<u8, A0Error> {
        validate_register(rd)?;
        validate_register(rs1)?;
        Ok(rd | (rs1 << 3))
    };
    let triple = |rd: u8, rs1: u8, rs2: u8| -> Result<(u8, u8), A0Error> {
        validate_register(rs2)?;
        Ok((pair(rd, rs1)?, rs2))
    };
    let bytes = match instruction {
        Instruction::Mov { rd, rs1 } => [0x00, pair(rd, rs1)?, 0, 0],
        Instruction::MovImmediate { rd, immediate } => {
            validate_register(rd)?;
            [0x01, rd, 0, immediate.cast_unsigned()]
        }
        Instruction::Load { rd, base, offset } => {
            [0x02, pair(rd, base)?, 0, offset.cast_unsigned()]
        }
        Instruction::Store {
            base,
            source,
            offset,
        } => {
            validate_register(base)?;
            validate_register(source)?;
            [0x03, base << 3, source, offset.cast_unsigned()]
        }
        Instruction::Add { rd, rs1, rs2 } => encode_three(0x10, triple(rd, rs1, rs2)?),
        Instruction::Sub { rd, rs1, rs2 } => encode_three(0x11, triple(rd, rs1, rs2)?),
        Instruction::And { rd, rs1, rs2 } => encode_three(0x12, triple(rd, rs1, rs2)?),
        Instruction::Or { rd, rs1, rs2 } => encode_three(0x13, triple(rd, rs1, rs2)?),
        Instruction::Xor { rd, rs1, rs2 } => encode_three(0x14, triple(rd, rs1, rs2)?),
        Instruction::Not { rd, rs1 } => [0x15, pair(rd, rs1)?, 0, 0],
        Instruction::ShiftLeft { rd, rs1, rs2 } => encode_three(0x18, triple(rd, rs1, rs2)?),
        Instruction::ShiftRight { rd, rs1, rs2 } => encode_three(0x19, triple(rd, rs1, rs2)?),
        Instruction::ArithmeticShiftRight { rd, rs1, rs2 } => {
            encode_three(0x1a, triple(rd, rs1, rs2)?)
        }
        Instruction::Compare { rs1, rs2 } => {
            validate_register(rs1)?;
            validate_register(rs2)?;
            [0x20, rs1 << 3, rs2, 0]
        }
        Instruction::Branch { condition, offset } => {
            [0x30, 0, condition.encoding() << 3, offset.cast_unsigned()]
        }
        Instruction::Jump { offset } => [0x31, 0, 0, offset.cast_unsigned()],
        Instruction::Halt => [0xff, 0, 0, 0],
    };
    Ok(bytes)
}

const fn encode_three(opcode: u8, fields: (u8, u8)) -> [u8; 4] {
    [opcode, fields.0, fields.1, 0]
}

const fn validate_register(register: u8) -> Result<(), A0Error> {
    if register < 8 {
        Ok(())
    } else {
        Err(A0Error::InvalidRegister(register))
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
        Instruction::Halt => {
            next.pc = state.pc;
            next.outcome = Outcome::Halted;
        }
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
    struct ConcreteAddition;

    impl AdditionDomain for ConcreteAddition {
        type Word = Word;
        type Bit = bool;

        fn sum(&mut self, lhs: Word, rhs: Word) -> Word {
            lhs.wrapping_add(rhs)
        }

        fn is_zero(&mut self, word: Word) -> bool {
            word.unsigned() == 0
        }

        fn high_bit(&mut self, word: Word) -> bool {
            word.high_bit()
        }

        fn carry(&mut self, lhs: Word, rhs: Word, _sum: Word) -> bool {
            let full = u128::from(lhs.unsigned()) + u128::from(rhs.unsigned());
            full >= (1_u128 << lhs.width())
        }

        fn overflow(&mut self, lhs: Word, rhs: Word, sum: Word) -> bool {
            lhs.high_bit() == rhs.high_bit() && sum.high_bit() != lhs.high_bit()
        }
    }

    let result = addition(&mut ConcreteAddition, lhs, rhs);
    (
        result.result,
        Conditions {
            zero: result.zero,
            negative: result.negative,
            carry: result.carry,
            overflow: result.overflow,
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
    PrefixReturned,
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
    run_with_running_stop(program, initial, max_steps, StopReason::BoundExhausted)
}

/// Executes a caller-requested prefix without claiming that a running machine
/// exhausted a semantic or verification bound.
///
/// Terminal states reached within `requested_steps` are still classified as
/// halted or trapped. A running final state is classified as
/// [`StopReason::PrefixReturned`].
#[must_use]
pub fn run_prefix(program: &Program, initial: State, requested_steps: usize) -> Trace {
    run_with_running_stop(
        program,
        initial,
        requested_steps,
        StopReason::PrefixReturned,
    )
}

fn run_with_running_stop(
    program: &Program,
    initial: State,
    steps: usize,
    running_stop: StopReason,
) -> Trace {
    debug_assert!(matches!(
        running_stop,
        StopReason::BoundExhausted | StopReason::PrefixReturned
    ));
    let mut current = initial;
    let mut states = vec![current.clone()];
    for _ in 0..steps {
        if current.outcome != Outcome::Running {
            break;
        }
        current = step(program, &current);
        states.push(current.clone());
    }
    let stop = match &current.outcome {
        Outcome::Halted => StopReason::Halted,
        Outcome::Trapped(_) => StopReason::Trapped,
        Outcome::Running => running_stop,
    };
    Trace { states, stop }
}

/// Construction or decoding failure outside machine execution.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A0Error {
    /// Width is not 8, 16, ..., or 64.
    InvalidWordWidth(u8),
    /// A widening operation was asked to narrow, or truncation to widen.
    InvalidWidthConversion { from: u8, to: u8 },
    /// A complete state contains a word of another architectural width.
    StateWidthMismatch {
        component: &'static str,
        expected: u8,
        actual: u8,
    },
    /// A state or its canonical binary encoding violates the format contract.
    InvalidStateEncoding(&'static str),
    /// A finite memory map names the same address twice.
    DuplicateMemoryAddress(u64),
    /// A finite memory address does not fit the state's architectural width.
    InvalidMemoryAddress { width: u8, address: u64 },
    /// Two values that must share a width do not.
    WidthMismatch { expected: u8, actual: u8 },
    /// An encoder input named a register outside r0 through r7.
    InvalidRegister(u8),
    /// Reserved or unused encoding fields were nonzero, or opcode was unknown.
    IllegalEncoding([u8; 4]),
}

impl fmt::Display for A0Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWordWidth(width) => write!(
                formatter,
                "invalid A0 word width {width}; expected 8, 16, ..., or 64"
            ),
            Self::InvalidWidthConversion { from, to } => {
                write!(formatter, "invalid width conversion from {from} to {to}")
            }
            Self::StateWidthMismatch {
                component,
                expected,
                actual,
            } => write!(
                formatter,
                "state component {component} has width {actual}; expected {expected}"
            ),
            Self::InvalidStateEncoding(reason) => {
                write!(formatter, "invalid A0 state encoding: {reason}")
            }
            Self::DuplicateMemoryAddress(address) => {
                write!(formatter, "duplicate A0 memory address {address}")
            }
            Self::InvalidMemoryAddress { width, address } => write!(
                formatter,
                "A0 memory address {address} does not fit width {width}"
            ),
            Self::WidthMismatch { expected, actual } => {
                write!(
                    formatter,
                    "width mismatch: expected {expected}, got {actual}"
                )
            }
            Self::InvalidRegister(register) => {
                write!(
                    formatter,
                    "invalid A0 register r{register}; expected r0 through r7"
                )
            }
            Self::IllegalEncoding(bytes) => {
                write!(formatter, "illegal A0 encoding {bytes:02x?}")
            }
        }
    }
}

impl std::error::Error for A0Error {}

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
