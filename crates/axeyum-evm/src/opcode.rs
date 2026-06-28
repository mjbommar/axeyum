//! EVM opcode constants and a thin bytecode decoder for the Phase-1 subset.
//!
//! Only the opcodes the symbolic + concrete interpreters implement are named;
//! every other byte decodes to [`Op::Unsupported`] so the interpreters can treat
//! it as a sound "give up this path / havoc" point rather than mis-execute it.

/// A decoded EVM instruction: the program-counter offset, the opcode byte, and —
/// for the `PUSH1..=PUSH32` family — the immediate big-endian bytes that follow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    /// Byte offset of this opcode in the bytecode.
    pub pc: usize,
    /// The opcode.
    pub op: Op,
    /// For `PUSH*`, the immediate bytes (big-endian, `1..=32` long); empty
    /// otherwise.
    pub immediate: Vec<u8>,
}

/// The Phase-1 supported opcode set, plus a catch-all for anything else (treated
/// as a path-terminating havoc/unsupported point — never silently mis-executed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    // --- 0x00 range: stop & arithmetic ---
    /// `STOP` (0x00): halt execution.
    Stop,
    /// `ADD` (0x01): `a + b` mod 2^256.
    Add,
    /// `MUL` (0x02): `a * b` mod 2^256.
    Mul,
    /// `SUB` (0x03): `a - b` mod 2^256.
    Sub,
    /// `DIV` (0x04): unsigned division (`b == 0` ⇒ 0).
    Div,
    /// `SDIV` (0x05): signed division (`b == 0` ⇒ 0).
    Sdiv,
    /// `MOD` (0x06): unsigned remainder (`b == 0` ⇒ 0).
    Mod,
    /// `SMOD` (0x07): signed remainder (`b == 0` ⇒ 0).
    Smod,
    /// `ADDMOD` (0x08): `(a + b) % n` at 512-bit precision (`n == 0` ⇒ 0).
    Addmod,
    /// `MULMOD` (0x09): `(a * b) % n` at 512-bit precision (`n == 0` ⇒ 0).
    Mulmod,
    // --- 0x10 range: comparison & bitwise ---
    /// `LT` (0x10): unsigned less-than.
    Lt,
    /// `GT` (0x11): unsigned greater-than.
    Gt,
    /// `SLT` (0x12): signed less-than.
    Slt,
    /// `SGT` (0x13): signed greater-than.
    Sgt,
    /// `EQ` (0x14): equality.
    Eq,
    /// `ISZERO` (0x15): is the top word zero.
    IsZero,
    /// `AND` (0x16): bitwise and.
    And,
    /// `OR` (0x17): bitwise or.
    Or,
    /// `XOR` (0x18): bitwise xor.
    Xor,
    /// `NOT` (0x19): bitwise complement.
    Not,
    /// `BYTE` (0x1a): the `i`-th most-significant byte of a word.
    Byte,
    /// `SHL` (0x1b): logical left shift.
    Shl,
    /// `SHR` (0x1c): logical right shift.
    Shr,
    /// `SAR` (0x1d): arithmetic (sign-propagating) right shift.
    Sar,
    // --- 0x20 range: hashing ---
    /// `KECCAK256` / `SHA3` (0x20): `keccak256(memory[offset:offset+length])`.
    Sha3,
    // --- 0x30 range: environment (calldata / value / caller) ---
    /// `CALLVALUE` (0x34): the wei sent with the call.
    CallValue,
    /// `CALLDATALOAD` (0x35): load a 32-byte word of calldata at an offset.
    CallDataLoad,
    /// `CALLDATASIZE` (0x36): the byte length of the calldata.
    CallDataSize,
    /// `CALLER` (0x33): the immediate caller address.
    Caller,
    // --- 0x50 range: stack, memory, storage, flow ---
    /// `POP` (0x50): discard the top of stack.
    Pop,
    /// `MLOAD` (0x51): load a 32-byte word from memory.
    Mload,
    /// `MSTORE` (0x52): store a 32-byte word to memory.
    Mstore,
    /// `MSTORE8` (0x53): store the low byte of a word to memory.
    Mstore8,
    /// `SLOAD` (0x54): load a word from storage.
    Sload,
    /// `SSTORE` (0x55): store a word to storage.
    Sstore,
    /// `JUMP` (0x56): unconditional jump to a `JUMPDEST`.
    Jump,
    /// `JUMPI` (0x57): conditional jump to a `JUMPDEST`.
    Jumpi,
    /// `PC` (0x58): the current program counter.
    Pc,
    /// `JUMPDEST` (0x5b): a valid jump target (no-op).
    Jumpdest,
    // --- 0x60..0x9f: push / dup / swap (n = 1..=32 / 1..=16) ---
    /// `PUSH1..=PUSH32`: the `n` payload (number of immediate bytes, `1..=32`).
    Push(u8),
    /// `DUP1..=DUP16`: the 1-based stack depth duplicated.
    Dup(u8),
    /// `SWAP1..=SWAP16`: the 1-based stack depth swapped with the top.
    Swap(u8),
    // --- 0xf0 range: halting ---
    /// `RETURN` (0xf3): halt and return memory bytes.
    Return,
    /// `REVERT` (0xfd): halt, revert state, return memory bytes (the
    /// assertion/`require`/`Panic` signal).
    Revert,
    /// `INVALID` (0xfe): the designated invalid opcode (legacy assert failure).
    Invalid,
    /// An *environment / context* opcode that pops `pops` stack args and pushes
    /// one nondeterministic value the contract has no control over: `GAS`,
    /// `BALANCE`, `EXTCODESIZE`/`EXTCODEHASH`, `RETURNDATASIZE`, and block/tx
    /// context (`TIMESTAMP`/`NUMBER`/`GASPRICE`/`COINBASE`/…). Modeled as a
    /// **witnessed symbolic input** (fresh symbol symbolically; replayed from the
    /// witness concretely) so paths explore past it soundly instead of halting.
    Env(u8),
    /// Any opcode outside the Phase-1 subset (KECCAK256, CALL, LOG*, …).
    /// Carries the raw byte so the interpreter can decide to havoc or stop.
    Unsupported(u8),
}

impl Op {
    /// Decodes a single opcode byte (not the PUSH immediate, which the decoder
    /// handles separately).
    #[must_use]
    pub fn from_byte(byte: u8) -> Op {
        match byte {
            0x00 => Op::Stop,
            0x01 => Op::Add,
            0x02 => Op::Mul,
            0x03 => Op::Sub,
            0x04 => Op::Div,
            0x05 => Op::Sdiv,
            0x06 => Op::Mod,
            0x07 => Op::Smod,
            0x08 => Op::Addmod,
            0x09 => Op::Mulmod,
            0x10 => Op::Lt,
            0x11 => Op::Gt,
            0x12 => Op::Slt,
            0x13 => Op::Sgt,
            0x14 => Op::Eq,
            0x15 => Op::IsZero,
            0x16 => Op::And,
            0x17 => Op::Or,
            0x18 => Op::Xor,
            0x19 => Op::Not,
            0x1a => Op::Byte,
            0x1b => Op::Shl,
            0x1c => Op::Shr,
            0x1d => Op::Sar,
            0x20 => Op::Sha3,
            0x34 => Op::CallValue,
            0x35 => Op::CallDataLoad,
            0x36 => Op::CallDataSize,
            0x33 => Op::Caller,
            0x50 => Op::Pop,
            0x51 => Op::Mload,
            0x52 => Op::Mstore,
            0x53 => Op::Mstore8,
            0x54 => Op::Sload,
            0x55 => Op::Sstore,
            0x56 => Op::Jump,
            0x57 => Op::Jumpi,
            0x58 => Op::Pc,
            0x5b => Op::Jumpdest,
            // Environment / context opcodes: pop their address arg(s), push one
            // nondeterministic value (modeled as a witnessed symbolic input).
            0x30 | 0x32 | 0x3a | 0x3d | 0x41..=0x48 | 0x5a => Op::Env(0),
            0x31 | 0x3b | 0x3f => Op::Env(1),
            0x60..=0x7f => Op::Push(byte - 0x5f),
            0x80..=0x8f => Op::Dup(byte - 0x7f),
            0x90..=0x9f => Op::Swap(byte - 0x8f),
            0xf3 => Op::Return,
            0xfd => Op::Revert,
            0xfe => Op::Invalid,
            other => Op::Unsupported(other),
        }
    }
}

/// Decodes the whole bytecode into a `pc -> Instruction` map (a flat `Vec`
/// indexed implicitly; lookups are via [`decode`]'s returned vector scanned by
/// the interpreter). Returns the instruction stream in program order with PUSH
/// immediates attached, plus the set of valid `JUMPDEST` byte offsets.
///
/// PUSH immediates that run off the end of the bytecode are zero-padded on the
/// right (EVM semantics).
#[must_use]
pub fn decode(bytecode: &[u8]) -> Program {
    let mut instructions = Vec::new();
    let mut pc_to_index = vec![usize::MAX; bytecode.len() + 1];
    let mut jumpdests = std::collections::BTreeSet::new();
    let mut pc = 0usize;
    while pc < bytecode.len() {
        let op = Op::from_byte(bytecode[pc]);
        let index = instructions.len();
        pc_to_index[pc] = index;
        let mut immediate = Vec::new();
        let mut next = pc + 1;
        if let Op::Push(n) = op {
            let n = n as usize;
            for i in 0..n {
                immediate.push(bytecode.get(pc + 1 + i).copied().unwrap_or(0));
            }
            next = pc + 1 + n;
        }
        if op == Op::Jumpdest {
            jumpdests.insert(pc);
        }
        instructions.push(Instruction { pc, op, immediate });
        pc = next;
    }
    Program {
        instructions,
        pc_to_index,
        jumpdests,
    }
}

/// A decoded program: the instruction stream and a `JUMPDEST`-validity oracle.
#[derive(Debug, Clone)]
pub struct Program {
    /// Instructions in program order.
    pub instructions: Vec<Instruction>,
    /// `pc_to_index[pc]` = index into `instructions` of the op starting at `pc`,
    /// or `usize::MAX` if no instruction starts there (e.g. a PUSH immediate
    /// byte). Length is `bytecode.len() + 1`.
    pub pc_to_index: Vec<usize>,
    /// Byte offsets that hold a `JUMPDEST` — the only legal jump targets.
    pub jumpdests: std::collections::BTreeSet<usize>,
}

impl Program {
    /// The instruction index for a program-counter byte offset, if one begins
    /// exactly there.
    #[must_use]
    pub fn index_at(&self, pc: usize) -> Option<usize> {
        let idx = *self.pc_to_index.get(pc)?;
        (idx != usize::MAX).then_some(idx)
    }

    /// Whether `pc` is a valid `JUMPDEST`.
    #[must_use]
    pub fn is_jumpdest(&self, pc: usize) -> bool {
        self.jumpdests.contains(&pc)
    }
}
