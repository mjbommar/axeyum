//! The symbolic EVM interpreter + `SymbolicExecutor` DFS driver.
//!
//! Each opcode is lowered to `BV256` IR terms over an [`axeyum_ir::TermArena`];
//! calldata is a symbolic byte buffer, memory is a concrete-offset byte map of
//! IR terms, storage is a concrete-key word map. At every `JUMPI` we ask the
//! [`SymbolicExecutor`] which directions are feasible and explore them
//! depth-first. A bug is a path-feasible `REVERT` / `INVALID` / `Panic(0x11)`, or
//! a path-feasible `bv_uaddo` / `bv_umulo` overflow on a tracked arithmetic op.
//!
//! Soundness caveats encoded here (frontend concerns, not solver bugs):
//! * EVM `DIV`/`MOD`/`SDIV`/`SMOD`-by-0 = 0 via an `ite` guard (NOT SMT-LIB
//!   all-ones).
//! * `ADDMOD`/`MULMOD` evaluated at 512 bits then truncated.
//! * Environment opcodes (`GAS`/`BALANCE`/block-context/…) are **witnessed
//!   symbolic inputs** (`Op::Env`): a fresh symbol symbolically, replayed from the
//!   witness concretely, so paths explore past them soundly.
//! * CALL / LOG / other unsupported opcodes → conservative path `Unknown`
//!   (never wrong-pruned).
//! * Symbolic jump offsets that are not concretely resolvable terminate the
//!   path as `Unknown` (never silently mis-stepped).
//!
//! ## Phase 2 — symbolic-offset memory / storage (read-over-write at the frontend)
//!
//! Symbolic `SLOAD`/`SSTORE` keys and symbolic `MSTORE`/`MLOAD` offsets are no
//! longer havoc'd. Storage and (word-granular) memory carry an **ordered write
//! list**: a `store(k, v)` appends `(k, v)`; a `load(k)` folds
//! `ite(k == kᵢ, vᵢ, prev)` from newest to oldest write, ending in the base
//! value. This is read-over-write done in the frontend — it emits **pure `QF_BV`**
//! (`eq` / `ite` only), so the warm incremental `SymbolicExecutor` reasons about
//! it directly (the executor's bit-blast path refuses `select`/`store` array
//! terms; the ite-fold sidesteps that while giving the same semantics, last-write
//! -wins by key equality, exactly mirroring the concrete `BTreeMap` oracle).
//! Concrete-key/offset fast-paths are retained.
//!
//! ## Phase 2 — keccak with injectivity constraints
//!
//! `KECCAK256` (`SHA3`, 0x20) over a concrete-length byte span is modeled with a
//! **fresh symbolic `BV256`** result (not an uninterpreted `apply`, which the
//! warm bit-blaster cannot encode). For every pair of same-width keccak
//! applications on a path we assert the injectivity lemma
//! `argᵢ == argⱼ ⇔ resultᵢ == resultⱼ` — pure `QF_BV` `eq` over the fresh symbols
//! (the halmos/hevm precision trick expressed in the warm fragment) — so
//! mapping-style storage keyed by `keccak(slot . key)` is *decided* by key
//! (dis)equality, not havoc'd. The concrete oracle uses *real* keccak256 (so a
//! witness whose bug hinges on an invented hash value, not key equality, simply
//! does not reproduce and is not reported).

use std::collections::BTreeMap;

use axeyum_ir::{SymbolId, TermArena, TermId};
use axeyum_solver::{PathStatus, SymbolicExecutor, SymbolicMemory};
use axeyum_solver::{SolverConfig, SolverError};

use crate::MemoryEncoding;
use crate::opcode::{Op, Program};

/// Word width for the symbolic machine (EVM 256-bit).
const W: u32 = 256;
/// Bound on how many `CALLDATALOAD` / `CALLDATASIZE` care about; calldata symbols
/// past this are still fresh but unconstrained.
const MAX_CALLDATA_BYTES: usize = 256;
/// Largest keccak preimage (in bytes) we model symbolically. The dominant
/// mapping-storage pattern hashes a 32-byte slot or a 64-byte `(key . slot)`
/// pair; longer preimages are havoc'd to a sound `Unknown`.
const MAX_KECCAK_BYTES: usize = 128;

/// The kind of bug a path can witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BugKind {
    /// A reachable `REVERT` (includes Solidity `require`/`assert` failures and the
    /// `Panic(0x11)` checked-arithmetic revert).
    Revert,
    /// A reachable `INVALID` opcode (`0xfe`).
    Invalid,
    /// A reachable unsigned addition overflow on a tracked `ADD`.
    AddOverflow,
    /// A reachable unsigned multiplication overflow on a tracked `MUL`.
    MulOverflow,
}

/// The concrete inputs of one transaction in a witnessing sequence.
#[derive(Debug, Clone)]
pub struct TxWitness {
    /// The concrete calldata for this transaction.
    pub calldata: Vec<u8>,
    /// The concrete `CALLVALUE` for this transaction.
    pub callvalue: crate::word::Word,
    /// The concrete `CALLER` for this transaction.
    pub caller: crate::word::Word,
}

/// A bug witnessed on some feasible path, with a lifted concrete witness.
#[derive(Debug, Clone)]
pub struct PathBug {
    /// What kind of bug.
    pub kind: BugKind,
    /// The byte offset (pc) where the bug was witnessed.
    pub pc: usize,
    /// The concrete calldata driving the **bug's** transaction to the bug.
    pub calldata: Vec<u8>,
    /// The concrete `CALLVALUE` of the bug's transaction.
    pub callvalue: crate::word::Word,
    /// The concrete `CALLER` of the bug's transaction.
    pub caller: crate::word::Word,
    /// Inputs for the transactions *preceding* the bug's transaction (empty for a
    /// single-tx bug). Replayed in order, with storage persisting, before the
    /// bug's transaction — the multi-tx revalidation sequence.
    pub prior_txs: Vec<TxWitness>,
    /// Concrete values for the environment opcodes (`Op::Env`) on the path, in
    /// execution order — replayed by the concrete oracle so a bug that branches on
    /// `gas()`/context reproduces deterministically.
    pub env_inputs: Vec<crate::word::Word>,
}

/// Outcome of exploring the program.
pub struct Exploration {
    /// The first bug found, with a lifted concrete witness (Phase-1 reports the
    /// first feasible bug).
    pub bug: Option<PathBug>,
    /// Whether any path ended in `Unknown` (havoc/limit) — the result is not a
    /// sound "no bug" proof when this is set on the explored sub-tree.
    pub saw_unknown: bool,
    /// The real bug-reachability obligations the explorer **refuted** (each is a
    /// term `pathᵢ ∧ bug_predicateᵢ` the solver found infeasible). On a clean
    /// no-bug run their disjunction is the actual "no bad state is reachable up
    /// to the bound" formula — UNSAT — which becomes the `SafeUpToBound` proof
    /// (item #3), replacing the Phase-1 `0==1` placeholder. Carried with the
    /// arena they live in.
    pub refuted_obligations: RefutedSafety,
}

/// The refuted bug-reachability obligations plus the arena they were built in,
/// so the caller can hand them to `produce_evidence` as the real safety proof.
pub struct RefutedSafety {
    /// The arena holding the obligation terms.
    pub arena: TermArena,
    /// Each refuted `pathᵢ ∧ bug_predicateᵢ` term (proved infeasible).
    pub obligations: Vec<TermId>,
}

/// A symbolic store record `array[key] = value` (key/value are 256-bit IR
/// terms). Reads fold over these newest-first.
#[derive(Clone)]
struct Write {
    key: TermId,
    value: TermId,
}

/// The symbolic machine state along one path.
#[derive(Clone)]
struct State {
    stack: Vec<TermId>,
    /// Concrete-offset memory: byte offset -> an 8-bit IR term (the fast path,
    /// used whenever every offset on the path is a syntactic constant).
    memory: BTreeMap<usize, TermId>,
    /// Word-granular memory writes at *symbolic* offsets (read-over-write list,
    /// key = byte offset as a 256-bit word, value = the stored 256-bit word).
    /// Populated only once a symbolic `MSTORE` offset is seen; `MLOAD` then folds
    /// these over the concrete `memory` base.
    sym_memory: Vec<Write>,
    /// Concrete-key storage: 256-bit key bytes -> a 256-bit IR term (fast path).
    storage: BTreeMap<[u8; 32], TermId>,
    /// Symbolic-key storage writes (read-over-write list); a symbolic `SSTORE`
    /// appends here and an `SLOAD` folds these over the concrete `storage` base.
    sym_storage: Vec<Write>,
    /// `keccak(arg)` applications observed on this path: `(arg_term, byte_len,
    /// result_term)`. Used to emit pairwise injectivity constraints when a hash
    /// participates in a feasibility query.
    keccak_apps: Vec<KeccakApp>,
    /// How storage reads/writes are lowered on this path.
    encoding: MemoryEncoding,
    /// The warm SMT-array storage state, used only under
    /// [`MemoryEncoding::WarmArray`]. Lazily created (as `const_array(0)`) on the
    /// first symbolic storage access so the `IteFold` path allocates nothing.
    storage_array: Option<SymbolicMemory>,
    /// The current transaction index (0-based) on this path. Advanced on a normal
    /// halt when more transactions remain; selects which `TxVars` calldata reads.
    tx: usize,
    /// Environment-input symbols consumed on this path, in execution order (one
    /// per `Op::Env`). Lifted into the witness so the concrete oracle replays the
    /// same nondeterministic values. Persists across tx boundaries (whole-path
    /// order).
    env_syms: Vec<SymbolId>,
}

/// A keccak application observed on a path.
#[derive(Clone)]
struct KeccakApp {
    /// The concatenated argument bytes as one `BV(8 * len)` term.
    arg: TermId,
    /// The argument byte length (selects which `keccak_n` was applied).
    len: usize,
    /// The `BV256` hash result.
    result: TermId,
}

impl State {
    fn new(encoding: MemoryEncoding) -> Self {
        State {
            stack: Vec::new(),
            memory: BTreeMap::new(),
            sym_memory: Vec::new(),
            storage: BTreeMap::new(),
            sym_storage: Vec::new(),
            keccak_apps: Vec::new(),
            encoding,
            storage_array: None,
            tx: 0,
            env_syms: Vec::new(),
        }
    }

    /// The warm storage array, created on first use as `const_array(0)` (EVM cold
    /// slots read zero). Only called under [`MemoryEncoding::WarmArray`].
    fn storage_mem(&mut self, arena: &mut TermArena) -> Result<SymbolicMemory, SolverError> {
        if let Some(mem) = self.storage_array {
            return Ok(mem);
        }
        let zero = arena.bv_const(W, 0)?;
        let base = arena.const_array(W, zero)?;
        let mem = SymbolicMemory::from_array(arena, base)?;
        self.storage_array = Some(mem);
        Ok(mem)
    }

    /// `SLOAD(key)` lowered per the active encoding (warm `select` vs `ite`-fold).
    fn storage_load(&mut self, arena: &mut TermArena, key: TermId) -> Result<TermId, SolverError> {
        match self.encoding {
            MemoryEncoding::WarmArray => {
                let mem = self.storage_mem(arena)?;
                mem.load(arena, key)
            }
            MemoryEncoding::IteFold => {
                let base = storage_base(arena, self, key)?;
                fold_word_writes(arena, &self.sym_storage, key, base)
            }
        }
    }

    /// `SSTORE(key, value)` recorded per the active encoding.
    fn storage_store(
        &mut self,
        arena: &mut TermArena,
        key: TermId,
        value: TermId,
    ) -> Result<(), SolverError> {
        // The concrete fast-path map is maintained in both encodings (it also
        // feeds keccak preimage byte reads); it is harmless when unused.
        if let Some(k) = concrete_bytes(arena, key) {
            self.storage.insert(k, value);
        }
        match self.encoding {
            MemoryEncoding::WarmArray => {
                let mut mem = self.storage_mem(arena)?;
                mem.store(arena, key, value)?;
                self.storage_array = Some(mem);
            }
            // A later symbolic read must see this write even when the key is
            // concrete (it may alias a symbolic key), so record it on the list.
            MemoryEncoding::IteFold => self.sym_storage.push(Write { key, value }),
        }
        Ok(())
    }
}

/// The symbolic inputs of one transaction (calldata bytes, msg.value, sender).
/// Each external call in a multi-tx sequence gets its own independent set.
struct TxVars {
    /// One 8-bit symbol per calldata byte index.
    calldata_bytes: Vec<TermId>,
    calldata_syms: Vec<SymbolId>,
    callvalue: TermId,
    callvalue_sym: SymbolId,
    caller: TermId,
    caller_sym: SymbolId,
}

/// Reusable symbolic environment (declared once, shared across all paths).
struct SymEnv {
    /// Per-transaction input variables, index = transaction number. Index 0 uses
    /// the unprefixed names (`calldata[i]`/`callvalue`/`caller`) so single-tx
    /// behavior is byte-identical; tx `k>0` uses `tx{k}.`-prefixed names.
    txs: Vec<TxVars>,
    /// Monotonic counter for fresh havoc symbols.
    havoc_counter: u64,
    /// Monotonic counter for fresh environment-input symbols.
    env_counter: u64,
}

/// Symbolically explores `program`, returning the first feasible bug (if any).
///
/// # Errors
///
/// Propagates a genuine [`SolverError`] from the executor (not feasibility
/// `Unknown`, which is handled in-band).
pub fn explore(
    program: &Program,
    config: &SolverConfig,
    max_steps: usize,
    track_overflow: bool,
    encoding: MemoryEncoding,
    max_txs: usize,
) -> Result<Exploration, SolverError> {
    let mut arena = TermArena::new();
    let mut env = build_env(&mut arena, max_txs)?;
    let mut exec = SymbolicExecutor::with_config(config.clone());

    let mut saw_unknown = false;
    let mut obligations = Vec::new();
    let bug = walk(
        program,
        &mut arena,
        &mut exec,
        &mut env,
        max_steps,
        track_overflow,
        encoding,
        max_txs.max(1),
        &mut saw_unknown,
        &mut obligations,
    )?;

    Ok(Exploration {
        bug,
        saw_unknown,
        refuted_obligations: RefutedSafety { arena, obligations },
    })
}

/// Declares the input variables of transaction `tx`. Transaction 0 uses the
/// unprefixed names so single-tx runs are byte-identical to before; `tx>0` uses a
/// `tx{tx}.` prefix so each external call has independent symbolic inputs.
fn declare_tx_vars(arena: &mut TermArena, tx: usize) -> Result<TxVars, SolverError> {
    let prefix = if tx == 0 {
        String::new()
    } else {
        format!("tx{tx}.")
    };
    let mut calldata_bytes = Vec::with_capacity(MAX_CALLDATA_BYTES);
    let mut calldata_syms = Vec::with_capacity(MAX_CALLDATA_BYTES);
    for i in 0..MAX_CALLDATA_BYTES {
        let sym = arena.declare(
            &format!("{prefix}calldata[{i}]"),
            axeyum_ir::Sort::BitVec(8),
        )?;
        calldata_syms.push(sym);
        calldata_bytes.push(arena.var(sym));
    }
    let callvalue_sym = arena.declare(&format!("{prefix}callvalue"), axeyum_ir::Sort::BitVec(W))?;
    let callvalue = arena.var(callvalue_sym);
    let caller_sym = arena.declare(&format!("{prefix}caller"), axeyum_ir::Sort::BitVec(W))?;
    let caller = arena.var(caller_sym);
    Ok(TxVars {
        calldata_bytes,
        calldata_syms,
        callvalue,
        callvalue_sym,
        caller,
        caller_sym,
    })
}

/// Declares the input variables for `max_txs` transactions up front (eager, so
/// per-tx access needs no `&mut` and every path agrees on each tx's variables).
fn build_env(arena: &mut TermArena, max_txs: usize) -> Result<SymEnv, SolverError> {
    let mut txs = Vec::with_capacity(max_txs.max(1));
    for tx in 0..max_txs.max(1) {
        txs.push(declare_tx_vars(arena, tx)?);
    }
    Ok(SymEnv {
        txs,
        havoc_counter: 0,
        env_counter: 0,
    })
}

impl SymEnv {
    /// The input variables of transaction `tx`.
    fn tx(&self, tx: usize) -> &TxVars {
        &self.txs[tx]
    }

    /// A fresh unconstrained 256-bit word (the havoc primitive).
    fn havoc(&mut self, arena: &mut TermArena) -> Result<TermId, SolverError> {
        let name = format!("havoc!{}", self.havoc_counter);
        self.havoc_counter += 1;
        let sym = arena.declare(&name, axeyum_ir::Sort::BitVec(W))?;
        Ok(arena.var(sym))
    }

    /// A fresh environment-input value plus its symbol, so the caller can record
    /// it for witness lifting and the concrete oracle can replay it in order.
    fn fresh_env(&mut self, arena: &mut TermArena) -> Result<(TermId, SymbolId), SolverError> {
        let name = format!("env!{}", self.env_counter);
        self.env_counter += 1;
        let sym = arena.declare(&name, axeyum_ir::Sort::BitVec(W))?;
        Ok((arena.var(sym), sym))
    }
}

/// Pops the top of stack or signals an underflow (a malformed path → Unknown).
fn pop(stack: &mut Vec<TermId>) -> Option<TermId> {
    stack.pop()
}

/// Depth-first exploration. Returns the first feasible bug found. Recurses at
/// `JUMPI` forks (and at tracked-overflow checks) within `enter`/`backtrack`
/// scopes so the path condition is correctly scoped.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn walk(
    program: &Program,
    arena: &mut TermArena,
    exec: &mut SymbolicExecutor,
    env: &mut SymEnv,
    max_steps: usize,
    track_overflow: bool,
    encoding: MemoryEncoding,
    max_txs: usize,
    saw_unknown: &mut bool,
    obligations: &mut Vec<TermId>,
) -> Result<Option<PathBug>, SolverError> {
    let mut state = State::new(encoding);
    run_from(
        program,
        arena,
        exec,
        env,
        &mut state,
        0,
        0,
        max_steps,
        track_overflow,
        max_txs,
        saw_unknown,
        obligations,
    )
}

/// Runs a single straight-line path from instruction index `idx` (pc-resolved),
/// forking recursively at `JUMPI`. `steps` counts executed ops against
/// `max_steps`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn run_from(
    program: &Program,
    arena: &mut TermArena,
    exec: &mut SymbolicExecutor,
    env: &mut SymEnv,
    state: &mut State,
    mut idx: usize,
    mut steps: usize,
    max_steps: usize,
    track_overflow: bool,
    max_txs: usize,
    saw_unknown: &mut bool,
    obligations: &mut Vec<TermId>,
) -> Result<Option<PathBug>, SolverError> {
    macro_rules! pop_or_unknown {
        () => {
            match pop(&mut state.stack) {
                Some(t) => t,
                None => {
                    *saw_unknown = true;
                    return Ok(None);
                }
            }
        };
    }

    loop {
        if steps >= max_steps {
            *saw_unknown = true;
            return Ok(None);
        }
        steps += 1;

        let Some(inst) = program.instructions.get(idx) else {
            // Fell off the instruction stream — implicit STOP.
            return Ok(None);
        };
        let pc = inst.pc;
        let op = inst.op;

        match op {
            Op::Stop | Op::Return => {
                // Normal end of the current transaction. If more transactions
                // remain in the sequence, begin the next one: EVM semantics clear
                // memory and the stack between external calls but **persist
                // storage**, and the next call gets fresh symbolic calldata.
                if state.tx + 1 < max_txs {
                    state.tx += 1;
                    state.stack.clear();
                    state.memory.clear();
                    state.sym_memory.clear();
                    idx = 0;
                    continue;
                }
                return Ok(None);
            }
            Op::Invalid => {
                // INVALID is reachable on this (feasible) path; lift a witness.
                if let Some(bug) = lift_witness(
                    arena,
                    exec,
                    env,
                    state.tx,
                    &state.env_syms,
                    BugKind::Invalid,
                    pc,
                )? {
                    return Ok(Some(bug));
                }
                *saw_unknown = true;
                return Ok(None);
            }
            Op::Revert => {
                if let Some(bug) = lift_witness(
                    arena,
                    exec,
                    env,
                    state.tx,
                    &state.env_syms,
                    BugKind::Revert,
                    pc,
                )? {
                    return Ok(Some(bug));
                }
                *saw_unknown = true;
                return Ok(None);
            }
            Op::Add => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                if track_overflow {
                    let ovf = arena.bv_uaddo(a, b)?;
                    if let Some(bug) = check_overflow(
                        arena,
                        exec,
                        env,
                        state.tx,
                        &state.env_syms,
                        ovf,
                        BugKind::AddOverflow,
                        pc,
                        saw_unknown,
                        obligations,
                    )? {
                        return Ok(Some(bug));
                    }
                }
                state.stack.push(arena.bv_add(a, b)?);
            }
            Op::Mul => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                if track_overflow {
                    let ovf = arena.bv_umulo(a, b)?;
                    if let Some(bug) = check_overflow(
                        arena,
                        exec,
                        env,
                        state.tx,
                        &state.env_syms,
                        ovf,
                        BugKind::MulOverflow,
                        pc,
                        saw_unknown,
                        obligations,
                    )? {
                        return Ok(Some(bug));
                    }
                }
                state.stack.push(arena.bv_mul(a, b)?);
            }
            Op::Sub => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state.stack.push(arena.bv_sub(a, b)?);
            }
            Op::Div => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state
                    .stack
                    .push(div_guard(arena, a, b, TermArena::bv_udiv)?);
            }
            Op::Sdiv => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state
                    .stack
                    .push(div_guard(arena, a, b, TermArena::bv_sdiv)?);
            }
            Op::Mod => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state
                    .stack
                    .push(div_guard(arena, a, b, TermArena::bv_urem)?);
            }
            Op::Smod => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state
                    .stack
                    .push(div_guard(arena, a, b, TermArena::bv_smod)?);
            }
            Op::Addmod => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let n = pop_or_unknown!();
                state.stack.push(mod_512(arena, a, b, n, false)?);
            }
            Op::Mulmod => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let n = pop_or_unknown!();
                state.stack.push(mod_512(arena, a, b, n, true)?);
            }
            Op::Lt => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let c = arena.bv_ult(a, b)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::Gt => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let c = arena.bv_ugt(a, b)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::Slt => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let c = arena.bv_slt(a, b)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::Sgt => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let c = arena.bv_sgt(a, b)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::Eq => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                let c = arena.eq(a, b)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::IsZero => {
                let a = pop_or_unknown!();
                let zero = arena.bv_const(W, 0)?;
                let c = arena.eq(a, zero)?;
                state.stack.push(bool_to_word(arena, c)?);
            }
            Op::And => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state.stack.push(arena.bv_and(a, b)?);
            }
            Op::Or => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state.stack.push(arena.bv_or(a, b)?);
            }
            Op::Xor => {
                let a = pop_or_unknown!();
                let b = pop_or_unknown!();
                state.stack.push(arena.bv_xor(a, b)?);
            }
            Op::Not => {
                let a = pop_or_unknown!();
                state.stack.push(arena.bv_not(a)?);
            }
            Op::Shl => {
                let shift = pop_or_unknown!();
                let value = pop_or_unknown!();
                state.stack.push(arena.bv_shl(value, shift)?);
            }
            Op::Shr => {
                let shift = pop_or_unknown!();
                let value = pop_or_unknown!();
                state.stack.push(arena.bv_lshr(value, shift)?);
            }
            Op::Sar => {
                let shift = pop_or_unknown!();
                let value = pop_or_unknown!();
                state.stack.push(arena.bv_ashr(value, shift)?);
            }
            Op::Byte => {
                // BYTE is rarely needed for the Phase-1 examples; havoc to stay
                // sound rather than mis-encode the endianness.
                let _i = pop_or_unknown!();
                let _x = pop_or_unknown!();
                let h = env.havoc(arena)?;
                state.stack.push(h);
                *saw_unknown = true;
            }
            Op::Sha3 => {
                let off = pop_or_unknown!();
                let len = pop_or_unknown!();
                // We need a concrete offset and length to gather the hashed bytes
                // (a symbolic-length hash is beyond this model → sound Unknown).
                let (Some(o), Some(l)) = (concrete_usize(arena, off), concrete_usize(arena, len))
                else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                if l == 0 || l > MAX_KECCAK_BYTES {
                    // Empty / oversized preimage: havoc to stay sound (the common
                    // mapping pattern hashes 32- or 64-byte slots).
                    let h = env.havoc(arena)?;
                    state.stack.push(h);
                    *saw_unknown = true;
                    return Ok(None);
                }
                let arg = gather_bytes(arena, state, o, l)?;
                // Model the hash result as a **fresh symbolic BV256** rather than
                // an uninterpreted `apply` (the warm executor cannot bit-blast
                // `Op::Apply`). Injectivity is then stated as pure `QF_BV` `eq`
                // constraints over these fresh symbols — the halmos trick expressed
                // entirely in the warm fragment, so feasibility/model queries work.
                let result = env.havoc(arena)?;
                let new_app = KeccakApp {
                    arg,
                    len: l,
                    result,
                };
                // Assert injectivity of this new hash against every prior
                // same-width hash on the path (`argᵢ == argⱼ ⇔ resultᵢ == resultⱼ`),
                // so the solver reasons about mapping keys by (dis)equality. These
                // are monotone facts; asserting them now keeps them live for all
                // downstream feasibility queries on this path.
                if let Some(lemma) = keccak_injectivity_pair(arena, &state.keccak_apps, &new_app)? {
                    let status = exec.assume_auto(arena, lemma)?;
                    if matches!(status, PathStatus::Unknown(_)) {
                        *saw_unknown = true;
                    }
                }
                state.keccak_apps.push(new_app);
                state.stack.push(result);
            }
            Op::CallValue => state.stack.push(env.tx(state.tx).callvalue),
            Op::Caller => state.stack.push(env.tx(state.tx).caller),
            Op::CallDataSize => {
                // We model exactly MAX_CALLDATA_BYTES of symbolic calldata.
                let size = arena.bv_const(W, MAX_CALLDATA_BYTES as u128)?;
                state.stack.push(size);
            }
            Op::CallDataLoad => {
                let off = pop_or_unknown!();
                let Some(o) = concrete_usize(arena, off) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                let word = calldata_word(arena, env, state.tx, o)?;
                state.stack.push(word);
            }
            Op::Pop => {
                let _ = pop_or_unknown!();
            }
            Op::Mload => {
                let off = pop_or_unknown!();
                let word = if let Some(o) = concrete_usize(arena, off) {
                    // Concrete-offset fast path: byte-granular over the base map,
                    // then any symbolic word-writes folded on top.
                    let base = mem_load(arena, state, o)?;
                    let off_word = arena.bv_const(W, o as u128)?;
                    fold_word_writes(arena, &state.sym_memory, off_word, base)?
                } else {
                    // Symbolic offset: a word-granular read-over-write fold. The
                    // byte-addressed `memory` base is conservatively read as 0
                    // (a symbolic offset that aliases a concrete byte write is
                    // outside this word-level model — see UPSTREAM-FEEDBACK).
                    let base = arena.bv_const(W, 0)?;
                    fold_word_writes(arena, &state.sym_memory, off, base)?
                };
                state.stack.push(word);
            }
            Op::Mstore => {
                let off = pop_or_unknown!();
                let val = pop_or_unknown!();
                if let Some(o) = concrete_usize(arena, off) {
                    mem_store(arena, state, o, val)?;
                    // A concrete store also shadows any earlier symbolic write to
                    // the same word offset (record it so a later symbolic read at
                    // an aliasing offset sees the newest value).
                    let off_word = arena.bv_const(W, o as u128)?;
                    state.sym_memory.push(Write {
                        key: off_word,
                        value: val,
                    });
                } else {
                    state.sym_memory.push(Write {
                        key: off,
                        value: val,
                    });
                }
            }
            Op::Mstore8 => {
                let off = pop_or_unknown!();
                let val = pop_or_unknown!();
                let Some(o) = concrete_usize(arena, off) else {
                    // A symbolic single-byte store is below our word granularity;
                    // stay honest rather than mis-model byte aliasing.
                    *saw_unknown = true;
                    return Ok(None);
                };
                let lo = arena.extract(7, 0, val)?;
                state.memory.insert(o, lo);
            }
            Op::Sload => {
                let key = pop_or_unknown!();
                let word = state.storage_load(arena, key)?;
                state.stack.push(word);
            }
            Op::Sstore => {
                let key = pop_or_unknown!();
                let val = pop_or_unknown!();
                state.storage_store(arena, key, val)?;
            }
            Op::Pc => {
                state.stack.push(arena.bv_const(W, pc as u128)?);
            }
            Op::Jumpdest => {}
            Op::Jump => {
                let dest = pop_or_unknown!();
                let Some(d) = concrete_usize(arena, dest) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                let Some(next) = program.index_at(d) else {
                    // Bad jump destination = an INVALID-style halt; not a tracked
                    // bug here (no JUMPDEST). Terminate the path.
                    return Ok(None);
                };
                if !program.is_jumpdest(d) {
                    return Ok(None);
                }
                idx = next;
                continue;
            }
            Op::Jumpi => {
                let dest = pop_or_unknown!();
                let cond = pop_or_unknown!();
                let Some(d) = concrete_usize(arena, dest) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                // cond != 0 takes the jump.
                let zero = arena.bv_const(W, 0)?;
                let taken = arena.eq(cond, zero)?;
                let taken = arena.not(taken)?; // cond != 0
                let branch = exec.branch(arena, taken)?;

                // Explore the taken (jump) direction if feasible/unknown.
                if !branch.if_true.is_infeasible() {
                    if matches!(branch.if_true, PathStatus::Unknown(_)) {
                        *saw_unknown = true;
                    }
                    if let Some(next) = program.index_at(d) {
                        if program.is_jumpdest(d) {
                            exec.enter()?;
                            let status = exec.assume_auto(arena, taken)?;
                            if !status.is_infeasible() {
                                let mut forked = state.clone();
                                let found = run_from(
                                    program,
                                    arena,
                                    exec,
                                    env,
                                    &mut forked,
                                    next,
                                    steps,
                                    max_steps,
                                    track_overflow,
                                    max_txs,
                                    saw_unknown,
                                    obligations,
                                )?;
                                if found.is_some() {
                                    exec.backtrack();
                                    return Ok(found);
                                }
                            }
                            exec.backtrack();
                        }
                    }
                }

                // Continue the fall-through (not-taken) direction in place.
                if branch.if_false.is_infeasible() {
                    return Ok(None);
                }
                if matches!(branch.if_false, PathStatus::Unknown(_)) {
                    *saw_unknown = true;
                }
                let not_taken = arena.not(taken)?;
                let status = exec.assume_auto(arena, not_taken)?;
                if status.is_infeasible() {
                    return Ok(None);
                }
                // fall through to next instruction
            }
            Op::Push(_) => {
                let word = push_word(arena, &inst.immediate);
                state.stack.push(word);
            }
            Op::Dup(n) => {
                let n = n as usize;
                if state.stack.len() < n {
                    *saw_unknown = true;
                    return Ok(None);
                }
                let t = state.stack[state.stack.len() - n];
                state.stack.push(t);
            }
            Op::Swap(n) => {
                let n = n as usize;
                if state.stack.len() < n + 1 {
                    *saw_unknown = true;
                    return Ok(None);
                }
                let len = state.stack.len();
                state.stack.swap(len - 1, len - 1 - n);
            }
            Op::Call(pops) => {
                // Pop the call args; the last one is the return-data length. Push a
                // nondeterministic success flag as a witnessed env input, and
                // continue. Return data is not modeled: if a nonzero (or symbolic)
                // amount is requested, flag the path Unknown so we never claim
                // safety we did not establish — but still explore for bugs that do
                // not depend on the returned bytes.
                let mut ret_len = None;
                for k in 0..pops {
                    let v = pop_or_unknown!();
                    if k + 1 == pops {
                        ret_len = Some(v);
                    }
                }
                if ret_len.is_none_or(|rl| concrete_usize(arena, rl) != Some(0)) {
                    *saw_unknown = true;
                }
                let (success, sym) = env.fresh_env(arena)?;
                state.env_syms.push(sym);
                state.stack.push(success);
            }
            Op::Env(pops) => {
                // Pop the (ignored) address arg(s), then push one nondeterministic
                // environment value as a *witnessed* symbolic input: a fresh symbol
                // recorded in path order so `lift_witness` can pin it and the
                // concrete oracle can replay the same value (keeping DISAGREE=0).
                for _ in 0..pops {
                    let _ = pop_or_unknown!();
                }
                let (value, sym) = env.fresh_env(arena)?;
                state.env_syms.push(sym);
                state.stack.push(value);
            }
            Op::Unsupported(_) => {
                // KECCAK / CALL / LOG / … : havoc and continue is unsound for
                // control flow, so we conservatively terminate the path as Unknown.
                *saw_unknown = true;
                return Ok(None);
            }
        }

        idx += 1;
    }
}

/// Lifts the current (committed, feasible) path's model into a concrete witness.
/// Returns `None` if no model is available (path turned out infeasible/unknown),
/// in which case the caller surfaces it as Unknown rather than a finding.
fn lift_witness(
    arena: &TermArena,
    exec: &mut SymbolicExecutor,
    env: &SymEnv,
    tx: usize,
    env_syms: &[SymbolId],
    kind: BugKind,
    pc: usize,
) -> Result<Option<PathBug>, SolverError> {
    let Some(model) = exec.model(arena)? else {
        return Ok(None);
    };
    let env_inputs: Vec<crate::word::Word> = env_syms
        .iter()
        .map(|&sym| {
            model
                .get(sym)
                .map_or_else(crate::word::Word::zero, |v| crate::value_to_word(&v))
        })
        .collect();
    // Lift the inputs of every transaction up to and including the bug's tx, so a
    // cross-tx bug carries the full replayable sequence (txs 0..tx are `prior_txs`,
    // tx is the bug's transaction). For a single-tx bug `prior_txs` is empty and
    // this is the original behavior.
    let lift_tx = |k: usize| -> TxWitness {
        let vars = env.tx(k);
        let mut calldata = vec![0u8; vars.calldata_syms.len()];
        for (i, &sym) in vars.calldata_syms.iter().enumerate() {
            if let Some(v) = model.get(sym) {
                calldata[i] = crate::value_to_u8(&v);
            }
        }
        let callvalue = model
            .get(vars.callvalue_sym)
            .map_or_else(crate::word::Word::zero, |v| crate::value_to_word(&v));
        let caller = model
            .get(vars.caller_sym)
            .map_or_else(crate::word::Word::zero, |v| crate::value_to_word(&v));
        TxWitness {
            calldata,
            callvalue,
            caller,
        }
    };
    let prior_txs: Vec<TxWitness> = (0..tx).map(lift_tx).collect();
    let here = lift_tx(tx);
    Ok(Some(PathBug {
        kind,
        pc,
        calldata: here.calldata,
        callvalue: here.callvalue,
        caller: here.caller,
        prior_txs,
        env_inputs,
    }))
}

/// Tests whether an overflow predicate is path-feasible. Returns the bug if so;
/// flags `saw_unknown` if the feasibility query is undecided.
#[allow(clippy::too_many_arguments)]
fn check_overflow(
    arena: &mut TermArena,
    exec: &mut SymbolicExecutor,
    env: &SymEnv,
    tx: usize,
    env_syms: &[SymbolId],
    ovf: TermId,
    kind: BugKind,
    pc: usize,
    saw_unknown: &mut bool,
    obligations: &mut Vec<TermId>,
) -> Result<Option<PathBug>, SolverError> {
    let branch = exec.branch(arena, ovf)?;
    if branch.if_true.is_feasible() {
        // Commit the overflow condition so model() lifts a witnessing input.
        exec.assume_auto(arena, ovf)?;
        return lift_witness(arena, exec, env, tx, env_syms, kind, pc);
    }
    if matches!(branch.if_true, PathStatus::Unknown(_)) {
        *saw_unknown = true;
    } else {
        // The overflow is *infeasible* under the current path: record the real
        // refuted obligation `path ∧ ovf` (item #3 — the SafeUpToBound proof is
        // the conjunction of these being UNSAT, not a fabricated `0==1`).
        if let Some(ob) = path_obligation(arena, exec, ovf)? {
            obligations.push(ob);
        }
    }
    Ok(None)
}

/// Builds the term `(⋀ path_condition) ∧ predicate` — a single self-contained
/// reachability obligation the solver refuted. Returns `None` if the path
/// condition references nothing (the obligation is just `predicate`).
fn path_obligation(
    arena: &mut TermArena,
    exec: &SymbolicExecutor,
    predicate: TermId,
) -> Result<Option<TermId>, SolverError> {
    let mut acc = predicate;
    for &c in exec.path_condition() {
        acc = arena.and(acc, c)?;
    }
    Ok(Some(acc))
}

/// EVM div/mod-by-zero = 0 guard around a partial SMT-LIB op.
fn div_guard(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    op: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Result<TermId, SolverError> {
    let zero = arena.bv_const(W, 0)?;
    let is_zero = arena.eq(b, zero)?;
    let raw = op(arena, a, b)?;
    Ok(arena.ite(is_zero, zero, raw)?)
}

/// ADDMOD/MULMOD at 512 bits then truncate, with n==0 ⇒ 0.
fn mod_512(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    n: TermId,
    mul: bool,
) -> Result<TermId, SolverError> {
    let zero = arena.bv_const(W, 0)?;
    let n_zero = arena.eq(n, zero)?;
    let aw = arena.zero_ext(W, a)?;
    let bw = arena.zero_ext(W, b)?;
    let nw = arena.zero_ext(W, n)?;
    let prod = if mul {
        arena.bv_mul(aw, bw)?
    } else {
        arena.bv_add(aw, bw)?
    };
    let r = arena.bv_urem(prod, nw)?;
    let trunc = arena.extract(W - 1, 0, r)?;
    Ok(arena.ite(n_zero, zero, trunc)?)
}

/// Maps a Boolean term to the 256-bit word 1 (true) / 0 (false).
fn bool_to_word(arena: &mut TermArena, cond: TermId) -> Result<TermId, SolverError> {
    let one = arena.bv_const(W, 1)?;
    let zero = arena.bv_const(W, 0)?;
    Ok(arena.ite(cond, one, zero)?)
}

/// Builds a 256-bit constant from up-to-32 big-endian immediate bytes.
fn push_word(arena: &mut TermArena, immediate: &[u8]) -> TermId {
    let word = crate::word::Word::from_be_bytes(immediate);
    arena.wide_bv_const(word.0)
}

/// Reads 32 calldata bytes starting at offset `o` as a big-endian 256-bit word.
/// Bytes past the modeled buffer are zero.
fn calldata_word(
    arena: &mut TermArena,
    env: &SymEnv,
    tx: usize,
    o: usize,
) -> Result<TermId, SolverError> {
    // Concatenate bytes o..o+32, most-significant first.
    let mut acc: Option<TermId> = None;
    for i in 0..32 {
        let byte = match env.tx(tx).calldata_bytes.get(o + i) {
            Some(t) => *t,
            None => arena.bv_const(8, 0)?,
        };
        acc = Some(match acc {
            None => byte,
            Some(prev) => arena.concat(prev, byte)?,
        });
    }
    Ok(acc.expect("32 bytes concatenated"))
}

/// Loads a 256-bit word from concrete-offset memory (big-endian), zero for
/// untouched bytes.
fn mem_load(arena: &mut TermArena, state: &State, o: usize) -> Result<TermId, SolverError> {
    let mut acc: Option<TermId> = None;
    for i in 0..32 {
        let byte = match state.memory.get(&(o + i)) {
            Some(t) => *t,
            None => arena.bv_const(8, 0)?,
        };
        acc = Some(match acc {
            None => byte,
            Some(prev) => arena.concat(prev, byte)?,
        });
    }
    Ok(acc.expect("32 bytes concatenated"))
}

/// Stores a 256-bit word into concrete-offset memory as 32 big-endian bytes.
fn mem_store(
    arena: &mut TermArena,
    state: &mut State,
    o: usize,
    val: TermId,
) -> Result<(), SolverError> {
    for i in 0..32u32 {
        let hi = 255 - i * 8;
        let lo = hi - 7;
        let byte = arena.extract(hi, lo, val)?;
        state.memory.insert(o + i as usize, byte);
    }
    Ok(())
}

/// Folds a symbolic read-over-write list newest-first into an `ite` chain:
/// `select(key) = ite(key == kₙ, vₙ, … ite(key == k₀, v₀, base))`. All terms are
/// pure `QF_BV` (`eq`/`ite`), so the warm executor reasons about them directly.
fn fold_word_writes(
    arena: &mut TermArena,
    writes: &[Write],
    key: TermId,
    base: TermId,
) -> Result<TermId, SolverError> {
    let mut acc = base;
    for w in writes {
        let hit = arena.eq(key, w.key)?;
        acc = arena.ite(hit, w.value, acc)?;
    }
    Ok(acc)
}

/// The base value for a storage read at `key`: the concrete-key fast-path entry
/// when `key` is a syntactic constant present in the concrete map, else 0 (the
/// EVM cold-slot default). Symbolic writes are layered on top by the caller.
fn storage_base(arena: &mut TermArena, state: &State, key: TermId) -> Result<TermId, SolverError> {
    if let Some(k) = concrete_bytes(arena, key) {
        if let Some(&t) = state.storage.get(&k) {
            // A concrete write is also on the symbolic list (SSTORE records both);
            // returning 0 here and letting the fold pick it up keeps a single
            // source of truth. But constant-folding the common pure-concrete path
            // is cheaper, so prefer the map value when no symbolic key exists.
            if state
                .sym_storage
                .iter()
                .all(|w| concrete_bytes(arena, w.key).is_some())
            {
                return Ok(t);
            }
        }
    }
    Ok(arena.bv_const(W, 0)?)
}

/// Gathers `len` bytes of memory starting at concrete offset `o` into one
/// `BV(8*len)` term (most-significant byte first), reading symbolic word-writes
/// when the byte is not in the concrete map. Used to build a keccak preimage.
fn gather_bytes(
    arena: &mut TermArena,
    state: &State,
    o: usize,
    len: usize,
) -> Result<TermId, SolverError> {
    let mut acc: Option<TermId> = None;
    for i in 0..len {
        let byte = byte_at(arena, state, o + i)?;
        acc = Some(match acc {
            None => byte,
            Some(prev) => arena.concat(prev, byte)?,
        });
    }
    Ok(acc.expect("len >= 1"))
}

/// The 8-bit memory term at byte offset `b`: the concrete byte map first, else
/// the byte sliced out of a symbolic word-write covering `b` (newest-first),
/// else zero.
fn byte_at(arena: &mut TermArena, state: &State, b: usize) -> Result<TermId, SolverError> {
    if let Some(&t) = state.memory.get(&b) {
        return Ok(t);
    }
    // Look for the newest symbolic word-write whose 32-byte span covers `b` at a
    // *constant* offset. Symbolic-offset word writes cannot be byte-sliced for a
    // keccak preimage here, so they contribute zero (a conservative read).
    let base = arena.bv_const(8, 0)?;
    let mut acc = base;
    for w in &state.sym_memory {
        if let Some(off) = concrete_usize(arena, w.key) {
            if b >= off && b < off + 32 {
                let bit_hi = 255 - u32::try_from((b - off) * 8).unwrap_or(0);
                let lo = bit_hi.saturating_sub(7);
                acc = arena.extract(bit_hi, lo, w.value)?;
            }
        }
    }
    Ok(acc)
}

/// The keccak injectivity lemma pairing a *new* hash application against every
/// prior *same-width* one: `⋀ᵢ (argᵢ == arg_new ⇔ resultᵢ == result_new)` (the
/// collision-freedom assumption; same-width because the UF is per-length). `None`
/// when there is no prior same-width hash to relate. Asserted when the hash is
/// created so a mapping keyed by `keccak(slot.key)` is decided by key
/// (dis)equality rather than havoc'd.
fn keccak_injectivity_pair(
    arena: &mut TermArena,
    prior: &[KeccakApp],
    new_app: &KeccakApp,
) -> Result<Option<TermId>, SolverError> {
    let mut lemma: Option<TermId> = None;
    for p in prior {
        if p.len != new_app.len {
            continue;
        }
        let arg_eq = arena.eq(p.arg, new_app.arg)?;
        let res_eq = arena.eq(p.result, new_app.result)?;
        // arg_eq <=> res_eq : injective both ways (no collisions, and equal args
        // hash equally). Stating both keeps the UF from being forced apart on
        // equal preimages.
        let inj = arena.eq(arg_eq, res_eq)?;
        lemma = Some(match lemma {
            None => inj,
            Some(prev) => arena.and(prev, inj)?,
        });
    }
    Ok(lemma)
}

/// Resolves a term to a concrete `usize` offset/target *on the current path*:
/// feasible iff it can take exactly one value here. Phase-1 only resolves
/// offsets that are syntactically constant (interned `wide_bv_const` / small
/// const) — fully general concretization is deferred. Returns `None` when the
/// value is not a resolvable constant (the path is then surfaced as Unknown).
fn concrete_usize(arena: &TermArena, term: TermId) -> Option<usize> {
    const_word(arena, term).and_then(|w| w.to_usize())
}

/// Resolves a 256-bit term to concrete key bytes (only syntactic constants).
fn concrete_bytes(arena: &TermArena, term: TermId) -> Option<[u8; 32]> {
    const_word(arena, term).map(|w| w.to_be_bytes())
}

/// If `term` is a syntactic bit-vector constant, returns it as a [`Word`].
fn const_word(arena: &TermArena, term: TermId) -> Option<crate::word::Word> {
    use axeyum_ir::TermNode;
    match arena.node(term) {
        // A bit-vector constant of any width `≤ 256` is a resolvable offset/key
        // (PUSH constants intern as `WideBvConst` at width 256; narrower consts
        // arise from small literals).
        TermNode::BvConst { width, value } if *width <= W => {
            Some(crate::word::Word::from_u128(*value))
        }
        TermNode::WideBvConst(w) if w.width() == W => Some(crate::word::Word(w.clone())),
        _ => None,
    }
}
