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
//! * KECCAK / CALL / GAS / unsupported opcodes → **havoc** (a fresh unconstrained
//!   word), so those paths become sound `Unknown`, never wrong.
//! * Symbolic memory/jump offsets that are not concretely resolvable terminate
//!   the path as `Unknown` (never silently mis-stepped).

use std::collections::BTreeMap;

use axeyum_ir::{SymbolId, TermArena, TermId};
use axeyum_solver::{PathStatus, SymbolicExecutor};
use axeyum_solver::{SolverConfig, SolverError};

use crate::opcode::{Op, Program};

/// Word width for the symbolic machine (EVM 256-bit).
const W: u32 = 256;
/// Bound on how many `CALLDATALOAD` / `CALLDATASIZE` care about; calldata symbols
/// past this are still fresh but unconstrained.
const MAX_CALLDATA_BYTES: usize = 256;

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

/// A bug witnessed on some feasible path, with a lifted concrete witness.
#[derive(Debug, Clone)]
pub struct PathBug {
    /// What kind of bug.
    pub kind: BugKind,
    /// The byte offset (pc) where the bug was witnessed.
    pub pc: usize,
    /// The concrete calldata driving the path to the bug.
    pub calldata: Vec<u8>,
    /// The concrete `CALLVALUE` along the path.
    pub callvalue: crate::word::Word,
    /// The concrete `CALLER` along the path.
    pub caller: crate::word::Word,
}

/// Outcome of exploring the program.
#[derive(Debug)]
pub struct Exploration {
    /// The first bug found, with a lifted concrete witness (Phase-1 reports the
    /// first feasible bug).
    pub bug: Option<PathBug>,
    /// Whether any path ended in `Unknown` (havoc/limit) — the result is not a
    /// sound "no bug" proof when this is set on the explored sub-tree.
    pub saw_unknown: bool,
}

/// The symbolic machine state along one path.
struct State {
    stack: Vec<TermId>,
    /// Concrete-offset memory: byte offset -> an 8-bit IR term.
    memory: BTreeMap<usize, TermId>,
    /// Concrete-key storage: 256-bit key bytes -> a 256-bit IR term.
    storage: BTreeMap<[u8; 32], TermId>,
}

/// Reusable symbolic environment (declared once, shared across all paths).
struct SymEnv {
    /// One 8-bit symbol per calldata byte index.
    calldata_bytes: Vec<TermId>,
    calldata_syms: Vec<SymbolId>,
    callvalue: TermId,
    callvalue_sym: SymbolId,
    caller: TermId,
    caller_sym: SymbolId,
    /// Monotonic counter for fresh havoc symbols.
    havoc_counter: u64,
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
) -> Result<Exploration, SolverError> {
    let mut arena = TermArena::new();
    let mut env = build_env(&mut arena)?;
    let mut exec = SymbolicExecutor::with_config(config.clone());

    let mut saw_unknown = false;
    let bug = walk(
        program,
        &mut arena,
        &mut exec,
        &mut env,
        max_steps,
        track_overflow,
        &mut saw_unknown,
    )?;

    Ok(Exploration { bug, saw_unknown })
}

fn build_env(arena: &mut TermArena) -> Result<SymEnv, SolverError> {
    let mut calldata_bytes = Vec::with_capacity(MAX_CALLDATA_BYTES);
    let mut calldata_syms = Vec::with_capacity(MAX_CALLDATA_BYTES);
    for i in 0..MAX_CALLDATA_BYTES {
        let name = format!("calldata[{i}]");
        let sym = arena.declare(&name, axeyum_ir::Sort::BitVec(8))?;
        calldata_syms.push(sym);
        calldata_bytes.push(arena.var(sym));
    }
    let callvalue_sym = arena.declare("callvalue", axeyum_ir::Sort::BitVec(W))?;
    let callvalue = arena.var(callvalue_sym);
    let caller_sym = arena.declare("caller", axeyum_ir::Sort::BitVec(W))?;
    let caller = arena.var(caller_sym);
    Ok(SymEnv {
        calldata_bytes,
        calldata_syms,
        callvalue,
        callvalue_sym,
        caller,
        caller_sym,
        havoc_counter: 0,
    })
}

impl SymEnv {
    /// A fresh unconstrained 256-bit word (the havoc primitive).
    fn havoc(&mut self, arena: &mut TermArena) -> Result<TermId, SolverError> {
        let name = format!("havoc!{}", self.havoc_counter);
        self.havoc_counter += 1;
        let sym = arena.declare(&name, axeyum_ir::Sort::BitVec(W))?;
        Ok(arena.var(sym))
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
    saw_unknown: &mut bool,
) -> Result<Option<PathBug>, SolverError> {
    let mut state = State {
        stack: Vec::new(),
        memory: BTreeMap::new(),
        storage: BTreeMap::new(),
    };
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
        saw_unknown,
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
    saw_unknown: &mut bool,
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
            Op::Stop | Op::Return => return Ok(None),
            Op::Invalid => {
                // INVALID is reachable on this (feasible) path; lift a witness.
                if let Some(bug) = lift_witness(arena, exec, env, BugKind::Invalid, pc)? {
                    return Ok(Some(bug));
                }
                *saw_unknown = true;
                return Ok(None);
            }
            Op::Revert => {
                if let Some(bug) = lift_witness(arena, exec, env, BugKind::Revert, pc)? {
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
                        ovf,
                        BugKind::AddOverflow,
                        pc,
                        saw_unknown,
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
                        ovf,
                        BugKind::MulOverflow,
                        pc,
                        saw_unknown,
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
            Op::CallValue => state.stack.push(env.callvalue),
            Op::Caller => state.stack.push(env.caller),
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
                let word = calldata_word(arena, env, o)?;
                state.stack.push(word);
            }
            Op::Pop => {
                let _ = pop_or_unknown!();
            }
            Op::Mload => {
                let off = pop_or_unknown!();
                let Some(o) = concrete_usize(arena, off) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                let word = mem_load(arena, state, o)?;
                state.stack.push(word);
            }
            Op::Mstore => {
                let off = pop_or_unknown!();
                let val = pop_or_unknown!();
                let Some(o) = concrete_usize(arena, off) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                mem_store(arena, state, o, val)?;
            }
            Op::Mstore8 => {
                let off = pop_or_unknown!();
                let val = pop_or_unknown!();
                let Some(o) = concrete_usize(arena, off) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                let lo = arena.extract(7, 0, val)?;
                state.memory.insert(o, lo);
            }
            Op::Sload => {
                let key = pop_or_unknown!();
                let Some(k) = concrete_bytes(arena, key) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                let v = match state.storage.get(&k) {
                    Some(t) => *t,
                    None => arena.bv_const(W, 0)?,
                };
                state.stack.push(v);
            }
            Op::Sstore => {
                let key = pop_or_unknown!();
                let val = pop_or_unknown!();
                let Some(k) = concrete_bytes(arena, key) else {
                    *saw_unknown = true;
                    return Ok(None);
                };
                state.storage.insert(k, val);
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
                            let status = exec.assume(arena, taken)?;
                            if !status.is_infeasible() {
                                let mut forked = State {
                                    stack: state.stack.clone(),
                                    memory: state.memory.clone(),
                                    storage: state.storage.clone(),
                                };
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
                                    saw_unknown,
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
                let status = exec.assume(arena, not_taken)?;
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
            Op::Unsupported(_) => {
                // KECCAK / CALL / GAS / LOG / … : havoc and continue is unsound for
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
    kind: BugKind,
    pc: usize,
) -> Result<Option<PathBug>, SolverError> {
    let Some(model) = exec.model(arena)? else {
        return Ok(None);
    };
    let mut calldata = vec![0u8; env.calldata_syms.len()];
    for (i, &sym) in env.calldata_syms.iter().enumerate() {
        if let Some(v) = model.get(sym) {
            calldata[i] = crate::value_to_u8(&v);
        }
    }
    let callvalue = model
        .get(env.callvalue_sym)
        .map_or_else(crate::word::Word::zero, |v| crate::value_to_word(&v));
    let caller = model
        .get(env.caller_sym)
        .map_or_else(crate::word::Word::zero, |v| crate::value_to_word(&v));
    Ok(Some(PathBug {
        kind,
        pc,
        calldata,
        callvalue,
        caller,
    }))
}

/// Tests whether an overflow predicate is path-feasible. Returns the bug if so;
/// flags `saw_unknown` if the feasibility query is undecided.
fn check_overflow(
    arena: &mut TermArena,
    exec: &mut SymbolicExecutor,
    env: &SymEnv,
    ovf: TermId,
    kind: BugKind,
    pc: usize,
    saw_unknown: &mut bool,
) -> Result<Option<PathBug>, SolverError> {
    let branch = exec.branch(arena, ovf)?;
    if branch.if_true.is_feasible() {
        // Commit the overflow condition so model() lifts a witnessing input.
        exec.assume(arena, ovf)?;
        return lift_witness(arena, exec, env, kind, pc);
    }
    if matches!(branch.if_true, PathStatus::Unknown(_)) {
        *saw_unknown = true;
    }
    Ok(None)
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
fn calldata_word(arena: &mut TermArena, env: &SymEnv, o: usize) -> Result<TermId, SolverError> {
    // Concatenate bytes o..o+32, most-significant first.
    let mut acc: Option<TermId> = None;
    for i in 0..32 {
        let byte = match env.calldata_bytes.get(o + i) {
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
