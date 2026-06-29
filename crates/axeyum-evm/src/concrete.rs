//! A concrete EVM interpreter over 256-bit [`Word`]s — the *soundness oracle*.
//!
//! Every symbolic witness must be re-checked here: run the contract on the
//! concrete calldata the solver produced and confirm the bug actually fires. A
//! witness that does not reproduce means the symbolic lowering is wrong (a defect
//! to fix), never a reported finding. This is the DISAGREE=0 floor.
//!
//! The interpreter mirrors the symbolic lowering opcode-for-opcode, including the
//! EVM totality caveats (DIV/MOD-by-0 = 0, ADDMOD/MULMOD at 512-bit). Opcodes
//! outside the supported subset (KECCAK, CALL, GAS, …) halt the path as
//! [`Halt::Unsupported`] — matching the symbolic side's havoc-to-Unknown.

use std::collections::BTreeMap;

use axeyum_ir::WideUint;

use crate::opcode::{Op, Program};
use crate::word::{WIDTH, Word};

/// Why a concrete run stopped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Halt {
    /// `STOP` or `RETURN` — normal termination.
    Stop,
    /// `RETURN` with the returned bytes.
    Return(Vec<u8>),
    /// `REVERT` with the revert data (the assertion-violation / require-failure
    /// signal; a `Panic(0x11)` overflow shows up here too via the Solidity
    /// checked-arithmetic prelude).
    Revert(Vec<u8>),
    /// `INVALID` opcode (`0xfe`) — the legacy assertion failure.
    Invalid,
    /// Ran off the end of code, or hit an opcode outside the Phase-1 subset, or a
    /// stack underflow / bad jump. Concrete execution cannot continue soundly.
    Unsupported(String),
}

/// The concrete machine environment the harness fixes.
#[derive(Debug, Clone)]
pub struct Env {
    /// Symbolic-input calldata, made concrete.
    pub calldata: Vec<u8>,
    /// `CALLVALUE` (msg.value).
    pub callvalue: Word,
    /// `CALLER` (msg.sender).
    pub caller: Word,
}

impl Default for Env {
    fn default() -> Self {
        Self {
            calldata: Vec::new(),
            callvalue: Word::zero(),
            caller: Word::zero(),
        }
    }
}

/// Runs `program` concretely under `env`, returning why it halted. `step_limit`
/// bounds execution (loops / runaway code) — exceeding it is `Unsupported`.
#[must_use]
pub fn run(program: &Program, env: &Env, step_limit: usize) -> Halt {
    run_with_env(program, env, step_limit, &[])
}

/// Like [`run`] but replays a witnessed sequence of environment-opcode values
/// (`Op::Env` — `GAS`/`BALANCE`/context/…) in execution order, so a bug that
/// branches on environment nondeterminism reproduces deterministically.
#[must_use]
pub fn run_with_env(program: &Program, env: &Env, step_limit: usize, env_inputs: &[Word]) -> Halt {
    let mut storage: BTreeMap<[u8; 32], Word> = BTreeMap::new();
    let mut env_cursor = 0usize;
    run_core(
        program,
        env,
        step_limit,
        None,
        &mut storage,
        env_inputs,
        &mut env_cursor,
    )
    .0
}

/// Runs a **sequence** of transactions with persistent storage between them
/// (memory and the stack are per-tx; storage carries over) — the concrete oracle
/// for multi-tx witnesses. `env_inputs` are the path's environment values,
/// consumed in global order across the whole sequence. Returns the halt of the
/// *last* transaction. An earlier tx that does not halt normally (`Stop`/`Return`)
/// aborts the sequence and its halt is returned (the sequence could not proceed).
#[must_use]
pub fn run_sequence(
    program: &Program,
    envs: &[Env],
    step_limit: usize,
    env_inputs: &[Word],
) -> Halt {
    let mut storage: BTreeMap<[u8; 32], Word> = BTreeMap::new();
    let mut env_cursor = 0usize;
    let mut last = Halt::Stop;
    for (i, env) in envs.iter().enumerate() {
        last = run_core(
            program,
            env,
            step_limit,
            None,
            &mut storage,
            env_inputs,
            &mut env_cursor,
        )
        .0;
        let is_last = i + 1 == envs.len();
        if !is_last && !matches!(last, Halt::Stop | Halt::Return(_)) {
            // A pre-final tx reverted/failed: the intended sequence cannot reach
            // the final-tx state, so report this halt (it will not match the
            // expected final-tx bug and the witness is rejected).
            return last;
        }
    }
    last
}

/// The single concrete interpreter. When `watch = Some((pc, is_mul))`, it reports
/// — as the second return value — whether the tracked `ADD`/`MUL` at byte offset
/// `pc` *unsigned-overflowed* the first time it was reached (the concrete
/// overflow-witness check). One interpreter, no divergent second copy.
#[must_use]
#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
fn run_core(
    program: &Program,
    env: &Env,
    step_limit: usize,
    watch: Option<(usize, bool)>,
    storage: &mut BTreeMap<[u8; 32], Word>,
    env_inputs: &[Word],
    env_cursor: &mut usize,
) -> (Halt, bool) {
    let mut stack: Vec<Word> = Vec::new();
    let mut memory: BTreeMap<usize, u8> = BTreeMap::new();
    let mut pc = 0usize;
    let mut steps = 0usize;
    let mut overflowed = false;
    // Set after a may-reenter external call: subsequent `SLOAD`s read a witnessed
    // env value (adversarial storage), mirroring the symbolic re-entrancy model.
    let mut storage_dirty = false;

    macro_rules! pop {
        () => {
            match stack.pop() {
                Some(w) => w,
                None => return (Halt::Unsupported("stack underflow".into()), overflowed),
            }
        };
    }

    loop {
        if steps >= step_limit {
            return (Halt::Unsupported("step limit exceeded".into()), overflowed);
        }
        steps += 1;

        let Some(index) = program.index_at(pc) else {
            // No instruction starts here (off the end, or mid-PUSH-immediate).
            return (Halt::Stop, overflowed);
        };
        let inst = &program.instructions[index];
        let next_pc = inst.pc
            + 1
            + match inst.op {
                Op::Push(n) => n as usize,
                _ => 0,
            };

        match inst.op {
            Op::Stop => return (Halt::Stop, overflowed),
            Op::Add => {
                let (a, b) = (pop!(), pop!());
                if watch == Some((inst.pc, false)) {
                    overflowed = a.0.add(&b.0).ult(&a.0);
                }
                stack.push(Word(a.0.add(&b.0)));
            }
            Op::Mul => {
                let (a, b) = (pop!(), pop!());
                if watch == Some((inst.pc, true)) && !a.0.is_zero() {
                    overflowed = a.0.mul(&b.0).udiv(&a.0) != b.0;
                }
                stack.push(Word(a.0.mul(&b.0)));
            }
            Op::Sub => {
                let (a, b) = (pop!(), pop!());
                stack.push(Word(a.0.sub(&b.0)));
            }
            Op::Div => {
                let (a, b) = (pop!(), pop!());
                stack.push(if b.is_zero() {
                    Word::zero()
                } else {
                    Word(a.0.udiv(&b.0))
                });
            }
            Op::Sdiv => {
                let (a, b) = (pop!(), pop!());
                stack.push(if b.is_zero() {
                    Word::zero()
                } else {
                    Word(a.0.sdiv(&b.0))
                });
            }
            Op::Mod => {
                let (a, b) = (pop!(), pop!());
                stack.push(if b.is_zero() {
                    Word::zero()
                } else {
                    Word(a.0.urem(&b.0))
                });
            }
            Op::Smod => {
                let (a, b) = (pop!(), pop!());
                stack.push(if b.is_zero() {
                    Word::zero()
                } else {
                    Word(a.0.srem(&b.0))
                });
            }
            Op::Addmod => {
                let (a, b, n) = (pop!(), pop!(), pop!());
                stack.push(if n.is_zero() {
                    Word::zero()
                } else {
                    let wide = 512;
                    let aw = a.0.zero_ext(wide - WIDTH);
                    let bw = b.0.zero_ext(wide - WIDTH);
                    let nw = n.0.zero_ext(wide - WIDTH);
                    let r = aw.add(&bw).urem(&nw);
                    Word(r.extract(WIDTH - 1, 0))
                });
            }
            Op::Mulmod => {
                let (a, b, n) = (pop!(), pop!(), pop!());
                stack.push(if n.is_zero() {
                    Word::zero()
                } else {
                    let wide = 512;
                    let aw = a.0.zero_ext(wide - WIDTH);
                    let bw = b.0.zero_ext(wide - WIDTH);
                    let nw = n.0.zero_ext(wide - WIDTH);
                    let r = aw.mul(&bw).urem(&nw);
                    Word(r.extract(WIDTH - 1, 0))
                });
            }
            Op::Lt => {
                let (a, b) = (pop!(), pop!());
                stack.push(bool_word(a.0.ult(&b.0)));
            }
            Op::Gt => {
                let (a, b) = (pop!(), pop!());
                stack.push(bool_word(b.0.ult(&a.0)));
            }
            Op::Slt => {
                let (a, b) = (pop!(), pop!());
                stack.push(bool_word(a.0.slt(&b.0)));
            }
            Op::Sgt => {
                let (a, b) = (pop!(), pop!());
                stack.push(bool_word(b.0.slt(&a.0)));
            }
            Op::Eq => {
                let (a, b) = (pop!(), pop!());
                stack.push(bool_word(a.0 == b.0));
            }
            Op::IsZero => {
                let a = pop!();
                stack.push(bool_word(a.is_zero()));
            }
            Op::And => {
                let (a, b) = (pop!(), pop!());
                stack.push(Word(a.0.and(&b.0)));
            }
            Op::Or => {
                let (a, b) = (pop!(), pop!());
                stack.push(Word(a.0.or(&b.0)));
            }
            Op::Xor => {
                let (a, b) = (pop!(), pop!());
                stack.push(Word(a.0.xor(&b.0)));
            }
            Op::Not => {
                let a = pop!();
                stack.push(Word(a.0.not()));
            }
            Op::Exp => {
                let (base, exp) = (pop!(), pop!());
                stack.push(base.pow(&exp));
            }
            Op::SignExtend => {
                let (b, x) = (pop!(), pop!());
                // Sign-extend x from a (b+1)-byte value to 256 bits. b >= 31 is a
                // no-op. Implemented over big-endian bytes to match the symbolic
                // extract+sign_ext model exactly (replay must agree).
                let out = match b.to_usize() {
                    Some(bb) if bb < 31 => {
                        let keep = bb + 1; // bytes to keep, counting from the LSB
                        let mut bytes = x.to_be_bytes();
                        // Most-significant *kept* byte sits at index 32 - keep.
                        let sign_idx = 32 - keep;
                        let fill = if bytes[sign_idx] & 0x80 != 0 { 0xff } else { 0x00 };
                        for byte in bytes.iter_mut().take(sign_idx) {
                            *byte = fill;
                        }
                        Word::from_be_bytes(&bytes)
                    }
                    _ => x,
                };
                stack.push(out);
            }
            Op::Byte => {
                let (i, x) = (pop!(), pop!());
                // byte i (from the most-significant) of x.
                let out = match i.to_usize() {
                    Some(idx) if idx < 32 => {
                        let b = x.to_be_bytes()[idx];
                        Word::from_u128(u128::from(b))
                    }
                    _ => Word::zero(),
                };
                stack.push(out);
            }
            Op::Shl => {
                let (shift, value) = (pop!(), pop!());
                stack.push(match shift.to_usize().and_then(small_shift) {
                    Some(s) => Word(value.0.shl(s)),
                    None => Word::zero(),
                });
            }
            Op::Shr => {
                let (shift, value) = (pop!(), pop!());
                stack.push(match shift.to_usize().and_then(small_shift) {
                    Some(s) => Word(value.0.lshr(s)),
                    None => Word::zero(),
                });
            }
            Op::Sar => {
                let (shift, value) = (pop!(), pop!());
                stack.push(match shift.to_usize().and_then(small_shift) {
                    Some(s) => Word(value.0.ashr(s)),
                    // Shift >= 256: result is the sign extension (0 or all-ones).
                    None => {
                        if value.0.is_negative() {
                            Word(WideUint::ones(WIDTH))
                        } else {
                            Word::zero()
                        }
                    }
                });
            }
            Op::Sha3 => {
                let (off, len) = (pop!(), pop!());
                let (Some(o), Some(l)) = (off.to_usize(), len.to_usize()) else {
                    return (
                        Halt::Unsupported("SHA3 offset/length too large".into()),
                        overflowed,
                    );
                };
                if l > 1 << 20 {
                    return (
                        Halt::Unsupported("SHA3 region too large".into()),
                        overflowed,
                    );
                }
                let preimage: Vec<u8> = (0..l)
                    .map(|i| memory.get(&(o + i)).copied().unwrap_or(0))
                    .collect();
                let digest = crate::keccak::keccak256(&preimage);
                stack.push(Word::from_be_bytes(&digest));
            }
            Op::CallValue => stack.push(env.callvalue.clone()),
            Op::Caller => stack.push(env.caller.clone()),
            Op::CallDataSize => stack.push(Word::from_u128(env.calldata.len() as u128)),
            Op::CallDataLoad => {
                let off = pop!();
                let word = match off.to_usize() {
                    Some(o) => {
                        let mut bytes = [0u8; 32];
                        for (i, b) in bytes.iter_mut().enumerate() {
                            *b = env.calldata.get(o + i).copied().unwrap_or(0);
                        }
                        Word::from_be_bytes(&bytes)
                    }
                    None => Word::zero(),
                };
                stack.push(word);
            }
            Op::Pop => {
                pop!();
            }
            Op::Mload => {
                let off = pop!();
                let Some(o) = off.to_usize() else {
                    return (
                        Halt::Unsupported("MLOAD offset too large".into()),
                        overflowed,
                    );
                };
                let mut bytes = [0u8; 32];
                for (i, b) in bytes.iter_mut().enumerate() {
                    *b = memory.get(&(o + i)).copied().unwrap_or(0);
                }
                stack.push(Word::from_be_bytes(&bytes));
            }
            Op::Mstore => {
                let (off, val) = (pop!(), pop!());
                let Some(o) = off.to_usize() else {
                    return (
                        Halt::Unsupported("MSTORE offset too large".into()),
                        overflowed,
                    );
                };
                let bytes = val.to_be_bytes();
                for (i, b) in bytes.iter().enumerate() {
                    memory.insert(o + i, *b);
                }
            }
            Op::Mstore8 => {
                let (off, val) = (pop!(), pop!());
                let Some(o) = off.to_usize() else {
                    return (
                        Halt::Unsupported("MSTORE8 offset too large".into()),
                        overflowed,
                    );
                };
                memory.insert(o, val.to_be_bytes()[31]);
            }
            Op::Sload => {
                let key = pop!();
                let v = if storage_dirty {
                    // Adversarial storage after a re-entrant call: replay the
                    // witnessed value (matches the symbolic side's fresh read).
                    let value = env_inputs
                        .get(*env_cursor)
                        .cloned()
                        .unwrap_or_else(Word::zero);
                    *env_cursor += 1;
                    value
                } else {
                    storage
                        .get(&key.to_be_bytes())
                        .cloned()
                        .unwrap_or_else(Word::zero)
                };
                stack.push(v);
            }
            Op::Sstore => {
                let (key, val) = (pop!(), pop!());
                storage.insert(key.to_be_bytes(), val);
            }
            Op::Jump => {
                let dest = pop!();
                let Some(d) = dest.to_usize() else {
                    return (
                        Halt::Unsupported("JUMP to oversized dest".into()),
                        overflowed,
                    );
                };
                if !program.is_jumpdest(d) {
                    return (Halt::Invalid, overflowed);
                }
                pc = d;
                continue;
            }
            Op::Jumpi => {
                let (dest, cond) = (pop!(), pop!());
                if cond.is_zero() {
                    pc = next_pc;
                } else {
                    let Some(d) = dest.to_usize() else {
                        return (
                            Halt::Unsupported("JUMPI to oversized dest".into()),
                            overflowed,
                        );
                    };
                    if !program.is_jumpdest(d) {
                        return (Halt::Invalid, overflowed);
                    }
                    pc = d;
                }
                continue;
            }
            Op::Pc => stack.push(Word::from_u128(inst.pc as u128)),
            Op::Jumpdest => {}
            Op::Push(_) => {
                stack.push(Word::from_be_bytes(&inst.immediate));
            }
            Op::Dup(n) => {
                let n = n as usize;
                if stack.len() < n {
                    return (Halt::Unsupported("DUP underflow".into()), overflowed);
                }
                let w = stack[stack.len() - n].clone();
                stack.push(w);
            }
            Op::Swap(n) => {
                let n = n as usize;
                if stack.len() < n + 1 {
                    return (Halt::Unsupported("SWAP underflow".into()), overflowed);
                }
                let len = stack.len();
                stack.swap(len - 1, len - 1 - n);
            }
            Op::Return => {
                let (off, len) = (pop!(), pop!());
                let data = read_mem(&memory, &off, &len);
                let halt = data.map_or_else(
                    || Halt::Unsupported("RETURN region too large".into()),
                    Halt::Return,
                );
                return (halt, overflowed);
            }
            Op::Revert => {
                let (off, len) = (pop!(), pop!());
                let data = read_mem(&memory, &off, &len);
                let halt = data.map_or_else(
                    || Halt::Unsupported("REVERT region too large".into()),
                    Halt::Revert,
                );
                return (halt, overflowed);
            }
            Op::Call { pops, may_reenter } => {
                // Args (top→bottom): …, retOffset (2nd-to-last), retLength (last).
                let mut ret_len = None;
                let mut ret_off = None;
                for k in 0..pops {
                    let v = pop!();
                    if k + 1 == pops {
                        ret_len = Some(v);
                    } else if k + 2 == pops {
                        ret_off = Some(v);
                    }
                }
                if may_reenter {
                    storage_dirty = true;
                }
                // Replay the witnessed success flag (env oracle, in execution
                // order). Default 0 if exhausted.
                let value = env_inputs
                    .get(*env_cursor)
                    .cloned()
                    .unwrap_or_else(Word::zero);
                *env_cursor += 1;
                stack.push(value);
                // Replay witnessed return data into memory, mirroring the symbolic
                // model (same region condition, same env-order consumption).
                let rl = ret_len.and_then(|w| w.to_usize());
                let ro = ret_off.and_then(|w| w.to_usize());
                if let (Some(len), Some(off)) = (rl, ro) {
                    if len != 0 && len % 32 == 0 && len / 32 <= crate::symbolic::MAX_RETURN_WORDS {
                        for k in 0..(len / 32) {
                            let word = env_inputs
                                .get(*env_cursor)
                                .cloned()
                                .unwrap_or_else(Word::zero);
                            *env_cursor += 1;
                            let bytes = word.to_be_bytes();
                            for (i, &byte) in bytes.iter().enumerate() {
                                memory.insert(off + 32 * k + i, byte);
                            }
                        }
                    }
                }
            }
            Op::Env(pops) => {
                for _ in 0..pops {
                    let _ = pop!();
                }
                // Replay the witnessed env value (in execution order).
                let value = env_inputs
                    .get(*env_cursor)
                    .cloned()
                    .unwrap_or_else(Word::zero);
                *env_cursor += 1;
                stack.push(value);
            }
            Op::Invalid => return (Halt::Invalid, overflowed),
            Op::Unsupported(b) => {
                return (
                    Halt::Unsupported(format!("unsupported opcode 0x{b:02x}")),
                    overflowed,
                );
            }
        }
        pc = next_pc;
    }
}

/// Re-runs the program concretely and reports whether the tracked `ADD`/`MUL`
/// instruction at byte offset `watch_pc` **concretely overflows** (unsigned) on
/// this `env`. This is the concrete witness check for an overflow finding: the
/// same predicate (`bv_uaddo`/`bv_umulo`) the solver found feasible, re-evaluated
/// on the lifted concrete operands by the single shared interpreter. Returns
/// `false` if the instruction is never reached before the run halts.
#[must_use]
pub fn overflow_reproduces(
    program: &Program,
    env: &Env,
    watch_pc: usize,
    is_mul: bool,
    step_limit: usize,
) -> bool {
    let mut storage: BTreeMap<[u8; 32], Word> = BTreeMap::new();
    let mut env_cursor = 0usize;
    run_core(
        program,
        env,
        step_limit,
        Some((watch_pc, is_mul)),
        &mut storage,
        &[],
        &mut env_cursor,
    )
    .1
}

/// A shift amount `< 256` as a `u32` (EVM shifts ≥ 256 produce 0 / sign-fill,
/// handled by the caller's `None` arm).
fn small_shift(s: usize) -> Option<u32> {
    if s < 256 { u32::try_from(s).ok() } else { None }
}

fn bool_word(b: bool) -> Word {
    if b { Word::from_u128(1) } else { Word::zero() }
}

fn read_mem(memory: &BTreeMap<usize, u8>, off: &Word, len: &Word) -> Option<Vec<u8>> {
    let o = off.to_usize()?;
    let l = len.to_usize()?;
    if l > 1 << 20 {
        return None;
    }
    Some(
        (0..l)
            .map(|i| memory.get(&(o + i)).copied().unwrap_or(0))
            .collect(),
    )
}
