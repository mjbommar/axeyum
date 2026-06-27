# axeyum-evm — PLAN

> **App A**, the flagship. A pure-Rust EVM bytecode **symbolic bug-hunter**: take
> raw runtime bytecode + a tiny harness, symbolically execute it, and find
> arithmetic-overflow / assertion-violation (REVERT/INVALID/`Panic(0x11)`) bugs
> over symbolic calldata — emitting a **replayable calldata witness** on a bug and
> a **Lean/Carcara-checkable "no-bug" certificate** when a function is proven safe.
> Full scoping: [02-research-synthesis §A](../02-research-synthesis.md).

## Goal (worked backwards)
A security auditor points the tool at a contract's runtime bytecode (+ a one-line
"which function / what's the bad state" harness) and gets: a concrete exploit
input, or "no bug up to bound K" *with a certificate they can independently check*
— running natively or **in a browser tab** (no install, no external solver). That
last clause is the moat: halmos (Python+Z3) and hevm (Haskell) shell out to
external solver binaries and ship **zero** checkable proofs; neither runs client-side.

## Why it's tractable / unblocked
The decidable EVM core *is* QF_BV/QF_ABV — axeyum's strongest measured rows
(88–100% dominant). Already present in `axeyum-solver`: `BV256` (width cap 65536),
the full BV op set, **native overflow predicates** `bv_uaddo/usubo/umulo`, symbolic
array memory/storage (read-over-write + Ackermann, no 2²⁵⁶ blowup), `declare_fun`
for uninterpreted **keccak**, the `SymbolicExecutor` DFS explorer, and
`produce_evidence`/`prove_unsat_to_lean_module`. **No solver change is needed.**

## MVP scope
- **Frontend = a stack-machine interpreter** (new crate `axeyum-evm`) over the
  ~140 must-have opcodes: arith/logic (ADD…SIGNEXTEND), stack (PUSH/DUP/SWAP/POP),
  concrete-offset memory (MLOAD/MSTORE/MSTORE8), control (JUMP/JUMPI/JUMPDEST/
  STOP/RETURN/**REVERT/INVALID**), calldata (CALLDATALOAD/SIZE/COPY, CALLVALUE,
  CALLER), storage (SLOAD/SSTORE over one `BV256→BV256` array). Lower each op to IR
  terms; memory = `BV256→BV8` array, calldata = symbolic byte buffer.
- **Havoc the hard parts → `PathStatus::Unknown`** (sound, never wrong-pruned, same
  as halmos/hevm defer): KECCAK256 = fresh `declare_fun (BV*)->BV256`;
  CALL/DELEGATECALL/CREATE/EXTCODE* = havoc return + (conservatively) touched
  storage; GAS = unconstrained symbolic word; LOG* = no-op.
- **Encode the EVM semantics caveats in the frontend** (not solver issues): EVM
  `DIV/MOD-by-0 = 0` (`ite` guard — differs from SMT-LIB all-ones), ADDMOD/MULMOD at
  512-bit then `bvurem`, symbolic `EXP` bounded/havoc, constant `EXP` unrolled.
- **Drive with `SymbolicExecutor`:** at each JUMPI `branch`; fork feasible
  directions; flag a bug when REVERT/INVALID/`Panic(0x11)` or a `bv_uaddo`/`bv_umulo`
  overflow predicate is path-feasible; emit `model()` as replayable calldata.

## Phases (each compiles, gates, DISAGREE=0 vs an oracle on its slice)
- **Phase 1:** the must-have opcode interpreter + `SymbolicExecutor` driver;
  overflow + assertion-violation on single-contract functions over symbolic
  calldata; replayable-witness output. Bench on hand-built overflow/assert
  micro-contracts. Reuse App B's `Certificate` plumbing for the no-bug proof.
- **Phase 2:** keccak-injectivity constraints (pairwise `b1≠b2 ⇒ keccak(b1)≠keccak(b2)`
  + slot gap — emitted over `declare_fun`, the halmos/hevm precision trick) and
  per-mapping storage decomposition; symbolic-offset memory (perf-gated).
- **Phase 3:** multi-tx invariants via `bounded_model_check_with_memory`; WASM
  in-browser surface (the differentiator); the committed vs-hevm/halmos scoreboard.

## Success criteria
1. **Clean** — `axeyum-evm` new crate, `#![forbid(unsafe_code)]`, idiomatic.
2. **Functional** — finds real overflow/assert bugs on real bytecode, emits a
   replayable calldata witness; proves no-bug-up-to-K with a re-checked cert.
3. **SOTA-measured** — corpus = SWC registry + halmos examples + overflow
   micro-contracts; metric = bugs found / safe proved vs **hevm** (raw-bytecode
   CAV'24) + **halmos**, **DISAGREE = 0**; differentiator = **proofs carried** (they
   ship zero).
4. **Certifying where it can** — no-bug results carry the App-B `Certificate`
   (`EvidenceReport` always; Lean module when in fragment).

## Honest moat caveat
Edge is **trust + delivery** (checkable proof + WASM client-side), NOT out-running
Bitwuzla on keccak-saturated queries. The product wedge: "the verifier whose *pass*
you can independently check, running anywhere."

## Coordination
New crate `crates/axeyum-evm`, consumer-track worktree, consumes axeyum-solver as a
black box. Capability wish: a reusable `bv_*_overflows` helper (shared with App C) —
filed as a note, not a core reach-in.
