# axeyum-evm — STATUS

Live tracker for the EVM symbolic bug-hunter (App A). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-26 — Phase 2 LANDED.** Symbolic-offset memory/storage (frontend
  read-over-write), keccak-injectivity, the real `SafeUpToBound` refutation, App-B
  reproduction rendering, and a `SHA3`/keccak256 oracle — all gates green
  (fmt + clippy `-D warnings` pedantic + tests + doc). See "What Phase 2
  implements" below; Phase-1 summary retained underneath.
- **2026-06-25 — Phase 1 LANDED (end-to-end).** The crate is a working symbolic
  bug-hunter: decode → symbolic interpreter (BV256) → `SymbolicExecutor` DFS →
  feasible-bug detection → lifted concrete calldata witness → **concrete
  re-execution revalidation** (DISAGREE=0). All gates green
  (fmt + clippy `-D warnings` pedantic + tests + doc).

## What Phase 2 implements
- **Symbolic-offset storage + memory (the keystone).** `SLOAD`/`SSTORE` with a
  symbolic key and `MLOAD`/`MSTORE` with a symbolic word offset are no longer
  havoc'd: each store appends to an ordered write-list, each load folds
  `ite(key == kᵢ, vᵢ, base)` newest-first → **pure QF_BV** (`eq`/`ite`), so the
  warm `SymbolicExecutor` reasons about it (its bit-blast path refuses array
  `select`/`store` — see UPSTREAM U6). Last-write-wins-by-key matches the concrete
  `BTreeMap` oracle exactly. Concrete-key/offset fast-paths retained. `MSTORE8` at
  a symbolic offset stays sound `Unknown` (sub-word granularity).
- **Keccak (`SHA3`, 0x20) with injectivity.** Hash result = a **fresh BV256**
  symbol; for each pair of same-width hashes on a path we assert
  `argᵢ == argⱼ ⇔ resultᵢ == resultⱼ` (pure QF_BV — the halmos/hevm trick, done in
  the warm fragment because `Op::Apply` is unsupported there, U6). A new
  pure-Rust `keccak256` (`src/keccak.rs`, no C dep) is the concrete oracle's
  *real* hash, so a keccak-mapping witness re-checks under the actual digest
  (DISAGREE=0). Concrete-length preimages ≤ 128 B; empty/oversized/symbolic-length
  → sound `Unknown`.
- **Real `SafeUpToBound` proof (item #3).** The explorer now records each refuted
  bug-reachability obligation `pathᵢ ∧ bug_predicateᵢ`; the no-bug certificate is
  `produce_evidence` over their disjunction (UNSAT), re-checked before hand-out —
  the actual "no bad state reachable up to the bound" refutation, not the Phase-1
  `0==1` placeholder. Empty obligation set ⇒ vacuous `false` (honest, structural).
- **Reproduction rendering (item #4).** `reproduce::reproduction_source` turns any
  `Finding` into a runnable, self-contained `#[test]` via App-B's shared
  `render_reproduction_test` (`Finding: Witness`). The rendered test re-runs the
  witness through the concrete oracle — the frozen DISAGREE=0 re-check. A committed
  generated example (`tests/generated_repro.rs`) compiles and passes.
- **More opcodes:** `SHA3` added to decode + both interpreters.

## Phase-2 worked examples (tests/phase2_examples.rs) — all DISAGREE=0
- **D** symbolic-key storage round-trip: `storage[k]=v; if storage[lk]==0xdead
  revert` → `Revert` found with `lk==k ∧ v==0xdead`; concretely reverts. ✅
- **D-safe** load a cold constant slot → no finding + real `SafeUpToBound` cert. ✅
- **E** keccak `mapping(uint=>uint)` alias: write sentinel under `keccak(k1.0)`,
  read under `keccak(k2.0)`, revert on sentinel → `Revert` found with `k1==k2`;
  **reproduces under real keccak256** (the concrete oracle), confirming the
  injectivity reasoning is sound, not an artifact of the UF model. ✅
- **F** a finding renders a runnable reproduction `#[test]`. ✅
- **generated_repro.rs** the rendered Example-D test, committed and passing. ✅

## Public API (`crates/axeyum-evm/src/lib.rs`)
- `analyze(bytecode: &[u8], cfg: &AnalyzeConfig) -> AnalysisReport`
- `AnalyzeConfig { detect_overflow, detect_assertions, max_steps, solver }`
- `AnalysisReport { findings: Vec<Finding>, verdict: Option<Verdict> }`
- `Finding { kind, pc, calldata_witness, callvalue, caller, concrete_halt }`,
  `FindingKind ∈ {Revert, Invalid, AddOverflow, MulOverflow}`
- `Verdict ∈ { SafeUpToBound { evidence: Option<Box<EvidenceReport>> },
  InconclusiveDueToUnknown }` — the no-bug path carries a re-checked App-B
  `EvidenceReport` (best-effort); an undecided path is honest `Unknown`, never a
  wrong "safe".
- Modules `opcode` (decode), `word` (256-bit `Word` over `WideUint`),
  `concrete` (the soundness-oracle interpreter), `symbolic` (the driver).

## What Phase 1 implements
- **Opcode subset** (lowered to BV256 IR + a mirror concrete interpreter):
  STOP, ADD/MUL/SUB/DIV/SDIV/MOD/SMOD/ADDMOD/MULMOD, LT/GT/SLT/SGT/EQ/ISZERO,
  AND/OR/XOR/NOT/BYTE(havoc'd, sym side)/SHL/SHR/SAR, CALLVALUE/CALLER/
  CALLDATALOAD/CALLDATASIZE, POP/MLOAD/MSTORE/MSTORE8/SLOAD/SSTORE,
  JUMP/JUMPI/JUMPDEST/PC, PUSH1-32/DUP1-16/SWAP1-16, RETURN/REVERT/INVALID.
- **Semantics caveats encoded**: DIV/MOD/SDIV/SMOD-by-0 = 0 via `ite` (not
  SMT-LIB all-ones); ADDMOD/MULMOD at 512-bit then truncate.
- **Havoc → sound Unknown**: KECCAK/CALL/GAS/LOG/any unsupported opcode and any
  unresolved symbolic memory/jump offset terminate the path as Unknown
  (`saw_unknown`), never wrong-pruned. A no-finding result with `saw_unknown` is
  reported as `InconclusiveDueToUnknown`, not `SafeUpToBound`.
- **Bug = path-feasible** REVERT / INVALID, or a feasible `bv_uaddo`/`bv_umulo`
  on a tracked ADD/MUL. On a bug, `model()` is lifted to concrete calldata +
  callvalue + caller.
- **DISAGREE=0 gate**: every reported witness is re-run through the independent
  concrete interpreter; a witness that does not reproduce yields NO finding
  (treated as a lowering defect → inconclusive), never a false positive.

## Worked examples (tests/worked_examples.rs)
- **A** ADD-overflow `x+y` → `AddOverflow` finding; witness concretely overflows. ✅
- **A2** MUL-overflow `x*y` → `MulOverflow` finding; witness concretely overflows.
  ✅ but `#[ignore]`d in the default gate (256-bit `bv_umulo` bit-blast ~2 min;
  run `cargo test -p axeyum-evm -- --ignored`).
- **B** safe `x & 0xff` → no finding + re-checked `SafeUpToBound` certificate. ✅
- **C** `require(x != 0)` → reachable `Revert` finding; all-zero witness concretely
  REVERTs; sibling test confirms the `x != 0` path halts cleanly (genuine fork). ✅
- All non-ignored tests pass in ~0.02s; DISAGREE=0.

## Capability gaps / notes (no core edits)
- **Array theory is unused on the incremental path** (filed UPSTREAM U6/U7).
  Symbolic memory/storage is reasoned about via a **frontend** read-over-write
  `ite`-fold (pure QF_BV), not the solver's array DP, because the warm
  `SymbolicExecutor` refuses `select`/`store` and `Op::Apply`. Sound and shipping,
  but per-read cost is O(writes) in `ite` depth (U7). Keccak is likewise
  fresh-symbol + manual injectivity rather than an uninterpreted `declare_fun`.
- **Symbolic-offset `MSTORE8` and byte-slicing a symbolic-offset word write for a
  keccak preimage stay `Unknown`** (sub-word / non-constant byte aliasing is below
  the word-granular model). The common 32-/64-byte mapping pattern is covered.
- **Jump targets** still require a concrete destination (symbolic `JUMP`/`JUMPI`
  dest → `Unknown`). Dynamic dispatch is future work.
- **256-bit MUL overflow is bit-blast-expensive** (~2 min). Capability is real;
  perf is gated on the native-core/word-level reduction work, not this crate.
- **BYTE** is havoc'd on the symbolic side (endianness not yet encoded); concrete
  side implements it. Add the symbolic encoding when an example needs it.

## Next actions (Phase 3)
1. Multi-tx invariants via `bounded_model_check_with_memory` (sequence of calls,
   persistent storage between txs).
2. CALL/DELEGATECALL/CREATE/EXTCODE* modeling (havoc return + touched storage) so
   real dispatched contracts explore further before going `Unknown`.
3. WASM in-browser surface (the differentiator) + the vs-hevm/halmos scoreboard.
4. Reduce the `ite`-fold cost (UPSTREAM U6/U7) — pursue a warm array path or a
   write-list canonicalizer.

## Gates / discipline
`#![forbid(unsafe_code)]`; fmt + clippy `-D warnings` + tests per increment; build
caps (`-j4`, `./scripts/mem-run.sh`); new-crate-only; DISAGREE=0 once a corpus exists.

## Changelog
- **2026-06-25** — PLAN/STATUS written; crate scaffold queued behind App B.
- **2026-06-25** — Phase 1 landed: opcode interpreter (sym + concrete oracle),
  `SymbolicExecutor` DFS driver, overflow + REVERT/INVALID detection, lifted
  concrete witnesses revalidated by concrete re-execution (DISAGREE=0), App-B
  certificate hook on the no-bug path. 5 worked examples (4 fast + 1 ignored MUL),
  all green; fmt + clippy `-D warnings` + doc clean.
- **2026-06-26** — Phase 2 landed: symbolic-offset storage + word-memory via
  frontend read-over-write (`ite`-fold, pure QF_BV); `SHA3`/keccak with fresh-symbol
  + pairwise injectivity; pure-Rust `keccak256` concrete oracle; real
  `SafeUpToBound` refutation (disjunction of refuted reachability obligations,
  re-checked); App-B reproduction rendering (`Finding: Witness`) + committed
  generated test. 4 new worked examples (D storage round-trip, D-safe, E keccak
  mapping reproduces under real keccak256, F reproduction render) + the generated
  repro, all green; DISAGREE=0. Filed UPSTREAM U6 (no warm array/UF path) and U7
  (`ite`-chain scaling). fmt + clippy `-D warnings` pedantic + tests + doc clean.
