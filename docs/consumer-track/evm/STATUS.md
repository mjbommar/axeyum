# axeyum-evm — STATUS

Live tracker for the EVM symbolic bug-hunter (App A). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — Phase 1 LANDED (end-to-end).** The crate is a working symbolic
  bug-hunter: decode → symbolic interpreter (BV256) → `SymbolicExecutor` DFS →
  feasible-bug detection → lifted concrete calldata witness → **concrete
  re-execution revalidation** (DISAGREE=0). All gates green
  (fmt + clippy `-D warnings` pedantic + tests + doc).

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
- **Symbolic memory/storage/jump offsets are deferred to Phase 2.** Phase 1
  resolves only *syntactically constant* offsets/keys (`const_word`); a symbolic
  offset/key/jump-target is havoc'd to Unknown (sound). This covers the
  dispatcher-style examples but not symbolic-index arrays. PLAN named array
  memory/storage; the real `SymbolicExecutor` path is QF_BV-only here, so concrete
  offsets keep us in the fast, certain fragment. Generalize via the array path in
  Phase 2.
- **256-bit MUL overflow is bit-blast-expensive** (~2 min). Capability is real;
  perf is gated on the native-core/word-level reduction work, not this crate.
- **`safety_evidence` is a placeholder certificate** (a checked `0==1` unsat
  carrier) wired through the App-B `produce_evidence` + re-`check`. Phase 2 ties it
  to the actual bug-reachability refutation.
- **BYTE** is havoc'd on the symbolic side (endianness not yet encoded); concrete
  side implements it. Add the symbolic encoding when an example needs it.

## Next actions (Phase 2)
1. Symbolic-offset memory + per-mapping storage decomposition (array path).
2. Keccak-injectivity constraints over `declare_fun` (halmos/hevm precision trick).
3. Tie `SafeUpToBound` evidence to the real reachability query; multi-tx invariants.

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
