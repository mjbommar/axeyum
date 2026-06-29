# axeyum-evm

An EVM bytecode symbolic bug-hunter built on Axeyum: find overflow /
assertion-violation bugs in a contract over symbolic calldata, and emit a
**replayable calldata witness** for each bug or a re-checked **no-bug
certificate** when a function is proved safe up to a bound.

The decidable EVM core is `QF_BV`/`QF_ABV` — Axeyum's strongest fragments. 256-bit
words are `BV256`; the hunter symbolically executes raw runtime bytecode with the
[`SymbolicExecutor`] DFS explorer and decides branch feasibility with the pure-Rust
solver.

## Soundness — `DISAGREE = 0`

Every reported bug is **independently re-checked by a from-scratch concrete
interpreter** ([`concrete::run`]): the solver's calldata is run on a separate EVM
emulator and the bug must actually fire. A witness that does not reproduce is a
lowering defect, never a reported finding — it is surfaced as honest `Unknown`.
This is the soundness floor, stress-tested by an adversarial differential fuzz
(`tests/differential_fuzz.rs`): over random bytecode, a concretely-reachable
`REVERT`/`INVALID` is *never* reported `SafeUpToBound`. The fuzz found and we
fixed a real wrong-safe (a bad jump destination was treated as a safe path end).

## What it decides

```rust
use axeyum_evm::{analyze, AnalyzeConfig};

let report = analyze(&bytecode, &AnalyzeConfig::default());
for finding in &report.findings {
    // finding.kind, finding.pc, finding.calldata_witness — a reproducible bug.
}
```

Bug classes: reachable `REVERT` / `INVALID` / Solidity `Panic(0x11)`, and unsigned
`ADD`/`MUL` overflow over symbolic calldata. Modeled, soundly:

- **Symbolic-offset memory & storage** — read-over-write at the frontend (pure
  `QF_BV` `ite`-fold; an optional `MemoryEncoding::WarmArray` uses real
  `select`/`store`).
- **`keccak256`** — fresh symbol + pairwise injectivity, with a real pure-Rust
  `keccak256` concrete oracle (so a witness hinging on an invented hash, not key
  equality, does not reproduce and is not reported).
- **Multi-transaction** sequences (`AnalyzeConfig::max_txs`) with persistent
  storage between calls — finds bugs reachable only across calls (e.g.
  init-then-trigger), with a replay-validated multi-tx witness.
- **Environment opcodes** (`GAS`/`BALANCE`/block context) and **external calls**
  (`CALL`/`DELEGATECALL`/`STATICCALL`) as *witnessed* symbolic inputs, and
  **re-entrancy** (storage is adversarial after a non-static call — the DAO
  threat model).

## Honest limits

- **Bounded**: a step bound per path; deep loops / long paths beyond it →
  `Unknown`, never a false "safe".
- **Havoc → Unknown**: anything unmodeled (unsupported opcodes, unresolved
  symbolic jumps) ends the path as a sound `Unknown`, not a wrong verdict.
- `SafeUpToBound` is a *bounded* guarantee (no bug within the step bound), not
  total correctness; it carries a best-effort re-checked `EvidenceReport`.
- 256-bit `bv_umulo` (MUL overflow) bit-blasts slowly (~2 min) — the MUL example
  is `#[ignore]`d in the default gate.

## Measured

A construction-known capability scoreboard
([`docs/consumer-track/evm/SCOREBOARD.md`](../../docs/consumer-track/evm/SCOREBOARD.md),
`cargo run -p axeyum-evm --example measure_evm`) reports decided/bug-found/safe
per memory-shape class with `DISAGREE = 0`, plus a warm-array-vs-`ite`-fold
scaling comparison.

## Status

The client-side **WASM** delivery surface (the moat vs Python/Haskell +
external-solver incumbents) is blocked on `axeyum-solver` building for `wasm32`
(see `UPSTREAM-FEEDBACK.md` U8). The vs-hevm/halmos differential scoreboard is
install-gated; the `ExternalOracle` seam exists.

[`SymbolicExecutor`]: axeyum_solver::SymbolicExecutor
[`concrete::run`]: crate::concrete::run
