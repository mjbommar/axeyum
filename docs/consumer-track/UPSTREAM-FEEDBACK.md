# Upstream feedback log — for the axeyum core/solver developer

A running diary of bugs / errors / capability gaps / enhancements the **consumer
track** (apps `axeyum-property`, `axeyum-evm`, `axeyum-verify`) wants the upstream
**axeyum-solver / axeyum-ir** maintainer to action. The consumer track consumes the
solver as a black box and **never reaches into the core** — every friction point we
hit while building real applications is logged here instead, as an actionable item.

Format per entry: **severity** (blocker / high / medium / low) · **area** · what we
hit · why it matters (which app, what it blocks) · the concrete ask · source.
Status: `open` unless noted.

---

## Open

### U1 · medium · proofs/Lean · `prove_unsat_to_lean_module` is shape-sensitive
- **What:** `prove_unsat_to_lean_module` reconstructs a `QF_BV` `unsat` to a Lean
  module only when the contradiction is supplied as *separate top-level conjuncts*
  (e.g. `[a≤b, b<a]`); a single `and(..)` term, or a `not(not(..))` wrapper, is
  declined (verified empirically).
- **Why it matters:** `evidence::prove` appends one `not(goal)` assertion, so the
  natural `hyps ∧ ¬goal` query is often *not* in the accepted shape. The
  `axeyum-property` SDK works around it **client-side** (flatten top-level `BoolAnd`,
  strip `¬¬` before the best-effort Lean attempt) — but this caps the headline
  **Lean-cert coverage at 8.3%** on the property scoreboard, and every consumer app
  that wants a Lean certificate inherits the limit.
- **Ask:** normalize/flatten (split conjunctions, strip double-negation, push the
  query into the reconstructable normal form) *inside* the reconstructor, so callers
  don't have to pre-massage the query.
- **Source:** `docs/consumer-track/property/STATUS.md`; measured in `property/SCOREBOARD.md`.

### U2 · medium · perf/BV · 256-bit `bv_umulo` bit-blast is slow (~2 min)
- **What:** unsigned multiply-overflow on `BV256` (`bv_umulo`) takes ~2 minutes to
  bit-blast, so the `axeyum-evm` MUL-overflow example is `#[ignore]`d in the default
  gate.
- **Why it matters:** EVM arithmetic is 256-bit; MUL-overflow is a core bug class.
  At 2 min/query it's impractical for a real-contract sweep.
- **Ask:** the native-core / word-level-reduction work on the perf track should target
  wide-multiplier overflow; a word-level `umulo` would make 256-bit overflow checks
  interactive.
- **Source:** `docs/consumer-track/evm/STATUS.md`.

### U3 · low · ergonomics · no first-class counterexample minimization
- **What:** a `Disproved(Model)` is not minimized; there's no "smallest failing input"
  helper.
- **Why it matters:** consumer UX — a minimal counterexample is far more useful to a
  user than an arbitrary one. The SDK can shrink client-side (via `SymbolicExecutor`
  / `minimize_*`), but a core helper would be cleaner and shared.
- **Ask:** an optional model-minimization pass (lexicographic / by-magnitude) callable
  from `prove`/`produce_evidence`.
- **Source:** iteration-2 research synthesis §B notes.

### U4 · high (strategic) · proofs/Lean · widen the reconstructable fragment
- **What:** Lean reconstruction coverage is narrow outside bitwise QF_BV: per
  `DOMINANCE.md`, QF_LIA ~25%, QF_LRA ~0%, QF_NRA ~6%, and QF_BV mul/rem/shift go
  through DRAT, not the kernel.
- **Why it matters:** the consumer apps' differentiating "Lean-checkable certificate"
  is only as broad as the reconstructor. Widening it directly widens every app's
  cert-coverage headline (the moat).
- **Ask:** prioritize Lean reconstruction of QF_BV arithmetic (carry-chain add/mul,
  shifts) and the linear-arith certificates — the highest-leverage cert frontier for
  consumer apps.
- **Source:** `bench-results/DOMINANCE.md`; consumer-track decision doc.

### U5 · medium · proofs/Lean · QF_ABV array proofs emit no Lean module
- **What:** the property scoreboard's array `should-prove` rows
  (`array-store-select-roundtrip`, `array-store-other-unchanged` — the
  read-over-write axioms over `BvArray<8,4>`) `prove` and the in-process
  `EvidenceReport` re-checks, but `prove_unsat_to_lean_module` declines them, so
  `to_lean_module()` is `None`. Empirically QF_ABV refutations are outside the
  Lean-reconstructable fragment even when the BV sub-reasoning would be.
- **Why it matters:** arrays are the natural model for consumer-app memory /
  storage / fixed buffers (App B `BvArray`, App C slices, App A EVM storage). The
  read-over-write/extensionality lemmas are exactly the proofs a user most wants
  a Lean certificate for, and right now none of them carry one — the array
  `should-prove` rows are the only proved rows on the scoreboard with `Lean = no`
  that are *not* arithmetic.
- **Ask:** extend Lean reconstruction to the array-elimination path — emit a Lean
  module for a QF_ABV `unsat` whose certificate is built via `eliminate_arrays` /
  `certify_array_elim_unsat` (read-over-write + Ackermann are self-evidently valid
  theory rewrites; the residual is QF_BV, already partly reconstructable).
- **Source:** `docs/consumer-track/property/SCOREBOARD.md` (array rows);
  `axeyum-property` `BvArray` over `Sort::Array`.

### U6 · high · solver/symexec · `SymbolicExecutor` cannot reason about arrays or UFs
- **What:** the warm incremental path behind `SymbolicExecutor` (`branch` / `assume`
  / `model`, via `IncrementalBvSolver::check`) **refuses** any active array
  assertion (`select`/`store`) — `solve_with_extra` returns `Unsupported` — and the
  bit-blaster lists `Op::Apply` (uninterpreted functions) among its unsupported ops.
  So a DFS explorer that wants symbolic-array memory or an uninterpreted keccak in
  its *live, incremental* path condition cannot use the array theory / UF at all;
  only the one-shot `check_with_memory` decides arrays, and it is not incremental.
- **Why it matters:** symbolic-offset memory/storage and keccak-keyed mappings are
  THE high-value EVM (App A) targets, and the same wall blocks App B/C buffer
  reasoning. App A Phase 2 worked around it by lowering both to **pure QF_BV**
  (frontend read-over-write `ite`-fold for memory/storage; fresh-symbol + pairwise
  `eq` injectivity for keccak) — sound and it ships, but it (a) loses the solver's
  array decision procedure, (b) makes every symbolic read O(writes) in `ite` depth,
  and (c) cannot byte-slice a symbolic-offset word write for a keccak preimage.
- **Ask:** a warm/incremental array+UF path for `SymbolicExecutor` — either a lazy
  array axiom instantiation in the incremental engine (ADR-0030 is named for this)
  or an incremental wrapper over `check_with_memory` that keeps push/pop scopes.
  Even incremental `Op::Apply` (Ackermann-on-demand) would let consumers keep
  keccak uninterpreted instead of re-deriving injectivity by hand.
- **Source:** `crates/axeyum-solver/src/incremental.rs` (`solve_with_extra` array
  refusal; `check_with_memory`); `crates/axeyum-bv/src/lib.rs` (`Op::Apply`
  unsupported); `crates/axeyum-evm/src/symbolic.rs` Phase-2 workaround.

### U7 · medium · perf/encoding · `ite`-chain read-over-write scales poorly for deep stores
- **What:** the frontend read-over-write encoding a consumer must use (see U6)
  produces a `select(k)` term of `ite` depth = number of prior stores, each guard a
  256-bit `eq`. For a contract with many `SSTORE`s on a path the per-read CNF grows
  linearly and reads compound; there is no structure-sharing of the disequality
  chain the way a real array solver's congruence closure gives.
- **Why it matters:** it caps how deep a path App A can explore before the
  bit-blast cost dominates — exactly the QF_BV/QF_ABV fragment the project measures
  as dominant, so leaving the array DP unused on the incremental path forfeits that
  edge for symbolic-state contracts.
- **Ask:** (subsumed by U6) a native incremental array path; failing that, a helper
  that canonicalizes/dedups a frontend write-list into a minimal `ite` chain
  (drop shadowed concrete-key writes, share guards).
- **Source:** `crates/axeyum-evm/src/symbolic.rs` `fold_word_writes`.

---

## Resolved / superseded
- *(none yet)*

> Note: items that are **consumer-side** work (macro array parsing, symbolic-offset
> EVM memory, `usize` width mapping, CFG/BMC adapters, …) are tracked in each app's
> `STATUS.md`, not here — this log is **core/solver-only**.
