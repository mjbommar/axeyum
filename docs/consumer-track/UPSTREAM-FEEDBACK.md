# Upstream feedback log - for the axeyum core/solver developer

This is the consumer-track diary of bugs, capability gaps, and enhancement
requests for the upstream `axeyum-solver` / `axeyum-ir` maintainer. Consumer
apps such as `axeyum-property`, `axeyum-evm`, and `axeyum-verify` should consume
the solver as a black box; when real application work hits a missing capability,
record the ask here instead of reaching into core internals silently.

Format per entry: severity, area, what the consumer hit, why it matters, the
concrete ask, source, and status.

Status vocabulary:

- `open`: still needs upstream work.
- `partial`: a usable slice landed, but the original upstream capability is not
  fully done.
- `resolved`: the specific consumer-facing ask is addressed; any broader
  follow-up belongs in the normal roadmap.

Last reconciled with `main`: 2026-06-27.

---

## Open / Partial

### U4 - high strategic - proofs/Lean - widen the reconstructable fragment

- **Status:** open.
- **What:** Lean reconstruction coverage has improved substantially on exact
  audited rows, but complete Lean/proof support is still the binding product
  axis. The remaining strategic gap is broader kernel-checkable reconstruction
  beyond the rows already closed by the dominance audit, especially where results
  still go through DRAT or checked evidence rather than direct Lean-kernel terms.
- **Why it matters:** consumer apps sell "proved, with a kernel-checkable
  certificate" as the moat over Z3/cvc5/Kani/angr-style stacks. Every additional
  reconstructed fragment widens that moat for property, EVM, and verifier users.
- **Ask:** keep prioritizing reconstruction of high-value fragments already
  strong on decision rate: BV arithmetic beyond the bitwise/comparison slice,
  array/UF reduction proofs, and linear arithmetic certificates, with exact
  per-instance audit coverage rather than fragment-count claims.
- **Source:** `bench-results/DOMINANCE.md`, `PLAN.md`, and
  `docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md`.

### U6 - high - solver/symexec - true warm incremental arrays/UFs remain open

- **Status:** partial.
- **Consumer measurement (2026-06-27):** the warm memory work below is now
  *measured* end-to-end by the EVM/symexec capability scoreboard
  ([`evm/SCOREBOARD.md`](evm/SCOREBOARD.md), `cargo run -p axeyum-evm --example
  measure_evm`): a construction-known corpus decides 6/6 (incl. symbolic-storage
  and keccak-mapping rows) at DISAGREE=0. This scoreboard is the intended
  arbiter of *special-case folding vs the general warm array/UF theory* — grow
  the corpus with the memory shapes real contracts exercise, and let the
  unknown/fallback rows (not an open-ended fold list) drive which general
  capability is worth building next.
- **What:** the original consumer pain was that `SymbolicExecutor`'s warm path
  refused active array/UF assertions and `Op::Apply` was unsupported by the
  bit-blaster. A usable one-shot route has landed: deferred array/UF assertions
  are scoped, `check_with_memory` / `check_assuming_with_memory` dispatch through
  the full solver, and `SymbolicExecutor` / CFG exploration auto-route array/UF
  queries to that memory-aware path. A narrow warm memory slice also landed for
  syntactic same-index hits, literal-distinct concrete-address store misses,
  constant-array reads, reads over simple array-valued `ite` state merges,
  reads over index-valued `ite`s, selected stores with index-valued `ite`s, and
  reducible symbolic-address
  read-over-write over store chains, including same-index shadowed-store
  pruning before ROW expansion and trivial scalar `ite` / reflexive-equality
  collapse after branch reads simplify: the warm
  solver encodes the simplified BV term while retaining the original memory term
  for replay and assumption-core reporting. A first retained select-congruence slice
  also landed for plain reads over BV-indexed array symbols whose elements are
  Bool or BitVec, including wide/BV256 index or element values:
  `select(a,i)` is abstracted to an internal warm scalar variable, same-array
  reads get scoped congruence lemmas, and SAT models are projected back into
  concrete array entries before replay. Compact BV arrays still use
  `ArrayValue`; wide BV storage-style reads use `GenericArrayValue` so replay
  sees the full wide value. A scalar UF-app sibling now handles Bool/BV
  applications, including BV256 keccak-style argument or result values:
  `f(args)` is abstracted to an internal warm variable, same-function
  applications get scoped congruence lemmas, and SAT models are projected back
  into concrete `FuncValue` entries before replay. Compact Bool/BV<=128
  signatures use the scalar function table; wide-BV signatures use full-value
  entries so replay sees canonical `Value::WideBv`s. The warm ROW simplifier
  also prunes earlier same-index stores shadowed by a later store before
  expanding an undecided symbolic read, so simple write-log shapes do not retain
  dead old values or duplicate equality guards in the warm encoding. It also
  splits conditional read indices before ROW expansion, so
  `select(a, ite(c, i, j))` becomes a scalar branch choice over two ordinary
  reads and can reuse the existing branch-local memory simplifications.
  Selected stores with conditional write indices split the same way before the
  generic symbolic ROW equality, so `select(store(a, ite(c, i, j), v), k)`
  becomes a scalar branch choice over two branch-local store/read terms.
  Trivial scalar `ite`s exposed by memory rewrites collapse too, and the scalar
  cleanup now distributes equality over Bool/BV-valued `ite`s plus folds
  literal-distinct constant equalities, Boolean identity `ite`s, Boolean
  equality-to-constant wrappers, double negation, and Boolean connective
  wrappers including `xor` and implication. Branch reads whose branches
  simplify to the same value do not keep an irrelevant merge condition,
  comparisons like `ite(flag, 1, 0) = 1` collapse to `flag`, symbolic Bool
  readbacks like `select(store(mem, i, p), i) = true` collapse to `p`, and
  predicate-like readbacks such as `select(store(mem, i, p), i) and true` or
  `true => select(store(mem, i, p), i)` drop the connective wrapper; the
  resulting `v = v` tautology, `not true` contradiction, `p and not p`
  contradiction, or `p xor p` contradiction is folded before warm encoding.
  BV-valued readbacks also drop common bitwise wrappers such as all-ones masks,
  zero masks, zero ORs/XORs, self-XORs, and double `bvnot` before warm encoding.
  They now drop common modular arithmetic wrappers too, including add/sub zero,
  self-subtraction, zero-minus-readback, additive inverse pairs, multiply by
  zero/one, and double `bvneg`. Exact division/remainder wrappers now collapse
  for SMT-LIB-total cases too: unsigned division by zero, division by one, zero
  divided by a syntactically nonzero divisor, remainder/modulo by zero or one,
  and self-remainder/self-modulo; signed division by zero and nontrivial
  variable divisors remain ordinary BV terms. Loaded-value bounds checks also
  shed reflexive comparisons and unsigned endpoint facts such as
  `load <u 0`, `0 <=u load`, `load <=u all_ones`, and `load >=u 0`.
  Whole-width extracts and zero-bit `zero_extend` / `sign_extend` wrappers
  around readbacks now collapse too, while partial slices and positive-width
  extensions stay as ordinary BV terms. Exact shift wrappers now collapse as
  well: `bvshl` / `bvlshr` / `bvashr` by zero return the readback, zero shifted
  by any amount returns zero, and all-ones arithmetic-right-shifted by any
  amount remains all ones; nonzero variable shifts and over-shift rewrites stay
  as ordinary BV terms.
  Direct equality between supported BV-indexed Bool/BV array symbols now stays
  warm as a scoped theory fact too: equal-array classes generate cross-array
  select-congruence lemmas for committed assertions and one-shot assumptions,
  and SAT models merge equal arrays before replay. This keeps direct `a = b`
  plus equal-index read conflicts on the warm path, while arbitrary array terms
  and full extensionality still promote.
  `SymbolicMemory` load-equality helpers now use the same automatic warm/memory
  route, so frontend helper calls benefit from the warm slice without losing
  fallback on memory/UF shapes still outside it.
  `SymbolicExecutor::branch` now preflights simplified fork conditions against
  the retained select/UF abstraction coverage too, so plain BV-indexed
  Bool/BV array-symbol reads, including BV256 storage-style reads, and scalar
  Bool/BV UF calls, including BV256 keccak-style calls, stay on warm one-shot
  assumptions instead of jumping straight to the dispatcher.
  Default CFG exploration now uses that auto route too; `memory_aware=true`
  remains the explicit force-dispatch setting.
- **Why it matters:** symbolic memory/storage and keccak-style uninterpreted calls
  are central for EVM and verifier frontends. The one-shot fallback removes a
  frontend footgun and lets consumers keep arrays/UFs in path conditions, and
  the warm memory slice avoids the dispatcher for simple store/read-back path
  constraints, concrete-address store-chain misses, zero-initialized memory
  reads, simple branch-merged memory reads, reducible symbolic-address memory
  reads with same-index shadowed-store pruning, conditional read/write-index
  paths with scalar equality-over-`ite` cleanup, symbolic Bool readback
  equality/connective/xor/implication cleanup,
  BV bitwise/arithmetic/div-rem/comparison/slice-extension/shift readback cleanup,
  direct equal-array symbol facts,
  branch-merged reads whose selected branches
  reduce to the same scalar value plus the reflexive equality/negation cleanup
  exposed by that reduction, plain symbolic-base Bool/BV array loads,
  wide/BV256 storage-style base loads,
  scalar Bool/BV UF calls, wide/BV256 keccak-style UF calls, helper-level load
  branches, reducible CFG memory branches, and fork queries, but general array/UF work still
  rebuilds through the dispatcher instead of retaining warm learned clauses.
- **Ask:** finish the ADR-0030 half: a true warm lazy-array/UF incremental route
  with retained theory clauses / learned lemmas / push-pop reuse. Until that
  exists, document the one-shot fallback as sound but not the final performance
  story.
- **Source:** `STATUS.md` entries "memory-aware incremental assumptions",
  "SymbolicExecutor auto-routes array/UF CFG queries", and
  "Warm same-index ROW admission" / "Warm literal ROW chain admission" /
  "Warm constant-array read admission" / "Warm array-ITE read admission" /
  "Warm symbolic ROW conditional admission" / "Warm ROW same-index shadow
  pruning" / "Warm array-ITE same-readback guard pruning" /
  "Warm reflexive memory tautology pruning" /
  "Warm conditional-index read splitting" /
  "Warm conditional-write-index read splitting" /
  "Warm scalar ITE equality cleanup" /
  "Warm Bool readback equality cleanup" /
  "Warm Bool connective cleanup" /
  "Warm Bool xor/implication cleanup" /
  "Warm BV bitwise readback cleanup" /
  "Warm BV arithmetic readback cleanup" /
  "Warm BV div/rem readback cleanup" /
  "Warm BV comparison readback cleanup" /
  "Warm BV slice/extension readback cleanup" /
  "Warm BV shift readback cleanup" /
  "Warm BV-array select-congruence admission" /
  "Warm wide-BV array select projection" /
  "Warm direct array-equality admission" /
  "Warm scalar UF congruence admission" /
  "Warm wide-BV scalar UF projection" /
  "Warm branch routing recognizes retained select/UF slices";
  `docs/plan/track-4-usecases-frontend/P4.1` / `P4.2` notes.

### U7 - medium - perf/encoding - deep store/read-over-write scaling remains open

- **Status:** partial, subsumed by U6 for the main fix; frontend write-log
  mitigation landed on 2026-06-27.
- **What:** consumers previously had to encode symbolic memory reads as
  read-over-write `ite` chains, with one 256-bit equality guard per prior store.
  The memory-aware solver route lets frontends keep array assertions in path
  conditions, and `SymbolicMemory` now has a write-log helper that drops
  same-index shadowed writes, skips writes at literal-distinct addresses for a
  specific read, elides exact-hit guards, and emits guards only for remaining
  writes that may alias. The upstream warm ROW simplifier now mirrors part of
  that normalization by dropping syntactically shadowed same-index stores before
  expanding undecided symbolic reads and by splitting conditional read indices
  and conditional write indices before ROW expansion when the selected branches
  reduce through the warm slice. Deep store-chain scaling is still the
  array-solver performance problem unless the warm lazy array path reuses
  structure and instantiates ROW facts on demand.
- **Why it matters:** EVM paths with many storage writes can still make per-read
  formulas grow linearly or worse if the frontend has to materialize store-chain
  guards.
- **Ask:** prefer the native lazy-array route from U6. The interim
  frontend-facing helper exists for syntactic/concrete same-index shadowing and
  read-specific literal-distinct pruning; next upstream work is still retained
  lazy-array/UF theory clauses, not more frontend lowering.
- **Source:** `docs/plan/track-2-theories/P2.2-arrays-lazy.md`,
  `docs/plan/track-4-usecases-frontend/P4.1-warm-lazy-memory.md`, and the EVM
  memory notes when that app track is active.

---

## Resolved / Superseded

### U1 - medium - proofs/Lean - `prove_unsat_to_lean_module` shape sensitivity

- **Status:** resolved on 2026-06-27.
- **Original ask:** normalize/flatten conjunctions and strip double negation
  inside the Lean reconstructor so consumer callers do not have to pre-massage
  `hyps /\ not goal` queries.
- **Resolution:** `prove_unsat_to_lean_module` and the SOS Lean-module helper now
  retry with a normalized assertion spine when direct reconstruction declines:
  top-level `BoolAnd` assertions are split and repeated top-level double
  negations are stripped. Focused regressions include normalized QF_UFBV and
  array read-over-write examples checked by a real Lean binary.
- **Source:** `STATUS.md` entry "Lean proof input-shape normalization";
  `docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md`.

### U2 - medium - perf/BV - 256-bit `bv_umulo` bit-blast was too slow

- **Status:** resolved for the named consumer pain point on 2026-06-27.
- **Original ask:** avoid building a doubled-width BV512 multiplication term for
  BV256 unsigned multiply-overflow checks.
- **Resolution:** `TermArena::bv_umulo` now uses the word-width threshold
  encoding `a > all_ones / b` under SMT-LIB total `bvudiv` semantics. The BV256
  shape regression asserts one `BvUdiv`, no `BvMul`, and no doubled-width
  intermediate. Arbitrary wide multiplication constraints remain broader P1/P2
  reduction work, but this closes the EVM `umulo` overflow-shape blocker.
- **Source:** `STATUS.md` entry "Word-width `bvumulo` encoding for wide BV
  overflow checks"; `docs/plan/track-1-engine/P1.2-preprocessing.md`.

### U3 - low - ergonomics - no first-class counterexample minimization

- **Status:** resolved for Bool / unsigned-BV<=127 / Int and property-facing
  proof/evidence APIs on 2026-06-27.
- **Original ask:** expose an optional model-minimization pass callable from
  proof/evidence paths instead of requiring every consumer SDK to shrink models
  itself.
- **Resolution:** `minimize_model`, `produce_evidence_minimized`, and
  `prove_minimized` now return replay-checked minimized models/countermodels
  over selected Bool/BV/Int symbols, with signed-BV objective metadata surfaced
  through the property SDK. Broader objective support for wide BV, Real, arrays,
  datatypes, and uninterpreted-carrier values remains ordinary P4.3 backlog.
- **Source:** `STATUS.md` entries "First-class counterexample minimization
  helper" and "Minimized counterexamples surfaced through proof/evidence APIs".

### U5 - medium - proofs/Lean - QF_ABV array proofs emitted no Lean module

- **Status:** resolved for the measured exact QF_ABV dominance row on
  2026-06-25, with follow-up normalizer coverage on 2026-06-27.
- **Original ask:** extend Lean reconstruction to the array-elimination /
  read-over-write path so array proofs used by memory/storage frontends can
  carry Lean modules.
- **Resolution:** the exact QF_ABV audit is now closed at 169/169 dominant with
  Lean unsat 85/85. The proof path includes checked `ArrayAxiom` /
  read-over-write lanes and real-Lean reconstruction for normalized array
  read-over-write axiom refutations.
- **Source:** `bench-results/DOMINANCE.md`; `STATUS.md` entry "exact ABV
  dominance row closed"; `docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md`.

---

## Notes

- Items that are purely consumer-side work, such as macro parsing, EVM bytecode
  lifting, Rust frontend syntax, replay fixture shape, or per-app scoreboards,
  belong in each app's local `STATUS.md` / `PLAN.md`.
- Keep this file honest. If core work lands, move the corresponding item to
  "Resolved / Superseded" with concrete evidence and leave any broader ambition
  in the roadmap instead of preserving a stale blocker.
