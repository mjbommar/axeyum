# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

> Two lanes write here. The **solver/engine lane** owns *Current focus* below.
> The **consumer-integration lane** owns its own section (immediately following)
> so the two never edit the same lines. See
> [PLAN.md § Consumer-track integration](PLAN.md#consumer-track-integration-2026-06-27-converge-the-apps-onto-main).

## Project reality check (2026-06-28)

**Measured status vs the [north star](PLAN.md#where-we-are-vs-the-north-star--measured-reality-check-2026-06-28):
soundness holding, parity not yet reached, the road there fully mapped.** Sound
everywhere measured, dominant on a growing fragment set, with the remaining
decide-rate / performance / proof-coverage work decomposed into sized,
exit-criteria'd tracks we advance one increment at a time.
- **Soundness:** `DISAGREE = 0` across all 35 measured baselines (the
  oracle-compared count lives in the generated scoreboard) — *holding*. (Two consumer-app wrong-safes found by new fuzzes
  + fixed this session.)
- **Decide-rate (the central gap):** see the generated
  [SCOREBOARD](bench-results/SCOREBOARD.md) totals (~73% as of
  2026-07-07 — the scoreboard is authoritative; this line links rather than
  hand-copies because hand-copied totals rotted twice), 0–100% across
  divisions, **19/35 decide-strong**. Z3/cvc5 decide more on most fragments.
- **Performance:** the **first committed PAR-2 head-to-head exists**
  (`582ecba8`, public QF_BV p4dfa, lazy-vs-eager at 3s/20s, DISAGREE=0): lazy
  weakly dominates (7>4 decided at 20s) but `lazy_ops_total=0` everywhere —
  the edge is inherited word-level preprocessing, not CEGAR, and Z3 still
  decides all 113 in ≤1s. Parity remains open; the measured lever is
  reduction depth. No parity claim without these numbers widening.
- **Lean:** narrow (~15/35 rows audit-eligible; trusted-reduction ledger ≠ 0;
  tactic backend P3.7 unbuilt).
- **Dominance:** **23 fragments** with audited `dominant%` — the real, defensible
  claim.

**Where to continue (toward the mission) — updated 2026-07-01/02 after a heavy
landing wave.** The two theory frontiers **advanced from planning into landed
increments**:
- **Strings (P2.7): Phase A is essentially DONE** — A.1a/b landed (first-class
  `Sort::Seq` + seq ops), and **A.2 landed (ADR-0052)**: the `bv2nat`-linear→BV
  equivalence blast + a parser-built **unbounded length abstraction** + the
  bounded-string `unsat` gate at every `solve_smtlib` entry point (and the bench
  harness). The Gap-10 `str.len`-unsat marker **decides**, and a **measured
  pre-existing wrong-unsat class vs Z3** (bound-bite via length atoms,
  cross-width `prefixof`, long-forcing regex, symbolic over-bound `substr`, the
  lexicographic gap) was found and repaired — string fuzz DISAGREE=0 with an
  extended over-bound generator. Next: Phase B (word-level solver; the gate's
  `unknown`s are its routing signal). The scoreboard re-run landed
  (`cf923084`): QF_S 48/134, QF_SEQ 26/33, QF_SLIA 11/50 — 23 prior `unsat`s
  are honest `unknown`s, **two of them on declared-`sat` instances** (hidden
  wrong verdicts, repaired). **UPDATE 2026-07-07: those downgrades are largely
  recovered — QF_S is now 87/134 (65%), QF_SEQ 26/33, QF_SLIA 18/50 (36%)** after
  Phase B/C/D, lex-order, the code↔LIA bridge, #49 (membership-over-concat), and
  #55 (concat emptiness/joint search). The LenAbs length/LIA bridge (#53) and
  concat follow-up (#55) are both landed; the remaining string residue is
  extended-function/sequence machinery plus the research-gated Nielsen class.
- **Nonlinear (P2.5): there is NO new `axeyum-poly` crate** (ADR-0044 keeps the
  primitives in `axeyum-ir`); the FM→simplex keystone (P1.9) is complete, the
  Boolean case-split + sign-refutation landed, and **coprime-split CAD
  projection landed (98719094) and `/0` division witnesses followed
  (`124e18aa`): committed curated QF_NRA 21/38 decided** (was 9/38), DISAGREE=0 on
  both z3 fuzzes. Next levers: the free-division `/0` witness route and
  threshold-1 monotonicity (`ones`).
In parallel: Track 1 decide-rate + *committed* head-to-head PAR-2; Track 3
reduction certs → Lean (ledger → 0) + the e-graph and Alethe-emitter keystones.
The consumer track (below) is mature + fuzz-hardened; its role is demand-pull
(filed U6/U7/U8) and certifying user-facing value, not core decide-rate.

**Infrastructure honesty (2026-07-02):** main's CI had been **red for 198
consecutive runs** — repaired in `0d10aeba` (MSRV 1.85→1.88 for let-chains,
rustdoc links, `ir.rs` clippy, 11 unformatted files, a flaky timeout budget,
cargo-deny path-dep wildcards). The full-suite sweep discipline had been
silently blocked by an **exponential (per-path) DAG walk** in
`set_cardinality`'s BV-term collector (evidence binaries observed running 8+
hours; fixed in `0bc133c2`, FP evidence tests now ~3 s) — behind it, five stale
evidence reds had rotted unseen (un-rotted in `459ffc41`; the zero-trust Alethe
emitters again outrank the structural pre-solve certs, size-gated). Two honest
`#[ignore]`s remain, each with a tracked follow-up: the uninterpreted-sort
`ite` SAT row (needs the P1.4/P1.5 e-graph keystone) and the `fifo_bc04` perf
regression (pre-existing, root-cause pending).

## Consumer-track integration lane (2026-06-27) — `WIP`

**Goal.** Merge the diverged consumer apps onto `main`: port `axeyum-evm`,
`axeyum-verify` (+ `-macros`), and `axeyum-consumer-bench` from the
`consumer-track` worktree (`../axeyum-consumer`), converge on `main`'s
`axeyum-property` as the single canonical SDK, and stand up the missing
**EVM/symexec capability scoreboard** (DISAGREE=0) so the warm-incremental
engine work finally carries a number.

**Reconciliation (decided).**
- `axeyum-property`: **`main`'s is canonical** (it is a superset). The branch's
  `axeyum-property` + `axeyum-property-derive` are **retired, not ported**.
- `axeyum-evm`: depends only on `axeyum-ir`+`axeyum-solver` → low-friction port.
- `axeyum-verify`: only coupling is `axeyum_property::Witness` (2 sites) → rebind
  to `main`'s property surface (add a thin `Witness`/reproduce export if missing).
- `axeyum-consumer-bench`: port + extend into the capability scoreboard.

**Increment status.**
| ID | Increment | Status |
|----|-----------|--------|
| I0 | Record plan in PLAN/STATUS; reconcile consumer-track docs | `DONE` (79193f2) |
| I1 | Port `axeyum-evm` (+ workspace member; folded `reproduce` into property) | `DONE` (3a22101) |
| I2 | Port `axeyum-verify` + `-macros` (own `Witness` enum; direct syn deps) | `DONE` (19d11b4) |
| I3 | **EVM/symexec capability scoreboard** (6/6 decided, DISAGREE=0, 5 shapes) | `DONE` (c840cab) |
| I4a | Reconcile `UPSTREAM-FEEDBACK` — U6 now measured by the scoreboard | `DONE` |
| I4b | EVM `MemoryEncoding::WarmArray` (`select`/`store` via `SymbolicMemory`) + warm-vs-`ite`-fold scoreboard column | `DONE` |

**Landed.** All three apps (`axeyum-evm`, `axeyum-verify`+`-macros`) build on
`main`, pass `cargo test` + `clippy -D warnings`, and hold **DISAGREE = 0**.
`main`'s `axeyum-property` is the single canonical SDK (the `reproduce` layer was
folded in additively for the apps). The warm-incremental symbolic-execution
engine now carries a committed number via `evm/SCOREBOARD.md`.
`axeyum-consumer-bench` was deliberately **not** ported (its corpus is coupled to
the retired branch property API and duplicates `main`'s `property/SCOREBOARD`).

**I4b finding.** `axeyum-evm` now decides symbolic storage two ways —
`MemoryEncoding::IteFold` (frontend read-over-write, default) and
`MemoryEncoding::WarmArray` (`const_array(0)` + `store`/`select`, auto-routed via
`SymbolicMemory` + `assume_auto`). They are denotation-equivalent: cross-encoding
agreement holds on every symbolic-storage/keccak row (DISAGREE=0), proving
`main`'s warm array path handles the EVM's storage patterns.

**Measured (the store-chain scaling sweep refutes the naive hypothesis).** I
expected warm-array to *win* at depth; the data says the opposite. On a safe
contract that `SSTORE`s `n` concrete slots then `SLOAD`s a symbolic key,
`ite`-fold is consistently faster and the gap **grows** with depth (depth 2:
1.3 ms vs 1.2 ms ≈ tie; depth 16: 2.1 ms vs 4.9 ms; depth 32: 3.2 ms vs
14.5 ms), both proving safe (DISAGREE=0). Cause: the current warm path routes a
`select` over a deep `store`-chain through the **one-shot memory dispatcher**
(re-processing the chain each check), whereas `ite`-fold stays on the warm
incremental BV path where concrete-key equality guards constant-fold. So the
honest conclusion for **U6**: capability has landed but *performance has not* —
the win requires a true **incremental lazy-array** engine, not the one-shot
dispatcher; until then `ite`-fold rightly stays the EVM default. This is the
data-driven answer the special-case-vs-general question wanted.

**ADR-0086 follow-up (2026-07-10):** the supported store-chain shape no longer
uses the one-shot dispatcher; exact structural read definitions and SAT state
persist. The rerun remains slower (depth 32: 0.368 ms ITE-fold vs 30.933 ms
retained warm), so the bottleneck has moved to eager observation-time definition
of every parent. Candidate-triggered ROW activation is now the measured U6
lever; ITE-fold remains the EVM default.

**ADR-0087 follow-up (2026-07-10):** candidate-triggered transitive summaries
replace both observation-time per-parent definitions and a rejected one-step
candidate prototype. A replayable miss can install zero CNF, while a violated
nested chain activates one permanent exact summary and resumes the same SAT
instance. Depth 32 improves from 30.933 ms to 11.257 ms (2.75x); ITE-fold still
wins at 0.405 ms, so the consumer default remains unchanged.

**A1 multi-tx keystone — DONE** (`4159cd3`, `e0751c4`). `axeyum-evm` now explores
**transaction sequences** with persistent storage (memory/stack reset per tx,
fresh per-tx calldata): a bug reachable only across calls (init-then-revert) is
*reported* with a replay-validated multi-tx witness, validated by a
persistent-storage concrete-replay oracle (`concrete::run_sequence`); the
scoreboard has a Multi-transaction section, DISAGREE=0 over 8 cases. This is core
angr/unicorn-class stateful analysis. Default `max_txs=1` preserves single-tx.

**A2 CALL/environment phase — DONE** (`a695198`, `f3f45c8`, `1cfbf47`). The EVM
hunter explores past environment opcodes (`GAS`/`BALANCE`/context), external calls
(`CALL`/`DELEGATECALL`/`STATICCALL` success flag), and models **re-entrancy**
(adversarial storage after a non-static call — the DAO threat), all as *witnessed
symbolic inputs* replayed by the concrete oracle (DISAGREE=0). Scoreboard 12/12.

**C4 verify warm-loop phase — DONE** (`6c7be0c`, `4f9104f`, `babb70b`, `e54a946`,
`1a23c36`). `axeyum-verify` now has a general AST-loop→warm-`bounded_model_check`
path: `ScalarLoopSystem` (N-variable engine), `loop_system`/`loop_from_program`
(AST guard/update/assert → warm system, reusing the real `lower_pure_expr`),
nested-`if` folding to guarded `ite` updates, and `check_program_loop` auto-routing
a `let*; while` `#[verify]` Program. Validated by a **cross-check against the
established unroll route** (`verify_program`): the two agree on buggy and safe
loops (straight-line and branching). Scalar state only (arrays-in-loop stay
one-shot, off U6).

**Since C4 (all DONE, gated):** verify capability scoreboard (9 cases,
DISAGREE=0, with **Lean-cert coverage 2/3** + a warm-vs-unroll depth-scaling sweep
showing the warm route ~40× faster at depth — the *opposite* of the EVM I4b
result); `verify_program_warm` entry routing (C4.6); and **adversarial
differential fuzzes for both apps** — the EVM fuzz **found & fixed a real
wrong-safe** (bad jump destination treated as a safe path end; `b1cd4a2`), now
covering single-tx/multi-tx/totality over arith/mem/storage/env/call; the verify
fuzz hardens the arithmetic fragment. Filed **U8** (axeyum-solver fails to build
for `wasm32` — blocks the A3 client-side moat).

**C5 fragment-widening + EVM opcode-precision (this session, all DONE, gated).**
Two parallel capability pushes, every increment soundness-fuzzed against a std/
concrete oracle (DISAGREE=0), clippy-gated, pushed:
- **`#[verify]` fragment** now covers the common real-Rust integer idioms:
  `match`-on-int (desugar to `if`/`else`), `wrapping_{add,sub,mul}`,
  `saturating_{add,sub,mul}` (signed+unsigned clamp), `min`/`max`, `abs` (with its
  `iN::MIN` overflow panic), `checked_{add,sub,mul}.unwrap()/.expect()`,
  `.unwrap_or(d)` and `match … { Some(v) => .., None => .. }` (via a new boolean
  `Expr::Overflows` node). Also fixed a latent literal-coercion gap in bare
  `name = <lit>` assignment. Verify corpus 9→14 (4/7 Lean-cert). Method gaps that
  need core IR (popcount/clz/ctz, symbolic-amount rotate) filed as **U9**.
- **`axeyum-evm`** turned **ten** `Unknown`-forcing opcode classes into sound
  models (all common runtime opcodes now covered), each added to the
  differential-fuzz pool: **BYTE**/**SIGNEXTEND** — *fully precise* (concrete
  shift/extract + symbolic bounded-`ite`); **EXP** — concrete constant-fold via
  `Word::pow`; **CALL-family return data** — witnessed memory bytes for a
  concrete/aligned/bounded region; **LOG0–LOG4** — no-op pops (was the biggest
  false-`Unknown` source); **BLOCKHASH/MSIZE** — witnessed env values;
  **CALLDATACOPY/CODECOPY** — *precise* copies (real calldata symbols / concrete
  code bytes; `Program.code` now retained); **CREATE/CREATE2** — re-entrant deploy
  (witnessed address + adversarial storage). EVM corpus 13→18. Aggregate track: 48
  cases, DISAGREE=0. Full suite passes `clippy --all-features` + `cargo doc -D
  warnings`.

first-class (let-bound) checked-`Option` flow also landed (unwrap/unwrap_or/
is_some/match). **Next (consumer):** A3/C6 stay U8/install-gated; remaining
threads are `Option`-returned-from-fn, RETURNDATACOPY/EXTCODECOPY, symbolic-EXP.
Forward backlog in
[PLAN.md](PLAN.md#consumer-track-integration-2026-06-27-converge-the-apps-onto-main).

**Coordinated into core (Track 1) — measured QF_UF decide-rate gain.** Re-measured
the *accessible* curated corpus (the frontier's numbers are full-NAS): QF_S is
already at z3 parity (56/56); QF_UF lagged z3 by 4. Localized the gap (uninterp-
sort `ite`/theory-combination) and landed two solver changes: `check_auto` no
longer hard-errors on a valid QF_UF instance, and uninterpreted-sort `ite` is
eliminated equisatisfiably for the e-graph path (pure-UF-confined). **QF_UF
37/48 → 39/48** (gap to z3 −4 → −2), DISAGREE=0, lib 613/613 + qf_uf fuzz
DISAGREE=0. Then batch-measured the other slices and closed the next verifiable
gap: **QF_ABV** robustness (no hard-error on a wide-index array equality) +
**write-index array extensionality** (decides shared-base `store-chain =
store-chain` over 32-/64-bit indices without `2^iw` enumeration) → **QF_ABV
173 → 176/177** (gap to z3 −1), DISAGREE=0, abv fuzz DISAGREE=0, rewrite 88/88.
Grounding + the remaining leads in
[decide-rate-measured-2026-06-29](docs/plan/decide-rate-measured-2026-06-29.md):
the **UF+theory combination keystone** (deep; `issue5836-2`/`issue5396`); and a
**confirmed deadline-robustness defect** — QF_AUFLIA `bug330` runs 25 s under a
2 s `config.timeout` (the UFLIA combination solve on its UF-heavy array-abstracted
relaxation — eager Ackermann / e-graph recursion — does not check the deadline;
the lazy-row CEGAR and QF_LIA *are* clean). A solver must honor its budget; thread
the deadline through that inner path → graceful Unknown. *(Correction: an earlier
note over-broadly "ruled out" the hang from QF_LIA evidence; `bug330` confirms it
is real, scoped to the QF_AUFLIA path — and verified **pre-existing**, not from
the write-index change.)*

**Headline (honest):** after this session's gains — **curated QF_UF reached full
z3 parity** (37→41/48, via `ite`-elimination + the Bool-equality-is-`iff` euf fix
+ robustness); QF_ABV 173→176/177; NAS QF_UF 42→44/63 — **the bounded decide-rate
wins are exhausted across every slice we can measure** (curated + the mounted NAS
QF_BV/QF_LRA/QF_UF). Every remaining residual is *deep engine work*, measured and
localized: NAS QF_UF −11 = LIA+UF CEGAR convergence (`hash_sat_*`, grinds 248 LP
rounds w/o a sat candidate) + a `build_model` sub-cause; NAS QF_LRA −1 = MIP/LP
efficiency (`miplib-*`); QF_ABV −1 = lazy-ext replay/budget; QF_AUFLIA −2 = the
pre-existing `bug330` deadline-hang (#63) + a UFLIA budget case; `issue5836-2` =
UF+**NRA**. The next decide-rate work is genuine multi-week *engine* depth
(LIA+UF CEGAR, `build_model` completeness, CAD depth, the unbounded-string DP) —
where Z3/cvc5 parity is actually won — not more bounded triage. All gains
DISAGREE=0, fuzz-validated. *(Update 2026-07-01/02: two of the named engine
levers have since landed — the **FM→simplex LRA core** (P1.9 complete,
soundness-validated on 1199/1200 FM-blowup systems; large-corpus decide-rate
payoff still unmeasured) and **CAD coprime-split projection + `/0` witnesses**
(committed QF_NRA 9/38 → 21/38
curated). The remaining engine list stands.)*

**Discipline.** New-crate-only + one additive root `Cargo.toml` member line; no
core IR/solver/rewrite edits; every increment builds, passes gates, and holds
**DISAGREE = 0**; build/test via `scripts/mem-run.sh` (64 GB cap).

## Process/documentation lane (2026-06-27) — `WIP`

- **Curriculum coverage complete: every `planned` node now has a
  self-checking exercise family.** The five remaining `planned` nodes in the
  23-node formal-mathematics-tour DAG — `proof-methods`, `induction`,
  `relations-and-functions`, `rationals`, and `reals` — are now `covered`,
  each backed by a new oracle-free `axeyum-scenarios` family (ADR-0008: SAT
  by concrete-witness evaluation, UNSAT by exhaustive enumeration):
  `Family::ProofMethods` (contrapositive/case-analysis tautologies,
  proof-by-contradiction parity, and a wraparound counterexample),
  `Family::Induction` (base+step obligations for `Σ odds = n²` and the Gauss
  sum with the hypothesis abstracted into a fresh symbol, plus a false
  invariant's satisfiable step), `Family::Relation` (pigeonhole
  no-injection, a bijection witness, the symmetric+transitive⇏reflexive
  fallacy refuted by the empty relation, and injective-composition over
  packed function tables), `Family::Rational` (density midpoint, mediant
  inequality, exact 2×2 solves, trichotomy — exact rational witnesses), and
  `Family::RealAlgebra` (rational-root quadratics, an AM–GM instance with a
  rational geometric mean, nested intervals). The mathtour invariant test
  ("every Covered node's family is realized by a self-checking scenario")
  now enforces all 19 covered nodes; the curriculum source, node pages,
  README, and generated dashboards report **19 covered / 4 lean-horizon /
  0 planned**, and the curriculum-status audit's
  `source-planned-resource-validated` review queue is empty. The 4
  lean-horizon nodes (cardinality, complex, sequences-and-limits, calculus)
  remain proof-reconstruction targets by design.

- **Finite policy-iteration resource landed.**
  `finite-policy-iteration-v0` now pairs with the value-iteration pack to
  show two algorithms reaching one committed optimum on the same fixed
  three-state discounted MDP: it substitutes each committed policy's value
  vector back into its fixed-point equation for an exact zero residual —
  `(2, 2/3, 0)` for the deliberately suboptimal `(b, b, a)` (a genuine
  linear solve, since `s2` feeds back into `s1` and `s2`), `(2, 3, 0)`,
  then `(5/2, 3, 0)` — replays two greedy improvement rounds and the
  termination-by-stability round at `(a, a, a)`, and checks the
  componentwise monotone improvement ending at the exact optimum shared
  with `finite-value-iteration-v0`; rejects the malformed policy-evaluation
  claim `1/2` against exact `2/3`; and routes that scalar conflict through
  a source-linked QF_LRA/Farkas row. The focused learner page,
  probability/statistics and dynamics query guides, stochastic-kernel,
  value-iteration, policy-iteration, exact-vs-floating, and QF_LRA/Farkas
  bridge rows, validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed finite trace
  separate from the policy-improvement theorem in general, termination and
  optimality theorems, average-reward/continuous MDP theory, stochastic
  approximation, and floating-point dynamic programming. The public summary
  now reports 137 concept rows, 173 packs, 1131 expected checks, 399
  checked rows, 596 replay-only rows, 136 Lean-horizon rows, and 173
  promoted solver-reuse packs.

- **Finite value-iteration resource landed.**
  `finite-value-iteration-v0` now gives the probability, dynamics, and
  optimization lanes a dynamic-programming trace — a new proof shape next to
  the committed-optimum SVM pair and the iterative perceptron trace: it

> Full lane history archived: [docs/status-archive/process-documentation-lane-through-2026-07-06.md](docs/status-archive/process-documentation-lane-through-2026-07-06.md)

## Current focus

- **2026-07-13 — the ten-item Glaurung QF_BV performance roadmap is now an
  explicit Track 1/4 lane (`PLAN.md` GQ1--GQ10).** The ordering is
  benchmark-first: capture and profile the actual shadow-diff SMT-LIB stream,
  establish its first-class regression tier, and only then choose between cold
  rewriting/slicing, AIG/CNF construction, or SAT search from measured layer
  attribution. Warm delta reuse, duplicate/prefix caching, and an automatic
  preprocessing cost policy are separately tracked rather than being implied by
  the existing incremental API.

  **GQ1/GQ10 readiness increment:** artifact v22 charges Axeyum for word
  preprocessing, separates it from term→AIG, AIG→CNF, optional CNF
  inprocessing, SAT, model lift, and original-query model replay, and records
  exact p50/p95 distributions.
  The aggregate client ratio compares against in-process Z3 on the untouched
  parsed assertions, not Axeyum's reduced terms; binary fallbacks are
  verdict-only. `bench-glaurung-qfbv` is single-worker and requires in-process
  Z3 coverage for every file. Manifest v1 now also fixes exact corpus membership,
  per-query SHA-256, expected verdicts, families, stable order, and named tiers;
  all entries are validated before tier selection and every selected verdict is
  independently gated. The two-query representative micro plumbing smoke is
  2/2 decided/manifest-agreed/Z3-agreed with zero errors or replay failures, but
  carries no Glaurung speed claim. The untouched original-query DAG now also has
  deterministic per-instance and corpus shape telemetry: formula and width
  distributions, extract/concat/extension and surviving array-op counts,
  demanded-vs-source extract bits, exact GQ3 cancellation opportunities, and
  AIG/CNF p50/p95 sizes. Flattened memory provenance is intentionally supplied
  by manifest family/source metadata rather than inferred. A separate
  `--prove-unsat` companion now fails closed unless every UNSAT carries an
  inline-checked DRAT proof and reports proof-check p50/p95 nested within SAT
  time; it is not mixed into the default batsat performance artifact. The
  experiment identity now records the clean Axeyum revision, Cargo.lock hash,
  rustc/cargo/build profile, exact backends, CPU, kernel, parallelism, and
  memory. Glaurung recipes fail before solving unless that identity is complete and clean;
  matching `config_hash + environment_hash` is the per-commit comparison key.
  The fixed-seed gate is now executable too: v21 removes the unused decorative
  `--seed` label, records and hashes the actual Cargo.lock-pinned BatSat defaults
  (seed `91648253`, random-variable frequency `0`, randomized polarity and
  initial activity both off), explicitly sets and records Z3 `random_seed=0`,
  and records deterministic corpus ordering. Rust and repetition-validator
  tests fail on drift. This closes seed/configuration identity only; measured
  variance remains an independent gate.
  The deterministic resource gate is now executable as well. A required v22
  cold-client run fails before corpus work unless positive term-DAG,
  CNF-variable, CNF-clause, and backend-search limits are present. The search
  limit reaches the real engine as `BatSat` `within_budget` progress checks,
  native proof-CDCL conflicts, or Z3 `rlimit` units; artifacts name the unit and
  deny cross-backend numeric work equivalence. The provisional
  `axeyum-qfbv-cold-bounded-v1` recipe is 300k DAG nodes / 3M CNF variables / 8M
  CNF clauses / 2M search units. Timeout remains a non-deterministic safety
  backstop, and any real-corpus limit change requires a new named profile.
  The capture boundary now has a deterministic producer/consumer handshake:
  the shadow-diff side emits a versioned index of ordered paths, trusted
  verdicts, families, and tiers; Axeyum checks exact `.smt2` membership, hashes
  the bytes, rejects stale exporter-supplied hashes/unknown fields, emits
  manifest v1, and immediately re-ingests it through the normal validator.
  The committed micro index exercises this path without implying client data.
  A repeated-run recipe now launches independent whole-corpus processes and a
  streaming fail-closed summarizer verifies byte-identical configuration,
  clean experiment identity, 100% decisions, and every manifest/oracle/replay
  gate before reporting p50/p95, sample standard deviation, and coefficient of
  variation for Axeyum/Z3 corpus totals, their ratio, and all attributed stages.
  This closes the methodology gap between per-query shape distributions and
  actual run-to-run variance without retaining multiple large artifacts in
  memory.
  The committed
  [`glaurung-repetition-smoke`](bench-results/glaurung-repetition-smoke/summary.json)
  exercises three independent artifact-v22 trials from clean revision
  `fe65b076`: every run
  is 2/2 decided, manifest-agreed, and Z3-agreed with zero errors or replay
  failures. The summary records Axeyum-total CV 32.63%, Z3-total CV 2.59%, and
  ratio CV 29.92%, plus every stage distribution. Those sub-millisecond micro
  values validate variance plumbing only and carry no Glaurung performance
  claim.
  Cross-commit comparison now revalidates both repetition summaries from their
  trial records, requires identical corpus/manifest/config/environment/backends
  with distinct clean source revisions, and reports raw Axeyum, raw Z3 control,
  ratio, and per-stage deltas. Optional ratio/raw-Axeyum regression and absolute
  Z3-drift gates are caller-supplied; the micro fixture sets no threshold.
  The committed
  [`glaurung-cross-commit-smoke`](bench-results/glaurung-cross-commit-smoke.json)
  now records the artifact-v22 bounded-resource boundary between clean revisions
  `fe65b076` and `01c2441a`, with matching corpus, manifest, config,
  environment, backends, and resource profile. The candidate/baseline ratio
  mean is +21.78%, candidate ratio CV is 20.40%, the descriptive standardized
  delta is +0.97, and the raw Z3 control is +2.65%. These sub-millisecond micro
  results demonstrate identity/noise accounting and explicitly do not establish
  a performance regression, speedup, or product threshold.

  | ID | Live status | Next acceptance boundary |
  |---|---|---|
  | **GQ1 real-query profile** | **WIP; external capture is the remaining data dependency.** Artifact v22, executable solver-determinism and bounded-resource identity, capture-index→manifest generation, manifest-v1 ingestion, untouched-DAG formula/width/operator/opportunity profiling, typed AIG/CNF/inprocess stats with size distributions, separately charged SAT model replay, an optional fail-closed proof-check companion, complete clean source/tool/hardware identity, single-worker client recipe, whole-corpus process-level repetition/variance summary, p50/p95, original-query in-process Z3 ratio, complete manifest/oracle/decided-rate gates, and zero-error policy are landed | Obtain the representative Glaurung query pack plus trusted capture index, generate/validate its manifest, confirm its lifter-shape distributions, and publish the first valid same-environment repeated client attribution/ratio plus separate proof-check result; the micro smokes validate plumbing only |
  | **GQ2 cheap cold tier** | **TODO**, profile-gated; existing full preprocessing is opt-in and warm-oriented | Bounded constant/identity tier with non-worse cold aggregate time and an explicit cold/warm/size policy |
  | **GQ3 coercion peepholes** | **TODO**; only narrower extract-through-bitwise/ITE rules are landed | Exact extract/concat, nested-extract, zero/sign-extension cancellation with exhaustive and differential semantics gates |
  | **GQ4 cold relevant bits** | **WIP foundation**; warm 8-of-64 slicing is landed, cold demand propagation is not | Backward live-bit pass, original replay, counters, and measured target-corpus AIG/CNF reduction |
  | **GQ5 AIG/CNF construction** | **TODO, attribution-gated**; structural hashing exists and max-sharing/two-level rewriting remain P1.2 work | Measured gate/clause and end-to-end reduction on the real corpus, including only the gate families the profile identifies |
  | **GQ6 cold SAT/CDCL** | **WIP foundation, attribution-gated**; subsumption/BVE, XOR/GF(2), VSIDS, phase saving, Luby, and LBD foundations exist | Exact-CNF backend attribution first; tune/default a stronger path only where SAT dominates and proof replay stays green |
  | **GQ7 warm delta entry** | **WIP foundation**; retained CNF/search state exists, but `assert_configured` delta-only preprocessing is not complete | Preprocess only new/affected terms and publish per-check cost plus warm break-even sequence length |
  | **GQ8 verdict/CNF cache** | **TODO** | Versioned canonical keys, exact duplicate verdict reuse, sound prefix-state reuse, deterministic bounds, and mandatory original replay |
  | **GQ9 auto cost model/docs** | **TODO**; P1.8 shape/resource probes are only the general foundation | Telemetry-visible raw/cheap/configured/warm choice that beats or matches fixed policies and documents embedder guidance |
  | **GQ10 real-lifter regression tier** | **BLOCKED on the external capture**; artifact-v22 validity/attribution/shape/replay/experiment/determinism/bounded-resource gates, a strict versioned capture-index generator, manifest-v1 exact membership/SHA-256/expected-verdict/family/tier contract, independent-process repetition/variance summarization, fail-closed same-environment cross-commit comparison, and separate performance/proof recipes are landed | Export the real capture plus trusted index, generate its manifest, then land its regular representative gate, repeated scheduled full run, proof companion, cross-commit baseline, and corpus-grounded regression thresholds |

  **Next actions:** (1) receive the Glaurung `.smt2` capture plus versioned
  trusted index without normalizing away its width-mixed/extract/concat/memory
  shape, generate the strict manifest, and verify that distribution in the
  artifact-v22 shape/profile gate; (2) establish the repeated GQ1/GQ10 baseline at
  100% decided, zero errors/disagreements/replay failures with reported
  whole-corpus variance, then compare subsequent clean revisions under the same
  environment before setting any regression threshold; (3) select the first
  implementation slice from the largest measured cold stage, with GQ2/GQ3/GQ4
  preferred only if word construction or bit-blast attribution supports them.
  Until the capture arrives, instrumentation/ingestion work may proceed and the
  quantified Lean lane may continue, but no synthetic-only performance win
  closes a GQ item.

- **2026-07-14 — ADR-0124 construction/export are now bounded; final deep
  kernel inference remains WIP.**
  Reconstruction now preserves the exact `forall+ exists+ (antecedent ->
  consequent)` source proposition, discharges the antecedent by evaluation, and
  feeds the consequent into a local-let Alethe tail. Compact module emission now
  streams byte-identically to a temporary file before inference; scoped free
  variables close at their associated lambdas in one shared-DAG traversal; and
  ordinary free-variable abstraction skips subgraphs without a requested local.
  The public `small-pipeline-fixpoint-3` direct/router pipeline passes under the
  guarded 4 GiB release envelope in 106.62 s at 3,692,844 KiB peak. `bug802` now
  finishes source reconstruction in 2.984 s and streaming export in 10.506 s,
  then the final generic inference of its 530-binder `Exists.rec` chain fails
  safely on a 2,181,038,096-byte allocation at roughly 2.0 GiB RSS. Kernel
  170/170 plus its doctest and the non-stress alternation gate pass. Lean UNSAT
  therefore remains 14/18. Next: bound the trusted nested-recursor type check
  itself, rerun both 4 GiB public direct/router equality gates, and only then
  claim coverage.

- **2026-07-13 — ADR-0140 reconstructs vacuous BV existential prefixes.**
  The ADR-0128 checker still proves the complete leading existential block
  absent and evaluator-replays the exact universal values against the untouched
  body. Reconstruction now encodes the full `exists+ forall+` source, eliminates
  each prefix binder with genuine `Exists.rec`, applies the surviving universal
  to typed constructors, and kernel-reduces the computational AIG to `False`.
  An explicit proof failed safely at a 1.42 GiB allocation; the compact route
  owns a 64 MiB worker stack and passes the public optimized direct/router gate
  in **16.54 s** (**38.04 s** cold, **1,975,764 KiB** peak under 4 GiB). Exact
  dominance rises **49→50/54** and Lean UNSAT **13→14/18**; 54/54 remain
  checked/certified with zero mismatch/error/timeout. Next: characterize
  ADR-0129 paired-existential source elimination/introduction against ADR-0124.

- **2026-07-13 — ADR-0139 reconstructs closed Bool/BV universal
  counterexamples.** The ADR-0100 certificate is rechecked, exact typed values
  instantiate the untouched universal, and an explicit gate-by-gate AIG proof
  refutes the carried body before the kernel checks `False`. `qbv-simp`
  reconstructs in **0.08 s** with no `sorryAx`, raising exact quantified-BV
  dominance **48→49/54** and Lean UNSAT **12→13/18**; 54/54 remain
  evidence-certified/rechecked with zero mismatch/error/timeout. Ranking also
  measured ADR-0127's real boundary: 15,705 commands with repeated
  4,700--5,000-premise RUP chains request a 2.18 GiB allocation and fail safely
  under 4 GiB, so that family now waits on compact reflected-RUP checking. Next:
  ADR-0128 vacuous-existential elimination over this evaluated-AIG spine.

- **2026-07-13 — ADR-0138 reconstructs concrete negated-BV-existential
  witnesses in Lean.** The ADR-0126 checker still binds the exact untouched
  source and evaluator-replays every complete typed witness before proof
  construction. Reconstruction now represents Bool/BV values with typed
  computational datatypes, proves small AIGs gate by gate, and uses shared
  reducible Bool operators plus local gate `let`s for large circuits. Genuine
  nested `Exists.intro` closes against the sole original negated source axiom;
  the kernel checks `False`, and generated modules contain no `sorryAx` or
  theorem-specific refuter. Abstraction, instantiation, universe substitution,
  open inference, definitional equality, and WHNF now traverse shared kernel
  DAGs with context-valid caches. All three public rows pass the release stress
  gate in **12.43 s** under 4 GiB; the cold build-and-test command takes **34.46
  s** and peaks at **1,941,680 KiB RSS**. The exact public audit remains 54/54
  evidence-certified/rechecked with DISAGREE=0 and no errors/timeouts, while
  dominance rises **45→48/54** and Lean UNSAT **9→12/18**. Next: rank
  ADR-0124/0127/0128/0129 by proof reuse and guarded reconstruction cost.

- **2026-07-13 — ADR-0137 makes corpus-scale Lean export DAG-linear.** The
  `psyco-107-bv` kernel proof already completed, but self-contained module export
  walked shared declarations as trees, capped repeated shares at 16,384, and
  left declaration types plus single-use resolution chains unchunked. Dependency
  discovery now visits each `ExprId` once; compact export retains every
  qualifying repeated closed node, cuts single-use closed regions at 512 nodes,
  and uses capture-safe scoped `let` aliases in declaration types/values. The
  timed one-pass release stress gate completed in **102.19 s** at **2,697,384
  KiB max RSS** under a 3 GiB test-process cap; the final cold-build recipe rerun
  passed in **106.51 s** inside 4 GiB. The refreshed public quantified-BV baseline is **36 SAT / 18
  UNSAT / 0 unknown / 0 unsupported**, 54/54 decided and agreed, DISAGREE=0,
  errors/replay failures 0, PAR-2 mean 0.0326168371 s. Exact audit: 54/54
  evidence-certified/rechecked, **45/54 dominant**, **Lean UNSAT 9/18**, zero
  mismatch/error/timeout. Next: rank the remaining source-bound quantified-BV
  UNSAT families for Lean reconstruction and reduce proof construction/export
  below the guarded 2.7 GiB peak.

- **2026-07-13 — ADR-0136 turns the Glaurung QF_BV feedback into a client
  boundary and a measured optimization target.** Strict IR sorts remain intact,
  with explicit unsigned `coerce_to`; `Value` is re-exported and the new
  command-independent SMT-LIB model accessor removes `(get-model)` ambiguity.
  A dependency-firewalled `qfbv` feature retains cold/warm pure-Rust solving,
  models, and proof rechecking without the e-graph/FP/Lean/SMT-LIB/string
  crates. Warm `assert_configured`/`assert_preprocessed` preserves original-term
  replay and now pushes narrow extracts through wide bitwise/ITE terms; the
  focused 8-of-64-bit test proves most discarded AIG gates are not built, and
  exhaustive evaluator plus Z3 differential routes cover denotation. The
  benchmark artifact is version 15, operational errors fail the run, and
  `--min-decided-percent` prevents fast failures from scoring as speedups. The
  external Glaurung capture is the primary 100%-decided client gate; it is not
  present in the local reference checkout, so the reported 1.7--3.2x Z3 gap has
  not yet been remeasured and no parity claim is made. Next: obtain a
  redistributable client capture, run `just bench-glaurung-qfbv`, and profile
  only comparable zero-error/zero-disagreement runs.

- **2026-07-13 — ADR-0135 reconstructs query-scoped BV instances from genuine
  source theorems.** The Lean route admits only ADR-0134's positive Bool/BV
  top-level conjunction shape, represents each binder with a typed Bool/BV
  inductive, introduces axioms only for untouched ordered assertions, projects
  ground leaves, and obtains every instance by applying its source universal to
  exact constructor witnesses. Source and residual formulas share the existing
  AIG lowering; shallow named gates feed the checked Alethe tail. Resolution no
  longer treats double negation as definitional equality: classical
  normalization constructs and checks an explicit excluded-middle proof. The
  kernel caches successful inference only for closed terms, with open/failing
  cache regression coverage. The two-instance route passes in-tree checking and
  is registered in the external-Lean representative suite. ADR-0137 subsequently
  closes the corpus-scale export gap and raises quantified-BV Lean to 9/18; the
  remaining work is the other source-bound quantified-BV UNSAT families.

- **2026-07-13 — ADR-0134 completes the public quantified-BV slice with a
  checked query-scoped instance set.** Bounded CEGIS may discover complete
  positive-universal Bool/BV source instances, but candidate models,
  quantifier erasure, and instance selection remain search-only. A separate
  checker binds the exact assertion sequence, reuses ADR-0133's positive
  Bool/BV admission, requires 1 through 256 unique complete typed source
  tuples, rebuilds the ground weakening and every instance, and rechecks the
  exact QF_BV DRAT/LRAT proof. Any heuristic candidate block disables the
  certificate. `psyco-107-bv` moves unsupported to certified UNSAT. Five
  release solve samples are 109.528079/112.048587/108.817031/108.590204/
  104.763955 ms (median 108.817031 ms); evidence samples are
  101.938/103.544/103.781/103.525/102.888 ms (median 103.525 ms). The public
  slice is **36 SAT / 18 UNSAT / 0 unknown / 0 unsupported**, 54 agreements,
  zero disagreement/error/replay failure, and PAR-2
  0.0334462169/0.0338140011/0.0328719061/0.0330305167/0.0327350909 s (median
  0.0330305167 s). Audit: 54/54 certified/rechecked, 44/54 dominant, Lean 8/18
  UNSAT, no mismatch/error/timeout, and empty target trust. Seven focused tests
  include a two-instance necessity gate, adversarial query/source/binding/
  proof/capture rejection, unsupported-sibling decline, deadline expiry, and 32
  direct-Z3 cases; cumulative
  quantified-BV direct-Z3 coverage is 1,912. Next: keep the 54/54 ratchet and
  characterize Lean reconstruction for the source-instance theorem plus
  residual QF_BV proof before broadening nested/alternating QSAT or quantified
  UF.

- **2026-07-12 — ADR-0133 lands checked residual-QF_BV free-Boolean models.**
  Bounded CEGIS may use a satisfiable negated residual to instantiate one
  concrete positive universal and refine a complete free-Boolean candidate,
  but neither the instance nor quantifier erasure has proof status. A separate
  checker admits only Bool/BV positive universals with unique binders disjoint
  from free symbols, no applications or free BVs, exact sorted free-Boolean
  coverage, and 128-binder/4,096-node/256-depth caps. It clones the untouched
  source, substitutes the complete model, opens the universals, negates the
  exact residual, and rechecks its source-bound DRAT/LRAT proof; canonical
  `check_model` remains the final gate. `psyco-001-bv` moves unsupported to
  replay-checked SAT. Five corpus target samples are
  339.664335/341.466781/339.928031/338.600498/342.665246 ms (median
  339.928031 ms); evidence samples are
  759.687/758.775/766.378/763.886/761.351 ms (median 761.351 ms). The 54-row
  slice is **36 SAT / 17 UNSAT / 0 unknown / 1 unsupported**, 53 agreements,
  zero disagreement/error/replay failure, and PAR-2
  0.408176/0.408413/0.408171/0.408370/0.408282 s (median 0.408282 s). Audit:
  53/53 certified/rechecked, 44/53 dominant, Lean 8/17 UNSAT, and empty target
  trust. Sixteen focused tests include 16 new certified SAT models, 16
  direct-Z3 UNSAT controls, and adversarial binder/free capture rejection;
  cumulative direct-Z3 coverage is 1,880. Strict
  all-target solver Clippy is green. The complete workspace `just check` gate
  passes, including the long variable-divisor NIA and UFLIA differential
  fuzzers, warning-denied rustdoc, foundational resources, generated
  documentation checks, and link validation. Next: characterize
  `psyco-107-bv`, the sole remaining unsupported row, from cvc5/Z3 source and
  preserve the positive-universal residual-proof boundary.

- **2026-07-12 — ADR-0132 lands checked zero-product quantified-BV models.**
  A complete free-BV model for one directly negated existential implication is
  now accepted only when a separate source checker finds exactly one
  binder-dependent inner implication whose conclusion is signed nonnegativity
  of a binary product. One direct binder-free `bvsdiv` factor must
  evaluator-replay to zero, the other factor must contain the unique binder,
  and the comparison bound must be a same-width literal zero. The nonlinear
  factor is never interpreted; every remaining ground fact replays, QF_BV only
  proposes values, and canonical `check_model` remains the final gate.
  `gn-wrong-091018` moves unsupported to replay-checked SAT. Five corpus target
  samples are 84.292858/89.874858/88.677335/79.148524/91.340195 ms (median
  88.677335 ms); evidence samples are 70.429/72.517/70.981/72.258/70.548 ms
  (median 70.981 ms). The 54-row slice is **35 SAT / 17 UNSAT / 0 unknown / 2
  unsupported**, 52 agreements, zero disagreement/error/replay failure, and
  PAR-2 0.794452/0.794156/0.794198/0.794015/0.794377 s (median 0.794198 s).
  Audit: 52/52 certified/rechecked, 43/52 dominant, Lean 8/17 UNSAT, and empty
  target trust. Thirteen focused tests include 16 new certified SAT models and
  16 direct-Z3 nonzero-factor UNSAT controls; cumulative direct-Z3 coverage is
  1,848. The complete workspace `just check` passes, including strict Clippy,
  all tests, warning-denied rustdoc, foundational resources,
  generated-document consistency, and links. Next: `psyco-001-bv` (147 DAG
  nodes), a positive mixed Bool/BV
  universal requiring a separate checked free-Boolean guarded-ITE/equality
  implication contract.

- **2026-07-12 — ADR-0131 lands checked signed-interval quantified-BV models.**
  A complete free-BV model for one directly negated existential implication is
  now accepted only when a separate source checker finds exactly one
  binder-dependent signed interval implication, evaluator-replays all other
  antecedent leaves to true and the untouched division-bearing outer conclusion
  to false, rejects empty intervals, and proves signed
  `lower <= upper <= cap`. QF_BV proposes only candidate values under the shared
  deadline; canonical `check_model` remains the final gate.
  `intersection-example-onelane` moves unsupported to replay-checked SAT. Five
  corpus target samples are 36.477393/36.338867/38.899419/39.272877/37.681117
  ms (median 37.681117 ms); evidence samples are
  32.651/32.914/33.267/33.429/34.863 ms (median 33.267 ms). The 54-row slice is
  **34 SAT / 17 UNSAT / 0 unknown / 3 unsupported**, 51 agreements, zero
  disagreement/error/replay failure, and PAR-2
  1.200739/1.200402/1.200617/1.200837/1.200235 s (median 1.200617 s). Audit:
  51/51 certified/rechecked, 42/51 dominant, Lean 8/17 UNSAT, and empty target
  trust. Nine focused tests include 16 new certified SAT models and 16 direct-Z3
  UNSAT controls; cumulative direct-Z3 coverage is 1,816. The complete workspace
  `just check` passes, including strict Clippy, all tests, warning-denied
  rustdoc, foundational resources, generated-document consistency, and links.
  Next:
  `gn-wrong-091018` (88 DAG nodes), whose nonlinear binder polynomial occurs
  under a binder-free zero-producing signed-division multiplier and requires a
  separate exact source annihilation/inequality contract.

- **2026-07-12 — ADR-0130 lands checked affine-LSB quantified-BV models.**
  A complete free-BV interpretation now receives SAT credit only through a
  separate untouched-source checker. Direct positive `forall+` bodies use an
  exact affine GF(2) LSB interpreter; directly negated `forall+` bodies carry
  complete typed binder values and must evaluate false. Admission is Bool/BV
  only, function-free, exact in free-symbol order/coverage, and capped at 128
  binders, 4,096 complete source nodes, and depth 256. Search exhausts low-bit
  assignments for at most eight free BVs under one deadline and uses QF_BV only
  to propose witnesses. `smtcomp-qbv-053118` moves unsupported to replay-checked
  SAT. Five target solve samples are 0.285816/0.195489/0.213322/0.192103/
  0.190069 ms (median 0.195489 ms); evidence samples are 3.339/3.287/3.293/
  2.437/3.036 ms (median 3.287 ms). The 54-row slice is **33 SAT / 17 UNSAT /
  0 unknown / 4 unsupported**, 50 agreements, zero disagreement/error/replay
  failure, and PAR-2 1.624330/1.623963/1.623953/1.624041/1.623998 s (median
  1.623998 s). Audit: 50/50 certified/rechecked, 41/50 dominant, Lean 8/17
  UNSAT, and empty target trust. Five focused tests include 32 direct-Z3 SAT
  models and 32 UNSAT controls; cumulative direct-Z3 coverage is 1,784. The
  model certificate families now share one lazy boxed aggregate, preventing
  future proof variants from inflating every ordinary `Model`. The complete
  workspace `just check` passes, including strict Clippy, all tests,
  warning-denied rustdoc, foundational resources, generated-document
  consistency, and links. Next:
  `intersection-example-onelane` (70 DAG nodes), requiring a separate checked
  contract for a negated existential implication with free BV facts and signed
  division, grounded in cvc5 inversion/linearization and Z3 model checking.

- **2026-07-12 — ADR-0129 lands checked paired-existential witness transfer.**
  The source-bound checker admits one positive existential and one directly
  negated existential only under exact shared ground premises, equal nonempty
  Bool/BV prefix lengths/sorts, 128 total unique binders, and 4,096 complete
  source DAG nodes. It deterministically alpha-aligns the complete witness tuple
  and requires every target-body conjunct either to match an available source
  conjunct or carry one exact justification: a regenerated source-subset
  `QF_BV` DRAT/LRAT implication, or signed-add monotonicity with
  `0<=weak<=strong` and `bound<=MAX_SIGNED-strong` rechecked to prove both
  additions cannot wrap. Search is untrusted and bounded to 256 ordered
  assertion pairs and 256 proof subsets under the shared deadline; solver and
  evidence dispatch act only after independent replay. `nested9_true-unreach-call`
  moves unsupported to checked UNSAT. Five release solve samples are 0.075/
  0.073/0.081/0.076/0.069 ms (median 0.075 ms), and evidence samples are
  0.039/0.039/0.055/0.038/0.037 ms (median 0.039 ms). Fresh 54-row measurement
  is **32 SAT / 17 UNSAT / 0 unknown / 5 unsupported**, 49 agreements, zero
  disagreement/error/replay failure, and PAR-2 2.065130/2.065493/2.065744/
  2.065791/2.066172 s (median 2.065744 s). The audit certifies/checks 49/49;
  the target taxonomy is `bv-paired-existential-transfer-unsat` with empty
  trust. Dominance is 40/49 and Lean 8/17 UNSAT. Eight focused tests include
  64 direct-Z3 safe transfers plus 64 genuine signed-wrap SAT controls;
  cumulative quantified-BV direct-Z3 coverage is 1,720 cases/controls. The
  width-10 control exposed two pre-existing linear-depth builders: exact finite
  expansion and AC canonicalization now both use deterministic balanced folds,
  with a maximum-width depth regression; the complete focused suite passes on
  Rust's normal test stack. The full `just check` aggregate passes, including
  all workspace tests and doctests, strict Clippy, warning-denied rustdoc,
  foundational-resource and rules-as-code validation, generated-dashboard
  checks, and documentation links; machine-specific frontier timing output is
  not recorded as a product change. Next: `smtcomp-qbv-053118` (37 DAG nodes),
  a SAT theorem with concrete `x=0`: prove the first universal by parity (even
  left, odd right) and replay a complete witness for the negated second universal.
  cvc5 BV inversion and Z3 model/projection remain candidate-generation
  references only; no free-BV or parity-normalization SAT credit without a
  separate original-source model certificate.

- **2026-07-12 — ADR-0128 lands checked vacuous-existential-prefix
  counterexamples.** The new source-direct checker admits only one exact
  nonempty `exists+ forall+` Bool/BV prefix, at most 128 unique binders and
  4,096 complete source DAG nodes. It proves every existential binder absent by
  requiring all body symbols to be universal binders, rejects nested/apply/open
  bodies, validates complete universal IDs/order/sorts/values, and evaluates the
  untouched body directly to `Bool(false)`. Search is untrusted: it freshens
  only universal binders, solves the negated QF body, and must pass the checker
  before solver or evidence dispatch returns UNSAT. `issue2031-bv-var-elim`
  moves unsupported to checked UNSAT with target samples 0.129/0.130/0.124/
  0.130/0.122 ms (median 0.129 ms). Fresh 54-row release measurement is **32
  SAT / 16 UNSAT / 0 unknown / 6 unsupported**, 48 agreements, zero
  disagreement/error/replay failure, and PAR-2 samples 2.529082/2.529085/
  2.529641/2.529659/2.529213 s (median 2.529213 s). The dominance audit
  certifies/checks 48/48; the target taxonomy is
  `vacuous-exists-universal-counterexample-unsat` with empty trust. Dominance
  remains 40/48 and Lean 8/16 UNSAT because ADR-0128 intentionally adds no Lean
  route. Six focused tests include 128 direct static-Z3 generated comparisons;
  the cumulative quantified-BV suite covers 1,592 cases/controls. Capability,
  support, foundational DAG, research question, P2.6, baseline, dominance, and
  scoreboard artifacts are refreshed. Solver library 866/866, evidence 69/69,
  focused/adjacent quantifier suites, all eight quantified-BV direct-Z3
  campaigns, strict workspace Clippy, warning-denied rustdoc, foundational
  137/174 resources, rules-as-code, links, formatting, and diff checks pass.
  The full `just check` aggregate again stops only at the known unrelated
  hardware-relative `frontier_bv_reduction` result, 28 decided versus the
  committed ratchet 30; the generated frontier artifacts were restored and no
  full-workspace green claim is made. Next: `nested9_true-unreach-call`, the
  smallest remaining row at 32 DAG nodes, through a separately checked
  paired-existential witness-transfer contract grounded in cvc5 CEGQI-BV and Z3
  projection; signed modular side conditions must be proved, not assumed.

- **2026-07-12 — recovery audit restores and bounds the checked ADR-0127
  boundary.** The post-switch worktree is preserved on
  `rescue/gpt54-dirty-20260712` and in an external bundle. Recovery removed
  unchecked vacuous-prefix, paired-existential, decision-only, model-guided,
  normalization, branch-splitting, and widened-candidate routes. Generated
  instances now require source provenance; targeted refutations require an
  independent original-IR theorem checker; every admitted SAT model replays
  against the untouched assertions. Global retained tuple joins are capped at
  8,192 per round, quantified Lean construction rejects oversized unary integer
  terms before allocation, and exact single-variable NRA coefficient overflow
  terminates as `ResourceLimit` instead of falling into unbounded abstraction.
  The stale word-fallback negative now uses a genuinely unsupported
  `str.indexof` mix; supported `str.from_int` coupling remains replay-checked.
  Fresh quantified-BV release measurement is **32 SAT / 15 UNSAT / 0 unknown /
  7 unsupported**, 47 agreements, zero disagreement/error/replay failure, and
  five-run PAR-2 median 3.008609 s. The dominance audit certifies/checks 47/47,
  marks 40/47 dominant, and reconstructs 8/15 UNSAT in Lean.
  Validation is green across solver library 866/866, Lean kernel 154/154,
  focused quantifier/e-graph/reconstruction suites, long NIA/NRA/UFLIA
  differentials, strict workspace Clippy, warning-denied rustdoc, foundational
  137/174 resources, rules-as-code, links, and all `axeyum-verify` tests and
  doctests. The explicit 2,000-instance quantified-UFLIA campaign completed in
  1,375.06 s: 1,052/1,052 jointly-decided agreements, 800 replayed SAT models,
  297 UNSAT, zero disagreement, and zero Axeyum errors. Its 256-instance smoke
  sweep remains in the default gate; the full campaign is retained as an
  explicit ignored test. A serialized workspace aggregate exceeded its outer
  wall cap only after reaching `axeyum-verify`; that package then passed in
  isolation, so no single-command aggregate pass is claimed. The
  hardware-relative `frontier_bv_reduction` remains 28/30 on both untouched
  `main` and recovery and is not weakened. **Next:** broaden checked
  nested/alternating BV QSAT and quantified-UF/function-valued models, then add
  Lean reconstruction for ADR-0124/0126/0127; preserve source-bound evidence,
  replay gates, and explicit resource limits in every increment.
- **2026-07-11 — ADR-0126 lands evaluator-replayed negated-existential
  witnesses.** One exact top-level `not (exists+ body)` over unique Bool/BV
  binders may carry complete typed values; the checker evaluates the untouched
  original quantifier-free body and accepts only true, with 128-binder and
  4,096-node caps. Search remains untrusted. `NUM878`, `ari-syqi`, and
  `ari118-bv-2occ-x` move **Unsupported→UNSAT** in median 3/0/3 ms. The cvc5
  quantified-BV slice is now **32 SAT / 14 UNSAT / 0 unknown / 8 unsupported**,
  with 46 agreements, zero disagreement/error/replay failure, and five-run
  PAR-2 median 3.508581 s. The audit certifies/checks 46/46, marks 40/46
  dominant, and Lean remains 8/14 UNSAT; all targets use
  `negated-existential-witness-unsat` with empty trust. All 1,400 direct-Z3
  cases/controls agree; focused tests are 6/6, solver library 863/863 and
  evidence 69/69, capability/support golden matrices, default pure-Rust check,
  workspace Clippy/rustdoc, foundational 137/174, links, formatting, and diff
  checks pass. The full solver run still stops only at the two known
  `bounded_string_replace_membership_deadline` wall caps; the unrelated
  `frontier_bv_reduction` 28/30 ratchet is unchanged. **Next:** certify
  `cond-var-elim-binary` (19 DAG), where the ground premise `k_332 < k_42`
  contradicts the exact universal instance at `x=1`. Keep the certificate
  source-bound and premise-aware; broader QSAT remains separate.
- **2026-07-11 — ADR-0125 lands scaled source-bound BV alternation.** Only
  ADR-0124's total-binder cap rises 128→1,024; the 4,096-node matrix cap and
  checker are unchanged. `bug802` (318 universal + 212 existential Bool/BV
  binders) moves **Unknown→UNSAT** with optimized median 19.804 ms. The cvc5
  quantified-BV slice is now **32 SAT / 11 UNSAT / 0 unknown / 11
  unsupported**, with 43 agreements, zero disagreement/error/replay failure,
  and five-run PAR-2 median 5.148639 s. The audit certifies/checks 43/43, marks
  40/43 dominant, and Lean remains 8/11 UNSAT; `bug802` uses
  `bv-alternation-counterexample-unsat` with empty trust. All 1,336 direct-Z3
  cases/controls agree. Alternation 6/6 and the 160-binder scaling matrix pass;
  solver 863/863, evidence 69/69, Clippy, rustdoc, generated matrices, links,
  foundational 137/174, formatting, and diff checks are clean. The independent
  full-workspace blocker remains the two
  `bounded_string_replace_membership_deadline` wall caps; the unrelated
  `frontier_bv_reduction` 28/30 ratchet remains unchanged. **Next:** add a
  checked original-body witness for the three smallest unsupported UNSAT rows
  `NUM878`, `ari-syqi`, and `ari118-bv-2occ-x`. They are exact negated
  existential closures, so one evaluator-replayed concrete witness suffices;
  search must remain untrusted. Four SAT and four UNSAT unsupported rows remain
  after that class.
- **2026-07-11 — ADR-0124 lands source-bound counterexamples for BV
  alternation.** One closed unique Bool/BV `forall+ exists+` implication with an
  outer-only antecedent can carry concrete outer bindings and a source-matched
  residual QF_BV DRAT/LRAT proof. Replay independently validates the prefix,
  binding order/sorts, exact substitution, deterministic existential freshening,
  CNF regeneration, and proof. `small-pipeline-fixpoint-3` moves
  **Unknown→UNSAT** with optimized median 63.692 ms. The cvc5 quantified-BV
  slice is now **32 SAT / 10 UNSAT / 1 unknown / 11 unsupported**, 42
  agreements, zero disagreement/error/replay failure, and five-run PAR-2 median
  5.613350 s. The audit certifies/checks 42/42, marks 40/42 dominant, and Lean
  remains 8/10 UNSAT; the target is `bv-alternation-counterexample-unsat` with
  empty trust. All 1,320 direct-Z3 cases/controls agree. Solver 863/863,
  evidence 69/69, alternation 4/4, Clippy, rustdoc, generated matrices,
  foundational 137/174, rules-as-code, and links pass. The full workspace run
  independently fails the two `bounded_string_replace_membership_deadline`
  30-second wall caps even in a serial isolated rerun; `just` is unavailable.
  The existing `frontier_bv_reduction` 28/30 ratchet remains unchanged.
  **Next:** characterize `bug802`, now the sole cvc5 quantified-BV unknown
  (3,317 DAG / 5,760 tree nodes), and pursue a checked alternation/invariant
  decomposition without enumerating its full BV domains. ADR-0124 Lean
  reconstruction and general QSAT remain separate open proof-ladder work.
- **2026-07-11 — ADR-0123 lands checked Boolean discharge of quantified BV
  closures.** ADR-0107's independent three-valued checker now admits
  Bool/Int/BV syntax while keeping non-reflexive BV predicates opaque. A
  complete carried free-Boolean assignment must make the untouched closure true
  independently of every BV value; unresolved BV formulas cannot enter the LIA
  fallback. `model_6_1_bv` moves **Unknown→SAT** with median 0.064489 ms. The
  cvc5 quantified-BV slice is now **32 SAT / 9 UNSAT / 2 unknown / 11
  unsupported**, with 41 agreements, no disagreement/error/replay failure, and
  five-run PAR-2 median 6.07677 s. The audit certifies/checks 41/41 and marks
  40/41 dominant; the target is `quantified-bool-model-sat`, dominant, and has
  empty trust. All 1,256 direct-Z3 cases and controls agree. Quantified LIA
  remains 12/12 (PAR-2 0.119 s) and Bitwuzla remains 5/5. Solver 863/863,
  Boolean-model 10/10, guard 5/5, certificate 13/13, evidence 69/69, and bench 7/7
  pass; workspace Clippy/rustdoc, matrices, links, foundational resources,
  rules-as-code, formatting/diff, and 26 references pass. The independent
  `frontier_bv_reduction` 28-versus-30 ratchet remains open and unchanged.
  **Next:**
  `small-pipeline-fixpoint-3` is the smaller remaining UNSAT unknown (235 versus
  3,317 DAG nodes). Derive a checked finite-state fixpoint/transition refutation
  from the original closure; do not enumerate the full 32-bit binder product.
- **2026-07-11 — ADR-0122 lands checked vacuous BV guard models.** A dedicated
  certificate carries one exact-width witness for one outer BV existential. The
  independent checker requires a nonempty direct unique Bool/BV quantifier
  prefix, a root implication, and an antecedent equating that exact binder with
  one same-width constant; the witness must differ, so the opaque consequent is
  irrelevant. `issue5365-nqe` moves **Unknown→SAT** with median 0.004147 ms. The
  cvc5 quantified-BV slice is now **31 SAT / 9 UNSAT / 3 unknown / 11
  unsupported**, with 40 agreements, no disagreement/error/replay failure, and
  five-run PAR-2 median 6.54204 s. The audit certifies/checks 40/40 and marks
  39/40 dominant; the target has empty trust. All 1,192 direct-Z3 cases and
  controls agree. Quantified LIA remains 12/12 (PAR-2 0.119 s) and Bitwuzla
  remains 5/5. Solver 863/863, guard 5/5, Boolean-model 6/6, certificate 13/13,
  evidence 69/69, bounded-instance, direct-Z3, and bench 7/7 suites pass;
  Clippy, rustdoc, matrices, links, foundational resources, rules-as-code,
  formatting/diff, and 26 references pass. The full workspace run exposes one
  independent open ratchet: isolated `frontier_bv_reduction` is 28 versus its
  committed baseline 30; the baseline was not weakened. **Next:**
  `model_6_1_bv` has a free-Boolean branch that can make
  its universal BV body globally true. Extend checked free-Boolean replay only
  for that exact structural discharge; do not imply general BV model/QE support.
- **2026-07-11 — ADR-0121 lands checked reflexive BV Skolem witnesses.** The
  existing arena-stable recipe now has one exact BV meaning: one same-width
  universal variable, coefficient one, constant zero. The independent checker
  substitutes it into the untouched `forall* exists` theorem and accepts only
  reflexive `bvsle`/`bvule` (plus equality); modular affine, composite, offset,
  foreign, width-mismatched, and tampered recipes decline. Attached certificates
  are checked before finite enumeration, closing the discovered width-16
  combinatorial replay path. Public `issue4328-nqe` moves **Unknown→SAT** with
  five-run optimized median 0.008736 ms. The 54-row cvc5 quantified-BV slice
  moves **29/9/5/11→30 SAT / 9 UNSAT / 4 unknown / 11 unsupported**, with
  DISAGREE=0, no errors/replay failures, and five-run PAR-2 median 7.00692 s.
  The audit certifies/checks 39/39; the target has empty trust and is dominant
  (division 38/39 dominant, Lean UNSAT 8/9). All 1,128 direct-Z3 and 900 bounded
  cases agree. Quantified LIA remains 12/12 (PAR-2 0.11871 s); Bitwuzla is now
  5/5 with one SAT/four UNSAT and no replay failure. Solver 863/863, witness
  14/14, certificate 12/12, evidence 69/69, MBQI 13/13, and bench 7/7 pass;
  workspace Clippy/rustdoc, matrices, foundational resources, links,
  formatting/diff, and 26 references pass. **Next:** `issue5365-nqe` is SAT by
  choosing outer `a != 0`, which makes its deeply alternating implication
  vacuous. Add a separately checked free-BV guard model over the untouched
  quantified source; do not broaden to general BV QE unless that narrow route
  fails measurement or checking.
- **2026-07-11 — ADR-0120 lands scoped SAT-candidate equality e-matching.** At
  an ordinary source-matching fixpoint, true equality atoms from the retained
  SAT candidate enter one temporary matching-e-graph scope. Exact merge paths
  execute affected patterns, a reverse index joins only their quantifiers, and
  concrete tuples are materialized before pop. Candidate equalities cannot
  become reasons/evidence; only complete exact source instances enter ADR-0119,
  and product UNSAT still requires ordinary QF replay. A nested-trigger target
  moves **Unknown→UNSAT** and improves optimized median **0.573→0.148 ms
  (74.2%, 3.87x)**. A 64-pattern target scans 1 pattern/application versus 64,
  returns the same tuple, and improves median **5.478→4.329 ms (21.0%,
  1.27x)**. cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11
  unsupported with zero disagreement/error/replay failure and PAR-2 7.47178 s;
  quantified LIA remains 12/12 with median 0.11852 s. All 1,064 direct-Z3 and
  900 bounded-instance cases agree; Bitwuzla retains four expected UNSAT rows
  and its known SAT replay alarm. Solver 863/863, e-matching 57/57, evidence
  69/69, MBQI 13/13, and bench 7/7 pass. Workspace Clippy/rustdoc, links,
  foundational resources, formatting/diff, generated matrices, and all 26
  references pass. Next: extend checked quantified-SAT Skolem replay to the
  exact `issue4328-nqe` BV theorem (`forall a. exists b. bvsle a b`, `b:=a`).
  All 16 remaining public BV blockers are nested/existential, so non-equality
  online antecedents and high-frequency callbacks are not the immediate
  decide-rate lever; online proof serialization remains the trust lane.
- **2026-07-11 — ADR-0119 lands checked quantifier clauses in retained
  CDCL(T).** The original ground Boolean/equality skeleton is encoded once;
  generated batches backtrack SAT/theory state to level zero, independently
  recheck exact-instance or recursive derivations, append root-stable equality
  atoms, and add permanent clauses while retaining learned clauses, VSIDS, and
  phases. Online SAT only resumes matching, and online UNSAT still requires an
  ordinary QF refutation of the exact admitted ground set. Unsupported,
  tampered, mismapped, and capped sessions fall back. A six-stage target cuts
  complete QF rebuilds **7→2** and five-run optimized median time
  **0.560→0.351 ms (37.3%, 1.60x)**. cvc5 quantified BV remains 29 SAT / 9
  UNSAT / 5 unknown / 11 unsupported with zero disagreement/error/replay
  failure and PAR-2 7.47183 s; quantified LIA remains 12/12 with three-run
  median 0.11770 s. All 1,000 direct-Z3 and 900 bounded-instance cases agree;
  Bitwuzla retains four expected UNSAT rows and its known SAT replay alarm.
  Solver 861/861, evidence 69/69, MBQI 13/13, and bench 7/7 pass. Workspace
  Clippy/rustdoc, links, foundational resources, formatting/diff, generated
  matrices, and all 26 reference checkouts pass. Next: measure and design
  SAT-trail-driven matching callbacks; non-equality antecedents and online proof
  serialization remain separate trust-boundary increments.
- **2026-07-11 — ADR-0118 lands bounded recursive quantifier ground
  provenance.** Every admitted generated equality/disequality retains an exact
  universal-instance or prior checked-propagation derivation. The public checker
  reconstructs every substitution, requires the exact sorted table for all
  non-source named reasons, recursively replays prior implications under
  depth-16/node-4,096 caps, and rejects missing/duplicate/unused/reordered,
  wrong-variant/conclusion, nested-tampered, and over-budget artifacts to
  complete-instance fallback. A six-stage target preserves UNSAT while DAG
  nodes fall **54→17 (68.5%)** and tree nodes **117→33 (71.8%)**. cvc5
  quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11 unsupported with
  zero mismatches/errors/replay failures and PAR-2 7.46909 s; quantified LIA
  remains 12/12 with median 0.11756 s. All 1,000 direct-Z3 and 900 bounded
  cases agree; Bitwuzla retains four expected UNSAT rows and its known SAT
  replay rejection. E-graph 35/35, e-matching/propagation 52/52, solver lib
  856/856, evidence 69/69, MBQI 13/13, and bench 7/7 pass. Workspace
  Clippy/rustdoc, links, foundational resources, formatting/diff, generated
  matrices, and all 26 reference checkouts pass. Next: reuse the
  checked implication in the direct online CDCL(T) quantifier-clause path;
  non-equality antecedents and proof serialization follow.
- **2026-07-11 — ADR-0117 lands source-bound checked detached quantifier
  literals.** A public certificate binds an untouched universal and ordered
  tuple to its exact complete instance, one remaining equality/disequality
  literal, and every false sibling's named original-ground reasons. A batch
  checker reconstructs instances in one fresh source context and separately
  replays each reason subset; generated-premise reasons fall back to complete
  instances. On 128 six-sibling matches, DAG nodes fall 4,230→2,438 and tree
  nodes 10,121→4,745; optimized QF median improves **8.250→3.226 ms (60.9%,
  2.56x)** and checked end-to-end median **11.301→9.886 ms (12.5%, 1.14x)**.
  cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11 unsupported with
  zero mismatches/errors/replay failures and PAR-2 7.46892 s; quantified LIA
  remains 12/12 with median 0.11825 s. All 1,000 direct-Z3 and 900
  bounded-instance cases agree; the known Bitwuzla SAT replay rejection remains
  beside four expected UNSAT rows. E-graph 35/35, e-matching/propagation 47/47,
  solver lib 851/851, evidence 69/69, MBQI 13/13, and bench 7/7 pass. Next:
  recursive generated-instance provenance, then direct online CDCL(T) reuse;
  non-equality literals and proof serialization follow.
- **2026-07-11 — ADR-0116 lands generation-delta top-application queues.** One
  complete initial match is retained; add rounds queue only new root
  applications and merge rounds queue ADR-0115-filtered path terminals. The
  unchanged recursive matcher appends candidate matches to monotonic caches,
  while joins/lifting canonicalize current roots. Current bridge terms are all
  active-source relevant, so a relevance bit would be a measured no-op. A
  one-pattern/4,096-application target scans 4,096 versus 1 top application with
  identical tuples and improves optimized complete-round median
  **0.370→0.122 ms (67.0%, 3.03x)**. cvc5 quantified BV remains 29 SAT / 9
  UNSAT / 5 unknown / 11 unsupported with zero mismatches/errors/replay failures
  and PAR-2 7.46919 s; quantified LIA remains 12/12 with median 0.11828 s. All
  1,000 direct-Z3 and 900 bounded-instance cases agree; the known Bitwuzla SAT
  replay rejection remains beside four expected UNSAT rows. E-graph 35/35,
  e-matching 42/42, solver lib 846/846, evidence 69/69, MBQI 13/13, and bench
  7/7 pass. Next: replayable false-sibling justifications for detached-literal
  propagation. Generation-cost scheduling and bytecode remain measurement-gated.
- **2026-07-11 — ADR-0115 lands exact class-label and nullary ground-argument
  path filters.** E-class roots retain sorted declaration sets through add,
  direct/congruence union, nested scopes, and rollback. Path terminals require
  the changed start class to contain a non-variable occurrence's top
  declaration; transitions may require one direct nullary ground sibling class
  to contain that constant declaration. Compound ground siblings remain
  unfiltered. A 64-pattern/4,096-application matrix reaches 64/8/8/1 terminals
  in unfiltered/class-only/ground-only/combined modes with identical complete
  tuples; optimized medians are **13.453/2.314/1.991/0.404 ms**, so combined
  filtering cuts complete-round time **97.0% (33.3x)**. cvc5 quantified BV
  remains 29 SAT / 9 UNSAT / 5 unknown / 11 unsupported with zero
  mismatches/errors/replay failures and PAR-2 7.46935 s; quantified LIA remains
  12/12 with median 0.11882 s. All 1,000 direct-Z3 and 900 bounded-instance
  cases agree; the known Bitwuzla SAT replay rejection remains beside four
  expected UNSAT rows. E-graph 34/34, e-matching 41/41, solver lib 845/845,
  evidence 69/69, MBQI 13/13, and bench 7/7 pass. Next: independently measure
  relevance/generation controls; bytecode remains measurement-gated and
  detached-literal justifications follow.
- **2026-07-11 — ADR-0114 lands compiled exact e-match parent paths.** Every
  interned pattern occurrence contributes outward `(declaration, argument)`
  steps to one deterministic shared trie. Merge lookup follows only compatible
  e-class parent arguments and records `(class, trie-node)` visited states, so
  common prefixes are shared and recursive equalities terminate without
  dropping paths. Add queues, union-journal index refresh, raw applications,
  and current-root joins remain unchanged. Direct/nested/repeated/ground,
  add-plus-merge, equal-application, duplicate/shared-prefix, divergent
  declaration/argument, multiple-start, cycle, and full-rematch parity pass. A
  64-pattern shared-root/4,096-term target executes 1 rather than 64 patterns
  and improves optimized complete-round median **12.777→0.386 ms (97.0%,
  33.1x)**. cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11
  unsupported with zero mismatches/errors/replay failures and PAR-2 7.46935 s;
  quantified LIA remains 12/12 with median 0.11791 s. All 1,000 direct-Z3 and
  900 bounded-instance cases agree; the known Bitwuzla SAT replay rejection
  remains beside four expected UNSAT rows. E-graph 33/33, e-matching 40/40,
  solver lib 844/844, evidence 69/69, MBQI 13/13, and bench 7/7 pass. Next:
  class-label/ground-argument filters, then relevance/generation controls;
  bytecode remains measurement-gated and detached-literal justifications follow.
- **2026-07-11 — ADR-0113 lands merge-incremental indexes and selective
  inverted-parent queues.** Every direct or congruence-cascade union enters a
  deterministic e-graph journal; retained indexes merge class membership from
  that journal and retain raw operator-indexed applications, rebuilding only
  after rollback/cross-graph reuse. The quantifier session follows transitive
  parent paths from changed equality endpoints, rematches only reached trigger
  roots, and joins cached substitutions through current roots. Visiting every
  raw top application fixes the explicit `f(a)=f(b)` completeness edge without
  collapsing distinct `a`/`b` bindings. Direct, repeated, nested, ground,
  add-plus-merge, cycle, rollback, and full-rematch parity tests pass. A
  64-root/4,096-term one-root merge executes 1 rather than 64 patterns and
  improves five-run optimized complete-round median **2.231→0.151 ms (93.2%,
  14.8x)**. cvc5 quantified BV is unchanged (29 SAT / 9 UNSAT / 5 unknown / 11
  unsupported, zero mismatches/errors/replay failures, PAR-2 7.46912 s), and
  quantified LIA remains 12/12 with median 0.11713 s. All 1,000 direct-Z3 and
  900 bounded-instance cases agree. The known Bitwuzla SAT replay rejection
  remains alongside four expected UNSAT rows. E-graph 33/33, e-matching 37/37,
  solver lib 841/841, evidence 69/69, MBQI 13/13, and bench 7/7 pass. Next:
  exact path-shape and relevance/generation filters; bytecode remains
  measurement-gated, then detached-literal justifications follow.
- **2026-07-11 — ADR-0112 lands revision-checked e-match indexes and add-only
  candidate queues.** `EMatchIndex` retains root-class membership and
  operator-indexed applications, extends from add-only node suffixes, and
  automatically rebuilds after real merges or scope rollback. The retained
  quantifier session caches complete per-pattern substitutions and dirties only
  patterns whose root declaration gained an application; merges conservatively
  invalidate all patterns. Fresh/indexed matching agrees across growth, nested
  congruence, and rollback. A 64-root/4,096-term target appends one application,
  returns identical complete tuples, executes 1 rather than 64 patterns, and
  improves five-run release median **2.555→0.311 ms (87.8%, 8.2x)** including
  refresh/join cost. The 54-row cvc5 quantified-BV slice remains 29 SAT / 9
  UNSAT / 5 unknown / 11 unsupported with zero mismatches/errors/replay
  failures and PAR-2 7.46905 s; quantified LIA remains 12/12 in three runs; the
  1,000-case direct-Z3 quantified-BV suites have zero disagreement. The known
  Bitwuzla SAT model-replay failure remains, alongside four expected UNSAT
  decisions. E-graph 30/30, e-matching 31/31, solver lib 835/835, evidence
  69/69, MBQI 13/13, bench 7/7, and the 900-seed soundness sweep pass. Next:
  inverted parent paths and selective merge queues, then relevance/generation
  filters. Bytecode remains measurement-gated; detached-literal justifications
  follow.
- **2026-07-11 — ADR-0111 lands shared incremental e-matching state.** One
  quantified refutation attempt now infers triggers once, interns identical
  recursive patterns, incrementally registers only appended ground source
  instances/equalities in one bridge, and executes all unique patterns through
  one batched class/application index per round. The public one-shot witness
  APIs and complete-source evidence contract are unchanged. A target with 32
  quantifiers and 256 ground applications preserves all 8,192 ordered tuples;
  five-run release median matching improves **17.477→0.974 ms (94.4%, 17.9x)**.
  A retained two-round chain gains `g(a)` only after asserting the first source
  instance and independently replays UNSAT. The 54-row quantified-BV division
  is decision-identical with PAR-2 within 0.03%; isolated quantified-LIA median
  is within 0.34% and remains 12/12. E-graph 27/27, e-matching 30/30, solver lib
  834/834, evidence 69/69, bench 7/7, the 900-seed soundness sweep, focused
  evidence/MBQI, direct-Z3 quantified-BV fuzz, workspace Clippy,
  warning-denied rustdoc, links, formatting/diff, generated matrices, and
  foundational resources pass. Next: direct add/merge candidate queues plus
  inverted parent paths and relevance/generation filters; bytecode remains
  measurement-gated against the recursive compiled baseline. Then land
  replayable false-sibling justifications, alternation/QSAT, and quantified-UF
  models.
- **2026-07-11 — ADR-0110 lands justified lazy quantifier-clause scheduling.**
  Equality/disequality clauses are three-valued from direct ground units,
  recorded disequalities, and the same congruence-closed e-graph used for
  matching. Any-true instances are suppressed; all-false and unit-like
  complete source instances run before unresolved/non-clausal fallback. No
  unjustified bare literal enters the solver or evidence path. The 256-match
  target schedules one instance (99.6% fewer) and improves five-run release
  median batch-plus-QF time **4.237→2.524 ms (40.4%)**. The 54-row quantified-BV
  slice is decision-identical to baseline (29 SAT / 9 UNSAT / 5 unknown / 11
  unsupported, zero mismatches/errors/replay failures), and quantified LIA
  remains 12/12. Solver lib 833/833, e-matching 29/29, the 900-seed
  bounded-instance sweep, focused evidence/MBQI, direct-Z3 quantified-BV fuzz,
  workspace Clippy, warning-denied rustdoc, links, formatting/diff,
  capability/support goldens, and 137-concept/174-pack foundational resources
  pass. The 2,000-case quantified-UFLIA debug fuzz was stopped after 15
  minutes/1.3 GB while CPU-active, so no pass is claimed. ADR-0111
  subsequently lands T2.6.1's shared matching-state slice.
- **2026-07-11 — ADR-0109 compacts Lean proof export without weakening the
  kernel boundary.** The opt-in renderer computes occurrence counts over the
  hash-consed expression DAG and hoists only repeated, compound, closed terms;
  loose de Bruijn variables and free locals are rejected, names and dependency
  order are deterministic, and the legacy renderer is unchanged. ADR-0108 now
  emits computational `Bool` as a real Lean inductive. `006-cbqi-ite` shrinks
  **151,845,067→2,682,977 bytes (98.23%)** and release reconstruction drops
  **17.74→10.75 seconds (39.43%)**. Fresh audit remains **12/12 decided,
  certified, checked, and dominant**, Lean UNSAT **8/8**, with no mismatch,
  timeout, audit error, replay failure, or trust hole. The explicit release
  regression requires a <3 MB, shared, real-`Bool`, `sorryAx`-free artifact;
  kernel renderer tests cover closed reuse, open-term rejection, determinism,
  and legacy stability. Verification: Lean kernel 154/154, solver lib 830/830,
  evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  workspace all-target/all-feature Clippy, warning-denied rustdoc, links,
  formatting/diff, and 137-concept/174-pack foundational resources. No external
  Lean binary or whole-workspace aggregate is claimed. Next: P2.6 lazy clause
  evaluation/MAM, then alternation and quantified-UF model/evidence boundaries;
  open-context sharing remains measurement-gated.
- **2026-07-11 — ADR-0108 closes the committed quantified-LIA division with
  checked counterexample covers and genuine kernel reconstruction.** Untrusted
  search weakens positive universals, generalizes concrete falsifying binder
  models to sufficient original free-Boolean cubes, and blocks candidates. The
  independent checker regenerates each exact source instance, proves every
  cube plus instance QF-unsatisfiable, and separately proves the weakened
  original skeleton plus all cube blocks QF-unsatisfiable. `006-cbqi-ite`
  carries 119 cases (maximum cube width 6), solves in about 1.2 seconds, and has
  empty trust steps. The first Lean slice retains one original universal leaf,
  applies every carried Bool/Int tuple, and closes a bounded excluded-middle
  tree with signed Boolean and normalized integer proofs. Fresh release audit
  is **12/12 decided, certified, checked, and dominant**, Lean UNSAT **8/8**,
  with DISAGREE=0 and no replay failure, mismatch, audit error, timeout, or
  trust hole. Its initial tree-expanded kernel artifact took about 17.7 seconds
  and rendered about 152 MB; ADR-0109 now closes that serialization debt.
  Verification: focused default/all-feature 5 passed + 1 explicit release
  validation, solver lib 830/830, evidence 69/69, bench 7/7,
  capability/support goldens 2/2 and 12/12, workspace all-target/all-feature
  Clippy, warning-denied rustdoc, links, formatting/diff, and
  137-concept/174-pack foundational resources. No external Lean binary or
  whole-workspace aggregate is claimed.
- **2026-07-11 — ADR-0107 closes both remaining quantified-LIA SAT rows with
  checked Boolean-guard models.** Search solves a quantifier-erased Boolean
  skeleton, but SAT credit requires canonical replay of an arena-stable
  original-symbol assignment. The checker retains untouched assertions, drops
  only positive universal binders, exactly lifts integer `ite`, and source-binds
  a self-checked LIA-DPLL refutation of the negated closure. Large propositional
  closures use source-matched DIMACS/DRAT instead of the old 22-Boolean
  enumeration ceiling. Counterexample paths generalize search blocking cubes
  only. `015-psyco-pp` and `psyco-196` are now replay-checked SAT; release
  measurement is **11/12** (sat 4, unsat 7, unsupported 1), DISAGREE=0, with no
  replay failures. The audit is checked/certified **11/11**, Lean UNSAT **7/7**,
  dominant **11/11**, with zero mismatch, audit error, timeout, or trust hole.
  `006-cbqi-ite` is the sole remaining row and needs symbolic/clause-level
  CEGQI; SAT-side model construction is no longer the blocker.
  Verification: focused default and all-feature integration 6/6, solver lib
  830/830, evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  workspace all-target/all-feature Clippy, warning-denied rustdoc, links,
  formatting/diff, and 137-concept/174-pack foundational resources. No external
  Lean binary is installed; the known Sturm nontermination still prevents a
  whole-workspace aggregate claim.
- **2026-07-11 — ADR-0106 closes the current quantified-LIA Lean proof gap.**
  The ADR-0101 certificate is rechecked before a recursive proof engine retains
  genuine Bool/Int quantifiers and exact guarded integer/Boolean `ite`
  propositions. Arbitrary witnesses are eliminated with `Bool.rec` or the new
  explicit standard `IntPrelude::eq_em`; the finite quotient evaluator remains
  untrusted proof-search guidance. The real `cbqi-sdlx-fixpoint-3-dd` row,
  polarity/connective/quantifier controls, tamper, multi-constant boundary, and
  direct-arithmetic declines pass 5/5. Fresh release audit is checked/certified
  **9/9**, Lean UNSAT **7/7**, dominant **9/9**, with zero mismatch, audit
  error, timeout, or trust hole. This completes proof credit for decided rows,
  but the division remains 9/12: the three large affine-ITE rows are still the
  decide-rate frontier, and multi-constant partitions remain a separate Lean
  extension.
  Verification: integer prelude 7/7, focused all-feature reconstruction 5/5,
  solver lib 829/829, evidence 69/69, bench 7/7, capability/support goldens 2/2
  and 12/12, workspace Clippy, warning-denied rustdoc, links, formatting/diff,
  and 137-concept/174-pack foundational resources. No external Lean binary is
  installed; the known Sturm nontermination still prevents a whole-workspace
  aggregate claim.
- **2026-07-11 — ADR-0105 lands constructive affine-growth Lean
  reconstruction.** The full checked ADR-0097 class retains every original Int
  binder and translates integer `ite` exactly into two guarded branch
  implications. ADR-0104 decomposition plus `r<c` proves the affine comparison
  at `q+1`; positive-slope monotonicity transfers it to `q+2`. Both guarded
  instances produce double-negated pivot equalities, and strict consecutive
  ordering closes constructively with no classical or new arithmetic axiom.
  The real ten-binder target, signed/swapped multi-binder class member, tamper,
  and binder-dependent near miss pass 4/4. Fresh release audit is
  checked/certified **9/9**, Lean UNSAT **6/7**, dominant **8/9**, with zero
  mismatch, audit error, timeout, or trust hole. Finite equality partition is
  now the sole current UNSAT proof gap; the three large affine-ITE engine rows
  remain unchanged.
  Verification: focused all-feature reconstruction 4/4, solver lib 829/829,
  evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  workspace Clippy, warning-denied rustdoc, links, formatting/diff, and
  137-concept/174-pack foundational resources. No whole-workspace aggregate is
  claimed because of the known pre-existing Sturm nontermination.
- **2026-07-11 — ADR-0104 lands Euclidean-residue Lean reconstruction.**
  `IntPrelude` now explicitly admits the standard positive-modulus existential
  decomposition theorem `t = k*q+r`, `0<=r`, `r<k`, without adding div/mod
  operations. The proof route rechecks ADR-0095, preserves the canonical clock
  theorem, eliminates quotient/remainder witnesses, and refutes all three
  disjuncts by equality symmetry and order irreflexivity. Prelude exact-type,
  both committed rows/router, tampered-certificate, and satisfiable weakened-
  bound tests pass. Fresh release audit is checked/certified **9/9**, Lean UNSAT
  **5/7**, dominant **7/9**, with zero mismatch, audit error, timeout, or trust
  hole. The two remaining proof gaps are affine growth and finite equality
  partition; the same Euclidean theorem is the next candidate for affine
  growth. The three large affine-ITE engine rows remain unchanged.
  Verification: focused all-feature reconstruction 3/3, integer prelude 6/6,
  solver lib 829/829, evidence 69/69, bench 7/7, capability/support goldens 2/2
  and 12/12, workspace Clippy, warning-denied rustdoc, links, formatting/diff,
  and 137-concept/174-pack foundational resources. No whole-workspace aggregate
  is claimed because of the known pre-existing Sturm nontermination.
- **2026-07-11 — ADR-0103 lands genuine nested-XOR Lean reconstruction.** The
  ADR-0099 certificate is regenerated before proof construction. The original
  universal is instantiated at both outer pivots; one classical
  excluded-middle split derives the nested universal from the outer XOR; an
  adjacent off-pivot nested instance then forces a false integer equality.
  Same-branch ITE equality is translated as `Iff` of its guards only after the
  certificate validates equal distinct branches. Permanent stage gates cover
  the selector Iff/falsity, outer orientation normalization, nested universal/
  instance, and final equality/disequality. Focused tests pass the real
  `issue4433-nqe`, a signed/swapped control, and tamper rejection. Those tests
  caught and closed a loose outer de Bruijn variable and a signed-literal
  definitional-equality mistake. Fresh audit is checked/certified **9/9**, Lean
  UNSAT **3/7**, dominant **5/9**, with no mismatch, audit error, timeout, or
  trust hole. Four UNSAT proof gaps remain; the three large affine-ITE engine
  rows remain unchanged.
  Verification: focused all-feature 3/3, solver lib 829/829, evidence 69/69,
  bench 7/7, capability/support goldens 2/2 and 12/12, all-feature workspace
  Clippy, warning-denied rustdoc, formatting/diff, links, and
  137-concept/174-pack foundational resources. No whole-workspace test aggregate
  is claimed because of the known pre-existing Sturm nontermination.
- **2026-07-11 — ADR-0102 lands genuine Lean reconstruction for checked
  closed-universal counterexamples.** The ADR-0100 certificate is rechecked
  against the untouched assertion, which is translated to dependent products
  over the existing computational Bool and integer ring preludes. Ordinary
  `forall` application specializes the theorem at the carried witnesses;
  integer normalization proves the resulting equality (`ARI176e1`) or literal
  disequality after Bool-rec ITE reduction (`issue5279-nqe`). No
  theorem-specific `P -> False` refuter axiom is introduced. Focused tests cover
  both real rows through the public certificate API and generic router plus
  tamper rejection; the optional external Lean check was skipped because no
  `lean` binary is installed. Fresh dominance audit remains checked/certified
  **9/9**, and moves from Lean UNSAT 0/7 and two dominant candidates to **Lean
  UNSAT 2/7 and 4/9 dominant candidates**, with no mismatch, audit error,
  timeout, or trust hole. The other five UNSAT certificate families remain
  uncredited; engine focus remains the three large affine-ITE rows.
  Verification: focused all-feature 3/3, solver lib 829/829, evidence 69/69,
  bench 7/7, capability/support goldens 2/2 and 12/12, all-feature workspace
  Clippy, warning-denied rustdoc, formatting/diff, links, and
  137-concept/174-pack foundational resources. The known pre-existing Sturm
  nontermination means no whole-workspace test aggregate is claimed.
- **2026-07-11 — ADR-0101 lands checked finite equality-partition
  quantifiers.** A closed nested Bool/Int formula is admitted only when every
  Int binder occurrence is a direct equality against an explicit signed
  constant. Each binder then has an exact finite quotient: every mentioned
  constant plus one deterministic other representative. Search independently
  constructs and evaluates the expansion in a clone; evidence checking instead
  recursively interprets quantifiers and Boolean connectives over the untouched
  original arena, with a 2^20 representative-case cap. This decides
  `cbqi-sdlx-fixpoint-3-dd`. Six focused all-feature tests include target,
  tamper, signed/multiple constants, Bool/exists nesting, free/direct-arithmetic
  declines, valid controls, and a 64-UNSAT + 64-valid static-Z3 sweep. Fresh
  release corpus is **9/12** (sat 2, unsat 7, unknown 0, unsupported 3),
  DISAGREE=0, errors/replay failures 0, PAR-2 mean 6.667 s. Audit is checked and
  certified **9/9**, dominant candidates 2, Lean UNSAT 0/7, with no mismatch,
  audit error, timeout, or trust hole. Remaining: two large SAT affine-ITE rows
  need general quantified model construction and the large UNSAT row needs
  scalable CEGQI; the finite quotient does not address those engines. A
  post-landing prototype flattened the direct universal conjunct in
  `006-cbqi-ite` and used model-fixed QF counterexample tuples: 8 rounds ended
  unknown in 8.2 s and a 32-round shared-deadline run still ended unknown at
  30.0 s. It was reverted (zero measured ROI). The next UNSAT lever needs
  symbolic tuple/clause-level CEGQI, not one concrete 40--50-component tuple per
  round.
- **2026-07-11 — ADR-0100 lands evaluator-replayed closed-universal
  counterexamples.** The two remaining bare quantified-LIA UNSAT decisions share
  one proof object: concrete values for every binder of a closed quantifier-free
  scalar universal. Search uses fresh constants and the ordinary QF solver, but
  the public certificate stores original binder IDs/typed values and a separate
  checker evaluates the untouched original body, accepting only `false`.
  Open/nested/UF/non-scalar forms decline. Both `ARI176e1` and `issue5279-nqe`
  now carry `closed-universal-counterexample-unsat` with zero trust steps.
  Focused target/tamper/decline/validity tests and a static-Z3 sweep of 64 false
  universals plus 64 valid controls pass. Fresh release corpus remains **8/12**
  (sat 2, unsat 6, unsupported 4), DISAGREE=0, errors/replay failures 0; the
  audit is now checked **8/8** and certified **8/8**, dominant candidates 2,
  Lean UNSAT 0/6, with no mismatches, audit errors, timeouts, or trust holes.
  The immediate post-landing census splits those four rows: the 19-line
  `cbqi-sdlx-fixpoint-3-dd` is a closed nested formula whose quantified integers
  are observed only through equality to constants, so exact finite-partition
  expansion is the next bounded reusable lever. The 299–422-line
  `006-cbqi-ite`/`015-psyco-pp`/`psyco-196` rows instead quantify 40–50 mixed
  Bool/Int variables through affine `ite` networks; they remain general
  CEGQI/model-construction work, not part of that finite slice. Lean
  reconstruction remains the separate proof-parity lane.
- **2026-07-11 — ADR-0099 lands checked nested-XOR hierarchical
  instantiation.** For the exact all-`Int` theorem behind `issue4433-nqe`,
  search instantiates the two outer selectors at their pivots, which makes the
  first XOR false and exposes the positive nested universal; one inner
  off-pivot instance then equates distinct constants. The ordinary QF solver
  must refute that genuine consequence. A separate checker independently
  re-matches the untouched original two-outer/one-inner XOR/equality/`ite`
  structure. Four focused evidence tests, two qinst tests, and a static-Z3 sweep
  of 64 permuted UNSAT schemas plus 64 satisfiable wrappers pass. Fresh 10 s/job
  release corpus: **8/12** (sat 2, unsat 6, unknown 0, unsupported 4),
  DISAGREE=0, errors/replay failures 0. Eight-decision audit: checked 8/8,
  certified 6/8, dominant candidates 2, Lean UNSAT 0/6, with no mismatches,
  audit errors, timeouts, or target trust holes. No rows remain incomplete.
  Next, close the two bare-UNSAT evidence debts (`ARI176e1`, `issue5279-nqe`),
  then return to the four unsupported Boolean-heavy universals.
- **2026-07-11 — ADR-0098 lands checked guarded unit-gap Skolem SAT.** The
  witness pass may pull one direct existential through a positive binary `or`
  when the binder is absent from the guard, but public SAT credit comes only
  from a separate original-IR checker for
  `upper <= lower+1 or exists z. lower<z<upper` over `Int`/`Real`. The witness
  is globally `lower+1`; no piecewise function is needed. The benchmark's
  cloned-backend replay exposed a certificate-format defect: synthesized
  `TermId`s belonged only to the solver clone. Certificates now own a
  deterministic affine recipe over validated original-arena atoms and
  materialize it only in the checker's private clone. Untouched-arena replay,
  target/Real positives, tampering, missing-margin and polarity negatives pass;
  a 64-seed static-Z3 positive sweep plus 32 integer negatives is clean. Fresh
  10 s/job release corpus: **7/12** (sat 2, unsat 5, unknown 1, unsupported 4),
  DISAGREE=0, errors/replay failures 0. Seven-decision audit: checked 7/7,
  certified 5/7, dominant candidates 2, Lean UNSAT 0/5, no mismatches/errors/
  timeouts/trust holes. The two bare UNSAT rows still prevent division-level
  Pareto dominance. This checkpoint handed off `issue4433-nqe`, now completed
  by ADR-0099 above; four Boolean-heavy rows remain unsupported.
- **2026-07-11 — checked quantified-LIA CEGQI and Skolem SAT are live.** The
  P2.6 e-graph fallback now recognizes only the exact Presburger partition
  `forall s m. k*m+s != t or s<0 or s>=k` (`k>0`), proposes the symbolic
  counterexample `s=mod(t,k), m=div(t,k)`, and returns `unsat` only when the
  ordinary QF solver independently refutes the genuine universal instance plus
  the ground query. Exact `k=3`/`k=10` and satisfiable near-miss controls pass.
  A fresh one-job 10 s run of the committed 12-file quantified-LIA slice moves
  current HEAD **2→5/12**: `clock-3`/`clock-10` become UNSAT and
  `issue4849-nqe` becomes SAT, matching all five cvc5 regression statuses with
  no other movement, errors, or replay failures.
  The old committed scoreboard row is 0/12 and predates several quantifier
  landings; it must be regenerated under a restored native Z3 oracle before its
  generated headline changes. Remaining census: 3 incomplete, 4 unsupported.
  **ADR-0096 now closes that quantified-SAT representation boundary for a first
  checked slice:** `Model` carries deterministic typed Skolem certificates and
  canonical `check_model` independently re-matches/substitutes the original
  `forall* exists` assertion, accepting only affine/reflexive tautologies. The
  identity witness `b:=a` now recovers `issue4849-nqe` without an empty-model
  replay bypass. **ADR-0095 closes the new UNSAT evidence debt:** a separate checker
  independently re-matches the exact positive-modulus theorem over the original
  IR, so `clock-3`/`clock-10` now carry certified
  `UnsatIntEuclideanResidue` evidence with zero trust steps. **ADR-0097 adds the
  positive-slope affine-growth theorem:** for
  `forall xs. not(c*x - ite(x=p,a,b) >= t)`, `c>0`, the consecutive candidates
  `div(b+t,c)+1` and its successor both clear the bound and cannot both equal
  `p`. Search adds those two genuine instances and requires an ordinary QF
  refutation; a separate original-IR matcher certifies the theorem without
  calling search. `repair-const-nterm` now decides in about 1.3 ms, moving the
  slice **5→6/12** (sat 1, unsat 5), DISAGREE=0, with no errors or replay
  failures. The six-decision audit is evidence-certified 4/6,
  evidence-rechecked 6/6, Lean-checked 0/5 UNSAT; one SAT row is individually
  dominance-eligible, but two bare UNSAT rows prevent a division claim. Its
  satisfiable binder-dependent controls exposed a legacy cartesian-instantiation
  stack overflow: duplicate instances from unused binders are now deduplicated
  and the conjunction is balanced. At this checkpoint six rows remained; the
  later ADR-0098 entry above closes `sygus-infer-nested`; ADR-0099 subsequently
  closes nested-QE `issue4433-nqe`.
- **2026-07-11 — aggregate validation repaired a nested AUFBV guard invariant.**
  The default workspace sweep exposed a deterministic failure when an array
  equality flag occurred only below a bit-vector expression: the e-graph could
  cite `!ext_eq_*` in a parent-equality explanation, but dynamic interface
  clauses could not address it because top-level Boolean atom discovery had not
  registered the flag. `build_theory_atoms` now registers every prepared array
  equality flag in stable preparation order, preserving its original equality
  for EUF. The full `abv_lazy_ext` integration file passes (10/10), including
  the nested-equality replay case. The unrelated 5 ms SOS wall-clock assertion
  exposed by that aggregate is now repaired: the test directly requires and
  independently checks `Evidence::UnsatSos`, proving the intended route without
  a hardware-sensitive timing proxy. A subsequent all-feature aggregate advanced
  to the hardware-relative `bv_reduction` frontier: both this worktree and an
  untouched detached `HEAD` stop at 28 versus committed baseline 30 on this host
  (`N=29/30` expire at about 4.02 s versus the artifact's 3.73/3.84 s). The
  baseline is preserved; CI mode intentionally records but does not enforce this
  dev-box-relative ratchet. The serialized CI-mode all-feature aggregate then
  passed every suite through that frontier, including the 737 s variable-div/mod
  and 1,353 s quantified-UFLIA differential fuzzers, before the pre-existing
  `sturm_overflow_declines_gracefully` test consumed a full core without
  terminating for 30 minutes; the run was stopped there, so this is not recorded
  as a full aggregate pass. Independent strict workspace Clippy, warning-denied
  rustdoc, formatting, link, foundational-resource, capability/support-matrix,
  focused quantified-certificate, and benchmark-harness gates are green.
- **2026-07-11 — regex canonicalization/derivative deadline guard is closed.**
  The string membership route now has a budgeted `canon_within` alongside
  `derivative_within`. Deadline-bounded solve/refute/witness paths canonicalize
  the combined regex through that pollable path, and every derivative residual
  canonicalization is interruptible too. Regressions pin: budgeted canon equals
  plain canon when the poll never trips; a tight poll aborts a large union spine;
  derivative-within still matches derivative under a never-tripping poll; and a
  pathological `Σ*`-enlarged membership intersection declines within the
  deadline, including the already-past-deadline entry case. The #49 concat
  follow-up (#55) and LenAbs bridge (#53) were already landed; remaining string
  work is the unsupported extended-function/sequence residue and Nielsen class.
- **2026-07-10 — memory-aware k-induction is live.**
  `prove_safety_k_induction_with_memory` extends the existing k-induction
  driver to array/symbolic-memory transition systems. The base case reuses
  `bounded_model_check_with_memory`; each inductive step uses
  `IncrementalBvSolver::check_with_memory`; unsupported theory shapes now
  surface as `SafetyOutcome::Unknown` rather than hard errors. A `Safe` result
  is still an unbounded k-induction result, but remains validation-backed rather
  than certified until array-aware proof export exists. Focused BMC module tests
  cover both an inductive array property and a reachable symbolic-memory
  counterexample. Next: certified memory k-induction, memory PDR/IMC, online
  array proofs, nested/extended arrays, and broader low-load aggregate timing.
- **2026-07-10 — nested warm array-valued UF parameters are live.**
  ADR-0094 admits supported array-valued `Apply` terms as finite-array keys to
  retained array-valued UF parents, both directly (`f(g(a))`) and inside
  supported structural keys (`f(store(g(a), k, v))`). Direct nested keys use
  the inner application's private projection symbol; structural keys use the
  replay-safe rewritten structural term. The warm array-UF parent suite now
  covers direct nested-key SAT replay, asserted nested-key equality UNSAT, and
  structural keys with nested application bases. Memory-aware k-induction
  subsequently lands. Next: certified memory k-induction, memory PDR/IMC,
  online array proofs, nested/extended arrays, and broader low-load aggregate
  timing.
- **2026-07-10 — structural warm array-valued UF parameters are live.**
  ADR-0093 admits supported `store`/`const-array`/array-ITE expressions as
  finite-array keys to retained array-valued UF parents. Scalar dependencies
  inside keys are retained before solving; private structural key owners are
  realized against the original structural terms before full-value `FuncValue`
  projection; and key congruence uses active equality classes or ADR-0091
  relation flags. The warm array-UF parent suite now covers structural-key SAT
  replay, relation-flag separation of independent structural keys, asserted
  structural-key equality UNSAT, and the former nested array-valued
  application-key deferral. ADR-0094 subsequently lands supported nested
  application keys. Next: memory BMC/k-induction, online array proofs,
  nested/extended arrays, and broader low-load aggregate timing.
- **2026-07-10 — direct warm array-valued UF parameters are live.** ADR-0092
  admits direct finite-array symbols as parameters to retained array-valued UF
  parents. Scalar parameters still use the existing warm abstraction; direct
  array-key equality uses either an active retained equality class or a private
  ADR-0091 relation flag, so function read congruence stays Boolean/BV-only.
  SAT projection now separates non-equal array-key classes with deterministic
  full array values before building `FuncValue` tables, while preserving
  user-visible select constraints and ignoring private guarded relation reads as
  public entries. Focused gates pass in the warm array-UF parent suite, including
  independent-key SAT replay, asserted-equality UNSAT, the private relation-flag
  count, and structural array-key deferral. ADR-0093 subsequently lands
  supported structural array-valued parameter expressions; nested array-valued
  application keys, memory BMC/k-induction, online array proofs, and broader
  low-load aggregate timing remain.
- **2026-07-10 — nested warm array relation flags are live.** ADR-0091
  admits supported array equality atoms under scalar Boolean structure by
  replacing each atom with a private candidate-sensitive flag. True flags add
  guarded paired-read equality observations and are the only flagged equalities
  merged/realized during projection; false flags add one guarded private diff
  witness. New and existing compatible read indices receive guarded observations,
  private flags/witnesses/owners are filtered, and original replay gates SAT.
  Focused gates pass: 5 relation-flag tests plus the ADR-0088/0089/0090 suites,
  with stale nested-Boolean deferrals converted to positive warm coverage.
  ADR-0092 subsequently lands direct array-valued UF parameters, and ADR-0093
  lands supported structural array-valued parameter expressions. Next: nested
  array-valued application keys, memory BMC/k-induction, online array proofs,
  and broader low-load aggregate timing.
- **2026-07-10 — retained warm structural array equality is live.** ADR-0090
  admits top-level positive equality over supported structural store/constant/
  array-ITE parents, alongside direct symbols and scalar-keyed array-valued UF
  parents. Structural parents get cached private constructor owners; equality
  adds bounded old/future shared-index observations plus a private probe; model
  projection realizes owner equations to a class-aware fixed point before array-
  valued function construction, filters private owners, and replays originals.
  Default gates pass: 8 structural-equality tests, the ADR-0088 and ADR-0089
  focused suites, and replay on every SAT matrix row. ADR-0090 is accepted.
  ADR-0091 subsequently lands nested Boolean relation flags, ADR-0092 lands
  direct array-valued UF parameters, and ADR-0093 lands supported structural
  parameter expressions. Nested array-valued application keys, memory
  BMC/k-induction, online array proofs, and broader low-load aggregate timing
  remain.
- **2026-07-10 — warm array relations now include exact diff witnesses.**
  ADR-0089 accepts positive equality between direct/application projection
  owners and top-level disequality over symbol/store/constant/ITE/application
  parents. Equality classes merge before array-valued function construction;
  disequality allocates one private BV index and sends both witness reads through
  candidate-triggered semantics. Private owners stay hidden and originals
  replay. Eight default/nine all-feature tests add 192 clean warm/`check_auto`/
  Z3 comparisons; exact depth, unsupported structural-positive
  deferral, all 816 solver units, 77 symexec tests, and complete EVM gates pass.
  Commits `d891c901`/`70c8a15c` are on `origin/main`. EVM has no whole-array
  relation root, so no timing delta is claimed. ADR-0090 subsequently lands
  positive structural equality and ADR-0091 subsequently lands nested Boolean
  relation flags, ADR-0092 lands direct array-valued UF parameters, and
  ADR-0093 lands supported structural parameter expressions; nested array-valued
  application keys, memory BMC/k-induction, and online proofs remain.
- **2026-07-10 — array-valued UF parents are retained on the warm path.**
  ADR-0088 admits scalar-keyed applications returning BV-indexed Bool/BV arrays
  as private warm leaves. Conditional argument/index congruence constrains their
  reads; projection merges split observations by concrete argument tuple, builds
  full-value function results, filters private owners, and replays originals.
  Store/ITE parents compose with ADR-0087 summaries. Ten all-feature tests and a
  64-seed warm/`check_auto`/Z3 matrix give 192 clean comparisons; exact 64/65-
  parent admission, 816 solver units, 77 symexec tests, the canonical array-
  result integration, and complete EVM gates pass. Commits `41019413`/
  `f2bb16ab` are on `origin/main`. EVM has no array-result UF case, so no timing
  change is claimed. ADR-0089/0090 subsequently land warm relations and
  structural equality, relation flags, direct array-valued UF parameters, and
  supported structural parameter expressions; nested array-valued application
  keys, memory BMC/k-induction, and online proofs remain.
- **2026-07-10 — retained warm ROW is candidate-triggered.** ADR-0087 stores one
  exact bounded transitive scalar summary per observed store/constant/array-ITE
  read as dormant metadata. Candidate-false summaries become permanent CNF roots
  and resume the same BatSat instance under one shared deadline; inactive pending
  summaries create no work, selectors and assumption cores remain sound, direct
  leaves alone project models, and original replay gates SAT. Ten all-feature
  mechanism/differential tests keep the 192 warm/`check_auto`/Z3 comparisons at
  zero disagreements; all 816 solver units, 77 symexec tests, and complete EVM
  gates pass. Commits `c777e756`/`3977f78b` are on `origin/main`. Release EVM
  depth 32 improves 30.933→11.257 ms, while ITE-fold remains faster at 0.405 ms.
  ADR-0088/0089/0090 subsequently land array-valued UF parents, warm relations,
  and structural equality; memory BMC/k-induction, online proofs, and the
  remaining performance gap remain.
- **2026-07-10 — structural array reads gained retained warm owners.** ADR-0086
  advances ADR-0030 in the existing `IncrementalBvSolver`: observed reads over
  store, constant-array, and array-ITE parents get private scalar owners whose
  exact definitions are installed once in the persistent CNF. Scoped user roots
  retract normally; only direct symbol leaves project array models; original
  replay gates SAT. The 512-node/256-depth limits defer one-over inputs. A
  64-seed matrix adds 64 warm + 64 `check_auto` + 64 direct-Z3 comparisons with
  zero disagreements; all 816 solver units, 77 symbolic-execution tests, and the
  complete EVM suite pass. Commits `4caed2ec`/`47c152ec` are on `origin/main`.
  The EVM depth-32 measurement is deliberately not called a speedup: frontend
  ITE folding is 0.368 ms vs 30.933 ms for retained observation-time definitions.
  ADR-0087 subsequently makes one exact transitive summary per observed owner
  candidate-triggered and improves the warm row to 11.257 ms.
- **2026-07-10 — bounded structural array-class equations are live.** ADR-0085
  rewrites array-ITE equality exactly into branch equalities before canonical
  search, so selected branches reach `EufTheory`; candidate-true store/ITE/
  constant equations then realize class-owned leaf arrays without changing any
  observed scalar read. Fixed-point, 256-leaf, 256-depth, 4,096-step, and shared-
  deadline bounds degrade to classified `Unknown`, and original replay remains
  mandatory after array-first/function-second projection. The 16-shape matrix
  adds 64 direct + 64 front-door + 64 Z3 comparisons, all clean; explicit SMT-
  LIB, Bool/Int boundary, cap, deadline, array-result/store, and nested-UF gates
  pass. All 816 solver units and the existing AUFBV/array-result belts pass;
  commits `e47da7a1`/`da957695` are on `origin/main`. Next: true warm array/UF
  ownership, nested/extended arrays, online array proof logging, and low-load
  aggregate measurement.
- **2026-07-10 — array-valued UF results now ride the canonical array bus.**
  ADR-0084 admits finite Bool/BitVec array results in IR/SMT-LIB and function
  abstraction while eager Ackermann elimination declines its non-scalar target.
  `select(f(args), i)` retains the original application as e-graph parent and
  uses the abstraction's fresh array as projection owner. Final parent classes
  union split observations across congruent applications; array-first/function-
  second projection then supplies full-value results and array-valued keys before
  mandatory replay. Six mechanism tests plus 96 direct, 96 front-door, and 96
  Z3 cases cover stores, array ITEs, equality/disequality, split observations,
  and nested scalar-UF use with zero disagreements. All 815 solver unit tests,
  the existing 11-test AUFBV fuzz, strict clippy, and the exact-SHA push gate
  pass. ADR/implementation commits `b1bc1836`/`e944f7c1` are on `origin/main`.
  ADR-0085 subsequently closes bounded structural store/ITE/constant class
  projection. Warm ownership, online ROW/extensionality/equality-chain proof
  logging, and the low-load aggregate remain.
- **2026-07-10 — BV lowering now honors the query deadline.** A fresh 1 s
  QF_AUFBV cvc5 regression run exposed `unconstrained__array1.smt2` returning
  after 437.5 s because five BV1024 dividers were built before warm SAT saw its
  timeout. One-shot and incremental lowering now poll an absolute deadline
  between DAG nodes and inside wide circuits; solver boundaries classify expiry
  as `Unknown(Timeout)`. Canonical BV also shares the conservative cumulative
  projected-clause gate, so the exact public row now returns
  `Unknown(EncodingBudget)` in 1 ms (157,298,694 projected clauses vs the
  64,000,000 ceiling). The fresh nine-row slice is 7 SAT / 1 unknown / 1
  unsupported, DISAGREE=0, replay failures=0; 17 lowerer, 53 canonical, 4
  deadline, and 28 SAT-BV tests pass. ADR-0083; `85e007b2`. Next: resume
  array-valued UF/select events and their cyclic function/array projection;
  broader low-load ABV/AUFBV aggregates and online proof logging remain.
- **2026-07-10 — pair-generated UFBV/AUFBV interfaces now refine inside one
  canonical search.** ADR-0082 gives `CdclT` explicit SAT-variable/theory-atom
  maps, so equality atoms appended after Tseitin auxiliaries preserve every
  existing variable, clause, trail, and reason index. `EufTheory` grows only over
  sides observed before search; exact BV owns the arena clone and grows aligned
  atom state. Candidate-violated function, explanation-guarded base/store-select,
  and bounded array-equality/extensionality interfaces now append and activate
  only their required atoms or clauses, then resume with learned clauses,
  phases, activities, e-graph state, and warm BV state retained. Former two- and
  three-round UF/select/mixed controls now pin one round. The new 384-comparison
  eager/front-door/Z3 matrix brings the clean array total to 2,304; all 809
  solver tests and the 11-test differential binary pass. Commit `39cc92ce`
  passed the exact-SHA pre-push gate and is on `origin/main`. Next: array-valued
  ITE/default/UF and merge-triggered events requiring new e-graph terms, non-
  symbol/warm class models, proof logging, and a low-load public remeasure.
- **2026-07-10 — violated ROW sites now refine inside one canonical search.**
  ADR-0081 reserves each store site's three local equality atoms before search;
  newly created variables stay dormant until final-check inserts the two valid
  permanent ROW clauses. `CdclT` resumes with learned clauses, phase state, and
  activities retained, backtracking if the old candidate violates the new
  clause. Hit/miss controls move from two outer rounds to one, two nested ROW
  obligations close in one outer round, a replayable equality branch changes
  safely, a UF-bearing index reuses the aligned e-graph atom, and the shared
  512-interface cap stays exact. The new 384-comparison eager/front-door/Z3
  matrix brings the array total to 1,920 clean comparisons; all 807 solver tests
  and the nine-test differential binary pass. Commit `07be0883` passed the
  exact-SHA pre-push gate. Next: pair-generating dynamic UF/select/extensionality
  atoms, array-valued ITE/default/UF events, non-symbol/warm models, proof
  logging, and a low-load remeasure.
- **2026-07-10 — structural store parents join explanation-guarded select
  scheduling.** ADR-0080 retains each read's original `store` term, observes it
  on `EufTheory`, and reuses the final-class candidate scan; distinct congruent
  parents carry their merge explanation while same-parent pairs are
  unconditional. Lazy ROW remains a separate candidate obligation. Same-parent,
  congruent-parent, alternate-branch, unrelated-parent, UF-index, and 80-parent
  scaling gates pass. The new 384-comparison eager/front-door/Z3 matrix brings
  the array total to 1,536 clean comparisons; all 802 solver tests pass. A fresh
  host sample still showed four blocked tasks and 13-25% I/O wait, so no new
  1-second aggregate replaces ADR-0078's QF_ABV 187/193 and QF_AUFBV 49/53.
  ADR-0081 subsequently moves bounded local ROW insertion inside one search.
  Remaining: array-valued ITE/default/UF and pair-generating merge events,
  non-symbol/warm models, proof logging, and a low-load remeasure.
- **2026-07-10 — canonical arrays admit every finite Bool/BitVec component
  combination.** ADR-0079 separates canonical finite-scalar admission from the
  broader fallback-routing flag: Bool→Bool, Bool→BV, BV→Bool, and BV→BV arrays
  share the exact scalar theory and replay-gated generic projection, while
  Int/Real/uninterpreted/datatype/FP components still decline. Public
  `issue5925` moves unknown→UNSAT in about 20 ms and `issue4240` moves
  unknown→replayed-SAT in about 5 ms. The new 384-comparison analytic/front-door/
  Z3 matrix brings the array total to 1,152 clean comparisons; all 797 solver
  tests and 12 route tests pass. The exact 1 s aggregate rerun was load-
  contaminated (four unrelated prior boundary decisions timed out), so the last
  comparable aggregate remains ADR-0078's QF_ABV 187/193 and QF_AUFBV 49/53.
  ADR-0080 subsequently adds store-parent select scheduling and ADR-0081 adds
  same-search local ROW. Remaining: low-load remeasure, then array-valued
  ITE/default/UF and pair-generating merge events, non-symbol/warm models, and
  proof logging.
- **2026-07-10 — base parent-select scheduling follows live e-classes.** Base
  read parents are now observed by `EufTheory`; a total candidate groups reads
  by final class and materializes only equal-index/unequal-result pairs. Every
  cross-parent implication is guarded by the e-graph equality explanation, so a
  rebuilt round can backtrack to another equality branch safely. Direct-symbol
  equalities no longer prepare the query-index cross product: an 80-array/read
  SAT gate now stays below the former 4,096-site boundary. Direct, transitive,
  UF-index, alternate-path/branch, and retained store/ROW gates pass. All 794 solver
  tests and 768 comparisons are clean, 456 equality-bearing. Public 1 s results
  remain QF_ABV 187/193 at 84 ms and QF_AUFBV 49/53 at 206 ms, DISAGREE=0 and
  replay failures=0. ADR-0078; ADR-0080 subsequently adds store parents and
  ADR-0081 same-search local ROW. Next: array-valued ITE/default/UF and
  pair-generating merge events, non-symbol class models, warm reuse, and
  ROW/diff-witness/equality-chain proof logging.
- **2026-07-10 — array equality is on the canonical e-graph, with class-owned
  symbol models.** Each abstract flag now retains its original array equality at
  the aligned `EufTheory` atom, so reflexivity/transitivity/congruence run on the
  existing backtrackable trail. `a=b ∧ b=c ∧ a≠c`, `a≠a`, a store/UF path, and
  the former 512-observation stress case all refute in one round with no
  extensionality instances. Candidate-true direct-symbol classes combine their
  observed entries into one deterministic majority-default model; a transitive
  SAT class with disjoint reads now replays. The strengthened 768-comparison
  matrix remains clean, 456 equality-bearing; all 790 solver tests pass. Public
  1 s results remain QF_ABV 187/193 at 84 ms and QF_AUFBV 49/53 at 205 ms,
  DISAGREE=0 and replay failures=0. ADR-0077 supersedes ADR-0076's compensating
  cross-diff queue. Next: parent-select merge scheduling, non-symbol class
  models, warm reuse, and ROW/diff-witness/equality-chain proof logging.
- **2026-07-10 — cross-array equality observations are candidate-triggered.** A
  deterministic `new`/`delayed`/`applied` queue now takes each false equality's
  diff index across one candidate-true shortest equality path, without preparing
  the quadratic cross product. `a=b ∧ b=c ∧ a≠c` closes with two observations;
  a disconnected disequality stays delayed and replays SAT; store/UF paths reuse
  existing abstraction and ROW; and the shared cap declines at exactly 512.
  The expanded 20-shape matrix keeps all 768 comparisons clean, 456 now
  equality-bearing. Public 1 s results remain QF_ABV 187/193 at 84 ms and
  QF_AUFBV 49/53 at 206 ms, DISAGREE=0 and replay failures=0. ADR-0076 is the
  historical precursor; ADR-0077 supersedes its queue with direct e-graph
  equality and class-owned symbol models.
- **2026-07-09 — direct array select congruence is externally checked.** The
  zero-trust ABV evidence route now prefers a literal-SMT-LIB `select` artifact
  for `a=b ∧ select(a,i)≠select(b,i)`. It uses `eq_reflexive`, `eq_congruent`,
  optional `symm`, and resolution, so no array axiom or elimination premise is
  trusted. Forward/reversed proofs pass the in-tree checker and installed
  Carcara; removing the array-equality antecedent is rejected. Evidence carries
  no trust steps, and the 67-family representative real-Lean gate checks the
  reversed artifact. ADR-0075. Remaining proof depth: ROW instances,
  disequality/diff-witness extensionality, equality chains, and canonical online
  proof logging.
- **2026-07-09 — projected arrays use deterministic majority-default models.**
  The shared canonical/fallback projection normalizes duplicate observations by
  index, votes for the most frequent value, uses a stable smallest-value tie,
  and retains only true overrides. Compact-BV, tie, and generic model gates pass;
  a 16-read canonical model with 12 repeated values returns in one round with
  four overrides and full replay. The 768 comparisons remain clean. Public 1 s
  decisions hold at QF_ABV 187/193 and QF_AUFBV 49/53 with zero
  disagreements/replay failures; one AUFBV PAR-2 sample moves 221→206 ms, which
  is not a performance claim. ADR-0074. ADR-0076 added the historical queue;
  ADR-0077 supersedes it and shares models across true direct-symbol classes.
  Parent-select/non-symbol models, warm reuse, and proof integration remain.
- **2026-07-09 — array equality/disequality is live on canonical CDCL(T).** The
  shared `RowCtx` equality abstraction supplies one diff witness plus paired
  query/store-index reads per equality flag. Only candidate-violated
  true-congruence or false-witness implications materialize; UF-bearing
  observations stay on the combined function/array/BV bus. Five focused
  extensionality mechanisms and two pristine-fallback isolation gates pass. The
  768-comparison matrix was half equality-bearing at that checkpoint and remained
  clean; ADR-0076 expanded it to 456 equality-bearing comparisons. Public
  1 s decisions hold at QF_ABV 187/193 and QF_AUFBV 49/53, DISAGREE=0 and replay
  failures=0; PAR-2 means move 77→84 ms and 155→221 ms, so no performance gain is
  claimed. ADR-0073. ADR-0074 adds majority-default projection; ADR-0077 puts
  equality on live `EufTheory` and shares direct-symbol class models. Parent-
  select/non-symbol ownership and proofs remain.
- **2026-07-09 — lazy read-over-write is live on the canonical array bus.** The
  ABV/AUFBV route reuses the existing ROW abstraction and starts store reads as
  independent scalar results. A violating candidate materializes one exact
  guarded hit/miss axiom (three shared scalar equalities); UF applications in ROW
  metadata remain visible to the same e-graph/BV refinement. Hit and miss controls
  each need one axiom, the UF-index control converges, and a 24-write concrete-miss
  chain replays in one round with zero ROW axioms. The 768-case matrix remains
  clean. Public 1 s runs move QF_ABV 185→187/193 and QF_AUFBV 48→49/53, with zero
  disagreements/replay failures; one tight-cap AUFBV SAT row becomes Unknown, so
  this is breadth evidence rather than a broad performance claim. ADR-0072.
  ADR-0077 subsequently puts equality on live `EufTheory`; parent-select merge
  scheduling and non-symbol class models remain.
- **2026-07-09 — base-array selects are live on canonical CDCL(T).** A true
  `abstract_arrays` boundary applies exact read-over-write without constructing
  eager pair constraints. Candidate equal-index/unequal-result reads materialize
  two exact BV atoms plus select congruence in the same replay-guided rounds as
  UF pairs. Mixed QF_AUFBV composes array-first/function-second abstraction,
  projects functions before arrays, and replays originals. Gates pin two-round
  array and three-round array→UF fixpoints, a 24-read zero-interface SAT, and the
  512-equality cap. The 768-case eager/front-door/Z3 matrix is clean. Public 1 s
  runs: QF_ABV 185/193 and QF_AUFBV 48/53 decided, DISAGREE=0, replay failures=0.
  ADR-0071. ADR-0072 supersedes the eager-ROW boundary on this canonical route;
  P2.2 still owns queue-state/extensionality/model depth. The old P1.6
  `str.len` marker was already closed by ADR-0052.
- **2026-07-09 — replay-guided dynamic UFBV interfaces are live and measured.**
  Canonical `CdclT` starts from the function-free relaxation and materializes
  only candidate pairs whose rewritten arguments are equal and fresh results
  differ. Partial-round UNSAT transfers; SAT still projects and replays. Bounds:
  64 rounds / 512 raw materialized interfaces / one shared deadline. Gates pin
  a two-round one-pair refutation, a three-round nested two-pair fixpoint, a
  replaying 24-symbolic-key table with zero pairs, and a forced control that
  stops at 256 pairs with `ResourceLimit`. `bug520` uses one round / zero pairs.
  Ten release samples: median 8.88→2.84 ms (~3.12x), six-row mean
  2.89→0.647 ms (~4.47x); Z3 row median 12.5 ms, so this narrow row is ~4.4x
  faster. Public 6/6, 1,536 differentials, replay, and 763 solver tests are
  clean. ADR-0070. Arrays followed in ADR-0071/0072; no broad parity claim.
- **2026-07-09 — exact ground-distinct UFBV interface pruning is live and
  measured.** Same-function application pairs are omitted only when cached
  empty-assignment evaluation proves one corresponding Bool/BV argument value
  differs; equal-valued, symbolic, and failed-evaluation pairs remain. The
  retained set owns the 512-interface cap. `bug520` drops 50→20 interface atoms
  and 93/31/46→69/14/16 probes/BV hits/combined propagations. A 24-concrete-key
  table now solves with zero generated interfaces; its 24-symbolic-key control
  still returns `ResourceLimit`. Exact release medians: `bug520` 15.32→8.88 ms
  (~1.72x), six-row PAR-2 mean 3.84→2.89 ms (~1.33x); enabled range
  8.35-19.19 ms, Z3 8-10 ms. Public 6/6, 1,536 differentials, replay, and 760
  solver library tests are clean. ADR-0069. Next: dynamic/model-based symbolic
  interface creation, then arrays on the bus; no general parity claim.
- **2026-07-09 — bounded exact BV-to-EUF interface propagation is live and
  measured.** One round-robin generated interface equality per theory-state
  change is proved by refuting its opposite polarity in the same warm CNF;
  failed frame selectors become the reason. Pending consequences survive
  stronger assignments and clear on pop. Caps: at most 64 interface atoms and
  128 probes. `bug520` has 50 deduplicated candidates; diagnostics recorded 93
  probes, 31 BV hits, and 46 total combined propagations. Exact five-run A/B:
  enabled 149.96-152.79 ms / corpus mean 0.034-0.036 s, disabled
  347.10-352.39 ms / 0.065-0.066 s. Public QF_UFBV remains 6/6 with zero
  disagreements/replay failures and the 1,536-case matrix is clean. Z3 remains
  about 9-11 ms, so this is a bounded ~2.3x win, not parity. ADR-0068; next:
  relevance-driven interface generation before cap expansion.
- **2026-07-09 — online UFBV BV conflicts now use same-solve decision-frame
  cores.** `IncrementalBvSolver` separates one-shot assumption cores from failed
  active-frame assertions, and `BvTheory` maps the latter back to tracked
  atom/polarity pairs with deterministic full-core fallback. A mechanism gate
  drops an irrelevant earlier frame; push/pop alignment is pinned. The
  one-selector-per-literal prototype was rejected after regressing the public
  six-row run from 0.061 s / `bug520` 0.332 s to 0.072 s / 0.382 s.
  Decision-frame cores are neutral at 0.063 s / 0.332 s. Gates: 7 direct UFBV,
  7 incremental, 77 symbolic-execution, three 512-case UFBV differentials,
  front-door routing, and public QF_UFBV 6/6 with zero disagreements/replay
  failures. ADR-0067 records the measured granularity; next is BV propagation
  and relevant interface generation, not unmeasured literal selectors.
- **2026-07-09 — bounded scalar QF_UFBV now combines EUF and exact BV through
  canonical `CdclT`.** `check_qf_ufbv_online_cdclt` starts from the
  abstraction-only function rewrite, registers explicit argument/result
  interface equalities, and drives `EufTheory` plus a warm
  `IncrementalBvSolver` on one trail. BV conflicts learn failed-frame cores;
  e-graph congruence propagates result equality; `sat` projects a
  `FuncValue` model and replays every original assertion. The front door records
  `ufbv-online-cdclt`; unsupported shape falls through, while timeout/resource
  outcomes stay terminal and eager proof production remains unchanged. Gates:
  five direct tests, three clean 512-case
  eager/front-door/Z3 matrices, all legacy UF/e-graph regressions, and public
  QF_UFBV 6/6 agreement (3 sat, 3 unsat, zero replay failures). No speedup is
  claimed: mean PAR-2 is 0.061 s and `bug520` is about 0.332 s online versus
  about 0.009 s in Z3. Next: BV propagation, relevant interface generation, and
  arrays on the live bus. ADR-0066 records the boundary.
- **2026-07-09 — P1.6 prerequisite: lazy UF routes no longer build and discard
  eager Ackermann constraints.** `abstract_functions` returns only the rewritten
  relaxation plus deterministic application/model-projection metadata, so lazy
  UFBV and UF+arithmetic construction is DAG-linear rather than secretly
  materializing O(k²) pair lemmas. Eager elimination and proof routes are
  unchanged. Gates: rewrite function tests 6/6, lazy EUF unit gates 22/22, UFBV
  scenario/integration 6/6, UFLIA 31/31, UFLRA 21/21, online/eager dispatch
  differential 2/2, and clippy clean. Next: canonical `CdclT` EUF+BV with warm BV
  conflicts and explicit argument/result interface equalities.
- **2026-07-09 — canonical `CdclT` now has deterministic LBD-based learned-clause
  reduction.** Aligned metadata records LBD, monotone recency, stable tombstones,
  and active reason-clause ids. Above a 2,000-clause budget growing by 300 per
  reduction, the worst half of eligible clauses are tombstoned by a total
  LBD/recency/slot order; originals, LBD<=2 glue, and every active reason remain.
  A forced PHP(7,6) reduction matches a never-delete UNSAT baseline, deletes no
  active reason, and repeats deterministically; all eight mechanism/adversarial
  gates pass. QF_UF/QF_S/UFLIA/UFLRA Z3 differentials stay DISAGREE=0; UFLIA is
  neutral at 425.18 s -> 425.90 s, and curated 5 s results remain bounded 6/6,
  overbound 0/2 timeout, replay failures=0. The planned VSIDS/phase/Luby/LBD
  migration is complete; no performance win is claimed. Next: P1.6 BV theory
  combination. The arithmetic-local driver remains for standalone fallback and
  diagnostics.
- **2026-07-09 — canonical `CdclT` now has deterministic Luby restarts.** The
  driver counts analyzed Boolean/theory conflicts, backjumps to root on the
  reluctant-doubling schedule, balances theory push/pop, and retains learned
  clauses, VSIDS activity, and saved phases. A forced-restart pigeonhole gate
  matches the never-restart verdict and repeats the identical trajectory; the
  20,000-run adversarial sweep remains green. Full QF_UF/QF_S/UFLIA/UFLRA Z3
  differentials stay DISAGREE=0; UFLIA is neutral at 426.19 s → 425.18 s and
  curated 5 s results stay bounded 6/6, overbound 0/2 timeout, replay failures=0.
  The LBD reduction follow-through is recorded above; no restart performance
  win is claimed from the current corpus.
- **2026-07-09 — canonical `CdclT` now has deterministic VSIDS and phase
  saving.** 1-UIP bumps conflict-side variables, decisions select maximum
  activity with lowest-index ties, every assignment saves its polarity, and
  backtracked variables reuse that phase. Direct mechanism tests and the
  20,000-run adversarial non-monotone-theory sweep pass. Focused EUF, strings,
  pure LIA/LRA, UFLIA, and UFLRA routes remain green; Z3 differentials cover
  3,000+ QF_UF, 1,500 QF_S, 2,500 UFLIA, and 1,500 UFLRA cases with
  DISAGREE=0. The long UFLIA sweep is neutral at 426.17 s → 426.19 s; curated
  5 s UFLIA remains bounded 6/6 and overbound 0/2 timeout with no replay
  failures. The follow-through Luby slice is recorded above; this mechanism
  alone claimed no performance win.
- **2026-07-09 — P1.5/P1.6 combined linear arithmetic now uses canonical
  `CdclT`.** Boolean-structured QF_UFLIA/QF_UFLRA drive
  `CombinedIncrementalLia` / `CombinedIncremental` through the same generic
  online loop as QF_UF, QF_S, and the pure arithmetic first probes. Interface
  variables/clauses, leaf reconstruction, and replay gates are unchanged; the
  propagation metrics now pin the production route rather than the enumerative
  fallback. Gates: UFLIA 31/31, UFLRA 21/21, combined learned-lemma checks 4/4,
  Z3 differential 2,500 UFLIA + 1,500 UFLRA with DISAGREE=0, and online-first
  dispatch differential clean. Curated 5 s UFLIA stays bounded 6/6 and
  overbound 0/2 timeout, with DISAGREE=0 and replay failures=0. Next engine work:
  the planned VSIDS/phase/Luby/LBD search machinery is now in canonical `CdclT`;
  advance BV combination while retaining the local driver for fallback/diagnostics.
- **2026-07-09 — P1.5 pure arithmetic default dispatch now leads with generic
  `CdclT`.** `check_with_arith_dpll` gives QF_LIA a bounded generic first probe;
  `check_with_lra_dpll_within` gives QF_LRA the full remaining deadline and
  falls back only on non-budget incompleteness. LRA deadlines now cover atom
  normalization, incremental Fourier–Motzkin feasibility/propagation/model
  work, combined UFLRA construction, and per-derived-row polling. A deterministic
  1,024-atom cap returns `ResourceLimit` before stack-risky construction. The NRA
  front door no longer sends linear-real formulas through CAD first, including
  SMT-LIB coefficients represented as `IntToReal(IntConst(_))`. Curated 5 s raw
  and preprocessed A/B preserves LIA 10/11 and LRA 9/11 decided, DISAGREE=0 and
  replay failures=0; LRA's two unknown rows improve 5.250 s / 11.853 s to
  4.838 s / 5.031 s. ADR-0060 records the routing/resource policy.
- **2026-07-09 — P1.5 QF_UF online default-dispatch ratified through generic
  `CdclT`.** `solve_qf_uf_online` / `prove_unsat_qf_uf_online` are compatibility
  wrappers over the replay-checked `check_qf_uf_online_cdclt` route, the old
  embedded EUF DPLL is test-only diagnostics, and `check_auto`'s existing
  `euf-online` route now calls `check_qf_uf_online_cdclt` with the caller's
  `SolverConfig`. ADR-0055's QF_UF criterion (2) is now fired: online pure-EUF
  solving is default-on at the front door, with offline EUF retained as fallback
  after online `unknown`. Gates: `cargo fmt --all --check`, `cargo test -p
  axeyum-solver --test route_trace`, `cargo test -p axeyum-solver --test
  cdclt_online`, `cargo test -p axeyum-solver --lib euf_egraph::tests`, `cargo
  test -p axeyum-solver --test qf_uf_differential_fuzz`, `cargo check -p
  axeyum-solver --tests`, `cargo clippy -p axeyum-solver --all-targets
  --all-features -- -D warnings`, and `cargo run -p axeyum-bench --
  corpus/regression/qf_uf --timeout-ms 5000 --backend solver --logic QF_UF
  --corpus-source regression-qf_uf-cdclt-front-door --jobs 1` (3/3,
  DISAGREE=0, model_replay_failures=0).
- **2026-07-09 — P1.5 keystone DFS slice: `StringTheory` now propagates
  variable-equality consequences through generic `CdclT`.** The online QF_S
  adapter no longer leaves theory propagation completely dark: asserted
  variable-variable `Seq` equalities now propagate equality closure, and asserted
  disequalities transport across those classes, with reasons made only of
  currently asserted trail literals. The deliberately narrow scope avoids
  propagating compound word-core facts that do not map cleanly to whole tracked
  atoms. Gates: `cargo fmt --all --check`,
  `cargo test -p axeyum-solver --lib string_theory::tests`, the existing
  `string_theory_online` / membership / front-door string integration bundle,
  `cargo test -p axeyum-solver --test qf_s_online_differential_fuzz`, and
  `cargo check -p axeyum-solver --tests`.
- **2026-07-09 — P1.5 keystone DFS slice: generic `CdclT` now consumes LIA/LRA
  theory propagation.** The `check_qf_lia_online_cdclt` and
  `check_qf_lra_online_cdclt` adapters now forward the already-validated
  `LiaTheory::propagate` / `LraTheory::propagate` entailments instead of
  suppressing them. `CdclT` gained internal propagation-count telemetry so the
  new tests prove the path actually fires. Gates: `cargo fmt --all --check`,
  `cargo test -p axeyum-solver --lib lia_theory::tests`,
  `cargo test -p axeyum-solver --lib lra_theory::tests`, the existing
  `cdclt_lia_online`/`cdclt_lra_online` integration suites, and
  `cargo check -p axeyum-solver --tests`.
- **2026-07-09 — SEQUENCING PIVOT: the theory-leaf breadth-first pass hit its ROI
  wall; next move is depth-first on the engine keystone (P1.4/P1.5).** A
  BFS-vs-DFS traversal analysis over the
  [dependency DAG](docs/plan/01-dependency-dag.md) is written up in
  [build-sequencing-bfs-dfs.md](docs/research/08-planning/build-sequencing-bfs-dfs.md)
  and the ranked conclusion is folded into
  [PLAN.md § The two engineering keystones](PLAN.md#the-two-engineering-keystones).
  **Empirical trigger (this session):** the arithmetic/string decide-rate BFS
  landed **+6 rows, all fuzz-verified DISAGREE=0** — the integer-algebraic
  identity refutation (`nl-eq-infer`, ADR-0064), the bounded-nonlinear-SAT
  dispatch fix (4× `nia-pythagorean`), and the finite-domain disjunction split
  (`rewriting-sums`, ADR-0065) — and then **ran out of tractable leaves**: a full
  sweep of QF_LIA/LRA/UFLIA/ALIA/AUFLIA (DISAGREE=0 everywhere) showed every
  remaining unknown is either engine-blocked (eager encodings no longer scale),
  large-scale (dense-ILP MILP, 200–360 KB LPs — four bounded LIA experiments
  built/measured/reverted per measure-don't-seed), or a research-grade
  completeness proof (Nielsen strings, #82). **Ranked next (quality × efficiency):**
  (1) DFS `P1.4 e-graph → P1.5 CDCL(T)` — the highest-leverage unblock;
  (2) thin measured-leaf skirt in parallel (NRA tail, strings-Nielsen); defer
  feature/scale leaves (#85/#89/#90/#91) into a funded engine phase;
  (3) trust-ledger proof spine (`P3.5 → ledger→0`) in parallel;
  (4) after P1.5, the categorical gap `P3.8 → P4.6 CHC/Horn`. Disk also cleaned
  (~265 GB reclaimed from stale `target/`); tree green.
- **2026-07-08 — Joy of Cryptography / provable-security planning scout
  recorded.** Added
  [provable-security-integration.md](docs/plan/provable-security-integration.md)
  and linked it from the plan + foundational-books index. Verdict: this is a
  Track 5 / proof-cookbook / scenario-corpus demand-pull lane, not a reason to
  reorder the active parity queue. Near-term shape: finite game examples
  (OTP reuse/xor cancellation), game-hop evidence anatomy, constant-time and
  transcript-verification micro-suites, and finite-field demand packets when
  P2.10.4 becomes eligible.
- **2026-07-07 — top-down Z3/cvc5 gap re-audit COMMITTED
  ([gap-analysis-z3-cvc5-2026-07-07.md](docs/plan/gap-analysis-z3-cvc5-2026-07-07.md));
  PLAN.md's leverage order superseded.** The audit (grounded in the scoreboard
  + direct code inspection, independently re-verified) corrected three stale
  premises — online NO CDCL(T) is already the *first* UF+arith route (not
  eager Ackermann); SAT inprocessing (subsumption/BVE/vivify) is *built,
  default-off* (so the perf lever is a flag-flip + measurement); and the
  quantifier hole is precisely the **sat direction** (e-matching/MBQI
  refutation exist, no model-finding → quantified LIA/UF at 0%). **The
  standing queue toward 100% Pareto dominance (PLAN.md § leverage order
  2026-07-07):** (1) measure the built inprocessing+reduction levers on p4dfa
  w/ unknown-cause split; (2) MBQI model-finding T2.6.5; (3) CdclT
  default-dispatch ADR + arrays onto the spine; (4) strings unsupported
  fragment (QF_SLIA first); (5) dominance audits for the 12 unaudited rows +
  ledger→0 (Fpa2Bv); (6) NIA residue then the ADR-0058 NRA arc. New theory
  columns stay deferred (P2.10, counted not built).
- **2026-07-07 — the NIA arc pays off: qf-nia-cvc5 21→33 (+12 sound rows), 9th
  review's pivot executing.** Live totals in the generated
  [SCOREBOARD](bench-results/SCOREBOARD.md) (never hand-copy): **QF_S 78/134,
  QF_NRA cvc5 32/38 (84%), QF_NIA cvc5 33/39 (85%) + iand 3/3 + synthetic 32/32, DISAGREE=0.**
  Strings frontier is theory-coupled-closed (remaining = unsupported
  to_int/replace_re/seq, new machinery). The 9th review's "NIA is NOT
  bounded-exhausted" call was RIGHT: the two landed NIA slices (#40 congruent
  div-0, #41 int.pow2) beat the entire prior ~57-commit arithmetic arc, and
  closed two soundness bugs along the way (the div-0 P0 + a pre-existing wrong-sat
  the new const-0 fuzz caught). See Changelog for detail.
- **Pivot (9th review, correcting the 8th) — the active queue:**
  (1) ✅ **#40** congruent-div-0 recovery — SOUNDLY recovered div.01/minimal_unsat_core/div.08
  (`b91dd918`+`73dceb72`, qf-nia 21→25, DISAGREE=0);
  (2) ✅ **#41** NIA `int.pow2` — first-class `Op::IntPow2` + value-table axioms,
  cvc5 semantics verified from source (neg-exp = 0, DEFINED not underspecified)
  (`fb2da08b`, qf-nia 25→33, DISAGREE=0);
  (3) ✅ **#42** underspecified-operator fuzz-COVERAGE audit — the Hard Rule is now an
  ENFORCED per-op checklist (`docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`),
  4 degenerate seed-classes added (`7ce23583`); it SURFACED a live P0 → ✅ **#46**
  `str.from_code` wrong-sat fixed (`6877c365`, decline the unrepresentable code-point
  window instead of folding to `""`). Tracked GAPs remain (RealDiv-0, BV const-0
  seed, seq/FP fuzzes);
  (4) ✅ **#43** last cheap NRA pickups (`4d74b288`, slices 4+7a+7b: parser Int→Real,
  algebraic-√2 sat, equality-anchored disjunctive unsat + the DPLL→CAD edge; qf-nra
  27→32/38 84%, DISAGREE=0);
  (5) **#45/ADR-0058** — the bounded arithmetic levers are now HARVESTED; a **10th
  review is re-ranking** the next major thrust (funded NRA CAD/nlsat engine arc for
  the 6/12 genuine-engine residue vs **#44** regex-emptiness→Lean vs strings breadth
  vs Track-1 word-level-reduction perf vs closing the #42 fuzz GAPs). NB #43 already
  landed the DPLL→CAD edge ADR-0058 Phase B was scoped around — ADR-0058 needs a
  scope/status refresh.
  The 9th review corrected two 8th-review premises: Lean breadth is FAR more
  complete than assumed (8+ fragments incl. integer equality-systems; only the
  regex-emptiness cert **#44** is a cheap Lean pickup left), and the lazy-CEGAR
  QF_BV perf lever is a DEAD END (never fires on public p4dfa — the real Track-1
  lever is word-level reduction depth). CdclT LIA/LRA adapters stay DARK (#35,
  shelved). Session history: [docs/status-archive/](docs/status-archive/) — FOCUS not log.

## Already shipped this session (pre-plan)

The reachability / symbolic-execution / certificate surface that motivated this
plan is built and committed on the current branch:

- BMC driver, k-induction (unbounded safety), symbolic-memory BMC,
  symbolic-memory k-induction,
  `SymbolicExecutor` (path exploration + test-suite enumeration + path-condition
  optimization), and self-rechecking certificates (`UnsatProof::recheck`,
  `SafetyCertificate::recheck`, `EndToEndUnsatOutcome::recheck`).
- These map onto Track 4 (use cases) and Track 3 (the recheck family); the plan
  records what remains around them.

## Phase status

### Track 1 — Engine & Performance
| Phase | Title | Status |
|---|---|---|
| P1.6w | Retained warm nested array-valued UF parameters | **DONE (ADR-0094)** — supported array-valued `Apply` terms can key retained array-valued UF parents directly or under supported structural keys. Direct nested keys encode by the inner application's private projection symbol; structural nested keys encode by replay-safe rewritten structural terms, with private projection/owner symbols excluded from public array-key synthesis. The focused warm array-UF parent suite covers direct nested-key SAT replay, asserted nested-key equality UNSAT, and structural keys with nested application bases. Nested/extended arrays, proofs, and low-load aggregate timing remain |
| P1.6v | Retained warm structural array-valued UF parameters | **DONE (ADR-0093)** — supported store/constant/array-ITE expressions can key retained array-valued UF parents. The warm path retains scalar dependencies inside structural keys, realizes private key owners against the original structural terms before full-value function projection, uses active equality classes or ADR-0091 relation flags for key congruence, filters private owners/flags/witnesses, and replays originals. The focused warm array-UF parent suite covers scalar UF dependencies inside keys, independent structural-key SAT via relation flags, asserted structural-key equality UNSAT, and the former nested array-valued application-key deferral. ADR-0094 subsequently lands supported nested application keys; proofs and low-load aggregate timing remain |
| P1.6u | Retained warm direct array-valued UF parameters | **DONE (ADR-0092)** — direct finite-array symbols can key retained array-valued UF parents. Array-key congruence uses active retained equality classes or private ADR-0091 relation flags; projection separates non-equal key classes with deterministic full array values before `FuncValue` construction, preserves user-visible select constraints, filters private guarded reads, and replays originals. The focused warm array-UF parent suite covers independent-key SAT, asserted-equality UNSAT, private relation-flag use, and the former structural array-key deferral. ADR-0093 subsequently lands supported structural array-valued parameter expressions, and ADR-0094 lands nested application keys; proofs and low-load aggregate timing remain |
| P1.6t | Retained warm Boolean array relation flags | **DONE (ADR-0091)** — supported array equality atoms nested under scalar Boolean structure become private candidate-sensitive flags; true flags add guarded paired-read equality observations and are the only flagged equalities merged/realized during projection, while false flags add one guarded private diff witness. New/existing compatible read indices are observed under guards, private flags/witnesses/owners are filtered, and original replay gates SAT. Five focused relation-flag tests plus the ADR-0088/0089/0090 suites pass. ADR-0092 subsequently lands direct array-valued UF parameters, ADR-0093 lands supported structural keys, and ADR-0094 lands nested application keys; proofs and low-load aggregate timing remain |
| P1.6s | Retained warm structural array equality | **DONE (ADR-0090)** — supported store/constant/array-ITE parents get cached private constructor owners; positive structural equalities add bounded old/future shared-index observations plus a private probe, realize owner equations to a class-aware fixed point before array-valued function projection, filter private owners, and replay originals. Default gates cover no-read SAT, constants/store conflicts, selected/unselected ITE branches, array-result UF composition, push/pop and one-shot cores, Bool elements, BV256 components, exact limits, timeout, and a 64-seed warm/check-auto matrix. ADR-0091 subsequently adds nested Boolean relation flags, ADR-0092 adds direct array-valued UF parameters, ADR-0093 adds supported structural keys, and ADR-0094 adds nested application keys; proofs and low-load aggregate timing remain |
| P1.6r | Retained warm array relations | **DONE, literal relation slice (ADR-0089)** — positive equality merges direct/application projection owners before function construction; one private BV diff index reduces top-level disequality over symbol/store/constant/ITE/application parents to exact retained reads. Scope/core/filter/replay, Bool/BV256, exact depth, eight default/nine all-feature tests, 192 warm/check-auto/Z3 comparisons, 816 solver units, 77 symexec tests, and complete EVM gates pass. ADR-0090 subsequently adds positive structural equality, ADR-0091 adds nested Boolean relation flags, ADR-0092 adds direct array-valued UF parameters, ADR-0093 adds supported structural keys, and ADR-0094 adds nested application keys; proofs remain |
| P1.6q | Retained warm array-valued UF parents | **DONE, scalar-keyed slice (ADR-0088)** — finite Bool/BV application arguments and read indices reuse warm abstraction; private application arrays enforce conditional argument/index read congruence; concrete-equal tuples merge split observations before full-value function projection, private-owner filtering, and replay. Exact 64/65 admission, ten focused tests, 192 warm/check-auto/Z3 comparisons, 816 solver units, 77 symexec tests, and complete EVM gates pass. ADR-0090 subsequently adds warm structural equality, ADR-0092 adds direct array-valued UF parameters, ADR-0093 adds supported structural keys, and ADR-0094 adds nested application keys; proofs remain |
| P1.6p | Bounded structural array-class equations | **DONE (ADR-0085)** — exact pre-search array-ITE equality decomposition puts selected branch equality on the e-graph; bounded observed-read-preserving realization solves true store/ITE/constant equations before function projection and replay. Leaf/depth/fixed-point/deadline caps, SMT-LIB, mixed-component, 192 analytic/front-door/Z3 comparisons, 816 solver tests, and the exact-SHA gate pass. Warm reuse, nested/extended arrays, and proofs remain |
| P1.6o | Array-valued UF results on the canonical array bus | **DONE (ADR-0084)** — IR/SMT-LIB and abstraction admit finite Bool/BitVec array results; application reads retain semantic e-graph parents and fresh-array projection owners. Final classes union observations before array-first/function-second projection and original replay. Stores/ITE/equality/nested-UF controls, 288 analytic/front-door/Z3 comparisons, 815 solver tests, and the exact-SHA gate pass. ADR-0085 subsequently closes bounded structural store/ITE/constant class ownership; warm reuse and proofs remain |
| P1.6n | Bounded dynamic interface atoms | **DONE (ADR-0082)** — `CdclT` explicitly maps appended SAT variables to aligned theory atoms; `EufTheory` grows equality metadata over pre-observed sides; exact BV grows in its owned arena. Candidate-violated UF, explanation-guarded parent-select, and bounded extensionality interfaces now refine inside one retained search. One-round mechanism/backtracking/cap/scale gates, 809 solver tests, and 2,304 eager/front-door/Z3 comparisons are clean. ADR-0084/0085 subsequently add application-parent projection and bounded structural ITE equality/realization; richer new-term events, warm models, and proofs remain |
| P1.6m | Dynamic in-search ROW insertion | **DONE, bounded local-atom slice (ADR-0081)** — each store site reserves three atoms dormant; a violated candidate activates them through two permanent valid ROW clauses and resumes the same `CdclT` with learned/phase/activity state retained. Hit/miss, nested-site, replayed-branch, UF-index, inactive-propagation, and exact-cap gates pass; 807 solver tests + 1,920 comparisons are clean. ADR-0082 subsequently generalizes retained-search growth to pair-generated scalar atoms |
| P1.6l | Explanation-guarded store-parent select scheduling | **DONE, original outer-round slice (ADR-0080)** — original store terms join final e-class grouping; only candidate-violated equal-index/unequal-result pairs materialize, distinct-parent lemmas retain merge guards, and lazy ROW stays independent. Same/congruent/alternate/unrelated/UF-index/80-parent gates pass. ADR-0081/0082 move local ROW and pair-generated select interfaces into one search; ADR-0084/0085 add application parents and bounded structural ITE equality/realization. Richer events, warm models, and proofs remain |
| P1.6k | Finite Bool/BitVec array admission | **DONE (ADR-0079)** — canonical ABV/AUFBV accepts Bool or BitVec independently for index and element sorts while broader fallback routing stays intact. Four component-shape replay gates, the exact `issue5925` route, a Bool-only UF+array route, and an Int negative control pass. `issue5925`/`issue4240` move unknown→unsat/sat; 797 solver tests + 1,152 comparisons are clean. Low-load aggregate remeasure remains because current 1 s artifacts were I/O-contaminated |
| P1.6j | Explanation-guarded parent-select scheduling | **DONE, original base-symbol outer-round slice (ADR-0078)** — base reads group by final live e-class; only candidate-violated equal-index/unequal-result pairs materialize, and cross-parent lemmas carry the merge explanation as a branch-safe guard. Direct-symbol equality drops query-index preconstruction; direct/transitive/UF/alternate-path/backtracking/80-array gates pass. ADR-0080 adds store parents and ADR-0082 moves pair-generated scalar select interfaces into one retained search; new-term ITE/default/UF events, non-symbol/warm models, and proofs remain |
| P1.6i | Array equality on the canonical e-graph + symbol-class models | **DONE, direct-symbol model slice (ADR-0077)** — each flag retains its original array equality for backtrackable EUF; transitive/self/store-UF conflicts and the former 512-observation stress case refute in one round without extensionality work. True direct-symbol classes share one deterministic model; disjoint-read transitive SAT and a Boolean backtrack choice replay. 790 solver tests + 768 comparisons pass, 456 equality-bearing; public coverage is unchanged. ADR-0078/0080 subsequently add base/store-parent scheduling; non-symbol models, warm reuse, and proofs remain |
| P1.6h | Candidate-triggered cross-array equality queue | **SUPERSEDED (ADR-0076 → ADR-0077)** — the outer-round queue established the missing transitive-equality case, but diff-index path observations duplicated the e-graph's equality job. ADR-0077 removes that implementation and retains the evidence as the root-cause precursor |
| P1.6g | Candidate-guided array extensionality | **DONE (ADR-0073)** — shared equality flags receive one diff witness and paired reads at existing query/store indices; only violated congruence/witness instances materialize. UF-bearing observations share canonical refinement, cloned probes preserve pristine fallbacks, and replay gates SAT. Five mechanism + two isolation gates pass; public coverage holds at QF_ABV 187/193 and QF_AUFBV 49/53. ADR-0074/75/77/78/80 add majority models, checked direct congruence, live equality/classes, and base/store-parent scheduling; ITE/default/UF events, non-symbol models, ROW/diff-witness/online proofs, and opaque-heavy arithmetic lifting remain |
| P1.6f | Candidate-guided lazy ROW on the canonical array bus | **DONE (ADR-0072)** — shared ROW abstraction records store sites; only candidate-violated hit/miss semantics materialize guarded axioms. UF-bearing metadata shares the dynamic function path, and function-then-array replay gates SAT. The 768 differential comparisons remain clean; public QF_ABV is 187/193 and QF_AUFBV 49/53 at 1 s, DISAGREE=0. ADR-0073/74 subsequently add bounded extensionality and majority models; merge-triggered queue/class work remains |
| P1.6e | Replay-guided array interfaces | **DONE (ADR-0071)** — `abstract_arrays` avoids eager pair construction; canonical rounds batch only violated select pairs and compose them with dynamic UF interfaces. Original replay gates SAT. 768 differential comparisons and public QF_ABV 185/193 + QF_AUFBV 48/53 are DISAGREE=0 with zero replay failures. ADR-0072 subsequently makes ROW lazy; ADR-0084 supersedes the original function-first projection order |
| P1.6d | Replay-guided dynamic UFBV interfaces | **DONE (ADR-0070)** — canonical rounds start with no generated pairs and batch only candidate-model congruence violations; relaxation UNSAT transfers and SAT remains projection/replay-gated. `bug520` materializes 0 pairs and improves release median 8.88→2.84 ms; a 24-symbolic-key table moves cap-decline→replayed SAT. Arrays followed in ADR-0071/0072; the old `str.len` marker was already closed by ADR-0052 |
| P1.6c | Exact ground-distinct interface pruning | **DONE (ADR-0069)** — cached empty-assignment evaluation omits only application pairs with a proved unequal argument value; dynamic/equal-valued pairs remain. `bug520` 50→20 interface atoms and release median 15.32→8.88 ms; a 24-concrete-key table bypasses the prior quadratic cap while the symbolic control still declines. Arrays followed in ADR-0071/72/73 |
| P1.6b | Exact BV interface propagation | **DONE (ADR-0068)** — generated argument/result equalities are probed one per state by exact opposite-polarity warm-CNF refutation; failed frames explain propagation; 64-interface/128-probe caps. Same-tree 5-run A/B improves `bug520` 347.10-352.39→149.96-152.79 ms and corpus mean 0.065-0.066→0.034-0.036 s, with 6/6 public agreement and 1,536 clean differential comparisons. Arrays followed in ADR-0071/72/73 |
| P1.6a | Warm BV conflict-core precision | **DONE (ADR-0067)** — online UFBV maps same-solve failed decision-frame selectors back to theory literals with deterministic full-core fallback. A per-literal selector prototype was reverted after a measured 0.061→0.072 s mean and 0.332→0.382 s `bug520` regression; accepted frame cores are neutral at 0.063 s / 0.332 s. Remaining core work is within-level precision only if it avoids repeated-assumption cost |
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. **CDCL(XOR) foundation landed** (`gf2`/`xor_extract`/`xor_propagate` in `axeyum-cnf`) — the path-2 multiplier-wall attack: a sound GF(2) Gaussian engine + exact XOR-gate extraction + an entailment-checked propagation pass; slice 4 wires it into the live preprocess pipeline (measured). Vivification / glue tiers remain. **GQ6** makes further cold inprocessing conditional on the Glaurung exact-CNF profile showing that SAT search, rather than word/AIG/CNF construction, dominates |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). **T1.2.4 elim_unconstrained landed** (`axeyum-rewrite::elim_unconstrained`): a variable occurring once under an invertible BV op (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`) makes that subterm unconstrained → replaced by a fresh var, operator dropped (Z3's `elim_unconstr`); peels nested layers, terminates. Model-sound via the trail (`x := op⁻¹(u,w…)`; orphaned operands defaulted, sound by the inverse identity); wired into `check_with_preprocessing` after solve_eqs (opt-in, default-off per ADR-0034). `bvumulo` now uses the word-width threshold encoding `a > all_ones / b` instead of a doubled-width multiplier, so BV256 overflow checks no longer build BV512 multiplication terms. **ADR-0136 adds the first Glaurung-shaped BV-slice rule:** narrow extracts distribute exactly through pointwise bitwise operations and BV `ite`, and the warm solver exposes config-driven preprocessing while retaining original-term replay. Exhaustive evaluation, Z3 differential, and an 8-of-64-bit AIG-reduction gate pass. **GQ2--GQ5** now explicitly require the cheap cold tier, coercion-cancellation identities, cold relevant-bit propagation, and profile-gated AIG/CNF sharing/encoding work. Next: run GQ1 on the external 100%-decided Glaurung capture, then rank these slices by its measured profile rather than the synthetic corpus alone |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | WIP — the proof-producing core `solve_with_drat_proof` (`proof_sat.rs`) modernized: **VSIDS activity branching** (bump conflict-side vars, MiniSat-style decay, rescale-on-overflow; highest-activity unassigned var, ties to lowest index), **phase saving**, and **Luby restarts**. Sound by construction — every emitted clause is RUP and the proof is DRAT-checked, so a heuristic bug only slows search. All 231 cnf tests pass (incl. the 400-CNF differential vs BatSat + a new pigeonhole-4→3). NB the modern CDCL(XOR) core in `xor_cdcl.rs` already has VSIDS/Luby/LBD. Remaining: arena + packed watches, chronological backtracking, and wiring a modern core into the default path only where **GQ6** exact-CNF/backend attribution demonstrates a client win |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. **Slices a+b LANDED 2026-07-03** (`a3460101`,`c9d332c1`): the generic online `CdclT<T: TheorySolver>` driver (1-UIP over the mixed implication graph, lockstep theory push/pop, deadline in the loop; EufTheory parity 2500/2500 vs offline, z3 QF_UF fuzz unchanged) + the StringTheory adapter (per-assert certified refutations, premise-index→trail-literal explanations, replay-gated sat; census disjunctive shapes decide; 1500-case fuzz DISAGREE=0; found+fixed a real 1-UIP underflow on non-current-level theory cores). Front-door QF_S wiring landed same day (`c924fcb0`). **2026-07-09/10 DFS slices:** generic LIA/LRA propagation, conservative StringTheory equality consequences, canonical QF_UF/LIA/LRA/UFLIA/UFLRA dispatch, deterministic VSIDS/phase/Luby/LBD search, bounded warm EUF+BV, aligned array-equality atoms, explanation-guarded base/store/application-parent readout, finite Bool/BV array admission, retained-search ROW, ADR-0082's explicit mapped dynamic theory-variable growth, ADR-0083's deadline-aware wide BV construction, ADR-0084's array-result projection, ADR-0085's structural ITE equality/class realization, ADR-0086's retained structural-read owners, ADR-0087's candidate-triggered transitive warm ROW summaries, ADR-0088's retained scalar-keyed array-valued UF parents, ADR-0089's projection equality/exact structural diff witnesses, ADR-0090's retained positive structural equality, and ADR-0091's nested Boolean relation flags are live. Remaining: broader corpus timing, within-level BV core precision when measurement justifies it, proof integration, and opaque-heavy arithmetic participation |
| P1.6 | Theory combination (th_eq bus, interface equalities) | WIP — EUF+LIA/LRA dispatch and canonical QF_UFBV/QF_ABV/QF_AUFBV combination are live. ADR-0066–0070 establish exact BV/EUF interfaces and replay-guided UF refinement; ADR-0071/72/73 add select congruence, lazy ROW, and bounded equality/diff observations; ADR-0074 adds majority-default models; ADR-0077 puts equality flags on the live e-graph and direct-symbol classes on one model; ADR-0078/0080 schedule explanation-guarded base/store-parent reads from final e-classes; ADR-0079 admits every Bool/BitVec component combination without changing broader fallbacks; ADR-0081/0082 insert ROW and pair-generated scalar UF/select/extensionality interfaces inside one retained search; ADR-0083 bounds wide scalar lowering with cumulative admission plus cooperative deadlines; ADR-0084 adds finite-scalar array-valued UF results and final-class-owned result projection; ADR-0085 adds exact array-ITE equality branching and bounded structural class realization; ADR-0086/0087 add retained warm structural owners and candidate-triggered transitive ROW summaries; ADR-0088 retains scalar-keyed array-valued UF parents with conditional read congruence and full-value projection; ADR-0089 adds projection-owned equality and exact top-level disequality over supported structural parents; ADR-0090 adds retained positive structural equality over supported store/constant/array-ITE parents through private owners, bounded observations, class-aware realization, filtering, and replay; ADR-0091 adds candidate-sensitive nested Boolean relation flags; ADR-0092 adds direct array-valued UF parameters with guarded key congruence and full-value key projection; ADR-0093 adds supported structural array-valued UF parameter keys with scalar dependency retention and structural owner realization; ADR-0094 adds supported nested array-valued application keys through private projection and rewritten-structural key encoding. Array-first/function-second projection and original replay gate SAT; eager routes remain fallbacks/proof producers. ADR-0052 closes the recorded bounded-string marker. Remaining: opaque-heavy arithmetic admission/model lifting, nested/extended arrays, proof integration, and a broader low-load aggregate remeasure |
| P1.7 | PBLS local-search BV engine (portfolio) | WIP — **word-level WalkSAT landed** (`solve_local_search` + `PblsBackend`, `pbls.rs`): keeps a concrete Bool/BitVec(≤128) assignment, scores by evaluator-falsified assertions, nudges a variable in an unsatisfied assertion (greedy + WalkSAT noise + random restarts) toward a model. One-sided + sound: `Sat` only with an evaluator-verified model, never `Unsat`, `Unknown` (incl. out-of-scope sorts) otherwise. Read-only on the arena (fits the trait); deterministic (fixed seed, explicit budgets). 4 unit + an ignored 150-formula differential vs the eager backend (never contradicts). Remaining: integrate as a portfolio strategy; tune moves/budgets; measure on satisfiable corpora |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO — Codex review recommends promoting this from cleanup to risk control: split `solve()` into explicit tactic contracts with fragment predicates, transformation class, replay/proof obligation, resource behavior, and benchmark-visible per-step metrics. **GQ9** is the concrete QF_BV client slice: a telemetry-visible raw/cheap/configured/warm preprocessing policy, benchmarked against fixed alternatives and documented for embedders |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | WIP — **destination-2 lever measured & scoped** (commits beee599/9846349, `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`). KEY FACT: lazy abstraction-refinement bit-blasting (`solve_lazy_bv_abstraction`, ADR-0019) is **built but NOT wired into default `solve()`/bench** — so the "~2-3/113 public QF_BV" picture is the *eager* mountain-builder. Measured (`tests/lazy_bv_curated_measure.rs`): lazy decides **incidental-heavy-op** cases with 0 multiplier blasts (`x=1∧x=2∧r=p·q` → unsat ~0ms, 0 refined), cracks `calypto_9` (sat, 2 ops refined), is a safe no-op when `ops=0` (public files), no shortcut on essential multiplier-equivalence. Next (coordinate on shared bench): lazy-bv bench backend → measure public 113 (DISAGREE=0) → opt-in `SolverConfig::lazy_bv` strategy → default-on ADR after net benefit. The highest-ROI perf move is wiring+measuring a built CEGAR bit-blaster, not a new algorithm |
| P2.2a | Deterministic majority-default array projection | **DONE, bounded structural class slice (ADR-0074/0077/0084/0085)** — votes count distinct observed indices, ties use stable smallest-value order, and only non-default overrides remain. Candidate-true direct-symbol/application classes union observations, then true store/ITE/constant equations realize total leaf arrays without changing reads; transitive, split-read, and structural SAT replay. Remaining: nested/extended arrays and warm reuse |
| P2.2b | Candidate-triggered cross-equality observations | **SUPERSEDED (ADR-0076 → ADR-0077)** — the queue exposed the missing transitive case but duplicated ordinary equality reasoning. Flags now retain their original equality on `EufTheory`; no cross-diff path is built |
| P2.2c | Canonical e-graph equality + class-owned models | **DONE, bounded structural slice (ADR-0077/0078/0084/0085)** — live backtrackable EUF handles array reflexivity/transitivity/congruence; direct symbols and fresh array-valued application owners share final-class models; exact ITE equality decomposition exposes selected branch classes; bounded store/ITE/constant equations realize derived structural values. Conflict/stress/transitive/alternate-path/backtracking/80-array, split-result, and structural gates pass. Warm reuse remains |
| P2.2d | Finite scalar component coverage | **DONE (ADR-0079)** — Bool/BitVec index and element combinations share canonical theory/model/replay; generic mixed-component models replay, Bool-only UF+array dispatches, and Int components remain outside admission. Two public unknowns become decided and 384 new comparisons are clean |
| P2.2e | Structural store-parent scheduling | **DONE, outer-round slice (ADR-0080)** — each store read retains its original parent, joins final-class candidate select scheduling, and independently remains a lazy ROW site. Distinct store terms carry explanation guards; same-parent, branch, unrelated, UF-index, and 80-parent scale gates pass. The 384-comparison structural matrix brings the clean total to 1,536; ADR-0081 subsequently moves the local ROW obligation inside one search |
| P2.2f | Dynamic local ROW final-check | **DONE, same-search slice (ADR-0081)** — bounded per-store atoms are dormant until a violated candidate adds permanent ROW clauses; learned/phase/activity state survives and ordinary conflict analysis changes branches. Hit/miss, nested, UF-index, replay, inactive-propagation, and exact-cap gates pass; the 384-comparison matrix brings the clean total to 1,920 |
| P2.2g | Dynamic scalar interface final-check | **DONE, same-search slice (ADR-0082)** — candidate-violated UF, explanation-guarded base/store-parent select, and bounded equality/extensionality interfaces append aligned atoms over pre-observed e-graph terms and resume one retained search. Former two/three-round controls pin one round; the 384-comparison matrix brings the clean total to 2,304 |
| P2.2h | Array-valued UF result projection | **DONE (ADR-0084)** — canonical ROW retains application parents and fresh-array projection owners; final e-classes union observations before array-first/function-second projection. Stores/ITE/equality/nested-UF controls and 288 analytic/front-door/Z3 comparisons pass with replay and zero disagreements |
| P2.2i | Structural array-class equations | **DONE (ADR-0085)** — exact array-ITE equality decomposition plus bounded observed-read-preserving store/ITE/constant realization closes selected-branch UNSAT and total-model SAT gaps. SMT-LIB, Bool/Int, cap/deadline, 192 analytic/front-door/Z3 comparisons, and replay gates pass |
| P2.2j | Retained warm array-valued UF parents | **DONE, scalar-keyed slice (ADR-0088)** — private application arrays and read owners enforce conditional argument/index congruence; equal concrete tuples merge split observations before full-value function projection, owner filtering, and replay. Ten focused gates, exact 64/65 admission, and 192 warm/check-auto/Z3 comparisons are clean |
| P2.2k | Retained warm array relations | **DONE, literal relation slice (ADR-0089)** — positive equality merges direct/application projection owners before function construction; top-level disequality over supported structural parents uses one exact private diff index and two retained reads. Eight default/nine all-feature gates and 192 warm/check-auto/Z3 comparisons are clean |
| P2.2l | Retained warm structural array equality | **DONE (ADR-0090)** — store/constant/array-ITE parents get private constructor owners, structural equality adds bounded shared-index/probe observations, and projection realizes owner equations to a class-aware fixed point before function construction and replay. Eight focused gates plus the 64-seed warm/check-auto matrix are clean |
| P2.2m | Retained warm Boolean array relation flags | **DONE (ADR-0091)** — nested supported array equality atoms become private flags; true flags add guarded paired-read equality observations and project as equality classes only when candidate-true, while false flags add a guarded diff witness. Five focused gates plus ADR-0088/0089/0090 suites are clean |
| P2.2p | Retained warm nested array-valued UF parameters | **DONE (ADR-0094)** — supported array-valued `Apply` keys use private projection symbols directly or inside rewritten structural keys, preserving function projection order and original replay. Direct nested-key SAT, asserted nested-key equality UNSAT, and structural nested-base SAT replay in the focused warm array-UF parent suite |
| P2.2o | Retained warm structural array-valued UF parameters | **DONE (ADR-0093)** — supported store/constant/array-ITE UF keys retain scalar dependencies and structural owners, then project function tables from replay-safe structural key values. Structural-key SAT, relation-flag separation, asserted-equality UNSAT, and the former nested array-valued application-key deferral replay in the focused warm array-UF parent suite; ADR-0094 subsequently lands supported nested application keys |
| P2.2n | Retained warm direct array-valued UF parameters | **DONE (ADR-0092)** — direct finite-array UF parameters reuse retained relation flags for key equality, then project distinct full array key values before full-value function tables. Independent-key SAT and asserted-equality UNSAT replay in the focused warm array-UF parent suite; ADR-0093 subsequently lands supported structural array keys |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | WIP — eager elimination/certifying fallback remains (ADR-0010). Canonical QF_ABV/QF_AUFBV has replay-guided base-select congruence (ADR-0071), lazy ROW (ADR-0072), bounded equality/diff observations (ADR-0073), majority-default models (ADR-0074), live e-graph equality plus direct-symbol class models (ADR-0077), explanation-guarded base/store-parent scheduling (ADR-0078/0080), Bool/BitVec finite-scalar component coverage (ADR-0079), same-search ROW plus pair-generated scalar interface insertion (ADR-0081/0082), deadline-aware scalar lowering/admission (ADR-0083), array-valued UF result projection (ADR-0084), bounded structural class equations (ADR-0085), retained incremental structural-read owners (ADR-0086), candidate-triggered transitive warm ROW summaries (ADR-0087), retained scalar-keyed array-valued UF parents (ADR-0088), retained projection equality/exact structural diff witnesses (ADR-0089), retained positive structural equality (ADR-0090), retained nested Boolean relation flags (ADR-0091), retained direct array-valued UF parameters (ADR-0092), retained supported structural array-valued UF parameters (ADR-0093), and retained nested array-valued UF parameters (ADR-0094). Array-first/function-second projection and replay gate SAT; cloned probes preserve fallbacks. All 2,784 canonical comparisons are clean, plus three 192-case warm/check-auto/Z3 matrices, the 64-seed structural-equality matrix, the focused relation-flag suite, and the focused direct/structural/nested-array-parameter gates. The focused nine-row cvc5 QF_AUFBV rerun is 7 SAT / 1 budget unknown / 1 unsupported with zero disagreements/replay failures; ADR-0078's broader low-load 1 s aggregate remains QF_ABV 187/193 and QF_AUFBV 49/53 pending comparable remeasurement. ADR-0075 checks direct select congruence externally. Remaining: nested/extended arrays and ROW/diff-witness/equality-chain/online proof integration |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | WIP — **multi-equation Diophantine infeasibility** (`prove_lia_unsat_by_diophantine`, commit 96f07a3): a conjunction of integer equalities that is rational-feasible but **integer-infeasible** is UNSAT — fraction-free Hermite-style integer Gaussian elimination reports a contradiction row (`0=c` or per-row `gcd ∤ rhs`), deciding the case B&B can't terminate on for unbounded vars and the single-equation GCD misses (e.g. `x+y=0 ∧ x−y=1 → 2x=1`). **Strictly generalizes & replaced** the single-equation `prove_lia_unsat_by_gcd` in dispatch (no regression). Sound (only integer-preserving row ops; `checked_*` → "not refuted" on overflow, never a wrong unsat; SAT systems never refuted, negative-tested). 11+2 tests. Remaining: Gomory/cube cuts; inequality-integrated cuts |
| P2.5 | NRA: incremental linearization → nlsat/CAD | WIP — linear-abstraction + sign/zero lemmas + McCormick + spatial B&B + point-lemma refinement already shipped. **Added threshold-1 monotonicity lemmas** — growing (`a≥1 ∧ b≥0 ⇒ r≥b`, decides `x≥1 ∧ y≥1 ∧ x·y<1`) and shrinking (`0≤a≤1 ∧ b≥0 ⇒ r≤b`, decides `0≤x≤1 ∧ y≥0 ∧ x·y>y` where only one operand is bounded so McCormick can't apply); two-operand only — **plus a refinement overflow safety net** (`too_large_to_refine`: stop refining past a 2³¹ magnitude bound, → `unknown` not a panic; hardens the exact-rational simplex against escalating witnesses). **Sum-of-squares lemmas landed (2026-06-18)** — `sos_lemmas`: for a pair `a,b` with `a·a`/`b·b`/`a·b` all abstracted, add `(a±b)² ≥ 0` over the result vars (sound), restoring the cross-product correlation independent abstraction drops, so **`a²+b² ≥ 2ab` / AM–GM₂ is now PROVED** (the Spivak SOS-frontier test promoted prompt-`Unknown`→`Unsat`; negative test confirms `a²+b²=2ab` stays sat). 26 NRA + 5 Spivak tests. **Since then (2026-06-28…07-02, see the changelog + [SCOREBOARD](bench-results/SCOREBOARD.md)): the CAD arc landed** — bignum algebraic core in `axeyum-ir` (ADR-0044/45/46), a 2-var-complete / N-var decision-complete fuzz-gated CAD, coprime-split projection, first-class `/0` division witnesses (`124e18aa`), and five z3-gated adversarial differential fuzzes at DISAGREE=0. **2026-07-06/07 arithmetic arc (decomposition `fcbde209`): QF_NRA 21→27/38 (71%)** — `/0` witnesses + sat-witness probe + threshold-1 (`5cc63a15`, closed `issue9164-2`), the `a²=−k` even-power-equality (`631be06f`), the `nra_even_power` frontier wire-in (`e0e24085`, `nra_degree` 2→40), coordinate sat-witness for >4 reals (`80206579`, budget-marginal); **and the parallel QF_NIA arc drove cvc5 21→33/39 (85%): div/mod Euclidean linearization (`a946f925`+P0 fix `52f3b1d1`) + `iand` bit-blast (`c5a829a3`) + congruent Ackermann div/mod-by-zero (`b91dd918`, recovered div.01/minimal_unsat_core/div.08 + closed a pre-existing wrong-sat) + `int.pow2` value-table axioms (`fb2da08b`, +8).** Remaining is genuinely hard: 7/12 QF_NRA residue is multi-week CAD/nlsat/transcendental (Boolean-CAD, MetiTarski, degree-10) — the *funded engine arc* (ADR-0058 proposed), not a slice; NIA's bounded levers are now largely harvested (div/mod-0, iand, pow2 all landed). |
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — e-graph E-matching, trigger inference/MBQI/MBP, restricted checked Skolem/model/counterexample certificates, retained checked quantifier clauses, and incremental candidate-sensitive e-matching are live through ADR-0140. **Checked UNSAT routes (ADR-0095/0097/0099/0100/0101/0108/0124/0125/0126/0127/0128/0129/0134/0139/0140):** Euclidean residue, affine growth, nested XOR, concrete closed-universal counterexamples including universal falsifiers below proved-vacuous existential prefixes, exact finite equality partitions, source-instantiated free-Boolean covers, source-bound residual-QF_BV alternation counterexamples, evaluator-replayed negated-existential witnesses, premise-aware conjunctive and query-scoped positive universal instances, and paired-existential witness transfer each carry separate checks. **Checked SAT routes (ADR-0096/0098/0107/0121/0122/0123/0130/0131/0132/0133):** arena-stable affine/reflexive and guarded unit-gap Skolems, exact same-width BV identities, false outer-BV equality guards, free-Boolean Bool/Int models, Boolean-discharged opaque BV closures, and complete free-BV affine-LSB, negated-universal-witness, signed-interval negated-existential, and zero-product negated-existential models, and positive-universal residual-QF_BV free-Boolean models replay through canonical `check_model`; unresolved BV semantics never enter the LIA fallback. **Lean routes (ADR-0102 through ADR-0106, ADR-0108/0109/0135/0137/0138/0139/0140):** all eight decided LIA UNSAT rows reconstruct through genuine quantifiers and kernel-checked reasoning. Quantified LIA is 12/12, certified/rechecked/dominant 12/12, Lean UNSAT 8/8. The committed quantified-BV slice is 36 SAT / 18 UNSAT / 0 unknown / 0 unsupported, with 54/54 evidence-certified/rechecked, 50/54 dominant, and Lean UNSAT 14/18. ADR-0137 closes the corpus-scale ADR-0134/0135 export gap, ADR-0138 constructs genuine typed witnesses for all three ADR-0126 public rows under guarded release gates, ADR-0139 applies a typed universal witness before an evaluated-AIG refutation for `qbv-simp`, and ADR-0140 eliminates ADR-0128's vacuous existential prefix with genuine `Exists.rec` before computationally refuting `issue2031-bv-var-elim`. Remaining boundaries: broader nonvacuous existential relations and nested/alternating BV QSAT, ADR-0124/0127/0129/0130/0131/0132/0133 Lean reconstruction, non-equality online antecedents/proof serialization, measurement-gated high-frequency callbacks, generation-cost scheduling/bytecode, quantified UF/function-valued models, multi-constant equality-partition proofs, and open-context proof sharing; current bridge relevance is exact by construction. |
| P2.7 | Strings (unbounded, full `str.*`, regex) | WIP — **Phase A DONE** (ADR-0051 `Sort::Seq`; ADR-0052 `len`↔LIA link + bounded-unsat gate, repaired a measured wrong-unsat class). **Phase B core LIVE both directions (ADR-0053, landed 2026-07-03):** T-B.1 normalization → T-B.4a arrangement search → T-B.4b routing + parser dual-build → extended-fn reductions → T-B.4d word-first fallback → harness parity (**QF_S 52→78 across 07-03…06** — see the generated scoreboard, oracle-verified) → **T-B.7 slices 1–2**: word `unsat` ONLY via the independent derivation checker (`check_derivation.rs`, own union-find + walkers; word fuzz **96 sat + 305 unsat, DISAGREE=0**). Phase C derivative membership (ADR-0054), Phase D reductions, lex order, code↔LIA, #49 membership-over-concat, #53 LenAbs SAT, and #55 concat emptiness/joint search are landed; QF_S is 87/134 and QF_SLIA 18/50 on the committed scoreboard. Remaining declines are unsupported `to_int`/`replace_re`/`seq.*` machinery plus the ADR-0063 Nielsen-arrangement class; T-B.5 F-Loop/T-B.6 eager conflicts remain performance work. The canon/derivative deadline guard is closed. |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | WIP — the FP theory is broad already (classification, compare, abs/neg/min/max, add/sub/mul/div/fma/sqrt/rem/roundToIntegral, fp→fp resize, fp→real/ubv/sbv). min/max ±0 confirmed correct (deterministic allowed choice). **Added integer→float conversion** (`from_ubv`/`from_sbv`, 2026-06-18): rounds a w-bit unsigned/signed-two's-complement integer to a dst float under a rounding mode (reuses `pack_value`; exact 0→+0; |x| via two's-complement read unsigned, correct for INT_MIN). Differential-tested vs Rust's native `as f32`/`as f64` (i32/u32→F32, i64/u64→F64; edges + 3000-case sweep, exact). Completes the `to_fp` family on the builder side. Remaining: SMT-LIB parse wiring for `(_ to_fp …)`/`to_fp_unsigned` over bv sources (axeyum-smtlib, coordinate); `to_fp` from real constants; unspecified-value edge polish |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | WIP — **structural refutation** (`prove_datatype_unsat_structurally`): acyclicity + distinctness + injectivity **+ congruence** (equal args ⇒ equal apps, e.g. `x=cons(h,a) ∧ y=cons(h,b) ∧ a=b ∧ x≠y`) + constructor exhaustiveness over a term-level union-find; also flattens top-level conjunctions and refutes top-level `or` when every branch is structurally contradictory. Sound, wired into dispatch/evidence/Lean reconstruction ahead of the eager expansion; the cvc5 QF_DT exact audit is now 3/3 dominant with Lean unsat 3/3. 13 focused tests. Remaining: e-graph constructor *splitting* (case-split `is-c` on the keystone) for SAT-side completeness; exact field guards to remove the relaxed `unknown` cases; broader datatype corpora beyond the cvc5 three-row slice |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P4.1d | Retained warm array relations | **DONE, literal relation slice (ADR-0089)** — projection-owned positive equality merges before function construction; exact private diff witnesses cover top-level disequality across supported structural parents. Scope/core/filter/replay, Bool/BV256, exact depth, 192 clean comparisons, 816 solver units, 77 symexec tests, and complete EVM gates pass; EVM has no whole-array relation case, so no timing claim |
| P4.1c | Retained warm array-valued UF parents | **DONE, scalar-keyed slice (ADR-0088)** — finite-scalar applications retain private array owners and conditional read congruence; concrete-equal tuples merge observations into full-value function results before owner filtering and replay. Exact 64/65 admission, ten focused tests, 192 clean comparisons, 816 solver units, 77 symexec tests, and complete EVM gates pass; EVM has no array-result UF case, so no timing claim |
| P4.1b | Candidate-triggered retained warm ROW | **DONE, bounded transitive-summary slice (ADR-0087)** — one exact scalar summary per observed structural read stays dormant until candidate violation, then becomes a permanent root in the same CNF/SAT instance under one shared deadline. Zero-activation replay, scope/core/reuse, exact caps, 192 clean comparisons, 816 solver units, 77 symexec tests, and complete EVM gates pass. Depth 32 improves 30.933→11.257 ms; ITE-fold remains faster at 0.405 ms, so broader warm models and the performance exit remain open |
| P4.1a | Retained warm structural array reads | **DONE, bounded ownership slice (ADR-0086)** — store/constant/ITE reads receive private retained owners; roots stay selector-scoped, direct leaves alone project models, and original replay gates SAT. ADR-0087 subsequently makes their exact transitive summaries candidate-triggered |
| P4.1i | Memory-aware k-induction | **DONE** — `prove_safety_k_induction_with_memory` runs the base case through `bounded_model_check_with_memory` and the inductive step through `IncrementalBvSolver::check_with_memory`, preserving unknown-safe behavior for unsupported shapes. Safe is unbounded but validation-backed until array-aware proof export exists; focused BMC module tests cover an inductive array property and a reachable symbolic-memory counterexample |
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | DONE |
| P3.1 | LRAT clausal upgrade (+ in-tree check_lrat) | WIP — **`check_lrat` (hint-based linear checker) + `elaborate_drat_to_lrat` + parse/write** landed in `axeyum-cnf`, sound (3 negative/rejection tests) + 600-CNF differential; **threaded into the evidence export**: every `UnsatProof` (QF_BV + reduced QF_ABV/AUFBV/UF/LIA/datatype) now carries a self-checked LRAT certificate, `recheck` cross-checks it, `recheck_lrat` re-checks it in linear time, tamper-detected. Remaining: emit LRAT hints directly from the proof-producing CDCL core (vs post-hoc elaboration); RAT-step elaboration (negative hints) |
| P3.2 | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | WIP — **resolution-layer IR + parser/printer + sound `check_alethe`** in `axeyum-cnf::alethe`: `resolution`/`th_resolution` steps verified by `{premises,¬concl}`-UNSAT via the proof-producing core + `check_drat` re-check (entailment itself independently checked); verify-before-record; 7 tests incl. 3 rejection. Remaining: typed-term IR (vs opaque atoms), more rules, emit Alethe from solver runs, Carcara CI cross-check; extract `axeyum-alethe` crate (ADR) when the term IR lands |
| P3.3 | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | WIP — **arithmetic `la_generic` checking** (`check_alethe_lra`): a linear-arith tautology clause verified by `¬clause`-UNSAT via the Farkas-certified `check_with_lra`; pluggable `check_alethe_with` callback keeps `axeyum-cnf` arithmetic-free. 5 tests incl. soundness rejections. **`lia_generic` (integer) checking+emission** added via `check_with_lia_simplex` (honors integrality; integer/real distinction tested). **Carcara cross-check harness (T3.3.5)**: EUF (transitivity+congruence), **LRA `la_generic`** (Farkas `:args` incl. equalities), and **clausal resolution** (`lrat_to_alethe`, T3.3.3) proofs all externally `valid`; gated test skips without the binary. Remaining: BV `bitblast_*` rules (T3.3.1–2) for the full QF_BV proof; LRA >2-atom (`and`) assertions; `lia_generic` is a Carcara hole. **Integer-systems certificate added** (commit c19f3ce): the multi-equation Diophantine refutation (P2.4) now emits an "integer Farkas" `DiophantineCertificate` (multipliers λ s.t. `Σ λᵢ·Eᵢ` is a `gcd ∤ const` contradiction row) with an independent `check_diophantine_certificate` re-deriving it from the originals — self-validated, tamper-tested. This is the in-tree route for integer-systems infeasibility that `lia_generic`/Carcara can't check |
| P3.4 | Embedded Alethe checker subset (self-checking) | TODO |
| P3.5 | Alethe for reductions (arrays → Ackermann → int-blast) | WIP — direct select consistency and equal-array same-index congruence now use standard Alethe equality rules; ADR-0075 makes the latter one artifact accepted in-tree, by Carcara (forward/reverse + tamper rejection), and by real Lean with no array-elimination trust step. ROW same/diff collapse reasoning is externally checked modulo an asserted ROW rewrite instance. Remaining: certify the ROW axiom itself, disequality/diff-witness extensionality, portable equality chains, canonical online proof logging, and the broader Ackermann/int-blast ledger |
| P3.6 | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | WIP — **crate started (ADR-0036, commit db18886)**: destination-3 (Lean parity) foundation. `Name`/`Level`/`Expr` + de Bruijn ops (instantiate/abstract/lift) ported from `references/nanoda_lib`, adapted to axeyum's **lifetime-free Copy-id interning** (no `'a` leaks). Faithful level `leq`/`is_equiv`/`simplify` + param subst; Expr with `BinderInfo`; cached `num_loose_bvars`/`has_fvars`. 27 tests incl. translated nanoda level tests + de Bruijn laws. **Type-theory core landed (slice 2, commit e37da7b)**: `whnf` (beta/zeta), `def_eq` (lazy structural + Pi/Lam congruence + eta + proof irrelevance), and checking-mode `infer` (Sort/FVar/App/Lam/Pi/Let, IMax impredicativity) over the **environment-free fragment** — the kernel now TYPE-CHECKS terms (polymorphic identity infers `Π(α:Sort 0),α→α`, etc.). Faithful nanoda port; the env boundary (`Const`/δ, inductives/ι, projections, literal typing) errors explicitly (`KernelError`), never a wrong accept. 52 kernel tests. **Environment + Const δ landed (slice 3, commit f0f6e0d)**: non-inductive declarations (Axiom/Definition/Theorem/Opaque) with `ReducibilityHint`; `Environment` (deterministic `BTreeMap`); `add_declaration` is the trusted gate (type-checks each decl's type-is-a-sort + value `def_eq` declared type); universe instantiation; `infer(Const)`; δ-unfolding in `whnf`; faithful `lazy_delta_step` (height-based side choice, same-const short-circuit, Opaque/Axiom non-unfolding). The kernel now type-checks terms referencing globals (`id := λαx,x` admits + δ+β-reduces under application). 68 kernel tests. **Inductive layer started (slice 4, commit 4457594)**: `Declaration::{Inductive,Constructor,Recursor}` + `RecRule`; `add_inductive` (trusted gate: type whnf's to a Sort, constructor telescopes type-check + end in `I` + **non-recursive** field restriction); **recursor generation** (`I.rec : Π {motive}(minors…)(major), motive major`, with the generated type infer-self-checked) + **ι-reduction** (`I.rec … (c_i flds) → m_i flds`). Scoped to **non-recursive, non-parametric, non-indexed** inductives — enums (`Bool.rec` ι picks the right minor) + structures (`P.rec C m (mk x y) → m x y`); param/indexed/mutual + Prop-subsingleton large-elim DEFERRED (reject explicitly). **Recursive inductives landed (slice 5, commit 24607a9)**: DIRECT recursive fields (field type exactly `I`, e.g. `Nat.succ : Nat→Nat`) now admitted; `mk_recursor` adds one IH binder `motive f_j` per recursive field to each minor (`Nat.succ`'s minor = `Π(n:Nat)(ih:motive n), motive (succ n)`); recursive ι appends a recursive `I.rec … f_j` call per recursive field (`Nat.rec C z s (succ k) → s k (Nat.rec C z s k)`). **The kernel checks AND computes with `Nat` and binary trees** (end-to-end recursive normalization verified; recursor type infer-self-checks). Higher-order/reflexive fields, params, indices still rejected. 82 kernel tests. **Parametric inductives landed (slice 6, commit bc95c21)**: `add_inductive(num_params)` — leading binders are params (fixed across the family), recursive field = `I params` (generalizing bare `I`); recursor abstracts params before the motive and threads them through minors/IH/ctor-apps + recursive ι calls. **`List`/`Option`/`Prod`/`Sum` check + compute** (`List.rec α C cnil ccons (cons α a l) → ccons a l (List.rec … l)`; a length recursion normalizes; recursor types infer-self-check). Indices (`Eq`/`Vector`, a binder between params and the `Sort`) → `IndicesNotSupported` (deferred). 92 kernel tests. **Indexed inductives landed (slice 7, commit 223e81c)**: indices after params; the dependent motive ranges over indices + major; each minor applies the motive to the constructor's OWN index exprs; index-matching ι. **`Eq.rec` (the dependent eliminator used in every equality proof) generates, infer-self-checks, and ι-reduces on `refl`** (`Eq.rec α a motive m a (refl α a) → m`); an end-to-end transport/symmetry normalizes; a 2-ctor indexed family picks the right minor by index. Recursive-indexed (`Vector.cons`) → `RecursiveIndexedNotSupported` (deferred). 97 kernel tests. **The inductive layer now covers non-recursive + recursive + parametric + indexed — essentially all of Lean's inductive families** (bar recursive-indexed/nested/mutual + projections + literal typing + Prop-subsingleton elim). Next: **P3.7 Alethe→Lean reconstruction** (where this kernel finally checks reconstructed solver proofs — the destination-3 payoff) + the remaining minor inductive cases. |
| P3.7 | Alethe→Lean reconstruction (proof terms) | WIP — **foundation laid (commit ab2e615)**: `axeyum_lean_kernel::build_logic_prelude` declares the standard Lean logical foundation (`True`/`False`/`And`/`Or`/`Iff`/`Eq`/`Not`) through the trusted gates, and the kernel **type-checks real proof terms** — And.intro, and-elim (via And.rec), Or case analysis, Eq symmetry transport (checks + ι-reduces on refl), modus ponens, ex-falso (False.rec), and a composite `And A B → And B A`. 15 proof tests. The kernel is a Lean-grade checker of real proofs. **Reconstruction started — Eq fragment (slice 1, commit 56709ef)**: `axeyum-solver` gained a dep on the leaf `axeyum-lean-kernel`; the new `reconstruct` module translates Alethe equality terms to Lean `Expr` (`(= a b)` → `Eq.{1} α a b`) and the **`eq_reflexive`/`eq_symmetric`/`eq_transitive`** Alethe rules into `Eq.rec` proof terms the **kernel type-checks** (`def_eq` against the translated conclusion — the kernel is the checker; a wrong term is rejected). End-to-end transitivity chain reconstructs + kernel-checks; 2 negative soundness tests (wrong conclusion rejected). 11 tests. **End-to-end EUF refutation reconstructed (slice 2, commit 7267b2d):** `reconstruct_qf_uf_proof` walks a REAL `prove_qf_uf_unsat_alethe` proof — `assume` (eq → `h:Eq`, diseq → `h:Not(Eq)`), `eq_transitive`/`eq_symmetric` (n-ary fold + reversed-edge flip), `eq_congruent` (unary, congrArg via `Eq.rec`), and the closing resolution to the empty clause → `h_ne h_eq : False` — into a Lean term the **kernel checks to `False`**. 7 end-to-end instances (transitivity `a=b∧b=c∧a≠c`, longer chain, reversed edge, depth-1 congruence `f(a)≠f(b)`) + 2 negative tests. 17 tests. **Propositional resolution reconstructed (slice 3, commit fc23d4c):** the clausal layer — atom → opaque `Prop`, `(cl l…)` → right-nested `Or`, `(cl)` → `False`; `reconstruct_resolution_proof` builds the resolvent via iterated `Or.rec` (constructive case-split; `em` declared for the classical commitment but unconsumed), pivot-scheduled for the emitter's arbitrary-order RUP hints. **A REAL emitted clausal proof reconstructs end-to-end** (UNSAT CNF → `solve_with_drat_proof` → LRAT → Alethe → kernel-checked `False`). 26 tests. **Both the EUF and the clausal-resolution fragments now close to kernel-checked `False`.** **Tseitin CNF-intro rules reconstructed (slice 4, commit 237d13b):** `reconstruct_cnf_intro_rule` builds all 12 gate-definitional tautologies (`and_pos/neg`, `or_pos/neg`, `equiv_pos1/2`+`neg1/2`, `xor_pos1/2`+`neg1/2`; `xor a b := Not(Iff a b)`) as kernel-checked classical-tautology proofs (em + Or.rec case-split + prelude eliminators); a composite feeds a reconstructed `and_neg` clause through the slice-3 resolution to `False`. 43 reconstruct tests. **P3.7 now covers EUF + clausal resolution + the Tseitin Boolean-gate layer.** **Bitwise QF_BV bitblast reconstructed (slice 5, commit 4b356b3):** bit model — each bit a Lean Prop, variable bit → opaque `((_ @bit_of i) x)`, const → `True`/`False`, `bvnot/and/or/xor` pointwise (`xor` = `Not(Iff)`), `@bit_of i (@bbterm bs)` → `bs[i]`. `reconstruct_bitblast_step` kernel-checks all 7 bitwise rules (`var`/`const`/`not`/`and`/`or`/`xor`/`equal`; the bit-iffs are reflexive under the pointwise model); non-bitwise → `UnsupportedRule`. `reconstruct_qf_bv_proof` walks a REAL `prove_qf_bv_unsat_alethe` bitwise proof → **kernel-checked `False`** (1-bit bvand w/ full cong/trans/`@bbterm` plumbing + width-2 eq). 55 reconstruct tests. **HONEST soundness boundary:** the bit-level Boolean refutation + each bitblast step's bit-iffs are GENUINELY kernel-checked, but the term-level `cong`/`trans`/`equiv` bridge (`(= bvterm @bbterm)` transport) enters resolution as out-of-band-verified clause hypotheses, not yet fused into the single `False` term. **Eq-transport bridge FUSED (slice 6, commit 8c19e23):** the bitwise QF_BV reconstruction is now a CLOSED proof — `False` derived from ONLY the input assumptions + prelude + `em`, **no bridge axioms** (asserted via `declared_axiom_roles()` = `[assume,assume,em]`). Input `(= s t)` → hypothesis `h:⟦B⟧` directly; equiv1/2 → genuine `¬B∨B` tautologies (not assumed); term-level cong/trans deferred (never load-bearing); bit-iffs kernel-checked up front. 58 reconstruct tests. **The bitwise QF_BV unsat fragment reconstructs to a fully-kernel-checked, axiom-free Lean `False` proof.** Remaining for full QF_BV: arithmetic bitblast (`bvadd`/`bvmul` carries). **LRA arithmetic prelude built (commit 6869e49):** `axeyum_lean_kernel::build_arith_prelude` declares an axiomatized linear ordered field (carrier `R`, `add/mul/neg/zero/one`, `le/lt`, order+additive+scaling axioms) through the trusted gate; a **baby-Farkas refutation kernel-checks to `False`** (`le a 0 ∧ le 1 a` → `lt 1 1` → `lt_irrefl` → False). 119 kernel tests. **VERIFIED CURRENT STATE (2026-06-20 — the above history understated coverage; confirmed by reading the dispatch at `reconstruct.rs:1334`):** the `prove_unsat_to_lean` dispatch now reconstructs **8 fragments** to kernel-checked `False` — **QF_BV (bitwise AND arithmetic: `bitblast_add` ripple-carry + `bvneg`/`bvmul`/`bvsub`/concat/extend, memoized-linear carry, closed over assume+em), QF_UF (EUF congruence), QF_UFBV, QF_ABV (via array elimination), datatypes (via simplification), ∀ (quantifier unsat), ∃ (skolem), and QF_LRA (general n-constraint arbitrary-rational `la_generic` Farkas — `try_general_farkas`/`try_mixed_farkas`/`try_strict_cycle`, λ-denominators cleared, ring cancellation via explicit kernel-checked `Eq` rewrites)**. Since `has_arith→Lra`, QF_LIA whose LP-relaxation is Farkas-infeasible ALSO reconstructs (ℤ⊂ℝ). **Integer equality-system infeasibility is ALSO reconstructed** — `int_reconstruct::reconstruct_diophantine_to_lean_module` (ADR-0042, wired into the dispatch at `reconstruct.rs:3723`) turns the `DiophantineCertificate` (P2.4) into a kernel-checked Lean `False` over the discretely-ordered ring `IntPrelude` (encode each `Eᵢ` as `h:Eq Z`, derive `Σλᵢ·Eᵢ`, reduce to `g·m'=r, 0<r<g`, close on the discreteness axiom `no_int_between`); `diophantine_lean_reconstruct.rs` covers it. **Genuine remaining proof gaps (the hard frontier):** integer *inequality* cutting-plane QF_LIA (LP-feasible-but-no-integer-point over inequalities via Gomory/cube cuts — the Diophantine route above is equality-systems only), NIA/NRA proofs (bar the degree-2 SOS fragment, which reconstructs), strings, FP-arith — each genuinely hard. |

> P3.7 update (2026-06-27): `prove_unsat_to_lean_module` and
> `reconstruct_sos_to_lean_module` now retry with a normalized assertion spine
> after direct reconstruction declines, splitting top-level conjunctions and
> stripping repeated top-level double negations. This closes the consumer-facing
> shape-sensitivity gap for common `hyps ∧ ¬goal` queries while preserving
> existing direct-route priority; focused real-Lean regressions cover a
> normalized finite-BV+UF refutation and a normalized array read-over-write
> refutation.

### Track 4 — Use Cases & Frontend
| Phase | Title | Status |
|---|---|---|
| P4.1j | Glaurung warm delta and duplicate/prefix reuse (GQ7/GQ8) | WIP — retained CNF, learned state, and push/pop are foundations; remaining work is affected-term-only `assert_configured` preprocessing, measured warm break-even, versioned canonical query keys, exact-duplicate verdict/model/proof reuse, sound extending-prefix CNF/search reuse, deterministic cache bounds, and mandatory original-term replay |
| P4.1e | Retained warm Boolean array relation flags | **DONE (ADR-0091)** — symbolic-memory path conditions can keep nested supported array equality atoms warm through private candidate-sensitive relation flags, guarded equality/diff observations, projection filtering, and replay |
| P4.1h | Retained warm nested array-valued UF parameters | **DONE (ADR-0094)** — nested supported array-valued memory/function parameters can stay warm as full-value UF keys through private projection keys or rewritten structural keys, with relation-flag guarded congruence, private filtering, and replay |
| P4.1g | Retained warm structural array-valued UF parameters | **DONE (ADR-0093)** — supported store/constant/array-ITE memory/function parameters can stay warm as full-value UF keys with scalar dependency retention, structural owner realization, relation-flag guarded congruence, private filtering, and replay; ADR-0094 subsequently lands nested application keys |
| P4.1f | Retained warm direct array-valued UF parameters | **DONE (ADR-0092)** — direct finite-array memory/function parameters can stay warm as full-value UF keys with relation-flag guarded congruence, deterministic distinct key projection, private filtering, and replay; ADR-0093 subsequently lands supported structural array keys |
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | WIP — committed assertions and one-shot assumptions over arrays/UFs route through memory-aware APIs with original-term replay/core reporting. The warm path now admits reducible ROW and array-ITE readbacks, retained BV-indexed Bool/BV selects, scalar UF applications, scalar-keyed array-valued UF parents (ADR-0088), projection equality and exact structural disequality witnesses (ADR-0089), top-level positive structural equality over supported store/constant/array-ITE parents through private constructor owners plus class-aware realization (ADR-0090), nested Boolean array-relation flags (ADR-0091), direct array-valued UF parameters (ADR-0092), supported structural array-valued UF parameters (ADR-0093), nested array-valued application keys (ADR-0094), and memory-aware k-induction through eager memory elimination. `SymbolicExecutor` and `SymbolicMemory` use these warm abstractions before falling back to the full dispatcher. Remaining: certified memory k-induction, memory PDR/IMC, path-condition CFG/import frontends, nested/extended arrays, deeper memory helpers, online proofs, and broader performance measurement |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | WIP — first frontend-facing primitives landed: `SymbolicMemory` wraps an SMT array memory state, builds `select`/`store`, routes load-equality branch/assume queries through `SymbolicExecutor`'s automatic warm/memory feasibility APIs, and now exposes conservative write-log normalization / compact read-specific read-over-write `ite` construction for frontend memory logs that skips literal-distinct writes, elides exact-hit guards, preserves later symbolic aliases, and uses the auto route; `SymbolicExecutor::assume_auto` and `SymbolicExecutor::branch` keep same-index store/read-back constraints, literal-distinct concrete-address store-chain misses, zero-initialized constant-array reads, simple array-ITE state-merge reads including same-readback merge-guard and tautology pruning, reducible conditional read/write-index paths with scalar equality-over-`ite` cleanup, symbolic Bool readback equality/connective/xor/implication cleanup, BV bitwise/arithmetic/comparison/slice-extension/shift/div-rem readback cleanup, reducible symbolic-address ROW over store chains with same-index shadowed-store pruning, plain symbolic-base Bool/BV array loads via retained select-congruence abstraction including wide/BV256 index or element projection, direct equal-array symbol assumptions/assertions via retained cross-array select congruence and equal-array model projection, scalar Bool/BV UF applications via retained congruence abstraction including wide/BV256 argument or result projection, helper-level load/write-log queries, and default `explore_cfg` branch/assume/status/model queries on the warm BV path when they reduce or abstract, with original-term replay, while remaining general memory/UF still auto-promotes to the memory/theory-aware route; `SymbolicExecutor::explore_cfg` provides a reusable DFS harness over frontend-supplied CFG states, with solver-scope management, infeasible pruning, unknown-safe traversal, and model-witnessed targets; `explore_cfg_checked` adds frontend-supplied concrete witness extraction + replay callbacks and buckets targets into verified/missing-witness/mismatch cases; `TinyBvProgram` is the first reusable small-target frontend, with a validated BV register/memory IR, label-aware line-oriented assembly import with retained label/source metadata, deterministic PC-to-label lookup, typed static CFG edges and basic blocks, deterministic Graphviz DOT export for the basic-block CFG plus trace-highlighted, block-coverage-highlighted, and edge-coverage-highlighted DOT overlays, block-level trace paths, taken-edge trace reports, source-aware trace rows, consolidated witness trace reports, replay-checked test-case generation reports, block-coverage and edge-coverage test-suite reports, register-register equality branches, symbolic instruction lifting, zero-initialized SMT array memory for `Load`/`Store`, model-witness extraction, independent concrete replay, concrete execution traces, and bounded PC/label reachability/safety reports. Remaining: byte-level/binary broader target work, unbounded/certified safety wrappers over richer CFGs, and eventually general warm memory reuse from P4.1 |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | WIP — single-objective `maximize/minimize_lia` + `_bv`/`_bv_signed` already shipped (exponential+binary bound search, Boolean-structured oracle). **Lexicographic multi-objective landed** (`optimize_lia_lexicographic`, 2026-06-18): optimize objectives in order, pinning each at its optimum (`obj≥v`/`obj≤v`) before the next so later ones range over the optimal face — z3's default lex combination. Sound + terminating (bounded composition of the checked single-objective optimizer); `LexOutcome::Stopped` at the first unbounded/infeasible/unknown objective. **BV lexicographic also landed** (`optimize_bv_lexicographic`, signed/unsigned, `bv_uge/ule/sge/sle` pinning) — lexicographic OMT now covers both LIA and BV. **Box** (`optimize_lia_box` / `optimize_bv_box`, independent) **and Pareto** (`optimize_lia_pareto` / `optimize_bv_pareto`, guided-improvement front enumeration, deterministic point/push caps, each point verified Pareto-optimal) modes also landed — **axeyum now has all 3 of z3's OMT modes (box, lexicographic, pareto) across LIA+BV**. BV Pareto covers unsigned and signed objective values, max/min directions, and graceful `Unknown` for out-of-fragment objective values. MaxSAT returns the witnessing model (`max_satisfiable_model`). `minimize_model` / `Solver::minimize_model` provide replay-checked lexicographic counterexample minimization over selected Bool, unsigned-BV<=127, and Int symbols, and the metadata-aware `minimize_model_objectives` / `Solver::minimize_model_objectives` route adds signed two's-complement BV objective order for signed SDK inputs. `produce_evidence_minimized` / `prove_minimized` preserve the default surface, while `_with_objectives` variants expose signed-objective metadata to frontends. `axeyum-property` v0 is now the first typed SDK consumer of that surface: Bool/BV/Int handles, assumptions, proof calls, minimized countermodel lifting, checked `EvidenceReport` exposure plus best-effort standalone Lean modules and stable evidence/trust/Lean summaries through `ProofCertificate`, typed BV overflow predicates, `.equals()` equality aliases, property-owned Bool/BV/Int builder aliases, `Property::all` / `Property::any` Boolean folds, deterministic native-scalar counterexample-to-`#[test]` rendering with caller-owned prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, deterministic multi-case fixture file assembly, direct named/tuple aggregate initializer snippets, and explicit nested aggregate field composition, scalar/tuple/derived-struct `Symbolic` declarations/lifting including signed-order two's-complement fixed-width Rust integers, named-field `symbolic_struct` bundles, and the generated SDK corpus/scoreboard gate with 16 graduated workflows, deterministic executable baseline comparisons for scalar counterexamples, an actual fixed-seed proptest shrunk counterexample, struct and replay counterexamples, proved assertions, assumption-backed proved assertions, and a Kani-style assume/assert counterexample baseline, machine-readable `corpus.json`, DISAGREE=0, and 1/1 Lean-required coverage. Remaining: MILP hardening; broader objective support for minimized counterexamples beyond Bool/BV/Int native scalars; property SDK ergonomics (operator traits, richer replay bodies); richer proptest families and real Kani CLI-backed property corpus comparison; differential validation vs Z3 `opt` |
| P4.4 | SMT-LIB command-surface completeness (declare-sort, reset, get-proof, …) | WIP — broad command surface already parsed (declare-const/fun/datatype(s), define-fun/sort, push/pop, reset(-assertions), check-sat(-assuming), get-proof/model/value/unsat-core/assignment/assertions, set-option/info, get-option, echo/exit); term forms let/forall/exists/`!`/`as` handled. `reset-assertions` is represented and honored by scoped incremental solving; full `(reset)` is explicitly rejected in the shared-arena parse/solve model. The single-result front-door helpers (`solve_smtlib`, OMT, `get-value`, `get-unsat-core`, `get-proof`, `get-assignment`) now replay the command stream for zero-or-one-query scripts, honoring `push`/`pop`, `check-sat-assuming`, and `reset-assertions` instead of flattening scoped scripts; multi-query scripts are rejected there and routed to `solve_smtlib_incremental`. `solve_smtlib_get_model` returns user-declared constants/functions for sat `(get-model)` scripts as Rust IR values, `solve_smtlib_get_assignment` returns active top-level named assertion assignments for sat scripts while filtering popped/reset assertions, and `solve_smtlib_get_assertions` returns exact command-point assertion-stack snapshots rendered from IR while excluding one-shot `check-sat-assuming` literals. The parser records `set-info`, `set-option`, requested `get-info`, and requested `get-option` commands; `solve_smtlib_get_info` returns recorded metadata, axeyum defaults for `:name`/`:version`, computed `:reason-unknown`, and explicit unsupported markers, while `solve_smtlib_get_option` returns recorded/default option values and explicit unsupported markers. **`match` datatype pattern-matching added** (commit d404794, P4.4): parse-time desugaring to nested `ite`/`DtTest`/`DtSelect`, exhaustiveness + arity checked, 11 tests. Remaining: parametric `declare-sort`/`define-sort`, `define-fun-rec`, full `match` for parametric datatypes, full option-driven solver semantics, and textual interactive command output |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | **DONE for the generic gate; WIP/BLOCKED for GQ1/GQ10 pending the external Glaurung capture.** The committed multi-division scoreboard plus Pareto-dominance report remains live. Current regenerated state (authoritative totals live in the generated [SCOREBOARD](bench-results/SCOREBOARD.md) — machine-derived, check it rather than any hand-copied figure): 35 measured rows, DISAGREE=0, and 23 complete per-instance dominance audits under `bench-results/dominance/`. The first `audit now` queue is fully measured; BV-quantified/ABV/AUFBV/QF_ALIA/QF_AX/QF_BV-bvred/QF_BVFP/QF_DT/QF_FF/QF_FP/QF_LRA/QF_LIA/QF_NIA/QF_NRA/QF_UF/QF_UFBV/QF_UFFF/QF_UFLIA exact audits have zero audit errors/timeouts, and the proof/evidence work has moved exact coverage to BV/bitwuzla quantified **4/4**, BV/cvc5 quantified **37/37**, QF_ABV **169/169**, QF_ALIA **6/6**, QF_AUFBV **41/41**, QF_AX **8/8**, QF_BV/bvred **6/6**, QF_BVFP **7/7**, QF_DT **3/3**, QF_FF **24/24**, QF_FP **16/16**, QF_LRA **9/9**, QF_LIA **10/10**, QF_NIA synthetic **32/32**, QF_NRA synthetic **30/30**, QF_UF bounded declared-sort **44/44**, QF_UF overbound declared-sort **4/4**, QF_UFBV/bitwuzla **2/2**, QF_UFFF **8/8**, QF_UFLIA curated **2/2**, QF_UFLIA bounded **6/6**, and QF_UFLIA parent **6/6** dominant. GQ1/GQ10 add the actual real-lifter query tier, stage attribution, regular representative subset, scheduled full run, and per-commit Z3-relative tracking; a synthetic substitute cannot close them |

### Track 5 — Verified Systems (IR reflection) — ADR-0056, adopted 2026-07-06
| Phase | Title | Status |
|---|---|---|
| P5.1 | Reflection front end (crate-ify the MIR+LLVM reflectors, full `.ll` parser, MIR extraction pipeline, loops→`TransitionSystem`, memory beyond byte arrays) | WIP — **T5.1.1 DONE (`cc695925`, ADR-0057)**: the reflectors are now the real library module `axeyum_verify::reflect` (`src/reflect/{mod,mir,llvm}.rs`, submodules `reflect::mir`/`reflect::llvm`), no longer per-test scaffolding — 8 test binaries (62 tests) rewired to `use axeyum_verify::reflect::…` and green, `missing_docs`+`implicit_hasher` API-hardened, clippy/rustdoc `-D warnings` clean; the crate split is deferred (one consumer today). The prototyped *capability* (rounds Q–U, design log `docs/consumer-track/verify/reflect-common-abstraction.md`): CFG symbolic executors for both IRs over one shared op vocabulary; 16 cross-IR equivalence proofs (MIR≡LLVM per function, LLVM O0≡O2, if-conversion/strength-reduction/umin-idiom validated, hypothesis-gated `unreachable`); 5-shape wrong-transform refutation corpus with replay-checked countermodels; exact panic specs from rustc's own checks (overflow, division `b==0` / signed `∨ (a==MIN ∧ b==-1)`, bounds over all 2^64 indices) with `catch_unwind` witness replay; checksum micro-module end-to-end on both platforms. Remaining T5.1.2–6: token-level `.ll` parser for unmodified compiler output, build-time MIR extraction, automatic loop bridging, `gep`/`load`/`store` + array writes, the semantics gate. Individual proofs are milliseconds — the suites already run as ordinary per-commit tests |
| P5.2 | Contracts & modular verification (`#[requires]`/`#[ensures]`, calls as composition) | TODO — the architectural unlock for cross-function claims; exit: the checksum module re-proves modularly (without the MIR inliner), with a modular-vs-inlined differential gate at DISAGREE=0 |
| P5.3 | Kernel obligations: bounded memory/page-table math, 2-safety/constant-time via self-composition, protocol-FSM refinement | WIP — **T5.3.1 (branch leakage) DONE (`ac7494f0`)**: `reflect::hyper::control_flow_ct_goal` proves **constant-time** by self-composition — the MIR reflector records `switchInt` scrutinees as control-flow leakage (`reflect_mir_params_with_leaks`), and two runs (shared-public / distinct-secret) must leak identical branch decisions. `constant_time.rs` (4 tests): public-predicated PROVED CT while its output is refuted secret-independent (the crisp distinction), secret-predicated REFUTED with a replay-checked witness, branch-free trivially CT. Residual: memory-index (cache-timing) + LLVM-side leakage; page-table math waits on P5.1 memory (T5.1.5); FSM refinement (T5.3.3) unblocked next. 2026-07-08 provable-security scout adds a future crypto micro-suite demand signal here (constant-time kernels + transcript/protocol examples), after current P5.3/P5.4 obligations stabilize |
| P5.4 | Fuzz-oracle loop (reflections as differential oracles, countermodels as seed corpora + generated `#[test]`s, honest `unknown`→directed-fuzz handoff) | WIP — **T5.4.1 DONE (`2423eaeb`)**: `reflect::oracle::DiffFuzz` is the reusable differential-fuzz harness (both shapes: reflection≡reflection via `check_agree`, reflection≡real-fn via `check_against`; deterministic LCG+corners; `FuzzReport`/`assert_agreed` for DISAGREE=0). Two suites collapsed onto it (cross-IR differential fuzz, checksum module oracle). Remaining: convert the `llvm_reflection` buffer/mixed-width loops (T5.4.1 residual); countermodels→seed corpora + generated `#[test]`s (T5.4.2); `unknown`→directed-fuzz handoff (T5.4.3); coverage accounting (T5.4.4) |
| P5.5 | External target, measured (Maestro / Hubris / Tock / Asterinas-OSTD slice / rust-sel4 task) | TODO — the measured-not-seeded rule applies doubly: the exit is a committed scoreboard result on someone else's code (module verified or bug found+reproduced), DISAGREE=0, wall-times recorded |

## Changelog

- **2026-07-14 — checkpoint bounded ADR-0124 proof construction and streaming
  Lean export.** Compact module output has a byte-identical streaming writer,
  solver reconstruction spools before final inference, requested-local
  abstraction prunes unrelated DAGs, and a new scope-aware closing traversal
  binds the full nested eliminator skeleton once. The public
  `small-pipeline-fixpoint-3` pipeline passes at 3,692,844 KiB under 4 GiB;
  `bug802` reaches the final kernel check before its remaining 2.18 GiB
  allocation. Coverage stays 14/18 until that trusted inference boundary and
  both ignored release equality gates pass.

- **2026-07-13 — GQ1/GQ10 artifact-v22 deterministic resource profile
  implemented.** `SolverConfig::resource_limit` now bounds the default cold
  BatSat path through deterministic `within_budget` progress checks and the
  proof-producing native core through an explicit conflict cap; Z3 retains its
  `rlimit` mapping. Exhaustion is classified `Unknown(ResourceLimit)`, never a
  verdict. The benchmark exposes and hashes `--resource-limit`, records
  backend-specific units, and `--require-deterministic-resources` rejects a
  missing/zero search, DAG-node, CNF-variable, or CNF-clause limit before corpus
  work. Every Glaurung recipe now selects the provisional named
  `axeyum-qfbv-cold-bounded-v1` profile (2M search / 300k DAG / 3M CNF variables
  / 8M CNF clauses); wall timeout remains explicitly non-deterministic. Rust
  tests force both BatSat and proof-CDCL resource exhaustion, an end-to-end
  SAT-BV test checks `UnknownKind::ResourceLimit`, and repetition fixtures reject
  decorative/mismatched resource records. Clean revision `fe65b076` produced
  the v22 performance/proof smokes and three-trial baseline: each performance
  trial is 2/2 decided/manifest-agreed/Z3-agreed with zero errors,
  disagreements, or replay failures; the proof companion checks its 1/1 UNSAT
  with none missing; and the baseline Axeyum/Z3/ratio CVs are
  32.63%/2.59%/29.92%. Clean candidate revision `01c2441a` completes the v22
  cross-commit smoke with identical corpus/manifest/config/environment/backend/
  resource identity. Its ratio mean moves +21.78%, candidate ratio CV is
  20.40%, the descriptive standardized delta is +0.97, and raw Z3 moves +2.65%.
  These are bounded-profile, sub-millisecond plumbing results only and support
  no performance regression or speedup claim.
- **2026-07-13 — GQ1/GQ10 artifact-v21 executable determinism identity
  implemented.** The audit found that the former benchmark `--seed` option only
  changed artifact identity and did not configure either backend. That option is
  removed. `config.determinism` and `config_hash` now bind the actual
  Cargo.lock-pinned BatSat defaults (seed `91648253`, random-variable frequency
  `0`, randomized polarity off, randomized initial activity off), explicit Z3
  `random_seed=0`, and deterministic corpus order. The BatSat values are read
  from the same option constructor the wrapper uses and pinned by a Rust test;
  the repeated-run validator fails closed on profile drift. This fixes the
  fixed-seed acceptance gate without claiming deterministic wall time or
  discharging the separate deterministic-resource-limit requirement. Clean
  revision `d39dc6ac` produced the v21 performance and proof smokes plus a
  three-trial repeated baseline: both direct smokes are 2/2
  decided/manifest-agreed/Z3-agreed with zero errors, disagreements, or model
  replay failures; the proof companion checks its 1/1 UNSAT with none missing;
  and the repeated baseline reports Axeyum/Z3/ratio CVs of 3.66%/2.36%/6.06%.
  A distinct clean candidate at `00a745c0` completes the v21 cross-commit smoke
  against that baseline with matching corpus/config/environment/backend
  identity. Its ratio mean moves -13.55%, but candidate ratio CV is 31.35%, the
  descriptive standardized delta is -0.85, and raw Z3 moves +1.83%; these remain
  micro plumbing results, not Glaurung performance evidence or a speedup claim.
- **2026-07-13 — GQ1/GQ10 artifact-v20 reproducible experiment identity
  implemented.** Artifacts now distinguish source revision from execution
  environment: Git revision/cleanliness, Cargo.lock SHA-256, rustc/cargo, exact
  build profile, backends, CPU, kernel, parallelism, and memory are explicit,
  while a stable `environment_hash` excludes the revision so consecutive commits remain
  comparable under matching `config_hash + environment_hash`.
  `--require-reproducible-run` rejects dirty/incomplete source identity before
  solving, and every Glaurung performance/proof recipe enables it. Unit tests
  pin hardware parsing, completeness, dirty rejection, source-hash exclusion,
  and hardware-hash sensitivity; a live dirty-tree negative run fails as
  intended. Clean v20 smoke artifacts are the immediate post-source-commit
  checkpoint: both release smokes name clean source `f1ed213e`, use the same
  environment hash, and are 2/2 decided/manifest-agreed/Z3-agreed with zero
  errors/disagreements/model-replay failures; the proof companion checks its
  1/1 UNSAT with zero missing proofs. These are identity/plumbing results only;
  no client performance conclusion is added.
- **2026-07-13 — GQ1 artifact-v19 replay attribution and proof companion
  landed.** SAT model reconstruction/replay against untouched assertions is now
  a separately timed stage included in each cold total, PAR-2, layer p50/p95,
  and both sides of the embedded Axeyum/Z3 comparison. `--prove-unsat` selects
  the proof-producing native core; any UNSAT without an inline-checked DRAT proof
  or checker timing fails the harness. Proof-check time is exposed separately as
  a nested part of SAT time, and dedicated Glaurung proof recipes keep that
  assurance cost out of the default batsat performance artifact. Both release
  micro smokes are 2/2 decided/manifest-agreed/Z3-agreed with zero errors or
  replay failures; the proof smoke checks 1/1 UNSAT with zero missing proofs.
  This closes another GQ1 instrumentation/validity gap but the external lifter
  capture still gates the actual profile and every optimization choice.
- **2026-07-13 — GQ1 artifact-v18 original-query shape profiling landed.** The
  harness now profiles unique nodes in every untouched parsed query DAG before
  rewriting: formula size/depth/sharing, BV width diversity,
  extract/concat/zero/sign-extension and surviving `select`/`store` operations,
  demanded-vs-source extract bits, and each exact GQ3 cancellation opportunity.
  Corpus summaries expose deterministic p50/p95 formula distributions and the
  layer profile now includes AIG/CNF size distributions. The fixture exercises
  all four peephole families plus exact low-slice zero-extension cancellation;
  bench tests and focused Clippy pass. The release manifest smoke is 2/2
  decided/manifest-agreed/Z3-agreed with zero errors/replay failures and emits a
  v18 artifact; its zero target-shape counts correctly expose why the micro
  arithmetic corpus is not the client distribution. This verifies future
  captures' shape but does not close GQ1/GQ10 or make a synthetic performance
  claim.
- **2026-07-13 — checkpoint ADR-0124 Lean alternation export work without
  claiming coverage.** Exact implication-shaped source reconstruction,
  evaluator-proved antecedent application, local-let Alethe tails, linear
  dependent-let telescope checking, transient compact-share maps, and guarded
  cache release for final serialization are committed. Kernel 167/167,
  alternation 7/7 non-stress, and focused Clippy pass. Both release-only public
  stress tests remain ignored and the last 4 GiB attempt allocation-failed;
  coverage stays 14/18 pending a measured peak reduction and restored
  direct/router stress equality.
- **2026-07-13 — GQ1/GQ10 artifact-v17 corpus manifest contract landed.**
  Manifest v1 binds an external run to source/logic, exact normalized `.smt2`
  membership, per-query SHA-256, expected verdict, family, stable order, and
  named tiers. The harness validates the entire pack before selecting a tier,
  rejects drift/unlisted queries and anonymous `--limit` prefixes, includes the
  manifest digest/tier in the config identity, annotates every instance, and
  fails unless every selected verdict agrees independently of SMT-LIB `:status`.
  The updated Glaurung recipe requires the manifest; a committed representative
  micro smoke is 2/2 decided/manifest-agreed/Z3-agreed with zero errors or replay
  failures and is explicitly not client performance evidence.
- **2026-07-13 — GQ1 artifact-v16 cold attribution landed.** The benchmark now
  measures word preprocessing, bit-blast, CNF encode/inprocess, SAT, and model
  lift separately with aggregate and exact p50/p95 output. Its embedded-client
  ratio compares Axeyum (including preprocessing) with in-process Z3 on the
  original parsed assertions; binary fallbacks are excluded. The Glaurung recipe
  is single-worker and requires embedded-Z3 coverage for every file. A
  three-query micro smoke is 100% decided/agreed with zero errors/replay failures
  and validates only the plumbing; the real capture still gates any optimization
  conclusion and GQ10 adoption.
- **2026-07-13 — all ten Glaurung QF_BV performance items are explicit in
  PLAN/STATUS as GQ1--GQ10.** The client lane now orders real-query capture and
  cold layer attribution before cheap simplification, coercion cancellation,
  relevant-bit reduction, AIG/CNF construction, or SAT tuning; it separately
  tracks delta-only warm entry, duplicate/prefix reuse, an automatic published
  preprocessing policy, and the versioned real-lifter regression tier. The
  external SMT-LIB capture remains the honest GQ1/GQ10 blocker; no
  synthetic-only timing closes an item.
- **2026-07-13 — ADR-0140 accepts kernel-checked vacuous BV existential
  prefixes.** `issue2031-bv-var-elim` now closes through genuine nested
  `Exists.rec`, exact typed universal application, and computational AIG
  reduction. The exact audit is 50/54 dominant and Lean UNSAT 14/18 with all 54
  decisions checked/certified and zero mismatch/error/timeout.
- **2026-07-13 — ADR-0139 accepts kernel-checked BV universal
  counterexamples.** `qbv-simp` now closes through a genuine typed source
  application and evaluated-AIG refutation; exact audit is 49/54 dominant and
  Lean UNSAT 13/18 with 54/54 checked/certified and zero mismatch/error/timeout.
- **2026-07-13 — ADR-0138 accepts kernel-checked negated BV existential
  witnesses.** Added a source-bound reconstruction fragment, genuine typed
  existential introduction, logical and computational AIG body proofs, and
  context-safe DAG-linear kernel caches. All three ADR-0126 public rows pass the
  12.43-second bounded release gate; refreshed audit is 48/54 dominant and Lean
  UNSAT 12/18 with 54/54 checked/certified and zero mismatch/error/timeout.
- **2026-07-13 — ADR-0137 accepts DAG-linear Lean module export.** Exact
  expression reachability, uncapped repeated sharing, bounded single-use closed
  chunks, and scoped declaration aliases replace the tree-expanding corpus path.
  The guarded `psyco-107-bv` release reconstruction passes in 102--107 s; the
  timed run peaks at 2,697,384 KiB max RSS. Refreshed artifacts are 54/54 decided and
  evidence-certified/rechecked, 45/54 dominant, Lean UNSAT 9/18, DISAGREE=0,
  with zero errors, replay failures, audit errors, or timeouts.
- **2026-07-13 — ADR-0136 accepts the QF_BV client integration and benchmark
  boundary.** Added explicit unsigned width coercion, precise builder convention
  docs, a `Value` re-export, command-independent SMT-LIB model access, a
  dependency-firewalled minimal QF_BV feature, warm config-driven preprocessing,
  extract-through-bitwise/ITE rewrites, per-worker `Send` guidance, and a
  decided-rate/error benchmark integrity gate. Focused structural measurement
  removes most discarded AIG gates on an 8-bit slice of a 64-bit operation;
  exhaustive evaluator and Z3 differential routes preserve denotation. The
  reproducible Glaurung recipe requires an external query capture and therefore
  carries no unmeasured parity claim.
- **2026-07-13 — ADR-0134 accepts checked query-scoped QF_BV universal
  instances.** Added exact query/source binding, complete typed instance
  regeneration, QF_BV DRAT/LRAT replay, multi-instance and adversarial tamper
  tests, 32 direct-Z3 comparisons, and fresh corpus/dominance measurement for
  `psyco-107-bv`. The public quantified-BV slice is now 54/54 decided and
  evidence-certified/rechecked with no disagreements, errors, replay failures,
  or unsupported rows. The first workspace-level audit caught and fixed the
  missing `audit_dominance` evidence label before landing; the complete
  `just check` gate passes.
- **2026-07-12 — ADR-0133 accepts checked residual-QF_BV free-Boolean models.**
  Added bounded counterexample-instance refinement, exact source residual
  reconstruction, DRAT/LRAT replay, admission/cap/tamper tests, 32 direct-Z3
  comparisons, and fresh corpus/dominance measurement for `psyco-001-bv`.
  Installed the missing system Z3 development library needed by the release
  comparison harness. The complete workspace `just check` passes, including
  strict Clippy, all tests, warning-denied rustdoc, foundational resources,
  generated documentation checks, and link validation.
- **2026-07-12 — ADR-0132 accepts checked zero-product quantified-BV models.**
  Added exact direct-signed-division-to-zero replay, binder-product
  annihilation, bounded QF_BV candidate generation, 32 direct-Z3 comparisons,
  and refreshed corpus/dominance artifacts for `gn-wrong-091018`; the complete
  workspace `just check` passes.
- **2026-07-12 — ADR-0131 accepts checked signed-interval quantified-BV models.**
  Added exact ground replay, nonempty signed interval containment, bounded QF_BV
  candidate generation, 32 direct-Z3 comparisons, and refreshed
  corpus/dominance artifacts for `intersection-example-onelane`; the complete
  workspace `just check` passes.
- **2026-07-12 — ADR-0130 accepts checked affine-LSB quantified-BV models.**
  Added complete free-BV source certificates, exact universal parity checking,
  complete negated-universal witness replay, bounded search, 64 direct-Z3
  comparisons, corpus/dominance artifacts, and compact lazy certificate storage
  in `Model`; the complete workspace `just check` passes.
- **2026-07-12 — ADR-0129 accepts checked paired-existential witness transfer.**
  Added source-bound alpha replay, per-conjunct `QF_BV` or signed no-wrap
  justifications, evidence/taxonomy wiring, 128 generated Z3 comparisons, and
  complete corpus/dominance measurement. The negative sweep also repaired
  linear-depth exact quantifier expansion and AC canonical rebuilding.
- **2026-07-12 — quantified-stack recovery audit completed.** Preserved the raw
  worktree, removed unchecked verdict shortcuts, restored source-bound evidence
  admission, added bounded tuple-join/Lean/NRA failure paths, repaired a stale
  word-fallback test, and split the quantified-UFLIA differential into a bounded
  default smoke test plus an explicit full campaign. The full 2,000-instance
  campaign passed with 1,052 agreements, 800 replayed SAT models, 297 UNSAT,
  zero disagreement, and zero Axeyum errors. Rebased onto the nested-array guard
  registration from `main`; focused warm array/UF matrices remain green.
- **2026-07-11 — ADR-0111 accepts shared incremental e-matching state.** Added
  `EGraph::ematch_many`, one round-local class/application index, interned
  recursive trigger patterns, and a retained solver session that extends only
  newly appended ground assertions and canonicalizes disequalities after
  merges. The 32-quantifier/256-term target preserves 8,192 exact tuples and
  improves release median matching 17.9x; a two-round retained chain replays
  UNSAT. Public quantified-BV decisions are identical and quantified LIA stays
  12/12. E-graph 27/27, solver lib 834/834, evidence 69/69, bench 7/7,
  bounded-instance, MBQI/evidence, direct-Z3 fuzz, and workspace Clippy pass.
  Warning-denied rustdoc, links, formatting/diff, generated matrices, and
  foundational resources pass.
- **2026-07-11 — ADR-0110 accepts justified lazy quantifier-clause
  scheduling.** Reused the congruence-closed matching bridge to classify
  equality/disequality clauses from recorded ground units, suppress true
  instances, and globally prioritize all-false/unit-like complete source
  instances before unresolved fallback. A 256-match stress target reduces the
  active batch to one and improves optimized median end-to-end time 40.4%; the
  selected term remains in the complete public witness set and independently
  refutes with the original ground assertions. The 54-row quantified-BV slice
  is decision-identical to baseline and quantified LIA remains 12/12. Solver
  lib 833/833, e-matching, bounded-instance, evidence/MBQI, quantified-BV Z3
  differential, Clippy, rustdoc, links, formatting/diff, generated matrices,
  and foundational-resource gates pass. The long 2,000-case quantified-UFLIA
  debug fuzz was stopped at 15 minutes and is not claimed.
- **2026-07-11 — ADR-0109 accepts binder-safe closed sharing for Lean export.**
  Added opt-in compact module renderers with saturated DAG occurrence counts,
  fixed size/share caps, child-before-parent deterministic definitions, and
  hard rejection of open/fvar-dependent candidates. ADR-0108 uses the compact
  path plus a real emitted `Bool` inductive. Its public artifact falls
  151,845,067→2,682,977 bytes and reconstruction 17.74→10.75 seconds; the audit
  remains 12/12 dominant and 8/8 Lean UNSAT with zero failures or trust holes.
  Renderer tests, the explicit release corpus regression, Lean kernel 154/154,
  solver lib 830/830, evidence 69/69, bench 7/7, matrices, workspace Clippy,
  rustdoc, links, formatting/diff, and foundational resources pass. No external
  Lean binary is available, so source acceptance remains explicitly unverified.
- **2026-07-11 — ADR-0108 accepts checked counterexample covers for quantified
  UNSAT.** Added the 256-case bounded source certificate/checker, integrated
  cover-producing Boolean-model search, zero-trust evidence, and
  `ProofFragment::QuantifiedCounterexampleCover`. The Lean route flattens
  original conjunctions, retains one genuine positive universal leaf, applies
  carried Bool/Int witnesses, proves signed ground arithmetic/Boolean facts,
  and closes a 100,000-node-capped excluded-middle tree. `006-cbqi-ite` now
  decides with 119 cases and maximum cube width 6. Fresh audit is 12/12
  certified/checked/dominant and 8/8 Lean UNSAT, with zero mismatches, errors,
  timeouts, replay failures, or trust holes. Focused default/all-feature tests
  pass 5 + 1 explicit release validation; solver lib 830/830, evidence 69/69,
  bench 7/7, capability/support 2/2 and 12/12, workspace Clippy, rustdoc, links,
  formatting/diff, and foundational resources pass. ADR-0109 subsequently
  closes the initial 152 MB proof-serialization boundary.
- **2026-07-11 — ADR-0107 accepts checked Boolean-guard quantified SAT
  models.** Added deterministic free-Boolean candidate search and an
  arena-stable certificate that canonical model replay checks against untouched
  assertions. Positive universal closure uses bounded structural evaluation or
  exact integer-`ite` lifting plus source-bound LIA-DPLL theory cores; closures
  above the enumeration threshold carry source-matched DIMACS/DRAT. Both SAT
  residue rows now replay, moving quantified LIA to 11/12 with DISAGREE=0. The
  audit checks/certifies 11/11, kernel-checks UNSAT 7/7, and records 11/11
  dominant candidates with no mismatch, error, timeout, or trust hole. Focused
  default/all-feature integration 6/6, solver lib 830/830, evidence 69/69,
  bench 7/7, capability/support goldens 2/2 and 12/12, workspace Clippy,
  warning-denied rustdoc, links, formatting/diff, and 137-concept/174-pack
  foundational resources pass. `006-cbqi-ite` remains the sole row; no external
  Lean or whole-workspace aggregate is claimed.
- **2026-07-11 — ADR-0106 accepts single-pivot equality partitions to Lean.**
  Added `IntPrelude::eq_em`, exact theorem-type tests, the public ADR-0101
  certificate-to-module route, and `ProofFragment::SinglePivotEqualityPartition`.
  The proof retains original Bool/Int quantifiers and recursively handles
  connectives plus exact guarded `ite`; arbitrary witnesses split through
  `Bool.rec` or integer equality decidability. Finite evaluation is only
  untrusted guidance. Target/controls/tamper/multi-constant/arithmetic-boundary
  tests pass 5/5. Fresh audit is checked/certified 9/9, Lean UNSAT 7/7, dominant
  9/9, with zero mismatches/errors/timeouts/trust holes. Integer prelude 7/7,
  solver lib 829/829, evidence 69/69, bench 7/7, capability/support goldens 2/2
  and 12/12, workspace Clippy, warning-denied rustdoc, links, formatting/diff,
  and 137-concept/174-pack foundational resources pass. The division remains
  9/12; no external Lean or whole-workspace aggregate is claimed.
- **2026-07-11 — ADR-0105 accepts affine-growth quantifiers to Lean.** Added a
  public full-class ADR-0097 certificate-to-module route and
  `ProofFragment::IntAffineGrowth`. The proof models integer `ite` by exact
  guarded branch implications, reuses ADR-0104 decomposition, derives two
  positive-slope comparisons, and closes their pivot equalities constructively
  through strict consecutiveness. No classical, arithmetic, query-specific, or
  refuter axiom is added. Target/signed-swapped/tamper/near-miss tests pass 4/4;
  fresh audit is checked/certified 9/9, Lean UNSAT 6/7, dominant 8/9, with zero
  mismatches/errors/timeouts/trust holes. Solver lib 829/829, evidence 69/69,
  bench 7/7, capability/support goldens 2/2 and 12/12, workspace Clippy,
  warning-denied rustdoc, links, formatting/diff, and 137-concept/174-pack
  foundational resources pass. Finite equality partition is the sole current
  proof gap; the known Sturm nontermination still prevents a whole-workspace
  aggregate claim.
- **2026-07-11 — ADR-0104 accepts Euclidean decomposition and residue proofs.**
  Added `IntPrelude::euclidean_decomposition`, an explicit trusted theorem of
  standard integers with no div/mod symbols, and a public certificate-to-Lean
  route for canonical ADR-0095 clock formulas. The route applies the original
  universal to existential quotient/remainder witnesses and closes all three
  branches with kernel-checked equality/order terms. Exact prelude type, both
  corpus rows/router, tamper, and satisfiable weakened-bound tests pass. Fresh
  audit is checked/certified 9/9, Lean UNSAT 5/7, dominant 7/9, with zero
  mismatches/errors/timeouts/trust holes. External Lean cross-check was not run
  because no `lean` binary is installed. Remaining proof debt is affine growth
  and finite equality partition. Focused all-feature reconstruction 3/3,
  integer prelude 6/6, solver lib 829/829, evidence 69/69, bench 7/7,
  capability/support goldens 2/2 and 12/12, workspace Clippy, warning-denied
  rustdoc, links, formatting/diff, and 137-concept/174-pack foundational
  resources pass; the known Sturm nontermination still prevents a
  whole-workspace aggregate claim.
- **2026-07-11 — ADR-0103 accepts nested-XOR quantifiers to Lean.** Added a
  public certificate-to-module route for the complete signed/swapped ADR-0099
  class. It uses two outer and one nested universal application, classical Iff
  reasoning, and existing integer normalization/order, with no theorem-specific
  refuter or new arithmetic axiom. Target/signed-swapped/tamper tests pass 3/3;
  per-stage kernel gates caught and closed an open-de-Bruijn and signed-literal
  representation defect. Fresh audit is checked/certified 9/9, Lean UNSAT 3/7,
  dominant 5/9, and has zero mismatches/errors/timeouts/trust holes. Solver lib
  829/829, evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  workspace Clippy, warning-denied rustdoc, formatting/diff, links, and
  137-concept/174-pack foundational resources all pass. The known pre-existing
  Sturm nontermination still prevents a whole-workspace aggregate claim.
- **2026-07-11 — ADR-0102 accepts closed-universal counterexamples to Lean.**
  Added a public certificate-to-module proof route for the ADR-0100 Int-equality
  slice. It rechecks the original-body certificate, represents the asserted
  universal as dependent products over the Int/Bool preludes, applies its typed
  witnesses, and closes by kernel-checked integer normalization/order. Both
  `ARI176e1` and `issue5279-nqe` reconstruct without a theorem-specific refuter
  axiom; tampered evidence is rejected. The fresh nine-decision audit is
  checked/certified 9/9, Lean UNSAT 2/7, and dominant 4/9, with no mismatches,
  errors, timeouts, or trust holes. Focused all-feature tests pass 3/3; real-Lean
  cross-check was skipped because the binary is unavailable. Solver lib 829/829,
  evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  workspace Clippy, warning-denied rustdoc, formatting/diff, links, and
  137-concept/174-pack foundational resources all pass. The known pre-existing
  Sturm nontermination still prevents a whole-workspace aggregate claim.
- **2026-07-11 — ADR-0101 accepts checked finite equality-partition
  quantifiers.** Added independent expansion-search and recursive original-IR
  checker implementations plus `UnsatEqualityPartition` evidence. The exact
  quotient closes `cbqi-sdlx-fixpoint-3-dd` and moves quantified LIA 8→9/12;
  all nine decisions are certified/rechecked with zero trust holes and
  DISAGREE=0. Verification: focused/static-Z3 6/6, solver lib 829/829,
  evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12,
  all-feature workspace Clippy, warning-denied rustdoc, formatting/diff, links,
  and 137-concept/174-pack foundational resources. The pre-existing Sturm
  nontermination remains isolated; no whole-workspace aggregate is claimed.
- **2026-07-11 — ADR-0100 accepts evaluator-replayed closed-universal
  counterexamples.** Added a generic certificate with one original-binder typed
  value per scalar universal binder and an independent checker that admits only
  a closed quantifier-free body and evaluates it to `Bool(false)`. The untrusted
  producer uses fresh constants and QF model search, then self-checks before
  publishing. `ARI176e1` and `issue5279-nqe` move from bare UNSAT to certified,
  zero-trust evidence. Five focused all-feature tests include a 64-UNSAT/
  64-valid static-Z3 sweep. Release corpus remains 8/12 with DISAGREE=0; audit
  is checked/certified 8/8, Lean UNSAT 0/6, and has no mismatches/errors/timeouts.
  Verification: solver lib 829/829, evidence 69/69, focused certificate 5/5,
  bench 7/7, capability/support goldens 2/2 and 12/12, all-feature workspace
  Clippy, warning-denied rustdoc, formatting/diff, links, and 137-concept/
  174-pack foundational resources. The pre-existing Sturm nontermination still
  prevents claiming a whole-workspace aggregate.
- **2026-07-11 — ADR-0099 accepts checked nested-XOR quantifier evidence.**
  Added one exact hierarchical-instantiation search route and a separately
  implemented `IntNestedXorRefutationCertificate` checker. `issue4433-nqe`
  now decides in about 0.1 ms with `int-nested-xor-unsat` evidence and zero
  trust steps. Four focused evidence tests, two qinst tests, and a 64-positive/
  64-negative static-Z3 sweep pass. Release corpus is 8/12 (sat 2, unsat 6,
  unknown 0, unsupported 4), DISAGREE=0, errors/replay failures 0. Audit is
  checked 8/8, certified 6/8, dominant candidates 2, Lean UNSAT 0/6, with no
  mismatches/errors/timeouts. Verification: solver lib 829/829, evidence 69/69,
  nested-XOR evidence 4/4, qinst focused 2/2 plus the 900-seed bounded soundness
  sweep, bench 7/7, capability/support goldens 2/2 and 12/12, all-feature
  workspace Clippy, warning-denied rustdoc, formatting, links, and
  137-concept/174-pack foundational resources. The full workspace aggregate was
  not repeated because the pre-existing Sturm nontermination is already
  isolated above; no broader pass is claimed. Next: checked certificates for
  bare UNSAT rows `ARI176e1` and `issue5279-nqe`.
- **2026-07-11 — ADR-0098 accepts guarded unit-gap Skolem SAT.** Added sound
  positive-`or` nested-existential extraction for untrusted search and a
  separate exact `Int`/`Real` original-assertion checker. Replaced clone-local
  witness `TermId`s with owned affine recipes over original-arena atoms after
  the release harness exposed replay against an untouched arena. Ten focused
  certificate tests and the existing ten prenex witness tests pass; the
  static-Z3 differential covers 64 positives and 32 integer missing-margin
  negatives. Release corpus is 7/12 (sat 2, unsat 5, unknown 1, unsupported 4),
  DISAGREE=0, errors/replay failures 0. Audit is checked 7/7, certified 5/7,
  dominant candidates 2, Lean UNSAT 0/5, with no mismatches/errors/timeouts.
  Verification: solver lib 827/827, certificate 10/10, prenex witness 10/10,
  evidence 69/69 plus focused 4+3, bench 7/7, capability/support goldens 2/2
  and 12/12, all-feature workspace Clippy, warning-denied rustdoc, formatting,
  links, and 137-concept/174-pack foundational resources. The full workspace
  aggregate was not repeated because the pre-existing Sturm nontermination is
  already isolated above; no broader pass is claimed. Next: `issue4433-nqe`.
- **2026-07-11 — ADR-0097 lands checked affine-growth CEGQI and closes a
  cartesian-instantiation stack overflow.** The P2.6 search matcher accepts only
  `forall xs. not(c*x - ite(x=p,a,b) >= t)` with positive constant `c` and
  binder-free parameters. It instantiates `x` at
  `div(b+t,c)+1` and its successor; both clear the else-branch threshold and at
  most one equals `p`, so the ordinary QF refutation transfers to the original
  universal. `IntAffineGrowthRefutationCertificate` independently re-matches
  the complete original theorem, and `Evidence::UnsatIntAffineGrowth` rechecks
  it with zero trust steps. Five integration tests include tampering, a
  satisfiable binder-dependent near miss, fallback termination, and a 64-case
  positive plus 64-case negative statically linked Z3 sweep at DISAGREE=0. The
  near-miss sweep exposed 3,125 repeated instances from five binders: legacy
  trigger expansion now deduplicates interned instances and folds a balanced
  conjunction, reducing the regression from a stack overflow to a shallow,
  prompt `Unknown`. Fresh release corpus: 6/12 (sat 1, unsat 5), unknown 2,
  unsupported 4, DISAGREE=0, errors/replay failures 0; `repair-const-nterm`
  solves in about 1.3 ms. Six-decision audit: certified 4/6, checked 6/6,
  Lean UNSAT 0/5, one dominant candidate, no mismatches/errors/timeouts. Two
  bare UNSAT rows still prevent a division-level Pareto claim. Verification:
  rewrite lib 93/93, solver lib 827/827, evidence 69/69 plus focused 5+3+5,
  900-seed qinst soundness, bench 7/7, strict all-feature workspace Clippy,
  warning-denied rustdoc, formatting, links, generated matrices, and
  137-concept/174-pack foundational resources are clean. This checkpoint handed
  off `sygus-infer-nested`, now completed by ADR-0098 above.
- **2026-07-11 — ADR-0096 lands checked infinite-domain Skolem SAT.** Added
  `QuantifiedSkolemSatCertificate` as a deterministic `Model` payload and
  `check_model` as the canonical SAT replay front door. The checker independently
  re-matches the exact `forall* exists` prefix, binder IDs/sorts, and witness
  vocabulary; substitutes in a cloned arena; and proves only Boolean combinations
  of affine `Int`/`Real` tautologies or syntactic reflexivity. It never calls the
  witness search or broad solver. The existing affine witness suite now requires
  replay, and five new tests cover the real `issue4849-nqe` identity witness,
  `Evidence::Sat` recheck, tampered/foreign/stale/extraneous certificates,
  binder-ID reuse, and a non-reflexive near miss. Fresh release measurement:
  5/12 (sat 1, unsat 4), unknown 3,
  unsupported 4, DISAGREE=0, errors/replay failures 0. Five-decision audit:
  certified 3/5, checked 5/5, one `quantified-skolem-sat` dominant candidate,
  Lean UNSAT 0/4, no mismatches/errors/timeouts; no division-level dominance
  claim. The cold certificate payload uses a boxed slice, keeping ordinary
  `Model` overhead pointer-sized. Strict all-target/all-feature workspace Clippy,
  warning-denied rustdoc, formatting, links, 137-concept/174-pack foundational
  resources, generated capability/support matrices, focused certificate tests,
  and the benchmark harness are clean. The serialized aggregate limitation is
  recorded under Current focus. This checkpoint handed off
  `repair-const-nterm`, now completed by ADR-0097 above.
- **2026-07-11 — ADR-0095 certifies Euclidean-residue quantified UNSAT.** Added
  `quant_residue_cert`, an independent small checker that re-scans the original
  IR for exactly two nested `Int` binders, the three exact recomposition/range
  disjuncts, a positive constant modulus, distinct quotient/remainder symbols,
  and a binder-free dividend. `Evidence::UnsatIntEuclideanResidue` re-runs that
  checker and compares the regenerated typed certificate; it never calls the
  instantiation search and carries no trust steps. Positive modulus-3/10,
  weakened-bound/zero-modulus/extra-disjunct negatives, and a tampered modulus
  pass. The release solve benchmark remains 4/12, DISAGREE=0, errors/replay
  failures 0. A fresh four-decision dominance audit reports certificate 2/4,
  evidence check 4/4, trust holes 0, audit errors/timeouts 0, Lean 0/4; therefore
  no Pareto-dominance promotion. The eight-row residue census is now explicit in
  the corpus README. Verification: solver lib 823/823, evidence suite 69/69,
  new evidence integration 3/3, 900-seed qinst soundness, bench 7/7, workspace
  all-target/all-feature Clippy `-D warnings`, rustdoc `-D warnings`, foundational
  resources, docs links, formatting, and diff checks. Next: quantified-SAT
  evidence/model ADR, then `repair-const-nterm` affine-growth CEGQI with a checker.
- **2026-07-11 — P2.6 Euclidean residue CEGQI slice landed locally.** The
  e-graph quantifier fallback recognizes only the exact two-Int-binder residue
  partition, builds `mod`/`div` symbolic witnesses, substitutes them into the
  universal body, and transfers `unsat` only after `check_auto` refutes that
  genuine instance with the ground query. Exact 3/10-modulus positives and
  altered-bound/extra-disjunct negatives pass. Fresh quantified-LIA measurement:
  HEAD 2/12 → working tree 4/12, only `clock-3` and `clock-10` move, all four
  decisions match cvc5 regression statuses, no errors/replay failures; the
  remaining row is 4 incomplete + 4 unsupported. `scripts/fetch-references.sh`
  also repopulated all 26 configured reference clones. Verification:
  `cargo fmt --all`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p
  axeyum-solver qinst_egraph --lib -j1` (22/22); `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test
  qinst_bounded_instance_soundness -j1`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --lib -j1` (821/821); 12-file
  release benchmark at 10 s/job. Direct Z3 comparison could not run because
  this host has no linkable `libz3`; restore that oracle before regenerating the
  committed baseline/SCOREBOARD. A follow-on `b:=a` witness correctly validated
  `issue4849-nqe` but caused the benchmark's mandatory original-term model replay
  to fail on the infinite `Int` quantifier, so that code and the apparent fifth
  decision were removed. The missing quantified-sat model/evidence format is now
  an explicit research question. Aggregate validation also repaired the nested
  AUFBV equality-flag registration invariant described in Current focus, plus
  pre-existing strict gates: regex `canon`'s panic contract, checked
  `Instant::sub`, two unnecessary mutable test borrows, and one public-to-private
  rustdoc link. Final gates: `cargo fmt --all --check`; workspace all-target,
  all-feature Clippy with `-D warnings`; workspace all-feature rustdoc with
  `-D warnings`; foundational resources (137 concepts, 174 packs); docs links;
  qinst unit tests (22/22), 900-seed bounded-instance soundness, solver lib
  (821/821), `abv_lazy_ext` (10/10), concat membership (11/11), and regex
  derivative tests (13/13). The default workspace aggregate passed through the
  repaired AUFBV case and later stopped only on the pre-existing 5 ms
  `negated_le_goal_engages_sos_fast` timing assertion; that test and its full
  9-test file pass immediately in isolation. `just check` itself was unavailable
  because `just` is not installed. Next: checked evidence for this unsat route,
  quantified-sat replay design, then the next measured CEGQI/MBP shape.
- **2026-07-11 — regex canonicalization deadline guard landed.**
  Added `canon_within` as the pollable counterpart to regex similarity
  canonicalization and routed deadline-bounded membership solve/refute/witness
  paths through it before derivative exploration starts. Derivative residual
  canonicalization now polls too, so large concat/union/intersection spines and
  `Σ*`-enlarged product searches decline as `Unknown` instead of overshooting a
  tight deadline. The concat-membership replay helper now looks up existing
  public symbols and internal `!weq!` aliases without crossing arena namespaces.
  Verification: `cargo fmt --all`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh
  cargo test -p axeyum-strings --test regex_derivative --test
  membership_deadline -j1 -- --nocapture`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-strings -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver --test
  qf_s_concat_membership concat_membership_simple_sat_replays_at_seq_level -j1`;
  `git diff --check`. Next: #49 concat follow-up and the LenAbs length/LIA
  bridge.
- **2026-07-10 — memory-aware k-induction landed.**
  `prove_safety_k_induction_with_memory` extends unbounded k-induction to
  array/symbolic-memory transition systems by using
  `bounded_model_check_with_memory` for the base case and
  `IncrementalBvSolver::check_with_memory` for each inductive step. Unsupported
  shapes degrade to `SafetyOutcome::Unknown`; `Safe` remains unbounded but
  validation-backed until array-aware proof export exists. Focused coverage
  proves an inductive array property and returns the base-case replayed
  counterexample for a reachable symbolic-memory property. Verification:
  `cargo fmt --all`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p
  axeyum-solver --lib bmc::tests -j1`; `CARGO_BUILD_JOBS=2
  UPDATE_CAPABILITY_MATRIX=1 scripts/mem-run.sh cargo test -p axeyum-solver
  --test capabilities -j1`; `CARGO_BUILD_JOBS=2 UPDATE_SUPPORT_MATRIX=1
  scripts/mem-run.sh cargo test -p axeyum-solver --test support_matrix -j1`;
  `cargo fmt --all --check`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test
  -p axeyum-solver --test capabilities --test support_matrix -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo clippy -p axeyum-solver
  --all-targets --all-features -- -D warnings`; `./scripts/check-links.sh`;
  `git diff --check`. Next: certified memory k-induction, memory PDR/IMC,
  online array proofs, nested/extended arrays, and broader low-load aggregate
  timing.
- **2026-07-10 — retained warm nested array-valued UF parameters landed.**
  ADR-0094 admits supported array-valued `Apply` terms as finite-array keys to
  retained array-valued UF parents, both directly and inside supported
  structural key expressions. Direct nested keys encode by the inner
  application's private projection symbol; structural nested keys encode by
  replay-safe rewritten structural terms; private projection/owner symbols stay
  out of public array-key synthesis; and original replay remains the SAT gate.
  Verification: `cargo fmt --all`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh
  cargo test -p axeyum-solver --test warm_array_uf_parents -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver
  --all-features --test warm_array_uf_parents -j1`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_array_relation_flags -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh
  cargo test -p axeyum-solver --test warm_array_relations -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_structural_array_equality -j1`; `CARGO_BUILD_JOBS=2
  UPDATE_CAPABILITY_MATRIX=1 scripts/mem-run.sh cargo test -p axeyum-solver
  --test capabilities -j1`; `cargo fmt --all --check`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test capabilities -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo clippy -p axeyum-solver
  --all-targets --all-features -- -D warnings`; `./scripts/check-links.sh`;
  `git diff --check`. Next: memory BMC/k-induction, online array proofs,
  nested/extended arrays, and broader low-load aggregate timing.
- **2026-07-10 — retained warm structural array-valued UF parameters landed.**
  ADR-0093 admits supported `store`/`const-array`/array-ITE expressions as
  finite-array keys to retained array-valued UF parents. The warm path retains
  scalar dependencies inside keys, realizes private structural key owners
  against the original structural terms before full-value function projection,
  uses active equality classes or private ADR-0091 relation flags for key
  congruence, filters private owners/flags/witnesses, and replays originals.
  Verification: `cargo fmt --all --check`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test warm_array_uf_parents
  -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver
  --all-features --test warm_array_uf_parents -j1`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_array_relation_flags -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo
  test -p axeyum-solver --test warm_array_relations -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_structural_array_equality -j1`; `CARGO_BUILD_JOBS=2
  UPDATE_CAPABILITY_MATRIX=1 scripts/mem-run.sh cargo test -p axeyum-solver
  --test capabilities -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test
  -p axeyum-solver --test capabilities -j1`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo clippy -p axeyum-solver --all-targets
  --all-features -- -D warnings`; `./scripts/check-links.sh`; `git diff
  --check`. ADR-0094 subsequently lands supported nested application keys.
  Next: memory BMC/k-induction, online array proofs, nested/extended arrays, and
  broader low-load aggregate timing.
- **2026-07-10 — retained warm direct array-valued UF parameters landed.**
  ADR-0092 admits direct finite-array symbols as parameters to retained
  array-valued UF parents. Array-key congruence now uses active retained
  equality classes or private ADR-0091 relation flags; projection separates
  non-equal key classes with deterministic full array values before
  `FuncValue` construction, preserves user-visible select constraints, filters
  private guarded reads, and replays originals. Verification:
  `cargo fmt --all`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p
  axeyum-solver --test warm_array_uf_parents -j1`.
  ADR-0093 subsequently lands supported structural array-valued parameter
  expressions, and ADR-0094 lands supported nested application keys. Next:
  memory BMC/k-induction, online array proofs, nested/extended arrays, and
  broader low-load aggregate timing.
- **2026-07-10 — retained warm Boolean array relation flags landed.** ADR-0091
  admits supported array equality atoms nested under scalar Boolean structure
  through private candidate-sensitive flags. True flags add guarded paired-read
  equality observations and participate in owner merging/structural realization
  only when candidate-true; false flags add one guarded private diff witness.
  Projection filters private flags/witnesses/owners and replay gates SAT.
  Verification: `cargo fmt --all --check`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_array_relation_flags -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo
  test -p axeyum-solver --test warm_structural_array_equality -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_array_relations -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test
  -p axeyum-solver --test warm_array_uf_parents -j1`.
  ADR-0092 subsequently lands direct array-valued UF parameters, and ADR-0093
  lands supported structural array-valued parameter expressions. Next: nested
  array-valued application keys, memory BMC/k-induction, online array proofs,
  and broader low-load aggregate timing.
- **2026-07-10 — retained warm structural array equality accepted.** ADR-0090
  was already implemented in `e90ebe55`; this session verified the focused
  default gates and brought PLAN/STATUS/ADR/capability ledgers into sync. The
  warm path admits top-level positive equality over supported structural
  store/constant/array-ITE parents through private constructor owners, bounded
  shared-index observations, class-aware fixed-point realization, filtering, and
  original replay. Verification: `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo
  test -p axeyum-solver --test warm_structural_array_equality -j1`;
  `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test -p axeyum-solver --test
  warm_array_relations -j1`; `CARGO_BUILD_JOBS=2 scripts/mem-run.sh cargo test
  -p axeyum-solver --test warm_array_uf_parents -j1`; `CARGO_BUILD_JOBS=2
  scripts/mem-run.sh cargo test -p axeyum-solver --all-features --test
  warm_structural_array_equality -j1`.
  ADR-0091 subsequently lands Boolean relation flags and ADR-0092 subsequently
  lands direct array-valued UF parameters; structural array-valued parameter
  expressions, memory BMC/k-induction, online array proofs, and broader
  low-load aggregate timing remain.
- **2026-07-10 — retained warm array relations landed.** ADR-0089 merges
  direct/application projection owners for positive equality before function
  construction and reduces top-level structural disequality to one private diff
  index plus two exact retained reads. Equality chains over prior reads, no-read
  function results, store/constant/ITE witnesses, Bool/BV256, scope/core/filter,
  replay, exact depth, and unsupported positive-structural/nested-Boolean
  controls pass. Eight default/nine all-feature gates add 192 clean warm/
  `check_auto`/Z3 comparisons; 816 solver units, 77 symexec tests, ADR-0088
  regressions, complete EVM/fuzz, strict clippy, rustdoc, resources/links, and
  exact-SHA gates pass. EVM has no whole-array relation root, so no timing delta
  is claimed. ADR-0089 accepted; `d891c901`/`70c8a15c` pushed.
- **2026-07-10 — retained warm array-valued UF parents landed.** ADR-0088
  preserves scalar-keyed array-result applications as private warm arrays,
  constrains observed reads by conditional argument/index congruence, merges
  split observations by concrete function key, projects full-value results,
  hides private owners, and replays originals. Store/ITE composition, nested
  scalar UFs, Bool/BV256 values, scope/core behavior, unsupported deferral, and
  exact 64/65-parent admission pass. The 64-seed warm/`check_auto`/Z3 matrix is
  192/192 clean; 816 solver units, 77 symexec tests, canonical array-result
  integration, complete EVM/fuzz, strict clippy, rustdoc, resources/links, and
  exact-SHA gates pass. No EVM timing delta is claimed because its corpus has no
  array-result UF. ADR-0088 accepted; `41019413`/`f2bb16ab` pushed.
- **2026-07-10 — candidate-triggered retained warm ROW landed.** ADR-0087 keeps
  one exact bounded transitive scalar summary per observed structural read as
  dormant metadata; candidate-false summaries become permanent roots in the
  same CNF/SAT instance under one shared deadline. Zero-activation replayed
  misses, nested one-round closure, push/pop, inactive pending metadata,
  one-shot core/reuse, Bool/ITE/constant reads, timeout, and exact cap gates pass.
  The 64-seed matrix remains 192/192 clean; all 816 solver units, 77 symexec
  tests, complete EVM/fuzz gates, strict clippy, rustdoc, resources/links, and
  exact-SHA pass. Release EVM remains DISAGREE=0 and depth 32 improves 2.75x,
  30.933→11.257 ms; ITE-fold still wins at 0.405 ms. ADR-0087 accepted;
  `c777e756`/`3977f78b` pushed.
- **2026-07-10 — retained warm structural array reads landed.** ADR-0086 gives
  observed store/constant/ITE reads exact private definitions installed once in
  the incremental CNF; scoped roots retract, leaf-only projection plus original
  replay gates SAT, and exact 512-node/256-depth limits defer larger roots. The
  64-seed matrix adds 192 warm/check-auto/Z3 comparisons with zero disagreement;
  816 solver units, 77 symexec tests, complete EVM/fuzz gates, strict clippy, and
  exact-SHA pass. EVM remains DISAGREE=0, but depth 32 measures 0.368 ms ITE-fold
  vs 30.933 ms retained warm definitions, making candidate-triggered activation
  the explicit next performance step. ADR-0086 accepted; `4caed2ec`/`47c152ec`
  pushed.
- **2026-07-10 — bounded structural array-class equations landed.** Exact pre-
  search ITE equality decomposition exposes selected branch equality to the
  e-graph; bounded fixed-point realization assigns true store/ITE/constant
  equations into leaf arrays only when every observed read remains unchanged.
  Array-result owners and array-valued keys compose before mandatory replay.
  The 16-shape matrix adds 192 direct/front-door/Z3 comparisons with zero
  disagreements; SMT-LIB, Bool/Int, cap, deadline, all 816 solver tests, existing
  AUFBV/array-result matrices, strict clippy, and exact-SHA gates pass. ADR-0085
  accepted; design/implementation `e47da7a1`/`da957695` pushed.
- **2026-07-10 — array-valued UF results landed on canonical AUFBV.** IR,
  evaluator, `FuncValue`, SMT-LIB, and abstraction now admit finite-scalar array
  results; eager Ackermann elimination declines cleanly. Original applications
  remain e-graph parents while fresh result arrays own projected reads. Final
  classes union congruent application observations before array-first/function-
  second table construction and original replay. Six focused mechanism tests,
  288 analytic/front-door/Z3 comparisons, all 815 solver tests, the existing
  AUFBV fuzz, strict clippy, and exact-SHA push gates pass. ADR-0084 accepted;
  design/implementation `b1bc1836`/`e944f7c1` pushed.
- **2026-07-10 — deadline-aware BV lowering landed.** `axeyum-bv` now exposes
  portable absolute-deadline one-shot and incremental lowering, with polling in
  DAG traversal and superlinear/wide circuit loops. The SAT-BV and canonical
  UFBV/AUFBV boundaries return classified timeout `Unknown`s; canonical BV
  reuses the cumulative pre-lowering clause estimate and 64M default ceiling.
  Exact regressions cover admitted scalar/AUFBV division cancellation and the
  public five-divider refusal. A fresh 1 s cvc5-regress-clean run is 7/9 SAT,
  one encoding-budget unknown, one unsupported, DISAGREE=0, replay failures=0;
  the former 437.5 s row returns in 1 ms. Focused suites and the exact-SHA
  pre-push gate pass. ADR-0083; `85e007b2`.
- **2026-07-10 — bounded dynamic interface atoms landed.** `CdclT` now maps
  appended SAT variables explicitly to aligned theory atoms, including atoms
  created after Tseitin auxiliaries. `EufTheory` grows equality metadata over
  pre-observed sides; exact BV grows terms and atom state in its owned arena.
  Candidate-violated UF, explanation-guarded parent-select, and bounded array-
  equality/extensionality interfaces now refine inside one retained search.
  Former two/three-round mechanism controls pin one round; backtracking, exact-
  cap, no-cross-product, replay, eager/front-door, and Z3 gates pass. The new 384
  comparisons bring the clean array total to 2,304; all 809 solver tests, the 11-
  test differential binary, strict Clippy, and the exact-SHA pre-push gate pass.
  ADR-0082; `39cc92ce`.
- **2026-07-10 — dynamic in-search ROW insertion landed.** Each store site now
  reserves three local atoms dormant; a violated candidate inserts two
  permanent valid ROW clauses and resumes the same `CdclT` search with learned
  clauses, phase state, and activities retained. Hit/miss controls move from two
  outer rounds to one, nested sites refine inside one round, a replayable branch
  backtracks safely, UF-bearing indices reuse aligned e-graph atoms, and the
  exact shared interface cap is preserved. The new 384-comparison dynamic-ROW
  matrix brings the clean total to 1,920; all 807 solver tests, strict clippy,
  rustdoc, and the exact-SHA pre-push gate pass. ADR-0081; `07be0883`.
- **2026-07-10 — explanation-guarded store-parent scheduling landed.** Original
  store terms now join the same final-e-class select scheduler as base symbols;
  distinct parents retain equality-explanation guards and lazy ROW remains an
  independent candidate check. Same-parent, congruent-parent, branch,
  unrelated-parent, UF-index, and 80-parent scaling gates pass. The new 384-
  comparison structural eager/front-door/Z3 matrix brings the clean total to
  1,536; all 802 solver tests, strict clippy, rustdoc, and the exact-SHA pre-push
  gate pass. Host I/O wait remains 13-25%, so ADR-0078's 187/193 and 49/53 stay
  the comparable public baseline. ADR-0080.
- **2026-07-10 — finite Bool/BitVec array admission landed.** Canonical
  ABV/AUFBV now admits Bool or BitVec independently at index and element while
  preserving the wider fallback-routing flag. Generic mixed-component models
  replay; Int components still decline. Public `issue5925` changes unknown→UNSAT
  and `issue4240` unknown→SAT. The new 384-comparison analytic/front-door/Z3
  matrix brings the clean total to 1,152; all 797 solver tests and 12 route tests
  pass. The exact 1 s aggregate rerun was host-I/O-contaminated, so ADR-0078's
  187/193 and 49/53 remain the comparable baseline pending a low-load rerun.
  ADR-0079.
- **2026-07-10 — explanation-guarded parent-select scheduling landed.** Base
  reads now group by final live e-class and only candidate-violated cross-parent
  pairs materialize. E-graph explanation literals guard each persisted lemma,
  preserving soundness across Boolean branch changes. Direct-symbol equality
  preparation drops its query-index cross product; the 80-array/read gate replays
  in one round under the old site cap, while structural store equality retains
  its observation+ROW route. All 794 solver tests and 768 comparisons pass.
  Public QF_ABV/QF_AUFBV remain 187/193 and 49/53 at 84/206 ms, with zero
  disagreement or replay failure. ADR-0078.
- **2026-07-10 — array equality moved onto the canonical e-graph.** Abstract
  flags now retain their original array equality for live backtrackable EUF,
  superseding ADR-0076's compensating cross-diff queue. Transitive/self/store-UF
  conflicts and the former cap stress case refute in one round with no
  extensionality instances. True direct-symbol classes share one projected
  majority-default model; transitive disjoint-read SAT replays. All 790 solver
  tests and the strengthened 768-comparison matrix pass (456 equality-bearing).
  Public results remain QF_ABV 187/193 at 84 ms and QF_AUFBV 49/53 at 205 ms,
  DISAGREE=0/replay failures=0. ADR-0077.
- **2026-07-10 — candidate-triggered cross-array equality queue landed.** False
  equality obligations now move through new/delayed/applied state and add their
  diff index only to one deterministic candidate-true equality path. Transitive
  equality closes with two observations, disconnected SAT still replays,
  store/UF paths compose with ROW, and the stress gate declines at exactly 512.
  All 788 solver tests and 768 differential comparisons pass; 456 comparisons
  are equality-bearing. Public QF_ABV/QF_AUFBV results remain 187/193 and 49/53
  at 84/206 ms PAR-2 with zero disagreement/replay failure. ADR-0076 records the
  retained live-merge/class-model/proof boundary; ADR-0077 subsequently
  supersedes the queue after identifying the opaque flag/e-graph root cause.
- **2026-07-09 — array select congruence gained one portable proof artifact.**
  Direct equal-array/same-index read conflicts now emit literal `select` with
  `eq_reflexive`/`eq_congruent`/optional `symm`/resolution. Forward and reversed
  forms pass `check_alethe` and Carcara, a missing-antecedent mutation is
  rejected, evidence has no trust steps, and the real-Lean representative gate
  remains 67/67. ADR-0075 records that ROW and diff-witness proof logging remain.
- **2026-07-09 — deterministic majority-default array models landed.** Shared
  projection now votes over distinct observed indices, applies a stable
  smallest-value tie, and stores only non-default overrides for compact BV and
  generic arrays. Three focused model-policy tests and a 16-read end-to-end
  canonical model gate pass; the latter compresses to four overrides in one
  round with full replay. The 768 differential and public corpora remain clean,
  with decisions unchanged at QF_ABV 187/193 and QF_AUFBV 49/53. ADR-0074
  records the original-symbol boundary and retained e-graph-class/warm work.
- **2026-07-09 — candidate-guided array extensionality joined canonical CDCL(T).**
  Shared equality flags now receive bounded query/store observations and one diff
  witness; only candidate violations add congruence/witness instances. UF-bearing
  indices remain aligned, online probes use pristine arena clones, and original
  replay remains mandatory. Five mechanism tests, two isolation tests, and 768
  eager/front-door/Z3 comparisons pass; 384 comparisons were equality-bearing at
  this checkpoint (ADR-0076 later expands the clean matrix to 456).
  Public decisions remain QF_ABV 187/193 and QF_AUFBV 49/53 with zero
  disagreements/replay failures. ADR-0073 records the cross-atom/queue/model/proof
  boundary and the absence of a performance claim.
- **2026-07-09 — lazy ROW joined the canonical array bus.** Store reads now
  start as a relaxation and materialize exact guarded hit/miss axioms only after
  a candidate violation. UF-bearing metadata shares the existing dynamic
  function path; function-then-array replay remains mandatory. Focused hit/miss,
  UF-index, and zero-axiom store-chain gates plus all 768 differentials pass.
  Public 1 s decisions move QF_ABV 185→187/193 and QF_AUFBV 48→49/53 with zero
  disagreements/replay failures. ADR-0072 records the tight-cap regression and
  the remaining queue/extensionality/model boundary.
- **2026-07-09 — replay-guided array interfaces landed.** The new
  abstraction-only array boundary does not build eager select pairs; canonical
  rounds add only candidate violations and compose array→UF refinement with
  function-then-array projection/replay. Mechanism, cap, 768-case differential,
  focused array, and public QF_ABV/QF_AUFBV gates pass with DISAGREE=0 and zero
  replay failures. ADR-0071 records the bounded base-select scope and P2.2
  follow-up.
- **2026-07-09 — replay-guided dynamic UFBV interfaces landed.** Candidate
  models now materialize only violated same-function pairs around canonical
  `CdclT`; subset UNSAT and projected/replayed SAT preserve the trust boundary.
  One-pair, nested-fixpoint, zero-pair symbolic-table, materialized-cap,
  1,536-case differential, public 6/6, and full solver gates pass. ADR-0070
  records the median 3.12x `bug520` / 4.47x corpus-mean gains and bounded rebuild
  tradeoff.
- **2026-07-09 — exact ground-distinct UFBV pair pruning landed.** The canonical
  interface builder proves impossible congruence antecedents with cached ground
  evaluation before generating atoms or charging the admission cap. Equal
  denotations and unknown terms stay conservative. Mechanism/equal-value/cap
  controls, 1,536 differentials, public 6/6, replay, and full solver gates pass;
  the exact release A/B records the median 1.72x `bug520` win and variance.
  ADR-0069 records the proof boundary and dynamic-symbolic follow-up.
- **2026-07-09 — exact warm BV interface propagation landed.** The canonical
  UFBV theory now proves bounded interface consequences with same-CNF
  opposite-polarity probes and failed-frame reasons, then feeds them to
  `CdclT`/EUF. Mechanism, production telemetry, `bug520`, differential, and
  public-corpus gates pin both soundness and the exact 5-run ~2.3x row win.
  ADR-0068 records caps and the model-is-hint/UNSAT-is-proof boundary.
- **2026-07-09 — warm BV decision-frame conflict cores landed.** Online UFBV
  now maps failed persistent frame selectors from the existing SAT solve back
  to theory literals, omitting irrelevant levels without a second solve. The
  per-literal-selector prototype was measured and reverted as a regression;
  accepted frame cores are runtime-neutral on the six-row corpus. Incremental,
  symbolic-execution, UFBV differential, and public corpus gates remain clean.
  ADR-0067 amends ADR-0066's initial full-core policy.
- **2026-07-09 — canonical online QF_UFBV combination landed.** Bounded scalar
  UFBV now runs one `CdclT` trail over e-graph congruence and warm exact BV
  feasibility, connected by explicit argument/result interface equalities.
  Front-door routing, replayed function models, timeout/cap `Unknown`s, three
  512-case differential matrices, and public QF_UFBV 6/6 agreement are pinned.
  Eager Ackermann remains fallback and proof production. ADR-0066 records the
  accepted architecture; the measured result makes no speed claim.
- **2026-07-09 — true function abstraction split from eager Ackermann
  elimination.** Added `FunctionAbstraction`/`abstract_functions`, retained the
  full projection/replay contract, and migrated the shared lazy
  functional-consistency loop. Lazy UFBV/UFLIA no longer constructs the
  quadratic congruence set it intends to learn on demand; eager solving and
  certifying reductions are unchanged. ADR-0013 and P1.6 record the boundary.
- **2026-07-09 — LBD learned-clause reduction migrated into canonical `CdclT`.**
  Learned metadata stays aligned with stable clause slots; reductions preserve
  originals, glue, and all active reasons, then tombstone the worst eligible
  half deterministically. A forced-reduction PHP(7,6) test matches a never-delete
  baseline and pins reason safety plus deterministic fire. Current adapters,
  the full Z3 differential matrix, and UFLIA corpus probes remain clean; the long
  sweep is neutral at 425.90 s. This completes the planned VSIDS/phase/Luby/LBD
  migration, not P1.5 or performance parity; P1.6 BV combination is next.
- **2026-07-09 — deterministic Luby restarts migrated into canonical `CdclT`.**
  Restarts run only above level zero after the joint propagation fixpoint,
  backjump through the existing theory-pop path, and retain all learned/search
  state. The forced-restart gate proves fire, verdict invariance versus disabled
  restarts, deterministic trajectory, and zero residual theory depth; the Luby
  prefix is pinned. All current adapters, external-oracle fuzz gates, and UFLIA
  corpus results remain clean; the long sweep is neutral at 425.18 s. The LBD
  reduction follow-through is recorded above.
- **2026-07-09 — VSIDS and phase saving migrated into canonical `CdclT`.**
  Conflict analysis now bumps first-seen conflict variables with MiniSat-style
  decay/rescaling; branching uses highest activity with stable index ties; saved
  phases survive backtracking while untouched variables retain true-first
  behavior. Search order is the only contract change. Mechanism/adversarial
  gates, every current theory adapter, 8,000+ external-oracle fuzz cases, and the
  five-second UFLIA corpus remain sound and verdict-stable. The UFLIA oracle
  sweep is runtime-neutral (426.17 s before, 426.19 s after). ADR-0060 records
  Luby restart and LBD/clause-reduction migration as the next separate slices.
- **2026-07-09 — Combined UFLIA/UFLRA production search migrated to canonical
  `CdclT`.** The live combined theory adapters keep their interface-variable
  layout, structural clauses, asserted-only reasons, deadline, and replay-gated
  leaf reconstruction while the shared driver now owns Boolean search. The
  propagation diagnostic gates were moved off the enumerative fallback and onto
  the production path. UFLIA 31/31, UFLRA 21/21, four learned-lemma checks, the
  online/eager dispatch differential, and Z3 differential fuzz (2,500 integer +
  1,500 real cases) pass with zero disagreements. Curated 5 s UFLIA remains 6/6
  bounded and 0/2 overbound timeout, DISAGREE=0, replay failures=0. ADR-0060 and
  the Nelson-Oppen research question now record `CdclT` as the combination owner.
- **2026-07-09 — Pure QF_LIA/QF_LRA default probes migrated to generic
  `CdclT`.** LIA now uses the generic adapter as a bounded first probe; LRA gives
  it the full remaining deadline, treats timeout/resource admission as terminal,
  and retains the legacy mixed fallback for non-budget incompleteness. Added
  deadline-aware/memoized LRA theory construction, deadline propagation through
  combined UFLRA and Fourier–Motzkin reconstruction/elimination, per-row polling,
  linear-vs-NRA route admission, numeric-coefficient recognition, and the
  deterministic 1,024-atom resource cap. Route-pinning/default deadline tests and
  the cap regression landed. Curated 5 s raw/preprocessed A/B: LIA 6 sat / 4
  unsat / 1 unknown; LRA 6 sat / 3 unsat / 2 unknown; DISAGREE=0 and replay
  failures=0 throughout. LRA unknown rows: 5.250 s / 11.853 s before, 4.838 s /
  5.031 s after. ADR-0060 updated.
- **2026-07-09 — QF_UF online default-dispatch ratified through generic
  `CdclT`.** The `euf-online` front-door route now calls
  `check_qf_uf_online_cdclt` with caller `SolverConfig`, so pure QF_UF online
  solving is default-on by ADR-0055 criterion (2); offline EUF remains the
  fallback after online `unknown`. A new route-trace regression pins a
  Boolean-structured congruence refutation to `euf-online` under the default
  config. Focused gates passed: fmt check, `route_trace`, `cdclt_online`,
  `euf_egraph::tests`, the `qf_uf_differential_fuzz` target (0 tests), `cargo
  check -p axeyum-solver --tests`, clippy all-targets/all-features, and the
  three-file QF_UF regression bench smoke (3/3, DISAGREE=0,
  model_replay_failures=0).
- **2026-07-09 — Generic `CdclT` string theory propagation enabled for variable
  equality atoms.** `StringTheory::propagate` now emits sound whole-atom
  consequences for bare `Seq` variables: asserted equality classes force
  unassigned equalities true, and asserted disequalities are transported across
  those classes to force equalities false. Explanations cite only asserted
  trail literals; compound word-core facts remain conflict-only. New tests cover
  direct equality closure, disequality transport, and end-to-end `CdclT`
  propagation counting. Focused gates passed: fmt check, `string_theory::tests`,
  the online string integration bundle, typed QF_S online test build, and
  `cargo check -p axeyum-solver --tests`.
- **2026-07-09 — Generic `CdclT` LIA/LRA theory propagation enabled.**
  The arithmetic adapters on the shared P1.5 spine now forward the
  already-validated `LiaTheory::propagate` / `LraTheory::propagate`
  entailments instead of returning an empty propagation set. `CdclT` records an
  internal `theory_propagations` counter for tests, and new LIA/LRA unit gates
  prove both direct reasons (`x >= 1` entails `x > 0`) and end-to-end driver
  assignment through propagation. Focused gates passed: fmt check, LIA/LRA
  module tests, `cdclt_lia_online`/`cdclt_lra_online`, and
  `cargo check -p axeyum-solver --tests`.
- **2026-07-08 — Provable-security roadmap intake from
  [The Joy of Cryptography](https://joyofcryptography.com/).**
  Added a docs-only integration note:
  [docs/plan/provable-security-integration.md](docs/plan/provable-security-integration.md).
  The note maps game-based proofs into existing lanes: Track 5
  constant-time/protocol/transcript examples, Track 4 scenario packs,
  Track 3 game-hop evidence recipes, P2.10 finite-field demand, and the
  foundational-books decidability lens. Explicit non-goal: no production crypto,
  no random-oracle trusted core, no solver-priority reorder, and no bounded-SMT
  claim of computational security. Linked from
  [docs/plan/README.md](docs/plan/README.md) and
  [docs/curriculum/foundational-books/README.md](docs/curriculum/foundational-books/README.md).
- **2026-07-07 — Z3/cvc5 gap re-audit: new dated analysis
  (`docs/plan/gap-analysis-z3-cvc5-2026-07-07.md`) + PLAN.md leverage order
  superseded.** Grounded in the generated scoreboard (992/727≈73%,
  DISAGREE=0), the frontier ratchets, and direct code inspection with an
  independent second read. Three stale premises corrected in PLAN.md's gap
  section: online NO CDCL(T) is the first UF+arith route (eager Ackermann is
  the *fallback*); subsumption/BVE/vivification exist but are default-off
  (`backend.rs` `cnf_inprocessing`/`cnf_vivify`) — the Gap-1 first step is a
  measurement; the quantifier gap is the sat direction specifically (T2.6.5
  MBQI model-finding), not instantiation. Added Gap 7 (the dominance
  denominator): 100% Pareto dominance = decide%→100 per division **and**
  complete audits on all 35 rows (12 still unaudited) **and** trusted ledger
  → 0. Docs-only change; no solver code touched.
  routes into the regex-derivative core (#49, `7197da29`). QF_S 78→82.**
  The scout corrected the census (the "str.++ bound-cap" was a mis-diagnosis —
  raising the cap gains ~0 rows; the real gap is the membership fragment
  declining a `str.++` subject). Extension: `word_bool`'s `str.in_re` arm
  (`parse.rs`) now rewrites `(str.in_re (str.++ p…) R)` to `w∈R ∧ w=p…` with a
  fresh operand `w` (reusing the single-variable machinery), and the online route
  (`string_theory.rs`) witnesses each membership class, **pins** the witness as an
  extra word equation, and re-solves the augmented word system (a concat operand
  is witnessed over `R ∩ shape`, decomposing into its parts). **5 rows
  unsupported→sat** (issue2060/5510/5520/7677/4608), each agreeing with **z3 AND
  cvc5**. **SAT-SIDE slice — sound by construction:** every sat replays at the
  `Seq` level vs the original (concat + membership both true) through the ground
  evaluator + the independent reference matcher; concat *emptiness*/unsat is
  deferred (stays `unknown`, never a wrong verdict); single-var unsat unchanged
  (re-checked `refute_empty`). Also a deadline-poll robustness fix
  (`derivative_closure_within`). Independently re-validated: #44's
  `regex_reconstruct` 7/7 survived the shared-core edit, corpus green,
  `qf_s_concat_membership` 6/6 (Seq-level replay + never-wrongly-sat), --lib
  18/18, membership fuzz DISAGREE=0 vs z3 AND cvc5 (413/413 each), string+seq
  fuzzes DISAGREE=0. **Sliced off (follow-up):** concat-unsat via coarse-shape
  emptiness, the joint product-automaton search for loosely-constrained parts
  (norn-*), the trivial-length-atom skeleton pass, and a latent
  single-pathological-`canon` deadline edge.
- **2026-07-07 — Lean-parity: regex derivative-emptiness → kernel-checked Lean
  `False` (#44, `cd6783b9`).** A new fragment `regex_reconstruct.rs` (mirroring
  word/lex reconstruct): the emptiness certificate (finite derivative closure S —
  start∈S, closed under derivative, no nullable member ⇒ `L=∅`) is encoded as an
  automaton (`Q` state enum, `delta`/`accept`/`run` recursors) whose "never
  accepts" invariant is proved by `Str`-induction and contradicts an assumed
  membership → `Eq Bool false true` → `False` via the `Bool` discriminator. The
  FULL multi-state closure reconstructs (empty-language, intersection/inclusion/
  disjoint-char emptiness), **NO new kernel axioms** (the `Q` enum goes through the
  trusted `add_inductive` gate); every term is `infer`+`def_eq`-checked to the
  prelude `False` (the kernel IS the checker — a wrong cert declines). 7/7 tests
  incl. a NEGATIVE test (kernel rejects a reflexive-`Eq` discriminator).
  **Honest scope:** a kernel-checked NARROWING (trust rests on the `recheck_empty`
  derivative substrate, like the `certify_*` sub-cases), not a from-nothing
  faithful proof — a Lean `InRe` relation needs recursive-indexed inductives the
  kernel doesn't yet support (documented follow-up). Also NOT yet wired into the
  live evidence dispatcher (`reconstruct_regex_emptiness_to_lean_module` is
  pub+test-exercised; wiring into `produce_evidence` is a follow-up). Landed
  alongside the concurrent Track-5 lane's T5.3.1 (below) on the same push.
- **2026-07-06 — Track 5 / P5.3 T5.3.1 (`ac7494f0`): certificate-backed
  constant-time by self-composition.** The first kernel-obligation family, and
  the most differentiating — a hyperproperty no current Rust tool proves with
  independent evidence. The MIR reflector now records control-flow leakage
  (`switchInt` branch scrutinees; `reflect::mir::reflect_mir_params_with_leaks`,
  threaded through `exec_block`, existing value/panic paths untouched);
  `reflect::hyper::control_flow_ct_goal` reflects a function twice over
  shared-public / distinct-secret inputs and conjoins the pairwise equalities of
  the leaked branch decisions — Proved = control-flow constant-time, Disproved =
  a secret-dependent branch with a distinguishing witness. `constant_time.rs`
  (4 tests): a public-predicated fn is PROVED CT while its output is refuted
  secret-independent (the crisp distinction), a secret-predicated fn is REFUTED
  with a replay-checked witness, a branch-free fn is trivially CT. Honest scope:
  branch leakage only — memory-access index (cache-timing) leakage is the
  documented residual. Full sweep green (35 binaries, 219 tests); clippy +
  rustdoc `-D warnings` clean.

- **2026-07-07 — 10th review re-ranks the pivot; the FP fuzz GAP-closure finds +
  fixes a FOURTH soundness bug (FP signed-zero wrong-unsat).**
  - **10th review** (`6b5e33bf`): caught a load-bearing false premise — ADR-0058
    Phase B ("route DPLL cubes into the exact CAD") was ~90% OBE (the edge existed
    at `5ede57f4`; #43 landed the bignum coeffs). Rescoped ADR-0058 (Phase B done;
    remaining = Phase C/D, DE-PRIORITIZED below strings), fixed the decomposition
    §3 + STATUS stale premise, refreshed decide-rate ~68%→~73%. Ranked the next
    thrusts: close the soundness fuzz-GAPs first, then strings breadth (the
    dominant measured gap now: QF_SLIA 36%, QF_S 58%). Strings census (#49): the
    #1 decline is the ADR-0029 bound-cap (~52 rows), not an extended function.
  - (`b6cd2af6`) **#47 — closed the FP + RealDiv-0 differential-fuzz GAPs.** New
    `fp_differential_fuzz` (598/598 DISAGREE=0) + RealDiv-0 seeds in the lra/nra
    fuzzes (DISAGREE=0). The FP fuzz **surfaced a P0** (the session's 4th, and the
    100%-hit-rate held: every blind axis given sight found a wrong verdict).
  - (`bqxsnujic`) **#50 — the P0 fixed: FP `isNegative`/`isPositive` classify
    signed zeros by the SIGN BIT.** They were `sign ∧ ¬nan ∧ ¬zero`, so
    `(fp.isNegative -0)` was a wrong-**UNSAT** (Z3+cvc5: −0 IS negative, +0 IS
    positive). Fix: public builders `sign ∧ ¬nan` (include signed zeros); an
    internal `is_strictly_negative` preserves the one legit zero-excluding use
    (`sqrt(-0)=-0`). FP is parse-desugared so the builder is both solve+replay.
    Verified: fuzz DISAGREE=0 (predicates re-enabled), axeyum-fp 55/55 incl
    min/max ±0, carcara 76/76, corpus 0 DISAGREE, `--workspace --lib` 18/18.
- **2026-07-07 — the last cheap QF_NRA pickups: qf-nra-cvc5 27→32 (84%),
  equality-anchored decision + the DPLL→CAD edge.**
  - (`4d74b288`) **#43 — decomposition slices 4 + 7a + 7b.** Slice 4
    (`parse.rs`): a nullary `(define-fun c () Real …)` with an Int-literal body
    now coerces Int→Real (was a parse-fail decline) → `parser__real-numerals`
    sat. Slice 7a (`nra_real_root.rs`): `nl__approx-sqrt` unknown→**sat** with the
    algebraic √2 witness — the CAD-entry coefficient path moved off the i128
    `MAX_ABS_COEFF=2^40` guard onto the bignum algebraic core (`poly.rs`
    `rat_to_int_poly_wide`: BigInt-intermediate denominator clearing so a 10²⁸
    denominator no longer overflows `num×lcm` even though the result fits i128).
    Slice 7b (LANDED, not deferred to the ADR-0058 arc): `nl__approx-sqrt-unsat`
    unknown→**unsat** — the DPLL-cube→exact-CAD edge already existed in
    `dpll_t.rs`; the missing pieces were recognizing the `x²≤2 ∧ x²≥2` pinning
    pair as an equality anchor + the wide clearing. **Mechanism (sound):** an
    equality atom `p(x)=0` bounds the witness set to the roots of that
    small-coefficient `p`; isolate ONLY those roots (exact Sturm) and sign-test
    ALL atoms — including the big-coefficient inequalities — via exact bignum
    `RealAlgebraic::sign_at`. sat = ground-evaluator/`sign_at` replay of the exact
    witness; unsat = complete enumeration of the anchor's roots; every clearing is
    `checked_*` → Unknown on overflow, never a wrong verdict; the anchored path
    only fires as a fallback after the guarded collector declines and returns None
    for any multi-var/structural shape. Independently re-validated: 4 anchored
    tests + 34/34 nra suite, progress_frontier 8/8 (no nra_degree regression),
    BOTH nra+nia differential fuzzes DISAGREE=0 (extended with tight/giant-rational
    single-var anchored seeds up to 10²⁸), `--workspace --lib` 18/18. qf-nra-cvc5
    27→32 (PAR-2 5.421→3.169), DISAGREE=0, model_replay_failures=0. **The bounded
    arithmetic levers (div-0, iand, pow2, √2) are now largely harvested; the
    genuine-engine NRA residue (6/12: Boolean-CAD multivar, MetiTarski, deg-8/10)
    is the ADR-0058 arc.**
- **2026-07-07 — the partial-operator Hard Rule made ENFORCEABLE + a third
  soundness bug closed (`str.from_code`).**
  - (`7ce23583`) **#42 — underspecified-operator fuzz-coverage audit.** Turned
    the Hard Rule from prose into an enforced per-operator checklist
    (`docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`):
    every partial op × {semantics, underspec-vs-total, evaluator convention, the
    fuzz generator that emits its degenerate shape}. Added four degenerate
    seed-classes to `string_differential_fuzz` (`str.indexof` negative start,
    `str.replace_all`, `str.from_code`, `str.to_int` signed) — all DISAGREE=0 vs
    Z3 (447 jointly decided) — and honestly tracked the remaining GAPs (RealDiv-0,
    a BV const-0 seed, seq/FP differential fuzzes). **The audit did its job: it
    surfaced a live P0 wrong-sat** (below).
  - (`6877c365`) **#46 — `str.from_code` wrong-sat, fixed.** `string_from_code`
    capped its sound range at `0..=127` and folded `i≥128` to `""`, while
    `str.to_code` round-trips the full byte range `0..=255` → `(= (str.from_code
    200) "")` was wrongly **sat** (Z3: unsat; U+00C8 is non-empty). A live
    pre-existing wrong-verdict on main. Fix splits on the constant-folded arg:
    `0..=255` → exact byte string (round-trips `to_code`, kills the class);
    `i<0`/`i>0x2FFFF` → `""` (genuinely-invalid code point); **`256..=0x2FFFF`
    and symbolic `i` → DECLINE to Unknown** (valid non-empty chars the 8-bit
    model can't represent — every byte surrogate is unsound BOTH ways, proven, so
    decline is the only sound choice; never `""`). 6 soundness bars + the
    un-ignored repro pass; `string_differential_fuzz` (seeded 0..=300) DISAGREE=0
    (independently re-run, 138s); `--workspace --lib` 18/18; corpus_regression 0
    DISAGREE. Completeness cost: one symbolic NAS-corpus case sat→Unknown (not in
    any committed gate). Third soundness bug closed this session (div-0 P0, the
    const-0 wrong-sat, now from_code) — the untrusted-search/trusted-check loop
    catching its own blind spots.
- **2026-07-07 — the NIA arc: congruent div-0 recovery + `int.pow2`, qf-nia 21→33
  (+12 sound), two soundness bugs closed. 9th review's pivot executing.**
  - (`b91dd918`, `73dceb72`) **#40 — congruent Ackermann div/mod-by-zero.** The
    P0 fix (`52f3b1d1`) made each `_/0` term fresh-per-term — sound vs wrong-unsat
    but it broke congruence (lost the structural div-0 unsats) and left a
    pre-existing wrong-sat in the constant-`_/0` relaxation. Fix: keep the `_/0`
    value free but add eager Ackermann congruence across `_/0` groups (`a=c →
    v_a=v_c`, a valid consequence of totality) on both the constant
    (`int_divmod.rs`) and variable (`nia_linearize.rs`) paths, bounded by
    `MAX_CONGRUENCE_GROUPS=48`. Monotone-sound (no wrong-unsat) + functionally
    consistent (no wrong-sat); the P0 `775<mod(0,0)` stays unrefuted (lone term,
    no congruence partner). Recovered div.01/minimal_unsat_core/**div.08** SOUNDLY
    (qf-nia 21→25); the NEW `qf_nia_divmod_const_differential_fuzz` (deliberately
    emits `(div x 0)`/`(mod x 0)`/nested div-0 — the P0 shape the variable fuzz
    couldn't generate) **caught + closed a pre-existing wrong-sat**. 4 soundness-bar
    tests + all four fuzzes (nia/nra/var/const) DISAGREE=0.
  - (`fb2da08b`) **#41 — `int.pow2` wiring + bounded value-table axioms, qf-nia
    25→33 (85%).** First-class `Op::IntPow2` (parse+eval+every match site), cvc5
    semantics VERIFIED FROM SOURCE (`references/cvc5`): `pow2(x)=2^x` for x≥0,
    **`=0` for x<0 — DEFINED, not underspecified** (confirmed 3 ways) → a hard
    equality, not a wrong-unsat convention. NIA abstraction with six theory-valid
    axiom families (negative, positivity, super-linear, evenness, **x≥0-guarded**
    monotonicity, div/mod-of-pow2) + a value table for pinned exponents;
    `interval_of` decides bounded pow2+product rows by finite-box enumeration;
    int-blast declines pow2 gracefully (`IntBlastError::UnsupportedOp`→unknown). All
    7 pow2-native corpus rows decide; 13 soundness bars incl. the negative-exp
    P0-class tests; new `qf_nia_pow2_differential_fuzz` (seeds negative+zero
    exponents) DISAGREE=0. Independently re-validated before push (`--workspace
    --lib` 18/18, pow2 fuzz DISAGREE=0). **The 9th review's "NIA is NOT
    bounded-exhausted" was right — these two slices beat the whole prior arc.**
- **2026-07-07 — NRA grid slice + the 8th review's soundness-hole closure.**
  - (`80206579`) NRA coordinate sat-witness for >4 free reals — `very-easy-sat`
    decides sat (replay-gated, unit-tested) but BUDGET-MARGINAL at the 10s
    bench, so QF_NRA reliably stays 27 (baseline correctly unchanged; the
    capability is real, the measurement isn't reliable under load).
  - (`b3c4150c`) **The 8th review found the P0's own durable fixes each had a
    hole on this bug's axis — closed:** the `--lib` pre-push gate was
    `-p axeyum-solver` but the defect lived in `axeyum-rewrite` → widened to
    `--workspace --lib` (18 crates green); the differential fuzz that "passed"
    only emits VARIABLE divisors and structurally cannot generate the
    constant-zero `(div x 0)` that bit → new Hard Rule that every partial
    operator's fuzz generates the degenerate argument; the `int_divmod`
    module doc still described the removed unsound convention → corrected.
- **2026-07-07 — NIA `iand` bounded blast (sound +2) + the P0 backstop
  validated.**
  - (`c5a829a3`) **NIA `iand` bit-blast — QF_NIA curated-iand 33%→100% (1→3),
    cvc5-regress 21→23 (59%) SOUNDLY.** Census verdict: `iand` is NOT an IR op
    (parse desugars `((_ iand k) a b)` to `bv2nat(bvand(int2bv k a, int2bv k
    b))`), so contained — a solver-side dispatch fix, not a workspace-wide IR
    rollout. Two additions to the finite-box exact blast: an `interval_of`
    `Bv2Nat` arm (`bv2nat` of a width-w BV ∈ [0, 2^w), the tight iand-bridge
    interval) + `propagate_linear_bounds` (interval propagation over top-level
    linear conjuncts to a fixpoint, so `x+y≤32 ∧ y≥0 ⇒ x≤32` bounds the box).
    Both are logical consequences → the box clamp is equisat-preserving, the
    covering-width invariant keeps the blast wraparound-free → BV-unsat is
    genuine integer unsat. Full `--lib` 716/716, both nra+nia fuzzes + a new
    `iand` differential fuzz (461/461, independently re-run) all DISAGREE=0.
    The +2 here are the iand rows — distinct from div.01/minimal_unsat_core
    (still awaiting the sound congruent-div-0 recovery, task #40).
  - The pre-push hook's new `--lib` gate **ran on this push and passed**
    ("corpus- and unit-sound") — the P0-recurrence prevention is live and
    validated.
- **2026-07-07 — P0 wrong-unsat caught + fixed; NRA slice 2; the pre-push
  unit backstop.**
  - (`52f3b1d1`) **A wrong-unsat that shipped to main, found and repaired.**
    The NIA div/mod slice (`a946f925`) routed unsat decisions through
    `eliminate_int_divmod`, which folded div/mod by a constant-ZERO divisor to
    a FIXED convention value (`div a 0→0`, `mod a 0→a`) — valid as a witness
    but an unsound unsat, since SMT-LIB leaves div/mod-by-zero underspecified
    (`775 < mod(0,0)` is sat, not `775 < 0`). Fix: divisor-zero terms become
    FRESH UNCONSTRAINED variables (underspecified → free; strictly more
    conservative — removes refutations, adds none; a non-convention sat model
    is caught by ground-evaluator replay). Verified: the P0 test passes,
    full `--lib` 712/712, rewrite 88/88, corpus 0 DISAGREE, divmod fuzz
    DISAGREE=0. **Found by the slice-2 agent's full `--lib` sweep — the nia
    lane's targeted `--test`+fuzz gates had skipped it.**
  - (`hooks/pre-push`, CLAUDE.md) **Durable fix: the pre-push hook now runs
    the full solver `--lib` sweep (~30s) on the pushed SHA**, alongside the
    corpus sweep. Both corpus_regression and the fuzzes miss soundness holes
    on shapes that are neither in the committed corpus nor fuzz-generated;
    `--lib` is the backstop that would have blocked `a946f925`. The wrong
    verdict must not leave the machine when a 30s local sweep catches it.
  - (`631be06f`) **NRA slice 2: `a²=−k` int↔real coercion + even-power-equality
    — QF_NRA 26→27 (71%), PAR-2 down.** The even-power matcher now sees
    through `to_real(int const)`/`(- k)` (exact ℤ↪ℝ), tried before the
    Nelson-Oppen coercion relaxation; a new even-power-EQUALITY arm refutes
    `Σ tᵢ^{2k} = c` (c<0). `a²=2` stays SAT (a=±√2) — verified + property-tested
    both directions; nra+nia fuzzes DISAGREE=0 (nra re-run independently).
    A soundness save during dev: a broad `to_real` fold rerouted a sat
    instance into the CAD's algebraic (non-replayable) model — reverted for
    the surgical approach.

- **2026-07-06 (night, cont.) — the next arithmetic arc opens: QF_NIA over
  QF_NRA, first slice lands.** The string program having closed at its
  theory-coupled ceiling, the remaining z3/cvc5 gap is nonlinear arithmetic —
  scoped (`fcbde209`,
  [decomposition doc](docs/plan/track-2-theories/P2.5-nra/09-next-arithmetic-lever-decomposition.md))
  to the measured ROI verdict **QF_NIA (54%) beats QF_NRA (68%)**: NIA's
  unknowns are bounded levers reusing existing machinery, NRA's residue is
  mostly a multi-week CAD/transcendental engine.
  - (`a946f925`) **First slice — NIA div/mod Euclidean linearization (P2.5
    Phase E.0): QF_NIA 21→23 (54%→59%), PAR-2 6.577→5.283.** `check_with_nia`
    (the integer analog of `check_with_nra`) reaches `div.03` (integer sign
    lemma over the variable-divisor Euclidean form) and `mod.02`
    (self-division identity), routed pre-width-ladder. Euclidean identity
    `x=b·q+r ∧ 0≤r<|b|` is theory-valid with the SMT-LIB sign convention
    matched to z3; the `b=0` branch is left FREE (a sound relaxation), so
    relaxation-unsat ⇒ original-unsat, and sat replays against the original
    div/mod. Honest declines: mod.03/div.08 (div-by-zero
    underspecification/congruence — the fixed evaluator convention can't
    soundly replay z3's free choice). DISAGREE=0 + replay=0 across the
    re-measure and THREE fuzzes (nra 2000, nia 2500, and the NEW
    variable-divisor div/mod 1500 — the last independently re-run:
    1227 jointly decided, 853 sat replays, 0 disagree). Next ROI slices:
    NRA a²=−2 coercion, NIA iand blast, NIA int.pow2.
- **2026-07-06 (night) — the 7th review applied + three robustness/decide-rate
  wins.**
  - (`a8f09e94`) **A whole bug class eliminated across 4 collectors.** The
    reported "bounded-encoder deadline hole" (str.replace×membership hang) was
    actually the EXPONENTIAL per-path DAG walk class (visited-set memoized only
    atoms, re-descending shared subtrees) — same as the 9h hang / set_cardinality
    / bv2nat. Fixed VERDICT-NEUTRALLY (memoize every node → linear) in
    collect_lia/lra/uflia/uflra_atoms; the shape now DECIDES sat in 0.27s (was
    ~6.2s @ 30× deadline overrun). Regression can't hang CI; uflia fuzz + cdclt
    parity DISAGREE=0.
  - (`e0e24085`) **nra_degree frontier 2→40.** Wired the existing sound
    `nra_even_power_refutation` matcher into the NRA decide path (was
    evidence-only): `(x-1)^2N+(y-2)^2N+1<0` is always-unsat, decided
    O(term-size) at any degree → a deterministic (load-insensitive) floor.
    Independently verified (nra fuzz + nia fuzz + corpus DISAGREE=0). Honest
    decline of the QF_NRA corpus front: the FM→simplex premise was FALSE (the
    linear residual already routes through Farkas-checked simplex); the 11
    unknowns need real CAD/nlsat, beyond a bounded increment — QF_NRA stays 26/38.
  - (`c82e6a5a`) **Two soundness invariants enforced STRUCTURALLY** (closing
    the class behind the day's two P0s): string fuzz generators now hard-assert
    ≥10% \u-escape + ≥2% >0x7F coverage (with a #[should_panic] plain-ASCII
    trip test), and `Script::checked_flat_view()` debug-asserts against the
    vacuous-sat path, adopted across the fixed-text consumers.
  - (`e4fe342a`) **7th-review currency:** ADR-0054 accepted; the twice-rotted
    string counts now LINK the scoreboard (78/707) instead of hand-copying;
    the CdclT LIA/LRA adapters honestly relabeled DARK + formally SHELVED
    (no measured win — a parity twin with 85 conservative unknowns — and no
    demand: slice b was census-declined as redundant); the P4.2/P5.1 symexec
    single-owner overlap DECIDED (Track 4's explore_cfg owns it, Track 5
    consumes). Frontier ratcheted (lia_cuts 26 / bv_reduction 30, quiet-box).
- **2026-07-06 (late) — Phase D + the theory-coupled string frontier closed;
  the CdclT arith adapters land (dark: opt-in, parity-only); string program QF_S 52→78 (58%).**
  - (`d124f427`) **Phase D extended-function reductions**: constant-pattern
    `prefixof`/`suffixof`/`contains` → regex memberships (polarity-symmetric,
    ride the certified derivative-emptiness/matcher-replay routes),
    constant-fold `str.replace` → exact first-occurrence splice. QF_S 74→76,
    QF_SLIA 15→16, both-oracle fuzzes DISAGREE=0. (Flagged a pre-existing
    deadline-hole in the bounded ADR-0029 encoder on `str.replace`+membership
    — filed, no wrong verdict, no corpus trigger.)
  - **CdclT arithmetic migration — adapters landed, still DARK (ADR-0055 criterion 2 NOT yet met):** LiaTheory
    (`9c5be4fc`) + LraTheory (`fc4e33bc`) — both a thin sound adapter over the
    validated online machinery (each already implemented the TheorySolver
    trait); parity DISAGREE=0 (LIA 3100 cases, LRA 1500 fuzz + 8/8). Slice b
    (strings+LIA combination) was **census-DECLINED honestly**: the len/code
    sharing was already eager+default-on via the code-bridge (`122c3c27`), so
    a CombinedStringLiaTheory would move zero files while adding cross-theory
    trust surface — measure-don't-seed. The census redirected to the real
    lever below.
  - (`0f864852`) **Lexicographic-order theory — `str.<=`/`str.<` over
    variables**, the last theory-coupled string class. A certified unsat-only
    refuter: constant folding (Arm A) + transitivity closure with first-char
    code-clash and prefix-exclusion (Arm B); independently re-derived from the
    word operands; only adds re-checked unsat to unknown, never sat. QF_S
    76→78, QF_SLIA 16→18; fuzz z3 653/653 + cvc5 641/641 DISAGREE=0
    (276 certified unsats, independently re-verified). **String program:
    QF_S 52→78 (39%→58%), QF_SLIA 36%, DISAGREE=0 held across the whole
    sprint; the theory-coupled string frontier on this corpus is closed.**
- **2026-07-06 (evening) — the post-sprint rotation lands: string sprint
  banked to Lean, the CdclT arithmetic keystone opens, NRA moves again.**
  Three of the 6th review's top-ranked levers, all pushed, DISAGREE=0 held:
  - (`ff648094`) **String word-clash certificates reconstruct to
    kernel-checked Lean — P3.7 gains its 9th fragment**, no new kernel
    axioms. `Char` is a finite enum (one nullary constructor per distinct
    code point, so constant-inequality is a constructor-distinctness
    ι-computation — no unary-`Nat` magnitude); `Str = List Char`; `append`
    opaque so equality-joining is pure `Eq`-congruence. Covers contradicted
    disequality + concrete constant clash (direct + chained); variable-prefix
    cancellation / self-loop-length / derivative-emptiness honestly deferred.
    360-case property all kernel-check; 2 negative kernel-rejection tests.
    This banks the QF_S 52→74 sprint as *checkable* evidence, not asserted
    soundness.
  - (`9c5be4fc`) **LiaTheory on the online CDCL(T) driver — ADR-0055
    criterion 2, slice (a).** Key finding: the validated online `LiaTheory`
    (`lia_online.rs`) *already* implemented the `TheorySolver` trait the
    driver consumes, so the migration is a thin sound adapter, not a rewrite.
    Trigger-literal invariant handled (deterministic fold-in when a minimized
    core drops the just-asserted literal — a superset of an unsat set stays
    unsat); propagation deferred; opt-in `check_qf_lia_online_cdclt`, default
    dispatch unchanged. Parity: 2500-case Boolean-structured 0 DISAGREE + a
    600-case conjunctive 600/600 vs the trusted simplex; step budget never
    tripped. The keystone that unlocks strings+LIA combination (the 8
    theory-coupled census files + 21 gate-downgraded unsats), QF_UF
    default-on, and NRA/NIA service.
  - (`5cc63a15`) **NRA off 21/38 → 26/38 (68%), PAR-2 8.66→5.97** — untouched
    since 07-02. Two sound levers: a bounded rational sat-witness probe (grid
    `{0,±1,±2,±½}`, replay-gated against the *original* division-intact
    assertions ⇒ never a wrong sat; closed issue9164-2 / dist-big /
    nlExtPurify-test / poly-1025), and threshold-1 monotonicity past the
    sign-refutation cap as a second bounded stage (chained `r≥b≥1` refutes
    `ones`). Correctly DECLINED the `1/(a/b)→b/a` rewrite (unsound under `/0`
    totality). Independently re-verified before push: nra fuzz 1713 jointly
    decided / 1478 sat replays / **DISAGREE=0**, nia fuzz DISAGREE=0 (the
    shared-multivariate-path guard).
- **2026-07-06 — Track 5 / P5.4 T5.4.1 (`2423eaeb`): the differential-fuzz
  oracle harness.** `reflect::oracle::DiffFuzz` packages the
  verification↔fuzzing loop as reusable API — deterministic (seeded-LCG +
  width-corner) differential fuzzing over BV input symbols in both shapes:
  `check_agree` (reflection ≡ reflection, e.g. MIR vs LLVM) and `check_against`
  (reflection ≡ the real Rust fn). `FuzzReport` + `assert_agreed` are the
  DISAGREE=0 one-liner. First two hand-rolled loops collapsed onto it (cross-IR
  differential fuzz, checksum module oracle); full axeyum-verify sweep green
  (34 binaries, 215 tests), clippy + rustdoc `-D warnings` clean.

- **2026-07-06 — Track 5 / P5.1 T5.1.1 (`cc695925`, ADR-0057): the IR
  reflectors are a real library module.** `tests/reflect_common/{mod,mir,llvm}.rs`
  (recompiled by 8 test binaries each) → `axeyum_verify::reflect`
  (`src/reflect/*`, submodules `reflect::mir`/`reflect::llvm`), so
  `axeyum-verify`'s own code — the coming P5.2 contracts / P5.3 kernel
  obligations — can call the reflectors, not just the tests. Decision: a
  **module, not a new crate** (ADR-0057 — one consumer today, ADR-0001
  minimality, no workspace-`Cargo.toml` edit, which also keeps it off the
  concurrent solver/strings lane). Library-API hardening: `missing_docs` on all
  newly-public items (the repo's `# Panics` convention for the parse-or-die
  reflectors) + per-item `#[allow(clippy::implicit_hasher)]` on the SSA-env
  maps. Exit criterion met: 8 reflection test binaries (62 tests) green against
  the module API; clippy + rustdoc `-D warnings` clean.

- **2026-07-06 — T-C.6 membership atoms online + a pre-existing escape-decoding
  wrong-verdict class fixed: QF_S 74 (55%), QF_SLIA 15, totals 695.**
  - (`ba0d9149`) **The seed-215 investigation exonerated the quarantined WIP
    and convicted MAIN**: both string-literal decoders (byte-model +
    word/skeleton routes) never expanded `\u{h…}`/`\uhhhh` escapes while the
    regex side always did — two denotations for one text, a wrong-verdict
    class against Z3/cvc5 for ANY escaped literal mixed with `str.in_re`
    (issue9784, instance3303/7075-delta, regexp003). One shared
    `decode_string_code_points` now serves every route; >0xFF declines in
    the byte model rather than truncating.
  - (`2bec9d87`) **T-C.6: membership atoms in the online CDCL(T) route** —
    both polarities in the word skeleton; unsat only via the per-variable
    regex-intersection re-checked emptiness certificate; sat only via full
    replay (word atoms by eval + membership truths recomputed by the
    independent matcher). Census: re-mod-eq (×2), re-neg-unfold-rev-a, and
    instance1079 all decide. New 700-script online-membership fuzz vs BOTH
    oracles (z3 552 jointly, cvc5 549) — DISAGREE=0.
    **Re-measure: QF_S 67→74 (55%, PAR-2 2.928→2.182), QF_SLIA 14→15,
    totals 695 decided / 640 compared / DISAGREE=0.**
  - (`84cd1a21`) vacuous-view audit: 9 embedded-literal consumers safe by
    construction; `explain_corpus` was the one real hole — closed via the
    new structural `Script::solvable_flat_view()` guard (None exactly when
    word-only-fallback), adopted at both risky call sites.
  - (`3a7f86b6`) the pre-push hook now gates the PUSHED SHA in a throwaway
    detached worktree (8-10s hot; docs-only skip 0.02s) — unrelated WIP in
    the shared checkout can no longer force `--no-verify`. First real push
    through it validated clean.
  - The `wip/t-c5-membership-atoms` quarantine branch is superseded and
    deleted; the string program stands at **QF_S 52→74 (+22, 39%→55%)
    across 2026-07-03…06 with DISAGREE=0 held at every step**.
- **2026-07-06 — Track 5 (Verified Systems, IR reflection) adopted as a
  first-class goal (ADR-0056).** The seL4-inspired application trajectory —
  reflect compiled Rust (rustc MIR + LLVM IR) into `axeyum-ir`, discharge
  panic-freedom / memory-safety / constant-time / translation-validation /
  protocol-refinement obligations push-button with replayed or certified
  evidence — is promoted from consumer-track horizon note to
  [`docs/plan/track-5-verified-systems/`](docs/plan/track-5-verified-systems/README.md)
  (phases P5.1 front end → P5.2 contracts → P5.3 kernel obligations → P5.4
  fuzz-oracle loop → P5.5 measured external target), with a third
  definition-of-done in the north star, a Track-5 lane in the dependency DAG
  (not keystone-blocked), and the phase table above. Basis: the prototype
  rounds Q–U (2026-07-02/03) landed both reflectors + CFG executors, 16
  cross-IR equivalence proofs, a 5-shape refutation corpus with replay-checked
  countermodels, exact panic specs (overflow/division/bounds) with
  `catch_unwind` witness replay, and a checksum module end-to-end — all green,
  millisecond proofs — plus the 2026-07-06 landscape survey (Hyperkernel /
  Ironclad / Asterinas-vostd / Kani / seL4-Rust) recorded in the ADR. The
  boundaries are explicit: no seL4-parity claims, no ghost-code deductive
  language, no source-level Rust semantics — post-borrowck MIR +
  post-optimization LLVM IR, cross-checked against each other.

> Changelog entries for 2026-07-03 archived: [docs/status-archive/changelog-2026-07-03.md](docs/status-archive/changelog-2026-07-03.md)
> Changelog entries through 2026-07-02 archived: [docs/status-archive/changelog-through-2026-07-02.md](docs/status-archive/changelog-through-2026-07-02.md)
