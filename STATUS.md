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
  [SCOREBOARD](bench-results/SCOREBOARD.md) totals (~68% as of
  2026-07-03 — the scoreboard is authoritative; this line links rather than
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
  wrong verdicts, repaired). Next: recover the 21 declared-`unsat` downgrades
  via regex Parikh intervals + `substr`-family facts + width widening
  (ADR-0052 residual; in progress).
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

- **2026-07-06 (late) — string sprint closed; rotate to NRA + Lean + honest
  keystone accounting (7th periodic review).** Live totals in the generated
  [SCOREBOARD](bench-results/SCOREBOARD.md) (**QF_S 78/134 ≈58%, QF_SLIA 18/50,
  ~707/992 decided**, DISAGREE=0 — do not hand-copy; string counts rotted twice
  across review cycles). The **theory-coupled string frontier is closed** on
  this corpus (len/code bridge, lex-order, membership, Phase D extended-fns);
  the ~78 QF_S / 28 QF_SLIA still-undecided are almost all **unsupported**
  fragment (to_int / replace_re / seq.* — each needs *new machinery*, not a
  cheap lever), so strings are **expensive-not-done**: the Phase-D census
  named the highest-count unsupported class before the lane parks.
  **Rotation (7th review's ranking): (1) make one CdclT arith adapter
  load-bearing OR honestly shelve it — the LIA/LRA adapters are landed but
  DARK (opt-in, zero scoreboard rows; slice b combination declined as
  redundant with the code-bridge), a recurrence of the 5th review's
  dark-keystone flag; (2) NRA 26/38 → higher (FM→simplex nested `1/(a/b)`,
  threshold-1 widening; `nra_degree` frontier 2/6 = the most headroom of any
  lever, highest ROI-per-effort); (3) enforce the two soundness invariants
  STRUCTURALLY (string-fuzz-generators-emit-escapes assert; the vacuous-view
  guard at all harness consumers) — both are "fixed at known sites, not
  enforced," the shape that produced the day's two P0s.** A bounded-encoder
  deadline-robustness fix (task #33) is in flight. Session history:
  [docs/status-archive/](docs/status-archive/) — FOCUS not log; keep ≤30 lines.

## Already shipped this session (pre-plan)

The reachability / symbolic-execution / certificate surface that motivated this
plan is built and committed on the current branch:

- BMC driver, k-induction (unbounded safety), symbolic-memory BMC,
  `SymbolicExecutor` (path exploration + test-suite enumeration + path-condition
  optimization), and self-rechecking certificates (`UnsatProof::recheck`,
  `SafetyCertificate::recheck`, `EndToEndUnsatOutcome::recheck`).
- These map onto Track 4 (use cases) and Track 3 (the recheck family); the plan
  records what remains around them.

## Phase status

### Track 1 — Engine & Performance
| Phase | Title | Status |
|---|---|---|
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. **CDCL(XOR) foundation landed** (`gf2`/`xor_extract`/`xor_propagate` in `axeyum-cnf`) — the path-2 multiplier-wall attack: a sound GF(2) Gaussian engine + exact XOR-gate extraction + an entailment-checked propagation pass; slice 4 wires it into the live preprocess pipeline (measured). Vivification / glue tiers remain |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). **T1.2.4 elim_unconstrained landed** (`axeyum-rewrite::elim_unconstrained`): a variable occurring once under an invertible BV op (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`) makes that subterm unconstrained → replaced by a fresh var, operator dropped (Z3's `elim_unconstr`); peels nested layers, terminates. Model-sound via the trail (`x := op⁻¹(u,w…)`; orphaned operands defaulted, sound by the inverse identity); wired into `check_with_preprocessing` after solve_eqs (opt-in, default-off per ADR-0034). `bvumulo` now uses the word-width threshold encoding `a > all_ones / b` instead of a doubled-width multiplier, so BV256 overflow checks no longer build BV512 multiplication terms. 6 unit (incl. 300-trial randomized reconstruction) + 2 solver end-to-end plus focused IR overflow/shape coverage. Next: measure on the public p4dfa slice; then max_bv_sharing / bv_slice / AIG 2-level (T1.2.5–T1.2.9) |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | WIP — the proof-producing core `solve_with_drat_proof` (`proof_sat.rs`) modernized: **VSIDS activity branching** (bump conflict-side vars, MiniSat-style decay, rescale-on-overflow; highest-activity unassigned var, ties to lowest index), **phase saving**, and **Luby restarts**. Sound by construction — every emitted clause is RUP and the proof is DRAT-checked, so a heuristic bug only slows search. All 231 cnf tests pass (incl. the 400-CNF differential vs BatSat + a new pigeonhole-4→3). NB the modern CDCL(XOR) core in `xor_cdcl.rs` already has VSIDS/Luby/LBD. Remaining: arena + packed watches, chronological backtracking; wire a modern core into the default path |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. **Slices a+b LANDED 2026-07-03** (`a3460101`,`c9d332c1`): the generic online `CdclT<T: TheorySolver>` driver (1-UIP over the mixed implication graph, lockstep theory push/pop, deadline in the loop; EufTheory parity 2500/2500 vs offline, z3 QF_UF fuzz unchanged) + the StringTheory adapter (per-assert certified refutations, premise-index→trail-literal explanations, replay-gated sat; census disjunctive shapes decide; 1500-case fuzz DISAGREE=0; found+fixed a real 1-UIP underflow on non-current-level theory cores). Front-door QF_S wiring landed same day (`c924fcb0`). Remaining: the DEFAULT-DISPATCH ADR + broad re-measure (the routes are opt-in — built, not yet banked), CdclT termination/livelock re-verify before default-on, propagation in StringTheory, arithmetic theories onto the driver; theory combination with BV (P1.6) for complete QF_UFBV |
| P1.6 | Theory combination (th_eq bus, interface equalities) | WIP — **EUF+LIA/LRA combination landed & dispatched (QF_UFLIA/UFLRA), complete for conjunctive UNSAT**: `declare_fun` admits Int/Real UF sorts, and `check_with_uf_arithmetic` decides the core squeeze/nested congruence UNSAT cases; SAT model lifting for arith UF remains conservatively `Unknown`. The QF_UFLIA overbound lazy CEGAR path now avoids duplicate generic LIA timeouts, folds narrow Int-bound structure, batches same-candidate UF lemmas and simple bound conflicts, checks deterministic Boolean-justified arithmetic supports, carries reusable arithmetic clauses, keeps an `IncrementalArithDpll` warm while UF lemmas are appended, deletion-minimizes small LP-relaxation Farkas supports before learning LP-core clauses, stage-gates checked affine-bound cores after the first warm solve, and schedules one post-candidate unary-Int sibling Ackermann lemma after a violated UF pair without broad preseed. The online UFLIA route now collects only actual theory atoms, handles n-ary `and`/`or` and Boolean equality, reports precise unsupported-shape details, and admits Int order atoms containing Int-sorted UF applications as opaque LIA variables for UNSAT/conflict/propagation only. Direct `uflia_online_probe` hard-row runs moved from `non-Boolean term with sort Int` to the bounded opaque-app guard, and that guard is now keyed by actual opaque-app order atoms rather than total atom count; the generated rows report **334** opaque-app order atoms out of **485** total (`opaque_app_order_atoms=334 > 128, total=485`). Nested LIA feasibility/core/model/probe checks, shared CDCL(T) Boolean/theory propagation loops, and Boolean UFLIA construction checkpoints now inherit/check the Boolean-layer deadline. Large combined opaque-app layouts use deferred LIA feasibility at the theory-propagation boundary, and opaque-app layouts that cannot build the incremental combined state now decline instead of falling into the older enumerative fallback. A temporary broad cap raise to **512** now declines both generated direct probes in about **4 ms** with `opaque-app online UFLIA incremental combined state could not be built safely` instead of running past **30 s**; the committed guard stays **128** because this is safe decline, not a solve-rate closure. The generated rows stay `unknown`: production lazy 1 s diagnostics still reach actual UF refinement (**2** UF rounds, **1** candidate, **282** pair checks, **6** equal-argument pairs, **5** violations, **1** sibling lemma, **7** total UF lemmas), and the 10 s hard row reaches **6** UF CEGAR rounds, **5** candidates, **1352** pair checks, **22** equal-argument pairs, **15** violations, **5** sibling lemmas, and **27** learned UF lemmas before a warm arithmetic timeout with **total_rounds=280**, **blocking_lemmas=295**, **core_src_affine=45**, **core_src_lp=204**, and **core_len_avg=6.4** in the latest sample. Plus the combination primitives `theory_combination` (shared/propose/classify/arrangement) + `th_eq` bus (`theory_var_classes`/`interface_th_eqs`) and the earlier lazy/on-demand Ackermann for QF_UFBV. Remaining: partitioned opaque-heavy admission that preserves incremental-build safety, opaque-app model lifting, UF CEGAR convergence/relevance after several candidate models, reducing LP-core-producing SAT branches, then full online interface-equality (Nelson-Oppen) combination of the e-graph + BV to drop Ackermann reduction entirely |
| P1.7 | PBLS local-search BV engine (portfolio) | WIP — **word-level WalkSAT landed** (`solve_local_search` + `PblsBackend`, `pbls.rs`): keeps a concrete Bool/BitVec(≤128) assignment, scores by evaluator-falsified assertions, nudges a variable in an unsatisfied assertion (greedy + WalkSAT noise + random restarts) toward a model. One-sided + sound: `Sat` only with an evaluator-verified model, never `Unsat`, `Unknown` (incl. out-of-scope sorts) otherwise. Read-only on the arena (fits the trait); deterministic (fixed seed, explicit budgets). 4 unit + an ignored 150-formula differential vs the eager backend (never contradicts). Remaining: integrate as a portfolio strategy; tune moves/budgets; measure on satisfiable corpora |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO — Codex review recommends promoting this from cleanup to risk control: split `solve()` into explicit tactic contracts with fragment predicates, transformation class, replay/proof obligation, resource behavior, and benchmark-visible per-step metrics |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | WIP — **destination-2 lever measured & scoped** (commits beee599/9846349, `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`). KEY FACT: lazy abstraction-refinement bit-blasting (`solve_lazy_bv_abstraction`, ADR-0019) is **built but NOT wired into default `solve()`/bench** — so the "~2-3/113 public QF_BV" picture is the *eager* mountain-builder. Measured (`tests/lazy_bv_curated_measure.rs`): lazy decides **incidental-heavy-op** cases with 0 multiplier blasts (`x=1∧x=2∧r=p·q` → unsat ~0ms, 0 refined), cracks `calypto_9` (sat, 2 ops refined), is a safe no-op when `ops=0` (public files), no shortcut on essential multiplier-equivalence. Next (coordinate on shared bench): lazy-bv bench backend → measure public 113 (DISAGREE=0) → opt-in `SolverConfig::lazy_bv` strategy → default-on ADR after net benefit. The highest-ROI perf move is wiring+measuring a built CEGAR bit-blaster, not a new algorithm |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | WIP — **lazy select-congruence** (`check_qf_abv_lazy`): read-over-read consistency added on demand (CEGAR) vs the eager O(n²) per-array pairing; sound (post-ROW abstraction relaxation ⇒ UNSAT transfers; sat replays) + terminating; 200-formula differential vs eager `check_with_array_elimination` (all agree). `eliminate_arrays` exposes `abstraction()`/`selects()`. **Array-extensionality refutation via congruence** wired into dispatch (`has_array` flag): `a=b ∧ select(a,i)≠select(b,i)` (incl. **wide-index** array equality the eager 2^iw enumeration refuses) is `unsat` by `prove_unsat_by_congruence` (select/store as UF; congruence valid for arrays). Lazy ROW/extensionality `unknown` details now report refinement counters and attempt replay-gated last-candidate SAT salvage before budget declines. The AUFLIA `bug337` probe still times out at round 2 with 4096 sites, 150 array-equality atoms, 6973 congruence lemmas, and 146 diff-skolems; the direct-select mixed replay beam moves the first false replay point from direct readback equality ordinal 34 / term 555 to generated OR ordinal 210 / term 3879 under the final strict replay-improvement gate. A generated-OR mixed beam is retained only for small, multi-false replay surfaces after the unguarded large-row attempt regressed `bug337` back to term 555 and doubled wall time. Branch-select diagnostics now show OR 210 branch 0 followed by select 34's store-chain repair makes term 555 true but lands back on OR 210 at total_false=2, while direct select repair worsens to ordinal 35. A small-surface branch/select-cycle repair now handles the alternate-branch version of that pattern, but the large `bug337` attempt was measured/rejected and guarded off after no frontier movement plus route-time growth. Returned-OR diagnostics show the remaining post-select blocker is OR 210 branch 0 with one false literal, store-definition equality term 580 (`x_339 = store(x_325,x_337,2)`). A guarded same-branch residual repair now covers the small case where preserving the select readback requires rebuilding the branch target `target = store(base,i,v)` from the current repaired base. The small-surface repair now follows bounded residual generated-OR chains and clears a two-OR array-copy analogue under the strict replay-improvement gate. Follow-up OR repair now compares greedy branch repair with scalar-choice branch repair; the small scalar-direction case is fixed, but large-row diagnostics still choose the greedy OR-236 branch. OR-236 false-literal diagnostics expose the sibling scalar blockers; the paired scalar-chain trace shows branch 0 oscillates; scalar-closure branch scoring shows reported OR-236 branches 0..7 all return to OR 236 with final_branch_false=2/final_total_false=1; production residual follow-up OR repair rejects that same no-progress scalar-closure returned-OR loop instead of forcing `followup_or236_branch0_branch`; guarded multi-literal branch scheduling applies the same returned-OR guard in projection/targeted replay; select-backed scalar repair updates asserted backing array entries before readback alignment, moving `bug337` past OR-236 to scalar equality term 3408 (`x_383 = x_330`) with projection repair changes down to 430; scalar-candidate diagnostics show term-3408's two directions expose OR 210 / term 3879 or OR 211 / term 4108, while unguarded targeted scalar replay repair was measured/rejected on the large row and kept behind a small-surface guard; scalar+OR follow-up diagnostics show those obvious OR-210/OR-211 branch repairs worsen full replay to total_false=3 and return to term 3408; closure-level diagnostics show OR 210 closes only to expose OR 211, while OR 211 closes only to expose OR 210, both at total_false=2; second-hop OR diagnostics now report `returns_first_or` for both directions (OR 210 -> OR 211 -> OR 210 and OR 211 -> OR 210 -> OR 211); production branch-choice/fallback now reject that two-hop no-progress cycle on small replay surfaces (<=64 positive conjuncts) while a measured ungated large-row version was rejected after regressing `bug337` to OR 210 and ~72.5 s; branch-term diagnostics identify the large-row toggle as OR210 branch term 3805 (store-definition branch) paired with OR211 branch term 4107 (copy/no-store branch); returned-OR literal diagnostics refine the blocker to term 4041 (`x_303 = x_317`, inserted-cell array vs default array) on 4107 plus term 583 (`x_331 = store(x_317,x_320,x_337)`, default array vs inserted-cell store RHS) on 3805; and a small-surface returned-OR stabilizer now handles the synthetic version under a strict replay gate while the ungated `bug337` attempt was measured/rejected after regressing the first diagnostic phase to 231.8 s, so the large-row path is capped at <=64 replay conjuncts; a diagnostic-only direct returned-OR stabilization probe then ruled out repairing the concrete large-row literals in isolation because OR210/branch3805/term583 and OR211/branch4107/term4041 both become worse (`total_false=3`) and return to term 3408. Remaining: paired scalar+array or relevance-guided learned large-row constraint for the 4041/583 array-cell disagreement that preserves term 3408; **lazy ROW (on-demand store axioms)** for the SAT side of wide-index arrays; and func_interp model polish |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | WIP — **multi-equation Diophantine infeasibility** (`prove_lia_unsat_by_diophantine`, commit 96f07a3): a conjunction of integer equalities that is rational-feasible but **integer-infeasible** is UNSAT — fraction-free Hermite-style integer Gaussian elimination reports a contradiction row (`0=c` or per-row `gcd ∤ rhs`), deciding the case B&B can't terminate on for unbounded vars and the single-equation GCD misses (e.g. `x+y=0 ∧ x−y=1 → 2x=1`). **Strictly generalizes & replaced** the single-equation `prove_lia_unsat_by_gcd` in dispatch (no regression). Sound (only integer-preserving row ops; `checked_*` → "not refuted" on overflow, never a wrong unsat; SAT systems never refuted, negative-tested). 11+2 tests. Remaining: Gomory/cube cuts; inequality-integrated cuts |
| P2.5 | NRA: incremental linearization → nlsat/CAD | WIP — linear-abstraction + sign/zero lemmas + McCormick + spatial B&B + point-lemma refinement already shipped. **Added threshold-1 monotonicity lemmas** — growing (`a≥1 ∧ b≥0 ⇒ r≥b`, decides `x≥1 ∧ y≥1 ∧ x·y<1`) and shrinking (`0≤a≤1 ∧ b≥0 ⇒ r≤b`, decides `0≤x≤1 ∧ y≥0 ∧ x·y>y` where only one operand is bounded so McCormick can't apply); two-operand only — **plus a refinement overflow safety net** (`too_large_to_refine`: stop refining past a 2³¹ magnitude bound, → `unknown` not a panic; hardens the exact-rational simplex against escalating witnesses). **Sum-of-squares lemmas landed (2026-06-18)** — `sos_lemmas`: for a pair `a,b` with `a·a`/`b·b`/`a·b` all abstracted, add `(a±b)² ≥ 0` over the result vars (sound), restoring the cross-product correlation independent abstraction drops, so **`a²+b² ≥ 2ab` / AM–GM₂ is now PROVED** (the Spivak SOS-frontier test promoted prompt-`Unknown`→`Unsat`; negative test confirms `a²+b²=2ab` stays sat). 26 NRA + 5 Spivak tests. **Since then (2026-06-28…07-02, see the changelog + [SCOREBOARD](bench-results/SCOREBOARD.md)): the CAD arc landed** — bignum algebraic core in `axeyum-ir` (ADR-0044/45/46), a 2-var-complete / N-var decision-complete fuzz-gated CAD, coprime-split projection, first-class `/0` division witnesses (`124e18aa`), and five z3-gated adversarial differential fuzzes at DISAGREE=0; the committed curated baseline is **QF_NRA 21/38 decided (was 9/38)**. Remaining: FM→simplex for nested `1/(a/b)` shapes, threshold-1 monotonicity widening, higher-degree/multi-var SOS (Bernoulli, general Cauchy–Schwarz), NRA proof production |
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — full e-matching vertical slice on the keystone: `enumerate_apps` + `ematch` engine + `instantiate_forall_via_egraph` (congruence-aware, single/multi-var, nested/joint triggers) + `prove_quantified_unsat_via_egraph` (the **instantiation loop**: instantiate → re-solve via `check_auto` → fixpoint, sound UNSAT). trigger *inference* (single + multi-pattern set cover) landed; loop **wired into `solve`** (infinite/too-wide-domain fallback → keystone before MBQI). **Closed-universal falsification lever landed 2026-07-03** (`3785c480`): the qinst census disproved the depth hypothesis (0/17 budget-starved — the blocker is quantifier shape), and a closed `∀` with QF body over exactly its bound vars is now refuted exactly via `¬body[x⃗:=fresh]` SAT (one bounded check_auto; the valid direction owned upstream); BV-quantified 37→38, new 600-case quantified-BV differential fuzz DISAGREE=0, 900-seed bounded-instance soundness harness. Next: MBQI on the keystone (the 16 existential/nested census files are its demand signal), then migrate `axeyum_rewrite`'s bespoke closure onto the keystone. (Verified: the multi-pattern join is already congruence-correct — `ematch` binds variables to canonical e-class roots and `trigger_to_pattern` never mutates the union-find, so raw `ENodeId` equality in `merge_substitutions` *is* root equality.) |
| P2.7 | Strings (unbounded, full `str.*`, regex) | WIP — **Phase A DONE** (ADR-0051 `Sort::Seq`; ADR-0052 `len`↔LIA link + bounded-unsat gate, repaired a measured wrong-unsat class). **Phase B core LIVE both directions (ADR-0053, landed 2026-07-03):** T-B.1 normalization → T-B.4a arrangement search → T-B.4b routing + parser dual-build → extended-fn reductions → T-B.4d word-first fallback → harness parity (**QF_S 52→78 across 07-03…06** — see the generated scoreboard, oracle-verified) → **T-B.7 slices 1–2**: word `unsat` ONLY via the independent derivation checker (`check_derivation.rs`, own union-find + walkers; word fuzz **96 sat + 305 unsat, DISAGREE=0**). Coverage-boundary census (3c13df63): the word fragment's corpus ceiling is reached — remaining 35 unknowns = regex 15 (→ **Phase C LANDED through T-C.6** (ADR-0054: derivative engine + membership sub-solver + membership atoms online)), extended-fns 11 (→ Phase D), lex-order/code↔LIA 8, seq+len 1. **Phase C (ADR-0054, ACCEPTED) LANDED through T-C.6** (derivative engine + membership sub-solver + membership atoms online); **Phase D extended-fn reductions + the lexicographic-order theory landed** — the theory-coupled string frontier is CLOSED on this corpus at QF_S 78/QF_SLIA 18. Remaining declines are unsupported fragment (to_int/replace_re/seq.*), each needing new machinery. Residual: T-B.5 F-Loop, T-B.6 eager conflicts (perf polish); the bounded-encoder deadline-hole (task #33, in flight) |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | WIP — the FP theory is broad already (classification, compare, abs/neg/min/max, add/sub/mul/div/fma/sqrt/rem/roundToIntegral, fp→fp resize, fp→real/ubv/sbv). min/max ±0 confirmed correct (deterministic allowed choice). **Added integer→float conversion** (`from_ubv`/`from_sbv`, 2026-06-18): rounds a w-bit unsigned/signed-two's-complement integer to a dst float under a rounding mode (reuses `pack_value`; exact 0→+0; |x| via two's-complement read unsigned, correct for INT_MIN). Differential-tested vs Rust's native `as f32`/`as f64` (i32/u32→F32, i64/u64→F64; edges + 3000-case sweep, exact). Completes the `to_fp` family on the builder side. Remaining: SMT-LIB parse wiring for `(_ to_fp …)`/`to_fp_unsigned` over bv sources (axeyum-smtlib, coordinate); `to_fp` from real constants; unspecified-value edge polish |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | WIP — **structural refutation** (`prove_datatype_unsat_structurally`): acyclicity + distinctness + injectivity **+ congruence** (equal args ⇒ equal apps, e.g. `x=cons(h,a) ∧ y=cons(h,b) ∧ a=b ∧ x≠y`) + constructor exhaustiveness over a term-level union-find; also flattens top-level conjunctions and refutes top-level `or` when every branch is structurally contradictory. Sound, wired into dispatch/evidence/Lean reconstruction ahead of the eager expansion; the cvc5 QF_DT exact audit is now 3/3 dominant with Lean unsat 3/3. 13 focused tests. Remaining: e-graph constructor *splitting* (case-split `is-c` on the keystone) for SAT-side completeness; exact field guards to remove the relaxed `unknown` cases; broader datatype corpora beyond the cvc5 three-row slice |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | DONE |
| P3.1 | LRAT clausal upgrade (+ in-tree check_lrat) | WIP — **`check_lrat` (hint-based linear checker) + `elaborate_drat_to_lrat` + parse/write** landed in `axeyum-cnf`, sound (3 negative/rejection tests) + 600-CNF differential; **threaded into the evidence export**: every `UnsatProof` (QF_BV + reduced QF_ABV/AUFBV/UF/LIA/datatype) now carries a self-checked LRAT certificate, `recheck` cross-checks it, `recheck_lrat` re-checks it in linear time, tamper-detected. Remaining: emit LRAT hints directly from the proof-producing CDCL core (vs post-hoc elaboration); RAT-step elaboration (negative hints) |
| P3.2 | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | WIP — **resolution-layer IR + parser/printer + sound `check_alethe`** in `axeyum-cnf::alethe`: `resolution`/`th_resolution` steps verified by `{premises,¬concl}`-UNSAT via the proof-producing core + `check_drat` re-check (entailment itself independently checked); verify-before-record; 7 tests incl. 3 rejection. Remaining: typed-term IR (vs opaque atoms), more rules, emit Alethe from solver runs, Carcara CI cross-check; extract `axeyum-alethe` crate (ADR) when the term IR lands |
| P3.3 | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | WIP — **arithmetic `la_generic` checking** (`check_alethe_lra`): a linear-arith tautology clause verified by `¬clause`-UNSAT via the Farkas-certified `check_with_lra`; pluggable `check_alethe_with` callback keeps `axeyum-cnf` arithmetic-free. 5 tests incl. soundness rejections. **`lia_generic` (integer) checking+emission** added via `check_with_lia_simplex` (honors integrality; integer/real distinction tested). **Carcara cross-check harness (T3.3.5)**: EUF (transitivity+congruence), **LRA `la_generic`** (Farkas `:args` incl. equalities), and **clausal resolution** (`lrat_to_alethe`, T3.3.3) proofs all externally `valid`; gated test skips without the binary. Remaining: BV `bitblast_*` rules (T3.3.1–2) for the full QF_BV proof; LRA >2-atom (`and`) assertions; `lia_generic` is a Carcara hole. **Integer-systems certificate added** (commit c19f3ce): the multi-equation Diophantine refutation (P2.4) now emits an "integer Farkas" `DiophantineCertificate` (multipliers λ s.t. `Σ λᵢ·Eᵢ` is a `gcd ∤ const` contradiction row) with an independent `check_diophantine_certificate` re-deriving it from the originals — self-validated, tamper-tested. This is the in-tree route for integer-systems infeasibility that `lia_generic`/Carcara can't check |
| P3.4 | Embedded Alethe checker subset (self-checking) | TODO |
| P3.5 | Alethe for reductions (arrays → Ackermann → int-blast) | TODO |
| P3.6 | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | WIP — **crate started (ADR-0036, commit db18886)**: destination-3 (Lean parity) foundation. `Name`/`Level`/`Expr` + de Bruijn ops (instantiate/abstract/lift) ported from `references/nanoda_lib`, adapted to axeyum's **lifetime-free Copy-id interning** (no `'a` leaks). Faithful level `leq`/`is_equiv`/`simplify` + param subst; Expr with `BinderInfo`; cached `num_loose_bvars`/`has_fvars`. 27 tests incl. translated nanoda level tests + de Bruijn laws. **Type-theory core landed (slice 2, commit e37da7b)**: `whnf` (beta/zeta), `def_eq` (lazy structural + Pi/Lam congruence + eta + proof irrelevance), and checking-mode `infer` (Sort/FVar/App/Lam/Pi/Let, IMax impredicativity) over the **environment-free fragment** — the kernel now TYPE-CHECKS terms (polymorphic identity infers `Π(α:Sort 0),α→α`, etc.). Faithful nanoda port; the env boundary (`Const`/δ, inductives/ι, projections, literal typing) errors explicitly (`KernelError`), never a wrong accept. 52 kernel tests. **Environment + Const δ landed (slice 3, commit f0f6e0d)**: non-inductive declarations (Axiom/Definition/Theorem/Opaque) with `ReducibilityHint`; `Environment` (deterministic `BTreeMap`); `add_declaration` is the trusted gate (type-checks each decl's type-is-a-sort + value `def_eq` declared type); universe instantiation; `infer(Const)`; δ-unfolding in `whnf`; faithful `lazy_delta_step` (height-based side choice, same-const short-circuit, Opaque/Axiom non-unfolding). The kernel now type-checks terms referencing globals (`id := λαx,x` admits + δ+β-reduces under application). 68 kernel tests. **Inductive layer started (slice 4, commit 4457594)**: `Declaration::{Inductive,Constructor,Recursor}` + `RecRule`; `add_inductive` (trusted gate: type whnf's to a Sort, constructor telescopes type-check + end in `I` + **non-recursive** field restriction); **recursor generation** (`I.rec : Π {motive}(minors…)(major), motive major`, with the generated type infer-self-checked) + **ι-reduction** (`I.rec … (c_i flds) → m_i flds`). Scoped to **non-recursive, non-parametric, non-indexed** inductives — enums (`Bool.rec` ι picks the right minor) + structures (`P.rec C m (mk x y) → m x y`); param/indexed/mutual + Prop-subsingleton large-elim DEFERRED (reject explicitly). **Recursive inductives landed (slice 5, commit 24607a9)**: DIRECT recursive fields (field type exactly `I`, e.g. `Nat.succ : Nat→Nat`) now admitted; `mk_recursor` adds one IH binder `motive f_j` per recursive field to each minor (`Nat.succ`'s minor = `Π(n:Nat)(ih:motive n), motive (succ n)`); recursive ι appends a recursive `I.rec … f_j` call per recursive field (`Nat.rec C z s (succ k) → s k (Nat.rec C z s k)`). **The kernel checks AND computes with `Nat` and binary trees** (end-to-end recursive normalization verified; recursor type infer-self-checks). Higher-order/reflexive fields, params, indices still rejected. 82 kernel tests. **Parametric inductives landed (slice 6, commit bc95c21)**: `add_inductive(num_params)` — leading binders are params (fixed across the family), recursive field = `I params` (generalizing bare `I`); recursor abstracts params before the motive and threads them through minors/IH/ctor-apps + recursive ι calls. **`List`/`Option`/`Prod`/`Sum` check + compute** (`List.rec α C cnil ccons (cons α a l) → ccons a l (List.rec … l)`; a length recursion normalizes; recursor types infer-self-check). Indices (`Eq`/`Vector`, a binder between params and the `Sort`) → `IndicesNotSupported` (deferred). 92 kernel tests. **Indexed inductives landed (slice 7, commit 223e81c)**: indices after params; the dependent motive ranges over indices + major; each minor applies the motive to the constructor's OWN index exprs; index-matching ι. **`Eq.rec` (the dependent eliminator used in every equality proof) generates, infer-self-checks, and ι-reduces on `refl`** (`Eq.rec α a motive m a (refl α a) → m`); an end-to-end transport/symmetry normalizes; a 2-ctor indexed family picks the right minor by index. Recursive-indexed (`Vector.cons`) → `RecursiveIndexedNotSupported` (deferred). 97 kernel tests. **The inductive layer now covers non-recursive + recursive + parametric + indexed — essentially all of Lean's inductive families** (bar recursive-indexed/nested/mutual + projections + literal typing + Prop-subsingleton elim). Next: **P3.7 Alethe→Lean reconstruction** (where this kernel finally checks reconstructed solver proofs — the destination-3 payoff) + the remaining minor inductive cases. |
| P3.7 | Alethe→Lean reconstruction (proof terms) | WIP — **foundation laid (commit ab2e615)**: `axeyum_lean_kernel::build_logic_prelude` declares the standard Lean logical foundation (`True`/`False`/`And`/`Or`/`Iff`/`Eq`/`Not`) through the trusted gates, and the kernel **type-checks real proof terms** — And.intro, and-elim (via And.rec), Or case analysis, Eq symmetry transport (checks + ι-reduces on refl), modus ponens, ex-falso (False.rec), and a composite `And A B → And B A`. 15 proof tests. The kernel is a Lean-grade checker of real proofs. **Reconstruction started — Eq fragment (slice 1, commit 56709ef)**: `axeyum-solver` gained a dep on the leaf `axeyum-lean-kernel`; the new `reconstruct` module translates Alethe equality terms to Lean `Expr` (`(= a b)` → `Eq.{1} α a b`) and the **`eq_reflexive`/`eq_symmetric`/`eq_transitive`** Alethe rules into `Eq.rec` proof terms the **kernel type-checks** (`def_eq` against the translated conclusion — the kernel is the checker; a wrong term is rejected). End-to-end transitivity chain reconstructs + kernel-checks; 2 negative soundness tests (wrong conclusion rejected). 11 tests. **End-to-end EUF refutation reconstructed (slice 2, commit 7267b2d):** `reconstruct_qf_uf_proof` walks a REAL `prove_qf_uf_unsat_alethe` proof — `assume` (eq → `h:Eq`, diseq → `h:Not(Eq)`), `eq_transitive`/`eq_symmetric` (n-ary fold + reversed-edge flip), `eq_congruent` (unary, congrArg via `Eq.rec`), and the closing resolution to the empty clause → `h_ne h_eq : False` — into a Lean term the **kernel checks to `False`**. 7 end-to-end instances (transitivity `a=b∧b=c∧a≠c`, longer chain, reversed edge, depth-1 congruence `f(a)≠f(b)`) + 2 negative tests. 17 tests. **Propositional resolution reconstructed (slice 3, commit fc23d4c):** the clausal layer — atom → opaque `Prop`, `(cl l…)` → right-nested `Or`, `(cl)` → `False`; `reconstruct_resolution_proof` builds the resolvent via iterated `Or.rec` (constructive case-split; `em` declared for the classical commitment but unconsumed), pivot-scheduled for the emitter's arbitrary-order RUP hints. **A REAL emitted clausal proof reconstructs end-to-end** (UNSAT CNF → `solve_with_drat_proof` → LRAT → Alethe → kernel-checked `False`). 26 tests. **Both the EUF and the clausal-resolution fragments now close to kernel-checked `False`.** **Tseitin CNF-intro rules reconstructed (slice 4, commit 237d13b):** `reconstruct_cnf_intro_rule` builds all 12 gate-definitional tautologies (`and_pos/neg`, `or_pos/neg`, `equiv_pos1/2`+`neg1/2`, `xor_pos1/2`+`neg1/2`; `xor a b := Not(Iff a b)`) as kernel-checked classical-tautology proofs (em + Or.rec case-split + prelude eliminators); a composite feeds a reconstructed `and_neg` clause through the slice-3 resolution to `False`. 43 reconstruct tests. **P3.7 now covers EUF + clausal resolution + the Tseitin Boolean-gate layer.** **Bitwise QF_BV bitblast reconstructed (slice 5, commit 4b356b3):** bit model — each bit a Lean Prop, variable bit → opaque `((_ @bit_of i) x)`, const → `True`/`False`, `bvnot/and/or/xor` pointwise (`xor` = `Not(Iff)`), `@bit_of i (@bbterm bs)` → `bs[i]`. `reconstruct_bitblast_step` kernel-checks all 7 bitwise rules (`var`/`const`/`not`/`and`/`or`/`xor`/`equal`; the bit-iffs are reflexive under the pointwise model); non-bitwise → `UnsupportedRule`. `reconstruct_qf_bv_proof` walks a REAL `prove_qf_bv_unsat_alethe` bitwise proof → **kernel-checked `False`** (1-bit bvand w/ full cong/trans/`@bbterm` plumbing + width-2 eq). 55 reconstruct tests. **HONEST soundness boundary:** the bit-level Boolean refutation + each bitblast step's bit-iffs are GENUINELY kernel-checked, but the term-level `cong`/`trans`/`equiv` bridge (`(= bvterm @bbterm)` transport) enters resolution as out-of-band-verified clause hypotheses, not yet fused into the single `False` term. **Eq-transport bridge FUSED (slice 6, commit 8c19e23):** the bitwise QF_BV reconstruction is now a CLOSED proof — `False` derived from ONLY the input assumptions + prelude + `em`, **no bridge axioms** (asserted via `declared_axiom_roles()` = `[assume,assume,em]`). Input `(= s t)` → hypothesis `h:⟦B⟧` directly; equiv1/2 → genuine `¬B∨B` tautologies (not assumed); term-level cong/trans deferred (never load-bearing); bit-iffs kernel-checked up front. 58 reconstruct tests. **The bitwise QF_BV unsat fragment reconstructs to a fully-kernel-checked, axiom-free Lean `False` proof.** Remaining for full QF_BV: arithmetic bitblast (`bvadd`/`bvmul` carries). **LRA arithmetic prelude built (commit 6869e49):** `axeyum_lean_kernel::build_arith_prelude` declares an axiomatized linear ordered field (carrier `R`, `add/mul/neg/zero/one`, `le/lt`, order+additive+scaling axioms) through the trusted gate; a **baby-Farkas refutation kernel-checks to `False`** (`le a 0 ∧ le 1 a` → `lt 1 1` → `lt_irrefl` → False). 119 kernel tests. **VERIFIED CURRENT STATE (2026-06-20 — the above history understated coverage; confirmed by reading the dispatch at `reconstruct.rs:1334`):** the `prove_unsat_to_lean` dispatch now reconstructs **8 fragments** to kernel-checked `False` — **QF_BV (bitwise AND arithmetic: `bitblast_add` ripple-carry + `bvneg`/`bvmul`/`bvsub`/concat/extend, memoized-linear carry, closed over assume+em), QF_UF (EUF congruence), QF_UFBV, QF_ABV (via array elimination), datatypes (via simplification), ∀ (quantifier unsat), ∃ (skolem), and QF_LRA (general n-constraint arbitrary-rational `la_generic` Farkas — `try_general_farkas`/`try_mixed_farkas`/`try_strict_cycle`, λ-denominators cleared, ring cancellation via explicit kernel-checked `Eq` rewrites)**. Since `has_arith→Lra`, QF_LIA whose LP-relaxation is Farkas-infeasible ALSO reconstructs (ℤ⊂ℝ). **Genuine remaining proof gaps (the hard frontier):** integer-cut-needing QF_LIA (LP-feasible-but-no-integer-point — needs cutting-plane/Diophantine proof reconstruction), NIA/NRA proofs, strings, FP-arith — each genuinely hard. |

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
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | WIP — committed assertions over arrays/UFs are now scoped as deferred theory assertions and decided by `check_with_memory` through the full pure-Rust dispatcher; one-shot branch assumptions over arrays/UFs are supported by `check_assuming_with_memory` / `check_assuming_core_with_memory`, with a coarse-but-sound full-assumption core on UNSAT. `IncrementalBvSolver` exposes deferred-theory introspection and now admits a narrow warm-safe memory slice: same-index hits collapse to the stored value, literal-distinct index misses skip the unrelated store so concrete-address store chains can expose inner same-index read-backs, constant-array reads collapse to the default value, reads over array-valued `ite`s distribute to scalar branch reads and then collapse dead scalar merge guards / reflexive equalities when both branches simplify to the same value, reads over index-valued `ite`s distribute to scalar branch reads before ROW handling, stores with index-valued `ite`s split to branch-local store/read terms before the generic symbolic ROW equality, scalar equality-over-`ite` plus Boolean-identity cleanup removes residual branch choices when branch values compare to constants, Boolean equality-to-constant and double-negation cleanup remove residual wrappers around symbolic Bool readbacks, Boolean connective cleanup removes constant/idempotent/complement/xor/implication wrappers around predicate-like readbacks, BV bitwise cleanup removes constant/idempotent/double-negation wrappers around BV-valued readbacks, BV arithmetic cleanup removes add/sub/mul/div/rem zero/one, self-subtraction, self-remainder, additive-inverse, and double-negation wrappers around BV-valued readbacks while preserving SMT-LIB zero-divisor totality, BV comparison cleanup removes reflexive signed/unsigned and unsigned endpoint wrappers around BV-valued readbacks, BV slice/extension cleanup removes whole-width extract and zero-bit extension wrappers around BV-valued readbacks, BV shift cleanup removes zero-shift and constant zero/all-ones arithmetic-shift wrappers around BV-valued readbacks, and undecided symbolic-address ROW first prunes syntactically same-index shadowed stores before expanding to a scalar `ite` that stays warm when the base read reduces away. Plain `select(a,i)` reads over BV-indexed array symbols whose elements are Bool or BitVec now abstract to retained warm scalar variables with scoped same-array select-congruence lemmas and replay-projected array models, covering symbolic-base helper loads, predicate/set reads, wide/BV256 storage-style reads whose index or element value needs generic-array projection, and ROW tails whose remaining base read is a memory symbol. Direct equality between supported array symbols is now retained as a scoped warm theory fact: equal-array classes generate cross-array select-congruence lemmas for committed assertions and one-shot assumptions, and SAT models merge equal arrays before replay. Scalar Bool/BV uninterpreted-function applications now abstract to retained warm variables with scoped same-function congruence lemmas and replay-projected `FuncValue` entries, covering keccak-style scalar UF branch constraints including BV256 argument or result values via full-value function entries. Committed assertions and one-shot assumptions encode the simplified/abstracted pure-BV term while retaining the original memory/UF term for replay and, for assumptions, original-term core reporting. `SymbolicExecutor` exposes memory-aware assume/branch/status/model/enumerate calls plus auto route-selection helpers, `assume_auto` and `branch` use the warm memory simplifier/abstraction before deciding whether the one-shot dispatcher is needed, and `SymbolicMemory` provides typed load/store helpers plus compact read-specific write-log helpers over array-backed memory states that skip literal-distinct writes, elide exact-hit guards, and preserve later symbolic aliases. This is a consumer-facing one-shot fallback plus a narrow warm memory/select-congruence/direct-array-equality/UF-congruence admission, not the final warm lazy-array/UF incremental engine: remaining deferred theory checks rebuild through `check_auto`, while the warm BV path still refuses active deferred theories rather than silently ignoring them. Remaining: true warm lazy arrays/UF with learned theory clauses, path-condition CFG/import frontends, and deeper memory model helpers |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | WIP — first frontend-facing primitives landed: `SymbolicMemory` wraps an SMT array memory state, builds `select`/`store`, routes load-equality branch/assume queries through `SymbolicExecutor`'s automatic warm/memory feasibility APIs, and now exposes conservative write-log normalization / compact read-specific read-over-write `ite` construction for frontend memory logs that skips literal-distinct writes, elides exact-hit guards, preserves later symbolic aliases, and uses the auto route; `SymbolicExecutor::assume_auto` and `SymbolicExecutor::branch` keep same-index store/read-back constraints, literal-distinct concrete-address store-chain misses, zero-initialized constant-array reads, simple array-ITE state-merge reads including same-readback merge-guard and tautology pruning, reducible conditional read/write-index paths with scalar equality-over-`ite` cleanup, symbolic Bool readback equality/connective/xor/implication cleanup, BV bitwise/arithmetic/comparison/slice-extension/shift/div-rem readback cleanup, reducible symbolic-address ROW over store chains with same-index shadowed-store pruning, plain symbolic-base Bool/BV array loads via retained select-congruence abstraction including wide/BV256 index or element projection, direct equal-array symbol assumptions/assertions via retained cross-array select congruence and equal-array model projection, scalar Bool/BV UF applications via retained congruence abstraction including wide/BV256 argument or result projection, helper-level load/write-log queries, and default `explore_cfg` branch/assume/status/model queries on the warm BV path when they reduce or abstract, with original-term replay, while remaining general memory/UF still auto-promotes to the memory/theory-aware route; `SymbolicExecutor::explore_cfg` provides a reusable DFS harness over frontend-supplied CFG states, with solver-scope management, infeasible pruning, unknown-safe traversal, and model-witnessed targets; `explore_cfg_checked` adds frontend-supplied concrete witness extraction + replay callbacks and buckets targets into verified/missing-witness/mismatch cases; `TinyBvProgram` is the first reusable small-target frontend, with a validated BV register/memory IR, label-aware line-oriented assembly import with retained label/source metadata, deterministic PC-to-label lookup, typed static CFG edges and basic blocks, deterministic Graphviz DOT export for the basic-block CFG plus trace-highlighted, block-coverage-highlighted, and edge-coverage-highlighted DOT overlays, block-level trace paths, taken-edge trace reports, source-aware trace rows, consolidated witness trace reports, replay-checked test-case generation reports, block-coverage and edge-coverage test-suite reports, register-register equality branches, symbolic instruction lifting, zero-initialized SMT array memory for `Load`/`Store`, model-witness extraction, independent concrete replay, concrete execution traces, and bounded PC/label reachability/safety reports. Remaining: byte-level/binary broader target work, unbounded/certified safety wrappers over richer CFGs, and eventually general warm memory reuse from P4.1 |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | WIP — single-objective `maximize/minimize_lia` + `_bv`/`_bv_signed` already shipped (exponential+binary bound search, Boolean-structured oracle). **Lexicographic multi-objective landed** (`optimize_lia_lexicographic`, 2026-06-18): optimize objectives in order, pinning each at its optimum (`obj≥v`/`obj≤v`) before the next so later ones range over the optimal face — z3's default lex combination. Sound + terminating (bounded composition of the checked single-objective optimizer); `LexOutcome::Stopped` at the first unbounded/infeasible/unknown objective. **BV lexicographic also landed** (`optimize_bv_lexicographic`, signed/unsigned, `bv_uge/ule/sge/sle` pinning) — lexicographic OMT now covers both LIA and BV. **Box** (`optimize_lia_box` / `optimize_bv_box`, independent) **and Pareto** (`optimize_lia_pareto` / `optimize_bv_pareto`, guided-improvement front enumeration, deterministic point/push caps, each point verified Pareto-optimal) modes also landed — **axeyum now has all 3 of z3's OMT modes (box, lexicographic, pareto) across LIA+BV**. BV Pareto covers unsigned and signed objective values, max/min directions, and graceful `Unknown` for out-of-fragment objective values. MaxSAT returns the witnessing model (`max_satisfiable_model`). `minimize_model` / `Solver::minimize_model` provide replay-checked lexicographic counterexample minimization over selected Bool, unsigned-BV<=127, and Int symbols, and the metadata-aware `minimize_model_objectives` / `Solver::minimize_model_objectives` route adds signed two's-complement BV objective order for signed SDK inputs. `produce_evidence_minimized` / `prove_minimized` preserve the default surface, while `_with_objectives` variants expose signed-objective metadata to frontends. `axeyum-property` v0 is now the first typed SDK consumer of that surface: Bool/BV/Int handles, assumptions, proof calls, minimized countermodel lifting, checked `EvidenceReport` exposure plus best-effort standalone Lean modules and stable evidence/trust/Lean summaries through `ProofCertificate`, typed BV overflow predicates, `.equals()` equality aliases, property-owned Bool/BV/Int builder aliases, `Property::all` / `Property::any` Boolean folds, deterministic native-scalar counterexample-to-`#[test]` rendering with caller-owned prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, deterministic multi-case fixture file assembly, direct named/tuple aggregate initializer snippets, and explicit nested aggregate field composition, scalar/tuple/derived-struct `Symbolic` declarations/lifting including signed-order two's-complement fixed-width Rust integers, named-field `symbolic_struct` bundles, and the generated SDK corpus/scoreboard gate with 16 graduated workflows, deterministic executable baseline comparisons for scalar counterexamples, an actual fixed-seed proptest shrunk counterexample, struct and replay counterexamples, proved assertions, assumption-backed proved assertions, and a Kani-style assume/assert counterexample baseline, machine-readable `corpus.json`, DISAGREE=0, and 1/1 Lean-required coverage. Remaining: MILP hardening; broader objective support for minimized counterexamples beyond Bool/BV/Int native scalars; property SDK ergonomics (operator traits, richer replay bodies); richer proptest families and real Kani CLI-backed property corpus comparison; differential validation vs Z3 `opt` |
| P4.4 | SMT-LIB command-surface completeness (declare-sort, reset, get-proof, …) | WIP — broad command surface already parsed (declare-const/fun/datatype(s), define-fun/sort, push/pop, reset(-assertions), check-sat(-assuming), get-proof/model/value/unsat-core/assignment/assertions, set-option/info, get-option, echo/exit); term forms let/forall/exists/`!`/`as` handled. `reset-assertions` is represented and honored by scoped incremental solving; full `(reset)` is explicitly rejected in the shared-arena parse/solve model. The single-result front-door helpers (`solve_smtlib`, OMT, `get-value`, `get-unsat-core`, `get-proof`, `get-assignment`) now replay the command stream for zero-or-one-query scripts, honoring `push`/`pop`, `check-sat-assuming`, and `reset-assertions` instead of flattening scoped scripts; multi-query scripts are rejected there and routed to `solve_smtlib_incremental`. `solve_smtlib_get_model` returns user-declared constants/functions for sat `(get-model)` scripts as Rust IR values, `solve_smtlib_get_assignment` returns active top-level named assertion assignments for sat scripts while filtering popped/reset assertions, and `solve_smtlib_get_assertions` returns exact command-point assertion-stack snapshots rendered from IR while excluding one-shot `check-sat-assuming` literals. The parser records `set-info`, `set-option`, requested `get-info`, and requested `get-option` commands; `solve_smtlib_get_info` returns recorded metadata, axeyum defaults for `:name`/`:version`, computed `:reason-unknown`, and explicit unsupported markers, while `solve_smtlib_get_option` returns recorded/default option values and explicit unsupported markers. **`match` datatype pattern-matching added** (commit d404794, P4.4): parse-time desugaring to nested `ite`/`DtTest`/`DtSelect`, exhaustiveness + arity checked, 11 tests. Remaining: parametric `declare-sort`/`define-sort`, `define-fun-rec`, full `match` for parametric datatypes, full option-driven solver semantics, and textual interactive command output |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | DONE — committed multi-division scoreboard plus Pareto-dominance report. Current regenerated state (authoritative totals live in the generated [SCOREBOARD](bench-results/SCOREBOARD.md) — machine-derived, check it rather than any hand-copied figure): 35 measured rows, DISAGREE=0, and 23 complete per-instance dominance audits under `bench-results/dominance/`. The first `audit now` queue is fully measured; BV-quantified/ABV/AUFBV/QF_ALIA/QF_AX/QF_BV-bvred/QF_BVFP/QF_DT/QF_FF/QF_FP/QF_LRA/QF_LIA/QF_NIA/QF_NRA/QF_UF/QF_UFBV/QF_UFFF/QF_UFLIA exact audits have zero audit errors/timeouts, and the proof/evidence work has moved exact coverage to BV/bitwuzla quantified **4/4**, BV/cvc5 quantified **37/37**, QF_ABV **169/169**, QF_ALIA **6/6**, QF_AUFBV **41/41**, QF_AX **8/8**, QF_BV/bvred **6/6**, QF_BVFP **7/7**, QF_DT **3/3**, QF_FF **24/24**, QF_FP **16/16**, QF_LRA **9/9**, QF_LIA **10/10**, QF_NIA synthetic **32/32**, QF_NRA synthetic **30/30**, QF_UF bounded declared-sort **44/44**, QF_UF overbound declared-sort **4/4**, QF_UFBV/bitwuzla **2/2**, QF_UFFF **8/8**, QF_UFLIA curated **2/2**, QF_UFLIA bounded **6/6**, and QF_UFLIA parent **6/6** dominant. Remaining work is broader proof/Lean coverage plus faster actual decisions on the hard array/UF/arithmetic solve frontier, not standing up the gate. |

### Track 5 — Verified Systems (IR reflection) — ADR-0056, adopted 2026-07-06
| Phase | Title | Status |
|---|---|---|
| P5.1 | Reflection front end (crate-ify the MIR+LLVM reflectors, full `.ll` parser, MIR extraction pipeline, loops→`TransitionSystem`, memory beyond byte arrays) | WIP — **T5.1.1 DONE (`cc695925`, ADR-0057)**: the reflectors are now the real library module `axeyum_verify::reflect` (`src/reflect/{mod,mir,llvm}.rs`, submodules `reflect::mir`/`reflect::llvm`), no longer per-test scaffolding — 8 test binaries (62 tests) rewired to `use axeyum_verify::reflect::…` and green, `missing_docs`+`implicit_hasher` API-hardened, clippy/rustdoc `-D warnings` clean; the crate split is deferred (one consumer today). The prototyped *capability* (rounds Q–U, design log `docs/consumer-track/verify/reflect-common-abstraction.md`): CFG symbolic executors for both IRs over one shared op vocabulary; 16 cross-IR equivalence proofs (MIR≡LLVM per function, LLVM O0≡O2, if-conversion/strength-reduction/umin-idiom validated, hypothesis-gated `unreachable`); 5-shape wrong-transform refutation corpus with replay-checked countermodels; exact panic specs from rustc's own checks (overflow, division `b==0` / signed `∨ (a==MIN ∧ b==-1)`, bounds over all 2^64 indices) with `catch_unwind` witness replay; checksum micro-module end-to-end on both platforms. Remaining T5.1.2–6: token-level `.ll` parser for unmodified compiler output, build-time MIR extraction, automatic loop bridging, `gep`/`load`/`store` + array writes, the semantics gate. Individual proofs are milliseconds — the suites already run as ordinary per-commit tests |
| P5.2 | Contracts & modular verification (`#[requires]`/`#[ensures]`, calls as composition) | TODO — the architectural unlock for cross-function claims; exit: the checksum module re-proves modularly (without the MIR inliner), with a modular-vs-inlined differential gate at DISAGREE=0 |
| P5.3 | Kernel obligations: bounded memory/page-table math, 2-safety/constant-time via self-composition, protocol-FSM refinement | TODO — 2-safety and FSM refinement are unblocked now (self-composition reuses the shared-arena pattern; the spec-side FSM toolkit + PDR/k-induction ship today); page-table math waits on P5.1 memory |
| P5.4 | Fuzz-oracle loop (reflections as differential oracles, countermodels as seed corpora + generated `#[test]`s, honest `unknown`→directed-fuzz handoff) | WIP — **T5.4.1 DONE (`2423eaeb`)**: `reflect::oracle::DiffFuzz` is the reusable differential-fuzz harness (both shapes: reflection≡reflection via `check_agree`, reflection≡real-fn via `check_against`; deterministic LCG+corners; `FuzzReport`/`assert_agreed` for DISAGREE=0). Two suites collapsed onto it (cross-IR differential fuzz, checksum module oracle). Remaining: convert the `llvm_reflection` buffer/mixed-width loops (T5.4.1 residual); countermodels→seed corpora + generated `#[test]`s (T5.4.2); `unknown`→directed-fuzz handoff (T5.4.3); coverage accounting (T5.4.4) |
| P5.5 | External target, measured (Maestro / Hubris / Tock / Asterinas-OSTD slice / rust-sel4 task) | TODO — the measured-not-seeded rule applies doubly: the exit is a committed scoreboard result on someone else's code (module verified or bug found+reproduced), DISAGREE=0, wall-times recorded |

## Changelog

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

- **2026-07-03 (evening) — the keystone is banked (ADR-0055), its
  verification debt paid, and the code↔LIA bridge moves strings again:
  QF_S 61, totals 680.**
  - (`5707563b`) **Default-on verification debt paid** (the 5th review's §3):
    CdclT termination under adversarially non-monotone theories proven by a
    20,000-run MockTheory property + a 16M-step budget belt (no livelock
    found — the trigger-literal invariant forces strict backjump progress);
    the congruence checker's substitution expansion was a REAL defect
    (doubling chains stack-overflow at k≥14, reachable per-assert) — now
    size-budgeted (`MAX_EXPANSION_COMPONENTS=4096`, declines in ~100µs);
    closed-universal polarity pinned safe (a ∀ under or/not/ite never
    reaches the lever) + 400 nested-polarity differential cases DISAGREE=0.
  - (`dd732e2b`) **ADR-0055 accepted**: the QF_S online CDCL(T) route is
    default-on (ratifying the landed second-chance ordering that moved the
    scoreboard); QF_UF online stays an opt-in parity twin with recorded
    default-on criteria; new theories arrive online-first.
  - (`122c3c27`) **The code↔LIA bridge** (5th review's #2 lever): `str.to_code`
    twins a fresh Int with the universally-true domain fact (`len=1 ∧
    0≤c≤0x2FFFF` ∨ `len≠1 ∧ c=-1`) + single-char code↔equality links; the
    ADR-0052 abstraction now also upgrades `unknown` verdicts (a sound
    relaxation refuting is unsat regardless of what produced the unknown —
    the three str-code census files were actually blocked on the 32-bit
    bit-blast, not the gate). Faithfulness: the Unicode cap 0x2FFFF, not the
    byte model's 255 — fixing a latent wrong-unsat risk (regression-guarded).
    **QF_S 58→61, QF_SLIA 12→13, totals 676→680 decided, 627
    oracle-compared, DISAGREE=0**; lex-order (`str.<=` over variables) and
    seq.update honestly declined. String day total: **QF_S 52→61 (+9)**.
  - (`c5f181b9`) **T-C.5 REGEX MEMBERSHIP LANDED (ADR-0054)** — the largest
    census demand (15 files) attacked: full SMT-LIB RegLan → code-point
    derivative-engine translation; single-variable DFS witness search with
    MANDATORY independent-matcher replay (sat); **re-checked
    derivative-emptiness certificates** (unsat — complete nullable-free
    closure, independently re-verified); front-door + bench routing.
    **QF_S 61→67 (50%, PAR-2 4.372→2.928), QF_SLIA 13→14; totals 687
    decided / 632 oracle-compared / DISAGREE=0.** Fuzzes vs BOTH oracles:
    z3 627 jointly decided, cvc5 175, plus a 2000-case brute-force
    differential — all zero disagreements. Census remainder honestly
    unknown: membership+extended-fn coupling (Phase D), disjunctive
    membership Boolean shapes (next: membership atoms in the online CDCL(T)
    route), re.all+prefixof. **String day total: QF_S 52→67 (+15, 39%→50%),
    with every verdict oracle-verified and DISAGREE=0 held throughout.**
  - (`f5b00c72`) **P0 incident, resolved same evening — a vacuous-sat HARNESS
    hole, engine exonerated.** CI's corpus_regression reported 1 DISAGREE at
    `c5f181b9` (instance1079-re-loop-cong: declared+z3 unsat, reported sat).
    Direct probes cleared the engine, matcher, translation, and front door
    (all correct on the shape; `solve_smtlib` decides the file unsat). Root
    cause: T-C.5 made membership scripts word-only-fallback eligible (EMPTY
    flat assertion view), and corpus_regression handed that empty view to
    `check_auto` — the vacuous empty conjunction. The same class was fixed
    for the bench in `f5d3e1ec`; this harness was never taught. Fixed:
    empty-flat-view scripts decide via the front door (118 agree, 0
    DISAGREE). **Lessons queued (task #29): audit the other 11 parse_script
    consumers + a structural guard; the pre-push hook must gate the pushed
    SHA, not the working tree (it blocked this validated fix over unrelated
    WIP); corpus_regression joins the standard string-slice gate list.** A
    second suspected wrong-sat (fuzz seed 215) was confined to an
    UNCOMMITTED feature WIP — quarantined on `wip/t-c5-membership-atoms`
    with a do-not-merge note; verified absent at HEAD.
  - Also: the pre-push compile gate is live (`hooks/pre-push`,
    `core.hooksPath`), the cap audit found only two CI-scaled sites (both
    healthy), ADR-0051/0053 flipped to accepted, and the tracker count-rot
    was replaced with scoreboard references (5th review applied, `1cb7155f`).
- **2026-07-03 (afternoon) — the P1.5 keystone opens, UF×NRA lands, Phase C
  engine core lands, and the 4th review is applied.**
  - (`a3460101`) **P1.5 slice (a): the generic online CDCL(T) driver** —
    `CdclT<T: TheorySolver>` with 1-UIP learning over the MIXED implication
    graph (Boolean + theory reason clauses from e-graph `explain` cores),
    lockstep theory push/pop, deadline in the search loop. EufTheory wired
    first, opt-in entry (`check_qf_uf_online_cdclt`), default dispatch
    unchanged. Parity: 2500-instance online-vs-offline house fuzz, 2500
    agree, 0 DISAGREE; the z3-gated QF_UF fuzz (3000) unchanged; no
    TheorySolver trait changes.
  - (`c9d332c1`, `c924fcb0`) **P1.5 slice (b) + front-door wiring: the word
    core runs inside a real CDCL(T) loop.** StringTheory adapter (per-assert
    certified refutation checks; conflict explanations map the checker's
    premise indices to trail literals; sat only via arrangement-search model
    + full replay) — and the fuzz found a REAL CdclT bug (1-UIP path_count
    underflow on non-current-level theory cores; fixed by always including
    the trigger literal — a sound superset). Census str002-class disjunctive
    shapes DECIDE; 1500-case z3 fuzz 549 decided (157 sat/392 unsat)
    DISAGREE=0. Front door + bench wired via the new `word_skeleton` parser
    side channel (Boolean structure over word atoms, all-or-nothing);
    four fuzzes/crosschecks green incl. the cvc5 second oracle. **Honest
    re-measure: three string divisions UNCHANGED** — the 6 reachable census
    unsats need suffix-cancellation/quadratic/length refutation shapes the
    certified refuter deliberately does not close yet (the named next
    lever); the other ~116 declines are regex/length-bridge territory.
  - (`4d039c5a`, `09e40e41`, `5ad952b8`) **Word-unsat hardening COMPLETE
    (all four 4th-review demands):** cvc5 1.3.4 static as a SECOND
    differential oracle (word fuzz 401/401 agree incl. all 305 unsats;
    corpus 90/90; skip-when-absent); the normalize denotation fuzz (24k
    adversarial pairs at the checker's one shared primitive); mutation
    testing (175 mutants — zero dangerous survivors in the accept paths, 21
    killing tests); and Alethe certificates for word-conflict derivations
    (verify-before-record, 7 tamper modes rejected, 600-refutation
    property; the `axeyum_word_clash` custom-rule Carcara hole disclosed
    exactly as `lia_generic`'s).
  - (`881c76f6`) **UF×NRA combination made explicit (P1.6 slice)** — the
    eager-Ackermann→NRA composition existed *accidentally*, four declining
    routes deep; now an intentional, telemetry-recorded route with replay-
    gated sat, threaded deadline, and a documented boundary. NEW 700-case
    `qf_ufnra` differential fuzz DISAGREE=0; both shared-path guards
    (nra/nia fuzzes) DISAGREE=0; issue5836-2 decided; the linear QF_UFLRA
    path provably untouched.
  - (`0acf3535`) **Phase C engine core (T-C.1/2, ADR-0054)** — interval-set
    code-point predicates + transition-regex Brzozowski derivatives with
    native `R{n,m}` (no pre-unrolling: `R{100,200}` closure = 202 states,
    linear) + the independent reference matcher. Trust anchor: the
    fundamental derivative theorem property-tested over 20,000 engine-vs-
    matcher cases, zero disagreements.
  - (`686087cd`, `6b17e70c`, `3c13df63`) **4th periodic review applied +
    the census** — scoreboard counts made rot-proof (links, not copies;
    machine totals 674/992), multi-agent git hygiene promoted from private
    memory to CLAUDE.md + the contributor guide, the CI docs-filter leak
    actually fixed (`scripts/**`/`justfile`), ADR-0054 proposed, and the
    review's sequencing recorded: P1.5 integration outranks Phase-C
    broadening; word-unsat hardening (cvc5 second oracle, mutation testing,
    normalize fuzz, Alethe emitter) queued before any parity language.
- **2026-07-03 — 🟢 FIRST GREEN CI RUN IN 200+ RUNS** (`10e29199`, all 8 jobs).
  Main had been red for 198+ consecutive runs; the repair was an onion peeled
  over two days, each layer only visible after the previous one:
  MSRV 1.88/let-chains, rustdoc intra-doc links, rustfmt drift, cargo-deny
  wildcard paths, ~100 clippy sites plus the final `axeyum-verify`
  `too_many_lines` (red since `70f2dce2`; local scoped clippy never caught
  it — the lesson is the workspace `-D warnings` gate, not scoped runs),
  the evidence-suite exponential DAG walks + budget flakes, the z3-sys
  prebuilt-download 403 (now authenticated via `READ_ONLY_GITHUB_TOKEN`) +
  the missing `/usr/bin/z3`, runner disk exhaustion, hardware-relative
  frontier ratchets + the budget-excused cap, QF_AX `build_model` hash-order
  nondeterminism (a 12% verdict flake → 0/200), route-trace telemetry
  invariants, the uflra fuzz deadline hole, and runner-pool saturation
  (queue-and-complete concurrency + a docs-only CI split + cancelling 11
  doomed runs). The test job runs ~4.5h because the z3 differential fuzzes
  execute at full iteration counts on shared runners — acceptable for now;
  a CI-scaled iteration count is the queued follow-up if it becomes the
  bottleneck.
- **2026-07-03 (early)** — **The nia_unsat frontier regression (40→23) found,
  bisected, and fixed; the uflra fuzz-hang class closed; Phase B started; two
  more CI onion layers.**
  - (`4f27961e`) **nia_unsat frontier regression**: commit `4fe9491f`
    ("certify bounded QF_NIA dominance", 06-25) had put a 10⁶-case
    exhaustive-evaluation probe ahead of the exact int-blast on every
    bounded-int query. UNSAT must walk the whole box, so mid-size boxes ground
    for seconds where the blast decides in tens of ms — the frontier family
    fell **40 → 23** (n=14: 86ms→848ms; whole family 2.2s→46s) and SHIPPED.
    Caught by the frontier ratchet only during a full local sweep, 8 days
    later; git-bisected across 829 commits. Fix: the pre-blast probe caps at
    10⁴ cases (where enumeration genuinely beats blast setup) and the full
    10⁶ budget moves to a post-decline fallback, so boxes the blast cannot
    encode keep their only decider. Frontier restored 40/40 in 2.19s; all 8
    frontier families green; NIA differential fuzz DISAGREE=0 (1500
    instances). **Lesson recorded: the ratchet must become a pre-merge gate —
    a 17-point capability regression should not need post-hoc bisection.**
  - (`3b5bbcf0`) **uflra fuzz-hang class**: the two 600-case UFLRA
    differential fuzzes ran the budget-blind offline reference
    (`check_with_uf_arithmetic`) with no `config.timeout` and hung unbounded
    (a 3.9h binary was observed). Measured first: the *online* path decides
    all 600 in 0.02s — the offline reference was the grinder. Every
    offline-reference test call now carries a per-case budget (expiry →
    `Unknown`, never a wrong verdict), and the latent un-threaded-deadline
    sibling of the UFLIA `3cd6c810` hole in the UFLRA interface-search DFS is
    threaded (checked per DFS node). Suite: unbounded-hang → 44s/21-pass;
    qf_uflra fuzz 1500 instances DISAGREE=0.
  - (`271ecaa2`) budget-excused cap recalibrated 4→12 locally after verifying
    across three commits that the decided/agree counts are byte-identical and
    only wall-clock excusals moved (quiet-box floor is 8/300) — an audit item
    remains: excused-cap loosenings are a place real regressions can hide.
  - (`10e29199`, `424c761c`) two more CI onion layers: the workspace-clippy
    red (`too_many_lines` in `axeyum-verify`, red on every run since
    `70f2dce2` — local scoped clippy never caught it) and the z3-sys prebuilt
    download 403 (anonymous GitHub API rate-limit; now authenticated via
    `READ_ONLY_GITHUB_TOKEN`). Cancelled 11 already-doomed queued runs to
    unclog the runner pool; `424c761c` is the first run carrying the full fix
    stack.
  - (`90592350`, `c5590668`, `bfc32805`) **Strings Phase B started** —
    ADR-0053 + `axeyum-strings` + T-B.1/T-B.2 (see Current focus).

> Changelog entries through 2026-07-02 archived: [docs/status-archive/changelog-through-2026-07-02.md](docs/status-archive/changelog-through-2026-07-02.md)
