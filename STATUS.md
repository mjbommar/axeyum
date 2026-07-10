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
  recovered — QF_S is now 82/134 (61%), QF_SEQ 26/33, QF_SLIA 18/50 (36%)** after
  Phase B/C/D, lex-order, the code↔LIA bridge, and #49 (membership-over-concat).
  The dominant remaining strings gap is now QF_SLIA (36%), whose lever is the
  **LenAbs length/LIA bridge (P2.7 Phase A, task #53)** — see the current focus.
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
  Next: structural store/ITE/default class projection, warm ownership, online
  ROW/extensionality/equality-chain proof logging, and the low-load aggregate.
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
  `SymbolicExecutor` (path exploration + test-suite enumeration + path-condition
  optimization), and self-rechecking certificates (`UnsatProof::recheck`,
  `SafetyCertificate::recheck`, `EndToEndUnsatOutcome::recheck`).
- These map onto Track 4 (use cases) and Track 3 (the recheck family); the plan
  records what remains around them.

## Phase status

### Track 1 — Engine & Performance
| Phase | Title | Status |
|---|---|---|
| P1.6o | Array-valued UF results on the canonical array bus | **DONE (ADR-0084)** — IR/SMT-LIB and abstraction admit finite Bool/BitVec array results; application reads retain semantic e-graph parents and fresh-array projection owners. Final classes union observations before array-first/function-second projection and original replay. Stores/ITE/equality/nested-UF controls, 288 analytic/front-door/Z3 comparisons, 815 solver tests, and the exact-SHA gate pass. Structural store/ITE/default class ownership, warm reuse, and proofs remain |
| P1.6n | Bounded dynamic interface atoms | **DONE (ADR-0082)** — `CdclT` explicitly maps appended SAT variables to aligned theory atoms; `EufTheory` grows equality metadata over pre-observed sides; exact BV grows in its owned arena. Candidate-violated UF, explanation-guarded parent-select, and bounded extensionality interfaces now refine inside one retained search. One-round mechanism/backtracking/cap/scale gates, 809 solver tests, and 2,304 eager/front-door/Z3 comparisons are clean. ADR-0084 subsequently adds application-parent projection; structural new-term events, warm models, and proofs remain |
| P1.6m | Dynamic in-search ROW insertion | **DONE, bounded local-atom slice (ADR-0081)** — each store site reserves three atoms dormant; a violated candidate activates them through two permanent valid ROW clauses and resumes the same `CdclT` with learned/phase/activity state retained. Hit/miss, nested-site, replayed-branch, UF-index, inactive-propagation, and exact-cap gates pass; 807 solver tests + 1,920 comparisons are clean. ADR-0082 subsequently generalizes retained-search growth to pair-generated scalar atoms |
| P1.6l | Explanation-guarded store-parent select scheduling | **DONE, original outer-round slice (ADR-0080)** — original store terms join final e-class grouping; only candidate-violated equal-index/unequal-result pairs materialize, distinct-parent lemmas retain merge guards, and lazy ROW stays independent. Same/congruent/alternate/unrelated/UF-index/80-parent gates pass. ADR-0081 moves local ROW into one search and ADR-0082 moves the pair-generated select interface into that search; new-term ITE/default/UF events, non-symbol/warm models, and proofs remain |
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
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. **CDCL(XOR) foundation landed** (`gf2`/`xor_extract`/`xor_propagate` in `axeyum-cnf`) — the path-2 multiplier-wall attack: a sound GF(2) Gaussian engine + exact XOR-gate extraction + an entailment-checked propagation pass; slice 4 wires it into the live preprocess pipeline (measured). Vivification / glue tiers remain |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). **T1.2.4 elim_unconstrained landed** (`axeyum-rewrite::elim_unconstrained`): a variable occurring once under an invertible BV op (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`) makes that subterm unconstrained → replaced by a fresh var, operator dropped (Z3's `elim_unconstr`); peels nested layers, terminates. Model-sound via the trail (`x := op⁻¹(u,w…)`; orphaned operands defaulted, sound by the inverse identity); wired into `check_with_preprocessing` after solve_eqs (opt-in, default-off per ADR-0034). `bvumulo` now uses the word-width threshold encoding `a > all_ones / b` instead of a doubled-width multiplier, so BV256 overflow checks no longer build BV512 multiplication terms. 6 unit (incl. 300-trial randomized reconstruction) + 2 solver end-to-end plus focused IR overflow/shape coverage. Next: measure on the public p4dfa slice; then max_bv_sharing / bv_slice / AIG 2-level (T1.2.5–T1.2.9) |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | WIP — the proof-producing core `solve_with_drat_proof` (`proof_sat.rs`) modernized: **VSIDS activity branching** (bump conflict-side vars, MiniSat-style decay, rescale-on-overflow; highest-activity unassigned var, ties to lowest index), **phase saving**, and **Luby restarts**. Sound by construction — every emitted clause is RUP and the proof is DRAT-checked, so a heuristic bug only slows search. All 231 cnf tests pass (incl. the 400-CNF differential vs BatSat + a new pigeonhole-4→3). NB the modern CDCL(XOR) core in `xor_cdcl.rs` already has VSIDS/Luby/LBD. Remaining: arena + packed watches, chronological backtracking; wire a modern core into the default path |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. **Slices a+b LANDED 2026-07-03** (`a3460101`,`c9d332c1`): the generic online `CdclT<T: TheorySolver>` driver (1-UIP over the mixed implication graph, lockstep theory push/pop, deadline in the loop; EufTheory parity 2500/2500 vs offline, z3 QF_UF fuzz unchanged) + the StringTheory adapter (per-assert certified refutations, premise-index→trail-literal explanations, replay-gated sat; census disjunctive shapes decide; 1500-case fuzz DISAGREE=0; found+fixed a real 1-UIP underflow on non-current-level theory cores). Front-door QF_S wiring landed same day (`c924fcb0`). **2026-07-09/10 DFS slices:** generic LIA/LRA propagation, conservative StringTheory equality consequences, canonical QF_UF/LIA/LRA/UFLIA/UFLRA dispatch, deterministic VSIDS/phase/Luby/LBD search, bounded warm EUF+BV, aligned array-equality atoms, explanation-guarded base/store/application-parent readout, finite Bool/BV array admission, retained-search ROW, ADR-0082's explicit mapped dynamic theory-variable growth, ADR-0083's deadline-aware wide BV construction, and ADR-0084's array-result projection are live on the shared driver. Remaining: broader corpus timing, within-level BV core precision when measurement justifies it, structural non-symbol class projection, model/proof integration, and opaque-heavy arithmetic participation |
| P1.6 | Theory combination (th_eq bus, interface equalities) | WIP — EUF+LIA/LRA dispatch and canonical QF_UFBV/QF_ABV/QF_AUFBV combination are live. ADR-0066–0070 establish exact BV/EUF interfaces and replay-guided UF refinement; ADR-0071/72/73 add select congruence, lazy ROW, and bounded equality/diff observations; ADR-0074 adds majority-default models; ADR-0077 puts equality flags on the live e-graph and direct-symbol classes on one model; ADR-0078/0080 schedule explanation-guarded base/store-parent reads from final e-classes; ADR-0079 admits every Bool/BitVec component combination without changing broader fallbacks; ADR-0081/0082 insert ROW and pair-generated scalar UF/select/extensionality interfaces inside one retained search; ADR-0083 bounds wide scalar lowering with cumulative admission plus cooperative deadlines; ADR-0084 adds finite-scalar array-valued UF results and final-class-owned result projection. Array-first/function-second projection and original replay gate SAT; eager routes remain fallbacks/proof producers. ADR-0052 closes the recorded bounded-string marker. Remaining: opaque-heavy arithmetic admission/model lifting, structural store/ITE/default class projection, non-symbol/warm class models, proof integration, and a broader low-load aggregate remeasure |
| P1.7 | PBLS local-search BV engine (portfolio) | WIP — **word-level WalkSAT landed** (`solve_local_search` + `PblsBackend`, `pbls.rs`): keeps a concrete Bool/BitVec(≤128) assignment, scores by evaluator-falsified assertions, nudges a variable in an unsatisfied assertion (greedy + WalkSAT noise + random restarts) toward a model. One-sided + sound: `Sat` only with an evaluator-verified model, never `Unsat`, `Unknown` (incl. out-of-scope sorts) otherwise. Read-only on the arena (fits the trait); deterministic (fixed seed, explicit budgets). 4 unit + an ignored 150-formula differential vs the eager backend (never contradicts). Remaining: integrate as a portfolio strategy; tune moves/budgets; measure on satisfiable corpora |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO — Codex review recommends promoting this from cleanup to risk control: split `solve()` into explicit tactic contracts with fragment predicates, transformation class, replay/proof obligation, resource behavior, and benchmark-visible per-step metrics |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | WIP — **destination-2 lever measured & scoped** (commits beee599/9846349, `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`). KEY FACT: lazy abstraction-refinement bit-blasting (`solve_lazy_bv_abstraction`, ADR-0019) is **built but NOT wired into default `solve()`/bench** — so the "~2-3/113 public QF_BV" picture is the *eager* mountain-builder. Measured (`tests/lazy_bv_curated_measure.rs`): lazy decides **incidental-heavy-op** cases with 0 multiplier blasts (`x=1∧x=2∧r=p·q` → unsat ~0ms, 0 refined), cracks `calypto_9` (sat, 2 ops refined), is a safe no-op when `ops=0` (public files), no shortcut on essential multiplier-equivalence. Next (coordinate on shared bench): lazy-bv bench backend → measure public 113 (DISAGREE=0) → opt-in `SolverConfig::lazy_bv` strategy → default-on ADR after net benefit. The highest-ROI perf move is wiring+measuring a built CEGAR bit-blaster, not a new algorithm |
| P2.2a | Deterministic majority-default array projection | **DONE, symbol + array-result class slice (ADR-0074/0077/0084)** — votes count distinct observed indices, ties use stable smallest-value order, and only non-default overrides remain. Candidate-true direct-symbol classes and congruent array-valued application result owners union observations before one shared model is built; transitive and split-read SAT replay. Remaining: structural store/ITE/default class ownership, nested/extended arrays, and warm reuse |
| P2.2b | Candidate-triggered cross-equality observations | **SUPERSEDED (ADR-0076 → ADR-0077)** — the queue exposed the missing transitive case but duplicated ordinary equality reasoning. Flags now retain their original equality on `EufTheory`; no cross-diff path is built |
| P2.2c | Canonical e-graph equality + class-owned models | **DONE, symbol + array-result slice (ADR-0077/0078/0084)** — live backtrackable EUF handles array reflexivity/transitivity/congruence; direct symbols and fresh array-valued application result owners share models by final class, while base/store/application reads follow explanation-guarded class merges. Conflict/stress/transitive/alternate-path/backtracking/80-array and split-result gates pass. Structural store/ITE/default class ownership plus warm reuse remain |
| P2.2d | Finite scalar component coverage | **DONE (ADR-0079)** — Bool/BitVec index and element combinations share canonical theory/model/replay; generic mixed-component models replay, Bool-only UF+array dispatches, and Int components remain outside admission. Two public unknowns become decided and 384 new comparisons are clean |
| P2.2e | Structural store-parent scheduling | **DONE, outer-round slice (ADR-0080)** — each store read retains its original parent, joins final-class candidate select scheduling, and independently remains a lazy ROW site. Distinct store terms carry explanation guards; same-parent, branch, unrelated, UF-index, and 80-parent scale gates pass. The 384-comparison structural matrix brings the clean total to 1,536; ADR-0081 subsequently moves the local ROW obligation inside one search |
| P2.2f | Dynamic local ROW final-check | **DONE, same-search slice (ADR-0081)** — bounded per-store atoms are dormant until a violated candidate adds permanent ROW clauses; learned/phase/activity state survives and ordinary conflict analysis changes branches. Hit/miss, nested, UF-index, replay, inactive-propagation, and exact-cap gates pass; the 384-comparison matrix brings the clean total to 1,920 |
| P2.2g | Dynamic scalar interface final-check | **DONE, same-search slice (ADR-0082)** — candidate-violated UF, explanation-guarded base/store-parent select, and bounded equality/extensionality interfaces append aligned atoms over pre-observed e-graph terms and resume one retained search. Former two/three-round controls pin one round; the 384-comparison matrix brings the clean total to 2,304 |
| P2.2h | Array-valued UF result projection | **DONE (ADR-0084)** — canonical ROW retains application parents and fresh-array projection owners; final e-classes union observations before array-first/function-second projection. Stores/ITE/equality/nested-UF controls and 288 analytic/front-door/Z3 comparisons pass with replay and zero disagreements |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | WIP — eager elimination/certifying fallback remains (ADR-0010). Canonical QF_ABV/QF_AUFBV has replay-guided base-select congruence (ADR-0071), lazy ROW (ADR-0072), bounded equality/diff observations (ADR-0073), majority-default models (ADR-0074), live e-graph equality plus direct-symbol class models (ADR-0077), explanation-guarded base/store-parent scheduling (ADR-0078/0080), Bool/BitVec finite-scalar component coverage (ADR-0079), same-search ROW plus pair-generated scalar interface insertion (ADR-0081/0082), deadline-aware scalar lowering/admission (ADR-0083), and array-valued UF result projection (ADR-0084). Array-first/function-second projection and replay gate SAT; cloned probes preserve fallbacks. All 2,592 comparisons are clean, including 384 Bool/mixed, 384 structural-store, 384 dynamic-ROW, 384 dynamic-interface, and 288 array-result analytic/front-door/Z3 checks. The focused nine-row cvc5 QF_AUFBV rerun is 7 SAT / 1 budget unknown / 1 unsupported with zero disagreements/replay failures; ADR-0078's broader low-load 1 s aggregate remains QF_ABV 187/193 and QF_AUFBV 49/53 pending comparable remeasurement. ADR-0075 checks direct select congruence externally. Remaining: structural store/ITE/default class projection, non-symbol/warm class models, nested/extended arrays, and ROW/diff-witness/equality-chain/online proof integration |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | WIP — **multi-equation Diophantine infeasibility** (`prove_lia_unsat_by_diophantine`, commit 96f07a3): a conjunction of integer equalities that is rational-feasible but **integer-infeasible** is UNSAT — fraction-free Hermite-style integer Gaussian elimination reports a contradiction row (`0=c` or per-row `gcd ∤ rhs`), deciding the case B&B can't terminate on for unbounded vars and the single-equation GCD misses (e.g. `x+y=0 ∧ x−y=1 → 2x=1`). **Strictly generalizes & replaced** the single-equation `prove_lia_unsat_by_gcd` in dispatch (no regression). Sound (only integer-preserving row ops; `checked_*` → "not refuted" on overflow, never a wrong unsat; SAT systems never refuted, negative-tested). 11+2 tests. Remaining: Gomory/cube cuts; inequality-integrated cuts |
| P2.5 | NRA: incremental linearization → nlsat/CAD | WIP — linear-abstraction + sign/zero lemmas + McCormick + spatial B&B + point-lemma refinement already shipped. **Added threshold-1 monotonicity lemmas** — growing (`a≥1 ∧ b≥0 ⇒ r≥b`, decides `x≥1 ∧ y≥1 ∧ x·y<1`) and shrinking (`0≤a≤1 ∧ b≥0 ⇒ r≤b`, decides `0≤x≤1 ∧ y≥0 ∧ x·y>y` where only one operand is bounded so McCormick can't apply); two-operand only — **plus a refinement overflow safety net** (`too_large_to_refine`: stop refining past a 2³¹ magnitude bound, → `unknown` not a panic; hardens the exact-rational simplex against escalating witnesses). **Sum-of-squares lemmas landed (2026-06-18)** — `sos_lemmas`: for a pair `a,b` with `a·a`/`b·b`/`a·b` all abstracted, add `(a±b)² ≥ 0` over the result vars (sound), restoring the cross-product correlation independent abstraction drops, so **`a²+b² ≥ 2ab` / AM–GM₂ is now PROVED** (the Spivak SOS-frontier test promoted prompt-`Unknown`→`Unsat`; negative test confirms `a²+b²=2ab` stays sat). 26 NRA + 5 Spivak tests. **Since then (2026-06-28…07-02, see the changelog + [SCOREBOARD](bench-results/SCOREBOARD.md)): the CAD arc landed** — bignum algebraic core in `axeyum-ir` (ADR-0044/45/46), a 2-var-complete / N-var decision-complete fuzz-gated CAD, coprime-split projection, first-class `/0` division witnesses (`124e18aa`), and five z3-gated adversarial differential fuzzes at DISAGREE=0. **2026-07-06/07 arithmetic arc (decomposition `fcbde209`): QF_NRA 21→27/38 (71%)** — `/0` witnesses + sat-witness probe + threshold-1 (`5cc63a15`, closed `issue9164-2`), the `a²=−k` even-power-equality (`631be06f`), the `nra_even_power` frontier wire-in (`e0e24085`, `nra_degree` 2→40), coordinate sat-witness for >4 reals (`80206579`, budget-marginal); **and the parallel QF_NIA arc drove cvc5 21→33/39 (85%): div/mod Euclidean linearization (`a946f925`+P0 fix `52f3b1d1`) + `iand` bit-blast (`c5a829a3`) + congruent Ackermann div/mod-by-zero (`b91dd918`, recovered div.01/minimal_unsat_core/div.08 + closed a pre-existing wrong-sat) + `int.pow2` value-table axioms (`fb2da08b`, +8).** Remaining is genuinely hard: 7/12 QF_NRA residue is multi-week CAD/nlsat/transcendental (Boolean-CAD, MetiTarski, degree-10) — the *funded engine arc* (ADR-0058 proposed), not a slice; NIA's bounded levers are now largely harvested (div/mod-0, iand, pow2 all landed). |
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
| P5.3 | Kernel obligations: bounded memory/page-table math, 2-safety/constant-time via self-composition, protocol-FSM refinement | WIP — **T5.3.1 (branch leakage) DONE (`ac7494f0`)**: `reflect::hyper::control_flow_ct_goal` proves **constant-time** by self-composition — the MIR reflector records `switchInt` scrutinees as control-flow leakage (`reflect_mir_params_with_leaks`), and two runs (shared-public / distinct-secret) must leak identical branch decisions. `constant_time.rs` (4 tests): public-predicated PROVED CT while its output is refuted secret-independent (the crisp distinction), secret-predicated REFUTED with a replay-checked witness, branch-free trivially CT. Residual: memory-index (cache-timing) + LLVM-side leakage; page-table math waits on P5.1 memory (T5.1.5); FSM refinement (T5.3.3) unblocked next. 2026-07-08 provable-security scout adds a future crypto micro-suite demand signal here (constant-time kernels + transcript/protocol examples), after current P5.3/P5.4 obligations stabilize |
| P5.4 | Fuzz-oracle loop (reflections as differential oracles, countermodels as seed corpora + generated `#[test]`s, honest `unknown`→directed-fuzz handoff) | WIP — **T5.4.1 DONE (`2423eaeb`)**: `reflect::oracle::DiffFuzz` is the reusable differential-fuzz harness (both shapes: reflection≡reflection via `check_agree`, reflection≡real-fn via `check_against`; deterministic LCG+corners; `FuzzReport`/`assert_agreed` for DISAGREE=0). Two suites collapsed onto it (cross-IR differential fuzz, checksum module oracle). Remaining: convert the `llvm_reflection` buffer/mixed-width loops (T5.4.1 residual); countermodels→seed corpora + generated `#[test]`s (T5.4.2); `unknown`→directed-fuzz handoff (T5.4.3); coverage accounting (T5.4.4) |
| P5.5 | External target, measured (Maestro / Hubris / Tock / Asterinas-OSTD slice / rust-sel4 task) | TODO — the measured-not-seeded rule applies doubly: the exit is a committed scoreboard result on someone else's code (module verified or bug found+reproduced), DISAGREE=0, wall-times recorded |

## Changelog

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
