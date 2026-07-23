# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

> Two lanes write here. The **solver/engine lane** owns *Current focus* below.
> The **consumer-integration lane** owns its own section (immediately following)
> so the two never edit the same lines. See
> [PLAN.md § Consumer-track integration](PLAN.md#consumer-track-integration-2026-06-27-converge-the-apps-onto-main).

## Project reality check (updated 2026-07-21)

**Measured status vs the [north star](PLAN.md#where-we-are-vs-the-north-star--measured-reality-check-2026-06-28):
legacy baselines sound, full-library P0 fixed on `main` with slice revalidation
open; parity not yet reached, the road there fully mapped.** The remaining
decide-rate / performance / proof-coverage work is decomposed into sized,
exit-criteria'd tracks we advance one increment at a time.
- **Soundness:** the legacy 35 measured baselines remain at `DISAGREE = 0`, but
  the 2026-07-22 full-library run found a real QF_ABVFP/QF_BVFP wrong-`sat`:
  exact FP cancellation under RTN was incorrectly forced to `+0`. The add/FMA
  convention is fixed on `main`, bit-for-bit all-mode tests and a 600-script cvc5
  differential sweep are green, and both preserved full queries now return
  `unsat`. The complete QF_FP/QF_BVFP/QF_ABVFP selected slices must return to
  DISAGREE = 0 before the broader soundness floor is called restored. The same
  stale run also exposed a distinct QF_AUFLIA wrong-`unsat` on the declared-`sat`
  `pipeline-invalid.smt2`. Current `main` reproduced it, and cvc5 1.3.4 plus an
  Axeyum parse/write round-trip both returned `sat`, ruling out stale-binary and
  parser artifacts. The lazy-ROW AUFLIA adapter now converts unchecked scalar
  refutations to `unknown`, preserving the existing foundational evidence
  boundary; the exact public benchmark is committed as a regression. (Two
  consumer-app wrong-safes were also found by earlier fuzzes and fixed.)
- **Decide-rate (the central gap):** see the generated
  [SCOREBOARD](bench-results/SCOREBOARD.md) totals (authoritative; this line
  intentionally does not hand-copy the aggregate), 0–100% across divisions;
  **25 / 35 rows** are decide-strong. The missing piece is representative depth
  and coverage, not another unpartitioned global percentage.
- **Performance:** the **first committed PAR-2 head-to-head exists**
  (`582ecba8`, public QF_BV p4dfa, lazy-vs-eager at 3s/20s, DISAGREE=0): lazy
  weakly dominates (7>4 decided at 20s) but `lazy_ops_total=0` everywhere. The
  later paired controls correct the old Z3 premise: Axeyum and the Z3 crate each
  decide 8/113 at 20s; exact overlap is 6 jointly decided, 2 Axeyum-only, and 2
  Z3-only (Z3 CLI 9/113). This is bounded corpus
  parity; matched breadth, decision-set overlap, RSS, and warm/cold regimes
  remain open.
- **Lean:** all 35 rows have complete audit artifacts; 327 baseline UNSAT
  decisions become 325 evidence-audit UNSAT outcomes, 267 certified + genuinely
  independently checked outcomes, and 260 Lean-checked outcomes. The affected
  v1 rows historically had 28 vacuous `bare-unsat` check booleans; the v2
  refresh now records zero and attributes all 58 residual bare outcomes to a
  decision backend. The full conjunction remains 259/327: 58 uncertified
  audit-row occurrences, eight reconstruction-only gaps, zero declared trust
  holes, and two QF_NIA `IntPow2` proof-production errors. Four stale QF_SEQ rows
  created before the string evidence soundness fix lose source-invalid DRAT
  credit without verdict changes. The parser-backed census deduplicates the 58 to
  56 paths / 51 exact contents, split 25 arithmetic / 26 string-sequence, and
  attributes 31/15/12 occurrences to the string front door, `auto-solve`, and
  NRA fallback respectively. Coverage is substantial but uneven; trace the
  QF_SEQ source-to-lowered boundary and route-provenance P1 before choosing a
  proof mechanism.
- **Dominance:** **23 / 35 audited rows** are fully dominant and the current
  mixed-vintage artifacts mark 594/753 decisions as dominant candidates. The
  v2 proof refresh changed 22 timing-derived flags without verdict changes, so
  paired timing cells must be refreshed before this count supports publication.

**Where to continue (toward the mission) — updated 2026-07-01/02 after a heavy
landing wave.** The two theory frontiers **advanced from planning into landed
increments**:

**Parity-gap research update (2026-07-21).** The current evidence and research
queue now live in
[`docs/plan/gap-analysis-z3-lean-2026-07-21.md`](docs/plan/gap-analysis-z3-lean-2026-07-21.md).
It separates selected-fragment decision parity, production Z3 replacement,
certified-result coverage, Lean-kernel compatibility, and Lean workflow
integration. The first prototype, `scripts/check-parity-docs.py`, derives the
live scoreboard/dominance/p4dfa denominators from committed artifacts and is in
`just check`; it caught and corrected the stale universal-sweep Z3 premise plus
stale decide/proof denominators in PLAN, STATUS, and SCOREBOARD. The same gate
now binds the branch's harder 228-file SMT-COMP-style inventory and 24-file
QF_BV three-solver control (19/24 each). The public inventory's legacy
82-decision scorer field is
**78 known-status agreements plus 4 unadjudicated decisions**, with zero
contradictions of known statuses; the exact p4dfa overlap is 6 jointly decided,
2 Axeyum-only, and 2 Z3-only. General Z3 solving-power distance is therefore
unmeasured, while production compatibility remains demonstrably far. The
required 71-family official-Lean solver-proof tier now bypasses the
Lake-only action, installs checksum-pinned elan, and fails closed on a missing
binary or incomplete sweep. Its first real local run rejected four modules
(67/71): three lost Bool/BV iota rules under opaque-inductive export and one hit
Lean's default elaborator recursion depth. Narrow export corrections rerun at
**71/71 accepted with two workers, zero skipped, zero failed**. The first
corrected run's Lean-worker phase took 6.8 s; a same-shape confirmation under
different local load took 53.3 s, so neither is promoted as a performance
claim. The standalone inductive test and missing-Lean negative control also
pass. The first corrected remote job is now retained as a failed gate: it
stopped before the representative sweep because `AXEYUM_LEAN_BIN` named an
elan shim without a default toolchain outside the repository working directory.
A true remote 71/71 attestation and archived duration/RSS remain open before
sizing the scheduled exhaustive tier. See the
[target evidence audit](docs/plan/parity-target-evidence-audit-2026-07-21.md).

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

- **2026-07-22 — TL0.7.4 attempt 001 failed closed at the exact 4 GiB
  boundary; R1 is source-first preregistered and the exporter has not run.** The
  [plan](docs/plan/lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md)
  freezes the exact Lean 4.30 binary/toolchain, official `lean4export` v4.30.0
  commit/tree/build, committed flat source and 65-line NDJSON oracle, 4/8 GiB
  lanes, external process records, immutable artifact/completion closure, and
  sixteen mutation families. The two empty-selection controls compile the flat
  probe, then export its owned `.olean` and require byte equality. They cannot
  create a U2/Axeyum outcome, denominator, pair, performance row, or parity
  credit. The original plan was pushed before preparation. The exact source build
  produced SHA-256 `8e763913...4449`; its first `-j1` invocation was rejected
  before compilation, and the supported build stayed clean. A plan amendment
  also corrected a 62-character source-hash transcription before implementation.
  Source revision `4ba69b70` was pushed before attempt 001, which retained a
  98-byte `failed to create thread` diagnostic and no `.olean` or completion.
  A focused trace shows a third 1,073,745,920-byte stack mapping failing with
  `ENOMEM`; 5/6/8 GiB pass with default stacks. Under 4 GiB, explicit Lean
  `-s` values through 768 MiB pass and produce identical `.olean` bytes, while
  960 MiB/1 GiB fail. The [R1 plan](docs/plan/lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md)
  freezes `-s524288`, preserves the [failed result](docs/plan/lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md),
  and hardens terminal-before-artifact retention before any retry.

- **2026-07-22 — TL0.7.3 closes registered local process-interruption
  checkpointing without Lean, U2, durability, or parity credit.** The
  source-first [plan](docs/plan/lean-execution-store-tl0.7.3-plan-2026-07-22.md)
  was pushed at `8bad6146` before implementation or kill cells; the final
  checkout-portable source was pushed at `afe7db6e` before the authoritative
  pass. The [result](docs/plan/lean-execution-store-tl0.7.3-2026-07-22.md),
  [authority](docs/plan/lean-execution-store-v1.json), generated
  [summary](docs/plan/generated/lean-execution-store.md), and 65 retained files
  now close 16/16 dependency/completion × four-boundary × observed ext4/tmpfs
  `SIGKILL` cells. All workers were reaped; eight pre-link and eight post-link
  resumes have the exact expected outcomes; all 16 projections equal the
  uninterrupted reference. Twenty-two contract tests cover all eighteen
  mutation families. This is local process-interruption recovery, not power/
  host loss, NFS, provider, object, or distributed durability. Real/U2
  outcomes, paired cells, performance rows, and parity credit remain zero.
  Next: source-first TL0.7.4 no-credit pinned-Lean/export controls; TL0.6.3
  remains blocked.

- **2026-07-22 — TL0.7.2 closes bounded process behavior without Lean, U2,
  completion, or parity credit.** The
  [plan](docs/plan/lean-execution-process-adapter-tl0.7.2-plan-2026-07-22.md)
  was pushed at `45bf823a` before implementation or probes; the final adapter
  was pushed at `367b9f34` before the authoritative pass. The
  [result](docs/plan/lean-execution-process-tl0.7.2-2026-07-22.md),
  [authority](docs/plan/lean-execution-process-v1.json), generated
  [summary](docs/plan/generated/lean-execution-process.md), and 40 retained
  files now close 8/8 synthetic attempts: zero/nonzero exit, signal, a
  descendant-bearing timeout with no live member, 4/8 GiB cooperative memory
  limits, launch failure, and preflight failure. Eleven tests cover sixteen
  mutation families. There are 16 raw streams but zero case/completion records,
  official/Axeyum outcomes, paired cells, performance rows, or parity credit.
  TL0.7.3 now supplies the bounded local process-interruption store; TL0.7.4's
  two no-credit real controls are next.

- **2026-07-22 — TL0.7.1 closes the machine execution-evidence contract with
  zero process or parity outcomes.** The source-first
  [plan](docs/plan/lean-execution-evidence-tl0.7-plan-2026-07-22.md) was pushed
  at `ff8f8dd4` before implementation. The
  [result](docs/plan/lean-execution-evidence-tl0.7.1-2026-07-22.md),
  [authority](docs/plan/lean-execution-evidence-v1.json), and generated
  [summary](docs/plan/generated/lean-execution-evidence.md) now retain explicit
  4 GiB standard/8 GiB exporter templates, twelve typed termination classes,
  exact immutable run/attempt/case/artifact/completion contracts, five valid
  synthetic lifecycle controls, and nineteen fail-closed mutation classes
  covered by twelve tests. The contract rejects implicit 64 GiB wrapper use,
  runner-label hardware inference, guessed OOM, JUnit/provider-only completion,
  lost retries, and adapter-to-native promotion. Real runs, executed attempts,
  completed cases, official/Axeyum outcomes, paired cells, and performance rows
  all remain zero. Next: TL0.7.2's forced process behavior, not U2 execution.

- **2026-07-22 — TL0.6.2 closes official CI profile derivation without
  claiming execution or parity.** The source-first
  [plan](docs/plan/lean-u2-official-ci-profiles-tl0.6.2-plan-2026-07-22.md)
  was pushed before profile counts were observed. The
  [result](docs/plan/lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md),
  [authority](docs/plan/lean-u2-official-ci-profiles-v1.json), and generated
  [summary](docs/plan/generated/lean-u2-official-ci-profiles.md) now retain 17
  contexts, nine active job literals, 153 cells, 111 declared CTest attempts,
  and eight exact selection sets. CTest independently reproduces every ordered
  filter membership; 13 contract tests cover the preregistered mutations.
  Linux release's `-E foreign` excludes zero registered names, while the
  sanitizer filter selects the same 3,477 ordered names from both registration
  profiles. All attempts remain `not-run`; official executions, Axeyum
  executions, paired cells, axes, and terminal gates remain zero. Next: TL0.7
  resource/checkpoint authority, then retained TL0.6.3 official executions.

- **2026-07-22 — bounded bignum base checking carries direct moments through
  order 255 and raw moments through 35.** `certifies_wz_sum` retains its
  checked-`i128` finite-base route first, then only on `Unknown` evaluates the
  fully concrete rational/positive-integer-Gamma fragment with exact
  `BigRational`; variables, other unary heads, poles, Gamma arguments above 256,
  and powers above 1024 decline. The symbolic telescoping or quotient identity
  remains mandatory and a certified-false result never falls back. Exact
  bignum product-scalar accumulation plus a Gamma-shift span of 256 remove the
  order-128 and order-130 representation artifacts. Falling moments 0 through
  255 now pass symbolic checking, bounded exact bases, BigInt concrete samples,
  tamper rejection, and the ceiling; order 256 still passes the compact symbolic
  identity, then deliberately declines at `Γ(257)`. Bignum monic normalization
  also closes raw orders 34 and 35 while requiring every final coefficient to
  fit public `Rational`; raw order 36 is the first measured decline because its
  monic numerator needs coefficients beyond `i128`. The CAS topic stack passes
  525 unit tests, 147 doctests, warning-denied all-target Clippy, strict
  stable/nightly rustdoc, `wasm32-unknown-unknown`, links, and
  `git diff --check`. Next: return to broad timeout-bounded gap probing, with
  fixed-shift `r=8` retained as a focused exact-growth candidate if demanded.

- **2026-07-22 — the independent ADR-0356 S4 selection auditor is
  preregistered and remains live-blocked on commit/push.** The standard-library
  implementation streams all 450,472 S1 eligibility and S2 corpus rows in
  lockstep, joins the twice-repeated S3 membership, checks the closed seven-
  reason partition and exact per-logic new/old quotas, and physically rehashes
  all 45,905 selected files. It publishes eleven required artifacts only after
  the 18-invariant/18-mutation register passes, then requires a fresh-process
  reconstruction of the complete corpus/history/decision join and a second
  selected-file rehash. `QF_UFFP` is explicitly frozen at two
  `excluded-trivial` rows, zero eligible rows, zero cap, and zero selections;
  the earlier S3 note incorrectly attributed its absence to the competitive-
  logic gate and is corrected. Next: pass the bounded repository gates, commit
  and push this implementation, then perform the first live S4 build and fresh
  verification. No solver execution is admitted yet.
- **2026-07-22 — TL0.6.1 derives U2 from Lean's executable CMake/CTest
  registration without claiming test execution or parity.** The new
  [U2 result](docs/plan/lean-u2-test-authority-2026-07-22.md),
  [machine-readable authority](docs/plan/lean-u2-test-authority-v1.json), and
  generated [Markdown](docs/plan/generated/lean-u2-test-authority.md)/
  [JSON](docs/plan/generated/lean-u2-test-authority.json) summaries freeze
  pinned Lean v4.30.0's 3,678 default and 3,723 `LAKE_CI=ON` registrations.
  The default set is a strict subset with 45 full-Lake-only cases; the full
  set partitions into 3,639 pile, 31 non-Lake directory, 52 Lake directory,
  and one lint case. Exact-output/empty/ignored/script-defined policies close
  at 1,480/2,099/60/84. Every normalized command/property, primary, sidecar,
  output policy, and over-approximating support subtree is content-bound across
  7,004 Git-tracked files. Pile selection independently closes 3,660 candidates
  as 3,639 registered plus 21 excluded. Eight mutation/contract tests and an
  offline generated-output check are in `parity-docs`, the shell aggregate,
  and both docs CI jobs; optional upstream verification reconstructs the
  capture in an isolated archive. U2 advances from inventory-only to
  `bounded_profile`, but the authority records zero official executions, zero
  Axeyum executions, and zero paired cells. All complete populations, axes,
  and terminal gates remain at zero. TL0.6.2 has since closed the official
  event/check-level/platform/preset/filter/stage/rebootstrap profile
  derivation without executing tests; TL0.7/TL0.6.3 and TL0.3's true remote
  71/71 executable-identity gate remain independently open.

- **2026-07-22 — product-level cancellation carries raw squared-binomial
  moments through order 33.** Every even factor shared with the known
  `(2n)ₘ` denominator is now removed from each Stirling term before polynomial
  expansion. The reduced terms and the independent Stirling power identity use
  exact `BigRational` intermediates, but a result is admitted only when all
  coefficients convert back to the public checked-`i128` `Rational` domain.
  Component and final central-binomial quotients are first compared in a
  deterministic factored form after bounded power expansion, exact scalar and
  monic-factor normalization, Gamma lowering, and structural cancellation;
  the prior exact rational comparison remains the fallback. Focused tests
  reconstruct every pre-cancelled term through order 12 and freeze scalar,
  power, and factor-order canonicalization. The full family regression now
  certifies raw orders 0 through 33 with direct sums and tamper/ceiling checks.
  Order 34 remains outside both public moment families because its required
  falling-factorial component reaches the independently measured exact base
  boundary `34! > i128::MAX`. The CAS topic stack passes 524 unit tests, 147
  doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc,
  `wasm32-unknown-unknown`, links, and `git diff --check`. Next: decide whether
  a deliberate bignum exact base checker is justified for falling/raw order 34,
  or return to broader timeout-bounded CAS gap probing.

- **2026-07-22 — complete Lean 4.30 parity now has an explicit terminal
  contract and a fail-closed generated registry, without promoting the
  completed TL2.14 slice.** The
  [contract](docs/plan/lean4-complete-parity-contract-2026-07-22.md) transfers
  the SMT-LIB measurement rules—content-identified authoritative populations,
  exact paired overlap, typed one-sided/mismatch/unadjudicated/not-run results,
  layer-specific equivalence, and zero incomplete-run credit—to twelve native
  Lean behavioral axes over ten upstream populations. The current generated
  matrix remains one satisfied K0 row, four of five K1 rows, and zero satisfied
  K2-K6 rows. TL0.6 is now partial: the
  [registry](docs/plan/lean-complete-parity-v1.json) and generated
  [Markdown](docs/plan/generated/lean-complete-parity.md)/
  [JSON](docs/plan/generated/lean-complete-parity.json) status derive current
  K-profile, construct, task, and axiom facts, but publish zero complete U0-U9
  authorities, zero complete A0-A11 axes, zero terminal paired cells, and zero
  satisfied G1-G10 gates. Eight contract/mutation tests reject incomplete
  denominators, missing evidence, illegal axis/gate credit, malformed paired
  identity, and a premature terminal claim; CI and local parity-document gates
  check both generated outputs and scan the live public claim surfaces. The
  Lean v4.30.0 tree audit records 6,931 test-tree blobs / 4,035
  Lean test sources and the mathlib pin records 8,606 Lean files, but the
  contract explicitly refuses to treat those inventories as executable test
  denominators. The first corrected remote Lean CI job is reclassified from
  pending/unattempted to failed-before-sweep on working-directory-dependent
  elan resolution. TL0.6.1 and TL0.6.2 have since derived the bounded U2
  registration and official CI configuration authorities, but have executed
  no tests. Next are TL0.3's executable identity and TL0.7/TL0.6.3's retained
  official runs before exact paired records can be populated.

- **2026-07-22 — structured composition carries raw squared-binomial moments
  through order 19.** Raw order 11 was mathematically valid but hit two
  representation limits: exhaustive rational-root search overflowed on its
  remaining degree-11 residual, and recombining eleven Gamma-valued component
  RHSs in one equality overflowed. The compositor now peels only exactly dividing
  bounded integer roots and retains an unfactored residual, constructs the
  remaining `(2n)ₘ` denominator from known uncancelled linear factors with an
  exact reconstruction check, and verifies composition after cancelling the
  shared central binomial. Each component and final quotient is compared as
  exact monic numerator/denominator parts after checked cancellation of known
  `(2n)ⱼ` factors. Orders 0 through 19 certify; order 20 is the first measured
  decline because common-numerator term 13 overflows checked `i128` polynomial
  normalization, while all twenty direct WZ component candidates still
  construct. Regressions freeze the explicit order-11 form, bounded exact
  direct sums, tamper/missing-evidence rejection, and the ceiling. Next: explore
  product-level common-factor extraction for raw order 20 or a deliberate
  bignum exact-polynomial path; falling order 34 independently needs a bignum
  base checker.

- **2026-07-22 — nested quotient cancellation carries direct moments through
  order 33.** Order 19's symbolic quotient was mathematically small, but Gamma
  lowering left equal atoms and polynomial factors inside nested divisions;
  the top-level-only product cancellation missed them and expanded the RHS
  ratio into degree-36 polynomials. The exact preprocessor now recursively
  collects multiplicative numerator/denominator factors, reverses sides through
  nested division, canonicalizes polynomial factors and Gamma arguments, and
  removes only structurally equal pairs. The compact quadratic ratio passes the
  unchanged symbolic equality gate through order 33. Order 34 also passes that
  symbolic gate, then declines exactly because its base value `34!` exceeds the
  `i128` rational domain. Raw moments remain independently certified through
  order 10; a fresh order-11 probe still reaches and declines in bounded
  numerator factorization. The CAS topic stack passes 522 unit tests, 147
  doctests, warning-denied all-target Clippy, stable/nightly strict rustdoc,
  `wasm32-unknown-unknown`, links, and `git diff --check`. Next: attack raw order
  11 or design an explicit bignum-only exact base checker before widening the
  direct family again.

- **2026-07-22 — structured exact base evaluation extends direct moments
  through order 18.** Order 16 already passed the symbolic quotient identity;
  its remaining `Unknown` was the exact base term
  `(16)₁₆(16!/16!)²`, whose whole-expression rational normalization multiplied
  through overflowing intermediates before cancelling the unit quotient.
  `certifies_wz_sum` now asks the existing exact rational evaluator to reduce
  each fully substituted summand and RHS first, retaining the prior normalizer
  as a fail-closed fallback. This changes only concrete proof preprocessing;
  the symbolic WZ gate and exact base equality remain unchanged. The direct
  falling-factorial family now certifies through order 18; order 19 is the
  first measured symbolic-quotient decline. Raw moments remain independently
  certified through order 10. The CAS topic stack passes 521 unit tests, 147
  doctests, warning-denied all-target Clippy, stable/nightly strict rustdoc,
  `wasm32-unknown-unknown`, links, and `git diff --check`. Next: isolate order
  19's quotient growth and raw order 11's bounded numerator-factorization
  limit.

- **2026-07-22 — pre-expansion factor cancellation closes direct moment 15.**
  The remaining order-15 WZ `Unknown` was isolated to the outer `n` quotient:
  its exact falling-factorial products were expanded before division, exceeding
  bounded rational normalization. `wz_symbolic_ratios` now canonicalizes each
  polynomial factor and removes only structurally identical numerator and
  denominator factors before gamma/rational normalization. Falling factorials
  also retain this exact product representation inside their WZ proof objects.
  The direct family now certifies through order 15; order 16 is the first
  measured decline. Raw moments remain independently certified through order
  10. The CAS topic stack passes 521 unit tests, 147 doctests, warning-denied
  all-target Clippy, stable/nightly strict rustdoc, `wasm32-unknown-unknown`,
  links, and `git diff --check`. Next: isolate order 16's residual quotient
  growth and raw order 11's bounded numerator-factorization limit.

- **2026-07-22 — product-aware WZ checking extends squared-binomial moments.**
  When direct symbolic telescoping overflows, `certifies_wz_sum` now checks the
  exact quotient identity; certified-false direct checks never fall back. This
  preserves the symbolic soundness gate while cancelling consecutive gamma
  products before polynomial expansion, extending the direct falling-factorial
  family through order 14 (order 15 remains `Unknown`). The raw compositor now
  uses the known `(2n)ₘ` common denominator and cancels only exactly divisible
  linear factors, extending independently rechecked raw moments through order
  10. Order eight recovers
  `n³(n⁹+6n⁸−31n⁷−106n⁶+315n⁵+294n⁴−693n³+18n²+96n−20)C(2n,n)/(16(2n−7)(2n−5)(2n−3)(2n−1))`.
  A measured raw order-11 probe reaches numerator factorization and declines.
  The CAS topic stack passes 521 unit tests, 147 doctests, warning-denied
  all-target Clippy, stable/nightly strict rustdoc, `wasm32-unknown-unknown`,
  links, and `git diff --check`. Next: isolate order 15's quotient growth and
  order 11's bounded factorization limit without weakening the proof objects.

- **2026-07-22 — exact base preprocessing extends composed moments through
  order seven.** The order-seven falling-factorial certificate already passed
  the fully symbolic WZ identity; only the finite base check returned `Unknown`
  after accumulating zero-supported terms with unsimplified gamma factors.
  `certifies_wz_sum` now simplifies each concrete summand and RHS before exact
  base equality, preserving the symbolic gate and soundness. Both public moment
  ceilings are now 7; raw order seven recovers
  `n⁴(n+1)(n⁵+5n⁴−15n³−35n²+70n−14)C(2n,n)/(16(2n−5)(2n−3)(2n−1))`.
  Order eight remains a symbolic `Unknown`. The CAS topic stack passes 521 unit
  tests, 147 doctests, warning-denied all-target Clippy, stable/nightly strict
  rustdoc, `wasm32-unknown-unknown`, links, and `git diff --check`. Next: isolate
  order eight's symbolic normalization growth without weakening the checker.

- **2026-07-22 — strict CAS rustdoc is green on stable and nightly.** Cleared
  ten pre-existing `-D warnings` failures: escaped the `𝔽ₚ[x]` spelling, changed
  links to private helpers into code spans, qualified the crate-level `equal`
  link, and removed redundant explicit targets. This is documentation-only;
  public APIs and runtime semantics are unchanged. Both
  `RUSTDOCFLAGS="-D warnings" cargo +stable doc -p axeyum-cas --no-deps` and the
  local-nightly equivalent pass. Next: retain strict rustdoc in every CAS branch
  gate alongside tests, Clippy, WASM, and link validation.

- **2026-07-22 — direct falling-factorial composition reaches the sixth raw
  squared-binomial moment.** `prove_squared_binomial_falling_moment(order)` now
  constructs one parameterized rational WZ certificate and replays it through
  the shared symbolic/base checker for orders `0..=6`.
  `prove_squared_binomial_moment(moment)` composes those proofs via the exact
  Stirling expansion, and its proof object rechecks every component, the power
  identity, and closed-form recombination. This closes order six without raw WZ
  interpolation, cuts the family regression from roughly 55 to 15 seconds, and
  rejects tampered/missing evidence. Both public ceilings are explicitly 6;
  order seven currently declines under bounded exact symbolic checking. The CAS
  topic stack passes 521 unit tests, 147 doctests, warning-denied all-target
  Clippy, `wasm32-unknown-unknown`, links, and `git diff --check`. Next: isolate
  the order-seven normalization boundary without weakening the checker.

- **2026-07-22 — squared-binomial raw moments are now a generated checked
  family.** `prove_squared_binomial_moment(moment)` derives the candidate from
  the exact Stirling/falling-factorial expansion
  `C(2n,n)∑S(m,j)(n)ⱼ²/(2n)ⱼ`, compacts the reduced rational through monic
  numerator/denominator factorization, and accepts it only through the existing
  fully symbolic WZ plus exact base-case checker. The returned
  `CertifiedSquaredBinomialMoment` can recheck its own order, closed form, and
  certificate. Regressions certify orders `0..=5`, direct-sum cross-check every
  generated member, recover the known fifth-moment form, and reject tampered
  closed forms and certificates. `MAX_PROVED_SQUARED_BINOMIAL_MOMENT=5` makes
  the current bounded-discovery ceiling explicit; larger requests decline
  immediately. The CAS topic stack passes 520 unit tests, 147 doctests,
  warning-denied all-target Clippy, `wasm32-unknown-unknown`, links, and
  `git diff --check`. Next: investigate direct falling-factorial certificate
  composition for higher moments without weakening the symbolic gate.

- **2026-07-22 — fixed-shift Vandermonde is now a checked public family route.**
  `prove_fixed_shift_binomial_convolution(shift)` constructs the closed
  certificate `k(k+r)(2k−3n+r−3)/(2(2n+1)(k−n−1)(k−n+r−1))` for a concrete
  nonnegative shift and returns it only after the same fully symbolic WZ check
  and exact base-case check used by discovery. The checker is shared with
  `prove_wz_sum`; no interpolation or answer table is trusted. Regressions prove
  `r=0..7` and reject a zero certificate; larger exact-growth cases retain
  fail-closed `None` semantics. The CAS topic stack passes 519 unit tests, 147
  doctests, warning-denied all-target Clippy, `wasm32-unknown-unknown`, links,
  and `git diff --check`. Next: derive a similarly explicit squared-binomial
  moment-family boundary rather than adding isolated moments indefinitely.

- **2026-07-22 — proof-carrying CAS closes fixed-shift four and the fifth
  squared-binomial moment.** `prove_wz_sum` now certifies
  `∑C(n,k)C(n,k+4)=C(2n,n−4)` and
  `∑k⁵C(n,k)²=n⁴(n+1)(n²+2n−5)C(2n,n)/(8(2n−3)(2n−1))`, checks the exact
  returned certificates, and declines `rhs+1` controls. Every symbolic WZ ratio
  now cancels common canonical gamma atoms before concrete specialization; this
  removes the `Γ(n)` factorial overflow that previously cut fifth-moment samples
  off at `n=12`. The exact sample target is 16 (scan bound 32), enough to reject
  under-fit rational coefficients and aligned with the existing dimension-16
  bignum solve cap. The fully symbolic WZ equality gate remains mandatory. The
  CAS topic stack passes 518 unit tests, 147 doctests, warning-denied all-target
  Clippy, `wasm32-unknown-unknown`, documentation-link validation, and
  `git diff --check`. Next: turn the observed `r=0..4` certificate pattern into
  a checked family route and derive the moment family before adding another
  isolated tier.

- **2026-07-22 — proof-carrying CAS closes fixed-shift three and the fourth
  squared-binomial moment.** The public WZ route now certifies
  `∑C(n,k)C(n,k+3)=C(2n,n−3)` and
  `∑k⁴C(n,k)²=n³(n³+n²−3n−1)C(2n,n)/(4(2n−3)(2n−1))`, checks the exact
  returned certificates, and declines `rhs+1` controls. Discovery now derives
  the compact inner/outer WZ ratios before concrete specialization, canonicalizes
  polynomial gamma arguments, cancels residual denominator cofactors only after
  exact division, and uses a dimension-capped exact bignum fallback when an
  `i128` interpolation solve overflows but its final coefficients fit. The fully
  symbolic WZ equality gate remains mandatory. The CAS topic stack passes 516
  unit tests, 147 doctests, warning-denied all-target Clippy,
  `wasm32-unknown-unknown`, documentation-link validation, and
  `git diff --check`. Next: probe `r=4`/general fixed shift and the fifth
  squared-binomial moment without weakening the symbolic gate.

- **2026-07-22 — proof-carrying CAS closes fixed-shift two and the third
  squared-binomial moment.** The public WZ route now certifies
  `∑C(n,k)C(n,k+2)=C(2n,n−2)` and
  `∑k³C(n,k)²=n³(n+1)C(2n,n)/(4(2n−1))`, checks the exact returned
  certificates, and declines `rhs+1` controls. A structured Gosper fallback
  derives the consecutive ratio of `f(n+1,k)−f(n,k)` from three smaller exact
  quotients instead of expanding an additive gamma tower; shared integer-linear
  factors and a one-way finite-field coprimality certificate keep exact fraction
  reduction inside `i128`. The final fully symbolic WZ equality gate remains
  mandatory. The CAS topic stack passes 512 unit tests, 147 doctests,
  warning-denied all-target Clippy, `wasm32-unknown-unknown`, documentation-link
  validation, and `git diff --check`. Next: probe the `r=3`/general fixed-shift
  convolution and the fourth squared-binomial moment without weakening the
  symbolic soundness gate.

- **2026-07-22 — proof-carrying CAS closes adjacent convolution and the first
  two squared-binomial moments.** `prove_wz_sum` now symbolically certifies
  `∑C(n,k)C(n,k+1)=C(2n,n−1)`, `∑kC(n,k)²=(n/2)C(2n,n)`, and
  `∑k²C(n,k)²=n³C(2n,n)/(2(2n−1))`, with exact returned-certificate checks and
  `rhs+1` false controls. Discovery now admits monic rational interpolants whose
  denominator vanishes at zero (`1/(2n)`), prefers balanced degree splits when
  samples exactly determine several same-total-degree fits, strips scalar
  content before polynomial GCD, and uses primitive-part Euclid to avoid
  removable `i128` growth. Large concrete gamma towers may use the equivalent
  exact reduced Gosper equation when expanding the full residual overflows; the
  final fully symbolic WZ equality gate remains mandatory and unchanged. The
  CAS topic stack passes 508 unit tests, 147 doctests, warning-denied all-target
  Clippy, `wasm32-unknown-unknown`, and documentation-link validation. Next:
  probe fixed-shift (`r=2`) convolution and the third squared-binomial moment.

- **2026-07-22 — proof-carrying CAS closes the Vandermonde WZ gap; broader
  creative telescoping is next.** `prove_wz_sum` now proves
  `∑ₖ C(n,k)² = C(2n,n)` and returns
  `R(n,k)=k²(2k−3n−3)/(2(2n+1)(k−n−1)²)`, with the fully symbolic WZ identity
  checked by the existing exact zero-test and a false `C(2n,n)+1` control still
  declining. Concrete discovery now cancels exact common gamma-monomial content
  before its univariate gate, scans bounded dispersion candidates by direct
  shifted GCD instead of an overflow-prone symbolic resultant, and folds the
  specialized summand/RHS before division to avoid representation-induced
  `i128` blow-up. The lane passes 504 unit tests, 147 doctests, warning-denied
  all-target Clippy, and `wasm32-unknown-unknown`. Capability, diary, and CAS
  handoff docs are synchronized. Next: probe adjacent-binomial convolution and
  weighted squared-binomial identities through the same concrete-discovery plus
  symbolic-certificate gate.
- **2026-07-22 — G1 official selection identity is preregistered after E3.**
  Proposed
  [ADR-0356](docs/research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)
  and the
  [execution plan](docs/plan/smtcomp-official-selection-identity-plan-2026-07-22.md)
  pin organizer commit `401302678311593efcef8a79b614b33a3b853eac`, the
  matching 450,472-file SMT-LIB 2025.08.04 Zenodo release, locked Polars 1.39.2,
  all 2018--2024 Single Query inputs, and corrected official seed
  `22,731,074`. The
  organizer remains the sampler producer; a separate standard-library auditor
  must prove release-byte closure, competitive-logics/difficulty eligibility,
  per-logic caps, complete decision reasons, and selected-file hashes. S0 now
  freezes 29 source/config files, 51 direct-child submissions, seven historical
  result inputs, 90 archives, 18 invariants, 18 mutations, and nine exact fixture
  files; the S1a official-format/AST adapter and S1b bounded-memory streaming
  runner raise the offline gate to fourteen tests. The runner is committed
  before use and emits only eligibility/cap facts, never an official sample.
  Its first live selection-free attempt is retained as a negative after it
  stopped before metadata reduction on regexp-valued submission logics. That
  failure also exposed the organizer's non-recursive submission glob, excluding
  two template examples and correcting the competitive count from 38 to 36 and
  seed from `22,731,158` to `22,731,074` before any official sample was
  observed. The next retained attempt reached the exact follow-on boundary:
  regexp expansion ranges over every organizer `Logic`, then
  `Participation.get` silently filters non-Single-Query matches through the
  Single Query division table. That behavior is now fixture-covered; another
  retained attempt then completed all 450,472 metadata rows and proved the two
  configured removal IDs match zero of them, making the official anti-join
  idempotent. That exact absence is now audited. The next retained attempt
  completed all seven historical streams (5,345,294 rows) and proved organizer
  metadata order is not canonical path order. A standard-library, bounded
  external merge sort now supplies the canonical ledger order and has sorted
  all 450,472 retained rows exactly. S1b is complete on the fifth fresh run:
  89 inputs, 450,472 metadata rows, 5,345,294 historical rows, and a
  256,182,191-byte eligibility ledger were independently rehashed and
  recounted. The resulting aggregate cap is 45,905 with 2,709 new and 43,196
  old quota slots. S2 is complete on a fresh acquisition: all 90 release files
  and 4,890,207,406 compressed bytes verified, 89 logic trees promoted, and the
  exact 450,472-file / 82,270,961,563-byte metadata-tree bijection published.
  A separate fresh process rehashed every archive and extracted file and
  reconstructed the canonical ledger and completion dependencies.
  S3 is complete after its implementation commit and push: two exact 88-file
  no-Git bundles, hash-required 14-package environments, independent official
  cache sets, and one-thread Polars 1.39.2 runs produced byte-identical
  45,905-path selections (2,709 new / 43,196 old). A fresh standard-library
  process rehashed both complete runs. `selection_observed=true`; S4's complete
  independent decision and selected-file audit is next. No solver run or
  selection credit is granted yet.

- **2026-07-22 — G1 E3 multi-host durability is complete, and the
  second full-library P0 is sound-declined.** The opt-in resumable path now
  validates the exact ordered benchmark ledger and the
  corpus/selection/environment/solver/runner/toolchain
  identity, acquires a no-steal shard lease, records attempt/terminal lifecycle,
  captures byte-exact outputs and typed process outcomes, publishes completion
  last, and exports legacy raw JSON only from a complete validating bundle.
  Real process kills before and during fake-solver execution, lease contention,
  explicit stale recovery, interruption equivalence, timeout-observed response
  admission, output mutation, and duplicate rejection are executable gates.
  `compete.py --host-run` now places the host runner, bounded shard workers,
  solvers, and descendants in one transient user-systemd/cgroup-v2 service;
  exact memory/swap/CPU/PID limits, controller counters, overcommit/environment
  rejection, evidence tamper, and destructive host-runner kill/resume pass with
  `AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh`. E3 now
  adds content-addressed source staging, exact three-host allocation,
  normalized NFSv4.1/environment registration, per-host cgroups, immutable
  outer allocation/fault/recovery evidence, dead-unit/launcher-gated stale
  lease quarantine, different-host retry, and completion-gated central export.
  The repeated committed `s5`/`s6`/`s7` six-case gate passes with identical
  timing-free outcomes; the final evidence root is
  `/nas3/data/axeyum/harness/e3-gate/live-1784740048714236679-84b40626d845`.
  E3 is complete but still grants no large-run measurement credit: the
  independent official eligibility/status/difficulty/release/seed/corpus/file
  selection identity remains open. Separately, the live
  stale run has exactly two WRONG markers: the repaired FP case and
  QF_AUFLIA `pipeline-invalid.smt2` (declared/cvc5 `sat`, Axeyum `unsat`). The
  latter reproduces on current code because the scalar UFLIA abstraction search
  exports an unchecked refutation. The AUFLIA lazy-ROW adapter now enforces the
  foundational rule that this result is `unknown` until a lifted checked proof
  exists; existing certificate-rechecked array refuters remain ahead of it.
  The exact 2024 benchmark and a no-wrong-verdict regression are committed.

- **2026-07-22 — P0 FP wrong-`sat` is fixed on `main`; complete affected-slice
  validation is next.** The full-library run exposed exact finite cancellation
  under `roundTowardNegative` being lowered to `+0` instead of `-0`. The same
  latent rule existed in FMA. `axeyum-fp` now selects exact-zero signs by
  rounding mode; independent `rustc_apfloat` tests cover add/FMA, operand order,
  signed-zero inputs, and all five modes. The QF_FP differential generator now
  uses all five modes and includes the minimized cancellation seed class; 600
  scripts agree with cvc5 1.3.4 (267 `sat`, 333 `unsat`, zero disagreements).
  The preserved QF_BVFP and QF_ABVFP originals both return `unsat` through the
  SMT-COMP CLI. Re-run the complete QF_FP/QF_BVFP/QF_ABVFP selected slices before
  restoring the full-library DISAGREE = 0 claim. The separate Lean
  reconstruction `ExprNode::Proj` exhaustiveness error found by the all-feature
  gate is also repaired; workspace check and warning-denied Clippy are green.
  The detailed state and resume sequence are in
  [the FP audit handoff](docs/plan/fp-theory-soundness-audit-handoff-2026-07-22.md).

- **2026-07-22 — TL2.14 nested-inductive kernel elimination is complete.**
  [Accepted ADR-0354](docs/research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)
  and the
  [P0--M5 execution plan](docs/plan/lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)
  bind pinned Lean 4.30's actual atomic group algorithm. M0 freezes a
  1,676-byte / 66-line source compiled twice to one OLEAN digest and
  two byte-identical-per-root official streams totaling 40,282 bytes. The
  independent inventory finds two motives and four minors per recursor and
  records that the wire `recs` arrays are dependency-ordered `Odd.rec,
  Even.rec`, not family-ordered; M4 must match names and owned rules rather than
  array position. Eleven fail-closed tests enforce the exact no-product-credit
  boundary. The subsequent
  [M1 result](docs/plan/lean-mutual-inductive-groups-m1-2026-07-22.md) adds the
  public ordered `InductiveFamilySpec`/`add_mutual_inductive` path, checks
  group-local names, definitionally equal shared parameters, per-family
  indices, and equivalent result universes, and places singleton admission
  inside an insertion-log transaction. Nine focused public-path tests preserve
  complete singleton declarations, iota computation, direct-recursive
  identities, exact error payloads, rollback, and retry behavior. The
  subsequent
  [M2 result](docs/plan/lean-mutual-inductive-groups-m2-2026-07-22.md) replaces
  the policy decline with one native group algorithm. Positivity sees every
  family before staging; all family/constructor headers then become
  provisionally visible; motives follow family order, minors follow family then
  constructor order; terminal-family motives/recursors drive recursive fields;
  and every recursor type plus closed rule value is inferred before commit.
  Eighteen public integration tests cover singleton, two/three-family cross,
  mixed self/cross, zero/one/two indices, indexed and higher-order recursion,
  empty-constructor families, mutual predicates, and the typed negative matrix.
  Two private tests freeze 16 mutation classes and inject a final-rule failure
  after complete staging to prove whole-group rollback. Exact singleton
  declarations, `MiniNat.rec`/`MiniList.rec` identities, and the 768/840
  controls remain unchanged. The subsequent
  [M3 result](docs/plan/lean-mutual-inductive-groups-m3-2026-07-22.md) executes
  720 unique public production records twice to a byte-identical summary:
  432 positive admission/inference/iota contracts and 288 exact typed
  rollbacks. It spans one through three families, zero through two shared
  parameters and per-family indices, zero through three constructors/recursive
  fields, zero through five total fields, telescope depths zero through two,
  `Prop`/`Type`, and self/earlier/later targets. The oracle reads motive/minor
  order from generated recursor telescopes and target-family counts from rule
  syntax; 288 group-order and 240 target-family mutations are detectably
  unequal. The descriptor is `2ea6769fa45ea159`, and the retained 768/840
  descriptors remain exact. Importer policy and both M0 streams are untouched.
  The subsequent
  [M4 result](docs/plan/lean-mutual-inductive-groups-m4-2026-07-22.md) removes
  only that blanket importer decline. Every ordered family/constructor/recursor
  record is validated, the atomic group gate is called once, and the official
  dependency-ordered `recs` arrays are matched by checked name. The construct
  stream and both computation streams import twice to identical reports with
  zero axioms; the selected non-indexed and indexed theorem sides both reduce
  to `MiniNat.succ (MiniNat.succ MiniNat.zero)`. Twenty-two rejecting metadata,
  type, count, rule, field, and late-publication mutations plus recursor-order
  and descriptive-metadata positive controls pass. The complete importer suite
  is 40 integration tests; the complete kernel suite, 720/768/840 populations,
  strict Clippy, and rustdoc pass. The
  [M5 final result](docs/plan/lean-mutual-inductive-groups-final-2026-07-22.md)
  adds a history-preserving assurance overlay with five admitted rows, three
  independently computation-checked rows, and one current decline; removes the
  obsolete live `inductive-mutual` decline; and closes every registered code,
  pinned-Lean, contract, foundational-resource, and link gate. ADR-0354 is
  accepted and TL2.13 is DONE. The subsequent
  [dependency audit](docs/plan/lean-post-tl2.13-dependency-audit-2026-07-22.md)
  corrects the next trust boundary: pinned Lean 4.30 performs nested-inductive
  expansion/restoration inside kernel admission, while native well-founded
  source recursion remains elaborator task TL4.10. The already elaborated
  well-founded root remains a passing 35-declaration/zero-axiom control, not
  new frontend credit. [Accepted ADR-0355](docs/research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)
  and the [P0--M6 execution plan](docs/plan/lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)
  bind structural nested discovery, complete auxiliary-container copying,
  reuse of TL2.13's atomic group checker, final-surface restoration,
  deterministic `.rec_N` publication, >=640 generated profiles, and retained
  720/768/840 controls. P0 and M0 are complete. The
  [M0 result](docs/plan/lean-nested-inductive-elimination-m0-2026-07-22.md)
  freezes a 2,917-byte positive source and 260-byte negative source, one
  byte-identical OLEAN digest, the exact no-local-variable kernel diagnostic,
  and three root-specific streams totaling 114,596 bytes / 2,022 records. The
  explicit recursors cover ordinary, indexed-container, and repeated-container
  nesting; the repeated case has `numNested = 1` for two identical
  applications. Wire recursor order varies (`.rec_1,.rec` versus
  `.rec,.rec_1`), so later comparison is by checked name and owned rules.
  Thirteen fail-closed tests and both aggregate documentation gates enforce the
  no-product-observation boundary. The subsequent
  [M1 result](docs/plan/lean-nested-inductive-elimination-m1-2026-07-22.md)
  parses one consistent group-wide `numNested` count before recursor policy,
  requires the exact source-family-plus-auxiliary population, and moves the
  official row to `Unsupported(inductive-nested)` before admission. Missing or
  extra nested recursors, inconsistent mutual metadata, and ordinary zero/two-
  recursor singletons retain typed malformed outcomes. The complete importer
  suite and exact well-founded/720/768/840 controls pass; no M0 computation
  stream or assurance artifact is observed. The subsequent
  [M2 result](docs/plan/lean-nested-inductive-elimination-m2-2026-07-22.md)
  implements structural discovery, complete checked-container copying,
  fixed-point queuing, unchanged atomic group checking, binder-aware recursive
  restoration, exact string `.rec_N` publication, private-name leakage checks,
  and cache-safe rollback. Twenty-three focused native tests cover the complete
  named matrix plus `Rose.rec -> Rose.rec_1 -> Rose.rec` computation. The
  complete kernel/importer suites, retained 720/768/840 populations, strict
  Clippy/rustdoc, M0 contracts, and local/tracking/remote semantic ref equality
  pass. Importer policy and all M0 computation streams remain untouched. M3's
  [pre-run grammar plan](docs/plan/lean-nested-inductive-elimination-m3-plan-2026-07-22.md)
  froze the exact schema, seed, 640-case construction, observer, mutation
  registry, resources, and stop conditions. The subsequent
  [M3 result](docs/plan/lean-nested-inductive-elimination-m3-2026-07-22.md)
  repeats all 640 cases twice with descriptor digest `a20fe056c9443a37`, exact
  public declaration/dependency observation, 320 main plus 462 auxiliary typed
  iota checks, and 16 transactional private restoration mutations. A bounded
  stop-review amendment validates the already-checked temporary surface after
  copied-constructor metadata mutants survived M2 restoration. Commit
  `6a2afdd5` is pushed with local/tracking/remote equality; the complete suites,
  retained populations, strict tooling, and M0 contracts pass. Importer policy
  and all M0 streams remain untouched. The authoritative
  [TL2.14 handoff](docs/plan/lean-nested-inductive-elimination-resume.md)
  now records the completed P0--M6 lane. The
  [M4 importer plan](docs/plan/lean-nested-inductive-elimination-m4-plan-2026-07-22.md)
  froze the requirements to derive auxiliary count from checked
  main-recursor motives, compare name-keyed main/auxiliary declarations, import
  four exact official streams twice, and close 20 wire/publication rejection
  classes plus order non-authority. Kernel, fixtures, identity, assurance, and
  the live decline remained outside M4 ownership. The subsequent
  [M4 result](docs/plan/lean-nested-inductive-elimination-m4-2026-07-22.md)
  imports those streams twice at 22/34/34/34 declarations and zero axioms,
  compares every exact main/auxiliary contract, and closes all registered
  mutations. Commit `f03dfcdf` is pushed with ref equality; complete suites and
  exact 640/720/768/840 plus well-founded 35/0 controls pass. M4 is the planned
  first product import of the immutable M0 streams but adds no explicit normal-
  form or assurance credit. The subsequent
  [M5 plan](docs/plan/lean-nested-inductive-elimination-m5-plan-2026-07-22.md)
  freezes three exact theorem roots and 3/3/5-successor normal forms before
  implementation at `dbaaedb4`. The
  [M5 result](docs/plan/lean-nested-inductive-elimination-m5-2026-07-22.md)
  reproduces the unchanged pinned-Lean OLEAN digest twice and checks all three
  theorem proofs and normal forms twice at `edfa7924`. Its append-only TL2.14
  overlay preserves every historical view and advances the current seven-row
  construct matrix to six independently admitted rows, four computation-
  checked rows, and zero current declines. Only then was the obsolete live
  `inductive-nested` code removed; five unrelated codes remain exact. Complete
  suites, exact 640/720/768/840 and well-founded 35/0 controls, strict tooling,
  73 related Python contract tests, generated documents, foundational
  resources, and links pass. The
  [M6 final result](docs/plan/lean-nested-inductive-elimination-final-2026-07-22.md)
  maps every decision exit and freshly repeats both positive and negative
  pinned-Lean controls plus the complete bounded aggregate. Containing commit
  `1d848ad4` was pushed with local/tracking/remote equality before integration,
  so ADR-0355 is accepted and TL2.14 is DONE. Native source parsing/elaboration,
  recursion compilation and termination, broad libraries, and ecosystem/runtime
  support remain separate work.

- **2026-07-22 — TL2.12 recursive induction hypotheses are complete; TL2.13
  mutual groups are next.**
  [Accepted ADR-0353](docs/research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)
  and the
  [M0--M5 execution plan](docs/plan/lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)
  bind direct, recursive-indexed, higher-order, and combined indexed/higher-
  order fields to one Lean 4.30 rule: `u : Pi xs, I params indices` receives
  `Pi xs, motive indices (u xs)`, while its computation rule passes
  `fun xs => I.rec params motive minors indices (u xs)` to the minor. Existing
  direct recursion is the empty-telescope/empty-index control. The plan freezes
  exact `MiniVector`/`MiniAcc` stream hashes and makes constructor-only witnesses
  ineligible for computation credit. The
  [M0 result](docs/plan/lean-recursive-induction-hypotheses-m0-2026-07-22.md)
  now freezes a 1,422-byte explicit-recursor source that compiles twice and two
  root-specific official streams that reproduce byte-identically: Vector
  15,944 bytes/284 records and Acc 17,722 bytes/314 records. Independent
  inventories freeze their exact recursive-indexed/reflexive metadata. Ten
  fail-closed tests bind source/stream/baseline hashes, roots and normal forms,
  pins/resources/commands, semantic/claim/case/mutation/generated/stop
  contracts, and reject any premature Axeyum observation. The Rust product has
  not run on either M0 computation stream. The
  [M1 result](docs/plan/lean-recursive-induction-hypotheses-m1-2026-07-22.md)
  routes direct recursion through one WHNF telescope-tail classifier and
  reopener shared by minor types and rule right-hand sides. The
  [M2 result](docs/plan/lean-recursive-induction-hypotheses-m2-2026-07-22.md)
  admits all ten positive native rows, retains four typed transactional
  negatives, rejects ten native mutation classes, and repeats a 768-case
  public-path grammar byte-identically. The retained 840-case grammar reports
  both its TL2.11 baseline partition and the intended 186-case M2 admission
  widening. Stable metadata retains only field position and telescope depth;
  reconstruction disagreement returns `RecursiveFieldShapeMismatch`. Exact
  `MiniNat.rec`/`MiniList.rec` declaration identities, Nat/List computations,
  182 kernel units, and both generated summaries remain green. The
  [M3 result](docs/plan/lean-recursive-induction-hypotheses-m3-2026-07-22.md)
  makes `isReflexive` descriptive metadata and completes both frozen construct
  targets twice with exact official/generated recursor comparison. The
  pre-elaborated well-founded stream also completes through `Acc.rec`; this is
  bounded kernel import, not source elaboration. Mutual/nested retain their
  typed outcomes, and metadata plus late-publication mutations pass. The
  [M4 result](docs/plan/lean-recursive-induction-hypotheses-m4-2026-07-22.md)
  confirms pinned Lean twice to one OLEAN digest, imports both computation
  streams twice, and recursively normalizes the selected results to
  `MiniNat.succ MiniNat.zero` and `True`. The generated matrix now reports four
  admitted rows, two separately computation-checked rows, and two typed
  declines from a machine-validated TL2.12 overlay. The
  [M5 final result](docs/plan/lean-recursive-induction-hypotheses-final-2026-07-22.md)
  closes the complete bounded Rust, contract, parity, foundational-resource,
  and link gates, accepts ADR-0353, and marks TL2.12 DONE. Every milestone was
  bounded to one Lean/two Rust workers and 4 GiB, then added, committed, pushed,
  and remote-verified. Resume by preregistering mutual-group positivity,
  multiple motives/minors, exact official recursor comparison, and group-level
  rollback as TL2.13. A later dependency audit assigns kernel-side nested-
  inductive elimination to TL2.14 and native recursive source elaboration to
  TL4.9/TL4.10.

- **2026-07-22 — TL2.11/T6.0.2 strict positivity is complete; TL2.12 is
  next.** Accepted
  [ADR-0352](docs/research/09-decisions/adr-0352-preregister-lean-strict-positivity.md)
  and the [execution plan](docs/plan/lean-strict-positivity-tl2.11-plan-2026-07-22.md)
  bind the implementation to Lean 4.30 commit `d024af09`: WHNF each field,
  reject family occurrences in `Pi` domains, recurse through codomains, and
  otherwise accept only the exact family application with fixed parameters,
  full index arity, and occurrence-free indices. The guard must run before
  provisional inductive environment insertion and return separate typed non-
  positive/invalid-occurrence errors. Direct recursion must remain admitted;
  positive `MiniVector`/`MiniAcc` shapes must pass positivity but retain their
  current feature declines. A >=256-case deterministic polarity grammar and a
  mandatory pinned-Lean differential gate precede acceptance. The
  [M0 result](docs/plan/lean-strict-positivity-m0-2026-07-22.md) and
  [`lean-strict-positivity-v1.json`](docs/plan/lean-strict-positivity-v1.json)
  hash-freeze four sources and six rule classes before new execution. Eight
  mutation tests reject source/case/pin/resource/command/diagnostic drift and
  premature observations. The
  [M1 result](docs/plan/lean-strict-positivity-m1-2026-07-22.md) now implements
  the exact single-family WHNF/`Pi`/family-application preflight before
  provisional environment insertion. It returns stable non-positive and
  invalid-occurrence payloads, preserves direct recursion and the positive
  recursive-indexed/reflexive feature declines, and passes 182 kernel unit
  tests plus focused clippy/rustdoc under the 4 GiB cap. The
  [M2 result](docs/plan/lean-strict-positivity-m2-2026-07-22.md) adds all twelve
  public contract rows and a seed-frozen 840-case grammar, repeated twice with
  exact summary identity across three parameter/index profiles, both result
  sorts, depths zero through four, and constructor/field ordering. Exact typed
  failures compare the complete environment before/after. It does not widen
  admission or complete TL2.11. The
  [M3 result](docs/plan/lean-strict-positivity-m3-2026-07-22.md) records eight
  cgroup-bounded runs at exact Lean 4.30 commit `d024af09`: the positive source
  accepts twice and all three negatives reject twice with the registered
  diagnostic, at 468432 KiB maximum RSS. A required CI test repeats that exact
  population and fails closed when Lean is required but absent. An explicitly
  synthetic format mutation propagates `NonPositiveInductiveOccurrence` at
  `MiniNat`, field zero, without returning `CompletedImport`; the immutable
  construct matrix preserves ten controls and ten declines. The
  [M4 final result](docs/plan/lean-strict-positivity-final-2026-07-22.md) closes
  182 kernel units, 38 kernel integrations, 30 importer integrations, both
  doctests, focused clippy/rustdoc/rustfmt, 14 observation-validator tests,
  foundational resources, parity artifacts, and links under the bounded
  policy. ADR-0352 is accepted, the research question is closed, and
  TL2.11/T6.0.2 are DONE without widening admission. TL2.12 recursive-indexed
  plus reflexive/higher-order induction-hypothesis generation is the next
  preregistration-first semantic slice.

- **2026-07-22 — the official Lean construct-matrix selected-family milestone
  is complete; its TL2.11 handoff is now closed.** The milestone remains explicitly
  a measurement artifact, not kernel implementation. The
  [execution plan](docs/plan/lean-official-construct-matrix-plan-2026-07-22.md)
  and [Stage A result](docs/plan/lean-official-construct-matrix-stage-a-2026-07-22.md)
  and [Stage B result](docs/plan/lean-official-construct-matrix-stage-b-2026-07-22.md)
  and [M3 product result](docs/plan/lean-official-construct-matrix-product-2026-07-22.md)
  and [M4 assurance result](docs/plan/lean-official-construct-matrix-m4-2026-07-22.md)
  and [accepted ADR-0351](docs/research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)
  define six positive/control families (existing direct recursion,
  recursive-indexed, Acc-shaped reflexive/higher-order, mutual, nested, and
  well-founded) plus one official non-positive source rejection. Source intent
  freezes before export; exact wire features freeze from two byte-identical
  official exports and the independent Python inventory before the Rust
  importer is run. Every Rust decline must be typed, repeatable,
  completion-only, and paired with the immutable 11-declaration direct-
  recursive pass. Source family, wire construct, parsing, translation,
  independent admission, computation, and assurance credit remain separate
  generated fields. New streams have fixed 1 MiB each / 2 MiB aggregate
  retention bounds, and all Lean/Rust work remains under 4 GiB with one/two
  workers. M0 regenerated both historical streams twice with exact hashes and
  repeated the flat 8-declaration/one-axiom and direct-recursive
  11-declaration/zero-axiom imports twice without drift. Stage A freezes seven
  ordered cases and two source hashes in a fail-closed registration: pinned
  Lean accepts the positive recursive-indexed/reflexive/mutual/nested/well-
  founded module at 471,712 KiB peak RSS and rejects the non-positive control
  at the kernel positivity check at 88,972 KiB. Eight contract tests reject
  source/case/pin/resource/retention drift and all premature Stage B or product
  fields. Stage B now retains five new byte-identical two-run streams totaling
  116,636 bytes. The independent reader freezes their complete declaration
  populations and group metadata: recursive-indexed `MiniVector`, indexed and
  reflexive `MiniAcc`, a two-type/two-motive mutual group, `Rose` with
  `numNested=1` and two recursors, and a well-founded source whose ordinary
  definition depends on recursive-indexed/reflexive `Acc`. All ten exports stay
  below 701 MiB RSS. M3 at remote Stage B revision `22f51b4b` then repeats all
  five current-product declines twice, with the 11-declaration/zero-axiom
  direct-recursive control passing before all ten runs. Recursive-indexed
  reaches `KernelError::RecursiveIndexedNotSupported`; reflexive, mutual, and
  the well-founded `Acc` closure stop at stable policy codes; nested exposes a
  transactional but incorrect `Malformed` classification for its valid two-
  recursor official group. The product freezer, 11 contract tests, and Rust
  integration test bind every payload and forbid a published `CompletedImport`.
  M4 now derives the seven-row
  [generated matrix](docs/plan/generated/lean-official-construct-matrix.md): one
  independently admitted control, one translated-kernel decline, three parsed/
  policy declines, one inventory-only nested misclassification, one official-
  source rejection, and zero computation-checked rows. Thirteen contract tests
  reject false admission, parsed, or computation promotion. The
  [M5 final result](docs/plan/lean-official-construct-matrix-final-2026-07-22.md)
  closes the bounded Rust, contract, parity, foundational-resource, link,
  documentation, ADR, and ref-equality gates. The first rustdoc link attempt's
  LLD `SIGBUS` reproduced only on the 80%-full `/tmp` tmpfs and passed under the
  same 4 GiB cgroup with an ext-family `TMPDIR`; no OOM or kernel I/O fault was
  logged. Workspace-wide rustfmt remains pre-existing red outside the milestone,
  while the new Rust test is focused-format clean. **Next:** preregister and
  implement TL2.11 strict positivity as the primary
  trusted-kernel task; TL1.5 property fuzzing remains an independent hardening
  lane.

- **2026-07-22 — TL1.7 canonical Lean declaration/dependency identity is
  complete; the remaining official inductive fixture matrix is next.** Every
  successful import now publishes `axeyum-lean-declaration-identity-v1` in its
  report: TL0.4-compatible axiom name/rendered-type SHA-256 rows plus a complete
  structural Merkle digest for every admitted declaration and a separate digest
  binding each sorted direct dependency name to its admitted content. The
  encoding covers names, levels, expressions, binder info, literals, all seven
  declaration variants, reducibility hints, inductive/constructor metadata, and
  recursor rules without hashing wire IDs, arena IDs, record order, debug text,
  or JSON spelling. Five focused tests freeze all eight flat-fixture identities.
  Repeated imports and an independent declaration-record reorder agree exactly;
  valid axiom-type, definition-body, and binder-info mutations change their
  intended content/dependency cone. The importer passes 28 cases across three
  binaries plus its example target. Warning-denied Clippy/rustdoc, compile-fail
  doctest, 21 compatibility/prototype/ledger tests, generated compatibility and
  65-row ledger checks, parity prose, foundational resources, focused format/
  diff hygiene, and links pass with two build jobs. Workspace-wide rustfmt is
  not credited because unrelated pre-existing benchmark/CAS drift remains;
  `cargo deny` is also red on the existing unlicensed `axeyum-wasm` manifest
  and benchmark/Rayon `crossbeam-epoch 0.9.18` advisory RUSTSEC-2026-0204. The
  importer reuses the already-locked `sha2` package with no new transitive
  package. See
  [ADR-0350](docs/research/09-decisions/adr-0350-canonical-lean-declaration-identity.md)
  and the [TL1.7 result](docs/plan/lean-declaration-identity-tl1.7-2026-07-22.md).
  **Next:** generate recursive-indexed, reflexive, mutual, nested, and well-
  founded official fixtures with direct-recursive positive controls. TL1.5 is
  dependency-ready for property fuzzing; TL2.11 owns strict positivity before
  semantic admission widens.

- **2026-07-22 — TL1.4's generated Lean import mutation corpus is complete;
  TL1.7 declaration digests were next at this checkpoint.** The new
  deterministic binary generates
  226 unique cases across EOF before every official record, one-byte truncation
  and one unknown top-level field for every official record, nested unknown
  fields, duplicate IDs, forward/self references, a declaration self-cycle,
  bounded/excessive JSON depth, raw/escaped/invalid Unicode, non-ASCII Nat
  digits, integer boundaries, version/exporter drift, and discriminant errors.
  Two full generations/executions produce the same ordered summary:
  `json=67`, `malformed=90`, `kernel=1`, `published=3`,
  `published-unsealed=64`, and `unsupported:format-version=1`. All 65
  record-body truncations reject. The 64 complete-record prefixes publish only
  relative to delivered EOF and are explicitly unsealed with no exact-artifact
  credit because upstream format 3.1 defines no footer, expected count, or root
  manifest. Raw and escaped `λ😀` names admit identically; excessive depth,
  invalid surrogate/numeral, width, topology, and semantic-cycle controls reject
  without panic. The importer now passes 23 cases across two binaries plus its
  example target. Warning-denied Clippy/rustdoc, compile-fail doctest, 14
  compatibility/prototype tests, generated compatibility, parity prose,
  foundational resources, focused formatting/JSON, and links pass. See
  [ADR-0349](docs/research/09-decisions/adr-0349-generated-lean-import-mutation-corpus.md)
  and the [TL1.4 result](docs/plan/lean-import-mutation-corpus-tl1.4-2026-07-22.md).
  **Then:** TL1.7 subsequently added canonical axiom/declaration/dependency
  identities. TL1.5 later adds property fuzzing; TL0.3/TL1.6/TL1.9 own
  external artifact identity and durable completion.

- **2026-07-22 — TL1.3 whole-environment import publication is complete;
  TL1.4 mutation generation was next at this checkpoint.** `import_ndjson` no longer accepts or
  mutates a caller-owned kernel. It stages the full format-3.1 stream in a
  private fresh kernel and returns a field-private `CompletedImport` only after
  EOF and every parse, topology, translation, independent-admission, and
  recursor-comparison check succeeds. The wrapper exposes read-only kernel and
  report borrows plus explicit `into_parts` ownership transfer. Late malformed
  JSON after a complete valid stream, final-declaration kernel rejection,
  quotient decline after dependencies, record exhaustion one line before
  completion, and injected I/O failure after all valid bytes each return only
  `ImportError`; no environment or arena handle crosses the error branch. All
  prior exact fixture reports, declaration order, computations, and repeated-
  import determinism remain unchanged. The importer passes 20 integration
  cases plus its example target; a compile-fail doctest rejects forged
  `CompletedImport` fields. Warning-denied Clippy/rustdoc, 14
  compatibility/prototype tests, generated compatibility, parity prose,
  foundational resources, and documentation links pass. See
  [ADR-0348](docs/research/09-decisions/adr-0348-owned-lean-import-publication.md)
  and the [TL1.3 result](docs/plan/lean-import-transactional-publication-tl1.3-2026-07-22.md).
  **Then:** TL1.4 subsequently generated the 226-case structural mutation
  corpus and made the upstream no-footer prefix boundary explicit. TL1.7
  canonical dependency digests subsequently landed.

- **2026-07-22 — TL2.7 checked Nat literal semantics is complete; TL1.3
  transactional publication was next at this checkpoint.** Natural literals now infer as `Nat`
  only after the independent kernel has admitted the exact canonical `Nat`,
  `Nat.zero`, and `Nat.succ` bootstrap. Definitional equality peels literal/
  constructor offsets in either direction, transparent wrappers do not obscure
  the comparison, `Nat.succ` over a literal reduces without narrowing, and
  `Nat.rec` exposes one literal constructor layer before ordinary iota. Missing,
  renamed, reordered, malformed, and Prop-valued bootstraps reject with a typed
  error; String literals and general accelerated Nat operations remain
  fail-closed. The official format-3.1 Nat root translates all 90 expressions,
  admits ten declarations from five records with zero axioms, and reduces
  `importNatLiteral` to `37`. Boundary replacements at and above `2^128` admit
  exactly, while a renamed `Nat.zero` mutation rejects. A required pinned-Lean
  4.30 differential agrees on zero, unary three, an above-`u128` successor,
  recursor computation, and a false adjacent-value control. The kernel passes
  179 unit tests and 35 integration cases across twelve binaries; the importer
  passes 18 cases; 14 compatibility/prototype tests pass. The generated
  compatibility matrix now records 12 rows, five profile passes, one declined
  row, six source-bound decline codes, and eight assurance fields. Focused
  rustfmt, warning-denied Clippy/rustdoc, doctest, parity-document,
  foundational-resource, and link gates pass; the unavailable `just` wrapper
  was replaced by its exact constituent commands. See
  [ADR-0347](docs/research/09-decisions/adr-0347-checked-lean-nat-literal-semantics.md)
  and the [TL2.7 result](docs/plan/lean-nat-literal-semantics-tl2.7-2026-07-22.md).
  **Then:** TL1.3 subsequently made completed-environment publication
  transactional. TL1.4 mutation corpora and TL1.7 dependency digests have since
  landed.
  TL2.8 still owns
  accelerated Nat operations and TL2.9 owns String literals.

- **2026-07-22 — TL2.6 arbitrary-precision Nat storage is complete; TL2.7
  literal typing was next at this checkpoint.** `Lit::Nat` now carries canonical `NatLit(BigUint)`
  storage, and the official format-3.1 decimal path validates directly into
  that representation without a `u64`/`u128` intermediate. Values at
  `2^128 - 1`, `2^128`, `2^128 + 1`, and a much larger decimal round-trip
  through parsing, interning, structural operations, and Lean rendering.
  Malformed spellings reject before the semantic boundary. The TL2.15 literal
  seed now includes explicit above-`u128` corners while preserving 768 total
  deterministic cases and rejecting every attempted `False` admission.
  Inference remains `UnsupportedLit`; no Nat typing, reduction, or official
  declaration admission is claimed. At this checkpoint the Nat root declines at line 125 with
  the narrower `literal-nat-typing` code. The kernel passes 179 unit tests and
  29 integration cases across ten binaries, the importer passes 16 tests, and
  focused doctest, warning-denied Clippy, and warning-denied rustdoc gates pass.
  See [ADR-0346](docs/research/09-decisions/adr-0346-arbitrary-precision-lean-nat-literals.md)
  and the [TL2.6 result](docs/plan/lean-nat-literal-storage-tl2.6-2026-07-22.md).
  **Then:** TL2.7 subsequently typed Nat literals, implemented checked
  constructor/literal conversion, and closed the exact official Nat closure.

- **2026-07-21 — TL2.5 structure eta is complete; this records the prior
  definitional-equality boundary.** Definitional equality now mirrors Lean's
  symmetric structure-eta rule only for an exactly saturated constructor whose checked
  parent inductive has one constructor, zero indices, and no recursive fields.
  Constructor admission persists the aggregate recursion bit after checking
  fields, so eta eligibility consumes trusted metadata rather than guessing
  from syntax. Seven native integration families cover both directions,
  under-application, a duplicated-field false equality, a wrong structure
  type, zero-field and multi-constructor boundaries, parameters and universes,
  a dependent second field, and explicit indexed/recursive exclusions. The
  required differential runs pinned Lean 4.30.0 commit
  `d024af099ca4bf2c86f649261ebf59565dc8c622`: official Lean accepts the
  reconstruction by `rfl` and rejects the duplicated-field mutation. Under the
  4 GiB bound, the kernel passes 179 unit tests and 25 integration cases across
  nine binaries; warning-denied all-target Clippy and the repository-local-TMP
  doctest pass. The generated TL2.15 projection/reduction/eta fuzz family
  remains open, and no new K1 import population is claimed. See the
  [TL2.5 result](docs/plan/lean-structure-eta-tl2.5-2026-07-21.md).
  TL2.6 arbitrary-precision storage and TL2.7 checked literal semantics have
  since landed; the exact Nat root now admits and computes.

- **2026-07-21 — TL2.4 constructor projection reduction and the exact official
  K1 projection root are complete; this records the prior computation/import
  boundary.** Projection reduction now
  runs in WHNF beside beta/zeta/iota: it normalizes the projected value, requires
  a constructor, skips checked parameters, selects the field, and re-applies any
  outer spine. Four native integration families cover parameterized and
  universe-polymorphic structures, dependent proof fields, transparent versus
  opaque/neutral values, under-application, and Lean's deliberate split where
  reduction follows the constructor but inference rejects a wrong structure
  name. Only after that gate passed did `axeyum-lean-import` translate the wire
  `proj` record. The pinned official stream now translates 61 expressions,
  independently admits nine declarations from four records with zero axioms,
  and computes `importPairLeft (ImportPair.mk 0 1)` to `0`; wrong-name/index
  mutations reject at declaration line 83. The importer suite grows to 14
  tests. Re-running the Nat root moves its first decline to line 125
  `literal-nat-bignum-and-typing`. The compatibility matrix now has four passing
  profiles, two declined rows, and nine live decline codes. This is one exact K1
  root, not `Init`/`Std`/mathlib or native-source parity; the unretained String
  stream's old projection decline is retired without guessing its next blocker.
  See the [TL2.4 result](docs/plan/lean-projection-reduction-tl2.4-2026-07-21.md).
  TL2.5 structure eta, TL2.6 arbitrary-precision Nat storage, and TL2.7 checked
  literal semantics have since landed separately. Both historical Nat decline
  codes above are retired; the exact Nat root now admits and computes.

- **2026-07-21 — TL2.3 dependent projection inference is complete; this records
  the prior typing boundary.** Checked inductive declarations now retain
  parameter/index counts, and `infer(Proj)` follows Lean's single-constructor
  telescope algorithm: it validates the structure head and full argument spine,
  instantiates parameters, substitutes earlier projections into dependent field
  types, and enforces the Prop-elimination restriction. Four integration
  families cover parameterized dependent fields, universe-polymorphism, indexed
  metadata, proof fields, and wrong name/head/arity/constructor-count/index/
  Prop-elimination controls; an internal corruption test rejects inconsistent
  unchecked metadata without panic. Under 4 GiB, the kernel passes 179 unit
  tests and 13 integration cases across six binaries, the importer passes 11
  integration tests while retaining the then-current `expr-projection` decline,
  and warning-denied all-target kernel Clippy passes. At that checkpoint this
  earned native K0 inference credit only: no constructor projection reduced and
  the official projection closure remained untranslated/unadmitted. TL2.5 eta
  was separate, and TL2.15 had not yet gained
  a generated projection/reduction/eta family. See the
  [TL2.3 result](docs/plan/lean-projection-inference-tl2.3-2026-07-21.md).
  TL2.4 has since landed reduction, wire translation, and exact closure
  computation. TL2.5 eta has since landed as its deliberately separate gate.

- **2026-07-21 — TL2.2 first-class projection representation is complete;
  this records the prior structural boundary.** `ExprNode::Proj(NameId, u32,
  ExprId)` and `Kernel::proj` now carry Lean's structure type name, zero-based
  non-parameter field index, and projected expression through interning,
  hashing, exact child metadata, level/term substitution, every de Bruijn and
  free-variable operation, dependency/constant traversal, and both Lean
  renderers. Numeric rendering converts to Lean's one-based field syntax. Four
  new integration tests independently mutate name/index/child payloads, cover
  abstraction/instantiation/lifting/closure, and prove neutral normalization,
  identical-term definitional equality, typed unsupported inference, and
  rollback-clean declaration rejection; renderer coverage also checks
  streaming parity and traversal order. The full 4 GiB package gate passes 178
  unit tests plus nine cases across five integration binaries; warning-denied
  all-target Clippy, all-target checking, and warning-denied rustdoc pass. The
  complete parity-document recipe's direct commands, generated-file checks,
  link checker, touched-file rustfmt, and `git diff --check` are green; `just`
  itself is unavailable on this host. Workspace-wide `cargo fmt --all --check`
  remains red only on the pre-existing unrelated `axeyum-bench`/`axeyum-cas`
  drift. At that checkpoint the importer intentionally retained
  `expr-projection`, the committed official projection closure remained
  untranslated/unadmitted, and TL2.15 gained no semantic seam. See the
  [TL2.2 result](docs/plan/lean-projection-representation-tl2.2-2026-07-21.md).
  TL2.3/TL2.4 have since landed dependent inference, constructor reduction,
  wire translation, closure admission, and the later separate TL2.5 eta gate.

- **2026-07-21 — T6.0.3 closes the current four-seam fuzz seed; TL2.15 remains
  partial by construction.** The new fixed-seed
  [`kernel_seam_fuzz`](crates/axeyum-lean-kernel/tests/kernel_seam_fuzz.rs)
  integration test registers `Prop`/elimination, universes/inductives,
  proof-irrelevance/iota, and literals/reduction as four explicit active bits.
  It runs 768 unique cases: 192 multi-constructor Prop cases; 320 universe cases
  whose first 288 exhaust the `8×4×3×3` universe/constructor/proof-field/data-
  field product; and 256 literal cases spanning Nat 0/1/`u128::MAX`/random plus
  empty/ASCII/Unicode/NUL strings under beta/zeta depths 0–4. Every case reaches
  theorem admission with `False` as the claimed type, rejects, and leaves no
  declaration behind. The complete population runs twice and produces equal
  structured summaries. The focused gate and the complete kernel `--lib
  --tests` package gate pass under 4 GiB: 177 unit tests plus five integration
  tests, including the historical exploit and the locally optional
  official-Lean cross-check wrapper. Forcing that wrapper with
  `AXEYUM_REQUIRE_LEAN=1` fails closed because this host has no Lean binary; no
  fresh official-Lean differential credit is taken for this slice.
  Warning-denied all-target Clippy, all parity-document generators/checkers, the
  link checker, and `git diff --check` are green. Workspace-wide `cargo fmt
  --all --check` remains red only on the pre-existing unrelated
  `axeyum-bench`/`axeyum-cas` drift; the touched Rust file passes standalone
  rustfmt. The [result note](docs/plan/lean-kernel-seam-fuzz-seed-2026-07-21.md)
  records seeds and non-credit: no projection/eta, quotient, typed-literal,
  shrinker, or official-Lean differential claim. TL2.2-TL2.4 representation,
  inference, reduction, and the separately gated TL2.5 eta rule have now
  landed; each admitted seam extends this negative class before receiving
  TL2.15 credit.

- **2026-07-21 — TL0.4 binds the actual 65-assumption prelude boundary.** A
  runtime inventory constructs the real, integer, and string reconstruction
  preludes in independent kernels and enumerates admitted `Declaration::Axiom`
  values. The checked
  [`lean-axiom-ledger-v1.json`](docs/plan/lean-axiom-ledger-v1.json) records 30
  real, 34 integer, and one string assumption with canonical rendered type,
  SHA-256 digest, source, owner, classification, and discharge fields; the
  generated [65-row ledger](docs/plan/generated/lean-axiom-ledger.md) is
  byte-stable. This corrects the old 64-row helper-call census, which missed
  `axeyum.string.append` because it is inserted directly as
  `Declaration::Axiom`. Seven mutation/contract tests reject missing, extra,
  duplicate, renamed, type-mutated, illegally classified, or falsely
  discharged rows, and `parity-docs` reconstructs the preludes under the 4 GiB
  cap. Validation passes 177 kernel unit tests, four integration tests including
  the official-Lean cross-check, all seven ledger tests, the full direct
  `parity-docs` command set, generated-file checks, link checks, touched-file
  rustfmt, and `git diff --check`. The single kernel doctest compiled but could
  not link because both lld and GNU ld hit the host `/tmp`/user quota; 52 GiB of
  regenerable incremental/example cache was removed without touching source or
  evidence. Workspace-wide `cargo fmt --all --check` still fails on the same
  pre-existing unrelated `axeyum-bench`/`axeyum-cas` drift. All 65 rows remain
  explicitly `unclassified`/`unreviewed`; TL0.4 freezes the trust boundary but
  does not prove it. The seam-fuzz seed follows immediately above; projection
  TL2.2-TL2.5 are now landed. TL3.2 owns semantic classification and discharge
  targets.

- **2026-07-21 — TL0.1/TL0.2 close the Lean ownership and assurance
  boundary.** ADR-0167 and ADR-0345 are accepted together: Track 6 owns the one
  goal/tactic engine; the Lean-system program owns versioned import,
  source/workflow/runtime compatibility, and pinned-mathlib build work; neither
  expands the kernel's admission authority. The new
  [`lean-compatibility-v1.json`](docs/plan/lean-compatibility-v1.json) contract
  separates `parsed`, `translated`, `admitted`, `official_admitted`,
  `source_elaborated`, `proof_checked`, `workflow_reproduced`, and
  `runtime_reproduced`. Its generated
  [12-row matrix](docs/plan/generated/lean-compatibility.md) reported four
  profile-passing exact rows (native K0 plus three K1 fixtures), two fail-closed
  K1 declines, and zero completed K2-K6 native profiles at that checkpoint.
  Six tests reject missing assurance fields or
  evidence, translation without parsing, official-oracle credit laundering,
  proof credit without admission, and missing/unregistered/misapplied decline
  codes. `parity-docs` now checks the contract and byte-identical generated
  matrix. Fourteen importer tests pass under the 4 GiB cap; the six contract
  tests, full parity-doc suite, JSON check, generated-file check, and docs links
  are green. `cargo fmt --all --check` remains red on pre-existing committed
  formatting drift in unrelated `axeyum-bench`/`axeyum-cas` Rust files; this
  slice does not rewrite them. TL0.4 follows immediately above; next is the
  now-landed T6.0.3/TL2.15 seam-fuzz harness, now-landed TL2.2-TL2.5
  projection representation/inference/reduction/eta sequence, and now-landed
  TL2.6 arbitrary-precision Nat storage. TL2.7 has since closed checked literal
  semantics, TL1.3 has closed atomic publication, and TL1.4 has closed the
  generated mutation corpus; TL1.7 has since closed canonical declaration and
  dependency identity.

- **2026-07-21 — the complete Lean-system implementation program is now an
  executable plan, not a list of missing subsystems.** The active
  [implementation plan](docs/plan/lean-system-implementation-plan-2026-07-21.md)
  defines checker-through-ecosystem profiles K0-K6, a common ten-part
  definition of done, crate/TCB ownership, parallel lanes, task IDs TL0.1
  through TL10.9, milestones M0-M7, and a 23-item immediate queue. It covers
  the production exporter reader, kernel projection/literal/quotient/inductive
  breadth, axiom discharge and selected libraries, the existing Track 6
  bridge/goal/tactic work, native parser/macros and elaboration, modules/caches,
  Lake and version-specific `.olean` compatibility outside the TCB, LSP,
  compiler/runtime/metaprograms, and a full pinned mathlib build. The first
  execution slice is TL0.1/TL0.2 contract reconciliation and capability schema,
  through the now-landed T6.0.3/TL2.15 fuzz seed; kernel semantics advance one
  measured slice at a time, and TL2.2-TL2.5 projection representation,
  inference, reduction/import, structure eta, arbitrary-precision Nat storage,
  and checked Nat literal semantics are now complete. The plan removes
  the rewrite-provenance/`simp` dependency cycle and makes selected mathlib
  imports and native source/workflow compatibility explicit owners rather than
  contradictions in Track 6 scope prose.

- **2026-07-21 — the Lean-system roadmap objective passes its completion
  audit; implementation remains open.** The
  [requirement audit](docs/plan/lean-system-roadmap-completion-audit-2026-07-21.md)
  maps all eight originally named gaps plus the detailed-roadmap and
  actual-assets requirements to current evidence, architecture, phase sizing,
  and exits. Fresh local inventory records 13,929 CAS source lines, exactly 56
  default canonical rules, a 19-covered/4-Lean-horizon curriculum, 137 concepts,
  173 non-template packs, 1,131 result rows (399 checked / 596 replay-only / 136
  Lean-horizon), 173 promoted solver-reuse packs, and 249 math learning files.
  Shallow tagged-tree checks reproduce Lean v4.30.0's subsystem scale and
  mathlib v4.30.0's 8,606 `.lean` files plus every listed directory count.
  Focused kernel/import validation passes 177 kernel unit tests, four kernel
  integration tests, one doctest, and eleven importer tests under 4 GiB. This
  completes the requested research/design/prototype/documentation deliverable,
  not Lean parity: ADR-0345 is accepted and L0-L10 implementation resumes
  with projection-first L2, axiom contracts, and the remaining fixture matrix.

- **2026-07-21 — Lean-system distance is now decomposed and a real import seam
  is prototyped.** The new
  [compatibility roadmap](docs/plan/lean-system-compatibility-roadmap-2026-07-21.md)
  distinguishes independent kernel admission, official source acceptance,
  declaration import, language compatibility, and workflow/ecosystem
  compatibility. It audits the actual assets rather than repeating the gap
  list: the pure-Rust kernel already has environments/reduction/definitional
  equality/type checking/selected inductives; Track 6 already owns goals,
  holes, delayed assignment, and certificate tactics; the
  13,929-line CAS, 56-rule canonical manifest, and 173 validated math packs are
  candidate proof engines and theorem targets, not mathlib coverage. Proposed
  ADR-0345 chooses both bridge directions, sequenced: retain fail-closed
  official source validation, then consume pinned `lean4export` NDJSON and
  independently admit supported declarations. A fresh official Lean 4.30 /
  export-format 3.1 fixture contains 14 names, two nonzero universe levels, 43
  expressions, and five declaration records; the Python reader reports no
  inventory blockers on that flat slice and passes six fixture/mutation tests,
  including the direct-recursive inventory.
  The new separate `axeyum-lean-import` Rust crate now independently admits the
  same stream as eight kernel declarations through checked public gates. A
  second official, byte-reproducible fixture admits direct-recursive `MiniNat`
  and parametric-recursive `MiniList`: 30 names, four nonzero levels, 130
  expressions, and five records become 11 checked declarations with no axioms.
  Its first import exposed alpha-equivalent fresh recursor universe names
  (`u_1` from official Lean versus `u.1` from Axeyum); the importer now
  alpha-renames exported universe binders before definitionally comparing the
  recursor type and iota-rule RHSs. Theorem-body and recursor-rule tampering
  reject among the original eleven Rust tests (now fourteen after TL2.4). The
  flat result still reports `axioms=P`, so
  the assumption is not converted into a theorem. This is exact flat and
  direct-recursive fixture credit, not `Init`/`Std`/mathlib or general kernel
  credit. Direct `.olean` reading remains rejected; official Lean is an optional
  sandboxed frontend/workflow adapter while the default checker remains pure
  Rust. A new four-root official census freezes exact projection, Nat, String,
  and quotient closures. Projection is the only blocker in its four-declaration
  closure and the first product decline for both literal roots. The String root
  expands to 290 declarations and also contains 27 projections, 20 Nat
  literals, one String literal, and recursive-indexed inductives; quotient is an
  isolated five-record closure. Three small streams are committed, the 570,807-
  byte String stream is source/command/hash bound, consecutive exports are
  byte-identical, and eight Python tests hash/inventory the evidence. **Next:**
  review ADR-0345 and the crate/TCB boundary, implement projection
  representation/inference/constructor reduction, generate the remaining
  recursive-indexed/mutual/nested/reflexive fixtures plus the assurance matrix,
  then retain the now-landed runtime/type-digested 65-assumption ledger before
  any native parser, Lake, LSP, or compiler work. See the
  [measured import result](docs/plan/lean4export-rust-import-prototype-2026-07-21.md)
  and [official blocker census](docs/plan/lean4export-official-blocker-census-2026-07-21.md).

- **2026-07-21 — the representative official-Lean gate is now locally real and
  fail-closed.** Primary-source inspection showed that `leanprover/lean-action`
  required a Lake manifest even though Axeyum only needs standalone Lean; a
  checksum-pinned elan installer now follows `lean-toolchain` without inventing
  a Lake project. Executing the previously blocked gate exposed four real
  quantified-BV exporter failures (67/71), fixed narrowly by retaining the
  required Bool/BV inductive computation and a self-contained measured
  `maxRecDepth` option. Two corrected official-Lean 4.30 runs accept 71/71 with
  zero skips/failures, and the missing-binary negative control now fails. Local
  duration varied materially (6.8 s and 53.3 s in the Lean-worker phase), so no
  speed claim is attached. **Next:** push the repaired workflow, require one
  remote 71/71 attestation with version/duration/RSS, then inventory expected
  axioms before sizing the exhaustive sweep. See the
  [gate audit](docs/plan/official-lean-ci-gate-audit-2026-07-21.md).

- **2026-07-21 — G1 now has a shared measurement schema, and the two headline
  populations overlap materially.** The generated 53-row provenance matrix
  gives the 35-row scoreboard and 18 public-inventory logic strata one
  raw/path/content/selection/scoring/oracle vocabulary without merging scores.
  Exact inspection contracts 927 scoreboard file occurrences to 837 normalized
  paths and 778 unique contents; 58 exact-alias groups remove 59 further path
  identities, while 65 synthetic cases remain aggregate-only. The 228-file
  public inventory is exact-byte unique but shares 99 contents with the
  scoreboard (43.4% of the public view), so it is not independent replication.
  Row-local PAR-2 is present for all 53 rows; both current regimes are
  non-official and have zero neutral-oracle rows on their exact populations.
  Proposed ADR-0343 forbids a global aggregate. Next: review that policy, then
  archive and validate the newly produced full-library candidate selection/run,
  then prototype mutation-tested syntax normalization before any deduplicated
  score. Concurrent commit `d9e71e21` adds explicit-file execution, a 2024
  full-tree cap/family selector, and the s4-s7 distributor. Its external
  manifest records 438,631 pool / 64,345 selected across 84 logics. The first
  52-shard 300-second run is now frozen incomplete: all workers stopped after
  2,041 total progress rows (36-44 per shard), no raw shard JSON exists, and no
  traceback explains the termination; remote `dmesg` is permission-denied, so
  OOM is unverified rather than ruled out. End-of-shard-only raw output made the
  partial work non-mergeable. Do not rerun unchanged; first
  preregister atomic checkpoint/resume records, terminal shard status, strict
  merge completeness, interruption equivalence, and aggregate memory controls.
  This is not yet committed measurement evidence or an official selection: the current selector does not bind the full
  eligibility/status/difficulty filters, official release/seed, corpus-tree
  digest, or per-file hashes. Do not add its numbers to the public matrix until
  a versioned complete result and those omissions are explicit. The exact
  selection hashes, failure snapshot, and safe resume checks are in the
  [candidate-run handoff](docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md).
  Accepted ADR-0344 now supplies the v2 E0 contract: 18 invariants and 28
  executable scenarios (five accepted controls, 23 rejected mutations), with
  deterministic interrupted/resumed and uninterrupted scoring projections
  byte-identical. V2 supersedes the committed v1 prototype before integration:
  it adds per-result attempt attribution, typed process termination,
  observed-vs-admitted verdicts, content-addressed outputs, and complete policy/
  source/toolchain identity. It separates terminal-less failed attempts from later honest
  shard completion, rejects silent duplicate overwrite and identity/resource
  drift, and requires a complete shard set before scoring. E1a implements the local
  immutable record boundary and passes 8/8 real `SIGKILL` recovery cells over
  tmpfs and the worktree's ext-family filesystem. Identical records skip,
  conflicting/truncated artifacts quarantine without overwrite or promotion,
  filename/key drift rejects, and all recovered canonical bundles equal the
  uninterrupted control. This does not test power loss, NFS, solvers, leases,
  cgroups, or remote hosts. E1b now integrates the opt-in writer and fake solver
  into the active runner, makes completion last, rejects duplicate raw merge,
  verifies byte-exact output sidecars, preserves timeout-observed responses
  under the registered SMT-COMP 2026 policy, removes signal-to-OOM guessing,
  records attempt lifecycle, and defines explicit single-owner recovery. Its
  E2 now launches all registered shards under one exact aggregate
  user-systemd/cgroup-v2 envelope, records immutable preflight/counter/terminal
  evidence, rejects resource overcommit and environment drift before launch,
  and preserves terminal-less resource sessions through host-runner kill and
  explicit lease recovery. E3 now passes repeated three-host shared-NFSv4.1
  uninterrupted and exact host-runner-loss controls with content-bound source,
  preregistered different-host retry, exact fault/recovery evidence, central
  completion, and identical timing-free outcome projections. Next: complete
  the independently versioned official-style selection ledger. Do not rerun
  the 64,345-file candidate first.

- **2026-07-21 — the public project state no longer requires reading the battle
  logs.** `docs/PROJECT-STATE.md` now separates implemented surface, committed
  measurements, selected-fragment parity, production Z3 distance, solver-proof
  export, Lean-core compatibility, and explicitly out-of-scope full Lean-system
  replacement. README, the docs hub, limitations, and benchmarks now route
  through that page and no longer claim every UNSAT is certified, describe
  WHNF/type checking as future work, turn finite differential evidence into
  universal soundness, or publish the superseded p4dfa 3/20/60-second narrative.
  `scripts/check-parity-docs.py` now guards these public pages and derives the
  project-state solver/proof denominators from the committed artifacts. The
  follow-on `gap-ownership-v1.json` manifest and generated contributor map route
  all G0-G10 gaps to owner paths, evidence, executable gates, ADR anchors, and a
  next safe action; path and gap-title drift fail generation. Three gaps expose
  the absence of a gap-specific ADR rather than inventing one. Next: use this map
  for the next behavior-preserving namespace/module split; do not expand the
  executive page back into a second STATUS.

- **2026-07-21 — the ordered SMT-LIB session contract is prototyped, and the
  real gap includes signature scope.** The official SMT-LIB 2.7 state machine,
  current parser/helper source, Z3 command-context source, and bounded local
  Bitwuzla transcripts show that declarations/definitions are scoped by
  `push`/`pop` by default, `reset-assertions` removes non-global declarations,
  output options take effect immediately, inspection commands bind to the
  exact most-recent query, and continued errors must be atomic. Axeyum currently
  has one shared arena, global parser environments, final option maps, output
  no-ops, full-reset rejection, and silent pop underflow. The new executable
  planning model checks 14 invariants and 20 fixtures / 107 commands with zero
  mismatch; nine deliberate errors continue into a verified unchanged state.
  Proposed ADR-0342 pins SMT-LIB 2.7 and stages the work as complete ordered
  command/event capture (S1), exact query snapshots, scoped external-name
  environments plus reset epochs, option enforcement/rendering, then facade
  convergence. No production behavior or conformance claim changes yet. Next:
  review ADR-0342 and implement S1 only if accepted.

- **2026-07-21 — SMT-LIB/API distance is now measured by command behavior, not
  helper presence.** The new machine-readable 30-row conformance manifest and
  generated matrix distinguish six axes that prior P4.4 prose collapsed:
  parser state, execution mode, output representation, assurance, exact test
  evidence, and residual scope. The audited snapshot has six absent command
  families, seven accepted no-ops, eight globally recorded surfaces, five
  command-point surfaces, three semantic definitions, one explicit rejection,
  27 rows with exact named tests, and zero ordered interactive-text rows. Models,
  values, assignments, scoped assertions, info/options, cores, Alethe proofs,
  and optimization already have bounded Rust helpers; interpolation, Horn, and
  abduction already have verify-before-return direct APIs. The actual P4.4
  blocker is one command-point textual session runner with option/lifecycle
  semantics, not another theory seed. `scripts/gen-smtlib-api-conformance.py
  --check` verifies source markers, negative parser assertions, named tests, and
  generated drift and now runs in the parity/docs gates. The follow-up session
  contract now defines the event/result IR, transcript invariants, signature
  scope, and reset-epoch requirements; retain production full `reset`, recursive
  definitions, and textual categorical commands as explicit negative controls
  until their separately gated implementation slices land.

- **2026-07-21 — Categorical-engine roadmap drift is corrected; depth is the
  gap.** Source/public-API/decline inspection plus a hard-4-GiB sequential run
  passes 125/125 focused tests: 94 interpolation, 22 CHC/Horn, and nine
  abduction. Six interpolation families have canonical direct APIs; Horn handles
  Real and Bool/BV state, stratified multi-predicate systems, compatible mutual
  SCCs, and lower-stratum nonlinear folding with source-clause reverification;
  abduction performs bounded synthesized shared-vocabulary search with mandatory
  consistency/sufficiency/vocabulary checks. These are seeded or selected-
  fragment implementations, not absent engines. Next work is textual
  conformance, representative Z3/cvc5/Spacer corpora, Horn theory/nonlinear
  depth, and portable certification. General SyGuS remains absent and separately
  demand-gated. The durable audit is
  `docs/plan/categorical-engine-depth-audit-2026-07-21.md`.

- **2026-07-21 — Proof-gap population is refreshed under dominance schema v2;
  causal tracing is next.** The eight rows containing every historical bare
  UNSAT were rerun sequentially in release mode: 211 decided instances retain
  zero verdict mismatches/timeouts, with only the two known QF_NIA `IntPow2`
  evidence-production errors. The live residual is 58 occurrences / 56 paths /
  51 exact contents, all independently unchecked and backend-attributed:
  string front door 31, `auto-solve` 15, NRA fallback 12. Four stale QF_SEQ rows
  created before the string evidence soundness fix lose DRAT credit because the
  old proof covered only the bounded/flat lowering. Use those as the first
  `source-side-channel-not-serialized` trace case, then land stable attempt/
  boundary and obligation IDs across all four bare exits only after proposed
  ADR-0341's invariance/mutation gates are reviewed. The eight
  reconstruction-only gaps remain an independent lane: five quantified-BV
  selected certificates and three QF_NIA Alethe proofs should be consumed
  directly by a bounded Lean prototype before any new theorem family is added.
  The first selected-evidence prototype now closes two BV rows directly (15 KB
  closed-universal and 18.5 MB paired-existential modules). Phase telemetry now
  separates the three remaining BV rows: `bug802` exceeds a hard 4 GiB cap in
  scoped kernel closure after its 8,524-command tail; `small-pipeline-fixpoint-3`
  closes the kernel in 7.744 seconds below 600 MiB, then misses 30 seconds before
  module spooling; and `cond-var-elim-binary` emits a 15,705-command residual by
  2.607 seconds below 525 MiB, then misses 30 seconds in CPS tail reconstruction.
  The three QF_NIA proof
  objects now also reconstruct directly through the existing EUF consumer:
  6/15-command congruence+resolution proofs produce 2,916/8,082-byte modules in
  about 0.10 seconds below 9.5 MiB RSS. Their prior `la_generic` failures were
  source-syntax route misclassification, not missing arithmetic proof theory.
  Five of eight diagnostic rows are existing-consumer plumbing wins. Profile
  the three distinct kernel-closure, compact-spooling, and CPS-reconstruction
  mechanisms under the existing 4 GiB/30-second bounds before selecting a
  production evidence-aware dispatch boundary; do not raise the cap or add a
  theorem family.

- **2026-07-21 — T5.4.3 reason-preserving directed-fuzz implementation is
  pushed, acceptance remains WIP (`3d75d407`, ADR-0340).** The new public
  `axeyum_verify::directed_fuzz` boundary composes the checked `prove`
  trichotomy, exact input domains/guards, sharing-preserving SMT-LIB,
  deterministic corner/LCG sampling, and caller-owned source callbacks.
  Proved and replay-confirmed solver refutations remain decided outcomes; only
  a genuine structured `UnknownReason` emits a canonical QF_BV target and
  sampled `fuzzed-only` report. Four unit and three integration tests cover the
  three branches, callback isolation, failed replay, oracle disagreement,
  repeatability, width-128 sampling, JSON controls, and independent exhaustive
  semantics of the embedded two-input violation query. Strict targeted Clippy,
  the complete `axeyum-verify` package, warning-denied rustdoc, and docs links
  pass inside the 4 GiB cap. Adding the direct SMT-LIB edge exposed a stale
  authenticated fixture lock and hash; the minimal one-edge/hash repair now
  passes both the capture and authentication regressions.
  Next: finish ADR-0340's rejection-family matrix, exact target/report fixtures
  and mutation identities, then run every frozen capped gate before acceptance.
  Glaurung integration, T5.4.4 coverage, multi-oracle publication evidence,
  concretization, symbolic memory, and performance remain separate.

- **2026-07-21 — ADR-0339 accepts deterministic replay-checked witness corpora
  (T5.4.2 DONE).** Full-width signed interpretation and all native signed/
  unsigned scalar/array boundary literals are regression-owned. Typed,
  fail-closed admission replay-checks a macro overflow, normally returning
  source-postcondition violation, and raw QF_BV equivalence refutation before
  producing a lexical corpus. Exact committed artifacts are 1,404-byte JSON
  (`fa44878a...6575`) and 712-byte generated Rust (`7e161d41...0bef`); reverse
  insertion reproduces both, a witness mutation changes both, and the exact
  generated tests compile and execute. The complete package, strict Clippy,
  warning-denied rustdoc, and current 129-test/12-binary reflection gate pass
  inside the 4 GiB cap. Next: preregister T5.4.3's honest `Unknown` -> directed-
  fuzz handoff. T5.4.4 coverage accounting, symbolic memory, performance, and
  automatic filesystem/git writes remain out of scope.

- **2026-07-21 — ADR-0334 accepts authenticated Tock capture v3.** Pushed
  producer `b2ad2641` corrects v2's merged-registration replay error, then
  produces two raw-identical 2,651,673-byte
  modules (`f9a1e155...`), both helpers admitted, 1.105/1.033 s builds,
  289,104/288,312 KiB peak RSS, and zero path leaks/partial/OOM deltas. T5.5.2
  capture/parser admission is closed. Next: preregister a zero-row T5.5.3
  proof/replay/scoreboard protocol before any query. ADR-0335 now freezes eight
  certified proof rows, six native-oracle-replayed controls, exact limits,
  pushed-HEAD archive isolation, and an atomic scoreboard. The ignored runner,
  producer/registration, five protocol tests, independent-spec test, strict
  Clippy, and full package suite pass; the authenticated test remains skipped.
  Pushed `7c3960c9` preflight stops before Cargo on HEAD's sole absolute corpus
  symlink. Pushed correction `8d059285` requires that exact link set, omits all
  links, and hash-checks required regular inputs. Local HEAD/tracking/remote now
  match and the repeated refs/capture/registration/archive preflight passes.
  The sole v1 invocation is now frozen negative: Cargo rejects archived HEAD's
  stale committed `Cargo.lock` under `--locked --offline` before compilation.
  Zero property queries/proofs/controls/rows run, cleanup leaves no output, and
  no OOM-delta failure is reported. Never rerun v1. Next: commit/push the exact
  negative, then preregister v2 with only a corrected committed lock snapshot.
  Negative commit `4a640e2b` is pushed. Clean archived-HEAD offline resolution
  adds only the missing `axeyum-cas` lock row and exactly matches the existing
  workspace lock bytes (`e9da054b...181f`); commit/push that isolated sync next.
  Full metadata subsequently lacks cached `wasip2`, so the successor retains a
  separate exact targeted locked-offline preflight before any query.
  Lock commit `3903223c` is pushed. ADR-0336 now freezes v2's only permitted
  correction: the matching committed lock hash plus versioned schemas/new
  output, with every proof/control/solver/trust/replay/resource gate unchanged.
  A pushed archived-HEAD compilation may run only the non-authenticated
  independent-spec test before the one official invocation. No v2 bytes/query.
  ADR commit `3492f422` is pushed. The thin wrapper/registration, five focused
  plus five inherited tests, and live lineage/capture validation pass with no
  v2 output. Next: commit/push exact producer bytes, then run only the frozen
  archived-HEAD non-authenticated compilation preflight. No target query yet.
  Producer commit `07b22549` is pushed. Its fresh archived-HEAD locked/offline
  compilation passes under the cap with exactly one independent-spec test and
  the authenticated test filtered out; `proof-v2` remains absent. Next:
  commit/push this zero-query gate, verify refs/output, then invoke v2 once.
  The sole v2 invocation is frozen negative after one target query: width-32
  `defined` returns `Proved`, but BitBlast is uncertified while Tseitin and
  SatRefutation are certified. The all-certified gate correctly grants zero row
  credit; no control/later proof runs, no output survives, and no OOM-delta
  failure is reported. Never rerun/weaken v2. Next: commit/push the exact
  negative, then audit the existing lowering-evidence path before a new ADR.
  The audit finds the existing `certify_qf_bv_unsat_end_to_end_within` route,
  which composes and rechecks a faithfulness-miter DRAT plus final-refutation
  DRAT. ADR-0337 now freezes v3 as a narrow positive-row API correction with an
  honest split proof/control policy; target semantics and controls are unchanged.
  Commit/push this zero-result ADR before implementation. No v3 query exists.
  ADR commit `27bcabdc` is pushed. V3 now selects/rechecks the dual-DRAT route,
  reports both certificate halves, and preserves controls. Ten Python protocol
  tests, two ordinary Rust tests, a small non-target route smoke, and targeted
  Clippy pass under the cap; `proof-v3` is absent. Next: commit/push exact bytes,
  then run only the archived non-authenticated compilation preflight.
  Producer `635e7cbd` is pushed. Its fresh archived locked/offline build passes
  under the cap in 37.77 s with one independent-spec pass, two filtered tests,
  no authenticated execution, and absent v4 output. Next: commit/push this gate,
  verify refs/output, then invoke v4 once.
  V4 is accepted at pushed runner `5267d6a5`: eight dual-DRAT proofs, six
  reflected/native-replayed controls, UNKNOWN=0, DISAGREE=0, stable identity
  `c4acae04...a37c`. Total query time is 12.700 s, hardest 64-bit rows are
  4.887/6.273 s, peak RSS is 1,256,496 KiB, and OOM deltas are zero. The committed
  certificate-hash summary matches the ignored full result. T5.5.3 is DONE;
  next commit/push acceptance, then write the honest T5.5.4 comparison.
  Producer `c22734c3` is pushed and its fresh archived locked/offline preflight
  passes under the cap in 38.32 s: one independent-spec pass, two filtered tests,
  zero authenticated execution, and no v3 output. Next: commit/push this gate,
  verify refs/output absence, then invoke v3 exactly once.
  The sole v3 run is frozen negative after the Rust test exits successfully:
  all eight proof/rechecks and six controls complete, but the outer parser counts
  7 rows because the test harness prefixes the first `TOCK_PROOF` marker on its
  status line. No result/output is credited and no OOM-delta failure is reported.
  Never rerun v3. Next: commit/push the exact negative; any successor changes
  only prefix-aware extraction plus failure-source/log retention.
  Negative commit `6c0e550c` is pushed. ADR-0338 freezes v4 as parser-only:
  recognize one first proof marker after the exact authenticated-test harness
  prefix and feed normalized output to every unchanged v3 validator. Commit/push
  the zero-result ADR before implementation. No v4 query/output exists.
  ADR commit `c9fa897e` is pushed. The thin wrapper/registration pass seven
  parser/lineage tests, reject wrong/duplicate/non-proof prefixes, preserve all
  v3 inputs/policies, and leave `proof-v4` absent. Next: commit/push exact bytes,
  then run only the archived non-authenticated compilation preflight.

- **2026-07-21 — ADR-0332 accepts the authenticated dedicated Cargo cache.**
  Pushed v5 passes DNS/fetch, 3,077-row hard-link-aware inventory (`fd6ee33d`),
  structural authentication of 162 active nodes / 814 edges against 169 lock
  entries (`da6971e4`), unchanged read-only/offline replay, independent
  inventory recomputation, and zero OOM deltas. The 41.18 MB distinct-byte
  cache remains ignored local input and feeds accepted capture v3. No property
  query or scoreboard row exists.

- **2026-07-21 — ADR-0331 accepts the exact metadata-count negative.** Pushed
  v4 passes DNS/fetch and hard-link-aware inventory, then read-only metadata
  returns 162 resolved packages and fails the invalid inherited equality to all
  169 lock entries. No cache/build/capture/query/partial/OOM result survives.
  V4 is closed. Next: preregister structural resolved-ID-to-lock authentication
  for v5, recording rather than expecting the resolved count.

- **2026-07-21 — ADR-0330 accepts the exact cache hard-link negative.**
  Pushed producer `384e2045` passes real DNS and completes the locked fetch.
  Inventory then rejects Cargo/libgit's legitimate firmware pack-index hard
  link between `git/db` and `git/checkouts`. No inventory/offline probe/cache/
  build/capture/query or partial output exists, with no OOM-delta failure. V3
  is closed. Next: preregister canonical hard-link alias rows for v4 while
  preserving every other preparation gate.

- **2026-07-21 — ADR-0329 accepts the exact cache-preparation DNS negative.**
  Pushed producer `de343f63` starts the locked Flux fetch, but its constructed
  root binds `/etc` without the runtime target of the host `resolv.conf`
  symlink. Three DNS attempts fail before any download; zero cache/inventory/
  probe/build/capture/query or partial output exists, with no OOM-delta failure.
  Preparation v2 is closed. Next: preregister a minimal hash-pinned resolver-
  file bind and actual DNS probe as v3, retaining all non-network gates.

- **2026-07-21 — ADR-0328 accepts the exact Tock capture v1 cache negative.**
  Pushed producer `a2051514` accepts every frozen identity but the official
  locked-offline metadata preflight cannot find cached `ghash 0.4.4`. Zero
  builds start, no module/extraction/admission/query or target/partial output
  exists, and no OOM-delta failure is reported. V1 must not be rerun after
  refilling the observed ambient cache. Next: preregister a v2 dedicated,
  checksum-validated cache-preparation and inventory protocol before any
  networked preparation or successor official build.

- **2026-07-21 — ADR-0327 accepts checked Tock `range`/`ctlz` semantics.** The
  frontend now types and canonically retains one non-wrapping call-result range
  plus exact `llvm.ctlz.iN` zero-poison semantics without adding an IR operator.
  Range and zero poison affect definedness, including selected-arm behavior;
  exhaustive widths 1--8, deterministic 32/64-bit rows, independent
  threshold-partition proofs, and zero/index/range/high-partition mutations
  pass. The standing gate is 82 variants / 18 groups / 12 binaries / 129 tests
  inside the one-job 4 GiB scope. Next: preregister the authenticated offline
  Tock capture; no target bytes, target proof, or scoreboard row exists yet.

- **2026-07-21 — ADR-0327 selected Tock integer logs and preregistered their
  checked frontend prerequisite (accepted above).** Exact Tock `ac5d597d`
  supplies two public, source-used 32/64-bit helpers; a non-crediting
  owning-kernel build emits both as one-block LLVM 22. At preregistration the
  parser failed closed on `range`
  before `llvm.ctlz`. ADR-0327 freezes typed range-to-poison, exact zero-poison
  ctlz lowering over existing BV terms, canonical syntax, independent proofs,
  mutations, and exhaustive/deterministic fuzz. The entry above records that
  accepted gate; no Tock capture or proof result is authorized yet.

- **2026-07-21 — ADR-0326 closes the Maestro capture route negative.** The
  corrected stable-root namespace reaches the first Cargo build, but upstream
  `build/font.rs` tries to fetch the configured GNU Unifont URL. The frozen
  network-isolated namespace fails name resolution before LLVM emission: 0/1
  builds complete, no extraction/parser/solver work starts, atomic output is
  absent, and the kernel OOM audit is clean. Do not add a v4 network/font-cache
  exception. Next: preregister replacement external-target/build-route
  selection for T5.5.2; keep proofs blocked until authenticated capture passes.

- **2026-07-21 — ADR-0326 preregisters stable-virtual-root Maestro capture.**
  V3 gives two independent physical source/target trees identical visible
  `/axeyum-vroot/source` and `/axeyum-vroot/target` paths through registered
  unprivileged Bubblewrap, uses no remap flags, requires zero host-path tokens
  and raw module equality, and only then allows extraction/parser admission.
  Next: implement/run this final bounded build-route correction; proofs remain
  unauthorized.

- **2026-07-21 — ADR-0325 rejects dependency-wide remapping as insufficient.**
  Both v2 modules contain zero real-root tokens and seven shared canonical-
  prefix occurrences, proving the dependency path-text leak is gone. Raw
  modules still differ (36,037,894 vs 36,038,325 bytes; 43.787/44.319 s;
  999,196/999,272 KiB), so the root-specific remap rule remains an identity
  input. The run stops before extraction/parser/solver work. Next: preregister
  independent physical roots at identical virtual source/target paths via the
  working unprivileged namespace route; do not normalize output.

- **2026-07-21 — ADR-0325 preregisters the dependency-wide-remapped Maestro
  capture.** The fresh v2 protocol uses exact Cargo-encoded target flags to
  preserve upstream symbol export and remap every dependency, removes the
  final-crate-only remap, requires zero real-root tokens and raw full-module
  equality, then rediscovers and parser-admits the three selected definitions.
  It cannot normalize ADR-0324 bytes or run proofs. Next: implement and execute
  this bounded T5.5.2 retry.

- **2026-07-21 — ADR-0324 identifies dependency-wide source-path leakage in
  the Maestro build protocol.** Its complete 40,665,637-byte diff classifies
  319,598 changed lines and finds seven absolute `utils` paths per module. The
  trailing rustc remap reached only the final kernel crate, cascading through
  symbols and metadata. All three selected functions pass scalar admission at
  6/5/13 instructions, but all symbols/current canonical hashes differ, so the
  frozen negative branch fires and no capture credit exists. Next: preregister
  a fresh dependency-wide-remapped two-root build; do not normalize these
  modules or use name-erased bodies.

- **2026-07-21 — ADR-0324 preregisters a non-crediting Maestro root-drift
  diagnostic.** It reuses ADR-0323's exact two builds, retains their external
  bytes only under ignored local storage, classifies every complete-diff line,
  detects absolute-root and symbol drift, and compares the three extracted
  checked typed projections. The diagnostic cannot normalize retroactively,
  revise ADR-0323, accept T5.5.2 from selected-function equality, or run a
  solver. Next: implement and execute this bounded causal audit.

- **2026-07-21 — ADR-0323 rejects the first Maestro external LLVM capture.**
  Both isolated offline owning-kernel builds completed under the cap (43.945 s
  / 998,932 KiB and 44.921 s / 1,000,360 KiB), but the frozen full-module gate
  failed: 36,037,712 bytes at `89b26e83…` versus 36,038,199 bytes at
  `56bc0a40…`. The run stopped before extraction, parser admission, or solving;
  atomic cleanup retained no external bytes. T5.5.2 remains open. Next:
  preregister a non-crediting root-drift diagnostic, not a retroactive
  normalization or selected-function-only identity.

- **2026-07-21 — ADR-0323 preregisters the Maestro external LLVM capture.**
  Before any official target byte or parser result is observed, the proposed
  T5.5.2 protocol freezes exact upstream/source/compiler/tool identities, two
  isolated byte-identical full-kernel builds, deterministic extraction of the
  three selected symbols, current-parser admission, atomic failure classes,
  and a local-only boundary for third-party-derived bytes. Only the known
  extraction `ModuleID` path line may be ignored; a full-module drift or parser
  decline is a negative result. Next: implement and run this gate without
  constructing or solving an inverse-property query.

- **2026-07-21 — P5.5 T5.5.1 selects Maestro device-number encoding.** The
  exact external population is `major`/`minor`/`makedev` at Maestro revision
  `650a3f62`. A disposable pinned owning-kernel build proves capture
  feasibility and emits all three as single-block scalar LLVM, but no upstream
  bytes or verification result are retained or credited. The selection note
  freezes the universal inverse properties, candidate comparison, P5.1 gap
  analysis, and a hard no-vendoring gate until the GPL-derived artifact
  distribution/attribution boundary is resolved. Next: preregister T5.5.2's
  exact whole-module capture and deterministic three-function extraction.

- **2026-07-21 — ADR-0322 accepts the P5.3 obligation catalog and bounded v1
  phase exit.** Separate pages for control-flow constant-time, bounded
  memory/page-table math, and FSM refinement expose their exact goals,
  fragments, evidence/authenticity routes, worked examples, reproduction
  commands, controls, and residuals. The comparison index is linked from Track
  5 and the primary Verify scoreboard. The fresh T5.3.1 reproduction passes
  4/4 tests in 0.10 s wall / 53,604 KiB peak RSS; the other pages retain their
  frozen accepted measurements and each focused suite passes 6/6. The catalog
  does not upgrade T5.3.1's MIR-text provenance or the bounded scope of the
  authenticated cells. P5.3 residuals remain future evidence-gated work; the
  next phase-level Track 5 milestone is P5.5 external-target measurement.

- **2026-07-21 — ADR-0321 accepts compiler-reflected handshake refinement.**
  Four fresh owning-Cargo captures are byte-identical to one authenticated
  2,691-byte raw module. Eight universal per-event proof groups and complete
  transition-relation equality pass under identity refinement; the declarative
  spec and reflected implementation are PDR-safe; and the blind-injection
  control is PDR/BMC/source replayed. Exactly 2,048 exhaustive
  reflection/spec/Rust rows have zero disagreement, error, panic, or drop, and
  nine semantic mutations have teeth. No production semantics or public API
  changed. This closes bounded deterministic scalar T5.3.3 v1 only; T5.3.4 and
  broader protocol/liveness work remain open.

- **2026-07-21 — ADR-0320 closes bounded T5.3.2 v1 with authenticated evidence.**
  Four fresh owning-Cargo captures are byte-identical to one committed
  8,218-byte raw module with root-independent provenance and two typed
  summaries. Seven universal reflected panic/spec/alignment/permission claims
  pass; three deliberately broken walks produce replayed source witnesses; and
  the exact 4,096-row sampler has zero disagreement, evaluation error, panic,
  or dropped row. Twelve semantic/authentication mutations have teeth. No
  production semantic form changed, the 81-variant inventory is unchanged,
  and this is a four-entry obligation shape rather than an MMU claim. P5.3
  remains open for FSM refinement and its obligation catalog.

- **2026-07-21 — ADR-0319 accepts exact compiler lexical-scope metadata.**
  Bare decimal nested `scope N {}` blocks now flatten only admitted `let`
  declarations into the existing ordered local inventory; debug names and
  scope IDs have no checked semantics. Four focused tests cover semantic
  identity, the 64/65 depth boundary, malformed/executable content, preserved
  duplicate/type classes, and 1,000 deterministic structured-noise cases. The
  exact owning-Cargo selection of `walk_permissions` now reaches the existing
  checked-memory profile from an 8,218-byte live capture containing
  `scope 1 {`. No executable semantic variant, committed raw walk artifact, or
  page-table result is admitted; a retry requires a fresh preregistered ADR.

- **2026-07-21 — ADR-0318 rejects the first P5.3 page-table cell before
  capture.** The operation/block probe fit the accepted checked-MIR fragment,
  but the real owning-Cargo selection failed strictly at compiler-emitted
  nested `scope` metadata for the named locals (`mir_syntax`,
  `UnsupportedStatement`, `scope 1 {` at 118:5). The command retained no raw
  output, its partial target was removed, and fixture source was restored
  byte-for-byte; no production/parser/test/lockfile change survives. The
  frozen no-weakening rule forbids rewriting the source to hide the result or
  widening the parser under ADR-0318. A separately preregistered exact scope-
  metadata grammar is the only selected continuation before the bounded walk
  can be retried.

- **2026-07-21 — ADR-0317 accepts the authenticated annotation-to-MIR seam.**
  The typed source bridge proves one total annotated `u8::wrapping_add`
  `ContractProgram`, emits the existing relational `ScalarCallContract`, and
  matches the frozen hand-built declaration exactly. Each declaration
  independently verifies against the same 10,124-byte compiler MIR body from
  the fixture's owning Cargo build before body discard. Two fresh pinned-nightly
  captures and the committed third copy are byte-identical; the distinct scalar
  summary replaces all machine-local roots with typed placeholders while
  preserving complete Cargo/rustc identities and ordered arguments. The exact
  compiler spelling `core::num::<impl u8>::wrapping_add` lowers only at its
  two-`u8`/`u8` boundary and remains outside relational-call inventory. Both
  resolvers match the separately reflected inlined control over all 256 inputs
  at 256 normal/zero panic with zero evaluation error/drop; removing the
  relation is disproved, and source/body/intrinsic/resource mutations fail
  closed. The complete package/doctests, strict Clippy, pinned capture replay,
  and expanded 81-variant / 17-group / eleven-binary / 123-test semantics gate
  pass under the one-job 4 GiB policy. This closes the bounded P5.2 v1 phase
  exit criteria alongside the already accepted dual-IR checksum and panic
  composition cells. Nontrivial `requires`, source panic
  summaries, broader syntax, effects, LLVM generation, performance, and the
  still-missing second machine remain out of scope.

- **2026-07-21 — ADR-0316 accepts the first source contract surface.** Outer
  `#[verify]` now consumes typed `#[requires(expr)]` and
  `#[ensures(|result| expr)]` markers for one straight-line scalar body. A
  separate `ContractProgram` preserves the source-compatible no-annotation
  path while retaining the typed result/pre/post terms. Panic states are
  precondition-guarded; postcondition failure is separately guarded by normal
  return and replays by calling the original function and evaluating its source
  closure, never by pretending it panicked. Postcondition-expression panics are
  separate totality obligations and a reachable one fails closed as an invalid
  contract. The safe increment verifies, the unguarded body keeps its `x = 255`
  overflow witness, the mutation returns
  normally and replays false, and a reachable division panic stays a panic.
  Lowered-term evaluation over all 256 `u8` rows yields exactly 255 admitted,
  zero safe violations, 255 mutated violations, zero evaluation errors, and no
  drops. Six source tests, three macro boundary tests, compiled documentation,
  the complete package/doctests, strict Clippy/rustdoc, and the unchanged
  81-variant / 17-group / ten-binary / 117-test reflection gate pass under the
  one-job 4 GiB cap. Direct `dmesg` is host-denied; the July 21 kernel journal
  has no new OOM kill. ADR-0317 now freezes the authenticated total-function
  continuation; it does not widen syntax or effects.

- **2026-07-21 — ADR-0315 accepts modular MIR panic propagation before
  annotations.** The remaining cross-machine evidence row still requires a
  genuinely different host, so independent local work advances P5.2's smallest
  missing runtime rule. Existing scalar contracts remain total by default; the
  opt-in `panic_when(args)` is separately verified against the checked
  MIR callee, joins the caller panic predicate, and guards the fresh-result
  relation by normal return. The frozen two-function gate requires exact
  modular/inlined panic equality and all 256 `u8` rows at exactly 255 normal and
  one panic. The witness and neighbors replay; body/predicate, old-total,
  sort/result, and zero-resource mutations fail closed. The 81-variant,
  17-group, ten-binary, 117-test semantics gate, complete package/doctests,
  strict Clippy, and strict rustdoc pass. No source annotations, unwind cleanup,
  memory/effects, loops, LLVM panic inference, or performance claim is admitted.
  ADR-0316 now closes the source-local annotation prerequisite. Its remaining
  continuation is authenticated annotation-to-summary composition, without
  widening call/effect semantics.

- **2026-07-21 — PLAN item 10's Axeyum artifact/code blocker is closed.** The
  closure audit confirms the minimal profile, semantic API facades, typed
  lowering configuration, direct-reconstruction/term-walker de-duplication,
  bounded rational CAD sharing, and measured module splits are complete.
  `reconstruct.rs` is 2,793 lines, `int_reconstruct.rs` is 3,489, and the
  documented all-feature root is 66 entries. ABV replay/repair remains in place
  because its ROW ownership and 16 test-private consumers make a move cosmetic
  or visibility-widening. A new ecosystem note positions the work against
  Veritas and Microsoft codename MDASH and separates six attacker-control
  predicates. This does not close publication generality, cross-machine
  reproducibility, broader recall, proof prevalence, or performance work.

- **2026-07-21 — I6 privately extracts Diophantine reconstruction and closes
  the integer structural lane.** The original ADR-0042 family now lives in the
  767-line `int_reconstruct/diophantine.rs` child with both public paths
  unchanged and eight family-specific context methods. The first compile
  gate exposed four sibling-consumed helpers omitted by the same-file census
  plus four transitive dependencies; all 17 shared context methods therefore
  stay parent-owned and private. `two_x_eq_one` remains exactly 868,243 Lean
  bytes at FNV-1a `d2f76675b12631ea`. The 5 reconstruction, 4 evidence, 19
  math-resource, 10 namespace, 895 library, strict Clippy, and both rustdoc
  gates pass. `int_reconstruct.rs` falls 4,246→3,489 lines / 141,804 bytes,
  60.7% below its original size. No generic large-file successor is admitted.

- **2026-07-21 — I5 privately extracts affine-growth reconstruction.** The
  seven-item ADR-0097/0105 family now lives in the 467-line
  `int_reconstruct/affine_growth.rs` child with explicit imports, unchanged
  outward paths, and one existing private parent helper. `repair-const-nterm`
  remains exactly 43,108 Lean bytes at FNV-1a `dd4d24cdf0168fb9`. All nine
  focused controls, including every 64-seed Z3 positive/near-miss row, all 895
  library tests, strict Clippy, and both rustdoc profiles pass.
  `int_reconstruct.rs` falls 4,701→4,246 lines, 52.2% below its original size.
  Next: remeasure; no further integer-family split is automatically admitted.

- **2026-07-21 — Post-I4 census authorizes only I5.** The independent affine-
  growth family is a contiguous 456-line ADR-0097/0105 seam with seven cohesive
  items, two outward paths, and nine focused controls including a 64-seed Z3
  positive/near-miss sweep. Capture `repair-const-nterm`’s Lean identity, then
  move it privately to `int_reconstruct/affine_growth.rs` with explicit imports
  and unchanged matching/order/caps/paths. It may reuse the existing private
  prefix helper but must remain separate from Euclidean residue and from the
  closed-universal/nested-XOR shared-helper region.

- **2026-07-21 — I4 privately extracts Euclidean-residue reconstruction.** The
  four-item ADR-0095/0104 family now lives in the 354-line
  `int_reconstruct/euclidean_residue.rs` child with explicit imports, unchanged
  outward paths, and one existing private parent helper. `clock-3` remains
  exactly 16,025 generated Lean bytes at FNV-1a `4e97fa307a29d1d0`. All six
  focused controls, all 895 library tests, strict Clippy, and both rustdoc
  profiles pass. `int_reconstruct.rs` falls 5,045→4,701 lines, 47.0% below its
  original size. Next: remeasure; affine growth is not automatically admitted.

- **2026-07-21 — Post-I3 census authorizes only I4.** The clean next seam is the
  344-line ADR-0095/0104 Euclidean-residue reconstruction family: four cohesive
  items, two outward paths, and six dedicated reconstruction/evidence controls.
  Capture the committed `clock-3` Lean identity, then move it privately to
  `int_reconstruct/euclidean_residue.rs` with explicit imports and unchanged
  paths/matching/order/caps. Affine growth remains separate. Closed-universal
  and nested-XOR code stays parent-owned because two distinct proof families
  share its large kernel-helper region; no combined cosmetic move is allowed.

- **2026-07-21 — I3 privately extracts equality-partition reconstruction.** The
  cohesive ADR-0101/0106 family now lives in the 1,200-line
  `int_reconstruct/equality_partition.rs` child with explicit imports and the
  same crate router/public reconstructor paths. The SDLX Lean output remains
  exactly 30,644 bytes at FNV-1a `84fe8e457b9b6b27`. All twelve focused tests,
  including the 64-seed Z3 differential sweep, all 895 library tests, strict
  Clippy, and both rustdoc profiles pass. `int_reconstruct.rs` falls
  6,233→5,045 lines, 43.2% below its original size. Next: remeasure reviewer
  navigation/dependency seams; do not infer another split from raw size.

- **2026-07-21 — Post-I2 remeasurement authorizes only I3.** The next clean
  reviewer-facing seam is the contiguous 1,188-line ADR-0101/0106 single-pivot
  equality-partition reconstruction family: 30 cohesive items, two outward
  paths, six reconstruction tests, and six evidence tests including a 64-seed
  Z3 differential sweep. Capture the SDLX generated Lean identity, then move the
  family privately to `int_reconstruct/equality_partition.rs` with explicit
  imports and unchanged paths/visibility/ordering/caps. The ABV replay wall,
  algebraic CAD, and raw-size-driven splits remain unauthorized. Today’s
  user-provided July 16 Glaurung feedback copy was also rechecked against the
  current reviewer checklist; no evidence-based disposition changed.

- **2026-07-20 — I2 privately extracts counterexample-cover reconstruction.**
  The cohesive ADR-0108 family now lives in the 1,465-line
  `int_reconstruct/counterexample_cover.rs` child with explicit imports and the
  same two outward paths. The pre-move 7,197-byte generated Lean module remains
  exact at FNV-1a `e592f1787653a4bf`. Seven ordinary focused controls, the
  explicitly run real-corpus reconstruction, all 895 library tests, strict
  Clippy, and both rustdoc profiles pass under the bounded cap.
  `int_reconstruct.rs` falls 7,683→6,233 lines, 29.8% below its original size.
  Next: remeasure reviewer navigation/dependency seams; completion does not
  authorize another raw-size-driven split.

- **2026-07-20 — Post-N1 residual ranking authorizes I2, not broader cleanup.**
  The next behavior-neutral reviewer cut is the contiguous 1,449-line ADR-0108
  quantified-counterexample-cover family: 28 cohesive items, only two outward
  seams, and a 247-line integration suite. Move it privately under
  `int_reconstruct/counterexample_cover.rs` while preserving paths, visibility,
  ordering, caps, verdicts, and generated Lean bytes. The 4,531-line ABV
  replay/repair block stays deferred because its ROW ownership and 16 private
  test imports make the seam wide; algebraic CAD stays separate. Raw size does
  not authorize work on other large files. Next: execute I2 as its own
  add/commit/push checkpoint.

- **2026-07-20 — N1c closes CAD parameterization at the rational policy
  boundary.** One `visit_rational_cells` recursion now takes explicit
  `OpenOnly` or `OpenAndRationalSections`; historical strict/non-strict wrappers
  remain, and algebraic traversal is untouched. Exact `(1,1,1)`, `(1,-1,-1)`,
  and zero-cell `(0,-1,-1)` controls plus drop/reorder mutations pin the policy.
  The 2,000-seed tally is exactly unchanged for a third run, all 86 focused NRA
  and 895 library tests pass, and strict lint/doc/OOM gates are green. Production
  falls 7,077→6,944 lines across N1; added controls make the whole file 7,503
  lines, still 41 below baseline. Next: re-rank remaining artifact residuals;
  do not genericize the algebraic value-domain traversal without new evidence.

- **2026-07-20 — N1b shares two-variable projection without sharing CAD
  policy.** `two_var_critical_roots` now owns only leading/discriminant/resultant
  projection, isolation, ordering/deduplication, and the cell cap. Strict keeps
  its entry poll; non-strict keeps its caller behavior; sampling and lifting
  remain separate. An exact `[0,1]` projection control and a poll-removal
  mutation pin the seam. The 2,000-seed tally is exactly unchanged from N1a,
  all 86 focused NRA and 893 library tests pass, and strict lint/doc/OOM gates
  are green. `nra_real_root.rs` is 7,485 lines, down 59 across N1a--N1b. Next:
  decide whether N1c's explicit rational cell-selection policy is genuinely
  easier to audit than the two remaining 90-line visitors; algebraic traversal
  remains separate.

- **2026-07-20 — N1a shares only the rational CAD cell mechanism.** One private
  `decide_rational_cell` now owns rational substitution, constant folding, and
  univariate decision behind the unchanged strict/non-strict wrappers. Exact
  deterministic models remain `(x=1,y=1)` and `(x=1,y=0)`. All 86 focused NRA
  tests, the fixed 2,000-seed Z3 sweep (1,807 joint decisions, 1,807 agreements,
  1,293 replayed SAT, zero disagreements), all 891 library tests, strict Clippy,
  both rustdoc profiles, links, and the OOM audit pass under the bounded cap.
  `nra_real_root.rs` is 7,521 lines, down 23. Next: review N1b's projection-only
  seam and the strict-only entry deadline poll; do not combine it with sampling
  or algebraic traversal.

- **2026-07-20 — N1 freezes the semantic gate before CAD
  parameterization.** The 7,544-line `nra_real_root.rs` does contain duplicated
  rational cell and projection mechanics, but strict open-cell coverage,
  non-strict zero-cell coverage, and algebraic `Value`-domain lifting are not
  three instances of one algorithm. The accepted census authorizes only N1a:
  share rational substitution/univariate cell decision behind the existing
  strict and non-strict wrappers. The 2,000-seed Z3 differential/replay gate,
  exact-model fixtures, mutation controls, full solver suite, and bounded OOM
  audit are preregistered. Next: implement and push N1a without touching
  projection, sampling, budgets, deadlines, algebraic fallback, or public APIs.

- **2026-07-20 — I1 gives integer-inequality reconstruction a private semantic
  module with byte-stable Lean output.** The 1,196-line body now lives in the
  1,201-line `int_reconstruct/inequality.rs` child. Its three public entry
  points retain exact paths; only `lt_lit_lit` is `pub(super)` for six earlier
  proof sites, with 15 explicit private parent imports. The representative
  `3*x` interval module keeps SHA-256 `27edf9b0...205de` before/after. All 14
  focused interval tests (including three real-Lean checks), 12 UFLIA
  interpolant tests, 10 namespace controls, and all 891 library tests pass;
  strict Clippy and both rustdoc profiles are green. `int_reconstruct.rs` is
  7,683 lines, down 13.4%. Next: census N1's CAD duplication and freeze a
  semantic differential gate before any behavior-bearing parameterization.

- **2026-07-20 — ABV A3 extracts the actual lazy-ext orchestration seam and
  rejects a cosmetic whole-lane move.** The census found 13 historical-lane
  items used by earlier ROW/projection code and 16 residual private items
  reached directly by `abv::tests`. The clean 434-line CEGAR/refinement body is
  now a 446-line private `abv/lazy_ext.rs` child with ten items and exactly one
  `pub(super)` dispatcher entry. Shared replay/index helpers, test imports, and
  every public path remain parent-owned and unchanged. The 42 focused private
  tests, 10 extensionality integrations, five lazy-ROW controls, differential
  fuzz, and all 891 library tests pass under the bounded cap. `abv.rs` is now
  10,675 lines, down 28.6% across A1--A3. Next: I1's exact 1,196-line
  integer-inequality reconstruction seam; do not force the remaining 4,531 ABV
  replay/repair lines across an artificial visibility boundary.

- **2026-07-20 — the July 16 Glaurung feedback is reconciled against the later
  evidence rather than copied forward as ten timeless claims.** The new durable
  reconciliation preserves strict sorts/errors, structural `Unknown`, lean
  model lift, bounded shared replay, self-rechecked DRAT, and fail-closed
  measurement. It explicitly retires the old 2.8--4x warm headline under
  ADR-0272's fair six-cell Bitwuzla/Z3 result, bounds robustness to named
  populations, and separates demonstrated proof attachment from still-open
  prevalence/nontriviality. `assert_configured_batch` now carries the same
  warm-only warning as the scalar configured entry point. Next remains A3's
  exact lazy-ext dependency/seam census; no solver behavior changed here.

- **2026-07-20 — ABV A2 gives eager array-elimination evidence its own private
  trust-boundary module.** The 333-line certificate/rechecker body plus a
  seven-line prelude now live in `abv/array_elim_certificate.rs`.
  `ArrayElimUnsatCertificate` and `certify_array_elim_unsat` retain their exact
  `abv` and crate-root paths; the child uses only two existing private parent
  helpers. All seven certificate mutation/recheck tests, seven Ackermann
  controls, end-to-end Lean reconstruction, namespace compatibility, all 891
  library tests, strict Clippy, and both strict rustdoc profiles pass under the
  bounded cap. `abv.rs` is 11,112 lines, down 25.7% across A1--A2. Next: census
  the exact 4,968-line lazy-ext lane dependencies before selecting its module
  seam; do not broaden visibility for a cosmetic split.

- **2026-07-20 — ABV A1 removes the inline test wall without touching
  production code.** The unchanged test bodies now live in the 3,510-line
  `abv/tests.rs` child; the parent keeps a four-line private test-module seam and
  falls 14,953→11,443 lines (23.5%). Six compile-time corpus paths gained one
  relative parent component after the move. All 891 solver-library tests retain
  their `abv::tests::*` identities, and strict all-target Clippy plus both strict
  rustdoc profiles pass under the bounded 4 GiB profile. Next: A2, extract the
  334-line eager array-elimination certificate/rechecker as a named
  trust-boundary module while preserving its two public paths and only two
  measured parent helpers.

- **2026-07-20 — ADR-0314 makes the only censused invalid `SolverConfig` state
  unrepresentable.** `BitLoweringMode` now selects eager, dense-demand, or
  admission-controlled range-demand cold lowering; the old fluent selectors
  remain and replace one another with last-call-wins semantics. The backend no
  longer needs a runtime conflicting-mode error. Benchmark flags, JSON keys,
  policy payload, and configuration-hash bytes remain unchanged, and the exact
  Glaurung minimal-`qfbv` consumer compiles without source changes. All 891
  solver library tests, 34 SAT/BV integration tests, 62 benchmark tests across
  its binaries/integrations, strict Clippy, and both strict rustdoc profiles
  pass under the 4 GiB one-job cap. The census does not justify grouping the
  remaining independent options or harmless no-ops. Next: re-rank the remaining
  item-10 module/duplication work from measured reviewer cost; do not reopen R4
  or infer a broader config project.

- **2026-07-20 — R4i gives constraint builders one final bounded namespace and
  closes R4.** The full-only `constraints` facade groups 12 existing `distinct`,
  cardinality, and pseudo-Boolean term constructors under a 14-entry subtree.
  Abduction, model-based projection, model replay, backends, incremental state,
  strategies, and solver front doors remain at the root. The all-feature
  documented root falls 77→66 items, while minimal `qfbv` stays at 26 with no
  constraints module. Historical aliases remain callable and type-identical.
  Dedicated compatibility gates, all 891 solver-library tests, strict
  all-target clippy, and both warning-denied rustdoc profiles pass inside the
  one-job 4 GiB profile. Further namespace work now requires new consumer
  evidence. Next: continue artifact-readiness item 10 with a separate
  typed-configuration/illegal-state census, without mixing behavioral policy
  changes into R4's documentation-only commits.

- **2026-07-20 — R4h completes the checked-refutation certificate catalog.**
  Four new full-only `certificates` submodules organize 51 existing arithmetic,
  finite-domain, structural, and UF refutation contracts. General decision
  procedures, `check_model`, SAT backends, and solver front doors remain outside
  the catalogs. The missed QF_UF Alethe emitter now has its canonical
  `proofs::alethe` path. The all-feature documented root falls 128→77 items;
  the certificate subtree grows 105→160 and the proof subtree 115→116, while
  minimal `qfbv` stays at 26 with no certificate module. Historical aliases
  remain callable and type-identical. Dedicated compatibility gates, all 891
  solver-library tests, strict all-target clippy, and both warning-denied
  rustdoc profiles pass inside the one-job 4 GiB profile. Next: one final
  residual query-construction/core-helper census, then stop R4 unless a distinct
  non-catch-all ownership boundary is measured.

- **2026-07-20 — R4g gives interpolation a bounded canonical surface.** The
  full-only `interpolation` facade groups 21 existing common, QF_BV, QF_UF,
  LIA, LRA, UFLIA, and UFLRA contracts under six logic-specific submodules.
  Model-based projection remains outside the boundary, and two verifier
  functions that were never part of the public crate surface remain private.
  The all-feature documented root falls 148→128 items; the interpolation
  subtree contains 27 entries including its six grouping modules, while minimal
  `qfbv` remains 26 with no interpolation module. Historical aliases remain
  callable and type-identical. Dedicated compatibility gates, all 891
  solver-library tests, strict all-target clippy, and both warning-denied
  rustdoc profiles pass inside the one-job 4 GiB profile. Next: census the
  remaining general refutation/certificate utilities and core solver helpers
  independently, without creating a miscellaneous namespace.

- **2026-07-20 — R4f exposes the exact SMT-LIB text-front-door module.** The
  existing full-only `smtlib.rs` has exactly the same 25 public contracts as the
  historical root export, with no public helper or internal state outside that
  set. It is now the canonical `axeyum_solver::smtlib` namespace; duplicate root
  aliases remain callable and type-identical but are hidden from rustdoc. The
  all-feature documented root falls 172→148 items, while minimal `qfbv` stays at
  26 with no SMT-LIB module. Dedicated compatibility gates, all 891
  solver-library tests, strict all-target clippy, and both warning-denied
  rustdoc profiles pass inside the one-job 4 GiB profile. Next: census
  interpolation independently, followed by the remaining general refutation
  utilities; do not fold either into the text namespace.

- **2026-07-20 — R4e gives objective optimization a bounded canonical surface.**
  The full-only `optimization::{models,maxsat,objectives}` facade groups 40
  existing replay-checked model-minimization, MaxSAT, and scalar/multi-objective
  contracts. Pbls remains a SAT decision backend, SMT-LIB optimization commands
  stay with the textual front door, and `Solver` remains a compact consumer
  facade. The all-feature documented root falls 211→172 items; the optimization
  subtree contains 43 entries including its three grouping modules, while
  minimal `qfbv` remains 26 with no optimization module. Historical aliases
  remain callable and type-identical. Dedicated compatibility gates, all 891
  solver-library tests, strict all-target clippy, and both warning-denied
  rustdoc profiles pass inside the one-job 4 GiB profile. Next: census the
  SMT-LIB textual front door independently, followed by interpolation and
  general refutation utilities.

- **2026-07-20 — R4d separates verification/application APIs from the solver
  root.** The full-only `verification` facade groups 66 existing BMC/
  k-induction, Horn, IMC, PDR, symbolic-execution, and tiny-BV reference-VM
  contracts under six semantic submodules. These APIs consume theories and
  proof artifacts but are neither theories nor proof formats. The all-feature
  documented root falls 276→211 items; the subtree contains 72 entries including
  its grouping modules, while minimal `qfbv` stays at 26 with no verification
  module. Historical aliases remain callable and type-identical. Dedicated
  compatibility gates, all 891 solver-library tests, strict all-target clippy,
  and both warning-denied rustdoc profiles pass inside the one-job 4 GiB
  profile. Next: census optimization, SMT-LIB, interpolation, and general
  refutation utilities independently; do not create a miscellaneous facade or
  mix API organization with solver behavior.

- **2026-07-20 — R4c gives direct theory APIs semantic homes without absorbing
  cross-cutting front doors.** The full-only `theories` facade groups 63 direct
  contracts/procedures under arrays, arithmetic, datatypes, quantifiers,
  strings, uninterpreted functions, and combination. General model replay,
  auto-dispatch, SMT-LIB, optimization, interpolation, symbolic execution,
  verification, proofs, and certificates remain outside it. The all-feature
  documented root falls 338→276 items; the theory subtree contains 70 entries
  including its seven grouping modules, and minimal `qfbv` remains 26 with no
  theory facade. Historical aliases remain callable and type-identical.
  Dedicated compatibility gates, all 891 solver-library tests, strict
  all-target clippy, and both warning-denied rustdoc profiles pass inside the
  one-job 4 GiB profile. Next: measure the remaining cross-cutting root domains
  independently before deciding whether R4 needs another facade; do not stretch
  `theories` or mix this artifact-readiness pass with solver behavior.

- **2026-07-20 — R4b removes the specialized certificate catalogs from the
  documented solver root without hiding core APIs.** The full-only
  `certificates::{arrays, quantifiers}` facade owns 31 array and 72 quantified
  entries; two finite-quantifier Alethe emitters now live canonically under
  `proofs::alethe`. General `check_model` replay and array decision procedures
  remain root-visible for the separate theory census. The all-feature root
  falls 442→338 items, the certificate subtree contains 105 entries, the proof
  subtree grows 113→115, and minimal `qfbv` stays at 26. Historical aliases are
  callable and type-identical. Dedicated full/minimal compatibility gates, all
  891 solver-library tests, strict all-target clippy, and warning-denied
  rustdoc pass inside the one-job 4 GiB profile. Next: R4c measures theory
  contracts and decision procedures independently; do not group by source-file
  accident or change solver behavior.

- **2026-07-20 — R4a gives proof APIs a canonical namespace without breaking
  downstream paths.** `axeyum_solver::proofs` now groups the minimal proof
  exports and the full-profile Alethe, end-to-end, evidence, faithfulness, and
  Lean surfaces. Every historical root export remains callable and
  type-identical but is hidden from root rustdoc. The measured documented root
  falls 549→442 items under all features and 36→26 under minimal `qfbv`; the
  facade owns 113 organized proof-facing entries. Dedicated compatibility tests
  cover both profiles, all 891 solver-library tests pass, and strict clippy plus
  warning-denied rustdoc are clean under the bounded one-job profile. Next:
  continue R4 with independent `theories` and `certificates` censuses, retaining
  the same source-compatibility gate and keeping behavior out of the refactor.

- **2026-07-20 — Reconstruction cleanup R2 establishes a real direct-lane
  module boundary.** All 34 direct structural adapters, their five constructive
  encodings, the shared checked wrapper, and their explicit dispatcher now live
  in `reconstruct/direct.rs`. The parent retains one dispatch call and one
  narrow boolean certification seam required by fragment scanning; no private
  certificate type or broad visibility leaked across the boundary. The main
  file falls from 18,387 to 16,999 lines. The 29-role byte-equivalence test, all
  884 full-profile library tests, and clippy `-D warnings` pass under the 4 GiB
  one-job discipline. Next: census the equality core before the first R3 family
  extraction; do not mix that move with proof behavior or public API changes.

- **2026-07-20 — Reconstruction cleanup R1 parameterizes only the shared
  checked wrapper.** The new inventory measures the 18,517-line monolith and
  classifies its 34 direct structural variants into five custom constructive
  encodings and 29 validators sharing one deterministic opaque-proposition
  wrapper. A characterization test proves the helper byte-identical to the
  pre-refactor algorithm over all 29 registered stem/role pairs. All 26 inline
  emission tails now call it; each validator, recheck, error string, dispatcher
  arm, and kernel `False` gate stays explicit. `reconstruct.rs` falls by 130
  lines / 8,924 bytes. All 884 full-profile solver tests and clippy pass under
  the bounded one-job discipline. Next: R2 moves this direct lane, one ownership
  boundary only, into `reconstruct/direct.rs` with the same byte-stability gate.

- **2026-07-20 — Artifact cleanup starts with one semantics-preserving internal
  walker consolidation.** Fifteen byte-equivalent binary top-level conjunction
  walkers now use one tested crate-private helper, removing 102 net source
  lines without changing public API or evidence behavior. The two non-equivalent
  implementations remain explicit: `auto` accepts arbitrary arity, while
  `array_axiom` additionally flattens asserted BV1 conjunctions. Two focused
  order/duplicate/leaf tests, all 883 full-profile solver library tests, and
  full-profile clippy `-D warnings` pass under the one-job 4 GiB discipline.
  Next: inventory the reconstruction twins and define their shared contract
  before any file split; generated Lean text and checker selection must remain
  byte-for-byte stable.

- **2026-07-20 — ADR-0304 closes the engine-cache factorial with a bounded
  mixed result.** The fresh successor completed 120/120 processes and 387,060
  checks; every producer and frozen-analyzer correctness, classification,
  telemetry, terminal-state, and resource gate passes with zero replay failure,
  eviction, bypass, or owner leak. Warm state remains additive under exact
  caching on vwififlt and SurfacePen, and under structural caching on vwififlt,
  IntcSST, and SurfacePen; DptfDevGen and the IntcSST exact cell exceed the 3%
  variance limit. The other interaction is negative for cache promotion:
  cache-on slows every already-warm path with a conclusive contrast, while mean
  maximum RSS rises 7.6%--67.3%. Canonical exact covers 8,001/12,902 checks and
  implication adds only 562. Keep warm solver reuse as the product mechanism;
  leave the Glaurung cache experimental and cold-policy-specific. The committed
  analysis reports per-driver intervals only. ADR-0303 remains rejected and
  contributes no timing claim. Next: resume the ranked backlog at item 10 while
  ADR-0302 awaits a genuinely different second machine.

- **2026-07-20 — The first ADR-0302 machine closes run stability and backend
  finding parity, while cross-machine evidence remains open.** A clean detached
  `fd0cab4a` run completed the frozen 32-cell matrix under the 4 GiB cgroup.
  Axeyum is exact across its two repetitions, Z3 is exact across its two
  repetitions, and all four runs share one finding/work digest with 2/2 pairs,
  clean fixed sides, replay-valid witnesses, and no non-return stop counts.
  The two authorities intentionally retain distinct model digests. The
  analyzer returns `accepted=false` with the sole reason
  `cross_machine_population_missing`; `server0` is one real machine, not the
  required two. Raw observation, analysis, hashes, and the 2.082 GiB aggregate
  peak are retained in the dated benchmark directory. A deterministic 3.0 MiB
  transfer bundle now carries exactly the eight registered objects; six focused
  tests reject manifest, payload, registration, and object-set drift before
  extracting to an absent second-machine root.

- **2026-07-20 — ADR-0302 preregisters the missing run/machine/backend
  reproducibility gate without erasing model diversity.** The accepted v3
  recall result is same-host and Axeyum-only, embeds an absolute object path,
  and builds against a machine-local Axeyum checkout; it cannot support the
  broader PLAN item 7 claim. Isolated Glaurung branch
  `codex/adr0302-reproducible-recall` at `31f7ebe` now pins pushed Axeyum
  `c38a9515`, emits a normalized object ID plus full hash, and labels the
  compile-time authority exactly. Both authority configurations and a real
  vulnerable cell pass under the 4 GiB cgroup. The disclosed cell finds the
  same constrained `OutOfBoundsIndex` under both authorities but returns two
  valid witnesses (`0x80010000` Axeyum, `0x80000000` Z3), so ADR-0302 freezes
  three projections: exact within-authority output; backend-invariant finding,
  work, and stop identity; and separately retained/replay-validated model
  choices. The versioned runner and six focused tests pass; zero full matrix
  rows exist at preregistration. Two real machines remain mandatory before a
  cross-machine claim.

- **2026-07-20 — The Glaurung correctness-oracle result is consolidated and
  its exact diagnostics are standing contracts.** The reviewer-facing methods
  note separates three consumer defects by mechanism: strict width/sort
  checking exposed the declared extension and concat bugs; fail-closed result
  typing plus ordered model-read replay exposed empty-model steering. It also
  separates Glaurung's linked-Z3 W128 truncation from the Z3 solver core. The
  existing named fuzz controls now assert both typed `IrError` variants and the
  exact actionable messages (`width 57`, `(_ BitVec 96) vs (_ BitVec 64)`, and
  the over-wide constant), while normalized positives, model-less UNSAT versus
  legitimate empty SAT, and the W128 high bit remain distinct controls. This
  consolidates ADR-0224/0237's 4,000-row three-way and 12,000-row four-way
  evidence without inflating invalid consumer states into valid-formula fuzz
  coverage or reviving the retired speed headline.

- **2026-07-20 — ADR-0300 rejects dense memo indexing at the frozen variance
  gate; production returns to BTree.**
  The audited mechanism is exact lookup on dense insertion-order `TermId`s:
  production currently uses `BTreeMap<TermId, Vec<AigLit>>` without semantic
  iteration. The reported 3.89x dense-plus-`Rc` scratch result is explicitly
  non-evidence because its named reproduction is absent and it conflates two
  changes. The frozen candidate is only `Vec<Option<Vec<AigLit>>>`; clones,
  lift maps, AIG/CNF construction, strict IR errors, solver policy, and proofs
  remain unchanged. Representation-neutral artifact-v39 telemetry now exposes
  the BTree representation, exact lookup/hit/write and payload/logical-storage
  accounting, actual/expected root bits, and deterministic ordered lowering and
  CNF digests. The independent analyzer fails closed on schema/config/population,
  manifest/Z3/replay, every invariant and aggregate sum, and any unregistered
  per-query structure delta. Focused BV/solver/bench tests, strict Clippy,
  warning-denied rustdoc, QF_BV-only, scalar-WASM, `+simd128` WASM, analyzer,
  formatting, and link gates pass inside the serialized 4 GiB envelope (the
  full-workspace run peaked at 3.4 GiB with 134.8 MiB swap). The clean detached
  profile from `d13d1f92` now decides 162/162 (88 SAT, 74 UNSAT), agrees with
  both the exact manifest and
  in-process Z3 on 162/162, replays every SAT model, and passes all 162 memo and
  structure-digest rows. The accepted BTree totals are 24,470 source/occupied
  terms, 656,638 payload literals, and 5,938,264 conservative logical bytes;
  artifact and analysis hashes are `d8258399...b39f5` and
  `205bdfcf...4f25`. The baseline run peaked at 1.3 GiB with zero swap inside
  the serialized cgroup. The isolated dense candidate is committed at
  `2c9209fe`; its clean detached v39 profile decides and agrees 162/162, replays
  88/88 SAT models, preserves every neutral per-query counter plus both ordered
  structure digests, and passes every memo invariant. Conservative logical
  bytes fall 5,938,264 -> 5,840,384 (-1.65%), and the fail-closed comparison
  sets `timing_authorized=true`. Candidate artifact and analysis hashes are
  `e4db458f...f0eac` and `dbb2d65c...56256`; its capped process peaked at
  1.2 GiB with zero swap. Full all-feature workspace tests and doctests,
  warning-denied workspace rustdoc, strict focused Clippy, QF_BV-only, scalar
  WASM, `+simd128` WASM, analyzer, formatting, and link gates pass. Exact
  structural/storage identity permitted six order-balanced pairs. The frozen
  timing runner/analyzer pinned source revisions, prebuilt binary hashes
  (`65d81952...5c515` BTree, `06d417ef...93377` dense), the exact schedule,
  correctness/structure, exhaustive paired bootstrap, family/CV/cold-total
  bounds, and every paired RSS ratio. All 12 runs preserve 162/162 decisions,
  manifest/Z3 agreement, 88/88 SAT replays, and exact AIG/CNF structure. The
  dense point estimates pass: bit-blast geometric mean 0.9222 with exhaustive
  bootstrap upper 0.9774, cold-total geometric mean 0.9927 with upper 1.0183,
  qualifying family tails <=1.02, and maximum paired RSS 1.0052. The fixed
  variance gate rejects the candidate: baseline bit-blast CV is 3.0023% and
  candidate CV is 6.8664%, both above 3%. No post-observation rerun is allowed.
  The exact timing artifact and failed verdict are retained, the BTree memo is
  restored, and this mechanism is closed. Return to the reviewer-aligned
  correctness/deployability/reproducibility queue; do not infer another cold
  layout candidate from this sample or turn its favorable point estimate into
  a speed claim.

- **2026-07-20 — ADR-0299 accepts checked MIR relational calls.** The located,
  typed scalar MIR path now admits exactly one opt-in direct checksum call after
  independently verifying the shared relation against the checked MIR callee
  and proving its panic predicate false. Resolver construction discards the
  body; caller reflection retains only a distinct internal result and separate
  assumption. MIR/LLVM modular and inlined results agree, weak contracts replay
  real havoc countermodels, and each IR classifies 100,000 valid plus 100,000
  deliberately invalid result choices with no dropped rows. Strict type,
  signedness, syntax, unwind, body/relation mutation, namespace, and explicit
  `Unknown` boundaries fail closed. The standing gate is 81 variants / 17
  groups / ten binaries / 114 tests; complete all-feature package tests and
  doctests pass at 1.8 GiB peak with zero swap inside the 4 GiB cap. General
  panic contracts, annotations, loop/memory/effectful calls, unwind paths, and
  performance claims remain outside the accepted slice.

- **2026-07-20 — ADR-0298 accepts relational scalar call results.** The
  checksum-module rule gives each opt-in
  straight-line call a fresh internal result and exposes its verified
  `ensures` relation separately from LLVM value definedness. The accepted gate
  verifies `sum16`, discards its body, re-proves modular `cksum_pair` against
  inlined MIR/LLVM, classifies 100,000 valid and 100,000 deliberately invalid
  havoc choices with no dropped work, and replays a weak-contract
  countermodel proving no hidden exact substitution. Strict `Result`/equality/
  `ite` sorts, namespace isolation, mutations, and explicit `Unknown` fail
  closed. The standing gate passes 76 variants / 16 groups / ten binaries / 108
  tests at 2.7 GiB; full package/doctests pass with test debug metadata disabled
  at 2.5 GiB. A parallel full-package run OOMed at the cap and a serialized
  full-debug retry was stopped there; neither is counted as evidence. ADR-0299
  now preregisters the separately body- and panic-checked MIR counterpart, not
  annotations, loop havoc, effects, or a performance claim.

- **2026-07-20 — ADR-0297 accepts explicit scalar call-requirement
  obligations.** A verified nontrivial `requires` constrains the transition only
  after `prefix && args_defined && !requires` is independently exposed in
  `TransitionSystem::bad`. The prefix contains only earlier checked operations
  and selected edges, so untaken natural-loop calls do not fail and later UB
  cannot erase an already reached violation. Both exact PAC callers retain
  source-attributed depth-1 `leaf(1)` witnesses and replay at defined `n=2`.
  Independent formulas plus 100,000 rows split 33,334 valid / 33,334 defined
  violation / 33,332 source undefined, with 16,666 omission controls, zero
  disagreement, and zero dropped work. Focused 17/17, standing nine-binary/98,
  and complete all-feature package/doctest gates pass under memory caps. Next:
  preregister relational scalar result/havoc on the checksum module before
  annotation syntax, MIR calls, or external effects.

- **2026-07-20 — ADR-0296 accepts verified scalar contract composition.**
  `ScalarCallContract` states the exact `leaf` requirement, value, poison, and
  immediate-definedness semantics as bounded typed data. Its resolver verifies
  the body once, then discards it; `compute` and `main` retain only the checked
  summary. Normalized modular/inlined formulas match, 100,000 tuples have zero
  disagreements, bounded/unbounded verdicts agree, and every contract/body
  mutation is refuted. Strict sort/signature/missing/duplicate/`Unknown` errors
  fail closed. A general nonlinear equivalence attempt was rejected after a
  disclosed 67.4 GiB anonymous-RSS OOM; the accepted small structural checker
  plus bounded fallback completes the suite at 61.3 MiB without rebuild.
  ADR-0297 has since added the explicit call-site obligation route required
  before nontrivial requirements. Relational result havoc and annotations
  remain separate work.

- **2026-07-20 — ADR-0295 accepts the executable direct-call baseline.**
  The three ADR-0294 call declines are not one sound mechanism: both PAC loops
  call the same internal straight-line scalar `leaf`, while external `puts`
  precedes a `hello.c` body that still needs pointer memory, `strlen`, global
  state, and variadic calls. `DirectCallResolver` therefore accepts only an
  explicitly supplied exact scalar, straight-line, memory/call-free callee body;
  the opt-in loop API admits both PAC callers while the default API still
  rejects ordinary calls and `puts` gets no effect-erasing model. Exact
  compiler/source/module/function identity reproduces live against Glaurung.
  Automatic value+definedness and transition formulas equal an independent
  specification; 100,000 tuples have zero disagreements; eager callee UB versus
  lazy unobserved poison, source replay, canonical syntax, and the complete
  negative boundary pass. At ADR-0295 acceptance the standing gate owned 63
  variants in 15 groups and nine binaries / 88 tests; ADR-0296 expands it to
  94 tests. This is the accepted inlined T5.2.4
  baseline, not modular contracts, cross-source evidence, or a revised census.
  ADR-0296 supplies the exact `leaf` contract comparison, ADR-0297 supplies its
  explicit precondition-obligation gate, and ADR-0298 supplies the separate
  straight-line relational result channel. Do not broaden loop call syntax;
  MIR-side modular composition is the next P5.2 boundary.

- **2026-07-20 — ADR-0294 accepts the corrected reproducible semantic census;
  no capability is selected.** A private classifier
  reuses the exact non-panicking function parser, typed scalar CFG, and checked
  self/single-latch reflector. It tries all non-Boolean PHIs only to remove
  property-name bias, then retains the stable error kind and located diagnostic.
  The producer revalidates ADR-0293, recompiles all 12 sources to exact LLVM
  hashes/diagnostics, uses pinned `llvm-extract`, and forbids dropped rows.
  Exact offline Cargo/rustc and both accepted fixtures pass; deliberate parser
  and memory declines remain precise. The complete Verify suite/doctests,
  all-target strict Clippy, warning-denied rustdoc, formatting, and links pass.
  The first artifact was rejected because `llvm-extract` embeds the temporary
  input path in ModuleID; it and the failure report remain retained. After the
  pushed ModuleID-agnostic/source-qualified correction, a fresh result creates
  then reproduces exactly: 0 accepted / 12 typed-CFG
  `unsupported_instruction` declines across all 12 functions/four loop-bearing
  sources. The frozen bucket selects a T5.1.2 audit lane only. Diagnostics split
  into seven one-source wide-memory rows, three cross-source call rows, one
  `alloca`, and one non-scalar result. Next: preregister broader cross-source
  semantic demand or an executable call boundary; no syntax-only shim or
  capability claim follows from this result.

- **2026-07-20 — ADR-0293 accepts the reproducible Glaurung LLVM loop-shape
  census and selects no implementation.** Both formal runs retain identical
  bytes: 12 loops in 12 functions, with 11 ADR-0291 self-loop structural rows,
  one early-exit `mathlib_is_prime` row, and zero rows in every other profile.
  The only rejected profile occurs in one function and one source, failing both
  frozen diversity thresholds. The earlier pilot remains disclosed and does
  not count again. A committed validator recomputes source/tool/manifest
  identity and every count with precise fail-closed errors. Structural shape is
  not semantic eligibility. Next: preregister semantic acceptance/rejection
  measurement over real loops or independently broaden the source population;
  do not implement early exits from this singleton.

- **2026-07-20 — ADR-0292 accepts the checked single-latch LLVM natural-loop
  bridge.** `reflect_single_latch_loop_checked` preserves the exact ADR-0291
  self-loop formulas and adds deterministic `%6 -> %15` / `%6 -> %11 -> %15`
  relations for the registered clang-21 `capdiv` fixture. Selected-edge
  polarity, simultaneous latch PHIs, path-local immediate UB, poison only when
  observed, defined back-edges/branch control, and immutable parameters remain
  explicit. Even `d=0` skips division; odd `d=0` is forbidden, and a deliberately
  eager global guard is refuted. Automatic formulas match an independent spec;
  50,000 recurrence tuples have `DISAGREE = 0`; k-induction proves `acc <= 100`;
  BMC rejects `acc > 100` through depth 8; abstract step-2 reachability is
  source-replayed by `capdiv(2, 1) == 1`. Exact shape/resource/type/dependency
  negatives pass. The standing 62-variant gate is unchanged in ownership and
  grows to eight binaries / 81 tests. Full verify tests/doctests, workspace
  Clippy, rustdoc, exact MIR replay, fixture hash/assembly, formatting, and links
  pass. Next: measure real rejected loop shapes before preregistering the next
  LLVM fallback/profile; T5.1.4 remains WIP and LLIR stays deferred.

- **2026-07-20 — ADR-0291 accepts the first typed canonical LLVM loop bridge.**
  The exact compiler's implicit `%1` entry-PHI slot is recovered only under a
  unique shared structural substitution and retained through canonical
  render/reparse. `reflect::llvm::loops` detects one scalar self-loop and builds
  deterministic PHI-plus-immutable-parameter state with checked poison,
  immediate-UB, branch-definedness, and exit-over-approximation semantics. The
  exact `capsum8` fixture proves `acc <= 100` unbounded, rejects `acc > 100`
  through depth 8, and separately source-replays abstract `acc > 2` at step 3.
  Automatic formulas match an independent spec; 20,000 recurrence tuples have
  `DISAGREE = 0`; negative shape/error tests pass. At this checkpoint the
  standing gate remained 62/62 semantic variants and grew to eight binaries /
  70 tests; ADR-0292's current total is recorded above. Complete
  verify tests/doctests, strict workspace Clippy, rustdoc, exact MIR replay,
  formatting, and links pass. Next: audit and preregister the bounded-unroll
  fallback versus the first multi-block/MIR loop continuation; T5.1.4 remains
  WIP and LLIR is still deferred.

- **2026-07-20 — ADR-0290 accepts the reflection semantics gate.** A versioned
  manifest now owns all 62 source-derived checked LLVM/MIR semantic variants
  exactly once across 14 evidence groups (15 proof, 13 fuzz/replay, five
  refutation tests). Six scalar-matrix tests prove 96 value/definedness goals
  and exhaust 11,248 bounded assignments without reading undefined LLVM values.
  All 11 ordinary cross-IR pairs agree on 110,000 deterministic tuples; `lut3`
  exhausts its three defined inputs; all five wrong transforms still replay.
  Ten checker mutations and the exact seven-binary/60-test runner pass under the
  same `just` and dedicated stable-CI command. The complete verify suite,
  workspace Clippy, rustdoc, exact MIR replay, formatting, and links pass. Next:
  preregister the smallest automatic reducible-loop bridge (T5.1.4) before
  wider places/memory or LLIR.

- **2026-07-20 — ADR-0289 accepts Cargo-owned MIR target selection.**
  `axeyum-mir-build` now binds canonical manifest/package/lib-or-bin/function,
  exact rustc, Cargo identity/arguments, 64-bit width, isolated target dir, and
  nonexisting output in one command. It checks strict named syntax and bounded
  semantics before atomic raw retention and emits deterministic typed/term
  JSON. Two target-package builds reproduce all 1,438 raw bytes and the summary;
  the exact panic/result/final-memory contract and source OOB witness replay
  pass.
  Stable selection/encoding/write failures leave no partial target or output.
  A real unsupported neighbor also exposed and fixed over-eager module scanning
  while preserving strict errors when that neighbor is selected. Exact nightly
  CI, five command units, three integration tests, the complete verify suite,
  strict Clippy/rustdoc, fixture replay, and links pass. This is one bounded
  profile, not general places or `stable_mir`. Next: preregister the small T5.1.6
  standing semantics/coverage gate before widening memory or touching LLIR.

- **2026-07-20 — ADR-0288 accepts checked MIR byte-memory CFG reflection.**
  The 3,262-byte authenticated module now includes a byte-identical replayed
  conditional write fixture and feeds a separate located, typed, non-panicking
  `Result` path. Every read/store derives its own bounds panic independent of
  compiler `assert`; bounded acyclic execution joins return, panic, and final
  memory. Exact straight-line and conditional panic/memory proofs pass, the
  embedded bounds strings are gone in favor of authenticated named functions,
  source OOB replay is retained, and MIR/LLVM separately prove the same
  four-byte roundtrip contract. Seven dedicated tests, three migrated bounds
  tests, exact fixture replay, the complete verify suite, and strict gates pass.
  This is bounded byte memory, not general MIR places or whole-crate extraction.
  Next: reassess the remaining T5.1.3/T5.1.5 prerequisite queue before admitting
  LLIR hardening or a same-object binary-vs-IR differential.

- **2026-07-20 — ADR-0287 accepts reproducible compiler-MIR capture before MIR
  writes.** One ordinary source is bound to raw 2,304-byte
  `rustc 1.97.0-nightly` stdout, exact compiler/LLVM identity and argv, and
  source/output/provenance SHA-256 values. The checker authenticates bytes
  before parsing, rejects duplicate keys/unsafe paths/argv, distinguishes
  stable-CI content validity from exact-toolchain replay, and preserves prior
  artifacts on compiler failure or nondeterminism. Eight adversarial tests,
  Cargo integration, two byte-identical regeneration captures, required replay,
  the complete verify suite, formatting, strict workspace Clippy/rustdoc, and
  links pass. The fixture contains a real checked store-then-load shape but
  capture makes no semantic or T5.1.3-completion claim. Next: preregister the
  smallest checked MIR syntax/memory slice; do not extend the panic-oriented
  line parser or infer write correctness from captured text alone.

- **2026-07-20 — ADR-0286 accepts checked bounded LLVM byte memory.** The first
  T5.1.5 memory slice now binds exactly one `ptr` parameter to 1--256 initialized
  non-aliasing bytes, types and canonically renders `inbounds` byte GEP plus
  `i8` load/store, and carries pointer poison, access UB, stored-byte
  definedness, and final-memory joins through checked acyclic paths. Three
  committed clang 21.1.8 fixtures, 11 dedicated tests, and 20 migrated LLVM
  reflection tests cover exact fixed/symbolic reads, replayed OOB witnesses,
  store/load and branch joins, optional `llvm-as`, rejection classes, and
  deterministic noise. The complete `axeyum-verify --all-features` suite, all
  ordinary workspace tests, formatting, strict workspace Clippy/rustdoc, and
  links pass; two EVM doctests that hit an environmental linker `SIGBUS` under
  `/tmp` pass unchanged with a workspace-backed `TMPDIR`. General provenance,
  wide accesses, MIR writes, LLIR hardening, and Glaurung lowering remain
  separate. Next: reassess the ranked Track 5 prerequisite queue against this
  accepted memory boundary before preregistering another semantic increment.

- **2026-07-20 — ADR-0285's flat CNF arena is rejected before timing and
  removed.** The one clean artifact-v38 process at `02e770c2` passes all
  162 decisions, 162 manifest/Z3 agreements, 88 SAT replays, exact legacy
  construction counts, and every offset/accounting invariant. Aggregate
  logical storage is favorable at 6,407,100 / 11,846,920 bytes (0.540824), but
  the frozen per-instance <=80% gate passes only 157/162. Five satisfiable
  singleton-clause formulas are payload-dominated: two 32-literal rows use
  260/280 bytes and three 64-literal rows use 516/536 bytes. The analyzer fails
  closed at the first row; no timing is authorized and the rule is not relaxed
  post-observation. The artifact/rejection summary are retained; validator
  `a57d5ace` is reverted at `56936920` and production arena `725858b1` at
  `f3456365`. Next: verify the restored representation, close this exact lane,
  then return to the ranked queue without deriving a replacement from the
  rejected rows.

- **2026-07-19 — ADR-0285 preregisters a flat CNF formula arena.** The latest
  PLAN evidence independently reopens GQ5 around retained memory layout, not the
  closed duplicate-clause population. The source audit finds 27 Rust files
  consume `CnfFormula::clauses()` and the Tseitin path still allocates a fresh
  canonicalization `Vec` per attempt, so the frozen slice includes a complete
  borrowed-clause API migration and one reusable encoder scratch. Reported
  scratch microbenchmarks are not accepted evidence because their named
  reproduction directories are absent. Production is selected only after exact
  formula/proof/verdict/replay identity, <=80% logical storage, full native/WASM
  gates, one fixed profiled structural run, and six clean paired runs showing a
  >=3% total-CNF improvement with bounded variance/RSS and no material-family
  regression. Next: commit this zero-row registration before red tests or any
  candidate corpus observation.

- **2026-07-19 — ADR-0284 accepts canonical scalar LLVM CFG rendering.**
  `render_scalar_cfg` now prints the validated typed graph deterministically;
  exact LLVM `\XX` byte decoding closes the prior identity-changing quoted-name
  defect with a stable located `MalformedIdentifierEscape`. Six renderer tests,
  all 16 canonical-gated cross-IR proofs, 21 existing LLVM syntax/typed tests,
  optional `llvm-as`, 1,024 structured-noise cases, and all frozen repository
  gates pass. The red gate also caught and corrected an initial PHI label-role
  writer error. Memory, loops, general calls, `freeze`/`undef`, module
  resolution, and Glaurung lowering remain outside the accepted slice. Next:
  retain the typed/canonical/definedness boundary and preregister the smallest
  remaining T5.1.2 semantic prerequisite rather than widening implicitly.

- **2026-07-19 — ADR-0283 accepts checked acyclic LLVM CFG execution.**
  The checked APIs now reuse ADR-0282's graph, enforce scalar return typing and
  function-wide SSA uniqueness, decline cycles and more than 4,096
  root-to-block executions, and join value+definedness only along selected
  branch, switch, and PHI edges. A reached `unreachable` is `defined=false`,
  never a dropped arm. Eleven focused tests plus all 16 cross-IR proofs pass;
  the proof migration makes definedness explicit and also caught/fixed negative
  LLVM integer normalization (`i32 -1`). The full crate suite and repository
  formatting/Clippy/rustdoc/link gates pass. Next: keep loops, memory, and
  Glaurung lowering deferred; preregister the next smallest T5.1.2 semantic
  prerequisite rather than widening the parser implicitly.

- **2026-07-19 — ADR-0282 accepts typed LLVM CFG syntax and validation.**
  `parse_scalar_cfg` now gives `phi`, `br`, `switch`, `ret`, and `unreachable`
  explicit span-carrying types; preserves true/false/default/case roles and
  terminator metadata; and validates terminator placement, every label, entry
  predecessor exclusion, normalized switch constants, and exact PHI
  predecessor sets. Unmodified clang/rustc division diamonds pass `llvm-as` and
  converge to one typed shape. Seven focused tests cover every control form,
  malformed graphs, exact multiline diagnostics, and 4,096 noise inputs; all
  existing cross-IR CFG fixtures validate before their legacy proofs. The full
  crate suite, workspace strict Clippy, and strict rustdoc pass. The wider
  workspace run now passes the stale `certificate_process_isolation` gate after
  updating its report-schema expectation from version 34 to the producer's
  current version 37; this was artifact-version drift, not a clause-count or
  solver change. Every ordinary workspace test then passed. The final EVM
  doctest link exhausted the shared `/tmp` tmpfs (LLVM `lld` surfaced a bus
  error and GNU `ld` reported `No space left on device`); the exact two doctests
  pass when `TMPDIR` is placed on the workspace disk. Next: preregister checked
  acyclic value+definedness execution. Cycles, memory, and Glaurung lowering
  remain deferred.

- **2026-07-19 — ADR-0281 accepts typed scalar LLVM instructions and checked
  definedness.** The T5.1.2 slice parses the existing QF_BV scalar op family into
  span-carrying enums, retains `nuw`/`nsw`/`exact`/`disjoint`/`nneg`, and exposes
  every SSA value with a Boolean LLVM-definedness term. Unmodified clang 21 and
  rustc 1.97 fixtures converge to the same typed shape; all admitted opcodes,
  predicates, casts, intrinsics, flags, malformed/unsupported cases, poison/UB
  witnesses, `i1` edge cases, and deterministic-noise paths are covered. The
  BE16 round-trip proof now proves definedness through the checked API. The full
  `axeyum-verify --all-features` suite and strict Clippy pass. Next: type the CFG
  boundary. Memory, `freeze`/`undef`, a shared crate, and the Glaurung lowerer
  remain outside this slice.

- **2026-07-19 — ADR-0280 accepts the first T5.1.2 structured LLVM parser
  slice.** `reflect::llvm::syntax::parse_function` now exposes owned
  function/parameter/block/instruction records, byte+line+column spans, quoted
  names, delimiter-aware parameters, and typed failures for malformed or
  ambiguous input. Only `param_decls` migrates through it; all existing
  reflection semantics and compatibility panics remain. The tests began red
  and cover compiler-shaped plus unlabeled functions, malformed spans,
  duplicate labels, multiple definitions, determinism, a body-call/header-
  confusion control, and 4,096 deterministic noise inputs. All five parser
  tests, the complete `axeyum-verify --all-features` suite, strict Clippy, and
  strict rustdoc pass.
  Next: preregister typed instruction syntax and checked-reflection migration;
  raw instruction lines remain intentionally unchanged in this slice.

- **2026-07-19 — ADR-0279 conditionally defers the general Glaurung LLVM
  importer and selects Axeyum P5.1/T5.1.2 as the reusable prerequisite.** The
  live-source audit confirms that `LlirFunction` and `Machine<D: Domain>` are a
  genuine reusable center, but current LLIR still infers temporary widths,
  encodes false edges as machine-address fallthrough, and mixes ABI/sink policy
  with physical register names. ADR-0268 had already measured the real kernel
  surface and selected the smaller AArch64 ELF route that delivered the
  accepted recall slice. Do not disturb that route or copy the current
  line-based Axeyum reflector. Build the structured, diagnostic `.ll` parser
  first; a Glaurung lowering waits for explicit LLIR and LLVM-semantics gates.
  The same audit corrects stale PLAN item 8: ADR-0227 already measured executable
  Node/Chromium WASM latency and bundle size.

- **2026-07-19 — ADR-0278 accepts one bounded downstream proof-carrying path
  verdict.** Isolated Glaurung `f01a057` now returns an owned
  `InfeasiblePathCertificate`, rebinds it to the exact `ExprPool` assertions,
  rejects a weakened satisfiable path, and keeps feasible/inconclusive/error
  outcomes non-infeasible. All 45 backend tests and two bundle tests pass.
  Pinned `drat-trim` accepts the fixed 32-variable/34-clause pair and rejects
  the same proof on a satisfiable control. The DRAT is only the two-byte empty
  clause over complementary input units: this demonstrates attachment and
  external consumption, not a nontrivial trace, lowering proof, whole-CFG
  certificate, or performance result. Keep the generic solver trait and normal
  pruning unchanged; assess broader proof cost/benefit separately.

- **2026-07-19 — ADR-0278 preregisters the first downstream proof-carrying
  infeasible-path verdict.** Axeyum's source-bound `UnsatProof` and external
  DRAT interoperability already exist; Glaurung's current prototype discards
  the certificate and keeps only a line count. The next isolated-worktree
  increment makes one concrete off-trait verdict own the proof, rechecks it
  against the exact Glaurung `ExprPool` path, proves source binding with a
  weakened-path negative, and exports one fixed bundle for pinned `drat-trim`.
  It does not change ordinary pruning, the generic solver trait, A0,
  authoritative findings, symbolic memory, or the Lean/Alethe track.

- **2026-07-19 — ADR-0277 passes its exact structural gate but is rejected by
  the full performance contract; candidate removed.** Candidate `9533c508`
  removes exactly 107,000 attempts/duplicates, 321,000 declared/visited
  literals, and 214,000 canonical literals while preserving all 162
  decisions, 88 SAT replays, oracle/manifest agreement, emitted CNF, per-query
  structure, and every nonselected origin row. The fixed 12-process unprofiled
  comparison has a favorable 0.96009 paired geomean and exhaustive-bootstrap
  95% upper bound 0.98146, but fails preregistered acceptance: baseline CV
  3.4250%, candidate CV 3.0152%, mixed family 1.04918, and trivial family
  1.32691. Production code is removed at `4fc45767`; do not rerun, relax the
  family rule, or mine the same 107,000 clauses again. The ADR-0259--0277
  duplicate-clause lane is closed. Advance GQ5 only from a new independently
  motivated mechanism/population; otherwise advance PLAN item 5's proof-
  carrying infeasible-path integration.

- **2026-07-19 — ADR-0276 accepts one within-leaf overlap cell; ADR-0277
  preregisters the only permitted production experiment.** The clean detached
  artifact-v37 observation at `6ff05905` passes all 162 decision, manifest/Z3,
  88 SAT replay, family, legacy-baseline, and overlap-invariant gates. All
  107,000 parity duplicates are binary clauses in one `within_leaf`
  `a2-f0-t0-d2-r0-x0` cell across 29 queries; the largest query owns 9.9738%.
  Cross-leaf and cross-owner parity overlap are zero. This does not revive
  ADR-0261's duplicate-leaf hypothesis. ADR-0277 now freezes an encoder-local
  memo only for repeated visits to the same positive direct-root parity leaf.
  It must reduce exactly 107,000 attempts/duplicates, 321,000 declared/visited
  literals, and 214,000 canonical literals while preserving emitted CNF and
  every correctness gate before any unprofiled timing. Candidate `9533c508` is
  now committed after its repeated-root regression began red at 12 versus 4
  attempts; 309 CNF, 21 solver, and 44 benchmark tests plus strict Clippy,
  rustdoc, no-default checks, and links pass. Run exactly one clean detached
  profiled structural gate next. No other leaf/root kind or optimization is
  authorized.

- **2026-07-19 — ADR-0276's GQ5 diagnostic is implemented and frozen before
  corpus observation.** ADR-0260's 107,000 same-owner forward-parity duplicates
  did not imply repeated normalized leaves: ADR-0261's candidate changed every
  selected construction counter by zero. The missing causal partition is
  within one leaf versus across distinct leaves. ADR-0276 therefore freezes an
  opt-in, zero-row parity-leaf overlap profile over the unchanged 162-query
  corrected-wide-v3 population. It records bounded leaf identity/shape,
  partitions parity/parity duplicates into `within_leaf`,
  `cross_leaf_same_owner`, and `cross_owner`, independently re-sums every row,
  and permits at most one separately preregistered follow-on under the fixed
  50% / 10-query / 50% rule. It authorizes no timing or production change.
  Commit `b02b6ab4` preserves the disabled zero-sized path, adds artifact-v37
  overlap rows only to the opt-in profile, retains artifact-v36 analysis, and
  binds the exact 107,000-binary and complete ADR-0260 baseline gates. All 307
  CNF, 21 solver, 44 benchmark, and 10 analyzer tests pass, as do strict Clippy,
  rustdoc, links, and no-default checks. A real retained v36 analysis and a v37
  two-query round trip pass; no corrected-wide-v3 query has been observed with
  v37. Run exactly the one preregistered clean detached fixed observation next,
  preserving strict IR errors, complete decisions, Z3/manifest agreement, and
  original-term replay.

- **2026-07-19 — ADR-0273's deterministic six-cell calibration is rejected;
  no census is authorized.** Axeyum
  `72375263` now bounds retained as well as cold BatSat checks with a reset-per-
  solve progress-check limit. Isolated Glaurung `dc06a37` routes distinct Z3
  rlimit, Axeyum progress-check, and Bitwuzla termination-poll controls through
  all six cold/warm cells, preserves the wall only as a typed safety cap, and
  emits validator-checked v4 traces. Axeyum `241dab31` consumes v4 with exact
  unit/limit identity, outcome/stop-reason drift rejection, and separate
  resource/wall/other accounting; 20 focused analyzer tests pass. ADR-0273
  freezes all 14 first-20 tcpip calibration tiers, N=3, and the independent
  smallest-limit-at-95%-decided selection rule. The dedicated runner and
  selector now encode all 42 processes, sanitize the environment, require the
  all-findings confidence partition, hash every resolved dynamic library and
  retained log, and reject escaped/unvalidated traces; 7 focused calibration
  tests plus the 20 paired-trace tests pass. There are zero real-driver v4 rows.
  The exact release executable is registered at SHA-256 `d96520a0...db5f7`
  together with all 12 resolved file-backed dynamic-library hashes. All 42
  processes complete and validate with exact N=3 tier vectors, zero wall/outer
  deadline stops, and stable finding/work partitions. Z3 first qualifies at
  rlimit 100,000 and Bitwuzla at 4 polls, but Axeyum has no qualifying value; at
  8,192 progress checks cold decides 4,233/4,846 and warm 3,280/4,846, with every
  residual typed resource-limit. The full campaign/analysis hashes are
  `118e90a4...2ec2ec` / `46e8e29f...d5e0c`. No 338-function row is authorized.
  Moreover the cold-Z3 authority ladder changes the explored stream, so limits
  from different tiers cannot be combined. ADR-0274 now preregisters the
  observation-aware correction with zero extension rows: fix Z3 at 100,000,
  require the exact invariant 4,846-check authority stream, and sweep ten
  Axeyum/Bitwuzla shadow-limit pairs at N=3. Its dedicated runner/analyzer now
  reuse every ADR-0273 source/binary/linkage/log gate and additionally reject
  any cross-tier authority identity, Z3 outcome, finding, or outer-work drift;
  3 focused shadow tests, 7 base calibration tests, and 20 paired-trace tests
  pass. All 30/30 rows now validate and reproduce one invariant 4,846-check
  stream. ADR-0274 accepts Z3 100,000, Axeyum 32,768, and Bitwuzla 512;
  campaign/analysis hashes are `0526f925...3ceb7` / `7b20e363...8cf6`. No
  census row exists. Preregister and jointly reproduce the triplet before
  freezing the 338-function census. ADR-0275 now freezes that zero-row boundary:
  N=3 exact first-20 joint reproduction, followed only on success by an N=3
  338/338 census under the unchanged triplet and work/deadline gates. Implement
  its two-phase fail-closed tooling now freezes the exact three-process triplet
  per phase, prevents Phase B unless the accepted Phase A campaign hash remains
  unchanged, and distinguishes the 20/338 work boundary from complete 338/338
  coverage. Phase A now passes 3/3: all six cells decide 4,846/4,846, direct
  warm execution holds, and authority/finding identities reproduce exactly;
  campaign/report hashes are `ec1e15f3...ed05b` / `f1d0d74c...4af4a`.
  Phase B then completes 3/3 validator-clean processes but is rejected: every
  row analyzes only 210/338 functions and records 102 assertion-cap fallbacks,
  despite byte-identical 3,266 findings and 97,112/97,112 verdict agreement.
  Campaign/analyzer hashes are `00928a7a...06d2` / `4522bd0e...fc303`.
  No full-census, recall, or performance claim is authorized. Close this exact
  harder-driver protocol negative and return to PLAN item 4's cold-path
  reduction-depth lane; A1 remains configuration/measurement, A0 remains
  complete, and symbolic memory remains closed.

- **2026-07-19 — ADR-0272 accepts the six-cell neutral warm map and closes the
  performance-leadership framing.** The exact 20-process campaign preserves
  12,902 checks per four-driver pass (10,647 SAT / 2,255 UNSAT), 64,510 repeated
  occurrences, and 387,060 measured cell executions. Every Z3, Axeyum, and
  Bitwuzla cold/warm cell decides every occurrence with the same verdict; all
  warm created/retained populations match, zero fallback occurs, every primary
  warm-pair CV is below 1.86%, and all four preregistered gates pass. Warm
  Axeyum beats warm Z3 on vwififlt (1.0523x), IntcSST (2.2321x), and SurfacePen
  (2.2819x), but loses on Dptf (0.8448x). Warm Bitwuzla beats both on all four;
  cold Axeyum leads only IntcSST/SurfacePen. The reports reproduce byte-for-byte
  under independent analysis. This validates a workload-dependent integration
  regime but rejects an Axeyum speed-lead thesis. PLAN item 3—the separately
  deterministic harder-driver tier—is now next; correctness, deployability,
  proofs, and reproducibility remain the paper spine.

- **2026-07-19 — The neutral in-process mechanism is frozen and ADR-0272 now
  fixes its six-cell experiment before timing.** Isolated Glaurung commit
  `2961d7c` adds benchmark-only Bitwuzla 0.9.1 cold/fresh and warm/source-owner
  cells beside the existing Z3 and Axeyum cells, keeps cold Z3 authoritative,
  rotates all six cells, and emits the additive ordered-measurement v3 schema.
  Focused adapter, lineage, all-operator, W128, six-cell integration, and v2/v3
  validator tests pass. The all-three-backend library suite is 1,030/1,032;
  only ADR-030's two untouched-baseline WinAPI signature failures remain. The
  feature fails closed without its explicit library and the default build is
  unaffected. ADR-0272 binds the exact Glaurung/Axeyum/Bitwuzla sources,
  resolved native libraries, four historical drivers, five fresh processes,
  fixed environment, nine paired contrasts, all-six parity/fallback/CV gates,
  and a zero-row boundary. The registered v3 analyzer is now frozen at
  `5d74283b`: 17 focused tests pass and the historical five-trace Dptf v2 ratio
  reproduces exactly. The exact guarded release executable is built and its
  SHA-256 plus complete resolved-library hashes are committed in the zero-row
  registration artifact. This is the zero-row checkpoint that preceded the
  accepted result above; A0 and symbolic memory remain closed.

- **2026-07-19 — ADR-0269--0271 complete the bounded AArch64 symbolic-CVE
  recall gate and move the integration critical path to the neutral warm
  baseline.** The isolated Glaurung AArch64 ET_REL frontend is frozen at
  `1bcfd304`; the final v3 registration binds two admitted vulnerable/fixed
  pairs, four source sides, eight ordinary/embedded cells, exact environments,
  sinks, witnesses, strict stop accounting, and relocation-equivalent concrete
  access telemetry. V1 correctly failed exact address identity; v2 correctly
  failed a runner/schema field error; both failures are preserved. The
  committed v3 run and independent rerun are byte-identical (SHA-256
  `13f8d286763f5bd326bc1b2d63ea175f4189e25a49303a1ba28a945a27bbb0e8`):
  paired detection recall 2/2, fixed sides clean 2/2, zero fixed-side
  false-positive pairs, and all eight cells execution-acceptable. This is only
  the artifact-admitted selected-pair result, not population precision or
  population-wide recall. ADR-0272 subsequently closes PLAN item 2's in-process
  warm Bitwuzla map; item 3's deterministic harder-driver tier is next. A0 stays
  reproducibility infrastructure, symbolic memory stays closed, and the
  general LLVM frontend stays later work.

- **2026-07-19 — ADR-0268 accepts the deterministic four-side frontend surface
  and narrows the minimum route to Glaurung's existing AArch64 ELF lifter.** The first exact run and immediate rerun had
  identical counts but four drifting stripped-module hashes because LLVM
  embedded each random scratch path in `ModuleID`; v1 output is deleted and
  supplies no claim. The analyzer now normalizes only that provenance line and
  fails if it is absent or duplicated. Nine tests cover that invariant plus recursive-module function,
  instruction, memory, control, call, global, pointer, malformed-input, and
  current-reflector-blocker accounting. The planned LLVM-18 pipeline extracts
  only the handler plus recursively defined direct callees, strips debug-only
  inflation, and leaves frontend/detector status `not-run`. A discarded
  vulnerable-only pilot confirms material inline-assembly and memory surface;
  do not use its partial counts. The committed registration now binds the
  corrected analyzer, ADR-0267 report, four-side denominator, LLVM-18 tools,
  and recursive-extract/strip/no-execution pipeline. V2 then runs twice
  byte-identically (SHA-256
  `47cfd951d7649a9b0528527bf42b28bc96c90e8af4888f0780a75b24542da282`)
  with zero frontend/detector rows. PCI is 1,013 instructions/174 blocks per
  side with 115 inline-assembly calls; Applicom is 560--565/76--78 with 139.
  Both have real memory, globals, external helpers, and pointer casts. Extending
  Axeyum's scalar LLVM reflector would be a general project; preregister exact
  ET_REL handler/CFG/relocation admission and Linux AAPCS64/environment seeding
  in Glaurung instead.

- **2026-07-19 — ADR-0267 retains complete symbolic-CVE artifact attrition and
  admits exactly two pairs to the frontend gate.** All twelve immutable sides
  run and the dedicated worktree restores cleanly: 4 pass, 8 fail. Both
  CVE-2025-40117 (`pci_endpoint_test_ioctl`) and CVE-2025-68797 (`ac_ioctl`)
  have vulnerable/fixed AArch64 ELF + bitcode + textual-IR pairs with exact
  handler presence and identical ordinary/embedded executable bytes. UVC and
  DRM compile but fail byte identity on both sides; both block handlers are
  absent as standalone ordinary-ELF text symbols on both sides. The campaign's
  `valid=false`/nonzero exit is fail-closed completion, not a partial run. Full
  report SHA-256:
  `051fef0102902407d3b1f2096e3c4787ca437f3ae496604c9050bf1de77b53eb`.
  The frontend denominator is two pairs only; measure their LLVM surface next
  without scoring detector recall.

- **2026-07-19 — ADR-0266 accepts the fail-closed paired-artifact builder and
  exact twelve-side campaign before selected execution.** Twelve tests cover
  exact Kbuild command parsing, the sole permitted `-Wa,`
  removal plus embedded-bitcode/output rewrite, AArch64 executable-section
  identity, exact ELF/IR handler names, campaign/tool hashes, zero-execution
  admission, and overwrite refusal. A two-side `pci_endpoint_test` parent/HEAD
  pilot builds and validates both sides, finds the handler in ordinary ELF,
  embedded ELF, and IR, and matches all `.text`/`.init.text`/`.exit.text` bytes
  (framed SHA-256 `1da357917722081d44962449834a6778c185f4198754d2b07c50c8863f607216`).
  The worktree restores cleanly. This is mechanism evidence on an unchanged,
  noncandidate pair. The final campaign pins builder/preflight bytes,
  six candidates/twelve sides, `make -j4`, and twelve exact tool identities.
  Its retained validation is byte-identical on rerun, with all commit/parent
  pairs resolved and zero builds executed (SHA-256
  `d32352e47032c0ef6b908c27fb67577066ef4867c45570a71b16f3ae0c17e406`).
  Zero selected CVE sides have run. Materialize the immutable campaign next.

- **2026-07-19 — ADR-0265 accepts the exact paired symbolic-CVE artifact and
  frontend-executability preflight before any candidate build.** The six corrected rows
  bind one direct helper, two file IOCTLs, one DRM callback, and two block
  helpers; each has an exact AArch64 translation unit, entry ABI, attacker
  inputs, environment requirements, and vulnerable-reachable/fixed-infeasible
  obligation. The clean Glaurung baseline is explicitly
  `no-linux-symbolic-detector-v1`. Seven tests pass. A scalar embedded-bitcode
  pilot succeeds; a noncandidate kernel-HEAD pilot rejects global embed flags
  but confirms ordinary AArch64 Kbuild and selects per-TU command replay plus
  executable-byte identity. No selected build, frontend, or detector row has
  run. The committed preflight is valid with six candidates, the exact
  1/2/1/2 entry partition, and zero build/frontend/detector executions; its
  SHA-256 is `99825d48d4410a29eff88aea4ae88261da3d610e1492e8b5ec4ba4d2f0c1807e`.
  Implement and preregister the non-overwriting paired builder next.

- **2026-07-19 — ADR-0264 accepts the corrected symbolic-CVE effective-handler join
  before any artifact execution.** The exact 22-row Linux IOCTL census and
  reachability result are source-hash pinned. Patch review partitions six
  direct scalar/address-safety candidates from 16 rows requiring speculative,
  authorization, API/protocol, lifetime/concurrency, resource-lifecycle, or
  uninitialized-output semantics. One UVC source path is explicitly corrected;
  the purported integer-underflow row is correctly classified as speculation
  semantics. The validator binds every fixing commit, vulnerable parent, patch
  hash, changed file, and parent handler. Execution preflight then invalidated
  v1 before any build: `CVE-2024-49994` declares `blk_ioctl_discard`, but the
  `BLKSECDISCARD` overflow and fixing guard are in
  `blk_ioctl_secure_erase`. V2 records declared and effective handlers, searches
  the effective symbol, and has nine passing tests. The committed run accepts
  all 22 rows, the unchanged 6/16 partition, 21 identical handler pairs, and
  the sole secure-erase correction. Candidate is not executable or detected;
  no recall claim exists yet. Bind artifact and frontend gates next.

- **2026-07-19 — ADR-0262 accepts all six wider v6 sole-authority finding
  cells.** All 36 tcpip first-20 processes pass exact identities, stable work
  and findings, 0/0 high-confidence parity, complete policy accounting, and the
  v6 partition (20 complete + one deterministic state-budget stop; zero
  deadline/timeout stops). Timeout is a measured no-op from 100 to 1000 ms:
  every ordered set and work counter is unchanged. AnyModel remains stably raw-
  divergent at 211 Z3 / 209 Axeyum with 11/9 backend-only rows. LeastUnsigned
  gives exact 185/185 parity at every timeout but costs 96,075 solves and about
  94 s Z3 / 169 s Axeyum authority time per process. Its set overlaps only 147
  of AnyModel's 220-row union, so parity is not preservation. Close this wider
  unlabeled tcpip tier; prioritize broader labels, A1 resource-config wiring,
  and coordinated Glaurung integration. Keep A2 gated and GQ5 closed.

- **2026-07-19 — ADR-0261 rejects private parity-leaf elision at the fixed
  structural gate; timing is not run.** Clean detached
  `1bce10fd` decides all 162 corrected-wide-v3 representative queries (88 SAT /
  74 UNSAT), agrees 162/162 with the manifest and in-process Z3, replays all 88
  SAT models, and passes every construction/origin identity. All 119,260 exact
  duplicates and 229,651 duplicate canonical literals are attributed. Exactly
  one cell passes the fixed 50% / 10-query / 50% rule: same-owner
  `root/and_tree/forward/parity` contributes 107,000 binary duplicates
  (89.7199%) across 29 queries, with a 9.9738% largest-query share. This is
  53,500 redundant two-clause private parity-leaf encodings, not a measured
  speedup. Candidate `8b95d42a` passes all 162 correctness, manifest, Z3,
  replay, DAG/AIG, CNF-variable, and emitted-clause gates, but clause attempts,
  duplicates, and canonical attempted literals all change by exactly zero
  instead of -107,000 / -107,000 / -214,000. The analysis is byte-identical to
  ADR-0260. Reject and remove the no-op candidate without timing. The origin
  cell established equal clauses, not identical enclosing parity leaves; close
  this lane until separately preregistered leaf-shape/clause-overlap evidence
  identifies a different mechanism.

- **2026-07-19 — ADR-0258 retains the capped nontrivial-DRAT no-selection and
  closes further holdout mining.** Clean detached `10ee9795` exports and self-
  rechecks all 32 fixed hash-ordered rows, but every DRAT is the same two-byte,
  one-line `0\n`; no row meets the preregistered proof-shape gate. Pinned
  `drat-trim` prints an exact `s VERIFIED` line for both real and empty proofs
  on all rows (16 exit 0, 16 checker-trivial-UNSAT exit 1). Preserve that odd
  exit/marker partition and the complete retained-attempt record. Do not widen
  the cap. Next: broader labeled-finding evidence and timeout-sensitive neutral
  sole-authority finding breadth under v6; keep symbolic memory gated.

- **2026-07-19 — ADR-0257 preregisters a bounded nontrivial external-DRAT
  selector before observing another proof shape.** The tested script excludes
  the already observed `0015f5bd...` row, scans at most 32 remaining expected-
  UNSAT rows in ascending content-hash order, and retains every attempt. It
  accepts only a proof longer than two bytes and one line when the real proof
  verifies but an empty proof over the same CNF does not. A fixed-cap
  `no-selection` is valid. Next: commit this protocol, build the exporter from
  that clean detached commit, and execute it without changing the order, cap,
  timeout, checker, or acceptance gates.

- **2026-07-19 — ADR-0256 accepts bounded external DRAT interoperability and
  its corrected checker-sanity control.** The unchanged real DIMACS/DRAT pair
  again makes pinned `drat-trim` exit 0 with `s VERIFIED`. The exact same
  two-byte proof against ADR-0255's preregistered satisfiable DIMACS
  `p cnf 1 0\n` exits 1, reports `no conflict`, and prints `s NOT VERIFIED`.
  Preserve ADR-0254's rejected final-line deletion beside this result. The
  accepted real proof is only `0\n` over an input-unit-refutable CNF, so this
  closes one standard-consumer/checker-binding cell, not a nontrivial proof-
  trace, coverage, lowering, or performance claim. Next: either preregister a
  deterministic retained-attempt scan for a genuinely nontrivial external
  trace under ADR-0257, then prioritize the broader labeled-finding population;
  do not infer symbolic-memory headroom from this proof result.

- **2026-07-19 — ADR-0255 preserves the verified external proof but rejects the
  no-op tamper design.** Clean detached `qfbv-proof-export` emits a self-checked
  558-variable/2,166-clause CNF, two-byte DRAT, and LRAT for the fixed real row;
  pinned `drat-trim` prints `s VERIFIED`. The CNF is already UNSAT by input unit
  propagation, so deleting the only DRAT line leaves an empty proof that also
  verifies. ADR-0254 therefore fails its negative gate without invalidating the
  positive interoperability observation. ADR-0255 now preregisters a corrected
  checker sanity control using exact satisfiable DIMACS `p cnf 1 0\n` and the
  unchanged real proof. Next commit this v1 result/v2 protocol before running
  the new control.

- **2026-07-19 — ADR-0254 adds standard proof export and preregisters the first
  neutral real-query consumer.** `qfbv-proof-export` writes DIMACS, DRAT,
  optional LRAT, and a SHA-256 manifest only after consumer-side self-recheck;
  it rejects scoped/multi-check ambiguity, non-QF_BV, SAT/inconclusive, and
  overwrite. Two process tests and clippy pass, and the former placeholder
  UNSAT-evidence guide now documents the exact clausal versus end-to-end
  boundary. The real cell is fixed before export to the lowest-hash holdout
  UNSAT and pinned `drat-trim` revision/binary, with a dropped-final-step teeth
  control. ADR-0255 now preserves the positive verification and rejected
  final-step control without committing access-controlled proof bytes.

- **2026-07-19 — ADR-0253 accepts the wider real-query proof holdout with one
  stable retained coverage miss.** Two clean detached artifact-v34 runs decide
  1,024/1,024, agree 1,024/1,024 with both the manifest and Z3, replay all 515
  SAT models, and independently recheck CNF DRAT for all 509 UNSAT. The stronger
  route certifies 508/509 (99.803536%); the same `slice-partial` row is retained
  as a 1,500 ms whole-worker hard timeout in both runs, with zero other alarm.
  The fail-closed analyzer accepts exact per-query stability. Combined with the
  disjoint representative, real evidence is now 1,186 queries, 603 SAT replays,
  583 CNF DRAT rechecks, and 582/583 stronger certificates. Next: an
  independent/standardized proof consumer and genuinely broader labeled
  finding evidence, not deadline tuning or another scalar policy cell.

- **2026-07-19 — ADR-0252 preserves the proof-holdout packaging rejection and
  preregisters exact materialization.** The first ADR-0251 command used the
  1,024-row manifest over the 30,628-file full root; `axeyum-bench` correctly
  rejected 29,604 unlisted files before executing a selected query. An exact
  clean-detached reproduction exits 1 with byte-identical 2,397,983-byte
  stderr, empty stdout, and no result artifact. Four tests now gate a
  materializer that verifies both manifest hashes, exact full-manifest
  membership, all source and copied bytes, byte-identical output manifest, and
  exactly 1,024 output `.smt2` paths while refusing overwrite. The committed
  boundary then materializes ADR-0253's accepted execution root without
  changing any ADR-0251 field.

- **2026-07-19 — ADR-0251 preregisters a 1,024-query real-proof holdout before
  execution.** The selector binds the corrected 30,628-query full manifest and
  accepted 162-query representative by SHA-256, excludes every representative
  hash, and takes the lowest content hashes under fixed family/verdict quotas.
  The byte-reproducible manifest contains 515 SAT / 509 UNSAT, zero
  representative overlap, and all six remaining comparison/SAT rows. Four
  tests cover selection, exclusion, malformed/short input, and committed
  registration identities. ADR-0253 now preserves the two unchanged CPU-3
  executions and their one stable retained hard-timeout row.

- **2026-07-19 — ADR-0250 closes the Axeyum-side hidden-worklist gate.** The
  authoritative-finding harness now offers
  `--require-deterministic-worklists`: every process must emit one internally
  consistent exploration-stop partition, deadline/timeout stops reject, and
  the full partition must reproduce within each backend. Required reports use
  v6 while historical/default v5 reports remain stable. All 26 focused producer
  tests and eight independent validator tests pass, and the parser accepts the
  real `runs=1 completed=1` Dptf footer from
  isolated Glaurung candidate `ff3c0a7`. Full two-authority use still requires
  owner-coordinated Glaurung integration; the live dirty checkout remains
  untouched. Next publication work returns to wider corrected real proof
  manifests or a genuinely broader labeled population, not another scalar-
  policy cell.

- **2026-07-19 — ADR-0249 executes and rejects usbprint's deterministic
  policy-resource frontier.** The exact clean-detached `f9511525` run executes
  all 15 point-major cells. Fourteen complete, every policy establishes a
  common prefix of 10, and four complete prefix 15. Prefix-15/site-hash-one has
  identical 91/0 raw/high output across authorities and repetitions, but the
  Axeyum repetitions drift from 522,032 solves / 7,951 canonical attempts to
  522,296 / 7,955. Because that is neither fixed work nor the preregistered
  four-run resource-bound outcome, the aggregate correctly rejects with no
  resource bracket. Post-result-only Glaurung instrumentation at isolated
  candidate `ff3c0a7` exposes the cause: 40 inner worklists partition as 36
  complete, three state-budget stops, and one wall-deadline stop. The outer
  15-function count concealed partial inner work. Preserve the rejected result;
  future evidence must require the new stop partition with zero deadline/
  timeout stops. This is not a solver-speed or recall result and cannot reopen
  symbolic memory.

- **2026-07-19 — ADR-0248 accepts the exhaustive source-backed policy-difference
  adjudication and closes the A0 evidence lane.** The fail-closed validator
  re-reads all 43 source ranges and instructions from 14 tracked, clean,
  hash-exact IOCTLance files. All 54 frozen rows close with no sampling: 30 are
  ordinary fixed IRP/request plumbing, 24 are duplicate presentations of
  already validated sinks, zero are independent vulnerability primitives, and
  zero are indeterminate. Every scalar policy therefore has zero independent
  validated primitives in the varying population; there is no validated policy
  difference or residual gap. Symbolic-address memory remains gated off.
  BoundarySet/DiverseEnum remain settings of A0 requiring bounded successor
  mechanics and new labeled evidence, not follow-on research programs. Next
  publication work should use a genuinely broader labeled population or wider
  real proof manifests; the rejected usbprint frontier remains a work-boundary
  lesson rather than a coverage result;
  the live dirty Glaurung checkout remains untouched pending owner coordination.

- **2026-07-18 — ADR-0246 accepts model-independent stack-region semantics;
  ADR-0247 accepts the corrected five-policy v3 sweep.** V2 remains preserved and
  rejected at maximum's 14/15 precision gate. Two isolated Glaurung candidates
  removed the false arbitrary-pointer row but returned only 13/14 because the
  genuine `[rbp-0x70]` destination is a constant-base expression DAG, not a
  free-symbol sibling of `rsp`/`rbp`. Glaurung `0581f57` admits non-leaf DAG
  ancestry while excluding common constant/symbol leaves. The exact N=2
  maximum-policy control now accepts 14/14 with precision and recall 1.0, zero
  false negatives, zero unexpected high rows, and exact Z3/Axeyum parity. The
  final documented clean revision `7f682e5` passes 992/994 dual-backend library
  tests; only the same two baseline WinAPI rendering assertions fail. The exact
  clean-detached Axeyum `f2af8b40` v3 run accepts all five scalar policies at
  14/14 with precision/recall 1.0 and zero unexpected high rows. Tcpip remains
  zero-high and unlabeled: deterministic settings have exact authority parity
  at 84--110 diagnostics; AnyModel remains 128 Z3 / 126 Axeyum. Work and RSS
  vary materially, with site-hash-one reaching about 264 seconds / 235 MiB in
  the Axeyum cell. ADR-0248 subsequently closes the complete source-backed
  policy difference without a validated primitive. Keep complete usbprint
  separate and symbolic memory gated off. The
  live dirty Glaurung checkout remains untouched pending owner coordination.

- **2026-07-18 — ADR-0243 establishes the nonzero source-backed positive
  control and moves A0 to sweep preregistration.** A new fail-closed validator
  joins Glaurung's v5 authority report to exact tracked source/binary hashes and
  source-plus-machine evidence rather than trusting producer confidence. The
  complete IOCTLance fixture review retains all available clear positives: 14
  finding rows at 12 sites across nine WDM fixtures, not the initially scoped
  five-row subset. At IOCTLance
  `905629a773f191108273a55924accd9f31145a8d`, all 18 manifest paths are tracked,
  clean, and hash-exact. Two order-balanced sole-authority repetitions per
  driver (36 processes) give exact Z3/Axeyum output and work parity: 14 validated
  high rows, 108 diagnostics, 122 raw rows, and 2,322 solves per authority and
  repetition. The join accepts 14 true positives, zero misses, and zero
  unexpected high rows. This is a planted regression denominator, not
  real-world recall or evidence that a policy improves discovery. Next:
  coordinate/integrate corrected Glaurung branch `b79f269`, then preregister the
  five executable AnyModel/least/greatest/site-hash-zero/site-hash-one cells
  with 14/14 as a hard control and separately labeled real-driver discovery
  output. BoundarySet/DiverseEnum remain later settings of the same policy knob
  after bounded successor forking exists; they are not executable cells at
  `b79f269` and must not be approximated by one selected boundary.
  Symbolic memory remains conditional. Exact evidence:
  [`bench-results/glaurung-source-backed-positive-validation-20260718/`](bench-results/glaurung-source-backed-positive-validation-20260718/README.md).

- **2026-07-18 — ADR-0242 retires usbprint's apparent nonzero target after an
  environment-model correction.** Exact switch-table and disassembly evidence
  maps all five former producer-high-confidence rows to guarded reads in
  `HPUsbIOCTLVendorGetCommand` for `METHOD_BUFFERED` IOCTL `0x0022003c`.
  Glaurung had incorrectly made the I/O-manager-owned SystemBuffer kernel
  pointer a free attacker address. Pre-correction ordered traces explain the
  Z3-only row: for the same `SystemBuffer + 2` query Z3 selects effective
  address 1 while Axeyum selects 3, so only Z3 binds the false base to
  `2^64 - 1` and wraps the next `+1` read to zero. TDD on isolated branch
  `axeyum-concretization-policy-a0` at `b79f269` now stores a fixed kernel
  address while preserving `*SystemBuffer` content provenance; genuine
  pointer-control tests use `METHOD_NEITHER` sources. All 22 focused IOCTL tests
  pass independently under Z3 and Axeyum, and both authority examples compile.
  The unchanged v5 harness accepts two order-balanced complete runs at 0/0
  high-confidence rows, 214 diagnostics, and 16,537 solves per process. The
  one raw CRT `memcpy` diagnostic per authority remains visible. Usbprint is
  not a recall denominator. ADR-0243 subsequently supplies a separate 14-row
  planted positive-control denominator before sweep preregistration. The exact
  artifact is
  [`bench-results/glaurung-usbprint-system-buffer-validation-20260718/`](bench-results/glaurung-usbprint-system-buffer-validation-20260718/README.md).
  Boundary/diverse selection remains configuration, symbolic memory remains
  conditional, and WDF/KMDF address/content plus request-length modeling remain
  explicit producer debt.

- **2026-07-18 — ADR-0241 makes finding confidence machine-readable and selects
  a provisional nonzero corpus.** Glaurung `931d8a8` adds opt-in,
  exhaustive `glaurung-ioctlance-confidence-v1` row annotations without
  changing legacy finding bytes; the isolated branch is documented at
  `9692f3c`. Axeyum `593cc582` advances the authority harness to v5, records
  raw/high-confidence/diagnostic sets from the same process, and fails closed
  when high-confidence acceptance lacks a valid producer partition. Twenty-one
  focused Axeyum tests and two Glaurung producer tests pass. Clean N=2 controls
  rebaseline AnyModel, least, greatest, site-hash-0, and site-hash-1 on the
  fixed tcpip prefix: raw counts remain 128/126, 110, 84, 95, and 98, while
  every backend/policy cell has zero high-confidence rows. The AnyModel and
  deterministic unions remain 128 each with 95 shared; all 33 formerly
  unclassified AnyModel-only rows are producer diagnostics with only
  `Arg0`/`Arg1` ancestry. Dptf, vwififlt, IntcSST, SurfacePen, and a NETwtw10
  prefix also have zero corrected accepted rows. Complete x64 `usbprint.sys`
  supplied the provisional target: five Z3 versus four Axeyum stable
  high-confidence rows, including one Z3-only `SystemBuffer` null dereference,
  so the harness correctly rejected parity and required independent review.
  ADR-0242 performs that review and retires all five rows as producer-model
  false positives; they were never accepted as ground truth.

- **2026-07-18 — ADR-0240 corrects the concretization finding baseline before
  the policy sweep.** Exact PDB, disassembly, and valid ordered-trace evidence
  place tcpip's two stable Z3-only AnyModel rows inside internal
  `TcpSendTrackerMarkTransmits` traversal and trace their addresses to generic
  `Arg0` ancestry. Glaurung had relabeled fresh values loaded through any
  tainted address as `*attacker`, laundering that ancestry past its own
  high-confidence filter. TDD on isolated branch
  `axeyum-concretization-policy-a0` at `845239f` now preserves every exact
  source (`*Arg0`, `*SystemBuffer`, nested dereferences); all 18 explorer tests
  pass. Two clean repetitions per authority keep AnyModel's raw 128/126 split,
  now as two Z3-only `**Arg0` diagnostics, while normal output is 0/0
  high-confidence. Least unsigned remains exact at 110/110 raw rows and also
  has no non-`ArgN` source. Therefore the two rows are classified model-sensitive
  false-positive diagnostics, the 33 older arbitrary-only rows remain
  unclassified, and raw `>= AnyModel` is removed as a policy acceptance gate.
  ADR-0241 subsequently closes the 33-row producer-confidence classification
  and advances the isolated branch to `9692f3c`; ADR-0242 then rejects its
  provisional usbprint candidate and advances the corrected branch to
  `b79f269`.

- **2026-07-18 — behavior-preserving Glaurung A0 concretization policy accepted
  on an isolated branch.** Branch `axeyum-concretization-policy-a0` at `07ea0c1`
  exposes one public `ConcretizationPolicy` across `concretize_addr` and
  `eval_concrete`, keeps `AnyModel` as the default, supports the existing
  deterministic extrema/site policies through one selector, and fails closed
  on conflicting preferred/legacy environment configuration. The exact tcpip
  fixed-work gate reproduces all three pre-A0 Axeyum controls in both new
  repetitions: 126 findings, 2,991 solves, zero canonical-choice work, and
  ordered hash
  `a67d7bca28602ab20bbc46d9a5d42705463bd340067dc8e6ec660b35d58ba265`.
  The two known Z3-only raw rows remain, so this is behavior preservation rather
  than authority parity. ADR-0240 subsequently classifies them as
  provenance-laundered `Arg0` artifacts and advances the integration head to
  `845239f`; the pre-correction hash remains A0 seam compatibility evidence,
  not a finding baseline. Focused 6-policy and 17-explorer tests pass; release
  build and dual-backend all-target check pass. Full testing has only two
  inherited WinAPI failures reproduced on untouched base `e98c090`; historical
  repository-wide format/clippy debt remains outside the changed files. The
  live dirty Glaurung checkout is untouched. ADR-0241 subsequently rebaselines
  the existing settings; ADR-0242 rejects its provisional usbprint corpus and
  corrects the WDM SystemBuffer model at branch head `b79f269`. Next coordinate
  and integrate that clean branch, select an independently validated nonzero
  corpus, then treat BoundarySet/DiverseEnum as settings of this mechanism.
  Symbolic memory remains conditional on validated sweep headroom.

- **2026-07-18 — ADR-0239 accepts bounded mixed-extremum four-schedule authority
  parity.** FNV-1a over the fixed
  choice-purpose bytes plus instruction address selects minimum/maximum for
  site-hash-zero; site-hash-one flips every choice. Solver output, expression
  IDs, mutable counters, and process order are excluded. The exact ADR-0238
  tcpip prefix, work/timeout bounds, N=3 authority protocol, rejected
  arbitrary-model control, and accepted minimum/maximum hashes remain fixed.
  Acceptance requires exact site-policy output/work/telemetry parity and an
  identical four-policy union. Growth and recovery of the 33 arbitrary-only
  rows are outcomes, not gates. The first exact attempt reproduced the rejected
  arbitrary-model control and all six exact minimum outputs, then failed closed
  on post-run source identity after a concurrent tracked planning-document edit;
  maximum and both site schedules were unobserved. That inadmissible attempt is
  preserved; the unchanged protocol was rerun from detached preregistration
  commit `57ee6720`. The isolated rerun passes every gate: site-hash-zero and
  site-hash-one produce 95 and 98 identical findings, 28,258 and 79,950 solves,
  and exact canonical telemetry under both authorities. They add three rows to
  the 125-row extremal union for an authority-identical 128-row four-schedule
  union. Against arbitrary-model combined output, 95 rows are shared, 33 remain
  arbitrary-only, and 33 are four-schedule-only. This is bounded parity, not
  finding preservation or exhaustive coverage. The next step is not another
  one-off policy implementation: A0 is accepted on isolated Glaurung branch
  `axeyum-concretization-policy-a0`; coordinate and integrate it, then sweep its
  configurations over wider fixed work. Keep deferred symbolic memory
  conditional on measured headroom after that sweep.

- **2026-07-18 — ADR-0238 accepts bounded extremal-model coverage-union
  authority parity and rejects a finding-preservation claim.** The exact
  ADR-0236 tcpip prefix, pinned source/input identities, 250 ms check wall, 300,000-solve and
  1,800-second process bounds, and N=3 order-balanced protocol remain fixed.
  A greatest-unsigned model policy beside the accepted least-unsigned policy
  yields 84 identical findings, 34,659 solves, 513 completed choices, and
  33,858 probes under each authority and repetition with zero inconclusive
  choice. The accepted least/greatest union contains 125 rows: 69 common, 41
  least-only, and 15 greatest-only. Against the arbitrary-model combined union,
  95 are shared, 33 are arbitrary-only, and 30 are extremal-only. The control
  therefore establishes bounded deterministic union parity, not exhaustive
  model coverage or finding preservation. Next widen fixed work or add
  genuinely broader deterministic representatives.

- **2026-07-18 — ADR-0236 closes the first measured canonical-authority
  cell without hiding the any-model divergence.** On the same current
  Glaurung/Axeyum revisions, sole-authority binaries, tcpip input, first 15
  functions, 250 ms check wall, and N=3 order-balanced repetitions, any-model
  output is stable but differs: 126 sinks are shared and two double-fetch rows
  are Z3-only. Opt-in `glaurung-min-unsigned-v1` instead yields 110
  byte-identical sinks, 80,563 solves, 1,206 canonical attempts, 1,204
  completed minima, two already-infeasible paths, and 79,466 probes under each
  authority, with zero inconclusive choice. Because the common population
  changes from 126 to 110, this is a reproducible experiment policy rather
  than a production default or finding-preservation claim. ADR-0238
  subsequently closes the bounded two-extremum union while retaining 33
  arbitrary-only rows; wider fixed work/model exploration and corrected real
  proof manifests remain. Standalone canonical timers are not performance
  evidence.

- **2026-07-18 — ADR-0235 closes the corrected representative's
  whole-certificate process-isolation gap.** Artifact v34 launches the same
  pinned executable as a source-hashed one-query worker; the parent wall covers
  parse, construction, both proof searches, and both completed-proof
  self-rechecks, then kills/reaps an overdue worker. Two clean CPU-pinned runs
  again decide 88 SAT / 74 UNSAT, replay every SAT model, recheck every primary
  CNF DRAT proof, and certify 74/74 end to end under a 1500 ms process wall. A
  separate 1 ms control keeps the same primary population and retains all 74
  UNSAT rows as `not-certified` plus `hard_timeout`, with zero dropped row or
  alarm. This closes isolation for the representative denominator only; the
  wall includes scheduler/poll/kill/reap overhead and is not a real-time OS
  guarantee. Next: wider corrected real manifests, independent fuzz/oracle
  breadth, and timeout-sensitive/wider authoritative findings.

- **2026-07-18 — ADR-0234 closes representative real-query term-to-CNF
  faithfulness.** Artifact v33 attempts every primary UNSAT on the raw/full
  proof path and independently rechecks both the independent-reference
  bit-blast miter proof and final CNF DRAT. Two clean CPU-pinned repetitions of
  ADR-0187's exact corrected 162-query representative manifest decide 88 SAT /
  74 UNSAT, replay every SAT model, and certify all 74 UNSAT end to end with zero
  non-certification or alarm row under a declared 1000 ms cooperative
  proof-search deadline. The observed maxima are about 154 ms, so this run does
  not exercise expiry, and construction/checking are not hard wall-clock
  bounded. ADR-0235 subsequently closes that representative isolation gap;
  wider real manifests, independent fuzz/oracle breadth, and timeout-sensitive/
  wider authoritative findings remain.

- **2026-07-18 — ADR-0233 closes the timeout-sensitive neutral formula
  control.** Artifact v32 fixes the hidden-oracle population bug: in-process Z3
  now runs after an Axeyum `unknown`, binary fallback cannot replace a real
  QF_BV timeout, and every query enters one of four decided populations. Five
  clean runs over the exact 52-formula tcpip frontier at 50/100/250/1000 ms,
  plus 1,040 cvc5 rows, have zero error, replay failure, decided disagreement,
  or cross-solver SAT/UNSAT contradiction. Axeyum/Z3/cvc5 decision coverage
  rises from 28/13/46 to 52/52/52. At the all-decided 1000 ms tier the
  Axeyum/Z3 per-query geomean is 0.21095 [0.14904, 0.29644], a cold one-shot
  Axeyum win on this exact corpus, not a retained-warm or authoritative result.
  Next: wider/timeout-sensitive sole-authority findings. ADR-0234 subsequently
  closes the representative real-query faithfulness cell.

- **2026-07-18 — ADR-0232 closes the accepted neutral retained-topology
  control.** The cvc5 runner now preserves the exact source-owner session,
  identity-derived persistent-prefix LCP, and temporary-assumption partition
  while remaining explicitly external/textual. Five repetitions decide all
  9,526 checks as 6,801 SAT / 2,725 UNSAT / 0 Unknown with byte-stable output
  and 0.28--1.61% CV. Same-protocol retained medians are 16.4x--57.0x below
  the accepted full-reset totals. This establishes session/representation
  retention as a first-order neutral mechanism, not an in-process cvc5 versus
  Z3/Axeyum ranking. Next: timeout-sensitive neutral/authority widening;
  ADR-0234 subsequently closes representative real-query faithfulness.

- **2026-07-17 — ADR-0231 widens generated proof coverage without deleting
  slow rows.** The public bounded miter/end-to-end APIs share an absolute
  proof-search deadline and map expiry only to `Inconclusive`/`NotCertified`.
  The stride-one width<=8 gate selects 1,505/2,513 generated UNSAT
  (59.888579%): CNF DRAT proves/rechecks all 1,505; stronger
  faithfulness-plus-DRAT certifies/rechecks 1,487 (98.803987%), with 18 exact
  seeds retained as uncovered at 100 ms. Two content-equivalent repetitions
  produce identical counts and seed lists. This closes seed 83's indefinite
  search block, not whole-call timing: construction/checking remain outside the
  cooperative deadline. ADR-0234 subsequently exercises the same bounded API
  on the representative real-query denominator.

- **2026-07-17 — ADR-0230 closes representative real-query CNF DRAT
  deployment.** The complete content-hashed 128-query Glaurung QF_BV manifest
  decides 64 SAT/64 UNSAT with 128/128 Z3 and manifest agreement, zero
  Unknown/error, and all SAT models replaying. Every UNSAT row carries an
  independently rechecked inline DRAT (64/64, zero missing), spanning
  register-slice, slice-partial, arithmetic, and comparison families. This is
  the requested concrete client proof use case, not term-to-CNF faithfulness or
  a performance result. ADR-0226's stronger generated denominator remains
  separate; ADR-0234 subsequently closes the corrected five-driver
  representative faithfulness cell while wider manifests remain open.

- **2026-07-17 — ADR-0229 closes bounded four-driver authoritative finding
  parity.** Separate Z3-only and Axeyum-only Glaurung binaries each control
  exploration for three order-balanced repetitions. All 302 canonical raw
  sinks are byte-identical on Dptf, vwififlt, IntcSST, and SurfacePen (1,812
  stable emitted rows across 24 processes), with zero backend-only output and
  no coverage-bound hit. vwififlt and IntcSST use 8/4 fewer Axeyum-authority
  solve calls, so output parity is exact while exploration equivalence is not
  claimed. A canonical model policy is unnecessary on this tier; timeout-
  sensitive/wider authority parity remains open. The standalone authority
  timers are not fair four-cell statistics, and warm telemetry stays in
  ADR-0228 because Glaurung hides its footer in a sole-feature build.

- **2026-07-17 — ADR-0228 exposes the bounded-warm time/RSS Pareto and real
  hit rate.** Five order-balanced one-shot/adaptive processes preserve every
  Z3-authoritative verdict and finding count on Dptf and SurfacePen. Adaptive
  cumulative Axeyum work is 6.829x/5.465x lower while paired median process RSS
  is 25.58%/14.77% higher. Dptf's one-shot RSS is noisy at 9.20% CV; SurfacePen
  is the stable memory control. Retained-owner hits are 98.75%/98.31%, with
  zero fallback, reset, replay failure, or lifecycle leak. This is a
  high-reuse whole-policy deployment Pareto, not a per-query solver speedup;
  ADR-0215/0217 remain the fair performance claim. Real-query proof coverage
  and ADR-0229's timeout-sensitive/wider authority extension now outrank
  optional four-driver RSS widening.

- **2026-07-17 — ADR-0227 makes QF_BV WebAssembly executable and measured.**
  A build-only wasm32 green hid an immediate runtime trap in the 32-bit AIG
  hash fold; the repair converts the folded value to `u32`, adds a host
  regression, and upgrades CI to instantiate the generated module and execute
  SAT/UNSAT. Stable release evidence records a 1,801,662-byte browser runtime
  (541,248-byte sum under `gzip -9`) and 75,000 measured solves in each of Node
  and Chromium with zero mismatch/trap. Small-case median means span
  13.08--70.66 microseconds. This is absolute deployability evidence, not a
  native comparison or minimum-footprint claim: the parser still pulls
  `axeyum-fp` and `axeyum-strings`. Next measure warm time/RSS and real-query
  proof coverage; preserve the bundle as the parser-slimming baseline.

- **2026-07-18 — ADR-0237 accepts the independent four-oracle correctness
  continuation.** Two untouched `uniform-v1` ranges
  (1,000,000..1,004,000 and 2,000,000..2,004,000) plus one `edge-v1` range
  (3,000,000..3,004,000) must each decide all 4,000 rows in Axeyum, direct Z3,
  cvc5 1.3.4, and Bitwuzla 0.9.1. The harness now accepts checked seed ranges,
  preserves the old generator by name, reports 14 semantic-corner frequencies,
  writes fail-closed JSON, and has a reproducible runner. A 256-row pilot passed
  but is excluded from evidence. The first full attempt then preserved 3,999
  four-way agreements and failed closed on reproducible seed 1,002,261 at the
  inherited 5-second Axeyum worker cap, before rounds B/C and without a success
  JSON. The amended protocol keeps all seeds fixed, names a 30-second cap that
  decides the seed, adds exact nondecision/reproducer telemetry, and asserts
  all-decided directly. The second attempt completed `uniform-a` 4,000/4,000,
  then failed closed at `uniform-b` seed 2,003,009 when cvc5 exhausted the
  inherited 2-second limit; the exact script decides `sat` in cvc5 and Bitwuzla
  under 30 seconds. The next committed protocol applies and records a 30-second
  cap for all engines without changing seeds. The third attempt closed both
  uniform rounds, then retained `edge-c` seed 3,000,881 after Axeyum exceeded
  120 seconds. All four engines decide that exact formula UNSAT under 600
  seconds (Z3 25.225 s, cvc5 41.67 s, Bitwuzla 12.62 s isolated; Axeyum between
  120 and 600 s). The final committed protocol applies the same 600-second
  correctness bound to all engines; these diagnostics are not performance
  evidence. The final same-commit run reaches 12,000/12,000 four-way decisions
  and agreements, replays all 4,471 SAT models, exercises all five widths, all
  35 operator/generator classes, and all 14 declared edge families, with zero
  unknown, timeout, crash, process/parser failure, replay gap, or disagreement.
  Independent seeds/edge frequencies and the second neutral implementation are
  done; next correctness evidence is wider real manifests.

- **2026-07-17 — ADR-0226 establishes the first generated proof-coverage
  denominator and its widening boundary.** The 4,000-row population contains
  2,513 UNSAT results; a predeclared width<=8/seed-divisible-by-4 subset selects
  169 (6.725030%). All 169 produce and independently recheck both CNF DRAT and
  end-to-end faithfulness-plus-DRAT certificates. The remaining 2,344 are
  unmeasured, not failed. A complete width<=8 diagnostic isolates seed 83:
  CNF DRAT rechecks, but end-to-end certification exceeds a 15-second process
  bound because the API has no cooperative deadline. Add isolated/deadline-aware
  certification before widening, then measure the real Glaurung UNSAT
  denominator.

- **2026-07-17 — ADR-0225 makes the accepted QF_BV seed round fully
  three-way and coverage-checked.** All 4,000 deterministic formulas decide and
  agree in Axeyum, direct Z3, and cvc5; all 1,487 Axeyum SAT models replay; and
  there are zero Unknowns, crashes, timeouts, replay gaps, or neutral
  process/parser failures. The test now requires all five declared random
  widths and all 35 operator classes. Routine CI retains the 250-row cvc5
  sample; the publication lane explicitly requires all 4,000 decisions. Next
  correctness evidence must add independent seeds/edge cases, another neutral
  implementation, or the proof-coverage denominator rather than repeat this
  bounded round.

- **2026-07-17 — ADR-0224 lands the first standing QF_BV multi-oracle fuzz
  gate.** All 4,000 deterministic well-typed instances decide identically in
  Axeyum and direct Z3; all 1,487 Axeyum SAT models replay on the original IR;
  and all 250 fixed cvc5 samples decide and agree three ways with zero skip.
  Four named Glaurung controls cover normalized concat/extension, legitimate
  empty SAT versus model-less UNSAT, and the linked-adapter W128 boundary;
  three strict-negative controls reject malformed width/value contracts. A
  fail-closed oracle-result split found and fixed nonstandard `!=` in the fuzz
  reproducer, which the old coarse skip bucket had hidden. Additional seed and
  coverage rounds plus proof-coverage measurement remain open; consumer
  state-machine failures are not misrepresented as valid-formula fuzz coverage.

- **2026-07-17 — ADR-0223 completes neutral cvc5 breadth across the accepted
  four-driver map.** The ADR-0222 runner now covers all 9,526 checks: 6,801 SAT
  / 2,725 UNSAT / 0 Unknown, with all 6,162 requested SAT value responses and
  only 2,608 expected post-UNSAT diagnostics. Every driver's stdout is
  byte-identical over N=5 and timing CV is 0.16--0.42%. cvc5's per-check
  difficulty order does not mirror the Axeyum/Z3 warm result, rejecting a
  universal formula-size or FFI explanation. Neutral cold-reset breadth is
  done; topology-equivalent neutral performance, broader multi-oracle coverage,
  timeout evidence, finding parity, and deployment remain open.

- **2026-07-17 — ADR-0222 adds a neutral cvc5 oracle and cold-reset external
  SMT point on the exact Dptf stream.** A fail-closed runner validates every
  trace/index/query hash and replays 561 ordered standalone scripts through
  one cvc5 1.3.4 process per repetition, with a full reset after every query
  and model output enabled. All five runs preserve 317 SAT / 244 UNSAT / 0
  Unknown, all 206 SAT value responses, and byte-identical stdout. CPU-pinned
  median batch time is 2.593056 s with 0.4222% CV. This is an external textual
  integration point, not a paired in-process or warm-cell ratio. Widen it to
  the accepted small drivers and add a warm-neutral API cell; multi-oracle
  fuzzing, timeout, finding parity, and deployment remain open.

- **2026-07-17 — ADR-0221 closes the ordered retained-core control and moves
  the mechanism to representation/integration.** The complete Dptf stream has
  561 decisions, of which 130 are replay-cache hits and 431 enter the SAT core.
  Five per-path replays preserve all 187 SAT and 244 UNSAT core verdicts.
  Retained BatSat beats retained Z3 Boolean on the same Axeyum CNF stream by a
  3.5527x per-call solve geomean; both SAT and UNSAT partitions agree. This is
  not an end-to-end ratio and learned clauses are core-private, but it rejects
  the hypothesis that native warm Z3 wins because its Boolean core generally
  searches Axeyum CNF faster. ADR-0222 now supplies the neutral cold-reset SMT
  point; the topology-equivalent neutral, timeout-sensitive,
  finding-authoritative, multi-oracle-fuzz, and deployment gates remain open.

- **2026-07-17 — ADR-0220 closes fresh exact-CNF parity and moves the causal
  boundary to retained state.** Glaurung exports 244 Dptf warm-UNSAT clause
  databases with active selectors materialized as units. Across N=5 fresh
  solves, BatSat, the proof core, Z3 Boolean, and Kissat 4.0.4 agree UNSAT on
  every input; all proof-core DRAT outputs recheck. The proof core is 2.627x
  faster than BatSat before checking, while fresh Z3 is far slower despite Z3's
  warm end-to-end win. Next compare the ordered persistent clause stream and
  learned-state/topology effects; this is not a neutral end-to-end SMT result.

- **2026-07-17 — ADR-0219 moves the warm mechanism boundary from construction
  to SAT and Dptf UNSAT.** A fail-closed ordered join pairs one cold and one
  retained profile with all 9,526 checks across four diagnostic runs.
  Retention removes 98--99% of cold AIG/CNF additions; SAT becomes 65% Dptf,
  70% vwififlt, 58% IntcSST, and 48% SurfacePen of Axeyum adapter time. Dptf's
  losing UNSAT stratum adds 148 AIG nodes/258 clauses per check and spends
  36.6%/51.9% in CNF/SAT. Profile emission dominates outer timing, so no new
  speed ratio is claimed. ADR-0220 subsequently completes the fresh exact-CNF
  control and moves the open mechanism to persistent learned state/topology.

- **2026-07-17 — ADR-0218 narrows the fair regime to outcome, purpose, and
  reuse composition; internal mechanism attribution is next.** A new
  fail-closed joiner revalidates all 20 raw traces and 9,526 hash-addressed
  queries. SAT favors Axeyum on every driver (1.16x--1.77x warm), while UNSAT
  ranges from 0.332x Dptf to 2.038x SurfacePen. IntcSST/SurfacePen remain
  1.476x/1.488x Axeyum wins on retained checks alone. Address concretization
  favors Axeyum everywhere; value witness favors Z3 on three drivers; repeated
  query frequency correlates +0.32 to +0.63 with Axeyum's warm advantage.
  Formula size alone does not order the win/tie/loss map. Marginal
  standardization is explicitly descriptive. ADR-0219 now completes the
  internal work join and selects a matched Dptf UNSAT cross-core control.

- **2026-07-17 — ADR-0217 establishes a fair Axeyum-winning regime but keeps
  its cause open.** Five fresh-process four-cell repetitions preserve fixed
  work and all decisions on each named small driver, with zero nondecisions,
  operational results, disagreements, replay failures, or fallbacks. Warm
  Z3/Axeyum is 1.5315x [1.4512, 1.6167] on IntcSST and 1.5584x [1.5069,
  1.6096] on SurfacePen, both favoring Axeyum; vwififlt is parity at 1.0030x
  [0.9731, 1.0350]. With Dptf's 0.7875x Z3 win, the map is two wins, one tie,
  and one loss—not a blanket speed result. Cold cells split too, so “small
  formula/FFI-bound” remains a hypothesis. ADR-0218 now completes the
  trace-available shape/outcome/purpose/reuse join; ADR-0219 adds internal
  AIG/CNF/SAT work attribution and selects a neutral cross-core control before
  the timeout-sensitive marked workload.

- **2026-07-17 — ADR-0216 makes the minimal QF_BV solver profile real in
  consumers and the browser target.** `axeyum-solver` now defaults exactly to
  `qfbv`; bench/EVM/property/verify explicitly select `full`; and a manifest +
  dependency-tree firewall rejects drift. Full-facade integration targets are
  explicitly gated, so the package-default test build is green without
  weakening the all-feature suite. Glaurung's production
  `solver-axeyum` selects only QF_BV, while the legacy SMT-LIB reference bridge
  is quarantined behind `solver-axeyum-text` + `full`; both profiles compile.
  `axeyum-wasm` is now a workspace member and preserves its JSON API through a
  narrow parse-to-`SatBvBackend` route with real SAT/UNSAT tests and fail-closed
  non-QF_BV rejection. The first actual wasm32 build found a stale
  `std::time::Instant`/`web_time::Instant` proof-export boundary; the repaired
  target build passes and CI now owns it. This establishes a minimal solver
  surface, not a minimum bundle-size claim: the shared parser still pulls its
  pure-Rust FP/string parsing dependencies. ADR-0227 subsequently executes and
  measures this boundary, preserving parser slimming as a baseline-relative
  candidate rather than an assumed footprint claim.

- **2026-07-17 — The consolidated code/publication review changes the success
  criterion and immediate order.** The paper is no longer organized around a
  general speed claim; its spine is strict correctness, measured deployability,
  and an honestly delimited performance regime. ADR-0221 closes the matched
  persistent clause-stream control; ADR-0222 supplies the first neutral Dptf
  cold-reset external SMT point; and ADR-0223 widens it to all 9,526 accepted
  checks; ADR-0224 adds the standing multi-oracle lane, and ADR-0225 closes the
  full-cvc5 4,000-row seed round with executable operator/width coverage;
  ADR-0226 adds the first explicit generated proof denominator; and ADR-0227
  executes and measures the stable browser artifact after fixing a wasm32-only
  runtime trap.
  Publication blockers are now: (1) wider authoritative/model-exploration
  evidence; (2) independent multi-oracle rounds plus another
  neutral implementation/API boundary; and (3) wider real-query proof
  populations.
  ADR-0229 closes exact raw finding parity for the current four-driver bounded
  tier without needing canonical model selection. ADR-0236 then records two
  stable tcpip Z3-only any-model sinks and closes one explicit canonical-
  authority cell with exact output and exploration-counter parity; because
  canonicalization changes the finding population. ADR-0238 accepts exact
  least/greatest union parity but retains 33 arbitrary-model-only rows, so
  wider authority/model exploration remains. Enforcing the existing `qfbv`
  profile in Glaurung and
  `axeyum-wasm`, plus executable WASM size/latency evidence, is complete;
  ADR-0228 now closes two current one-shot/warm RSS and hit-rate controls;
  ADR-0230 closes CNF-only proof deployment on the historical three-driver
  representative, ADR-0234 closes end-to-end faithfulness on ADR-0187's
  corrected five-driver representative, and ADR-0235 closes its whole-process
  isolation gap; wider proof populations remain. Solver
  namespace/module breakup, table-driven duplicate removal, and
  typed policy/config work follow as bounded behavior-preserving refactors; they
  must not churn the active evidence baseline. The latest 162-query semantic
  gate remains 162/162 decided and agreed under raw/canonical policies (0.627x/
  0.310x one-shot Z3 ratios), but those setup-sensitive smoke numbers are not a
  fair warm headline.

- **2026-07-17 — ADR-0215 closes the topology-equivalent four-cell mechanism
  and first clean control; the honest fair result favors warm Z3.** Glaurung
  `4ae96cf` adds a real persistent Z3 `IncrementalSolver`, exact source-prefix
  sibling rewind, shared owner/serial-lease lifecycle, rotating
  `{Z3, Axeyum} x {cold, warm}` timing, the additive ordered-check measurement
  v2 schema, strict validator aliases/classes, and a full-width u128 native-Z3
  repair. The W128 regression fails on the former low-64-bit model and passes
  with exact decimal numeral construction/model lifting. Axeyum's analyzer now
  accepts v1/v2, reports four separately filtered paired contrasts, and writes
  explicit four-cell CDFs; ten synthetic fail-closed tests pass, including
  cross-repetition decided-outcome drift rejection. Five clean
  fresh-process DptfDevGen runs preserve the same 561 checks, all four cells
  decide every occurrence, and both warm populations stay 7 created + 554
  retained with no fallback/error/disagreement/replay failure. Geomeans are
  cold Z3/Axeyum 0.9661x [0.8709, 1.0706], warm Z3/Axeyum 0.7875x
  [0.6893, 0.8977], Z3 cold/warm 8.9752x [8.5511, 9.4112], and Axeyum
  cold/warm 7.3157x [6.4477, 8.2741]; every per-run CV is below 1.67%.
  Therefore Axeyum is about 1.27x slower than topology-equivalent warm Z3 on
  this easy driver, and the legacy 7.0678x cold-Z3/warm-Axeyum alias is not a
  solver headline. Exact artifacts live in
  `bench-results/glaurung-four-cell-dptf-20260717/`; raw traces remain
  access-controlled. Next: map the small-formula fair regime, enforce real
  minimal-profile consumers, add multi-oracle/neutral evidence, and run
  authoritative finding parity while GQ5 resumes causal cold CNF work.

- **2026-07-17 — ADR-0214's paired mechanism and first clean real-driver
  exercise are complete; ADR-0215 supersedes its baseline blocker.** Glaurung
  `eb624c0` additively marks new
  ordered traces with both timed backend result classes and a closed Axeyum
  execution population: cold, snapshot warm, newly created warm, retained warm,
  timeout cold retry, or a named missing-path/auto-probe/path-cap/assertion-cap/
  invalid-delta class. Its validator binds field presence and rejects unnamed
  classes; a hash-repaired mutation test proves the semantic check is not only
  file-integrity checking. The complete historical 85,449-event dxgkrnl trace
  still validates without the additive marker. Axeyum's new fail-closed analyzer
  requires N>=5 identical-work repetitions, rejects operational/disagreement/
  configuration/query/execution-population drift, uses only occurrences both
  backends decide in every repetition, and reports per-occurrence geomean
  `Z3/Axeyum` speedup with deterministic bootstrap 95% CI, p50/p90/p95/p99,
  per-run CV, four outcome buckets, pure-warm/retained-warm execution rates and
  execution partitions, and optional CSV/PNG CDFs; ratio-of-sums is absent by
  construction. Seven analyzer tests and five producer trace tests pass. A clean
  detached Glaurung `eb624c0` / Axeyum solver `ee1bc306` DptfDevGen exercise
  then runs five fresh processes in each predeclared `{1,5,60}`-second cell.
  Every cell preserves the same 561/561 both-decided occurrences, 7 warm-created
  plus 554 warm-retained checks, zero fallback/disagreement/nondecision/error,
  and paired geomeans of 5.9771x, 6.0953x, and 6.0128x with 95% CIs
  `[5.3341,6.7167]`, `[5.4429,6.8513]`, and `[5.3662,6.7548]`; per-run CV is
  1.8037%, 0.7836%, and 1.5977%. Exact JSON/CSV/PNG artifacts are committed in
  `bench-results/glaurung-paired-dptf-20260717/`; the retained 133 MiB raw set
  reanalyzes byte-for-byte. This is a one-driver no-timeout mechanism control,
  not a headline: cold one-shot Z3 remains confounded with warm Axeyum.
  ADR-0215 now supplies the formerly missing topology-equivalent control;
  neutral-solver and timeout-sensitive marked workloads remained next at this
  checkpoint and were later closed by ADR-0233 and ADR-0262. Old
  tcpip/dxgkrnl artifacts cannot supply missing per-check outcomes retroactively.

- **2026-07-17 — ADR-0213 resets the Glaurung paper-evidence boundary without
  discarding the engineering gates.** Review of Glaurung's pre-submission
  checklist confirms that strict typing, actionable sort failures, original-
  term replay, and the three real consumer soundness defects are the strongest
  lead contribution. Existing exact-work, finding, RSS, and run-CV gates remain
  valid for product-policy and optimization admission, but aggregate/single-run
  ratios are not publication statistics. Immediate work is now: add both
  backend result classes and explicit warm/fallback reasons to each fixed-work
  ordered check; analyze N>=5 repetitions using both-decided paired geomean
  ratios, deterministic-bootstrap 95% CIs, p50/p90/p95/p99, CDFs, process CV,
  decided/nondecided buckets, and a timeout sweep; then add topology-equivalent
  warm Z3 plus a neutral solver and authoritative finding parity/canonical model
  selection. ADR-0214/0215 now complete the paired and topology-equivalent
  mechanisms; ADR-0222/0223 add complete neutral cvc5 cold-reset breadth, while
  warm-neutral/finding/timeout gates remain. GQ5 cold AIG/CNF work
  remains the leading pure-solver engineering lane. The current
  Glaurung benchmark README is therefore draft evidence, not an accepted
  headline-performance artifact.

- **2026-07-17 — ADR-0212 proves wider dxgkrnl functionality but defers the
  direct-delta default.** Clean Glaurung `9ace064` analyzes every available
  `dxgkrnl.sys` function under 139 dispatch roots and publishes 85,449 ordered
  events / 17,400 checks / 13,577 unique queries / 3,005 assertions / 8,816
  model reads plus 312 stable findings. Producer validation and independent
  Axeyum `1cc19181` replay both pass with zero verdict/model failures. Three
  ordinary-core native control/candidate pairs preserve exact work, actual
  outcomes, replay-cache behavior, source-owner/serial-lease topology, and
  zero continuation traffic. The standard gate nevertheless rejects control/
  candidate Axeyum-time CV of 14.430%/8.306% above 3%; a relaxed comparison is
  diagnostic only. Slower-core calibration stabilizes time but changes actual
  outcomes at the 250 ms first-check boundary and is rejected by the new exact
  no-op comparator mode. Keep direct delta opt-in; repeat in a quieter
  predeclared environment or use another valid no-timeout IOCTL driver. Real
  `win32k.sys` imports service-table/callout registration but exposes no WDM or
  KMDF dispatch roots, so route it to a future system-service/callout frontend
  rather than counting zero queries as solver evidence. The leading available
  pure-solver work remains measured cold AIG/CNF construction before SAT, after
  ADR-0213's paired fixed-work harness is available.

- **2026-07-17 — ADR-0211 accepts native same-session continuation inside
  direct delta; wider direct-delta admission remains separate.** Clean
  Glaurung `33191ac` completes the fixed 156/338-function tcpip run under
  4 GiB and publishes 326,364 ordered events / 71,136 checks / 50,687 unique
  queries / 10,515 native packs / 27,940 model reads plus 794 stable finding
  rows. Producer validation and independent Axeyum `ddb368b7` replay both
  pass; the latter validates every unique query and model read and is bound by
  report SHA-256 `3a9a6b45...b72b3387`. Three interleaved native
  control/candidate pairs preserve exact work, source-owner/serial-lease
  topology, findings, implementation revisions, and zero correctness/cleanup
  alarms. Candidates perform 29 continuations = 18 recoveries + 11 honest
  `Unknown`s + 0 errors. Candidate p50 Axeyum time/RSS changes
  +2.027%/+1.021%, time CV is 0.365%, and comparison SHA-256 is
  `0f27afce...d1adbc3`; every 3%/5%/3% alarm passes. Glaurung `9ace064`
  therefore defaults the single retry on only after direct delta is selected,
  with explicit/unrecognized values failing closed to off. Direct delta itself
  remains opt-in. Next use another wider/no-timeout driver to decide that
  separate route and investigate the zero-query `win32k` frontend gap; keep
  the pure-solver lane focused on measured cold AIG/CNF construction before SAT
  tuning.

- **2026-07-16 — ADR-0210 accepts exact ordered same-session timeout
  continuation; native admission remains explicit/off.** Glaurung `3c3c77e`
  replaces recursive trace rendering with deterministic postorder-ordinal
  SMT-LIB `let` bindings, preserving DAG sharing and cross-pool byte identity.
  The clean 4 GiB tcpip run publishes a validated 3.8 GiB stream with 301,852
  events, 15,501 paths, 70,823 exact checks, 50,429 unique queries, and 27,731
  model reads. The independent control/candidate bind the same manifest,
  event hash, executable, 5 s validation budget, and 250 ms policy budget;
  every work/structure/model/materialization field matches. The candidate
  performs 14 continuations = 1 SAT + 6 UNSAT recoveries + 7 repeated unknowns
  + 0 errors, leaves 7 `Unknown`s, and has zero decided disagreements. Warm
  replay changes 188.646→192.356 s (+1.97%) and RSS
  1,262,596→1,263,024 KiB (+0.034%), inside the alarms. This is a passing
  mechanism gate for ADR-0209, not a topology/default claim. Next repeat the
  native policy in Glaurung's production source-owner/serial-lease topology
  with exact traffic/findings and the full time, ratio, RSS, reset, replay, and
  variance gates; keep the switch off until then. The complete stable-toolchain
  verification is green: format, strict all-target/all-feature Clippy,
  serialized all-feature workspace tests and doctests under 4 GiB, warning-free
  rustdoc, QF_BV profile, 53 benchmark-recipe tests, the 162-query pinned
  Glaurung regular gate, foundational resources, generated rules-as-code, and
  documentation links.

- **2026-07-16 — ADR-0209 retains same-session timeout continuation as an
  explicit candidate.** Glaurung `6e5b255` grants one synchronized retained
  `Unknown` a second 250 ms check on the same solver, reusing translated
  assumptions and exporting an exact counter partition. The full-budget tcpip
  pair performs 14 continuations = 5 recoveries + 9 repeated unknowns + 0
  errors, reduces Axeyum nondecisions 14→9, and stays inside the time/RSS alarms
  (+1.98%/+0.034%) with zero SAT/UNSAT disagreements or resets. It is not an
  admissible causal/default result: both processes hit the analysis deadline,
  candidate traffic is +19 queries, and it retains all 780 control findings
  plus two later null dereferences. Keep the switch off. Next hold work/query/
  finding identity constant in a fixed-work or repeated DriverSpec comparison;
  do not interpret deadline-dependent extra coverage as a solver disagreement
  or speed claim. The subsequent fixed-156-function pair also fails exact
  identity: Z3 nondecisions differ 47→46, steering 70,592 versus 70,768 queries
  and 782 versus 783 findings (781 shared). Continuation recovers 3/11 at
  +1.47% Axeyum time/+0.18% RSS with zero disagreements/errors/resets/replay
  failures, but those deltas are descriptive only. Next capture one ordered
  authoritative stream and replay both policies exactly; another live pair is
  not the acceptance gate.

- **2026-07-16 — ADR-0208 rejects whole-snapshot cold timeout retry on RSS.**
  Glaurung `35b25ab` adds an explicit/off direct-warm `Unknown` retry through
  one fresh Axeyum solver under the same 250 ms cap, preserving the original
  `Unknown` on another timeout/error and exporting a complete counter
  partition. Tcpip performs 15 retries = 4 recoveries + 11 repeated unknowns +
  0 errors with zero SAT/UNSAT disagreements or resets. Axeyum time rises only
  2.38%, but RSS rises 10.46% (447,888→494,728 KiB), failing the 5% alarm; query
  count also drifts. Dxgkrnl performs zero retries and preserves the exact
  17,712-query traffic. Keep the diagnostic off. Next measure a bounded second
  check on the synchronized retained solver or a strict recoverability
  predictor; do not pay whole-snapshot reconstruction again without a memory
  proof.

- **2026-07-16 — ADR-0207 closes the widened concat error class and isolates
  the remaining timeout policy.** Glaurung's strict 60-second tcpip pack
  validates 784 distinct splits / 234,463,502 bytes; 733 are Axeyum errors with
  the same `extract [63:8] out of range for width 57` cause. A one-bit `setcc`
  child entered a concat declared as 56+8 bits, but the text/Z3/Axeyum consumers
  ignored those declared halves; Z3's later coercion hid the mismatch and used
  the wrong bit placement. Glaurung `d60ed0f` coerces both concat children at
  every boundary while Axeyum stays strict. Renderer/Z3/Axeyum regressions and
  all 43 backend tests pass. Exact reruns remove all adapter errors and warm
  resets: tcpip executes 72,291 queries with 55 split occurrences / 15 Axeyum
  nondecisions at 1.9x Z3; dxgkrnl executes 17,712 with zero Axeyum
  nondecisions at 2.7x. Axeyum cold replay decides all nine Z3-decided tcpip
  residual formulas (9/9 expected), while the 250 ms control decides 5/9 and
  returns four explicit `Unknown(Timeout)`; SAT is 93.2% of their diagnostic
  pipeline. Glaurung `0249d44`/`7b1671e` archive exact pre/post LFS packs and
  manifests. Measure warm-state versus cold fallback, then run full-budget and
  repeated findings/RSS/variance gates; direct stays opt-in and `win32k` stays
  a frontend coverage gap.

- **2026-07-16 — ADR-0206 turns the widened `tcpip` failure into an exact
  corpus boundary.** At the standard 600-second per-function ceiling,
  `tcpip` expands from the reported 33,501-query diagnostic tier to 70,639
  queries. SAT/UNSAT disagreements stay zero, but Z3 has 43 non-decisions,
  Axeyum 936, and 973 occurrences are decided by exactly one backend; 925 warm
  resets and 480 assertion-cap fallbacks also occur. Axeyum remains 1.7x faster
  at 440,384 KiB RSS, but the row fails parity. Glaurung `a6a5cc0` adds
  `GLAURUNG_DUMP_SHADOW_SPLITS`: exact atomic SMT-LIB bytes plus stable backend
  classes only for decided/nondecided splits. Four combined-feature tests pass.
  Capture the 60-second `tcpip`/`dxgkrnl` split corpora and attribute timeout,
  error, reset, and fallback before adding either to GQ10.

- **2026-07-16 — ADR-0205 accepts the source-prefix production win and moves
  next to large-driver widening.** Glaurung `29031f8` commits a clean
  92,721-check artifact with 100% Z3 agreement, unchanged findings, zero
  unknown/replay failures, exact traffic, terminal-zero gauges, and 4 GiB
  children. Against serial snapshot, source direct improves SurfacePen
  time/ratio/RSS 16.11%/17.39%/0.36% and NETwtw10 6.07%/6.61%/1.72%; Z3 drift
  is +1.55%/+0.58%, so every production alarm passes. A fresh exclusive-direct
  control favors the candidate too, but +4.06% SurfacePen Z3 drift correctly
  rejects that causal comparison. Direct stays opt-in. New one-process evidence
  adds 33,501 `tcpip` and 17,572 `dxgkrnl` checks with zero disagreements and
  2.5x/4.7x speedups; add them to the repeated RSS gate next. `win32k`/`pciidex`
  have zero solver queries and remain Glaurung dispatch-coverage gaps, not
  Axeyum evidence.

- **2026-07-16 — ADR-0204 lands exact source ancestry for direct siblings;
  production measurement is next.** Glaurung `aee3418` gives every persistent
  append an immutable ancestry node and lets forks share only its `Arc`. The
  direct adapter computes the true common ancestor by node identity, pops one
  worker-local mutable solver to that depth, and translates only the target
  suffix. Neither retain depth, cloned-pool `ExprId`, nor a probabilistic hash
  carries authority. A RED/GREEN regression deliberately submits the `x=7`
  sibling with stale depth two after solving `x=5`; it rewinds to the one-root
  parent and returns `x=7`. Backend 42/42, explorer 12/12, and both combined
  Z3+Axeyum direct regressions pass under 4 GiB. Direct remains opt-in. Extend
  the strict lineage gate, calibrate real SurfacePen traffic, and then repeat
  the SurfacePen/NETwtw10 production comparison.

- **2026-07-16 — ADR-0203 closes the direct-delta gate and defers production
  admission.** Six clean processes per artifact execute 92,721 exact checks
  with complete Z3 agreement, unchanged findings, zero unknown/replay failures,
  exact traffic, terminal-zero gauges, and the 4 GiB child limit. Direct entry
  beats exclusive-transfer snapshot on SurfacePen/NETwtw10 Axeyum time by
  10.98%/5.08%, so removing snapshot reconstruction is a real causal win. It
  fails the actual serial-snapshot replacement gate: SurfacePen time/ratio rise
  7.83%/9.54%, and NETwtw10 RSS rises 16.73%. Glaurung `12925e9` commits all
  three artifacts and ADR-012. Direct stays opt-in; the next GQ7 implementation
  target is source-identity/COW sibling-prefix sharing with exclusive mutable
  ownership and both controls repeated.

- **2026-07-16 — the real gate catches a direct-delta sibling soundness bug
  before default admission.** Combining depth-only direct retain markers with
  ADR-0199's complete-snapshot serial sibling lease produces 497/2,551
  SurfacePen verdict disagreements: equal-depth siblings have opposite final
  branch roots, but the direct session retained the prior sibling root. This is
  a downstream ownership-contract error, not an Axeyum solver error. Glaurung
  `f4da0eb` makes the incompatible lease ineffective in direct mode and uses
  exclusive LIFO transfer plus distinct sibling sessions. All 11 explorer tests
  pass, including the pure policy guard; the identical release stream then
  agrees 2,551/2,551 with zero unknowns/replay failures. Single-process smokes
  show the honest tradeoff: direct improves the topology-equivalent transfer-
  only snapshot control (399.8 versus 434.6 ms Axeyum, RSS 79,464 versus 78,952
  KiB) but loses to serial snapshot (357.7 ms, 73,936 KiB). Repeat both controls;
  direct cannot default until it beats production or gains sound source-
  identity/COW sibling sharing. ADR-0203's repeated gate now supersedes these
  smokes and confirms that decision.

- **2026-07-16 — ADR-0202 accepts causal direct-delta warm profiling.**
  Glaurung `00bd660` advances the warm producer to v7 with an explicit
  snapshot/direct entry mode and exact persistent/temporary partitions for the
  complete query, translated roots, and root encodings. Unprofiled direct
  checks do not sample detailed solver stats. Fresh-process direct and snapshot
  smokes validate at 4/4 and 6/6 decided respectively; the direct sequence
  records exactly two persistent roots and one temporary root
  translated/encoded. The fail-closed Axeyum validator suite is 53/53 green,
  retains v1--v6 historical inputs, and exposes entry partitions in both warm
  and adaptive mixed summaries; Ruff and links pass. The full Glaurung backend
  group is 41/41 green after an immediate rerun of one known text-bridge timeout
  flake, and combined Z3+Axeyum adapter coverage passes. Profiling is no longer
  the blocker; ADR-0203 records the completed repeated gate and defers default
  admission.

- **2026-07-16 — Glaurung wires the first-class session into the explorer,
  strictly opt-in.** Glaurung ADR-011/`f5a3b7a` gives every explorer state an
  absolute confirmed persistent depth and sends `(retain, persistent,
  temporary)` boundaries through the Axeyum session. Existing owners translate
  only suffix roots; temporary probes use assumptions; missing owners fully
  materialize; invalid partitions and operational errors drop state; forks
  inherit only the confirmed depth under a distinct owner; restarts reset both
  owner and depth. The marker advances only after backend acknowledgement, and
  the full query remains available to Z3, ordered capture, and one-shot
  fallback. The complete backend group is 41/41 green, both focused explorer
  ownership tests pass, and the selected adapter passes with both Axeyum-only
  and Z3+Axeyum feature sets. The route remains behind
  `GLAURUNG_AXEYUM_DIRECT_DELTA=1`; repeated ordered
  decision/finding/time/RSS gates are next.

- **2026-07-16 — ADR-0201 accepts a first-class retained solver trait.** The
  framework's `SolverBackend` is one-shot and `Solver<B>` currently resubmits
  complete snapshots, while `IncrementalBvSolver` genuinely retains AIG, CNF,
  SAT, learned, scope, and replay state. Commit `1058cf84` adds the always-
  exported object-safe `IncrementalSolver` trait for raw assert/push/pop/check/
  check-assuming and implements it only for that real retained session. Generic
  and trait-object lifecycle tests, the existing warm suite, strict Clippy, and
  warning-denied rustdoc pass under full and dependency-minimal `qfbv` profiles.
  Arena handles stay lifetime-free, exclusive mutation and original replay are
  preserved, and configured preprocessing/concrete stats stay outside the
  general contract. Glaurung ADR-011/`8d8cd6f` now lands the matching object-
  safe IR-level session plus a direct-delta Axeyum implementation: each assert
  translates only the new root, and scope-local symbol maps prevent popped or
  temporary values leaking into later models. All 37 backend tests pass. The
  explorer wiring is now downstream in `f5a3b7a`; real-stream measurement and
  admission remain next.

- **2026-07-16 — ADR-0200 defers open-addressed primary CNF ownership.** The
  isolated table is semantically and structurally exact: all focused/CNF/proof
  gates pass, and every one of ten representative processes decides 162/162
  with 88 SAT, 74 UNSAT, zero errors/disagreements/replay failures, and
  identical AIG/clause counters. Performance rejects it. Candidate mean/p50
  CNF time regress 8.55%/7.52%, and mean/p50 total time regress 3.67%/3.87%.
  The full tier is unnecessary; `90e298f2` restores `std::HashMap`. Do not
  transfer ADR-0175's AIG-table result by analogy. Re-attribute a larger cold
  CNF subphase or encoding hypothesis before another GQ5 implementation.

- **2026-07-16 — ADR-0199 accepts serial DFS sibling warm leasing.** The
  immutable-prefix audit finds no cheap snapshot seam: the arena/AIG can clone,
  but incremental CNF owns opaque BatSat state, so a fork artifact would still
  copy encoder maps and reinsert clauses under a new replay/invalidation
  contract. Glaurung siblings are already serialized by one LIFO worklist, and
  the snapshot adapter already performs exact LCP/pop/push transitions.
  accepted reference-counted continuation lease permits only the popped state
  to mutate the owner: never concurrent access, never verdict-only reuse,
  complete snapshots and original replay on every check, and zero reference/
  session/cache gauges on every exit. Four focused serial tests and all 36
  backend tests pass. The diagnostic profile cuts created sessions 79.2%, AIG
  nodes 88.0%, clauses 77.0%, bit blast 82.4%, CNF 66.8%, and internal total
  15.2%; retained SAT rises 36.2% and becomes 47.2% of candidate time.

  The clean adaptive/cache-on artifact preserves all 185,442 decisions,
  findings, exact warm/cache/lease traffic, and original replay with zero
  failures. SurfacePen time/ratio improve 17.08%/18.53% and RSS falls 6.11%,
  with +1.79% Z3 drift. NETwtw10 improves 0.72%/0.35% and RSS falls 13.36%,
  with -0.37% Z3 drift. Every alarm passes. Glaurung `f17dc08` defaults serial
  reuse on only under adaptive warm policy; explicit off restores ADR-0196.
  Parallel workers must retain independent owners and revalidate this premise.

- **2026-07-16 — Latest Glaurung feedback resets the next engineering order.**
  Cold one-shot remains the pure-solver gap: about 84% bit blast plus CNF and
  only about 15% SAT, so cold CNF encoding leads. Warm amortization is already
  decisive and ADR-0199 makes it faster and lower-RSS on current families.
  Next: (1) cold CNF ownership/emission; (2) first-class incremental
  push/pop/assume `Solver` API and explicit `assert_configured` warm-only docs;
  (3) widen repeated realworld drivers; (4) stronger replay-checked SAT-model
  subsumption; (5) independent-owner parallel exploration; and (6) causal
  large-BV preprocessing. GQ4 slicing stays off. Strict sort checking, precise
  `IrError`, scalar lean model lift, shared replay memo, DRAT recheck, QF_BV-only
  features, `coerce_to`, and `Value` re-export remain accepted strengths.

- **2026-07-16 — ADR-0198 rejects a three-owner adaptive initial cap.** The
  post-ADR-0196 SurfacePen no-fallback ceiling has the exact behavior an
  initial-three candidate would select: 207 created/closed owners, peak three,
  and zero fallbacks or terminal state. Three order-balanced runs preserve all
  15,306 decisions and findings. Mean Axeyum time improves 436.733→412.733 ms
  (-5.50%) and ratio 6.30%, with +0.86% Z3 drift, but median RSS rises
  78,708→84,736 KiB (+7.66%) and fails the 5% alarm. Keep the initial cap at two
  and do not implement the knob; next require immutable prefix construction
  reuse that cannot retain or share a third mutable solver.

- **2026-07-16 — ADR-0197 accepts unsplit adaptive warm/fallback attribution.**
  The accepted production policy deliberately mixes retained warm checks with
  bounded one-shot fallbacks, so the homogeneous warm summarizer correctly
  rejected its profile. The new separate fail-closed tool validates every
  record with the existing schema-specific validator, preserves global process/
  sequence order, requires both current warm v6 and native v1, normalizes only
  compatible phases, and keeps retained, created-owner, and fallback structures
  separate. Ten focused tests and all 51 script tests pass with Ruff clean.

  The real SurfacePen default has 2,535 warm plus 16 fallback records, all
  decided across the exact 2,551-check stream. Its 509.677 ms internal residual
  is SAT 28.01%, CNF 21.39%, translation 14.77%, bit blast 14.31%, replay
  11.19%, unattributed 8.11%, and setup 0.16%. Fallbacks are 0.63% of checks but
  6.02% of time. Among warm records, 207 created owners retain 78.4% of bit
  blast, 70.7% of CNF, 87.3% of new AIG nodes, and 77.6% of new clauses;
  retained owners own 94.7% of warm SAT, 90.2% of translation, and 94.3% of
  replay. Next test a bounded fresh-sibling/fallback prefix or admission lever;
  treat retained SAT as a separate identical-CNF GQ6 experiment.

- **2026-07-16 — ADR-0196 accepts LIFO-aligned exclusive fork-owner transfer.**
  Fresh post-ADR-0195 attribution showed 358 path-creation checks (14.0%)
  consuming 82.2% of CNF time, 89.0% of bit-blast time, 88.0% of added clauses,
  and 89.7% of root encodings. A first implementation transferred the terminal
  parent's retained solver to the earlier fork child. Although an isolated
  lineage profile showed less construction, that owner idled behind the
  sibling subtree, increased adaptive pressure, exceeded SurfacePen's RSS
  alarm, and regressed NETwtw10 Axeyum time about 9.4%; it was reverted.

  The accepted implementation instead transfers the owner only to the
  last-pushed child that Glaurung's DFS worklist executes next. The sibling is
  fresh, mutable solver/cache state is never shared, and the parent swaps to an
  unused fresh ID so ordinary cleanup cannot close the transferred solver. The
  clean adaptive/cache-on comparison preserves all 185,442 decisions,
  findings, exact transfer/cache traffic, terminal cleanup, and original replay
  with zero replay failures. SurfacePen mean Axeyum time/ratio improve
  14.71%/15.04%, with +0.76% median RSS and +0.39% Z3 drift; NETwtw10 improves
  34.77%/34.36%, with -0.36% RSS and -0.62% Z3 drift. Every alarm passes.
  Glaurung defaults transfer on with an explicit fail-closed off control; next
  re-profile the accepted current state and select the remaining causal GQ7/GQ5
  cost rather than revisiting unconditional slicing or non-firing rewrites.

- **2026-07-16 — ADR-0195 accepts the empty warm-theory projection bypass.**
  After constructing the same complete deterministic public model, scalar
  QF_BV checks now return it directly only when every active and one-shot array/
  UF projection class is empty. Any array select, scalar or array-valued UF
  app, array equality, or relation flag takes the unchanged full path. AIG
  validation, default completion, cache replay, and every original-root replay
  remain mandatory.

  The exact v6 SurfacePen candidate keeps all 2,551 checks decided/agreed with
  identical AIG/CNF, models, path/cache traffic, and zero replay failures.
  Completion falls 165.192→1.088 ms (-99.34%), model lift
  175.049→10.379 ms (-94.07%), and profiled internal total falls 20.52%. The
  same-current unprofiled three-process gate improves median Axeyum
  636.6→474.6 ms (-25.45%) and ratio about 0.147x→0.108x Z3 while median RSS
  falls 0.06% and Z3 drift stays at +1.19%. All 15,306 combined checks agree.
  Held-out NETwtw10 repetition also passes: median Axeyum
  17,765.2→16,996.6 ms (-4.33%), ratio about 0.342x→0.328x (-3.99%), and RSS
  falls 1.39% with -0.36% Z3 drift. All 170,136 combined checks agree, findings
  and exact traffic repeat, and replay failures remain zero.

  The clean machine-readable adaptive/cache-on refresh now closes the
  production-policy gate over another 185,442 checks. SurfacePen mean Axeyum
  time/ratio improve 23.82%/24.99%; NETwtw10 improve 3.55%/4.04%. Median RSS
  changes only +1.13%/+0.97%, absolute Z3 drift is 1.56%/0.52%, and exact
  findings, traffic, cleanup, and all alarms pass. Baseline/candidate artifact
  SHA-256 values are `21b95227...1f7c07` / `9ac47b7c...f015d`. The current
  highest-leverage implementation question returns to fresh residual native
  attribution; do not infer another model-lift or CNF change from the old v5
  balance.

- **2026-07-16 — ADR-0194 measures model completion as the residual.** The
  exact Glaurung v6 SurfacePen run decides and agrees on all 2,551 checks
  (2,282 SAT / 269 UNSAT), with zero unknown splits or replay failures. Of
  175.049 ms in `model_lift`, complete-model construction consumes 165.192 ms
  (94.37%), assignment reconstruction/validation 7.146 ms (4.08%), and
  retained-AIG recomputation 2.427 ms (1.39%). Exactly 5,066 reconstructed
  symbols become 5,066 completed public values. This rejects duplicate AIG
  traversal as the next lever.

  Source inspection finds that warm completion unconditionally traverses every
  active original assertion to discover user array selects even when all
  active and one-shot array/UF projection sets are empty. Next specify, test,
  and causally gate an exact scalar-QF_BV fast path that skips only this empty
  warm-theory projection pipeline. It must still default-complete every user
  symbol and replay every original root; validation and complete-model output
  remain mandatory.

- **2026-07-16 — ADR-0193 accepts bounded shared-memo original replay.** The
  v5 cache-aware SurfacePen profile finds mandatory original-term replay at
  447.046 ms / 38.82% because incremental replay rebuilt an evaluator memo for
  every root. Axeyum `d3d95299` now uses the same trusted `eval_with_memo`
  under one immutable assignment, clears accumulated cross-root values at a
  fixed 4,096-entry threshold, and never retains trusted values across a
  model, check, solver, arena, or thread.

  The identical 2,551-check profile remains fully decided/agreed with zero
  replay failures while replay falls 87.78% to 54.643 ms and attributed total
  falls 33.51%. A same-current-client three-process causal gate improves
  SurfacePen Axeyum 1,070.267→674.933 ms (-36.94%), ratio 0.243795→0.154875,
  and median RSS 78,888→77,976 KiB (-1.16%) with -0.73% Z3 drift; every alarm
  passes. A clean-Axeyum six-process candidate keeps all 92,721 checks green,
  measures SurfacePen at 674.700 ms / 0.155x Z3 and NETwtw10 at 17.328 s /
  0.333x Z3, and improves NETwtw10 against the committed artifact. The older
  SurfacePen artifact fails its RSS alarm (+6.52%) despite the causal pair
  proving the patch lowers RSS, so do not relabel it: refresh a clean
  same-current two-driver baseline/candidate before publishing a replacement.
  Then attribute model-lift operations versus replay-required symbols; CNF is
  the parallel measured lane.

- **2026-07-16 — ADR-0192 accepts Glaurung's bounded path-owned cache default.**
  Clean adaptive cache-off/cache-on artifacts execute 92,721 checks per policy
  across three SurfacePen and three NETwtw10 processes. All 185,442 combined
  checks agree with Z3, unknown splits and replay failures are zero, exact warm
  and cache traffic repeats, and findings are identical. Cache-on improves
  Axeyum time 1.16%/2.38%, ratio 0.67%/2.08%, and median RSS 6.88%/1.52%, with
  absolute Z3 drift below 0.50%; every ordinary alarm passes.

  Glaurung `e177142` maps unset to the measured 64-entry / 4,096-value /
  262,144-bit policy only for path-owned warm sessions and retains explicit
  off, one-shot fallback, terminal cleanup, and complete counters. Axeyum's
  generic incremental cache remains disabled by default. GQ8 is done for
  available Glaurung families; next obtain fresh native attribution before a
  bounded GQ5/GQ6 experiment and re-gate any new family.

- **2026-07-16 — ADR-0191 lands Glaurung's GQ8 measurement control.** Glaurung
  `d5475f6` wires ADR-0190 only into independently path-owned warm solvers;
  snapshot and one-shot fallbacks remain cache-free, and the accepted adaptive
  production default remains cache-off. Fixed 64-entry / 4,096-value /
  262,144-bit per-path bounds and all Axeyum cache counters enter the lineage
  footer and fail-closed artifact validator. The named comparator permits only
  off→on with otherwise exact policy/work/finding identity.

  A dirty single-process SurfacePen plumbing smoke decides/agrees 2,551/2,551,
  preserves findings, and records 183 hits / 2,368 misses / 2,099 insertions /
  269 declined UNSAT / 832 evictions, with zero replay failures and zero
  terminal gauges. This is not performance evidence: Z3 drift is 3.33% and
  there is no repetition. Next run clean repeated SurfacePen + NETwtw10 off/on
  artifacts under the ordinary 3%/3%/5% + 2% alarms before any default decision.

- **2026-07-16 — ADR-0190 implements the opt-in GQ8 SAT cache.** Each
  arena-bound incremental solver may explicitly enable caller-supplied entry
  model-value, and payload-bit bounds. Exact original assertion order, every frame boundary,
  and assumption order are compared directly; deterministic LRU eviction is
  total and bounded. Hits return only after original-term replay. Ordinary
  UNSAT/Unknown/oversized results are counted but never inserted, and replay
  corruption is evicted and fails closed. Full/minimal focused tests,
  all-feature Clippy, links/format, and 876/876 all-feature library tests pass.
  The cache-disabled corrected Glaurung raw/canonical gate remains 162/162
  decided/agreed with zero errors, unknowns, or replay failures. Next wire an
  explicit cache-off/cache-on Glaurung ordered control and gate
  exact traffic, models/findings, latency, total time, and RSS before any
  default.

- **2026-07-16 — ADR-0189 accepts the GQ8 replay boundary.** The first
  verdict cache is explicit/off, per arena-bound `IncrementalBvSolver`, and
  scalar-SAT-only. Exact ordered active assertions, scope boundaries, and
  one-shot assumptions are collision-checked identity; every hit runs the existing original-term
  model replay. Ordinary UNSAT, `Unknown`, errors, assumption cores, and strict
  prefixes are not cache entries. UNSAT waits for source-bound proof recheck;
  prefixes remain GQ7 retained-state reuse. Next implement deterministic
  entry/model-value bounds, eviction, invalidation, and telemetry, then test
  and measure the ordered same-lineage duplicate population before any client
  default.

- **2026-07-16 — ADR-0188 accepts corrected full-shard variance and alarms.**
  A second identical clean `f7f174c5` raw/canonical composite repeats all
  30,628 queries and deterministic construction. Across two complete sets,
  raw Axeyum/Z3/ratio CV is 0.458%/0.558%/0.100%; canonical is
  0.787%/0.150%/0.937%, and canonical maximum-child-RSS CV is 0.039%.

  New fail-closed repetition and cross-commit tools recompute source
  composites, reject identity/work drift within a revision, permit only a
  different clean source plus measured construction changes across revisions,
  and apply explicit 3% Axeyum / 3% ratio / 5% RSS / 2% Z3 alarms. All 46
  infrastructure tests pass. GQ1/GQ10 are complete for current families. Next
  specify GQ8's replay-safe bounded cache and obtain fresh causal canonical
  attribution before choosing any GQ5/GQ6 implementation; keep GQ4 off.

- **2026-07-16 — ADR-0187 accepts the corrected wide Glaurung cold corpus.**
  Glaurung producer `1b32cb9` plus strict builder `3b64aaf` capture 30,678
  observations / 30,628 distinct scripts across five drivers with 50 duplicate
  observations, zero verdict conflicts, and zero exclusions. The current
  corpus contains 7,953 scripts with wide roots and 13,015 width-64 assertion
  roots; the 2,225 old malformed hashes are stale and cannot be mapped to
  current corrected bytes.

  Four deterministic physical shards form one exact full tier. Eight clean
  Axeyum `f7f174c5` processes decide/replay 30,628/30,628 under both policies
  with zero errors, unknowns, disagreements, oracle gaps, replay failures, or
  rewrite decision changes. Raw is 30.803 seconds versus Z3's 69.127 (0.446x);
  canonical v4 is 18.471 versus 68.556 (0.269x), cuts AIG nodes
  68.16M→32.35M and clauses 72.70M→32.12M, and stays below 1.42 GiB child RSS.
  The corrected 162-query representative is now pinned in the regular gate.
  Repeat the complete shard composite before setting variance alarms, then use
  fresh canonical-stage attribution to choose GQ5/GQ6 or specify GQ8's
  replay-safe cache; keep GQ4 off.

- **2026-07-16 — ADR-0186 accepts pressure-adaptive admission as Glaurung's
  Axeyum explorer default.** The clean Glaurung `f99f72b` / Axeyum `f91fb232`
  artifact repeats all 92,721 agreements and exact adaptive counters. Against
  fixed lineage, SurfacePen changes +2.07% Axeyum / +2.28% ratio / -3.65% RSS;
  NETwtw10 changes -1.03% / -0.89% / -0.88%; Z3 drift is below 0.21%. Every
  3%/3%/5% plus 2% alarm passes.

  Glaurung `ca12028` makes adaptive the default only for Axeyum explorer calls
  with path ownership. `off`/`false`/`0` restores one-shot; generic Axeyum APIs
  and proof/model semantics are unchanged. Real unset/off SurfacePen runs both
  agree 2,551/2,551; backend 28/28 and runner 9/9 pass. GQ9 is complete for
  available families. Next regenerate ADR-0184's corrected cold corpus.

- **2026-07-16 — ADR-0185 lands pressure-adaptive warm admission as an opt-in
  repeat candidate.** Glaurung `95c43cb` starts lineage at two live sessions
  and expands once to the configured cap nine after 128 failed low-cap
  reservations. Purpose admission (1.140 s / 72,868 KiB), fixed cap 1, fixed
  cap 2 on NETwtw10 (+18.2% time), and cap 3 (no RSS gain) are rejected.

  Adaptive single-process calibrations clear the existing alarms: SurfacePen
  is +1.55% Axeyum / -2.41% RSS versus same-binary cap 9 and does not expand;
  NETwtw10 is -1.05% Axeyum / +1.11% RSS and expands exactly once. All 30,907
  checks agree with zero unknown splits/resets. The fail-closed runner now
  versions exact adaptive pressure/traffic; 27 backend and eight runner tests
  pass. Default remains off pending a clean three-process-per-family repeat.

- **2026-07-16 — ADR-0184 corrects Glaurung assertion export identity.**
  Glaurung `fcc2de5` makes text, ordered trace, native Z3, and native Axeyum
  agree on arbitrary-width truthiness (`true => term != 0@width`, false =>
  zero). The corrected real SurfacePen trace validates 12,574 events and all
  2,551 checks instead of failing at the first 64-bit root.

  Axeyum's strict sort checker was correct; the producer was not. The 2,225
  formerly excluded scripts are likely recoverable, and all expected-true query
  hashes change, so the old 128/13,462 cold tiers are historical until
  regenerated. Warm native verdict/work gates remain separate but must be
  rerun, not assumed.

- **2026-07-16 — ADR-0183 defers detected-reuse as the default.** The clean
  three-by-two auto artifact repeats all 92,721 agreements and exact topology
  counters. SurfacePen/NETwtw10 save 20.66%/15.93% median RSS but regress
  Axeyum time 7.37%/4.28%, failing ADR-0180's 3% alarm. Z3 drift is also outside
  2%, so normalized cross-run ratios are not causal evidence.

  Glaurung `ab3b27b` commits the byte-exact artifact. Auto remains an explicit
  low-memory option; fixed lineage remains the faster opt-in; default stays
  off. Next GQ9 work must avoid the second-check cold rebuild while declining
  only paths whose topology predicts no future checks. GQ4/GQ8 are unchanged.

- **2026-07-16 — ADR-0182 lands GQ9's detected-reuse candidate opt-in.**
  Glaurung `4ae5469` keeps the first path check one-shot with only an ID probe
  and promotes on the second same-live-path solve into the existing bounded
  lineage adapter. SurfacePen and fixed-budget NETwtw10 stay 100% agreed with
  exact finding/work partitions. Auto trades 4.5--8.7% Axeyum time for 16--21%
  lower RSS than lineage while preserving much of the cold-to-warm gain.

  All 24 backend tests, release build, and default Clippy pass (the repository's
  pre-existing strict-warning debt remains). Next extend the clean runner with
  auto policy/probe identity and repeat both families. Default remains off;
  GQ4/GQ8 and formal replay/proof boundaries are unchanged.

- **2026-07-16 — ADR-0181 publishes the clean lineage baseline.** Glaurung
  `51666a9` commits the exact atomic six-process artifact produced from clean
  detached Glaurung `a0e5f9f` and Axeyum `486b7e28` sources. Both dirty-path
  arrays are empty. All 92,721 checks agree with Z3 with zero unknown splits;
  SurfacePen is 1.063/4.395 seconds (0.242x, 82,432 KiB median RSS), and
  fixed-budget NETwtw10 is 18.751/52.149 seconds (0.360x, 257,632 KiB).

  The committed 7,986-byte JSON is byte-identical to the runner output and
  passes standalone validation and comparison. Four focused tests, Python
  compilation, Ruff lint/format, and whitespace validation pass. The clean
  prerequisite is closed; begin GQ9 detected-reuse topology/cost fitting
  against fixed off and lineage controls. Warm remains opt-in, GQ4 stays off,
  and GQ8 cache/replay authorization is unchanged.

- **2026-07-15 — ADR-0180 lands held-out lineage regression alarms.** Glaurung
  `a0e5f9f` fails homogeneous comparisons above 3% Axeyum mean, 3% normalized
  ratio, 5% median RSS, or 2% absolute Z3 drift. Time/ratio/RSS are one-sided;
  Z3 drift is absolute. All thresholds are explicit options applied only after
  exact identity, work, finding, correctness, and lifecycle validation.

  ADR-0178's Axeyum CV is 0.34%/0.44%; the thresholds sit well beyond measured
  noise while keeping RSS first-class. Four focused tests, Ruff/compilation,
  and real-artifact self-compare pass. Next publish a clean full baseline, then
  begin GQ9 topology/cost fitting. The dirty one-run smoke is not release data.

- **2026-07-15 — ADR-0179 lands the fail-closed held-out lineage artifact.**
  Glaurung `89aea59` adds `glaurung-axeyum-lineage-gate-v1`: it records both
  revisions/dirty paths, binary and driver hashes, platform/Rust identity,
  policy/resource limits, exact traffic, finding hashes, time, and RSS. Dirty
  trees fail unless exploratory, every child receives a hard 4 GiB limit, and
  JSON publishes atomically only after agreement/unknown/finding/lifecycle/
  fallback/work invariants pass. Comparison permits source/binary changes but
  rejects system, policy, driver, work, finding, or repetition drift.

  Three parser/invariant tests pass, covering exact footer/time extraction,
  accepted summaries, and structural-drift rejection. Python compilation and
  Ruff format/lint are green. A real SurfacePen one-run smoke produces,
  validates, and self-compares the artifact: 2,551/2,551 agreed, zero
  fallbacks/resets, Axeyum 1.067 seconds versus Z3 4.429, and zero self-delta.
  This is a plumbing smoke; ADR-0178 remains the repeated performance evidence.

  Next publish a clean full artifact and add explicit same-environment Axeyum,
  normalized-ratio, and median-RSS alarms. Then fit GQ9's topology/cost selector.
  Lineage remains opt-in; GQ8 cache and formal replay/proof boundaries are
  unchanged.

- **2026-07-15 — ADR-0178 accepts repeated exact-work held-out lineage
  variance.** Three SurfacePen default-policy processes execute identical
  2,551-check streams and lifecycle/root counters with zero fallbacks/resets;
  all 7,653 occurrences agree. Mean Axeyum/Z3 is 1.069/4.409 seconds (0.243x),
  Axeyum population CV is 0.34%, and median RSS is 83,140 KiB.

  A wall-deadline NETwtw10 repeat produces a different query count, so it is
  explicitly diagnostic rather than variance evidence. The accepted tier uses
  `IOCTLANCE_SOLVE_BUDGET=20000`, a 400-second analysis deadline, 600-second
  solver budget, and hard 4 GiB cap. Three processes each execute exactly
  28,356 checks with identical 20,031 retained checks, 1,285 exact snapshots,
  529,071 prefix roots, 247,311 added roots, 2,228 pops, 5,961 created/closed
  sessions, peak nine, 8,325 path fallbacks, zero assertion fallbacks/resets,
  and all 85,068 occurrences agreed. Mean Axeyum/Z3 is 18.771/52.086 seconds
  (0.360x), Axeyum population CV is 0.44%, and median RSS is 257,736 KiB.

  Glaurung `eb938ae` records the exact-work recipe and bars. Every available
  realworld query stream now has repeated evidence for explicit 9/512 lineage;
  pciidex issues no solver checks. Next automate fail-closed per-commit source,
  environment, work, fallback, RSS, and timing comparison. Automatic GQ9
  selection and GQ8 caching remain separate, unauthorized decisions.

- **2026-07-15 — ADR-0177 widens the opt-in assertion envelope after GQ10
  held-out evidence.** SurfacePen's exact 2,551-record v4 profile has assertion
  min/p50/p90/p95/p99/max 0/52/352/416/467/479. ADR-0176's 128 ceiling sends
  965 checks one-shot; 256 still sends 446. At 512, all checks stay warm and
  Axeyum improves 1.633→1.063 seconds (-34.9%) with 83,340 KiB RSS, matching
  the effectively unbounded control's traffic, 1.064 seconds, and 83,332 KiB.
  Every policy remains 2,551/2,551 agreed.

  The hard-4-GiB, 60-second NETwtw10 stress stream decides and agrees
  23,797/23,797 checks with zero assertion fallback at 512. Nine live sessions
  fall back 8,325 checks, measure Axeyum 16.840 seconds versus Z3 47.613, and
  peak at 257,280 KiB RSS. Cap 12 recovers only 417 checks and 1.5% Axeyum time
  while RSS rises to 267,232 KiB. Thus nine remains the conservative
  live-session tradeoff; only the assertion ceiling changes.

  Glaurung `90df708` now defaults explicitly selected lineage mode to 9/512.
  Its unset-limit SurfacePen smoke is 2,551/2,551 agreed, zero fallbacks,
  Axeyum 1.064 seconds versus Z3 4.365, and 83,140 KiB RSS. All six available
  realworld samples have now been exercised (pciidex issues no solver checks),
  but held-out variance is not yet repeated. Repeat SurfacePen/NETwtw10 next;
  automatic GQ9 selection and GQ8 caching remain unauthorized.

- **2026-07-15 — ADR-0176 accepts bounded admission inside opt-in Glaurung
  lineage reuse.** The accepted v4 profile shows assertion maxima of 123/78/51
  and live-path peaks of 11/5/11 on vwififlt, Dptf, and IntcSST. A coarse
  sweep rejects cap 4, shows cap 12 is an unbounded-equivalent no-op, and
  selects 9 as the live-session knee; 128 assertions covers every established
  occurrence without fallback.

  Three order-balanced cap-9/cap-12 rounds decide and agree 20,958/20,958
  checks per policy with zero assertion fallbacks, resets, unknown splits, or
  finding changes. Weighted mean Axeyum time is 5.088 versus 5.091 seconds.
  Median RSS falls 125,812 versus 136,804 KiB (-8.0%) on vwififlt and 120,076
  versus 128,164 KiB (-6.3%) on IntcSST; Dptf is flat. Cap 9 falls back 45,
  zero, and four checks per run respectively. The largest observed RSS falls
  137,968→126,860 KiB.

  Glaurung `1f24d5d` makes 9 live paths/128 assertions the visible defaults
  only after `GLAURUNG_AXEYUM_WARM_REUSE=lineage` is explicitly selected.
  Over-limit work remains one-shot; invalid overrides fail closed; the footer
  reports both limits and fallback reasons. A fresh unset-limit vwififlt smoke
  is 4,753/4,753 agreed with 45/0 fallbacks and Axeyum 4.477 seconds versus Z3
  4.555. This closes the first memory gate, not GQ9 automatic selection or GQ8
  caching. Widen GQ10 next and revalidate topology, fallback, RSS, and time.

- **2026-07-15 — ADR-0175 accepts deterministic open-addressed AIG structural
  hashing and moves the native lineage ratio to 0.680x Z3.** Glaurung `d79010a`
  and Axeyum `17f7747f` advance the opt-in warm profile to v4: every primitive
  AND request is classified, and profiling-only lowerer counters expose memo
  lookup/reuse, operand/root literal copies, term-bit writes, and symbol inputs.
  The fail-closed summarizer accepts historical v1--v3 but requires the exact
  v4 field sets and allocation/partition invariants.

  Dptf's 561-check control adds 284,870 AIG nodes in 40.989 ms. Of 786,558 AND
  requests, 57.25% simplify trivially, 3.14% by absorption, 4.45% hit the
  structural table, and 35.16% create a node. Thus 39.61% reach the old
  `BTreeMap`, and 88.77% of those probes insert. Lowering copies/writes 3.24
  literals per added node. The isolated deterministic 70%-load open-addressed
  table preserves every outcome/AIG/CNF/gate/work counter and cuts profiled
  Dptf bit blast 40.989→26.196 ms (-36.09%).

  Five order-balanced Dptf pairs improve unprofiled Axeyum mean 238.36→224.10
  ms (-5.98%). The wider acceptance gate runs three balanced pairs on each of
  the established drivers: both policies decide and agree 20,958/20,958 checks
  with identical path/root traffic and no fallbacks/resets. Per-driver Axeyum
  means improve 7.95% `vwififlt`, 6.32% Dptf, and 5.15% IntcSST. The weighted
  three-driver round falls 5.487→5.067 seconds (-7.66%); actual-client ratio
  improves 0.742x→0.680x (-8.34%). Median RSS changes -1.27%, -2.62%, and
  +0.41%, respectively.

  The accepted-table v4 rerun validates all 6,986 records, 8,758,247 AIG nodes,
  and 11,734,335 clauses. Profiled bit blast falls to 1.221 seconds / 18.21%;
  CNF is again dominant at 46.55%, with SAT at 18.48%. Next calibrate GQ7
  capacity/memory admission on this faster baseline and widen GQ10 drivers.
  Internal AND flattening remains deferred, GQ4 stays off, and literal-copy
  ownership requires a fresh isolated gate before reopening.

- **2026-07-15 — ADR-0174 defers bounded internal positive-AND flattening and
  moves GQ5 to AIG per-node attribution.** The exact implication replacement is
  semantically green, bounded to 64 fresh nodes, off by default, and replay-safe
  under later opposite-polarity reuse. Glaurung `74c7759` exposes it only via
  `GLAURUNG_AXEYUM_INTERNAL_AND_FLATTENING=1`; warm schema v3 distinguishes
  opportunities, applied halves, and immediate primitive clauses avoided.

  The 561-check Dptf gate rejects it cleanly. The candidate applies 2,597
  flattenings over 86,141 opportunity nodes and avoids 83,544 clauses at the
  moment of application, but later helper reuse grows cumulative clauses from
  429,432 to 505,090 (+17.62%) and profiled CNF time from 119.805 to 129.616 ms
  (+8.19%). Three alternating unprofiled runs remain 561/561 agreed with
  identical path/root traffic, while Axeyum mean regresses 239.5→248.3 ms
  (+3.65%). A full three-driver run is neither necessary nor authorizing after
  both required gates fail.

  Keep the explicit option off and stop tuning freshness/node thresholds: the
  missing information is future sharing in a monotone growing AIG. Reopen only
  with retained-future-use evidence or a clause replacement mechanism. Next
  attribute structural-hash lookup/reuse, node allocation/copy, and lowering
  bookkeeping per added AIG node. SAT remains third; GQ4 remains off.

- **2026-07-15 — ADR-0173 accepts exact native-lineage CNF gate/root
  attribution and selects one bounded internal AND-tree experiment.** Glaurung
  `21c01ce` advances the opt-in warm schema to v2 and attaches all 38 existing
  `IncrementalCnfStats` deltas to every exact query/path record. Axeyum's
  summarizer accepts historical v1, fails closed on the complete v2 field set
  and shape/fusion invariants, and aggregates gate totals only for a homogeneous
  v2 stream.

  The three-driver rerun remains 6,986/6,986 decided and agreed, with 2,103
  paths closed and zero fallbacks, resets, deadline hits, disagreements, or
  unknown splits. The 11,734,335 added clauses partition into 8,419,041
  definitions (71.75%), 3,313,208 guarded roots (28.24%), and 2,086 constants.
  AND-tree shapes own 3,070,411/5,697,696 definition halves (53.89%), followed
  by inverted-AND 25.50%, XOR 12.37%, and binary AND 8.24%. Every measured
  positive-root opportunity already takes ADR-0162's fusion path; all
  definition/root duplicate and tautology counters are zero.

  Reject another root-fusion or dedup tranche. Next implement one exact,
  future-reuse-safe positive internal AND-tree half flattening with explicit
  eligible/applied counters. Fewer clauses are necessary but not sufficient:
  acceptance still requires lower repeated, unprofiled, same-stream native
  time with identical decisions, replay, scopes, resources, root traffic, and
  findings. AIG per-node attribution follows; SAT remains third. GQ4 stays off.

- **2026-07-15 — ADR-0172 accepts exact native-lineage phase attribution and
  returns the implementation lead to measured CNF construction.** Glaurung
  `13f4bbe` selects Axeyum's profiling constructor only under the existing
  profile-directory opt-in and emits one exact query/path record per warm
  check. Ordinary warm solvers retain the zero-diagnostic constructor.

  Axeyum's new fail-closed summarizer accepts exactly 6,986/6,986 decided
  records across `vwififlt`, Dptf, and IntcSST: 5,102 unique hashes, 2,103 path
  sessions, 88,476 added roots, 8,758,247 added AIG nodes, and 11,734,335 added
  clauses. Every sequence/path/structure invariant and exact phase sum passes.

  Weighted internal shares are CNF 43.78%, bit blast 22.86%, SAT 17.45%, replay
  5.79%, translation 3.74%, model lift 3.41%, unattributed 2.70%, session create
  0.21%, and model extraction 0.04%. Profile clocks/output are expensive:
  7.106 seconds internal and 9.441 seconds at the client versus the unprofiled
  5.537-second median. Keep the 0.746x-Z3 unprofiled result authoritative.
  Next add causal warm gate/root-family deltas, then target the dominant CNF
  pattern under the unprofiled native gate; AIG is second and SAT third.

- **2026-07-15 — ADR-0171 accepts repeated native path-owned warm reuse as the
  leading opt-in GQ7 policy.** Glaurung `b9febbd`/`950cca4` gives every explorer
  path an independent retained arena/solver session; siblings never share
  mutable SAT state, terminal/restarted owners close explicitly, and solves
  without a path context fall back one-shot.

  Three alternating snapshot/lineage rounds across the same three drivers
  execute 20,958 checks per policy. All 41,916 combined occurrences agree with
  Z3, with zero unknown splits, warm resets, deadline hits, or finding changes.
  Weighted snapshot is 2.093x Z3; native lineage is 0.746x with 0.36% ratio CV,
  cuts Axeyum time 65.5%, and wins every driver. This closes the bounded native
  functionality/repetition gate, not default admission.

  Lineage's median RSS is higher on every driver: +31.0% `vwififlt`, +6.3%
  Dptf, and +15.8% IntcSST, with a 141,124 KiB observed peak. Next bound live
  sessions, inherited-prefix construction, memory, and deterministic fallback;
  then phase-profile translation/assert/model/SAT cost and widen the driver
  tier. GQ8 caching and GQ9 auto selection remain gated. Glaurung is downstream
  workload evidence, not Axeyum's formal-verification product architecture.

  Glaurung `49f1fe2` now adds the first explicit resource boundary required by
  that decision. Process-wide live-path and per-snapshot assertion caps reserve
  atomically, close over-limit retained owners, and route checks one-shot with
  visible fallback counters. Dptf cap-zero/cap-one smokes remain 561/561 agreed;
  cap one holds peak live paths at one and all runs finish at zero live paths.
  Capacity plumbing is complete, but limit calibration and a memory-based auto
  policy remain open.

- **2026-07-15 — ADR-0170 accepts the clean multi-driver ordered control and
  rejects a universal warm policy.** Clean Glaurung `dbdc6bf` traces preserve
  17,035 events, 1,225 paths, 1,081 assertions, 3,769 checks, 2,812 unique
  queries, 957 duplicate occurrences, and 1,502 model reads across
  `vwififlt`, Dptf, and IntcSST. Every check decides and all cold/snapshot/
  lineage occurrences agree and replay as 2,542 SAT / 1,227 UNSAT.

  Weighted same-stream ratios including arena construction are 1.591x Z3 for
  exact-byte cold, 1.049x for snapshot, and 0.698x for lineage. The aggregate
  hides a real reversal: snapshot is 0.974x on `vwififlt` but 1.225x/1.063x on
  Dptf/IntcSST; lineage is 1.458x on `vwififlt` but 0.689x/0.242x on the other
  two. Lineage replays 26,930 fork roots and peaks at 106.5 MB. Next carry
  native per-lineage/delta ownership through Glaurung's worker/path boundary,
  retain snapshot as the fixed comparator, and measure online topology/cost
  admission plus repeated variance. Warm remains opt-in; GQ8/GQ9 remain gated.

  The wider capture first found two downstream correctness defects, not Axeyum
  relaxations. Glaurung `57c6c09` forbids model-driven execution without SAT;
  `d450d2a` explicitly coerces extension children to their declared source
  width in the renderer and both adapters. The fail-closed trace validator and
  Axeyum's strict IR/parser were preserved. Glaurung is still an external
  corpus/integration client, not Axeyum's formal-verification architecture.

- **2026-07-15 — ADR-0169 completes one clean ordered T4 capture and
  dual-backend control.** Glaurung `497b1c6` persists all 180 asserted roots
  with sorted producer-declared symbols and separately times every same-query
  Z3/Axeyum call. Axeyum independently validates 3,280 events, 235 paths, 503
  unique queries, 776 checks, and 241 model reads; all three policies decide and
  replay 470 SAT / 306 UNSAT, with zero unmaterialized lineage assertions.

  The native Glaurung stream measures Axeyum/Z3 at 2.095/0.808 s (2.593x),
  confirming the real client bar. Exact-byte cold replay is 2.631 s. Snapshot
  replay plus shared-arena build is 0.476 s (0.590x Z3), 0.548/1.179 ms
  p50/p95, and 38.1 MB high-water RSS; naive lineage is 1.291 s (1.598x Z3),
  replays 7,378 fork roots, and reaches 88.7 MB. This proves bounded snapshot
  headroom but is not native integration. Depth telemetry is 45/46 buckets
  faster than Z3; the lone two-check depth-12 bucket is slower and every
  observed depth from 13 onward is faster. Repeat across drivers and carry
  snapshot reuse through Glaurung's client boundary before GQ8/GQ9 or default
  admission.

- **2026-07-15 — ADR-0166 accepts the independent ordered-trace T1/T2
  boundary; explicit warm replay is next.** Glaurung commits `7a11c29` and
  `32cabb0` add an opt-in, atomically published ordered trace plus a separate
  fail-closed producer validator. This is downstream corpus plumbing, not an
  Axeyum product dependency. The new `axeyum-bench` replayer independently
  treats the artifact as untrusted: it verifies all hashes and indexes,
  reconstructs lineage/scopes/depths/digests, strictly parses exact QF_BV
  bytes, re-solves unique queries with original-assertion model replay, and
  proves each unique exploration-driving expression/value constraint SAT.

  On the bounded real `win10-vwififlt.sys` trace, all 508 unique queries decide
  as 197 SAT / 311 UNSAT and match all 784 recorded occurrences. All 243 model
  choices are structurally consumed exactly once; their 158 unique exact
  constraints remain SAT. The stream has 276 duplicate occurrences (35.2%),
  156 same-lineage repeats, 271 prefix extensions adding 420 assertions, 348
  divergent-lineage checks, and maximum depth 45. This closes bounded T1/T2
  functionality only: the capture came from a development worktree and carries
  no clean multi-driver or performance claim. Immediate next action is T3:
  retain explicit solver state per lineage (with validated fork replay), then
  compare it to ADR-0164 snapshot inference on identical occurrences with
  p50/p95 latency, peak memory, replay, and break-even. GQ8 caching and GQ9
  admission stay downstream.

  The post-T2 4 GiB aggregate gate passed formatting, strict all-feature/
  all-target Clippy, every workspace test and doctest, warning-denied docs, the
  QF_BV profile, and all 31 Glaurung harness tests. It then found a packaging
  regression rather than a solver failure: the added trace replayer made
  unqualified `cargo run -p axeyum-bench` ambiguous. Commit `f6fcd81f` declares
  the established harness the package default binary. The repaired pinned gate
  is 128/128 decided under both policies with zero errors, disagreements, or
  replay failures (raw 1.222x and canonical 0.333x versus in-process Z3 in this
  run); foundational resources, generated rules-as-code drift, and links also
  pass. Keep these as semantic/regression evidence, not a replacement for the
  clean ordered multi-driver timing gate.

- **2026-07-15 — ADR-0165 contains the Lean-kernel P0.** Historical commit
  `2cb298e2` preserved a complete derivation that the trusted gate admitted as
  `theorem bad : False`. Commit `d26ad887` now implements Lean's exact
  syntactic-subsingleton criterion: provably non-`Prop`, empty, and valid
  singleton families retain a fresh motive universe; every other
  potentially-`Prop` recursor fixes its motive to `Sort 0` and omits that
  universe parameter. The complete old exploit is active and rejected by both
  inference and `add_declaration`; proof irrelevance remains intentional.

  The focused suite is 177 unit tests plus four active integration tests and
  doctests. It covers `False`/`True`/`And`/`Iff`/`Eq`, an exact exposed data
  index, and an accessibility-style recursive proof field positively; and
  `Or`/`Exists`, hidden data, nested-only index occurrence, multi-constructor
  `Prop`, and sort-polymorphic potentially-`Prop` families negatively. A
  generated 36-cell constructor/proof-field/data-field matrix guards the class.
  Commit `a10c8cde` pins Lean 4.30.0 and adds a mandatory CI job that renders
  real `True`/`Two` inductives, applies Lean's regenerated restricted recursor,
  and needs iota to check; the same command passes locally against the pinned
  binary. Full `Acc` is still outside the recursive-indexed fragment, so its
  direct-recursive proof-field boundary is tested without claiming that
  deferred capability. Commit `de249d48` also updates every downstream
  `Or.rec`/`Exists.rec` reconstruction site to the restricted universe arity.
  The complete serialized `just check` gate passes under the 4 GiB wrapper:
  format, strict workspace Clippy, all tests and doctests, warning-free docs,
  QF_BV profile checks, the pinned Glaurung regular corpus, foundational and
  rules-as-code generation/validation, and link checking. The regular 128-row
  Glaurung gate remains 100% decided with zero disagreements or replay
  failures; this run records raw/canonical ratios of 1.069x/0.346x against its
  in-process Z3 bar. Immediate next action: return the solver lane to Glaurung
  GQ7 ordered/multi-driver reuse while retaining broader external-kernel
  differential work in the assurance queue.

- **2026-07-15 — ADR-0164 accepts the first real GQ7 retained-state bridge,
  opt-in.** Glaurung commits `016935d`/`b09ec6b` adapt its complete one-shot
  assertion snapshots to one thread-local Axeyum arena and incremental solver.
  Structural Axeyum `TermId` prefixes—not Glaurung `ExprId`s, which can collide
  across cloned siblings—control per-root pop/assert deltas. Focused raw and
  delta-preprocessed tests cover exact, extending, shrinking, empty, and
  sibling-divergent snapshots; the colliding-sibling test is SAT at `x=5` on
  one branch and UNSAT on the other.

  Three alternating Z3-authoritative `win10-vwififlt.sys` pairs each preserve
  13,126/13,126 agreements, zero disagreements/unknown splits/warm resets, and
  identical findings. Median Axeyum time improves 17.784→9.426 seconds
  (-47.0%); median paired Axeyum/Z3 improves 2.648x→1.462x (-44.8%). Every warm
  run observes 5,609 consecutive exact snapshots, retains 679,870 prefix roots,
  adds 8,027, and pops 8,026. This is retained arena/AIG/CNF/SAT state, not a
  verdict cache; Axeyum still solves and replay-checks every SAT candidate.
  Warm remains off by default. Next validate the ordered worker/path/scope/model
  trace, compare explicit per-lineage state with snapshot inference, repeat
  across drivers, and publish p50/p95/memory/break-even before GQ9 admission.

- **2026-07-15 — the latest ten-item Glaurung queue supersedes the cold-path
  tuning order.** The controlling sequence in `PLAN.md` is now explicit:
  (1) wire and measure GQ7 on the ordered/prefix stream; (2) partition and
  remove the reported approximately 1.8x real-client/bench entry overhead with
  `check_profiled`; (3) reduce AIG construction cost per node while preserving
  client sharing; (4) continue only measured/native-gated CNF work; (5) use
  causal ablation to select Glaurung-relevant rewrites without globally deleting
  sound rules; (6) add replay-checked GQ8 duplicate/prefix reuse; (7) measure
  SAT-core/inprocessing tuning now that its reported share is about 20%; (8)
  ship a fixed-policy-compared, non-regressing GQ9 auto mode; (9) deepen GQ10
  with ordered lineage, more drivers, and full-tier variance; and (10) publish
  both the pre-parsed in-process Z3 bar and Glaurung's actual Z3 backend bar.
  GQ4 is out/off for this distribution. Highest leverage is GQ7, client entry
  attribution, and the dual real-client baseline. The immediate external input
  is the offered ordered/prefix capture; validate its small lineage/scope/model
  sample before scaling or designing cache capacity. The complete 4 GiB-capped
  `just check` gate is green without reproducing the prior OOM: workspace
  format/Clippy/tests/doctests/Rustdoc, QF_BV profile, 31 Glaurung harness tests,
  pinned capture, foundational resources, generated drift, and links all pass.
  The regular capture remains 128/128 decided and manifest/Z3-agreed with zero
  errors/disagreements/replay failures; this run measures raw/canonical at
  1.222x/0.342x.

- **2026-07-15 — ADR-0163 accepts exact incremental root-context
  deduplication and closes the large GQ5 clause residual.** New opt-in
  attribution separates root contexts, selectors, payload widths, exact
  definition/root duplicates, root-vs-non-root overlap, tautologies, and
  fresh/reused negative-root definitions without taxing ordinary constructors.
  The pinned representative profile remains 128/128 decided and
  manifest/Z3-agreed with zero errors, disagreements, or replay failures. It
  finds no guarded roots in this fresh cold pack; 1,981 repeated exact
  root/selector contexts account for 56,750 clauses. The accepted default key
  skips only those contexts after synchronizing the growing AIG, retains
  different selectors as distinct, and records a context only after successful
  encoding.

  AIG size remains 450,498 while incremental clauses fall
  615,537→558,787 (-9.22%); the residual over same-revision one-shot falls from
  69,632 (+12.75%) to 12,882 (+2.36%). Two interleaved native pairs against
  Glaurung `f56ffa8` each preserve 13,126/13,126 agreements, zero unknowns, and
  identical findings. Mean Axeyum time improves 17.697→17.325 seconds (-2.10%);
  mean per-run Axeyum/Z3 improves 2.789x→2.719x (-2.51%). A stronger exact
  per-root-clause index cut clauses to 550,900 but regressed native Axeyum
  2.16% and normalized ratio about 1.59%, so it was removed. GQ5 now yields to
  the GQ1 multi-driver publication boundary and GQ7 ordered warm-trace handoff;
  no further default fusion/dedup follows from the remaining small count alone.

- **2026-07-15 — ADR-0162 accepts selector-safe incremental direct-root fusion
  after structural and native Glaurung gates.** Positive AND assertions now
  flatten deterministically to selector-guarded conjunct clauses; structural
  XOR leaves use their exact two truth clauses. No global use count is assumed,
  and no bypassed definition is marked emitted, so a later opposite-polarity or
  differently scoped use still receives the ordinary unconditional lazy
  definition. Focused tests cover clause reduction, scoped XNORs, pop
  deactivation, and later opposite reuse; randomized QF_BV differential,
  symbolic-execution push/pop/assumption suites, and 34 SAT-BV replay tests are
  green. The complete 4 GiB-capped `just check` gate is green: format, strict
  workspace Clippy, all-feature tests and doctests, warning-denied Rustdoc,
  QF_BV profile, 31 Glaurung script tests, foundational resources, generated
  drift, and links. Its pinned regular gate is 128/128 decided and
  manifest-agreed with zero errors, disagreements, or replay failures; the
  observed raw/canonical ratios are 1.192x/0.349x.

  The pinned 128-query profile remains 100% decided and manifest/Z3-agreed with
  zero errors, disagreements, or replay failures. Its AIG remains 450,498 nodes.
  All 1,789 positive roots, 109,358 positive AND nodes, and 90,149 XOR leaves
  take the bounded path; incremental clauses fall 782,716→615,537 (-167,179,
  -21.36%). The remaining same-revision one-shot gap is 69,632 clauses
  (+12.75%). The diagnostic ratio moves 1.272x→1.197x, but is not promoted as
  unprofiled evidence.

  The unprofiled gate uses isolated release builds of Axeyum baseline
  `aa8ec437` and the fused revision against Glaurung `f56ffa8`. Two alternating
  pairs each execute the identical 13,126-query Z3-authoritative
  `win10-vwififlt.sys` stream with 100% agreement and zero unknowns. Mean
  Axeyum time improves 18.484→17.648 seconds (-4.52%); mean Z3 time changes
  6.400→6.367 seconds (-0.52%); mean Axeyum/Z3 improves 2.888x→2.772x (-4.0%).
  GQ5 remains open: attribute the residual negative-root/inverted-AND and
  repeated guarded-root costs before another bounded fusion. GQ7 ordered warm
  lineage remains the structural route below the fresh-client floor.

- **2026-07-15 — ADR-0161 measures the incremental CNF gate mix and selects a
  bounded positive-AND/XOR fusion.** The explicit
  `incremental-bv-raw-profile` backend keeps production constructors unchanged
  while partitioning polarity-specific lazy definitions and scanning direct
  root opportunities only when profiling. Focused CNF/solver/benchmark tests
  and strict all-feature Clippy are green under the 4 GiB cap.

  The pinned 128-query representative Glaurung run is 100% decided and agrees
  with both manifest and in-process Z3 on every query, with zero errors,
  disagreements, or replay failures. It records the same 450,498 AIG nodes as
  the standalone raw artifact, but incremental CNF emits 782,716 clauses versus
  545,905 one-shot (+43.38%). Of 508,729 lazy definition halves, positive
  AND-tree owns 253,274 (49.79%), inverted-AND 141,670 (27.85%), XOR 95,780
  (18.83%), binary AND 18,003 (3.54%), and negated ITE only two. The 1,789
  direct positive roots traverse 109,358 AND nodes and expose 90,149 structural
  XOR leaves.

  The next bounded GQ5 implementation is therefore selector-guarded direct
  encoding of asserted positive AND trees and their XOR leaves. It may not
  assume global single use: ordinary definitions must remain available for
  later opposite-polarity/scope reuse. Acceptance requires fewer clauses and
  lower **unprofiled native Glaurung time**, with identical AIG, SAT/UNSAT
  outcomes, scopes, model lift, and original-root replay. The profiled 1.272x
  ratio is diagnostic overhead and is not a GQ10 baseline.

- **2026-07-15 — ADR-0160 lands exact native Glaurung attribution and selects
  incremental gate fusion.** `IncrementalBvSolver` now has an explicit
  profiling constructor plus monotone phase/structure snapshots; ordinary
  constructors perform no diagnostic clock reads or counter updates. Glaurung
  commit `f201448` preserves its raw fresh-arena/fresh-solver policy, keys each
  check to the exact capture-rendered SHA-256, times translation, lower/encode,
  SAT, model lift/replay and client extraction separately, and writes ordered
  process-isolated JSONL. Axeyum's fail-closed summarizer validates schema,
  order, completeness, roots/checks, phase totals, policy/timeout identity,
  manifest overlap, and optional 100% decided.

  The first exploratory release process at Axeyum `c8ffb43d` and Glaurung
  `f201448` uses Z3-authoritative exploration of `win10-vwififlt.sys`: 13,126
  same-stream queries all decide and agree, with zero unknowns. The ordered
  stream retains 7,065 unique hashes and 6,061 duplicate occurrences; 52
  unique hashes/154 occurrences overlap the pinned representative manifest
  with no outcome conflict. Native profile time is 17.429 seconds: bit blast
  7.461 s (42.81%), incremental CNF 6.550 s (37.58%), SAT 1.260 s (7.23%),
  and translation 0.789 s (4.53%); p50/p95 are 0.881/3.667 ms. A matching
  unprofiled shadow control measures ordinary Axeyum/Z3 wrapper time at
  18.826/6.478 seconds (2.906x).

  All 52 exact overlap hashes retain standalone AIG size: weighted over 154
  occurrences, both paths build 494,150 AIG nodes while native incremental CNF
  emits 875,083 clauses versus one-shot's 506,480 (+72.78%). Glaurung `ExprId`
  sharing therefore survives translation; the next
  bounded cold slice is one measured incremental gate-fusion pattern, not more
  broad rewrite/demand work or SAT tuning. The 46.18% duplicate-occurrence
  rate also raises GQ7/GQ8 priority, but cache/reuse work still requires the
  ordered worker/path/scope trace. This single-driver run is exploratory;
  repeat cleanly across the multi-driver set and same-revision bench artifacts
  before publishing a GQ10 trend.

- **2026-07-14 — ADR-0159 closes the current GQ3 structural rewrite tranche;
  native Glaurung entry attribution is next.** Artifact v31's affected-family
  counts and default-minus-rule manifests now have a fail-closed repeated
  comparator and one-command recipe. It requires clean same-revision artifact
  v31 pairs, identical environment/corpus/non-rewrite policy, exact one-rule
  removal, identical manifest paths/outcomes, 100% decisions and oracle/
  manifest agreement, and zero errors/disagreements/replay failures. Deltas
  pair by path and use `ablation - base`; deterministic structure is reported
  separately from every fresh-process timing sample.

  Five clean rounds at `06750219` validate all 25 base/ablation artifacts over
  the pinned 128-query representative capture. `bv.extract_extend.v1` reaches
  45 queries (25 register-slice, 20 slice-partial); disabling it adds exactly
  6,259 term-bit materializations and averages +1.657 ms cold / +0.907 ms bit
  blast on those queries. `extract_nested` and `extract_concat` add 4,140 and
  635 term bits with small +0.106/+0.074 ms mean cold effects. `extract_bitwise`
  changes materialization in the opposite direction and is timing-neutral at
  this scale (mixed signs, +0.026 ms median cold). Every one of the four
  ablations changes **zero AIG nodes and zero CNF clauses**. Keep the exact
  rules enabled, but stop treating lexical opportunities or fire counts as an
  AIG/CNF optimization hypothesis on this capture.

  GQ3 is complete for the currently measured structural shapes, and both GQ4
  designs remain deferred/off after failed real gates. The immediate client
  task is GQ1: key native Glaurung arena allocation, `ExprPool` translation/
  interning, word policy, lower/encode, SAT, model extraction, replay, and
  caller overhead to the exact captured query hash. That measurement decides
  between GQ5 incremental gate fusion and a purpose-built one-shot client API.

- **2026-07-14 — ADR-0157 v1 fails the real Glaurung performance gate and is
  deferred off by default.** The cold SAT-BV backend
  now selects demand-driven lowering only through
  `SolverConfig::demand_bit_slicing`; the full and incremental defaults are
  unchanged. Dense backward propagation is exact for the first structural
  class and every other operator is a conservative full-width barrier. Sparse
  term-bit lookup and deterministic zero completion support partial symbol
  models, while mandatory original-assertion replay remains the SAT soundness
  gate. The focused 8-of-64 equality materializes 25/25 term bits and 8/8
  symbol bits instead of 81/64; SAT and UNSAT variants pass replay.

  Artifact v29 records the policy in configuration identity and distinguishes
  `structural-lowering` from observational demand. Dedicated whole-tier and
  `register-slice` recipes are present. All 26 BV tests, 31 SAT-BV tests, three
  typed-layer tests, 33 benchmark tests, and strict focused Clippy pass under
  the 4 GiB cap. A clean committed micro smoke decides/agrees 2/2 with zero
  errors, disagreements, or replay failures and records lowering on both
  instances; it demands every bit and makes no client-performance claim. The
  Glaurung measurement now supplies the decisive missing gate: v1 remains 100%
  decided with zero disagreements, but regresses Axeyum/Z3 from about 1.42x to
  4.49x and raises bit blast from 47% to 83% of Axeyum time. The backward
  demand analysis costs much more than the blast it avoids. ADR-0157 is
  therefore deferred, not accepted; v1 remains explicit and must not become a
  default or automatic choice.

  The client trajectory is now a plateau rather than a sequence of wins: the
  shipped default stays around 1.42x; the earlier arithmetic rewrites do not
  materially fire on this register-slice-heavy corpus; and the demonstrated
  cold improvement remains the CNF work that moved roughly 2.0x to 1.4x. Do not
  attribute progress to a semantically green experiment that increases client
  time.

  Proposed ADR-0158 defines GQ4-v2: a cheap syntactic admission precheck before
  per-term bitset allocation, a memoized and bounded range-demand pass, a
  deliberately wide predicted-savings threshold, and early fallback to
  ordinary full lowering. Its first isolated `axeyum-bv` implementation now
  provides all four mechanics: conservative structural screening, four-inline-
  range exact propagation, deterministic work-budget and exact-savings
  fallback, and sparse range-backed materialization. The ADR-0157 force-on path
  is unchanged. Six focused additions bring the BV suite to 32/32 green,
  including range-vs-dense equivalence, no-candidate/full-lowerer identity,
  budget determinism, fragmentation promotion, replay, and deadline coverage;
  strict focused Clippy is clean under the 4 GiB cap. Artifact v30 now completes
  the integration boundary: `SolverConfig::range_demand_slicing` is distinct
  from v1, conflicting modes fail explicitly, every threshold/work budget is
  configuration-hashed, and typed plus per-instance/aggregate telemetry records
  admission time, decision, estimate, work, merges, and promotions. Dedicated
  whole-tier and `register-slice` recipes take explicit calibration parameters.
  The CLI micro smoke is 2/2 decided/agreed with zero errors, disagreements, or
  replay failures; both queries correctly report `no-candidate`, so it is
  plumbing evidence only. The subsequent clean pinned-capture measurement
  defers v2. Five default processes average 183.551 ms total / 75.617 ms bit
  blast. Conservative v2 admits 0/128 (50 no-candidate, 78 insufficient
  estimate), costs 1.234 ms admission, and averages 184.683/77.168 ms
  (+0.62%/+2.05%). A moderate 128-bit/5% exact policy admits 33/128 but removes
  only 632 AIG nodes and zero CNF clauses; five processes average 184.670/77.994
  ms (+0.61%/+3.14%). Every process is 128/128 decided with zero errors,
  disagreements, or replay failures. Rejection overhead meets the <2% target,
  but the required family improvement fails. ADR-0158 is deferred and remains
  explicit/off; stop threshold tuning. Separately, ADR-0156's
  batched assertion API cannot validate the structural warm win through
  Glaurung today: Glaurung's `Solver` trait remains one-shot. GQ7/P5 must first
  expose persistent worker/path solver ownership and ordered push/assert/check/
  pop traces.

- **2026-07-14 — Glaurung post-capture priorities reset to demand slicing,
  rewrite impact telemetry, and exact client-path attribution.** The newest
  consumer profile reports bit blast/CNF/SAT at roughly 45%/32%/20%, about 88%
  register-slice-shaped traffic, and a material native-driver/standalone-bench
  gap. These are reproduction targets rather than a silent replacement for the
  accepted clean v4 full result at 0.730x Z3. `PLAN.md` and the Glaurung
  execution plan now integrate all ten follow-ups: production GQ4 slicing;
  per-rule causal telemetry; native translation/interning/model attribution;
  AIG sharing; measured gate CNF; delta warm entry; duplicate/prefix reuse;
  register-slice specialization; queued SAT tuning; and expanded cold plus
  ordered capture with per-commit trends.

  Existing telemetry already records stable rewrite fire counts. The next GQ3
  increment is affected-query/family counts plus default-minus-one-rule
  ablation, because local DAG shrinkage is not a defensible AIG/CNF-saved
  attribution. Existing `BitDemandStats`, dense term-bit ranges, and the
  structural worklist are GQ4 scaffolding only: the production pass still must
  materialize partial bits, default omitted model bits deterministically, and
  replay every untouched assertion. The first acceptance report is explicitly
  partitioned to `register-slice`.

  ADR-0156 is now deferred for cold recommendation. Five interleaved clean
  representative comparisons at `1588f97c` decide/replay every execution. The
  fresh incremental canonical batch averages 0.060969 s versus one-shot
  canonical `sat-bv` at 0.051301 s (+18.8%; `register-slice` +26.4%). Both build
  the same AIG, but incremental CNF emits 170,102 versus 94,043 clauses per
  trial (+80.9%) because it lacks the one-shot encoder's global gate fusion.
  This explains a measured part of the real-client/bench gap; Glaurung's native
  `ExprPool`→arena translation, interning, model extraction, and caller costs
  remain to be timed by matching query hash.

- **2026-07-14 — Glaurung's equality cancellation is accepted at 0.73x Z3;
  cold client integration remains a distinct boundary.**
  Sequential capture at Glaurung
  `286f744` produced 15,710 rows / 15,687 unique hashes / 23 duplicate rows /
  zero verdict conflicts. Strict validation rejected 2,225 ill-sorted producer
  dumps and bound separate 128-query representative and 13,462-query well-typed
  full manifests. ADR-0184 later attributes those failures to the producer and
  makes these hashes historical. Five artifact-v26 representative trials are valid under every
  gate: median raw/canonical/configured ratios are 6.53x/3.42x/3.54x, canonical
  cuts Axeyum total 48.5%, and raw/canonical proof companions recheck all 64
  UNSAT rows. Same-revision full raw/canonical trials decide 13,462/13,462 with
  zero errors/disagreements/replay failures and measure 15.19x/6.32x; canonical
  cuts Axeyum total 57.1% and term bits 72%.

  ADR-0143 and artifact v27 now make structural demand profiling opt-in and
  distinguish unprofiled production from complete diagnostics. Five-process
  representative raw/canonical medians are 0.2505/0.2069 s versus Z3
  0.1517/0.1505 s (1.65x/1.37x). Full raw/canonical single trials are
  24.30/21.07 s versus Z3 7.66/7.76 s (3.17x/2.71x). All 10 representative
  trials and both full trials are 100% decided with zero errors,
  disagreements, or replay failures. Corrected canonical is a 13.3% full-tier
  win, not v26's profiler-inflated 57.1%.

  ADR-0144 lands the first measured GQ5 win. A collision-safe deterministic
  fingerprint table references formula-owned clauses instead of cloning every
  accepted clause into an ordered vector set. Representative canonical median
  CNF/total improve 15.3%/6.3%; full CNF improves 9.40 → 7.66 s (-18.5%), total
  21.07 → 19.22 s (-8.8%), and ratio 2.71x → 2.47x. Clause and variable counts
  are unchanged and all gates remain green. The rejected scalar ordered-index
  prototype is retained as negative evidence.

  ADR-0145 lands the second measured GQ5 win. Fixed stack arrays and four exact
  factor-shape matches replace temporary-vector expansion for 2.23 million
  recognized not-AND gates. Representative canonical median CNF/total improve
  another 6.6%/2.0%; full CNF improves 7.66 → 7.23 s (-5.6%), gate emission
  3.56 → 3.19 s (-10.5%), total 19.22 → 18.69 s (-2.7%), and ratio 2.47x
  → 2.40x. Both full artifacts emit exactly 49,199,541 clauses and all
  verdict/replay gates remain green.

  After ADR-0150, full canonical stages are word rewrite 1.80 s, bit blast
  5.88 s, CNF 5.18 s, and SAT 3.50 s. CNF gate/root emission costs 2.40/1.08 s
  and planning 1.20 s. The residual family attribution is now complete and
  selects ADR-0153's `slice-partial` add-chain experiment below. Broad GQ4
  remains behind it because the complete canonical diagnostic demands 98.16%
  of term bits. Glaurung must separately fix explicit width coercion, strict dump
  validation, and atomic cross-process deduplication. Full evidence and digests:
  [`bench-results/glaurung-qfbv-2026-07-14.md`](bench-results/glaurung-qfbv-2026-07-14.md).

  ADR-0146 tests and rejects the first residual root-emission hypothesis.
  Reusing one cleared OR-leaf scratch passes a 128-row two-root regression, all
  284 CNF tests, 30 SAT-BV tests, and strict Clippy, but five clean
  representative processes regress median total 1.1%, CNF 4.9%, and the matched
  root subphase 2.0% with identical content. The accepted owned-vector path is
  restored; no full run is warranted. Profile planning next, and revisit direct
  roots only with a design that eliminates the second traversal entirely.

  ADR-0147 tests the first bounded planning candidate. `Aig::nodes()` is already
  backed by an exact-size double-ended slice iterator, but its opaque public
  type hid those traits, forcing private AND-tree planning to copy every node
  into a temporary vector solely to reverse it. Exposing the iterator traits
  preserves exact order and improves representative median planning 2.5%, but
  total regresses 0.5% and CNF 3.6%. The API/code is restored and ADR-0147 is
  deferred without a full run. Planning's projected ~0.03-second full saving is
  not worth another micro-slice while shared gate/root normalization sees 53.75
  million clause attempts.

  ADR-0148 tests and rejects the next bounded shared-ownership candidate. The deterministic
  `min(5 * variables + roots, 65,536)` hint covers all 13,462 measured formulas,
  reserves 69.23 million aggregate slots versus 49.20 million emitted and the
  current vector-growth estimate of 71.57 million, and uses no new traversal.
  Root contribution is capped at 1,024 and zero-variable encodings reserve
  nothing. Giving that hint to both formula headers and the exact-dedup index
  passes all semantic gates but regresses representative total/CNF 2.5%/10.0%
  and gate emission 23.5%; sparse hash lookup outweighs avoided rehashes. The
  accepted empty-growth path is restored and no full run is warranted. Any
  follow-up must isolate the contiguous formula-header vector.

  ADR-0149 isolates exactly that vector and leaves the fingerprint table
  byte-for-byte unchanged. All 284 CNF tests, 30 SAT-BV tests, and strict Clippy
  pass, and five representative processes preserve all 507,195 clauses,
  128/128 decisions, and replay. It nevertheless regresses CNF median/mean
  0.83%/0.67%; total median moves -0.16% but mean regresses 0.07%, with higher
  run variance. Ordinary vector growth is restored, no full run is warranted,
  and the capacity-hint lane is closed.

  The follow-up ownership audit selects ADR-0150 as the next bounded GQ5
  experiment. The accepted `HashMap<u64, Vec<usize>>` performs a membership
  lookup and then a second entry lookup for a unique clause, while the first
  push allocates a tiny vector for each distinct fingerprint. The full stream
  emits 49,199,541 clauses; `register-slice` plus `slice-partial` account for
  53,247,640/53,748,044 attempts (99.1%) and 48,702,009/49,199,541 emitted
  clauses (99.0%). ADR-0150 retains the common formula index inline and uses a
  secondary vector only for a genuine fingerprint collision, preserving exact
  equality and formula ownership. The implementation is now green across all
  283 CNF tests, 31 SAT-BV tests, strict Clippy, formatting, and link checks. A
  forced-collision test retains two distinct same-fingerprint clauses and
  suppresses exact repeats of both.

  ADR-0150 passes both client gates and is accepted. Against `c139d73b`, five
  representative processes improve total p50/mean 13.00%/12.97% and CNF
  p50/mean 28.96%/29.55%; gate/root medians improve 24.94%/23.07%, and total CV
  falls 0.570% → 0.212%. The full 13,462-query confirmation improves total
  18.691 → 16.540 s (-11.51%), CNF 7.231 → 5.177 s (-28.41%), gate/root
  3.186/1.391 → 2.400/1.083 s (-24.68%/-22.11%), and the ratio 2.399x →
  2.136x. Every run retains 100% decisions, zero errors/disagreements/replay
  failures, and exactly 53,748,044 attempts, 4,248,964 duplicates, and
  49,199,541 emitted clauses. Bit blast at 5.884 s is now the largest stage,
  narrowly ahead of CNF at 5.177 s; SAT remains 3.496 s.

  The cold-lowering ownership audit selects proposed ADR-0151. Full canonical
  lowering appends 23,029,676 `TermBitBinding`s and also inserts every binding
  into `BTreeMap<(TermId, u32), AigLit>`. `TermId`s are dense, every term's
  bindings are contiguous, and the only lookup consumer is
  `literal_for_term_bit`; interpolation already iterates the authoritative
  binding vector. `register-slice` plus `slice-partial` contribute 22,797,529
  records (99.0%). Replace the redundant ordered map with a dense per-term
  `(start, length)` range, preserving public lookup, deterministic order,
  incremental arena growth, and all replay/lift contracts. The implementation
  passes 20 BV tests (including lookup boundaries and incremental growth), 10 BV
  interpolant tests, 31 SAT-BV tests, strict Clippy, formatting, and link checks.
  ADR-0151 passes both performance gates and is accepted. Five representative
  processes improve total p50/mean 5.59%/5.67% and bit-blast p50/mean
  15.51%/15.58%, with identical 746,716 AIG requests, 410,719 created nodes,
  and 507,195 clauses. The full confirmation improves total 16.540 → 15.596 s
  (-5.71%), bit blast 5.884 → 4.939 s (-16.05%), and ratio 2.136x → 1.992x;
  CNF/SAT are flat at 5.178/3.495 s. All 13,462 queries decide with zero errors,
  disagreements, or replay failures and the exact same 76,493,904 AIG requests,
  40,063,239 created nodes, and 49,199,541 clauses.

  The next ownership audit selects proposed ADR-0152. The full post-word DAG has
  982,044 unique terms, and `BTreeMap<TermId, Vec<AigLit>>` retains a second
  vector for every completed term, duplicating the 23,029,676 literals already
  represented by the authoritative bindings and ADR-0151 ranges.
  `register-slice` plus `slice-partial` contribute 973,313 terms (99.1%). Use
  range presence as the dense completion memo and reconstruct the same owned
  child vectors from bindings; deliberately leave operand cloning and lowering
  algorithms unchanged for an attributable experiment. The implementation
  passes 21 BV tests (including interrupted-root retry), 10 BV interpolant
  tests, 31 SAT-BV tests, strict Clippy, formatting, and link checks. ADR-0152
  preserves every AIG/CNF counter across five representative processes but
  fails the performance gate: bit-blast p50/mean improve 0.57%/0.51%, while
  total p50/mean regress 0.02%/0.38%, CNF p50 regresses 0.88%, and total CV
  rises 0.231% → 0.712%. The exact ADR-0151 implementation is restored,
  ADR-0152 is deferred without a full run, and memo-ownership micro-work closes.

  GQ10 now has a regular real-lifter semantic gate. `just check` auto-discovers
  the pinned 2026-07-14 NAS representative pack or uses
  `AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR`; absent access is a visible skip,
  while explicit missing/incomplete data fails. Both raw/current-integration
  and canonical-candidate policies run under manifest, in-process Z3,
  deterministic-resource, 100%-decided, and zero-error/disagreement/replay
  gates, with artifacts retained under ignored `target/` state. The first real
  run passes 128/128 for both: raw Axeyum/Z3 is 0.184/0.149 s (1.23x), canonical
  is 0.157/0.150 s (1.04x). These dirty-worktree single trials validate regular
  functionality and attribution only; they do not set a performance threshold.

  The separate clean full-tier variance tranche is now complete. Five canonical
  processes at `0cfd6cdc` each decide and agree on all 13,462 rows. Mean
  Axeyum/Z3/ratio are 15.644/7.738 seconds/2.0217x; CV is
  0.514%/0.310%/0.510%, and every stage is below 1%. The provisional guarded
  comparison uses 3% maximum ratio regression, 3% maximum Axeyum-total
  regression, and 2% maximum absolute Z3 drift. During validation, the
  comparator's stale `preprocess=true` requirement was found to reject raw and
  canonical artifacts; it now validates explicit rewrite mode and accepts all
  three named policies without allowing baseline/candidate policy drift.

  The full family attribution selected ADR-0153. In canonical run
  003, `slice-partial` is 1,584/13,462 queries (11.8%) but consumes 6.207/15.627
  seconds (39.7%), runs 3.82x behind Z3, creates 16.91 million AIG nodes, and
  emits 22.87 million clauses. Bit blast plus CNF own 70.6% of its time. Its
  original scripts contain 377,320 `bvadd` occurrences, and the code audit
  confirms that current AC flattening sorts mixed symbol/constant chains but
  rebuilds lists wider than two before binary constant folding. The exact,
  wide-safe `bv.add_constant_chain.v1` rule is now accepted under rewrite
  identity v3. Five full processes improve total 15.644 → 14.111 seconds
  (-9.80%), ratio 2.022x → 1.852x (-8.37%), AIG requests 12.13%, clauses
  17.23%, and `slice-partial` time 24.4%. All 13,462 rows decide and replay
  cleanly in every run; the exact-additive rewrite comparator passes all
  3%/3%/2% alarms. The ordered
  worker/path/scope trace remains the next Glaurung functionality artifact;
  the cold pack cannot validate warm reuse, caching, or model-choice effects.
  The proposed
  [ordered warm-trace v1](docs/research/08-planning/glaurung-ordered-trace-v1.md)
  now specifies the event envelope, lineage/scopes, content-addressed query
  linkage, controlled model-choice classification, strict producer validation,
  and T0--T5 replay/integration gates.

  ADR-0154 closes the post-v3 attribution blind spot with artifact v28. Each
  original and post-word query-shape snapshot now counts every scalar Bool/BV
  operator over unique reachable DAG nodes and retains an explicit `other`
  bucket. All 31 benchmark unit tests, strict Clippy, 22 Glaurung consumer
  tests, and the 128/128 raw+canonical semantic gate pass under 4 GiB. The
  representative canonical post-word DAG contains 7,019 applications and zero
  `other` operators; equality (3,326), `ite` (1,788), and `bvadd` (1,008) lead.
  The clean full process at `37ebcd47` then decides/replays 13,462/13,462 with
  zero errors or disagreements and measures 14.2148/7.7184 seconds (1.8417x).
  Its SHA-256 is
  `2eea061282513d09dd417ba1713e60b4bffb607cf178a545d757006207343190`.
  Post-word totals are 659,445 applications and zero `other`: 309,160 equality,
  162,931 `ite`, and 104,510 add lead. Residual excess is nearly even between
  `register-slice` (+3.441 s) and `slice-partial` (+3.142 s); the latter's
  44,668 additions correlate 0.988 with bit-blast-plus-CNF time.

  ADR-0155 now accepts exact modular constant cancellation
  across equality: `sum(symbolic) + c = k` becomes
  `sum(symbolic) = k - c`. It removes one wide adder and exposes hash sharing
  across offset variants without changing symbols or model projection. The v4
  rule passes exhaustive evaluation through width 3, modular wrap,
  129-bit, both-orientation, multiplicity, and non-match tests plus strict
  Clippy. Five representative processes improve mean total 61.7% to 0.0515 s
  and ratio 61.3% to 0.351x Z3. Five full processes then improve mean total
  13.946 → 5.625 s (-59.7%) and ratio 1.829x → 0.730x (-60.1%); bit
  blast/CNF/SAT improve 70.5%/69.9%/68.0%, while word rewrite costs 2.9% more.
  The rule fires 104,465 times, output DAG nodes fall 45.4%, AIG requests/new
  nodes fall 63.1%/76.7%, and clauses fall 75.4%. All five runs decide and
  replay 13,462/13,462 with no errors or disagreements. `register-slice` and
  `slice-partial` improve 48.8%/82.8% and both are now faster than Z3. The exact
  v3→v4 comparator passes every 3%/3%/2% gate with 1.07% Z3 drift.

  Deferred ADR-0156 addresses the remaining cold integration mismatch.
  Glaurung already translates all query roots together, but singular
  `assert_configured` canonicalizes them independently; the accepted benchmark
  uses one shared multi-root memo. New additive
  `assert_preprocessed_batch`/`assert_configured_batch` methods match that
  boundary, retain original roots for replay, prevalidate all Boolean sorts,
  and document ordered partial admission. Four focused solver tests, 32
  benchmark tests, and strict solver/benchmark Clippy pass. The pinned 128-query
  comparison is replay-clean but fails the non-worse performance gate: the
  fresh incremental route is 18.8% slower and emits 80.9% more CNF clauses than
  one-shot canonical `sat-bv` despite the same AIG. The API remains explicit
  plumbing; it is not the recommended Glaurung cold path.

- **Historical Glaurung build-up through 2026-07-14 (superseded by the measured
  result above).** The ten-item Glaurung QF_BV performance roadmap is an
  explicit Track 1/4 lane (`PLAN.md` GQ1--GQ10). The ordering is
  benchmark-first: capture and profile the actual shadow-diff SMT-LIB stream,
  establish its first-class regression tier, and only then choose between cold
  rewriting/slicing, AIG/CNF construction, or SAT search from measured layer
  attribution. Warm delta reuse, duplicate/prefix caching, and an automatic
  preprocessing cost policy are separately tracked rather than being implied by
  the existing incremental API.

  **2026-07-14 capture inspection:** the Glaurung producer handoff at commit
  `7cab030` now supplies the capture procedure, builder, exclusions, and a
  128-query representative manifest. The balanced tier is 64 SAT / 64 UNSAT
  across 42 register-slice, 48 slice-partial, 23 arithmetic, 12 comparison, 2
  mixed, and 1 trivial queries. Its artifact-v17 producer run reports 128/128
  decided and manifest/Z3-agreed, zero unsupported/disagreements, a 2.10x
  Axeyum/Z3 ratio (272 ms / 130 ms), and cold attribution of 42% bit-blast,
  42% CNF encode, 15% SAT, and 1% model lift. That is enough to rank GQ3--GQ5
  ahead of GQ6, but not to close the current gate: neither the committed
  Glaurung capture directory nor this Axeyum checkout contains the referenced
  `.smt2` pack, and the measurement predates artifact v22. The producer handoff
  also needs three reproducibility repairs before the full tier is authoritative:
  its reported 15,687 total conflicts with the 15,710 SAT+UNSAT subtotal, its
  exclusion file has 17 rows but only 11 unique hashes, and its builder emits a
  full manifest while copying only representative query files.
  The likely explanation for the 23-row total/subtotal discrepancy is now
  localized but remains to be verified from the raw directory: capture
  deduplication is process-local, the documented command launches three
  processes into one directory, and the builder silently overwrites duplicate
  TSV hash rows without checking verdict consistency. The producer handoff also
  bypasses artifact v22's strict hash-free capture-index generator by authoring
  a hash-bearing manifest directly. The repaired handoff must report row and
  unique counts separately, reject conflicting duplicate verdicts, and let
  Axeyum compute hashes from a byte-complete root.

  **2026-07-14 execution-plan audit:** the producer's artifact-v17 command and
  Glaurung's current one-shot backend both use raw assertions (rewrite off,
  preprocessing off). The former Axeyum recipe instead forced `--preprocess`,
  even though Glaurung measured configured preprocessing as a 1.3--2x cold
  loss. That mismatch is now fixed: explicit raw/current-integration,
  canonical-only, and configured recipes exist for single, repeated, and
  matching proof-companion runs; unsuffixed compatibility recipes select raw;
  output defaults are policy-specific; and four dry-run regression tests pin
  every flag/alias boundary. The complete capture, implementation, functional,
  and warm-integration task graph is recorded in the
  [Glaurung QF_BV execution plan](docs/research/08-planning/glaurung-qfbv-execution-plan.md).
  It also records the non-performance acceptance requirement that model-choice
  divergence can steer Glaurung findings even under perfect verdict agreement;
  real warm integration needs a controlled concretization policy or an
  equivalent-choice-aware finding comparison.

  **GQ1/GQ10 readiness increment:** artifact v25 retains v23's word-policy
  boundary and charges Axeyum for word
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
  Artifact v23 now adds paired original/post-word-policy shape snapshots and
  before/after/removed/added opportunity transitions without changing solver
  behavior. It classifies concat slices as low-side, high-side, straddling, and
  exact whole operands; extension slices as low, high, or straddling; records
  exact low zero/sign-extension cancellation and maximum nested-extract depth;
  and reports the residual of every GQ3 class per instance and corpus. Three
  focused shape/transition tests plus the full 27-test `axeyum-bench` suite pass
  under the 4 GiB cap. Artifact v23's repetition ingestion locked that
  configuration/shape contract away from historical v22 trials.
  Artifact v24 now carries bounded AIG/CNF construction attribution through the
  typed solver layer, per-instance records, and corpus summary. Primitive AIG
  AND requests partition into trivial simplification, absorption, structural-
  hash hit, and new-node outcomes. CNF planning/allocation/gate/root time,
  reachable/helper/direct-root counts, recognized gate families, and clause
  attempt/tautology/duplicate/emitted outcomes are exposed with explicit
  partition invariants. CNF subphase time is marked nested inside encode time.
  Artifact v25 adds request/unique-demanded/available/actually-lowered term and
  symbol bit counts, ratios, coverage invariants, and nested analysis time. Its
  conservative structural propagation is exact across extract/concat/
  extension/pointwise/ITE/rotation cases and full-operand elsewhere. A focused
  narrow-extract regression measures 25/81 demanded term bits and 8/64 demanded
  symbol bits while the current lowerer still materializes all 81 and 64.
  Repetition ingestion is now version-locked to v25.
  ADR-0142 completes the exact GQ3 implementation surface. The default
  canonicalizer now handles nested extracts, concat-boundary straddles and
  whole-side returns, plus low/high/straddling zero/sign-extension slices.
  Replacement roots are reconsidered under an eight-application local budget;
  exhaustion is observable and returns an exact partial result. Stable rule
  IDs, fixed local fresh-node bounds, exhaustive small-width evaluation, 96
  seeded wider cases, and lifter-shaped Z3 SAT/UNSAT differential replay are
  green. The default benchmark identity advances to
  `axeyum-rewrite-default-v2`. No real-payload AIG/CNF/time claim is made.

  | ID | Live status | Next acceptance boundary |
  |---|---|---|
  | **GQ1 real-query profile** | **Map, query/internal attribution, fresh/retained exact-CNF controls, six-cell in-process neutral warm map, complete three-solver timeout frontier, bounded/canonical/four-schedule plus wider timeout-sensitive raw authority cells, process-isolated corrected-representative plus wider-holdout end-to-end faithfulness, deadline-aware generated proof widening, isolated behavior-preserving Glaurung A0, taint/SystemBuffer baseline corrections, confidence partition, source-backed nonzero positive control, rejected usbprint resource protocols, detector correction, corrected five-policy sweep, exhaustive difference adjudication, v6 hidden-work rejection, external DRAT controls, immutable symbolic-CVE artifact admission, 2/2 selected-pair symbolic recall, deterministic six-cell v4 wiring, and rejected first calibration DONE (ADR-0187/0188/0213--0273 plus Glaurung `dc06a37`; campaign revision `ff3c0a7`).** ADR-0272 accepts 64,510 repeated occurrences and 387,060 in-process cell executions with complete six-way parity, zero fallback, and all four neutral gates green. Axeyum's warm Z3-relative result is workload-dependent while Bitwuzla leads all four warm drivers, ruling out a performance-lead headline. ADR-0273 completes 42/42 clean processes but selects no Axeyum limit and authorizes no census. The symbolic-CVE result remains only two admitted pairs, not population recall; tcpip remains zero-high/unlabeled. | Either preregister a fixed-Z3-authority shadow calibration extension or close the harder-driver tier negative; admit broader labeled artifacts separately; keep symbolic memory closed |
  | **GQ2 cheap cold tier** | **WIP with three accepted rewrite tranches; batch integration deferred.** Canonical v4 reaches 5.625 s / 0.730x Z3; ADR-0156 preserves replay but is 18.8% slower than one-shot | Keep canonical v4 as the measured one-shot policy; do not recommend fresh incremental batch until its clause/entry overhead closes |
  | **GQ3 coercion/affine peepholes** | **DONE for current measured shapes (ADR-0159).** Clean repeated path-paired ablations are fail-closed; `extract_extend` is a material lowering-only win, while all four measured structural rules change zero AIG nodes/clauses | Keep rules enabled. Reopen only for a new residual shape with a specific downstream hypothesis and the same causal ablation gate |
  | **GQ4 cold relevant bits** | **v1 and v2 DEFERRED after failed real gates.** v1 regresses ~1.42x→4.49x. V2 rejection overhead is bounded, but defaults admit 0/128 and +0.62% total; a 33-query moderate policy removes 632 AIG nodes/zero clauses and regresses bit blast 3.14% | Keep both explicit/off. Reopen only with an AIG/CNF-cone estimator or after word rewrites materially change the residual; do not tune thresholds further |
  | **GQ5 AIG/CNF construction** | **Current duplicate-origin lane CLOSED without optimization (ADR-0259--0261); broad warm lane closed by ADR-0219.** ADR-0261 preserves all 162 gates but changes every selected construction counter by zero | Remove the no-op candidate; reopen only from a new preregistered leaf-shape/clause-overlap mechanism, not another interpretation of ADR-0260 |
  | **GQ6 cold SAT/CDCL** | **Fresh and retained exact-CNF controls DONE (ADR-0220/0221).** Proof core beats fresh BatSat before checking; retained BatSat beats retained Z3 Boolean | Do not select a core rewrite from Dptf; reopen only on a SAT-dominant family with a neutral core gap and deterministic limits |
  | **GQ7 warm delta entry** | **Source identity, fair map, query/internal attribution, fresh/retained CNF controls, four-driver neutral cold-reset plus source-owner-retained SMT, bounded raw finding parity, canonical tcpip authority, four-schedule union, isolated configurable-policy A0, taint/SystemBuffer baseline corrections, confidence partition, 14-row source-backed positive control, v1 resource rejection, v2 precision rejection, detector correction, v3 scalar sweep, exhaustive difference adjudication, rejected usbprint frontier, and a full v6-gated two-authority campaign DONE (ADR-0201--0250/0262 plus Glaurung `7f682e5`; campaign revision `ff3c0a7`).** Every scalar policy preserves 14/14; ADR-0248 finds zero independent primitives among all 54 varying source-backed rows. ADR-0249's common prefix 10 is descriptive only because prefix 15 concealed a deadline-terminated inner worklist; ADR-0250 prevents future fixed-work acceptance on that state. ADR-0262 then validates all six first-20 cells with zero hidden timeout/deadline stops. Tcpip remains diagnostic, and canonical policy cost reaches 96,075 solves / about 191 MiB | Keep symbolic memory gated; coordinate clean integration, require a broader labeled residual gap, and preserve v6 for future fixed-work acceptance |
  | **GQ8 verdict/CNF cache** | **DONE for available families (ADR-0192).** Clean repeated evidence admits exact same-arena scalar SAT reuse only in path-owned Glaurung sessions; fixed bounds, traffic partitions, cleanup gauges, findings, and replay are enforced | Preserve explicit off and re-gate new families; Axeyum's generic cache remains opt-in and ordinary UNSAT/Unknown/prefix verdicts remain excluded |
  | **GQ9 auto cost model/docs** | **DONE for available families (ADR-0186).** Clean adaptive repeat clears every alarm over 92,721 checks; downstream explorer default has explicit off/fixed controls | Re-gate newly captured families; do not broaden this Glaurung-specific default into Axeyum's generic API |
  | **GQ10 real-lifter regression tier** | **Native continuation admission DONE; wider direct-delta default DEFERRED (ADR-0205--0212).** The accepted tcpip trace admits bounded continuation. The new complete 85,449-event / 17,400-check `dxgkrnl` trace and independent replay preserve exact no-op behavior and every correctness/lifecycle gauge, but ordinary-core time CV is 14.430%/8.306% and slower-core outcomes drift | Keep direct delta opt-in. Repeat under a quieter predeclared environment or add another no-timeout IOCTL driver; route `win32k` to a system-service/callout frontend |

  **Next actions:** ADR-0271 closes the bounded selected-pair symbolic-CVE gate,
  ADR-0272 closes PLAN item 2's topology-equivalent six-cell neutral map, and
  ADR-0273 rejects item 3's completed deterministic calibration because no
  Axeyum ladder value qualifies. All four neutral gates pass; Axeyum's
  Z3-relative map is workload-dependent, and warm Bitwuzla leads every driver.
  Do not run the census or combine limits selected on different authority
  streams. Either preregister a fixed-Z3-authority extension or retain the
  negative result and advance the next publication lane. Standing integration constraints: (1)
  coordinate with the active Glaurung explorer owner and
  integrate isolated branch `axeyum-concretization-policy-a0` at `7f682e5`
  (confidence implementation `931d8a8`, provenance implementation `845239f`,
  WDM SystemBuffer correction `b79f269`);
  A0's two-seam `ConcretizationPolicy`, exact `AnyModel` compatibility gate,
  selector aliases, exact-source taint, and WDM address/content separation are
  complete, so do not reimplement them or edit the live dirty checkout; (2)
  retain ADR-0243's exact 14-row source-backed planted population as the hard
  positive-control stratum; tcpip and corrected usbprint remain zero-positive,
  and producer confidence is not ground truth; (3) preserve ADR-0245's rejected
  prefix, ADR-0246's accepted correction trail, and ADR-0247's accepted exact
  five-policy v3 campaign and ADR-0248's exhaustive 54-row adjudication; do not
  select further coverage work from raw diagnostic variation; extend with
  BoundarySet/DiverseEnum only after bounded
  multi-successor execution is implemented, keeping
  deterministic work bounds as configuration and separate raw,
  confidence-gated, validated, work, and cost partitions; do not use raw
  `>= AnyModel` as a recall gate, report real-driver policy variation as
  unlabeled discovery output until separately validated, and begin symbolic
  memory only if a genuinely broader labeled population establishes residual
  coverage headroom; (4)
  preserve ADR-0249's rejected bounded-function/work usbprint frontier and
  coordinate clean integration from Glaurung campaign revision `ff3c0a7`;
  ADR-0250's
  v6 harness gate now requires explicit exploration-stop telemetry, internally
  consistent counts, zero deadline/timeout stops, and stable per-backend
  partitions, so use it for any future fixed-work campaign rather than accepting
  outer function count alone; (5) after
  ADR-0235's completed process-isolated representative real-query denominator,
  preserve ADR-0252's zero-query membership rejection and ADR-0253's exact
  1,024-query result, including its stable 508/509 stronger-certificate
  coverage; preserve ADR-0254's positive external verification and rejected
  no-op tamper, plus ADR-0256's accepted satisfiable-CNF checker control and
  explicit trivial-proof limitation; if external proof depth still outranks
  broader labeled findings, preserve ADR-0258's retained 32-row no-selection
  and do not widen or keep mining this holdout; reopen nontrivial proof evidence
  only for a separately motivated SAT-search workload rather than selecting a
  proof post hoc or tuning the fixed deadline; (6) widen
  ADR-0237's accepted four-oracle/edge-frequency gate as a standing bounded
  correctness control; (7) keep each subprocess/FFI boundary named; (8)
  preserve ADR-0236's rejected any-model
  divergence beside every canonical result and never treat canonical output as
  the union of reachable findings; (9) preserve ADR-0262's completed wider
  timeout-sensitive sole-authority result, including separate timeout cells,
  the zero-high/unlabeled claim boundary, and the substantial canonical-policy
  cost; do not repeat this tcpip tier as coverage evidence; (10) preserve ADR-0259's accepted
  no-optimization result, ADR-0260's accepted duplicate-origin evidence, and
  ADR-0261's exact zero-delta rejection; do not run its timing protocol or
  reinterpret the origin cell, and reopen only from separately preregistered
  leaf-shape/clause-overlap evidence; (11) stage solver
  namespace/module, duplicate-removal, and typed-config refactors only as
  bounded behavior-preserving tranches; (12) keep
  GQ4 explicit/off.

  **Validation (2026-07-19, ADR-0251 preregistration):** four selector tests
  pass after a recorded missing-script red phase. The selector binds exact full
  and representative manifest SHA-256 values, refuses overwrite, invalid
  source shape, duplicates, nonmember exclusions, and quota shortage. A clean
  regeneration is byte-identical at `67c7f14f...`; independent inspection
  confirms 1,024 entries, 515 SAT / 509 UNSAT, exact registered strata, and
  zero representative overlap. No selected query is executed before commit.

  **Validation (2026-07-19, ADR-0252 preregistration):** the original and exact
  clean-detached reproduction both exit 1 before query execution with empty
  stdout, no artifact, and stderr SHA-256 `a94cc71d...`; 29,604 full-root files
  are unlisted by the 1,024-row holdout. Four materializer tests pass after a
  recorded missing-script red phase. They cover exact membership/bytes,
  pre-output source-hash rejection, nonmember and manifest-hash rejection, and
  overwrite refusal. Together with the four selector tests, 8/8 pass. No
  corrected holdout query is executed before the materialization registration.
  Full script discovery runs 162 tests: 152 pass and the same 10 recipe tests
  cannot start solely because `just` is not installed; the documentation link
  check passes.

  **Validation (2026-07-19, ADR-0253 result):** two clean detached CPU-3
  artifact-v34 processes exit zero with byte-identical summaries and matching
  source/config/environment/manifest identities. Each decides 1,024/1,024,
  reports 0 manifest or Z3 disagreement, replays 515/515 SAT models, and checks
  509/509 CNF DRAT proofs. The analyzer exits zero with exact per-query
  stability at 508 certified plus one retained hard timeout in each run. Raw
  artifact SHA-256 values are `b6d74d75...` and `8bc8822b...`; deterministic
  compressed artifacts and both raw hashes are committed beside the analysis.

  **Validation (2026-07-19, ADR-0254 preregistration):** the proof-export
  process suite passes 2/2 after a recorded missing-binary red phase, covering
  standard DIMACS/DRAT generation, in-tree recheck, manifest identity,
  overwrite refusal, SAT no-output, and scoped-query rejection. Axeyum-bench
  all-target clippy passes with warnings denied, and documentation links pass.
  Pinned upstream `drat-trim` source builds unchanged under the registered
  GCC-15 feature-macro command. At that preregistration commit, the selected
  real proof remained unexported; the subsequent result is recorded below.

  **Validation (2026-07-19, ADR-0254 result / ADR-0255 preregistration):** the
  clean exporter exits zero on the exact 6,543-byte source and self-rechecks
  DIMACS SHA `40154e42...`, DRAT SHA `9a271f2a...`, and LRAT SHA `f5eefbff...`.
  Pinned `drat-trim` exits zero with `s VERIFIED`. The final-line-deleted proof
  is empty, but the checker again prints `s VERIFIED` because seven input
  clauses unit-refute the CNF; the v1 negative gate therefore rejects exactly.
  ADR-0255 binds the replacement satisfiable-CNF bytes/hash before running it.

  **Validation (2026-07-19, ADR-0256):** the unchanged real pair reproduces
  with checker exit 0, `s VERIFIED`, and stdout SHA `c3d94242...`. The exact
  10-byte satisfiable control has preregistered SHA `946afef7...`; the same
  two-byte proof against it makes the checker exit 1, report `no conflict`, and
  print `s NOT VERIFIED`, with stdout SHA `c1924d7b...`. Both stderr streams are
  empty. The accepted result record has SHA `a81a6947...`; timing lines remain
  diagnostic only.

  **Validation (2026-07-19, ADR-0258):** the clean detached exporter at
  `10ee9795` has SHA `41d764a4...`; the selector and pinned checker identities
  match preregistration. All 32 exports succeed without timeout, all proofs are
  exactly 2 bytes / 1 line at SHA `9a271f2a...`, and none is selected. The
  attempts partition as 26 register-slice / 6 slice-partial. Pinned
  `drat-trim` emits an exact `s VERIFIED` line for every positive and empty-
  proof invocation; 16/32 exit zero and 16/32 checker-trivial-UNSAT paths exit
  one in each arm. The committed result SHA is `3821b66d...`; the raw report
  SHA is `fe0b2dc7...`. No timing is used.

  **Validation (2026-07-19, ADR-0250):** the focused authoritative-finding
  harness suite passes 26/26 after a recorded red phase for the missing parser
  and summary gate. A real Axeyum-only `ioctlance` run from clean isolated
  Glaurung `ff3c0a7` on DptfDevGen prefix 1 emits and passes
  `runs=1 completed=1 state_budget=0 solve_budget=0 timeout_budget=0 deadline=0`.
  The source-backed validator independently rechecks every v6 run rather than
  trusting the producer summary; the existing v5 positive-control output still
  reproduces byte for byte at `d068d3c2...`. Full Python script discovery runs
  154 tests: 144 pass, while the 10 existing benchmark-recipe tests cannot start
  because `just` is absent; no recipe assertion runs or fails. Python
  compilation, docs links, and diff checks are rerun at commit time.

  **Validation (2026-07-18, ADR-0242):** the reduced guarded-SystemBuffer
  regression fails before and passes after Glaurung `b79f269`. All 22 focused
  IOCTL tests pass under sole Z3 and sole Axeyum features, and both
  authority-specific `ioctlance` examples compile. The unchanged Axeyum v5
  authority harness runs from clean `f330ac57` against clean corrected Glaurung
  for two order-balanced complete usbprint repetitions; every cell is stable at
  214 raw diagnostics, 0 high-confidence rows, and 16,537 solves, so
  high-confidence parity is accepted. The compact evidence manifest validates,
  and ADR-0243's follow-on link and diff gates pass.

  **Validation (2026-07-18, ADR-0243):** seven validator unit tests cover exact
  acceptance, false negatives, unexpected producer-high rows, authority/source
  drift, driver drift, empty denominators, evidence coverage, repetition
  instability, and live source hash drift. The real join verifies 18 tracked
  IOCTLance paths at revision `905629a773f191108273a55924accd9f31145a8d`
  and accepts 14/14 rows across nine drivers after 36 sole-authority processes.
  All 114 directly runnable script tests pass. The separate 10 recipe tests
  cannot start in this environment because the `just` executable is absent;
  no recipe assertion ran or failed. Python compilation, JSON gates,
  byte-for-byte derived-report reproduction, documentation links, and diff
  hygiene pass.
  Raw v5 and derived validation JSON are retained byte-exact with SHA-256
  `a54333ba303517ea3cd6657572837fac69136439bb53d937fc76b907a7469a34`
  and `d068d3c2de89a1dbd29053caa3c137146e387be58d6d576f948178856be8b137`.

  **Validation (2026-07-18, ADR-0238):** all 20 changed-path runner/analyzer
  tests and all 98 directly runnable non-recipe Python tests pass. Strict
  all-target/all-feature `axeyum-bench` Clippy, all 54 all-feature benchmark
  tests, warning-denied benchmark docs, the lean QF_BV solver profile,
  workspace formatting, shell validation, documentation links, diff hygiene,
  and explicit JSON/hash assertions pass. Re-running the analyzer produces a
  byte-identical `6040c9f...` union report. Focused Glaurung extremum/parser
  tests pass under both sole-solver features, both release binaries build from
  the clean pinned source, and the five-patch mbox hash rechecks. Full Python
  discovery additionally identifies 10 recipe tests that cannot launch because
  `just` is absent from this environment; these are tooling errors rather than
  test assertions, and the 98 non-recipe tests remain green.

  **Validation (2026-07-18, ADR-0236):** workspace formatting, diff hygiene,
  all 93 directly runnable Python benchmark/gate/analyzer tests (including all
  15 authority-runner tests), strict all-target/all-feature `axeyum-bench`
  Clippy, all 54 all-feature benchmark tests, warning-denied benchmark docs,
  the lean QF_BV profile, and documentation links pass. Both committed report
  hashes recheck, and an independent artifact assertion confirms the rejected
  two-row any-model partition plus the accepted canonical output/counter
  equality and zero-inconclusive gate. The compressed mbox applies to the
  pinned Glaurung base and reproduces the measured source tree exactly. In
  isolated Glaurung builds, the three minimizer tests and two timeout-
  configuration tests pass under both
  `solver-z3` and `solver-axeyum`; the build repeats Glaurung's pre-existing
  unrelated warnings.

  **Validation (2026-07-18, ADR-0235):** stable formatting, strict
  all-target/all-feature `axeyum-bench` Clippy, all 54 all-feature benchmark
  tests, all 88 Python benchmark/gate/analyzer tests, warning-denied benchmark
  docs, the lean QF_BV profile, and documentation links pass. The bundled v34
  two-run analysis reproduces from its raw artifacts; the 1 ms control retains
  all 74 primary UNSAT rows as hard-timeout non-certifications with zero alarm.
  The pinned 162-query Glaurung regular gate again decides 162/162 under raw
  and canonical policies with zero disagreement, error, or replay failure
  (latest raw 0.699x Z3; canonical 0.317x; these one-shot semantic-smoke ratios
  are not fair warm headlines).

  **Validation (2026-07-18, ADR-0234):** stable formatting, strict
  all-target/all-feature `axeyum-bench` Clippy, all 51 all-feature benchmark
  tests, all 86 Python benchmark/gate/analyzer tests, the lean QF_BV profile,
  and documentation links pass. The bundled fail-closed analysis reproduces
  byte for byte from both raw v33 artifacts. The pinned 162-query Glaurung
  regular gate again decides 162/162 under raw and canonical policies with
  zero disagreement, error, or replay failure (latest raw 0.616x Z3;
  canonical 0.322x; these one-shot semantic-smoke ratios are not fair warm
  headlines).

  **Validation (2026-07-18, ADR-0232):** the ADR-0232 checkpoint passes the full
  serialized all-feature workspace and doc-test suite with zero failures,
  stable formatting, strict all-target/all-feature Clippy, warning-denied
  workspace docs, the lean QF_BV profile, all 76 Glaurung benchmark recipe/
  summarizer/comparator/gate/analyzer tests, the pinned 162-query Glaurung
  regular gate, foundational resources and generated dashboards, all
  rules-as-code generation/validation/query checks with zero generated drift,
  and documentation links. The regular gate decides 162/162 under both raw
  and canonical policies with zero disagreements, errors, or replay failures
  (latest raw 0.680x Z3; canonical 0.325x; these one-shot semantic-smoke ratios
  are not fair warm headlines). The host does not expose `just` globally, so
  the gate used the repository commands directly and the existing isolated
  pinned `just` 1.56.0 tool root for recipe dry-runs. Warning-denied docs also
  exposed and this checkpoint corrects one pre-existing unresolved
  `export_qf_bv_unsat_proof` intra-doc link.

  **Validation (2026-07-17):** the first parallel all-feature workspace test
  exceeded the shared 4 GiB envelope while several heavyweight test processes
  overlapped; the required serialized rerun (`CARGO_BUILD_JOBS=1`, one test
  thread) completes with zero failures, including all doctests. Stable
  formatting, strict all-target/all-feature Clippy,
  warning-denied workspace docs, the QF_BV profile, the pinned 162-query
  Glaurung regular gate, foundational resources, generated-resource drift,
  all 23 rules-as-code generation/validation/query checks, and documentation
  links pass. Both regular-gate policies decide 162/162 with zero disagreements,
  errors, or replay failures (latest raw 0.627x Z3; canonical 0.310x; these
  one-shot regular-gate ratios are semantic smoke, not fair warm headlines).
  All 69 benchmark recipe/summarizer/comparator/gate/analyzer tests pass after
  provisioning `just` v1.56.0 in an isolated temporary tool root. Strict
  current-nightly Clippy also exposed seven
  mechanical cleanup sites (byte-array literals, one redundant pattern, one
  suffix parse, and two needless match wrappers); those semantics-preserving
  edits are included in this checkpoint.

  **Validation (2026-07-15):** a clean, serialized `just check` at `623cae4c`
  completed under the 4 GiB memory cap with formatting, strict
  all-target/all-feature Clippy, the full workspace and doc-test suites,
  warning-denied docs, the lean QF_BV profile, all 31 Glaurung recipe/profile
  tests, the pinned 128-query representative Glaurung gate, foundational
  resources, generated-resource drift, and link checks green. The representative
  gate decided 128/128 with zero disagreements, errors, or replay failures. Its
  raw/current-integration result is Axeyum 0.181498 s versus Z3 0.169850 s
  (1.069x); canonical v4 is 0.050672 s versus 0.150092 s (0.338x). The gate
  refreshed five tracked frontier `solve_ms` curves; an ignored-timing
  comparison confirms their frontiers, decisions, and statuses are unchanged.

  A later post-T2 aggregate run passed the full format/Clippy/test/doctest/doc/
  QF_BV-profile/harness-test prefix under the same 4 GiB cap, then stopped at
  the real-corpus recipe because the new second package binary made its legacy
  `cargo run` ambiguous. `f6fcd81f` fixes that public-package integration with
  `default-run = "axeyum-bench"`. The exact failed stage and remaining tail
  were rerun successfully: both 128-query policies are fully decided and
  replay-clean (raw 1.222x, canonical 0.333x), followed by foundational,
  generated-resource, rules-as-code, and link gates. Five frontier artifacts
  changed only in measured `solve_ms`; frontier/decision/status structure is
  unchanged.

- **2026-07-14 — ADR-0141 lands exact source-term BV Skolem witnesses.** The
  checked `forall+ exists` SAT route now accepts one source-reachable,
  quantifier-free, same-width BV term over only the leading universals, encoded
  as one coefficient-one term with zero rational constant. Search proposes only
  an operand already opposite the existential in equality, `bvule`, or
  `bvsle`; the checker independently requires exact assertion reachability,
  arena identity, sort, binder scope, and untouched-source substitution to a
  reflexive complete body. Modular/bitwise terms and total UF applications such
  as `b := f(a)` therefore replay without a function table or a modular
  interpretation of rational coefficients. Detached, free-symbol, strict,
  nested, and non-reflexive recipes fail closed. Witness/certificate tests pass
  17/17 and 14/14. The 64-case Z3 BV matrix certifies all 48 intended SAT cases
  (eight agreed strict UNSAT, two safe Axeyum unknowns, six Z3 timeouts), and a
  separate 12-case quantified-UF matrix is jointly SAT/replayed at widths
  1--257. **Next:** extend the checked SAT boundary beyond one direct source
  term—piecewise or multiple dependent Skolems, or a separate function-model
  contract—while the real Glaurung payload and artifact-v25 reproduction remain
  the mandatory GQ1/GQ10 gate.

- **2026-07-14 — ADR-0124/0125 Lean alternation reconstruction is DONE under
  the 4 GiB release gate.**
  Reconstruction now preserves the exact `forall+ exists+ (antecedent ->
  consequent)` source proposition, discharges the antecedent by evaluation, and
  feeds the consequent into a local-let Alethe tail. Compact module emission now
  streams byte-identically to a temporary file before inference; scoped free
  variables close at their associated lambdas in one shared-DAG traversal; and
  ordinary free-variable abstraction skips subgraphs without a requested local.
  The trusted kernel checks the open skeleton with each marked local scoped only
  to its owning lambda, rejects an escaping local, and returns the mechanically
  closed proof. Complete application spines and expected lambdas avoid
  quadratic intermediate telescope copies. Exact direct/router equality is
  compared from a spool so both modules do not coexist in memory. The public
  `small-pipeline-fixpoint-3` gate passes in **81.57 s at 3,756,104 KiB peak**;
  the 530-binder `bug802` gate passes in **45.28 s at 2,186,192 KiB peak**. Both
  are below 4 GiB, contain genuine `Exists.rec`, and contain no `sorryAx`.
  Kernel 172/172 plus its doctest, focused Clippy, and non-stress routing pass;
  the scheduled `test-quant-bv-alternation-lean-stress` recipe owns both gates.
  Quantified-BV Lean UNSAT rises **14→16/18**. Next: ADR-0129 source
  elimination/introduction, then ADR-0127's compact reflected-RUP boundary.

- **2026-07-14 — ADR-0129 source reconstruction is DONE under the 4 GiB release gate.**
  The bounded route now rechecks the exact certificate, represents both
  untouched paired assertions, eliminates the positive witness with genuine
  `Exists.rec`, shares typed locals across positive/negative/alpha-aligned
  binders, regenerates unmatched QF_BV consequences, introduces the transferred
  witness with genuine `Exists.intro`, and closes against the untouched negative
  source. Identity and generic QF-proof cases kernel-check with exact
  direct/router module equality and no `sorryAx`. The public
  `nested9_true-unreach-call` residual has 2,430 commands and a live
  86-literal/411-premise RUP step; explicit resolution safely hit a 2.18 GiB
  allocation near the 4 GiB envelope. The route now declines before expansion
  above 64 literals or 256 premises. DAG-marked conjunction traversal,
  empty-clause backward slicing, and cached clause suffix propositions are
  landed. A continuation-coded clause proposition now converts each source/gate
  clause once, validates exact-order RUP or deterministic normalized unit
  closure, and constructs one locally shared falsified-literal continuation per
  propagation—no intermediate resolvent clauses. Wide-chain success and
  corrupted-conflict rejection both kernel-check, including deferred alias
  closure. Normalized clauses are cached at insertion. A minimized 4-bit version
  of the public three-conjunct/multiplication shape exposed the former scoped
  `TypeMismatch`: the route lowered the complete body as one shared AIG but
  projected it as the `And` of separately lowered leaves. Paired reconstruction
  now uses one structural conjunction proposition consistently from source axiom
  through `Exists.rec`, leaf transfer, and `Exists.intro`; the regression and
  authoritative scoped close pass. With the cap experimentally removed, the
  public release proof reaches module streaming in 211.18 s at 2,062,692 KiB
  peak under 4 GiB, but textual export exceeds the 14 GiB temporary filesystem.
  The final route preserves each witness-dependent gate proposition as an
  explicit scoped `let`, so CPS clause types reference a linear DAG instead of
  re-expanding open AIG trees. The trusted kernel context records let-bound
  local values separately and uses zeta equality during expected-type,
  application-spine, sort inference, proof-irrelevance, and
  definitional-equality checks; it retains the telescope
  rather than substituting the value through the complete proof. The 64/256 cap
  is removed. The public row emits a **106,809,049-byte** self-contained module
  and passes in **19.69 s at 2,078,224 KiB peak** under the 4 GiB release gate,
  with genuine `Exists.rec`/`Exists.intro` and no `sorryAx`. Kernel 174/174 plus
  its doctest and all 10 paired tests pass. **Lean rises 16→17/18. Next:** route
  ADR-0127 through the same compact reflected-RUP boundary.

- **2026-07-14 — ADR-0127 source reconstruction closes quantified-BV Lean
  UNSAT at 18/18.** A dedicated public proof fragment rechecks the exact
  conjunctive-universal certificate, represents the untouched source assertion,
  projects the selected conjunct, applies its complete typed witness tuple, and
  discharges the exact residual through the compact CPS Alethe route. LRAT hints
  are backward-trimmed to the conflict graph; every retained closed clause is a
  kernel-checked theorem declaration, deferred clause uses remain aliases, and
  logical AIG gates become explicit local `let`s so quantified subcircuits stay
  DAG-linear. Learned clauses never become axioms. The kernel expression
  interner now uses compact stable hashes, 64 shards, exact collision checks,
  and segmented arenas to avoid large contiguous reallocations. Focused routing,
  mutation, LRAT, ADR-0135, kernel, and Clippy gates pass. The authoritative
  `cond-var-elim-binary` release test finishes in **196.98 s** (**3:17.54** for
  the command) at **1,039,568 KiB max RSS** under the hard 4 GiB cap; its
  direct/router output agrees, is self-contained, contains no `sorryAx`, and is
  guarded below 128 MiB. Public quantified-BV Lean coverage rises
  **17→18/18**. The shared logical-AIG improvement also shrinks ADR-0129's
  module from 106,809,049 to **18,576,938 bytes** and its release gate to
  **4.10--4.21 s** (the measured no-rebuild peak is **419,460 KiB**). ADR-0129
  reconstruction now also owns a
  scoped 64 MiB worker stack; its complete debug file passes 9/9 instead of
  overflowing the test harness stack. **Next:** obtain and ingest the real Glaurung
  capture, establish the GQ1/GQ10 attribution baseline, and choose the first
  optimization only from that profile; continue broader nested/alternating QSAT
  and quantified-UF depth work independently.

  **Validation sweep:** the all-feature solver library/integration suite passes
  in full with one serial test thread under the hard 4 GiB cap, including all
  differential campaigns and the ADR-0127/0129 public routes. The remaining
  strings/verify crates and doctests also pass serially. A default-parallel
  workspace attempt exceeded the intentionally low cap in the FP harness; all
  55 FP library tests pass serially under that cap. Clippy across all targets
  and features and warning-denied rustdoc are green. The sweep regenerated the
  five tracked frontier curves: BV reduction advances **30→40** at the 4 s
  budget; LIA cuts 26, NIA UNSAT 40, NRA degree 40, and string bound 8 retain
  their declared frontiers. These host-local frontier timings are regression
  artifacts, not Glaurung performance evidence.

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
  external Glaurung capture is the primary 100%-decided client gate. Its
  producer-side manifest and artifact-v17 result are now visible, but the query
  bytes are not present in this checkout, so the 2.10x result has not yet been
  reproduced under artifact v25 and no parity claim is made. Next: obtain the
  manifest-bound payload, run `just bench-glaurung-qfbv`, and profile only
  comparable zero-error/zero-disagreement runs.

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
| P2.6a | Exact source-term BV Skolem depth | **DONE for the ADR-0141 slice:** a single direct BV existential may use one exact source-reachable QF term over leading universals; modular/bitwise/total-UF terms replay only after untouched-source reflexivity. General multiple/piecewise Skolems, free parameters, function-valued models, and SAT Lean export remain P2.6 work |
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
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — the general opt-in preprocessing foundation and model trail are landed; exact Glaurung canonical v4 reaches 0.730x Z3 on the standalone full capture. ADR-0157/0158 demand slicing are semantically green but out/off after real performance failures. ADR-0159 closes current structural extract attribution. ADR-0160/0161 attribute the native path and gate mix; ADR-0162/0163 accept direct-root fusion and exact context dedup, cumulatively cutting pinned incremental clauses 28.60%, with native wins of 4.52% then 2.10%. The residual is only 2.36%: lead with GQ7 and client-boundary reconciliation; profile AIG cost per node and continue CNF/rewrite work only from causal native evidence. SAT tuning is now a ranked follow-up at the reported 20% share. |
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
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — e-graph E-matching, trigger inference/MBQI/MBP, restricted checked Skolem/model/counterexample certificates, retained checked quantifier clauses, and incremental candidate-sensitive e-matching are live through ADR-0140. **Checked UNSAT routes (ADR-0095/0097/0099/0100/0101/0108/0124/0125/0126/0127/0128/0129/0134/0139/0140):** Euclidean residue, affine growth, nested XOR, concrete closed-universal counterexamples including universal falsifiers below proved-vacuous existential prefixes, exact finite equality partitions, source-instantiated free-Boolean covers, source-bound residual-QF_BV alternation counterexamples, evaluator-replayed negated-existential witnesses, premise-aware conjunctive and query-scoped positive universal instances, and paired-existential witness transfer each carry separate checks. **Checked SAT routes (ADR-0096/0098/0107/0121/0122/0123/0130/0131/0132/0133):** arena-stable affine/reflexive and guarded unit-gap Skolems, exact same-width BV identities, false outer-BV equality guards, free-Boolean Bool/Int models, Boolean-discharged opaque BV closures, and complete free-BV affine-LSB, negated-universal-witness, signed-interval negated-existential, and zero-product negated-existential models, and positive-universal residual-QF_BV free-Boolean models replay through canonical `check_model`; unresolved BV semantics never enter the LIA fallback. **Lean routes (ADR-0102 through ADR-0106, ADR-0108/0109/0124/0125/0127/0129/0135/0137/0138/0139/0140):** all eight decided LIA UNSAT rows reconstruct through genuine quantifiers and kernel-checked reasoning. Quantified LIA is 12/12, certified/rechecked/dominant 12/12, Lean UNSAT 8/8. The committed quantified-BV slice is 36 SAT / 18 UNSAT / 0 unknown / 0 unsupported, with 54/54 evidence-certified/rechecked, 50/54 dominant, and Lean UNSAT **18/18**. ADR-0137 closes the corpus-scale ADR-0134/0135 export gap, ADR-0138 constructs genuine typed witnesses for all three ADR-0126 public rows under guarded release gates, ADR-0139 applies a typed universal witness before an evaluated-AIG refutation for `qbv-simp`, ADR-0140 eliminates ADR-0128's vacuous existential prefix with genuine `Exists.rec`, ADR-0124/0125 reconstruct both source-bound alternation rows, ADR-0129 reconstructs the paired-existential public row, and ADR-0127 closes the final conjunctive-universal row through scope-checked compact CPS/RUP under 4 GiB. Remaining boundaries: broader nonvacuous existential relations and nested/alternating BV QSAT, SAT-side ADR-0130/0131/0132/0133 Lean theorem/model export, non-equality online antecedents/proof serialization, measurement-gated high-frequency callbacks, generation-cost scheduling/bytecode, quantified UF/function-valued models, multi-constant equality-partition proofs, and further open-context proof sharing; current bridge relevance is exact by construction. |
| P2.7 | Strings (unbounded, full `str.*`, regex) | WIP — **Phase A DONE** (ADR-0051 `Sort::Seq`; ADR-0052 `len`↔LIA link + bounded-unsat gate, repaired a measured wrong-unsat class). **Phase B core LIVE both directions (ADR-0053, landed 2026-07-03):** T-B.1 normalization → T-B.4a arrangement search → T-B.4b routing + parser dual-build → extended-fn reductions → T-B.4d word-first fallback → harness parity (**QF_S 52→78 across 07-03…06** — see the generated scoreboard, oracle-verified) → **T-B.7 slices 1–2**: word `unsat` ONLY via the independent derivation checker (`check_derivation.rs`, own union-find + walkers; word fuzz **96 sat + 305 unsat, DISAGREE=0**). Phase C derivative membership (ADR-0054), Phase D reductions, lex order, code↔LIA, #49 membership-over-concat, #53 LenAbs SAT, and #55 concat emptiness/joint search are landed; QF_S is 87/134 and QF_SLIA 18/50 on the committed scoreboard. Remaining declines are unsupported `to_int`/`replace_re`/`seq.*` machinery plus the ADR-0063 Nielsen-arrangement class; T-B.5 F-Loop/T-B.6 eager conflicts remain performance work. The canon/derivative deadline guard is closed. |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | WIP — the FP theory is broad already (classification, compare, abs/neg/min/max, add/sub/mul/div/fma/sqrt/rem/roundToIntegral, fp→fp resize, fp→real/ubv/sbv). min/max ±0 confirmed correct (deterministic allowed choice). **Added integer→float conversion** (`from_ubv`/`from_sbv`, 2026-06-18): rounds a w-bit unsigned/signed-two's-complement integer to a dst float under a rounding mode (reuses `pack_value`; exact 0→+0; |x| via two's-complement read unsigned, correct for INT_MIN). Differential-tested vs Rust's native `as f32`/`as f64` (i32/u32→F32, i64/u64→F64; edges + 3000-case sweep, exact). Completes the `to_fp` family on the builder side. Remaining: SMT-LIB parse wiring for `(_ to_fp …)`/`to_fp_unsigned` over bv sources (axeyum-smtlib, coordinate); `to_fp` from real constants; unspecified-value edge polish |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | WIP — **structural refutation** (`prove_datatype_unsat_structurally`): acyclicity + distinctness + injectivity **+ congruence** (equal args ⇒ equal apps, e.g. `x=cons(h,a) ∧ y=cons(h,b) ∧ a=b ∧ x≠y`) + constructor exhaustiveness over a term-level union-find; also flattens top-level conjunctions and refutes top-level `or` when every branch is structurally contradictory. Sound, wired into dispatch/evidence/Lean reconstruction ahead of the eager expansion; the cvc5 QF_DT exact audit is now 3/3 dominant with Lean unsat 3/3. 13 focused tests. Remaining: e-graph constructor *splitting* (case-split `is-c` on the keystone) for SAT-side completeness; exact field guards to remove the relaxed `unknown` cases; broader datatype corpora beyond the cvc5 three-row slice |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P3.6p | `Prop` large-elimination soundness incident | **DONE / contained (ADR-0165, `d26ad887`, `a10c8cde`, `de249d48`)** — exact Lean syntactic-subsingleton test; restricted motive universe and arity for other potentially-`Prop` families; complete exploit inverted; positive/negative/exact-index/polymorphic/generated-matrix coverage; pinned mandatory real-Lean flat-inductive/iota CI gate; downstream `Or.rec`/`Exists.rec` reconstruction aligned and the complete 4 GiB serialized `just check` gate green. Full recursive-indexed `Acc` remains an honest pre-existing fragment deferral, not a soundness exception |
| P3.6 / TL2.12 | Recursive indexed/reflexive induction hypotheses | **DONE (ADR-0353 accepted)** — one `Pi telescope, motive indices (field args)` rule covers direct, indexed, higher-order, and combined native fields. M0-M3 freeze the streams, close fourteen native rows/twelve mutation classes/768 recursive profiles, and complete both construct targets with exact recursor comparison. M4 confirms pinned Lean and Axeyum computations twice at `MiniNat.succ MiniNat.zero` and `True`; the generated matrix has four admitted, two computation-checked, and two declined rows. M5 closes every bounded gate. Mutual groups followed in TL2.13; a later audit separates TL2.14 kernel nested elimination from TL4.9/TL4.10 source elaboration. |
| P3.6 / TL2.13 | Mutual inductive groups | **DONE (ADR-0354 accepted)** — M0 freezes the exact source, two byte-identical official streams, semantic/wire-order contract, and no-product boundary. M1-M4 land ordered representation, native complete-group semantics across 18 public rows, the byte-identical 720-case grammar, exact official import/computation, and 22 rejecting importer/publication mutation classes while retaining the 768/840 controls. M5 adds the history-preserving assurance overlay (5 admitted, 3 computation-checked, 1 current decline), removes the obsolete live decline, and closes every bounded gate. |
| P3.6 / TL2.14 | Nested-inductive kernel elimination | **DONE (ADR-0355 accepted after containing-commit publication)** — M0 freezes three explicit computations and 114,596 bytes / 2,022 records without product observation. M1 establishes typed non-admission. M2 implements native fixed-point expansion/restoration and exact `.rec_N` publication. M3 repeats the exact 640-case grammar twice at digest `a20fe056c9443a37`, observes exact dependency/iota surfaces, and closes 16 transactional mutations plus the bounded integrity amendment. M4 derives auxiliary identity from checked motives, imports the construct plus all three frozen computation streams twice at 22/34/34/34 declarations and zero axioms, and closes 20 wire/publication classes plus order non-authority. M5 checks the registered 3/3/5-successor normal forms twice, appends the history-preserving current assurance overlay (7 rows / 6 admitted / 4 computation-checked / 0 current declines), and removes only the obsolete live nested decline. M6 closes exits 1--11 and every non-publication component of exit 12; the containing commit's push/ref equality completes the decision. Complete suites and exact 640/720/768/840 and well-founded 35/0 controls pass. Native source elaboration remains TL4.9/TL4.10. |
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
| P3.6 / TL2.2-TL2.7 | Projection representation, inference, reduction, exact K1 import, structure eta, and checked arbitrary-precision Nat literals | **DONE for the direct slices** — `Proj(NameId,u32,ExprId)` is structurally complete; checked metadata drives dependent inference and eta eligibility; WHNF selects constructor fields; format-3.1 translation admits/computes the exact official projection root with mutation rejection; symmetric eta passes native and pinned-Lean controls; `NatLit(BigUint)` removes the width ceiling; checked bootstrap typing, constructor-offset equality, successor reduction, and recursor conversion admit/compute the exact official Nat root. Generated TL2.15 projection/reduction/eta and quotient semantics remain. The kernel gate passes 179 unit tests plus 35 integration cases across twelve binaries; the expanded importer gate passes 28 tests across three binaries. |
| P3.6 / TL1.3 | Owned completed import publication | **DONE** — `import_ndjson` owns private staging state and publishes `CompletedImport` only after full success. Appended JSON, final kernel rejection, quotient, late record-limit, and post-byte-stream I/O failures return no partial environment. Existing exact K1 results remain unchanged; its 20-case checkpoint passed before TL1.4 expanded the importer suite. |
| P3.6 / TL1.4 | Generated format-3.1 mutation corpus | **DONE** — 226 unique deterministic cases run twice with exact stable counts: 67 JSON, 90 malformed, one kernel, one format decline, three positive, and 64 published-unsealed. Every official record body rejects truncation; complete-record prefixes remain explicitly unauthenticated because the upstream format has no footer. Its checkpoint total was 23 cases across two binaries. TL1.7 subsequently landed. |
| P3.6 / TL1.7 | Canonical imported declaration and dependency identity | **DONE** — `ImportReport` publishes TL0.4-compatible axiom identities plus complete domain-separated v1 structural content and sorted direct-dependency bindings for all seven declaration variants. Five focused tests freeze all eight flat-fixture rows and prove repeated/reordered identity, valid type/body/binder mutation sensitivity, and dependency propagation. Importer total is 28 cases across three binaries. |
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
| P4.1j | Glaurung warm delta and duplicate/prefix reuse (GQ7/GQ8) | **DONE for current serial/source-direct families and native continuation admission; wider direct-delta admission deferred.** ADR-0186/0192/0193/0195/0196/0199 establish adaptive snapshot ownership and serial LCP reuse. ADR-0201--0205 accept first-class source deltas and the two-driver production win. ADR-0206--0211 close the concat error class, reject cold retry, and admit low-memory continuation through the exact tcpip gate. ADR-0212 adds complete `dxgkrnl` no-op functionality but rejects default admission because ordinary-core variance exceeds 3% and slower-core outcomes drift. Glaurung `9ace064` still defaults continuation only inside separately selected direct delta. Keep direct delta opt-in; rerun the exact wider gate in a quieter environment or on another valid IOCTL driver. `win32k` belongs to a future system-service/callout frontend. |
| P4.1e | Retained warm Boolean array relation flags | **DONE (ADR-0091)** — symbolic-memory path conditions can keep nested supported array equality atoms warm through private candidate-sensitive relation flags, guarded equality/diff observations, projection filtering, and replay |
| P4.1h | Retained warm nested array-valued UF parameters | **DONE (ADR-0094)** — nested supported array-valued memory/function parameters can stay warm as full-value UF keys through private projection keys or rewritten structural keys, with relation-flag guarded congruence, private filtering, and replay |
| P4.1g | Retained warm structural array-valued UF parameters | **DONE (ADR-0093)** — supported store/constant/array-ITE memory/function parameters can stay warm as full-value UF keys with scalar dependency retention, structural owner realization, relation-flag guarded congruence, private filtering, and replay; ADR-0094 subsequently lands nested application keys |
| P4.1f | Retained warm direct array-valued UF parameters | **DONE (ADR-0092)** — direct finite-array memory/function parameters can stay warm as full-value UF keys with relation-flag guarded congruence, deterministic distinct key projection, private filtering, and replay; ADR-0093 subsequently lands supported structural array keys |
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | WIP — committed assertions and one-shot assumptions over arrays/UFs route through memory-aware APIs with original-term replay/core reporting. The warm path now admits reducible ROW and array-ITE readbacks, retained BV-indexed Bool/BV selects, scalar UF applications, scalar-keyed array-valued UF parents (ADR-0088), projection equality and exact structural disequality witnesses (ADR-0089), top-level positive structural equality over supported store/constant/array-ITE parents through private constructor owners plus class-aware realization (ADR-0090), nested Boolean array-relation flags (ADR-0091), direct array-valued UF parameters (ADR-0092), supported structural array-valued UF parameters (ADR-0093), nested array-valued application keys (ADR-0094), and memory-aware k-induction through eager memory elimination. `SymbolicExecutor` and `SymbolicMemory` use these warm abstractions before falling back to the full dispatcher. Remaining: certified memory k-induction, memory PDR/IMC, path-condition CFG/import frontends, nested/extended arrays, deeper memory helpers, online proofs, and broader performance measurement |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | WIP — first frontend-facing primitives landed: `SymbolicMemory` wraps an SMT array memory state, builds `select`/`store`, routes load-equality branch/assume queries through `SymbolicExecutor`'s automatic warm/memory feasibility APIs, and now exposes conservative write-log normalization / compact read-specific read-over-write `ite` construction for frontend memory logs that skips literal-distinct writes, elides exact-hit guards, preserves later symbolic aliases, and uses the auto route; `SymbolicExecutor::assume_auto` and `SymbolicExecutor::branch` keep same-index store/read-back constraints, literal-distinct concrete-address store-chain misses, zero-initialized constant-array reads, simple array-ITE state-merge reads including same-readback merge-guard and tautology pruning, reducible conditional read/write-index paths with scalar equality-over-`ite` cleanup, symbolic Bool readback equality/connective/xor/implication cleanup, BV bitwise/arithmetic/comparison/slice-extension/shift/div-rem readback cleanup, reducible symbolic-address ROW over store chains with same-index shadowed-store pruning, plain symbolic-base Bool/BV array loads via retained select-congruence abstraction including wide/BV256 index or element projection, direct equal-array symbol assumptions/assertions via retained cross-array select congruence and equal-array model projection, scalar Bool/BV UF applications via retained congruence abstraction including wide/BV256 argument or result projection, helper-level load/write-log queries, and default `explore_cfg` branch/assume/status/model queries on the warm BV path when they reduce or abstract, with original-term replay, while remaining general memory/UF still auto-promotes to the memory/theory-aware route; `SymbolicExecutor::explore_cfg` provides a reusable DFS harness over frontend-supplied CFG states, with solver-scope management, infeasible pruning, unknown-safe traversal, and model-witnessed targets; `explore_cfg_checked` adds frontend-supplied concrete witness extraction + replay callbacks and buckets targets into verified/missing-witness/mismatch cases; `TinyBvProgram` is the first reusable small-target frontend, with a validated BV register/memory IR, label-aware line-oriented assembly import with retained label/source metadata, deterministic PC-to-label lookup, typed static CFG edges and basic blocks, deterministic Graphviz DOT export for the basic-block CFG plus trace-highlighted, block-coverage-highlighted, and edge-coverage-highlighted DOT overlays, block-level trace paths, taken-edge trace reports, source-aware trace rows, consolidated witness trace reports, replay-checked test-case generation reports, block-coverage and edge-coverage test-suite reports, register-register equality branches, symbolic instruction lifting, zero-initialized SMT array memory for `Load`/`Store`, model-witness extraction, independent concrete replay, concrete execution traces, and bounded PC/label reachability/safety reports. Remaining: byte-level/binary broader target work, unbounded/certified safety wrappers over richer CFGs, and eventually general warm memory reuse from P4.1 |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | WIP — single-objective `maximize/minimize_lia` + `_bv`/`_bv_signed` already shipped (exponential+binary bound search, Boolean-structured oracle). **Lexicographic multi-objective landed** (`optimize_lia_lexicographic`, 2026-06-18): optimize objectives in order, pinning each at its optimum (`obj≥v`/`obj≤v`) before the next so later ones range over the optimal face — z3's default lex combination. Sound + terminating (bounded composition of the checked single-objective optimizer); `LexOutcome::Stopped` at the first unbounded/infeasible/unknown objective. **BV lexicographic also landed** (`optimize_bv_lexicographic`, signed/unsigned, `bv_uge/ule/sge/sle` pinning) — lexicographic OMT now covers both LIA and BV. **Box** (`optimize_lia_box` / `optimize_bv_box`, independent) **and Pareto** (`optimize_lia_pareto` / `optimize_bv_pareto`, guided-improvement front enumeration, deterministic point/push caps, each point verified Pareto-optimal) modes also landed — **axeyum now has all 3 of z3's OMT modes (box, lexicographic, pareto) across LIA+BV**. BV Pareto covers unsigned and signed objective values, max/min directions, and graceful `Unknown` for out-of-fragment objective values. MaxSAT returns the witnessing model (`max_satisfiable_model`). `minimize_model` / `Solver::minimize_model` provide replay-checked lexicographic counterexample minimization over selected Bool, unsigned-BV<=127, and Int symbols, and the metadata-aware `minimize_model_objectives` / `Solver::minimize_model_objectives` route adds signed two's-complement BV objective order for signed SDK inputs. `produce_evidence_minimized` / `prove_minimized` preserve the default surface, while `_with_objectives` variants expose signed-objective metadata to frontends. `axeyum-property` v0 is now the first typed SDK consumer of that surface: Bool/BV/Int handles, assumptions, proof calls, minimized countermodel lifting, checked `EvidenceReport` exposure plus best-effort standalone Lean modules and stable evidence/trust/Lean summaries through `ProofCertificate`, typed BV overflow predicates, `.equals()` equality aliases, property-owned Bool/BV/Int builder aliases, `Property::all` / `Property::any` Boolean folds, deterministic native-scalar counterexample-to-`#[test]` rendering with caller-owned prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, deterministic multi-case fixture file assembly, direct named/tuple aggregate initializer snippets, and explicit nested aggregate field composition, scalar/tuple/derived-struct `Symbolic` declarations/lifting including signed-order two's-complement fixed-width Rust integers, named-field `symbolic_struct` bundles, and the generated SDK corpus/scoreboard gate with 16 graduated workflows, deterministic executable baseline comparisons for scalar counterexamples, an actual fixed-seed proptest shrunk counterexample, struct and replay counterexamples, proved assertions, assumption-backed proved assertions, and a Kani-style assume/assert counterexample baseline, machine-readable `corpus.json`, DISAGREE=0, and 1/1 Lean-required coverage. Remaining: MILP hardening; broader objective support for minimized counterexamples beyond Bool/BV/Int native scalars; property SDK ergonomics (operator traits, richer replay bodies); richer proptest families and real Kani CLI-backed property corpus comparison; differential validation vs Z3 `opt` |
| P4.4 | SMT-LIB command/API conformance | WIP — the checked 30-row API matrix records 27 rows with exact tests, 6 absent families (including SMT-LIB 2.7 `declare-sort-parameter`), 7 accepted no-ops, and 0 interactive textual-session rows. The follow-up SMT-LIB 2.7 contract prototype passes 14 invariants and 20 abstract fixtures / 107 commands, and corrects the architecture estimate: default/global declaration and definition scope, `reset-assertions`, full-reset arena epochs, exact query snapshots, post-`unknown` inspection, immediate options, and atomic continued errors all precede rendering. Proposed ADR-0342 gates S1 complete ordered command/event capture; production behavior remains unchanged. Later gaps are canonical adapters, parametric sorts, recursive definitions, textual categorical commands, and separately scoped general SyGuS. |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | **WIP: correctness/deployability evidence, neutral warm controls, exact cold attribution, proof denominators, authoritative-policy gates, selected-pair symbolic-CVE recall, and negative harder-driver/duplicate-clause/storage/memo results are complete through ADR-0300; ADR-0302 now passes its run/backend gates on one machine but has not completed the required cross-machine recall-reproducibility matrix.** ADR-0272 rejects performance leadership because warm Bitwuzla wins all four fair drivers. ADR-0273--0275 retain the harder-driver census as incomplete-work negative evidence; ADR-0277 removes its structurally exact candidate after the frozen variance/family gates fail. ADR-0285's flat CNF arena preserves all correctness and exact construction identities and reaches a favorable 0.540824 aggregate logical-storage ratio, but fails its frozen per-instance <=80% gate on 5/162 payload-dominated singleton-clause rows. ADR-0300's dense memo preserves all registered structure and shows favorable bit-blast/cold-total point estimates, but fails the <=3% run-total CV gate (3.0023% BTree, 6.8664% dense); production is restored to BTree and the 12-run negative artifact is retained. ADR-0302 distinguishes exact authority-report stability, backend finding/work identity, and replay-valid model diversity and requires two genuine machines. Broader labeled recall and honest correctness/deployability/proof framing remain open; no warm-speed headline, post-observation rerun, or concretization/symbolic-memory reopening is authorized. |

### Track 5 — Verified Systems (IR reflection) — ADR-0056, adopted 2026-07-06
| Phase | Title | Status |
|---|---|---|
| P5.1 | Reflection front end (crate-ify the MIR+LLVM reflectors, full `.ll` parser, MIR extraction pipeline, loops→`TransitionSystem`, memory beyond byte arrays) | WIP — **T5.1.1 DONE (`cc695925`, ADR-0057)**: the reflectors are now the real library module `axeyum_verify::reflect` (`src/reflect/{mod,mir,llvm}.rs`, submodules `reflect::mir`/`reflect::llvm`), no longer per-test scaffolding — 8 test binaries (62 tests) rewired to `use axeyum_verify::reflect::…` and green, `missing_docs`+`implicit_hasher` API-hardened, clippy/rustdoc `-D warnings` clean; the crate split is deferred (one consumer today). The prototyped *capability* (rounds Q–U, design log `docs/consumer-track/verify/reflect-common-abstraction.md`): CFG symbolic executors for both IRs over one shared op vocabulary; 16 cross-IR equivalence proofs (MIR≡LLVM per function, LLVM O0≡O2, if-conversion/strength-reduction/umin-idiom validated, hypothesis-gated `unreachable`); 5-shape wrong-transform refutation corpus with replay-checked countermodels; exact panic specs from rustc's own checks (overflow, division `b==0` / signed `∨ (a==MIN ∧ b==-1)`, array bounds over all 2^64 indices) with `catch_unwind` witness replay; checksum micro-module end-to-end on both platforms. **T5.1.2 WIP (ADR-0279--0284/0295):** accepted slices provide a non-panicking LLVM function boundary, typed scalar instructions including opt-in exact direct-body calls, explicit value+definedness, typed PHIs/terminators, bounded checked acyclic execution, and canonical render/reparse. **T5.1.3/T5.1.5 WIP (ADR-0286--0289):** exact direct-rustc capture/replay and explicit locked Cargo manifest/package/target selection now feed the named located checked path; two Cargo runs reproduce 1,438 bytes and typed/term JSON, while LLVM/direct MIR/Cargo MIR carry the same initialized four-byte store/load contract with explicit safety, final-memory joins, and source replay. **T5.1.4 WIP (ADR-0291/0292/0295/0299 accepted):** the canonical scalar LLVM self-loop, first single-latch natural loop, two exact PAC loops with a supplied checked `leaf` body, and the exact modular MIR checksum call route to checked semantics. Exact compiler identity, deterministic PHI/parameter/path/call state, selected-edge/call/poison/UB/panic semantics, unbounded/bounded safety exercise, independent formulas, differential rows, precise rejection boundaries, and source-replayed witnesses pass. Existing solver BMC supplies bounded unrolling for accepted relations; measured broader rejected-loop routing remains open. **T5.1.6 DONE (ADR-0290, expanded by ADR-0295--0299/0315):** all 81 source-derived semantic variants retain exact proof+fuzz ownership; 96 scalar goals / 11,248 rows, 11 cross-IR pairs / 110,000 tuples, five base refutations plus direct-call/contract/requirement/havoc/panic-summary mutations, checker mutations, and the expanded ten-binary/117-test gate pass. Remaining T5.1.3–5: general MIR places and wide/aliased memory, `stable_mir`, and broader rejected-loop routing. Individual proofs are milliseconds — the suites already run as ordinary per-commit tests |
| ↳ P5.1 measured gate | Glaurung LLVM loop-shape demand census | DONE — **ADR-0293 accepted:** exact result reproduces 12 loops / 12 functions: 11 existing self-loop structural rows plus one under-diverse early-exit row; no new implementation selected |
| ↳ P5.1 measured gate | Glaurung LLVM loop semantic census | DONE — **ADR-0294 accepted:** disclosed first-artifact rejection followed by exact corrected reproduction; 0/12 reach loop reflection, and diverse first causes select a T5.1.2 audit lane but no code |
| P5.2 | Contracts & modular verification (`#[requires]`/`#[ensures]`, calls as composition) | WIP — ADR-0295 accepts the checked direct-body/inlined baseline. **ADR-0296 accepts the first actual composition rule:** one exact scalar `leaf` contract is checked against its body once and the body is discarded. **ADR-0297 accepts nontrivial requirements without silent pruning:** `trans` assumes the requirement only after its exact reached complement becomes a replayable, source-attributed `bad` state. **ADR-0298 accepts the LLVM checksum continuation:** a fresh straight-line result plus a separate verified relation, weak-contract havoc teeth, and 100,000 valid plus 100,000 violating choices. **ADR-0299 accepts the MIR counterpart** with independent checked-body postcondition and panic-freedom proofs before body discard, separate havoc, and the same 200,000-choice gate. **ADR-0315 accepts input-dependent MIR panic composition:** the exact callee predicate joins caller panic and guards the normal-result relation, matching an inlined specification on all 256 `u8` inputs. **ADR-0316 accepts the source-local annotation surface:** typed pre/post terms retain the scalar result and distinguish normal postcondition replay from panic replay across all 256 `u8` rows. **ADR-0317 proposes the authenticated first join:** a total annotated wrapping function must produce the existing typed summary and independently verify against exact owning-build MIR. Phase exit still requires that proposed bridge to pass before authenticated source annotations feed checked modular summaries; DISAGREE=0 holds on every accepted modular/inlined population. |
| P5.3 | Kernel obligations: bounded memory/page-table math, 2-safety/constant-time via self-composition, protocol-FSM refinement | **DONE (bounded v1, ADR-0322)** — **T5.3.1 branch leakage (`ac7494f0`)** proves public-predicated and branch-free controls and refutes a secret-predicated witness from committed MIR text; memory-index/LLVM leakage and compiler authentication remain. **T5.3.2 (ADR-0320)** authenticates an 8,218-byte compiler MIR module with seven universal claims, three replayed controls, and 4,096 exact rows; it is not an MMU. **T5.3.3 (ADR-0321)** authenticates a 2,691-byte compiler MIR module with eight per-event groups, complete relation equality, two PDR-safe systems, a replayed buggy control, and 2,048 exact rows. **T5.3.4 (ADR-0322)** publishes the bounded obligation catalog and comparison index. Named residuals remain future evidence-gated work. |
| P5.4 | Fuzz-oracle loop (reflections as differential oracles, countermodels as seed corpora + generated `#[test]`s, honest `unknown`→directed-fuzz handoff) | WIP — **T5.4.1 DONE (`2423eaeb`)**: `reflect::oracle::DiffFuzz` is the reusable deterministic differential-fuzz harness; cross-IR and checksum suites use it with DISAGREE=0. **T5.4.2 DONE (`873c671e`, `75971d1d`, `1efa7f25`; ADR-0339):** three replay-checked countermodel classes produce exact canonical JSON and compiled generated regressions; native full-width scalar/array rendering, ordering, fail-closed errors, and mutation teeth are tested. **T5.4.3 WIP (`3d75d407`, proposed ADR-0340):** the public reason-preserving hybrid API and guarded deterministic QF_BV `fuzzed-only` runner are implemented; 4 unit + 3 integration tests cover branch/callback separation, replay/disagreement failures, repeatability, width-128 safety, JSON escaping, and independent embedded-query semantics. Remaining before acceptance: frozen rejection-family matrix, exact fixtures/mutation hashes, and all capped gates; then convert the `llvm_reflection` residual and separately define T5.4.4 coverage accounting |
| P5.5 | External target, measured | **DONE (bounded v1, ADR-0323--0338):** authenticated Tock capture plus eight rechecked dual-DRAT proofs and six replayed controls, UNKNOWN=0, DISAGREE=0. Query time 12.700 s; fresh outer wall 50.745 s; peak RSS 1,256,496 KiB; zero OOM deltas. The committed case study compares exact target validation, universal coverage, trust, effort, artifact boundaries, and limits. No Tock bug was found, so no upstream issue is applicable. This is not a speed or whole-kernel claim. |

## Changelog

- **2026-07-22 — Completed TL0.7.1's contract-only Lean execution authority.**
  Two explicit local lanes, twelve evidence-gated termination classes, seven
  immutable record families, five synthetic lifecycle controls, and nineteen
  mutation classes validate with every real result counter at zero. Process
  launch/cleanup and forced exit/signal/timeout/limit evidence remain TL0.7.2.

- **2026-07-22 — Preregistered TL0.7 execution-resource and completion
  evidence.** The plan separates lane policy, immutable run identity, attempts,
  per-case artifacts, and completion-last closure; freezes 4/8 GiB local lane
  templates and twelve typed termination classes; and forbids guessed OOM,
  runner-label hardware inference, JUnit-only completion, or synthetic parity
  credit before implementation.

- **2026-07-22 — Completed TL0.6.2's bounded official CI profile authority.**
  The isolated pinned workflow evaluator closes 17 contexts, nine active jobs,
  153 candidate cells, 85 primary plus 26 rebootstrap attempts, and eight exact
  CTest selection sets. Fresh pinned-source capture and independent synthetic
  CTest filtering agree with the committed authority. Every attempt remains
  `not-run`, so U2 stays bounded with zero official/Axeyum execution or paired
  credit; TL0.7 and TL0.6.3 are next.

- **2026-07-22 — Preregistered TL0.6.2 official CI profile derivation.** The
  source identities, context closure, candidate-cell schema, CTest and
  rebootstrap rules, selection factoring, mutation matrix, outputs, and stop
  conditions are frozen before implementation or derived profile counts. U2
  remains bounded and records no execution or paired-result credit.

- **2026-07-22 — Preregistered the live-blocked ADR-0356 S4 auditor.** The new
  independent standard-library path validates exact prior-stage artifact sets,
  performs the full path-sorted decision/corpus/history join, checks per-logic
  quotas against the official producer, and rehashes every selected file. It
  publishes completion last to a completion-hash-addressed root; verify mode
  reconstructs all 450,472 rows and rehashes the selected population again.
  Six focused tests cover the closed terminal-reason map, cross-stage field and
  byte identities, the zero-selected trivial `QF_UFFP` case, canonical selected
  order, published-decision drift, and all 18 registered rejecting mutations.
  The implementation remains live-blocked until this commit is pushed.
- **2026-07-22 — Completed TL0.6.1's bounded U2 official-test registration
  authority.** Pinned Lean's executable CMake/CTest semantics reproduce 3,678
  default and 3,723 full-Lake registrations with exact commands, properties,
  content, sidecars, output policies, support scopes, and selection digests.
  The 3,660 pile candidates close as 3,639 registered and 21 excluded. The
  machine-readable capture, generated reports, eight fail-closed tests, local
  aggregates, and docs CI all preserve the boundary: official executions=0,
  Axeyum executions=0, paired cells=0. U2 is a bounded profile, not a complete
  authority; TL0.6.2 official workflow-profile derivation is next.

- **2026-07-22 — Completed the twice-repeated ADR-0356 S3 official producer.**
  The first live attempt ran only after implementation commit `38c5f2af` was
  pushed. Both exact 88-file bundles, hash-required 14-package environments,
  three-cache sets, and pinned one-thread Polars 1.39.2 runs produced the same
  45,905 selected paths: 2,709 new and 43,196 old across 88 logics. The selected
  bytes have SHA-256
  `49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b`.
  A fresh standard-library process rehashed both complete runs and every
  completion dependency. The compact result is
  [recorded here](docs/plan/smtcomp-official-selection-producer-s3-2026-07-22.md).
  `selection_observed=true`; independent S4 is next.

- **2026-07-22 — Implemented the preregistered ADR-0356 S3 official producer.**
  The live-blocked entry point binds S1 and S2 completions, copies and rehashes
  exactly 88 authority files into each of two no-Git bundles, derives the
  minimal 14-package runtime closure from the frozen Poetry lock, and installs
  only hash-listed artifacts. It freezes CPython 3.11.15, uv 0.11.1, Polars
  1.39.2, one Polars thread, and the exact organizer `create_cache` AST before
  invoking `smtcomp.selection.helper`. Five bounded tests cover bundle drift,
  extras/links, dependency/hash drift, decorator-free cache AST extraction,
  path/order mutations, and repetition drift. The implementation must be
  committed and pushed before the first official sample is observed.

- **2026-07-22 — Completed ADR-0356 S2 verified corpus acquisition.** The
  fresh retained attempt verified all 90 SMT-LIB 2025.08.04 release files,
  4,890,207,406 compressed bytes, and 89 safely extracted logic trees. Its
  disk-backed join proves exactly 450,472 regular corpus files totaling
  82,270,961,563 bytes with no missing, extra, duplicate, linked, traversing,
  or cross-logic entry. Canonical `archives.json`, `corpus.jsonl`, and
  `summary.json` hashes are rooted by completion payload
  `1d22d99635587f2ac743af85a30ff753ee60ad1f81f31ac911cb8c5932b998d1`.
  A separate fresh process rehashed all archives and all 450,472 extracted
  files and reconstructed every count. The compact result is
  [recorded here](docs/plan/smtcomp-official-selection-corpus-s2-2026-07-22.md).
  `selection_observed=false`; S3 has since completed.

- **2026-07-22 — Seeded TL0.6's fail-closed complete-Lean-parity registry.**
  The exact U0-U9 populations, A0-A11 axes, eight paired outcomes, and G1-G10
  terminal gates now have one validated machine-readable source and generated
  Markdown/JSON reports. The generator content-identifies its source manifests
  and derives K-profile, selected-construct, implementation-task, and axiom
  summaries without converting them into terminal denominators. Eight
  contract/mutation tests reject population/order drift, incomplete denominator
  credit, complete axes over incomplete populations, hand-promoted derived
  gates, malformed paired identities, missing evidence, and terminal-claim
  laundering. Local
  aggregate and both docs CI jobs check the generated reports; live public
  status surfaces cannot affirm complete Lean parity while the terminal gate is
  open. Current terminal credit remains honestly zero across complete
  populations, complete axes, paired cells, and satisfied gates.

- **2026-07-22 — Seeded TL0.6's fail-closed complete-Lean-parity registry.**
  The exact U0-U9 populations, A0-A11 axes, eight paired outcomes, and G1-G10
  terminal gates now have one validated machine-readable source and generated
  Markdown/JSON reports. The generator content-identifies its source manifests
  and derives K-profile, selected-construct, implementation-task, and axiom
  summaries without converting them into terminal denominators. Eight
  contract/mutation tests reject population/order drift, incomplete denominator
  credit, complete axes over incomplete populations, hand-promoted derived
  gates, malformed paired identities, missing evidence, and terminal-claim
  laundering. Local aggregate and both docs CI jobs check the generated
  reports; live public
  status surfaces cannot affirm complete Lean parity while the terminal gate is
  open. Current terminal credit remains honestly zero across complete
  populations, complete axes, paired cells, and satisfied gates.

- **2026-07-22 — Implemented ADR-0356 S2 verified corpus acquisition.** The
  new resumable runner binds the completed S1 audit, downloads all 90 release
  files with published size/MD5 and local SHA-256, records redirects, rejects
  unsafe tar members, atomically promotes one regular-file-only logic tree at a
  time, and joins extracted bytes to metadata through a disk-backed unique
  index. It writes canonical archive/corpus/summary artifacts and completion
  last. Three focused extraction/inventory tests raise the bounded gate to
  41 tests. The implementation is committed before the first 4.89 GB run.

- **2026-07-22 — Completed ADR-0356 S1 independent input audit.** The fifth
  fresh S1b run verified 89 pinned inputs, normalized 450,472 metadata rows
  across 89 logics, reduced 5,345,294 historical rows, and published a
  256,182,191-byte canonical eligibility ledger. It reports 3,445 eligible new,
  249,915 eligible old, 197,112 trivial, zero matched removals, and aggregate
  cap 45,905 split 2,709 new / 43,196 old. A fresh-process checker rehashed
  every input and completion dependency and reconstructed the counts. The
  compact result is
  [recorded here](docs/plan/smtcomp-official-selection-input-audit-s1b-2026-07-22.md).
  `selection_observed=false`; S2 has since completed.

- **2026-07-22 — Added bounded canonical ordering for the S1b ledger.** The
  fourth retained attempt passed the 89-input and 450,472-row metadata gates,
  then reduced 5,345,294 historical rows across 2018--2024 before rejecting the
  organizer's noncanonical metadata order. The second metadata pass now writes
  bounded sorted chunks and merge-iterates them by normalized benchmark ID.
  The retained full input proves an exact 450,472-row strict ordering. The
  failed attempt is
  `/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744715221056942-32ecd649`;
  no official sample was generated or inspected.

- **2026-07-22 — Recorded the official removal anti-join as idempotent.** The
  third retained S1b attempt streamed all 450,472 metadata rows, then rejected
  because the independent runner expected both configured removal IDs to be
  present. Neither is present in the pinned metadata; the organizer's anti-join
  therefore removes zero rows. The contract now distinguishes configured from
  matched removals and freezes the exact zero-match fact. The retained negative
  is
  `/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744522957943433-eb81e506`;
  no historical reduction or official sample was completed or inspected.

- **2026-07-22 — Matched the organizer's two-stage logic expansion.** The
  second retained S1b attempt verified all 89 corrected inputs, then stopped
  before metadata reduction on `QF_AUFBVLIA`: it is a valid organizer logic but
  not a Single Query logic. The independent adapter now expands list/regexp
  values against the complete `Logic` enum and then filters through the chosen
  track's division table, exactly following `Participation.get`. The retained
  negative is
  `/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744315286061407-0c81f06d`;
  no official selected set was generated or inspected.

- **2026-07-22 — Corrected the ADR-0356 authority before observing a sample.**
  The first S1b live attempt stopped before metadata reduction because official
  submission logics may be Pydantic root regexps, not only lists. The same
  investigation proved `Config.submissions` uses non-recursive
  `../submissions/*.json`, so two `submissions/template/` examples were never
  producer inputs. The registered population is therefore 51 direct-child
  submissions, 36 competitive submissions, seed sum `9,684,066,201`, and
  global seed `22,731,074`. The retained negative is
  `/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784743920768303217-16764d04`;
  no official selected set was generated or inspected.

- **2026-07-22 — Implemented the ADR-0356 S1b selection-free live auditor.**
  The new runner verifies and stages every pinned organizer/rules/data/
  submission byte, derives divisions and removals through a standard-library
  AST reader, streams official gzip arrays, reduces historical facts with
  bounded state, and writes eligibility plus per-logic cap/quota evidence with
  completion last. Fourteen offline tests include stream truncation/missing-key
  mutations and accumulator/batch equivalence. This commit deliberately
  precedes the live input audit and cannot emit a selected list.

- **2026-07-22 — Completed ADR-0356 S1a official-format fixture adapters.** A
  standard-library AST reader derives the Single Query division map directly
  from pinned `defs.py`; strict adapters normalize organizer benchmark/result
  gzip JSON and division/logic submission forms without importing organizer
  code. Eleven tests reject unknown divisions/logics/answers and wrong
  incremental identity. The fixture also freezes an important code/prose edge:
  the executable triviality expression is `result != Unknown`, so two
  sub-second OOM rows classify as trivial. No official selection has been
  generated or inspected; a full selection-free input audit is next.

- **2026-07-22 — Completed ADR-0356 S0 authority and fixture freeze.** The
  canonical authority manifest derives and cross-checks the exact organizer,
  result, submission, Zenodo, population, and seed facts without network access
  during ordinary checks. A standard-library auditor now validates normalized
  identities, competitive-logics expansion, old-criteria=false historical
  triviality, all four cap regions, new-before-old quotas, complete terminal
  decisions, and an exact nine-file corpus bijection. Eight tests cover the
  registered source/seed/release/path/corpus/eligibility/quota/decision
  mutations and are part of `check-smtcomp-resume.sh`. This is fixture contract
  credit only; S1 official-format inputs and the full producer remain open.

- **2026-07-22 — Preregistered official SMT-COMP 2026 Single Query selection
  identity.** Proposed ADR-0356 separates pinned upstream Polars production
  from an independent eligibility/corpus auditor, selects Zenodo release
  2025.08.04 by exact 450,472-row agreement with organizer metadata, freezes the
  2018--2024 result hashes and corrected `22,731,074` global seed, and requires one
  terminal decision plus exact bytes for every metadata row before E1b can
  consume the population. S0 fixture/authority implementation is next; the old
  64,345-file candidate still has zero selection credit.

- **2026-07-22 — Accepted ADR-0355 and completed TL2.14 nested-inductive
  elimination upon containing-commit publication.** M6 maps every decision exit to the pushed P0--M5
  evidence and repeats every bounded final gate under one worker and 4 GiB.
  Two fresh positive pinned-Lean runs reproduce the exact 374,840-byte OLEAN
  digest; both negative runs reject with the registered line-8 diagnostic.
  Kernel all-target tests pass 188 unit plus 85 integration cases; importer
  all-target tests pass 47 integration cases; both separate doctests pass.
  Exact 640/720/768/840 populations, well-founded 35/0 and identity controls,
  focused rustfmt, warning-denied Clippy/rustdoc, 73 related Python tests, every
  registered generator/checker, parity documents with `DISAGREE=0`, 137
  foundational concepts, 174 packs, links, shell syntax, and staged-path audit
  pass. Topic-branch publication is the final handoff condition: the containing
  commit must be pushed with local/tracking/remote equality. The
  [final result](docs/plan/lean-nested-inductive-elimination-final-2026-07-22.md)
  accepts ADR-0355 and marks TL2.14 DONE without granting native source,
  elaboration, broad-library, ecosystem, or full-parity credit.

- **2026-07-22 — Completed TL2.14 M5 computation and assurance.** Plan
  checkpoint `dbaaedb4` froze three exact theorem roots and their
  3/3/5-successor normal forms before implementation. Computation checkpoint
  `edfa7924` imports and reduces every theorem twice, infers each proof, checks
  its exact `Eq` type and definitionally equal sides, and confirms zero axiom
  identities. Two fresh pinned-Lean runs reproduce the unchanged
  `d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2`
  OLEAN digest. The append-only TL2.14 overlay preserves every older
  observation and advances the current matrix to 7 rows / 6 admitted / 4
  computation-checked / 0 current declines. The obsolete live
  `inductive-nested` code is removed; five unrelated codes remain exact. Two
  independent audits found no blocker. Complete importer/kernel suites, exact
  640/720/768/840 and well-founded 35/0 controls, strict tooling, 73 related
  Python contract tests, generated documents, foundational resources, and
  links pass. M6 final closure is next; ADR-0355 remains proposed and TL2.14
  remains WIP.

- **2026-07-22 — Completed TL2.14 M4 exact official nested import.** Commit
  `f03dfcdf` derives the auxiliary population from checked main-recursor motive
  count, maps all source main and `First.rec_N` records by generated name, and
  compares exact types, universes, indices, motives, minors, restored rule
  constructors, field counts, and rule bodies. The construct plus three frozen
  computation streams import twice with full-report equality at 22/34/34/34
  declarations and zero axioms; all four reversed recursor arrays produce the
  same identities. Twenty wire/publication rejection classes, including both-
  sided indices/rules/K variants and late line-642 collision, pass. An
  independent audit found no blocker. Complete importer/kernel suites, strict
  tooling, M0 checker history, and exact 640/720/768/840 plus well-founded 35/0
  controls pass. M5 explicit normal forms and assurance are next; the live
  decline remains.

- **2026-07-22 — Completed TL2.14 M3 deterministic nested grammar and
  restoration integrity.** Commit `6a2afdd5` repeats the exact 640-case public
  grammar twice with descriptor digest `a20fe056c9443a37`, covers every frozen
  range, independently checks the exact public declaration and per-rule
  recursor-dependency surface, and performs 320 main plus 462 auxiliary typed
  iota reductions. Sixteen malformed private mutations prove complete
  transactional rollback and retry; typed recursor mutations reject or change
  a named observation. The preregistered stop condition was handled before the
  semantic checkpoint: amendments `ab5dbf99` and `d03ba0fc` authorize and bind
  a narrow validator for already-checked temporary family/constructor/map/
  freshness metadata after copied-constructor mutants survived restoration.
  An independent final audit found no semantic blockers. The complete kernel
  and importer suites, retained 720/768/840 profiles, strict Clippy/rustdoc/
  doctests, and M0 no-observation contracts pass under the one-worker/4 GiB
  policy. M4 exact official import is next; importer policy and all frozen M0
  computation streams remain untouched.

- **2026-07-22 — Completed TL2.14 M2 native nested-inductive expansion and
  restoration.** Commit `96b6fbd4` adds rollback-aware ordered container-group
  metadata, exact structural discovery, complete specialized group copying,
  fixed-point queuing, unchanged TL2.13 atomic checking, recursive
  family/constructor/recursor restoration, exact string `.rec_N` names,
  private-name leakage rejection, final-surface inference, and cache-safe
  transactional publication. Twenty-three focused tests cover repeated and
  distinct parameterizations, outer/container mutual groups, zero/one/two
  parameters and indices, universes, higher-order and depth-two shapes,
  `Prop`/`Type`, empty owners, typed failures, bounds, collisions, retry, and
  the `main -> rec_1 -> main` computation chain. A two-pass independent review
  found no remaining restoration/publication blocker. The complete kernel and
  importer suites, retained 720/768/840 profiles, strict Clippy/rustdoc, and M0
  contracts pass under the one-worker/4 GiB policy. M3's >=640-case generated
  grammar and forced mutation teeth are next; importer policy and M0 streams
  remain untouched.
- **2026-07-22 — Added bounded exact bignum WZ base checking.** A private
  rational/positive-integer-Gamma evaluator runs only after the existing base
  equality returns `Unknown`, with explicit Gamma/power limits and fail-closed
  unsupported cases. Bignum product scalars and monic coefficient division
  remove two further intermediate-overflow artifacts. The direct
  squared-binomial family now certifies through 255 and the raw family through
  35; focused limit/overflow tests plus full family samples, tamper checks, and
  ceiling checks bring the CAS gate to 525 units and 147 doctests.

- **2026-07-22 — Extended Stirling-composed squared-binomial moments through
  order 33.** Exact even-factor pre-cancellation plus bignum-only polynomial
  intermediates remove the raw order-20 representation overflow while keeping
  public coefficients in checked `i128`. Deterministic monic product
  canonicalization lets the proof object compare high-order component and final
  quotients before expansion, with the existing rational comparison retained as
  fallback. Two focused regressions cover term reconstruction and factor
  canonicalization; the 524-unit/147-doctest family gate includes exact samples,
  tamper rejection, and the order-34 ceiling.

- **2026-07-22 — Completed TL2.14 M1 diagnostic preflight without nested
  admission.** `import_inductive` now parses one consistent group-wide
  `numNested` value before applying ordinary recursor cardinality, derives the
  claimed source-family-plus-auxiliary wire shape, and returns exact
  `Unsupported(inductive-nested)` before family translation or kernel
  admission. Missing/extra nested recursors and inconsistent mutual metadata
  remain malformed; non-nested singleton records with zero or two recursors
  retain their exact error. Four focused construct-matrix tests repeat the
  official nested/control rows and close singleton/mutual count mutations. The
  complete 41-test importer integration suite, well-founded 35-declaration
  control, 720/768/840 deterministic populations, warning-denied Clippy and
  rustdoc, M0 contract, parity, compatibility, foundational-resource, and link
  gates pass under the 4 GiB/one-worker policy. No M0 computation stream or
  generated assurance artifact was observed. M2 native expansion/restoration
  is next under proposed ADR-0355.
- **2026-07-22 — Completed SMT-COMP E3 three-host loss/retry durability.**
  The accepted ADR-0344 path now stages immutable content-addressed runner and
  fixture bytes, registers one exact `s5`/`s6`/`s7` environment and NFSv4.1
  class, preregisters disjoint initial plus different-host retry ownership,
  launches canonical commands under per-host E2 cgroups, and gates raw export
  on complete E1/E2/E3 evidence. The destructive six-case control seals its
  marker, exact cgroup/launcher/SIGKILL, failed outer allocation, terminal-less
  resource session and shard attempt, dead-unit/launcher proof, deterministic
  stale-lease quarantine, and successful shard-0 retry on `s6`. Its timing-free
  outcome projection is byte-identical to the uninterrupted control. The
  mandatory aggregate gate and same-commit source-bundle reuse pass; final
  evidence is under
  `/nas3/data/axeyum/harness/e3-gate/live-1784740048714236679-84b40626d845`.
  Official selection identity is next; no full-run credit is granted yet.

- **2026-07-22 — Completed SMT-COMP E2 one-host aggregate resource
  enforcement.** `compete.py --host-run` now launches all registered shards in
  one transient user-systemd/cgroup-v2 service with exact memory/swap/CPU/PID
  limits, bounded concurrency, controller readback, immutable preflight and
  terminal counter evidence, and resource-completion-gated raw export. Portable
  mutation tests and required live two-worker/destructive host-runner kill and
  explicit recovery tests pass; E3 multi-host durability and the independent
  official selection ledger remain open.

- **2026-07-22 — Completed fixture-only SMT-COMP resumable runner E1b and
  sound-declined a current QF_AUFLIA wrong-`unsat`.** The opt-in runner now
  validates exact run/selection/corpus/environment/solver/source/toolchain
  identity before execution, owns each shard through an explicit lease, records
  immutable attempts/results/output sidecars/terminals, and publishes completion
  last. Real kill/resume, contention, timeout-response, typed-termination,
  duplicate, and mutation gates pass; that E1b mode still rejects real resource
  envelopes. E2 is now complete and E3 remains pending. Audit of the stale
  64,345-file run found its second WRONG marker
  at `QF_AUFLIA/array_benchmarks/misc/pipeline-invalid.smt2`. Current Axeyum also
  returned `unsat`; cvc5 1.3.4 and cvc5 over Axeyum's parse/write round-trip both
  returned `sat`. Because the scalar UFLIA refutation has no proof checker/lift,
  the AUFLIA lazy-ROW adapter now returns `unknown` for that untrusted outcome.
  The exact benchmark and regression freeze the soundness boundary.

- **2026-07-22 — Completed TL2.14 M0 source/wire freeze without product
  observation.** A 2,917-byte explicit-recursor source compiles twice to one
  OLEAN digest; ordinary, indexed-container, and repeated-container theorem
  roots export twice to three byte-identical streams totaling 114,596 bytes /
  2,022 records. All three source families report `numNested = 1`; the repeated
  source proves structural auxiliary reuse, and variable recursor-array order
  proves later comparison must be name/rule based. A 260-byte negative source
  reproduces the pinned kernel's no-local-variable diagnostic twice. The
  machine registration freezes 19 cases, 21 mutations, the >=640 grammar,
  720/768/840 and well-founded controls, resources, stops, and exact nonclaims.
  Thirteen focused tests plus parity, compatibility, foundational-resource,
  link, and diff gates pass; the checker is registered in both aggregate
  routes. M1 may correct only the diagnostic preflight; no nested admission is
  yet authorized.

- **2026-07-22 — Fixed the full-library FP exact-cancellation wrong-`sat`.** The
  add bit-blaster had an RNE-only exact-zero convention and always emitted `+0`
  for finite cancellation; RTN requires `-0`. FMA carried the same latent bug.
  Both paths now share the correct mode-sensitive zero-sign rule. Added
  bit-for-bit `rustc_apfloat` tests across all five modes, a minimized QF_FP
  regression, an all-mode deterministic differential generator, and directed
  add/FMA seeds. A cvc5 1.3.4 differential run decided 600/600 scripts with zero
  disagreement (267 `sat`, 333 `unsat`), and both preserved QF_BVFP/QF_ABVFP
  originals changed from wrong-`sat` to `unsat`. Complete affected-slice
  revalidation remains the P0 exit gate.

- **2026-07-22 — Corrected and preregistered the post-TL2.13 trust boundary.**
  Direct inspection of pinned Lean 4.30 shows nested-inductive elimination in
  kernel `environment::add_inductive`, while well-founded source recursion is
  an elaborator transformation. The completed dependency audit therefore makes
  TL2.14 kernel-side nested expansion/restoration dependent only on TL2.13 and
  leaves source recursion in TL4.10. Proposed ADR-0355 and its P0--M6 plan bind
  the transformation, exact official comparisons, >=640 generated profiles,
  retained 720/768/840 and well-founded controls, resource limits, stop
  conditions, and non-claims. M0 source/wire/no-product freeze is next.

- **2026-07-22 — Completed TL2.13 M5 and accepted ADR-0354.** The append-only
  construct-matrix overlay preserves ADR-0351/TL2.12 history while recording
  five admitted rows, three independently computation-checked rows, and one
  current decline. The live compatibility contract removes
  `inductive-mutual`; historical validators project their original matrix
  view; 184 kernel units, 61 kernel integrations, 40 importer integrations,
  both doctests, the 720/768/840 populations, pinned-Lean differentials,
  strict Clippy/rustdoc, 77 Python tests, every generator/checker, 137 concepts,
  174 packs, and links pass under the 4 GiB policy. The
  [final result](docs/plan/lean-mutual-inductive-groups-final-2026-07-22.md)
  marks TL2.13 DONE. The subsequent dependency audit corrects the TL2.14
  handoff to kernel-side nested-inductive elimination.

- **2026-07-22 — Completed TL2.13 M4 exact official mutual-group import and
  computation.** The importer now validates each ordered family/constructor/
  recursor record, calls `add_mutual_inductive` once, and matches official
  dependency-ordered recursor arrays by checked name and owned rules. The
  construct, non-indexed computation, and indexed computation streams each
  import twice to identical zero-axiom reports; both selected cross-family
  theorem sides normalize to the registered two-successor normal form. A new
  six-test product target covers 22 rejecting metadata/type/count/rule/field/
  publication mutations plus recursor-order and descriptive-metadata controls.
  The 40-test importer suite, complete 184-unit kernel suite and integrations,
  retained 720/768/840 populations, strict Clippy, rustdoc, both doctests,
  owned formatting, and diff checks pass under one job and 4 GiB. The kernel
  doctest required temporary output on the normal filesystem because the
  unrelated `/tmp` tmpfs was 80% occupied; the unchanged test then passed and
  the unique temporary directory was removed. Historical pre-widening product
  observations remain immutable. M5 assurance/final closure is next.

- **2026-07-22 — Completed TL2.13 M3 deterministic mutual-group grammar.** A
  fixed-seed independent producer executes 720 unique public group cases twice
  to byte-identical descriptor `2ea6769fa45ea159`. The population contains 432
  positive admission/inference/base-iota contracts and 288 exact typed
  rollbacks across all registered group, parameter, index, constructor, field,
  recursion-target, telescope, binder, sort, and invalid-shape dimensions.
  Motive/minor order is read from generated recursor `Pi` telescopes; target
  recursion is counted from rule constants. Swapped group-order expectations
  reject in 288 cases, moved target-family expectations reject in 240, and all
  288 negatives restore the exact environment. The 768 recursive and 840
  positivity descriptors remain unchanged. Complete bounded kernel/importer,
  clippy, rustdoc, doctest, parity, foundational, link, owned-format, and diff
  gates pass; unrelated workspace formatting drift remains outside this
  milestone. No importer policy or M0 official stream changed. M4 is next.

- **2026-07-22 — Completed TL2.13 M2 native mutual-group semantics.** One
  trusted group algorithm now handles singleton and multi-family positivity,
  constructor classification, globally ordered motives/minors, target-family
  induction hypotheses and recursor calls, per-owner indices/majors, mutual-
  `Prop` elimination restriction, recursor/rule inference, and atomic
  publication. The 18-test public matrix covers all registered native rows,
  including non-indexed/indexed/higher-order cross computation; two private
  tests freeze the 16 mutation classes and prove complete rollback after a
  final staged-rule failure. The complete bounded kernel/importer suites,
  warning-denied clippy/rustdoc, exact direct-recursive identities, byte-
  identical 768/840 controls, parity/foundational/link gates, owned-file
  formatting, and diff checks pass under one job and 4 GiB. Workspace-wide
  formatting remains blocked only by unrelated existing CAS/bench drift, which
  this milestone does not rewrite. The importer decline and M0 streams remain
  untouched. M3's >=640-case deterministic group grammar is next.

- **2026-07-22 — Completed TL2.13 M1 ordered-group representation and
  singleton delegation.** `InductiveFamilySpec` and
  `Kernel::add_mutual_inductive` now express one ordered group with universe
  parameters and shared parameter count supplied once. Multi-family preflight
  rejects empty groups, group-local/environment name collisions, non-shared
  parameter telescopes, and inequivalent result universes with typed errors;
  each family opens its own indices. A private insertion log gives constant-
  time checkpoints and group-sized rollback without cloning the environment.
  `add_inductive` delegates through the singleton path with complete
  declaration/rule equality, exact iota computation and error payloads, and
  cache-safe same-name retry. Nine new focused tests, 182 kernel units, 51
  kernel integrations, 34 importer integrations, exact `MiniNat.rec`/
  `MiniList.rec` identities, and the unchanged 768/840 summaries pass under the
  one-job/4 GiB policy. Valid multi-family input remains a typed policy decline;
  M2 native semantics are next and no M0 official stream has entered Axeyum.

- **2026-07-22 — Completed TL2.13 M0 mutual-group source/wire freeze.** The
  pinned 66-line source compiles twice to one OLEAN digest and forces both
  non-indexed and indexed cross-family recursor computations to
  `MiniNat.succ (MiniNat.succ MiniNat.zero)`. Two twice-exported official
  format-3.1 streams are byte-identical per root and total 40,282 bytes; each
  recursor has two motives and four minors. Independent inventory exposes and
  freezes dependency-ordered wire recursor arrays (`Odd.rec, Even.rec`) while
  semantic motives/minors retain family order. The machine contract binds 18
  native cases, 16 mutation classes, the future >=640 group grammar, retained
  768/840 controls, 15 stop conditions, exact resource/tool pins, and no Axeyum
  product observation. Eleven fail-closed tests plus parity-doc/shell gate
  integration pass. M1 ordered representation/singleton delegation is next.

- **2026-07-22 — Preregistered TL2.13 atomic mutual-inductive groups.** Proposed
  ADR-0354 and a P0--M5 plan derive the exact shared-parameter, equivalent-
  universe, group-wide positivity, motive/minor ordering, target-family
  recursion, per-family index, mutual-`Prop`, and atomic-publication rules from
  pinned Lean 4.30. Eighteen native rows, sixteen mutation families, a future
  >=640-case group grammar, retained 768/840 controls, exact official recursor
  and explicit cross-computation gates, one-worker/4 GiB resources, stop
  conditions, and milestone commit/push discipline are fixed before semantics
  change. M0 source/wire freeze is next; no new Axeyum stream was observed.

- **2026-07-22 — Completed TL2.12 and accepted ADR-0353.** The final bounded
  pass closes 182 kernel unit, 42 kernel integration, 34 importer integration,
  and both doctest gates; focused rustfmt/clippy/rustdoc, 56 parity/contract
  tests, all registered generators/checkers, 137 foundational concept rows,
  174 packs, links, and `git diff --check` pass. The historical construct
  observation remains frozen while a separate TL2.12 overlay records four
  admitted, two computation-checked, and two declined rows. The research
  question and Lean roadmaps now hand the primary semantic path to TL2.13
  mutual groups with every positivity, direct-recursive, generated, official,
  and transactional-publication control retained.

- **2026-07-22 — Completed TL2.12 M4 official computation and assurance
  update.** Pinned Lean compiles the unchanged explicit-recursor source twice
  to one OLEAN digest. Both frozen computation streams retain their hashes,
  complete twice through Axeyum, preserve exact recursor metadata, and
  recursively normalize the selected theorem sides to
  `MiniNat.succ MiniNat.zero` and `True`. A machine-validated TL2.12 overlay
  preserves the historical ADR-0351 observation and regenerates the current
  matrix at four admitted rows, two separately computation-checked rows, and
  two typed declines. Timed validation remains below 463 MiB for Lean and 141
  MiB for the Rust gate. M5 final gates and disposition are next.

- **2026-07-22 — Completed TL2.12 M3 exact official construct imports.** The
  importer now parses `isReflexive` as descriptive metadata and leaves
  structural authority with the independent kernel. `MiniVector` and `MiniAcc`
  construct streams complete twice with exact generated/exported recursor
  comparison; the mandatory well-founded row also completes through `Acc.rec`
  without a frontend-support claim. Mutual and nested retain typed outcomes.
  Metadata flips, unsafe/nested/multi-family boundaries, and late recursor
  type/count/rule/`nfields` mutations all fail closed without partial
  publication. The 32 importer integration tests, one compile-fail doctest,
  focused clippy, and rustdoc pass. M4 owns the first computation-stream product
  observation and assurance regeneration.

- **2026-07-22 — Completed TL2.12 M2 generalized native recursion without an
  official-stream product observation.** The one M1 telescope-tail
  representation now generates index-aware, telescope-preserving IH types and
  matching recursive iota arguments. Ten positive and four negative registered
  rows pass through the public kernel path; a deterministic 768-case grammar
  repeats exactly and exercises nine semantic mutation classes, while the
  recursor contract rejects type/minor/rule/field-count corruption. The 840-case
  positivity population retains its TL2.11 digest and failure partition while
  reporting the intended 174-to-360 admission transition. All 182 kernel units,
  direct-recursive identities, focused clippy, and rustdoc pass. M3 owns both
  frozen official streams and the remaining importer mutations.

- **2026-07-22 — Completed TL2.12 M1 shared recursive-field representation
  without widening admission.** One WHNF telescope-tail operation now drives
  constructor classification plus the independently reopened minor-IH and rule
  RHS paths. Checked metadata stores stable field position/telescope depth;
  mismatches return `RecursiveFieldShapeMismatch`. Canonical identities remain
  `MiniNat.rec=dee04a36...f5ef` and `MiniList.rec=1087558f...7660`; Nat/List
  computation, both feature declines, 182 kernel units, and the exact 840-case
  positivity summary pass. The gate caught and rejected an eager-slice panic and
  a reducible-let error-precedence drift before acceptance. M2 native semantics
  is next; no new official stream has entered the Rust importer.

- **2026-07-22 — Completed TL2.12 M0 source/wire freeze without product
  observation.** The final 1,422-byte explicit-recursor source compiles twice
  under pinned Lean and closes both registered computations by `rfl`. Two
  root-specific `lean4export` streams repeat byte-identically: Vector is 15,944
  bytes/284 records at SHA-256 `1ab5a38b...6df19`; Acc is 17,722 bytes/314
  records at `3cb06283...c003`. Independent inventories freeze the exact target
  inductive/recursor metadata. A machine contract binds 14 native cases, 12
  mutation families, the future >=512-case grammar, the mandatory 840-case
  positivity control, resources, commands, claim limits, and 13 stop
  conditions; ten tests reject drift and premature Axeyum observations. No new
  stream was passed to the Rust importer. M1 shared representation is next.

- **2026-07-22 — Preregistered TL2.12 recursive-indexed plus
  reflexive/higher-order induction hypotheses.** Proposed ADR-0353 and a bounded
  M0--M5 plan now reduce all supported recursive fields to one telescope/index
  rule, pin the Lean 4.30 implementation authority and exact official stream
  hashes, separate constructor admission from recursor computation, register
  native/mutation/generated/official gates, preserve TL2.11 and transactional
  import controls, and freeze stop/resource/commit-push discipline. No kernel or
  importer semantics changed; M0 machine registration and supplemental official
  computation-source freeze are next.

- **2026-07-22 — Completed TL2.11/T6.0.2 and accepted ADR-0352.** The final
  bounded pass closes 182 kernel unit, 38 kernel integration, 30 importer
  integration, and both doctest cases; required pinned Lean, the repeated
  840-case grammar, focused clippy/rustdoc/rustfmt, 14 observation-validator
  tests, foundational resources, parity artifacts, and links all pass. The
  research question is closed. No inductive admission widened; TL2.12 is now
  the preregistration-first recursive-indexed/reflexive IH handoff.

- **2026-07-22 — Completed TL2.11 strict-positivity M3 official/import gate.**
  Ran four immutable sources twice at exact pinned Lean 4.30 under the 3/4 GiB
  systemd policy: two accepts and six diagnostic-matched rejects, max 468432
  KiB RSS. Added the mandatory fail-closed CI differential, an explicitly
  synthetic official-stream mutation that propagates the exact typed kernel
  error without publication, and a machine-checked observation manifest. The
  frozen construct matrix remains unchanged. M4 closure remains.

- **2026-07-22 — Completed TL2.11 strict-positivity M2 public/generated gate.**
  Added a twelve-row `add_inductive` contract matrix and a fixed-seed 840-case
  structural grammar with independently assigned outcomes. Two complete runs
  reproduce the frozen summary byte-for-byte: 174 admissions, 42 recursive-
  indexed declines, 144 reflexive declines, 270 non-positive rejections, and
  210 invalid-application rejections. All package unit/integration tests pass;
  the known `/tmp` LLD doctest fault passes when temporary linker output is
  redirected under `target/`. Focused clippy/rustdoc are clean. M3 official and
  importer evidence remains.

- **2026-07-22 — Completed TL2.11 strict-positivity M1 trusted preflight.**
  Added Lean 4.30's single-family WHNF/`Pi`/valid-family-application rule before
  provisional inductive insertion, with separate exact non-positive and
  invalid-occurrence errors. Public-path tests prove error precedence and
  transactional rollback; direct-recursive computation and positive deferred
  families retain their prior outcomes. The bounded gate passes 182 kernel
  unit tests plus focused clippy/rustdoc. M2's full public matrix and >=256-case
  repeated generated grammar remain open.

- **2026-07-22 — Completed TL2.11 strict-positivity M0 source freeze.** Added
  hash-frozen mixed-polarity and deep-negative Lean sources beside the immutable
  construct-matrix controls; registered six ordered rule classes and exact Lean
  4.30/resource/command policy; added a fail-closed checker plus eight mutation
  tests to normal parity/check paths. No new Lean or Axeyum product run occurred;
  M1 pre-insertion trusted checking is next.

- **2026-07-22 — Preregistered TL2.11/T6.0.2 strict positivity before kernel
  implementation.** Proposed ADR-0352 and a bounded M0--M4 execution plan from
  the exact Lean 4.30 kernel rule. Froze the intended WHNF/`Pi`/valid-family-
  application semantics, separate typed polarity/invalid-occurrence errors,
  pre-insertion environment ordering, twelve-row public case matrix, generated
  adversarial grammar, official differential, stop conditions, and TL2.12
  deferral. No kernel or importer semantics changed; M0 negative-source freeze
  is next.

- **2026-07-22 — Completed M5 and accepted the official Lean construct-matrix
  decision.** All milestone-owned Rust, Python, parity, foundational-resource,
  and link gates pass under bounded resources. Accepted ADR-0351, closed its
  research question, synchronized PLAN/STATUS and both Lean roadmaps, and handed
  the primary semantic sequence to TL2.11 strict positivity. The selected seven-
  row matrix remains one admission, one translated-kernel decline, three parsed
  declines, one inventory-only nested misclassification, one official source
  rejection, and zero computation rows; TL1.8/TL2.16 remain PARTIAL globally.
  The environmental `/tmp`-LLD rustdoc fault and unrelated workspace rustfmt
  failure are recorded without modifying their files.

- **2026-07-22 — Completed official Lean construct-matrix M4 generated
  assurance output.** The checked seven-row matrix derives one exact independent
  admission, one translated-kernel decline, three parsed/policy declines, one
  inventory-only nested format misclassification, one official source
  rejection, and zero computation-checked rows from the canonical registration.
  Implication tests reject promotion without `CompletedImport`, promotion of
  nested `Malformed` to parsed/unsupported credit, and computation credit
  without a check. TL2.16 is now PARTIAL for this selected population; M5 final
  gates and ADR closure remain.

- **2026-07-22 — Completed official Lean construct-matrix M3 current-product
  measurement.** At the pushed Stage B revision, ran the immutable direct-
  recursive positive control before every one of ten measurements and repeated
  all five new outcomes exactly. Recursive-indexed reaches the trusted kernel's
  typed decline; reflexive, mutual, and the well-founded `Acc` dependency stop
  at typed importer policy boundaries; nested reveals that the current importer
  misclassifies its valid two-recursor official group as malformed. Added a
  bounded Rust regression and machine product freezer/validator without changing
  importer or kernel semantics. Every decline publishes no `CompletedImport`;
  M4 generated assurance matrix is next.

- **2026-07-22 — Completed the official Lean construct-matrix Stage B wire
  freeze.** Exported each of five frozen roots twice under the 4 GiB cgroup;
  every pair is byte-identical and the retained set is 116,636 bytes. Extended
  the independent reader to freeze declaration names and complete inductive/
  constructor/recursor metadata. The measured wire forms distinguish source
  labels honestly: `MiniAcc` is both reflexive and recursive-indexed, `Rose`
  retains `numNested=1` with two recursors, and well-founded source elaborates
  through ordinary definitions plus the `Acc` closure. The Stage B generator,
  validator, and ten contract tests reject byte/inventory/repetition/retention/
  case-link/product drift. No Rust importer was run; M3 is next after push.

- **2026-07-22 — Completed official Lean construct-matrix M0 and Stage A.**
  Reproduced the flat and direct-recursive official streams twice at their
  committed SHA-256 identities and repeated both current importer reports
  twice. Froze minimal recursive-indexed, Acc-shaped reflexive, mutual, nested,
  and explicit well-founded sources plus an official non-positive negative;
  pinned Lean accepts the positive module and rejects the negative in the
  kernel positivity check under a 4 GiB cgroup. Added the seven-case
  machine-readable source registration and eight fail-closed tests. No new
  export or product measurement occurred; ADR-0351 remains proposed and M2
  official wire freeze is next.

- **2026-07-22 — Proposed the official Lean construct-matrix execution
  plan.** Proposed ADR-0351 and the linked execution plan separate source
  families from official core wire forms, freeze source then independently
  inventoried export evidence before product measurement, pair every current
  decline with the direct-recursive positive control, define generated
  assurance classes and exact retention/resource/stop gates, and keep
  TL1.8/TL2.16 honestly incomplete. M0 baseline reproduction and the Stage A
  source freeze are next; no importer or kernel semantics changed.

- **2026-07-22 — Completed TL1.7 canonical Lean declaration identity.**
  Accepted ADR-0350; published ledger-compatible axiom identities plus complete
  structural content and direct-dependency digests for every admitted
  declaration; froze the exact flat-fixture rows; and proved reorder invariance
  plus valid type/body/binder mutation sensitivity. Importer 28 across three
  binaries plus the example target pass. The remaining official inductive
  fixture matrix is next; TL1.5 property fuzzing is dependency-ready.

- **2026-07-22 — Completed TL1.4 generated Lean import mutation coverage.**
  Accepted ADR-0349; added 226 deterministic cases across every specified
  truncation/ID/reference/field/depth/Unicode/integer/cycle/version family;
  froze exact stable outcome counts and repeated-summary identity; and recorded
  64 complete-record prefixes as unsealed rather than full artifacts under the
  upstream no-footer grammar. Importer 23 across two binaries plus example
  target pass. TL1.7 declaration digests subsequently landed.

- **2026-07-22 — Completed TL1.3 transactional Lean import publication.**
  Accepted ADR-0348; removed caller-owned `&mut Kernel` import; introduced the
  private-field `CompletedImport` success boundary; preserved every exact
  fixture result; and added late parser, kernel, unsupported, resource, and I/O
  failure controls. Importer 20 plus example target pass. TL1.4 generated
  mutation coverage subsequently landed.

- **2026-07-22 — Completed TL2.7 checked Lean Nat literal semantics.** Accepted
  ADR-0347; required an independently checked canonical `Nat` bootstrap before
  literal typing; implemented arbitrary-precision constructor-offset equality,
  successor reduction, and one-layer recursor conversion; admitted and computed
  the exact official Nat root as ten declarations with zero axioms; added
  bootstrap, above-`u128`, false-equality, recursor, importer, seam-fuzz, and
  pinned-Lean controls. Kernel 179+35, importer 18, compatibility/prototype 14,
  and the required official Lean differential pass. The compatibility contract
  advances to five passing profiles, one decline, and eight codes. TL1.3
  transactional publication subsequently landed.

- **2026-07-22 — Completed TL2.6 arbitrary-precision Lean Nat literal
  storage.** Accepted ADR-0346; replaced the public `u128` payload with
  canonical `NatLit(BigUint)`; validated format-3.1 decimal payloads without
  narrowing; advanced the official Nat root to `literal-nat-typing`; added
  boundary, malformed-input, interning, structural, rendering, importer, and
  above-`u128` seam-fuzz coverage. Kernel 179+29, importer 16, doctest, focused
  warning-denied Clippy/rustdoc, compatibility generation, and link gates pass.
  TL2.7 literal typing is next.

- **2026-07-21 — Completed TL2.5 structure eta as a separate kernel and
  differential gate.** Checked inductives now persist whether constructor
  fields are recursive; definitional equality applies symmetric eta only to
  exactly saturated constructors of one-constructor, zero-index,
  non-recursive families and requires equal inferred types plus field-by-field
  projection equality. Seven native families cover symmetry, false equality,
  wrong types, parameters/universes, dependencies, and indexed/recursive
  exclusions. Pinned Lean 4.30 accepts the positive `rfl` control and rejects
  the duplicated-field mutation under the 4 GiB bound. PLAN, STATUS, the
  implementation and compatibility roadmaps, Project State, compatibility
  contract/matrix, blocker census, importer result, and TL2.4 handoff now agree
  that TL2.6 arbitrary-precision Nat storage is next; generated TL2.15 eta fuzz
  coverage remains open.

- **2026-07-21 — Completed TL2.4 constructor projection reduction and closed
  the exact official projection root.** Native parameter/universe/dependent/
  neutral/malformed controls pass; format-3.1 `proj` translation is live; the
  official four-record stream admits nine declarations and computes; name/index
  mutations reject. The compatibility contract advances that row to K1 pass and
  removes the retired `expr-projection` decline code. The Nat root now exposes
  line-125 bignum/literal typing as its exact first blocker. PLAN, Project State,
  both Lean roadmaps, blocker census, importer result, kernel trust plan, and
  diary preserve the TL2.5 eta and broader-compatibility boundaries.

- **2026-07-21 — Completed TL2.3 dependent projection inference without
  importing or computing projections.** The kernel preserves checked
  parameter/index metadata and infers parameterized, indexed,
  universe-polymorphic, and dependent field types using Lean's sole-constructor
  telescope rule. Positive and mutation tests cover malformed names, shapes,
  arity, fields, Prop elimination, and injected metadata corruption. The
  compatibility contract/matrix, Lean implementation/compatibility roadmaps,
  blocker census, Project State, PLAN, and prover-track documents now agree:
  TL2.4 reduction is next, TL2.5 eta is separate, and `expr-projection` remains
  a K1 decline until the official closure computes.

- **2026-07-21 — Completed TL2.2 projection representation without semantic
  overclaim.** The kernel now carries `Proj` through every structural and
  de Bruijn operation and both renderers, backed by four integration tests and
  renderer traversal coverage. Inference returns `UnsupportedProj`, admission
  rolls back, and the importer retains `expr-projection`; TL2.3 is the next
  unblocked task. The compatibility contract/matrix, Lean implementation and
  compatibility roadmaps, blocker census, Project State, PLAN, and current
  status all preserve that boundary.

- **2026-07-21 — Reclassified the Z3-class categorical-engine gaps.** The
  source-backed audit and 125/125 focused test run replace stale “new/absent”
  roadmap wording. Interpolation, substantial direct CHC/Horn, and bounded
  verified abduction are existing seeds; textual commands, representative
  corpora, Horn depth, portable certification, and production hardening remain.
  General SyGuS is the separately absent engine. P3.8/P4.6/P4.7 and the Track 4
  index now preserve those distinctions.

- **2026-07-21 — Classified the three quantified-BV Lean export costs.** Opt-in
  phase telemetry leaves proof semantics and default output unchanged. Under a
  30-second wall bound, `bug802` builds its 8,524-command tail and then exceeds
  a hard 4 GiB cap in scoped kernel closure; `small-pipeline-fixpoint-3` closes
  its 13,824-command proof in 7.744 seconds below 600 MiB but does not spool a
  module; and `cond-var-elim-binary` emits 15,705 commands by 2.607 seconds below
  525 MiB but does not finish CPS reconstruction. This rejects a single renderer
  fix and preserves the production denominator pending mechanism-specific work,
  evidence-aware dispatch, and official-Lean checking.

- **2026-07-21 — Prototyped Lean reconstruction from selected evidence.** The
  exact eight reconstruction gaps split into five existing-consumer plumbing
  wins and three bounded quantified-BV cost cases. Two quantified-BV selected
  certificates return 15 KB / 18.5 MB kernel-checked modules. All three QF_NIA
  selected Alethe proofs contain only congruence+resolution rules and route to
  the existing EUF reconstructor, producing 2.9--8.1 KB modules in about 0.10 s
  below 9.5 MiB RSS; query-only source classification had incorrectly selected
  `la_generic`. Two BV alternation rows and one conjunctive row remain bounded
  mechanism-specific cost diagnostics. The durable probe and result note
  preserve the 30-second per-row protocol; production credit still requires
  evidence-aware dispatch plus the official-Lean tier.

- **2026-07-21 — Refreshed the complete bare-UNSAT population under audit v2.**
  Corrected the v1 vacuous-check accounting in the artifacts themselves,
  recorded coarse backend/check-mode attribution for every residual, and
  regenerated the proof matrix and parser-backed shape census. The refresh
  preserves every verdict but removes four stale QF_SEQ source-invalid DRAT
  credits and changes 22 unpaired timing-derived dominance flags; both are
  reported rather than normalized away. Current proof counts are 267 certified
  and independently checked, 260 Lean-checked, 259 full-conjunction, 58 bare,
  zero declared trust holes, and two proof-production errors.

- **2026-07-21 — Landed the T5.4.3 directed-fuzz implementation checkpoint.**
  Pushed `3d75d407` after targeted tests and strict Clippy. The API retains
  exact `UnknownReason`, rejects operational/replay failures, samples only
  guard-admitted QF_BV tuples, and emits separately named `fuzzed-only`
  target/report JSON. The authenticated fixture lock/hash now records the new
  direct SMT-LIB edge. The full package, strict targeted Clippy,
  warning-denied rustdoc, and docs links pass under the cap. ADR-0340 stays
  proposed until fixtures, the full rejection matrix, mutation identities, and
  the remaining frozen capped gates pass.

- **2026-07-21 — Closed T5.4.2 with deterministic replay-checked witness
  artifacts.** Accepted ADR-0339 after fixing full-width signed replay, adding a
  typed fail-closed corpus API, and committing one three-class corpus plus its
  exact generated Rust tests. The JSON/source identities, reverse insertion,
  mutation teeth, full package, strict docs/lints, and 129-test semantics gate
  pass under the cap. The next cell is separately preregistered T5.4.3, not an
  automatic-write, coverage, performance, or symbolic-memory expansion.

- **2026-07-21 — Closed bounded P5.5 with the honest Tock comparison.** The
  committed case study contrasts the pinned target's concise source/build
  validation with Axeyum's all-input 32/64-bit properties, authenticated LLVM
  semantics, six mutation controls, and rechecked dual-DRAT route. It reports
  the 50.745 s fresh wall, 1.20 GiB peak, ignored-full/committed-summary artifact
  boundary, and compiler/frontend trust limits. No target bug was found, so no
  upstream issue is applicable. T5.5.4 and bounded P5.5 v1 are DONE.

- **2026-07-21 — Accepted Tock proof scoreboard v4 (ADR-0338).** Eight
  end-to-end dual-DRAT proofs and six native-replayed controls pass with
  UNKNOWN=0/DISAGREE=0. Stable identity `c4acae04...a37c` recomputes; query time
  is 12.700 s, peak RSS 1.20 GiB, and OOM deltas are zero. T5.5.3 is DONE.

- **2026-07-21 — Accepted ADR-0337 as a completed-test parser negative.** All
  eight dual-DRAT proofs/rechecks and six controls complete in the Rust test, but
  `--nocapture` prefixes the first marker and the column-zero parser counts seven.
  No output/credit survives. V3 is closed; only parser/log retention may change.

- **2026-07-21 — Preregistered the existing end-to-end Tock proof route
  (ADR-0337).** Post-v2 audit confirms that dual-DRAT bit-blast certification is
  already shipped; v3 changes only the positive-row API and truthfully splits
  proof/control policies. No new checker research or v3 query is authorized yet.

- **2026-07-21 — Accepted ADR-0336 as a target trust-boundary negative.** The
  first authenticated Tock query returns `Proved`, but its ledger marks
  BitBlast uncertified with certified Tseitin/SatRefutation. The frozen gate
  credits zero rows, stops before controls/later proofs, and atomically retains
  no output. V2 is closed; audit existing lowering evidence before new work.

- **2026-07-21 — Accepted ADR-0335 as a pre-query proof-v1 negative.** Pushed
  runner `10605313` passes refs/capture/registration/archive validation, then
  Cargo rejects the archived stale committed lock under `--locked --offline`
  before compilation. Zero queries/proofs/controls/rows run, cleanup leaves no
  output, and no OOM-delta failure is reported. V1 will not be rerun.

- **2026-07-21 — Corrected proof-runner HEAD archive link policy pre-query.**
  Pushed `7c3960c9` validates refs/capture but safe extraction rejects sole
  absolute symlink `corpus/public`. The registered correction requires exactly
  that link set, skips links, and hash-checks all required regular inputs. No
  Cargo command/query/output exists.

- **2026-07-21 — Froze Tock proof scoreboard pre-query.** The ignored runner,
  hash-pinned producer/registration, five producer tests, independent-spec test,
  strict Clippy, and full package suite pass; the authenticated test is skipped.
  Eight proof/six control rows remain zero until producer push.

- **2026-07-21 — Preregistered authenticated Tock proof scoreboard (ADR-0335).**
  Exact canonicals feed eight proof-producing QF_BV properties and six replayed
  controls; only fully certified trust ledgers and reflected/native agreement
  receive credit. The runner must build from pushed `HEAD`, not the dirty tree.
  No query or scoreboard row exists.

- **2026-07-21 — Accepted authenticated Tock capture v3 (ADR-0334).** Pushed
  `b2ad2641` builds two independent raw-identical 2.65 MB LLVM modules, admits
  both log helpers, and records exact time/RSS with zero OOM/path/partial drift.
  Stable identity `9ec0a0c3...84b9` independently recomputes; generated bytes
  stay ignored. T5.5.2 closes; zero queries/scoreboard rows exist.

- **2026-07-21 — Froze Tock capture v3 pre-invocation.** The thin policy wrapper
  passes only the full cache registration to structural replay and inherits all
  v2 gates. Five focused plus 41 inherited tests, six producer identities, nine
  tools, the 169-lock registration, local result, and 3,077-row inventory pass;
  no invocation/build/query exists.

- **2026-07-21 — Preregistered Tock capture-v3 replay correction (ADR-0334).**
  V3 may pass the exact validated full cache registration only to unchanged
  structural replay; it inherits all v2 build, identity, atomicity, resource,
  and no-query gates. No producer/build/query exists.

- **2026-07-21 — Accepted the exact Tock capture-v2 replay negative.** Pushed
  producer `9bff9d2e` validates source/tools/cache and twice recomputes inventory,
  then the structural replay raises `KeyError('expected_lock_packages')` because
  it receives the merged capture registration rather than the full cache
  registration. Zero builds/modules/admissions/queries and no output/OOM delta;
  v2 is closed.

- **2026-07-21 — Froze Tock LLVM capture v2 pre-build.** The thin wrapper
  removes ambient Cargo state, replays/mounts only the accepted cache read-only,
  rejects its physical path from LLVM, records the virtual-path count, and
  outer-atomically delegates all build/module/extraction/admission work to
  frozen v1. Eight focused plus 33 inherited protocol tests pass; registration
  and live cache identity validate. No build/query exists.

- **2026-07-21 — Preregistered Tock LLVM capture v2 (ADR-0333).** The successor
  will consume only the exact replayed ADR-0332 cache read-only, then restore
  ADR-0328's two independent source/target roots, raw module equality,
  compiler-matched extraction, and checked admission. No build/query exists.

- **2026-07-21 — Accepted authenticated dedicated Tock cache preparation
  (ADR-0332).** Pushed v5 completes one locked fetch and retains a replayed
  3,077-row hard-link-aware cache inventory (`fd6ee33d`), plus a structural
  162-node/814-edge resolution digest (`da6971e4`) against 169 lock entries.
  Zero OOM deltas; no build/capture/query. Cache bytes remain ignored local.

- **2026-07-21 — Froze structural-metadata preparation v5 pre-fetch.** The thin
  wrapper injects only the graph/lock/path validator into frozen v4. Five
  focused plus 18 inherited tests pass; compact registration validates nine
  producer files/six tools and contains no expected active count or digest.

- **2026-07-21 — Preregistered structural metadata authentication v5
  (ADR-0332).** Active package count is no longer an expected value. Closed
  package/node/edge identities, exact lock sources/checksums, in-tree path
  manifests, one workspace kernel, and a canonical result-only digest gate the
  read-only cache. No producer, DNS/fetch, or cache exists.

- **2026-07-21 — Accepted ADR-0331 as a metadata-count negative.** Pushed v4
  proves DNS/fetch and canonical hard-link inventory, then the read-only probe
  returns 162 active packages versus 169 lock entries. That equality is invalid;
  atomic cleanup leaves no cache or OOM/partial result. V5 needs structural
  package-ID/lock authentication, not a count learned from this run.

- **2026-07-21 — Froze hard-link-aware preparation v4 pre-fetch.** A thin
  policy wrapper injects only versioned owner/alias inventory into frozen v3.
  Four topology plus 14 inherited tests pass; compact registration validates
  seven producer files and six tools. No DNS probe, fetch, or cache exists.

- **2026-07-21 — Preregistered hard-link-aware cache preparation v4
  (ADR-0331).** Canonical inventory will represent each inode group as one
  lexicographic file owner plus explicit aliases, binding shared mode/size/hash/
  count and rejecting any outside-root link. No producer, fetch, or cache exists.

- **2026-07-21 — Accepted ADR-0330 as an inventory hard-link negative.** Pushed
  preparation v3 passes real DNS and its locked fetch, then rejects a shared
  firmware pack-index inode between Cargo's Git database and checkout. Atomic
  cleanup leaves no cache/partial output; no offline probe, build, or OOM-delta
  failure exists. V3 is closed; hard-link semantics need a fresh decision.

- **2026-07-21 — Froze resolver-corrected preparation v3 pre-DNS.** The thin
  successor reuses v2 inventory/offline/resource support and adds only exact
  resolver validation/mounting, strict `getent` IPv4 parsing, and `cache-v3`.
  Five v3 plus nine inherited tests pass; registration pins five producer files
  and six tools. A no-op confirms the resolver mount. No DNS lookup or fetch ran.

- **2026-07-21 — Preregistered resolver-corrected cache preparation v3
  (ADR-0330).** The only new input is the exact hash/mode/size-pinned
  systemd-resolved stub file at the target of `resolv.conf`; a pinned `getent
  ahostsv4 github.com` must prove real IPv4 resolution before Cargo. All v2
  non-network gates persist. No producer, DNS probe, fetch, or cache exists.

- **2026-07-21 — Accepted ADR-0329 as a DNS-boundary negative.** Pushed
  preparation producer `de343f63` reaches the exact locked Flux fetch, but
  `/etc/resolv.conf` points outside the constructed root to an absent
  `/run/systemd/resolve/stub-resolv.conf`. Three lookups fail before download;
  atomic cleanup leaves no cache or partial output and no OOM-delta failure is
  reported. V2 is closed; any resolver correction requires a fresh decision.

- **2026-07-21 — Froze the ADR-0329 cache-preparation producer pre-fetch.**
  The separate producer creates one atomic `cache-v2` envelope, allows network
  only for the exact locked fetch, remounts `cargo-home` read-only/offline for
  the v1 metadata replay, and binds every payload path in one inventory. Nine
  tests cover registration/environment/namespace/lock/inventory/probe/identity/
  cleanup boundaries; both no-op namespaces execute. No network fetch exists.

- **2026-07-21 — Preregistered dedicated Tock Cargo-cache preparation
  (ADR-0329).** A fresh ignored cache may receive one exact locked networked
  fetch only after its producer/tests/registration are pushed. It must then
  pass the v1 metadata gate with network removed and cache read-only, retain a
  canonical whole-tree inventory, and report OOM/atomic-cleanup state. This
  phase cannot compile, capture, admit, query, or rerun v1. No fetch exists.

- **2026-07-21 — Accepted ADR-0328 as a negative cache-preflight result.**
  After producer commit `a2051514` was pushed, the first official capped
  invocation stopped before Cargo execution: locked-offline metadata requires
  uncached `ghash 0.4.4`. Zero builds/modules/extractions/admissions/queries and
  no output/partial directory exist; no OOM-delta failure was reported. Exact
  negative metadata is committed. V1 cannot be rerun after an observed cache
  refill; only a separately preregistered dedicated-cache v2 may continue.

- **2026-07-21 — Froze the ADR-0328 Tock capture producer before execution.**
  The producer enforces complete traversal-safe Git archives, distinct roots,
  locked offline metadata/builds, exact Bubblewrap argv, raw module identity,
  LLVM-22 symbol extraction/assembly, checked admission, atomic output, and
  cgroup limit/OOM accounting. Ten focused tests mutate registration/tool,
  archive/root/namespace/module/symbol/admission/resource boundaries and prove
  partial-output cleanup. The registration pins every producer and tool byte.
  No official build or target artifact exists at this checkpoint.

- **2026-07-21 — Preregistered authenticated Tock log2 LLVM capture
  (ADR-0328).** The producer must materialize two exact complete trees, build
  them offline at identical virtual roots with one locked read-only cache,
  require raw full-module equality, use hash-pinned LLVM 22 tools for exact
  symbol extraction/assembly, and admit both functions before atomic local
  output. This is zero-result registration: implementation, target bytes,
  property queries, and scoreboard evidence do not yet exist.

- **2026-07-21 — Accepted checked LLVM call-result range and `ctlz` semantics
  (ADR-0327).** The exact typed/canonical syntax, range/zero poison
  definedness, selected-arm behavior, exhaustive widths 1--8, deterministic
  32/64-bit rows, independent threshold-partition proofs, and four semantic
  mutation classes pass. The standing inventory is 82 variants / 18 groups /
  12 binaries / 129 tests under the one-job 4 GiB cap. This admits only the
  prerequisite; authenticated Tock capture, target proofs, and scoreboard
  measurement remain separately preregistered work.

- **2026-07-21 — Selected Tock integer logs and preregistered checked LLVM-22
  support (ADR-0327).** The replacement target is two real kernel helpers used
  by MPU, ADC, and watchdog code. A non-crediting exact owning build exposes a
  bounded gap: call-result `range` poison and `llvm.ctlz` zero-poison semantics.
  The proposed gate requires typed/canonical lowering over existing BV terms,
  independent proofs, mutations, and fuzz before external capture. No Tock
  artifact, parser result, proof, or scoreboard row is admitted.

- **2026-07-21 — Closed the Maestro external-capture route negative
  (ADR-0326).** The corrected Bubblewrap root executes the pinned Cargo
  toolchain and starts the owning build, but Maestro's enabled TTY-font build
  downloads GNU Unifont. Network isolation makes that unregistered input fail
  before LLVM emission. Zero builds complete; no extraction, parser, solver,
  OOM, partial artifact, capture credit, or proof exists. T5.5.2 returns to a
  fresh replacement-target/build-route decision rather than a v4 relaxation.

- **2026-07-21 — Preregistered stable-virtual-root Maestro capture
  (ADR-0326).** The zero-result v3 route registers unprivileged Bubblewrap,
  mounts independent sources/targets at identical visible paths, removes remap
  flags, and retains raw module equality before extraction. No proof is
  authorized.

- **2026-07-21 — Rejected dependency-wide Maestro remapping as insufficient
  (ADR-0325).** Both v2 builds eliminate all real-root tokens, yet their raw
  full modules still differ in size/hash. The run stops before extraction and
  retains no partial output. A stable virtual-root build requires a new ADR.

- **2026-07-21 — Preregistered dependency-wide Maestro path remapping
  (ADR-0325).** The zero-result v2 retry preserves the upstream export flag,
  remaps every Cargo target dependency, requires zero real-root tokens and raw
  full-module equality, and only then permits symbol rediscovery and scalar
  parser admission. It grants no proof authorization.

- **2026-07-21 — Diagnosed the Maestro two-root LLVM drift (ADR-0324).** The
  complete diff classifies all 319,598 changed lines and identifies seven
  unremapped absolute paths from the `utils` dependency in each module. All
  three selected bodies enter the checked scalar profile, but their symbols
  and canonical hashes differ. No capture credit or solver result is claimed;
  a dependency-wide-remapped build requires a new preregistration.

- **2026-07-21 — Preregistered the Maestro LLVM root-drift diagnostic
  (ADR-0324).** The zero-row protocol freezes a complete local diff,
  all-line classification, root/symbol detection, and three-function checked
  projection comparison. It cannot weaken or revise ADR-0323, grant capture
  credit, or run verification queries.

- **2026-07-21 — Rejected the first Maestro external capture at its frozen
  root-independence gate (ADR-0323).** Two complete capped builds emitted
  unequal full LLVM modules (36,037,712 vs 36,038,199 bytes). The runner stopped
  before extraction/parser/solver work and atomically removed every partial
  target byte. The next action is a preregistered non-crediting drift
  diagnostic, not retroactive normalization.

- **2026-07-21 — Preregistered the selected external target capture
  (ADR-0323).** The zero-result T5.5.2 protocol binds exact Maestro source,
  tree, toolchain, build, LLVM tool, and symbol identities; requires two
  isolated byte-identical owning-kernel modules; permits only a known extracted
  `ModuleID` exclusion; measures parser admission without widening it; and
  keeps every third-party-derived byte local. No official capture, parser
  result, proof, or scoreboard row exists yet.

- **2026-07-21 — Selected the first P5.5 external target.** T5.5.1 freezes
  Maestro's three device-number encode/decode functions at exact revision
  `650a3f62`, with a pinned-owning-build feasibility observation, universal
  full-width inverse properties, a five-candidate comparison, precise P5.1
  capture gaps, and a no-vendoring gate for third-party-derived artifacts. No
  source, LLVM artifact, proof, or scoreboard row is admitted by this note.

- **2026-07-21 — Preregistered the authenticated source-contract/MIR bridge
  (ADR-0317).** The zero-row proposal freezes one total wrapping function,
  typed source-AST reuse, exact hand-built-summary equality, owning-Cargo-build
  MIR provenance, independent resolver verification/body discard, and a
  complete 256-input modular/inlined differential. Broader annotation and panic
  semantics remain separate.

- **2026-07-21 — Accepted typed straight-line scalar source contracts
  (ADR-0316).** `#[verify]` now consumes paired typed `requires`/`ensures`
  markers, retains the tail result, and separates normally returning
  postcondition replay from panic replay. The exhaustive lowered `u8` gate and
  all bounded package/semantics/strict documentation gates pass. The next P5.2
  boundary is authenticated source-contract-to-MIR summary generation, not
  broader syntax.

- **2026-07-21 — Closed artifact-readiness item 10 and added agentic related
  work.** The measured closure audit stops deferred cosmetic refactors and
  positions Axeyum/Glaurung against Veritas and Microsoft codename MDASH with
  explicit attacker-control semantics and claim boundaries.

- **2026-07-21 — Extracted Diophantine reconstruction.** Moved only the
  corrected family-specific body into a private 767-line child, preserving
  both public paths and the exact 868,243-byte Lean module. All focused,
  resource, namespace, full-library, lint, and documentation gates pass; the
  integer structural lane is closed.

- **2026-07-21 — Corrected and preregistered the Diophantine module seam.** The
  first compile gate expanded the dependency census beyond same-file callers:
  the authorized family-only body is 732 lines, while 17 shared context methods
  stay in the parent. Proof-byte, focused/resource, full, lint/doc, and OOM
  gates remain frozen. I6 is the integer structural lane's final planned
  extraction.

- **2026-07-21 — Extracted affine-growth reconstruction.** Moved the exact
  455-line production family into a private 467-line child, preserving proof
  bytes, paths, certificate semantics, and all focused/full/lint/doc gates.

- **2026-07-21 — Preregistered the affine-growth module seam.** Authorized only
  the seven-item, 456-line ADR-0097/0105 family with a proof-byte gate and all
  nine focused controls; residue and shared closed-quantifier helpers stay
  separate.

- **2026-07-21 — Extracted Euclidean-residue reconstruction.** Moved the exact
  344-line parent family into a private 354-line child, preserving the clock
  matcher, public paths, proof bytes, and all focused/full/lint/doc gates.

- **2026-07-21 — Preregistered the Euclidean-residue module seam.** Authorized
  only the four-item, 344-line ADR-0095/0104 family after rejecting a combined
  closed-universal/nested-XOR move across shared kernel helpers.

- **2026-07-21 — Extracted the single-pivot equality-partition proof family.**
  Moved the 1,188-line parent block into a private 1,200-line child with explicit
  dependencies and unchanged re-exports. Exact SDLX proof bytes, all twelve
  focused controls, 895 library tests, strict lint, and both docs profiles pass;
  the parent drops to 5,045 lines.

- **2026-07-21 — Rechecked Glaurung feedback and preregistered I3.** The July 16
  feedback still preserves strict correctness/deployability safeguards while
  later neutral controls supersede its broad speed and robustness claims. The
  measured artifact successor is only the 1,188-line equality-partition proof
  family; no behavior-bearing solver work is authorized.

- **2026-07-20 — Extracted the ADR-0108 reconstruction family.** Moved the
  1,449-line counterexample-cover block into a private 1,465-line child with
  explicit dependencies and unchanged re-exports. Exact generated Lean bytes,
  all eight focused/real-corpus controls, 895 library tests, strict lint, and
  both docs profiles pass; the parent drops to 6,233 lines.

- **2026-07-20 — Re-ranked artifact residuals after N1.** Authorized only the
  private I2 extraction of the 1,449-line ADR-0108 counterexample-cover proof
  family. Deferred the ABV replay/repair residual, stopped CAD consolidation at
  the algebraic boundary, and rejected raw file size as an automatic queue.

- **2026-07-20 — N1c closes rational CAD visitor parameterization.** Shared the
  identical rational N-variable recursion behind the explicit
  `RationalCellSelection::{OpenOnly, OpenAndRationalSections}` policy and kept
  both historical wrappers plus the algebraic value-domain traversal distinct.
  Exact strict `(1,1,1)`, non-strict `(1,-1,-1)`, and zero-cell `(0,-1,-1)`
  witnesses survive; open-only and section-first mutations fail their controls.
  The third fixed 2,000-seed sweep reproduces all 1,807 joint agreements and
  1,293 replayed SAT models with zero disagreements. All 86 focused NRA and 895
  library tests, strict Clippy, both rustdoc profiles, formatting, links, and the
  bounded OOM audit pass. Production falls 133 lines across N1; the 7,503-line
  file remains 41 lines below baseline despite the added semantic tests.

- **2026-07-20 — N1b shares two-variable CAD projection/root preparation.**
  Caller-specific deadlines and strict/non-strict sampling remain outside the
  helper. Exact-root and poll-removal mutation controls, focused NRA, the
  unchanged 2,000-seed tally, 893-library, lint/doc, and OOM gates pass.

- **2026-07-20 — N1a deduplicates rational CAD cell decision.** Strict and
  non-strict coverage remain in their named wrappers while one private helper
  owns their identical rational residual decision. Exact models, focused NRA,
  2,000-seed differential/replay, 891-library, lint/doc, and OOM gates pass.

- **2026-07-20 — N1 preregisters the CAD parameterization gate.** The measured
  census separates duplicated rational mechanics from strict/non-strict cell
  policy and algebraic value-domain lifting. Only the shared rational-cell
  helper is authorized next; later projection/visitor work remains gated.

- **2026-07-20 — artifact-readiness I1 isolates integer-inequality proof
  reconstruction.** Three public paths and representative generated Lean bytes
  are unchanged; one shared kernel helper is the only parent seam. Focused
  real-Lean/UFLIA/namespace gates and the complete 891-test library pass.

- **2026-07-20 — artifact-readiness A3 isolates lazy-ext CEGAR orchestration.**
  The new 446-line child has one parent-visible entry point and leaves the
  shared ROW/replay repair block in place after the dependency census disproved
  the original whole-lane seam. Focused extensionality/ROW/differential gates
  and the complete 891-test solver library pass.

- **2026-07-20 — reconciled the ten-item Glaurung consumer snapshot with current
  publication evidence.** A new planning note classifies each item as retained,
  superseded, closed, or open and links its controlling ADR. The configured
  batch assertion API now explicitly warns that the measured cold path lost;
  PLAN points to the reconciliation before historical numbers are reused.

- **2026-07-20 — artifact-readiness A2 isolates eager array-elimination UNSAT
  evidence.** A private named module now owns certificate emission and
  independent rechecking while its two public paths and private helper boundary
  remain unchanged. Focused mutation/Lean/namespace gates and the complete
  solver suite pass.

- **2026-07-20 — artifact-readiness A1 moves the ABV test module out of the
  production wall.** `abv.rs` is 3,510 lines shorter at 11,443 lines; test names,
  bodies, privacy, and all production behavior remain unchanged. The complete
  891-test library and strict lint/doc gates pass under the OOM-safe profile.

- **2026-07-20 — item 10 is re-ranked from measured residual structure.** The
  new artifact-readiness inventory separates low-risk module/test moves from
  correctness-sensitive CAD deduplication and selects the exact 3,514-line ABV
  test-module extraction as the next bounded checkpoint.

- **2026-07-20 — ADR-0314 accepts a typed cold bit-lowering mode.** The public
  `SolverConfig` can no longer represent simultaneous dense-demand and
  range-demand lowering. Existing builders remain compatible, default eager
  behavior and both experimental algorithms are unchanged, and benchmark
  artifact identity is preserved. The exact Glaurung production profile plus
  the full/minimal Axeyum gates pass under the bounded OOM-safe profile.

- **2026-07-20 — ADR-0313 accepts the constraint-builder namespace and closes
  R4.** Twelve existing `distinct`, cardinality, and pseudo-Boolean builders now
  have canonical paths under a full-only `constraints` facade. Derived
  reasoning, model replay, backends, and solver front doors remain outside the
  boundary. Warning-denied rustdoc measures 77→66 root items and 14
  constraint-subtree entries; minimal `qfbv` remains at 26 with only `proofs`
  exposed. Representative compatibility tests cover all three ownership groups,
  all 891 solver-library tests pass, and strict all-target clippy is clean under
  the bounded profile. Artifact-readiness work moves to the separate
  typed-configuration audit.

- **2026-07-20 — ADR-0312 accepts the general refutation certificate
  namespaces.** Fifty-one existing checked refutation entries now have canonical
  paths under arithmetic, finite-domain, structural, and UF certificate
  submodules; the QF_UF Alethe emitter joins its existing proof-format owner.
  General solvers and model replay are explicitly excluded. Warning-denied
  rustdoc measures 128→77 root items, 160 certificate-subtree entries, and 116
  proof-subtree entries; minimal `qfbv` remains at 26 with only `proofs`
  exposed. Representative compatibility tests cover every new submodule, all
  891 solver-library tests pass, and strict all-target clippy is clean under the
  bounded profile. Next R4 work is one final residual helper census with an
  explicit stop condition.

- **2026-07-20 — ADR-0311 accepts the interpolation API namespace.** Twenty-one
  existing interpolation entries now have canonical paths under a full-only
  facade with six logic-specific submodules. Model-based projection and two
  private-module verifier functions are explicitly excluded. Warning-denied
  rustdoc measures 148→128 root items and 27 interpolation-subtree entries;
  minimal `qfbv` remains at 26 with only `proofs` exposed. Representative
  compatibility tests cover every interpolation submodule, all 891
  solver-library tests pass, and strict all-target clippy is clean under the
  bounded profile. Next R4 work is an independent census of the remaining
  general refutation/certificate utilities and core solver helpers.

- **2026-07-20 — ADR-0310 accepts the exact SMT-LIB module boundary.** The
  existing full-only implementation module contains precisely the 25 structures
  and command/route functions already supported at the crate root, so it is now
  public directly rather than duplicated behind an artificial facade name.
  Private helpers remain private and root imports remain compatible.
  Warning-denied rustdoc measures 172→148 root items and 25 entries in
  `smtlib`; minimal `qfbv` remains at 26 with only `proofs` exposed.
  Representative compatibility tests cover solve, optimize, incremental, model,
  and string-route contracts; all 891 solver-library tests and strict all-target
  clippy pass under the bounded profile. Next R4 work is the independent
  interpolation census.

- **2026-07-20 — ADR-0309 accepts the objective-optimization namespace.** Forty
  public model-minimization, MaxSAT, and scalar/multi-objective entries now have
  canonical paths under three full-only `optimization` submodules. Pbls,
  textual SMT-LIB optimization commands, and `Solver` methods remain outside
  the boundary. Warning-denied rustdoc measures 211→172 root items and 43
  optimization-subtree entries; minimal `qfbv` remains at 26 with only `proofs`
  exposed. Representative compatibility tests cover all three submodules, all
  891 solver-library tests pass, and strict all-target clippy is clean under the
  bounded profile. Next R4 work is the independent SMT-LIB census.

- **2026-07-20 — ADR-0308 accepts the verification API namespace.** Sixty-six
  public transition-system/BMC, Horn, IMC, PDR, symbolic-execution, and tiny-BV
  reference-VM entries now have canonical paths under six full-only
  `verification` submodules. Root imports remain compatible and full-profile
  consumers are not migrated in the same change. Warning-denied rustdoc
  measures 276→211 root items and 72 verification-subtree entries; minimal
  `qfbv` remains at 26 with only `proofs` exposed. Representative compatibility
  tests cover all six submodules, all 891 solver-library tests pass, and strict
  all-target clippy is clean under the bounded profile. Next R4 work must keep
  optimization, SMT-LIB, interpolation, and refutation utilities separate.

- **2026-07-20 — ADR-0307 accepts the direct-theory namespace.** Sixty-three
  existing public contracts and procedures now have canonical homes under the
  seven-submodule full-only `theories` facade. Cross-cutting model replay,
  auto-dispatch, SMT-LIB, optimization, interpolation, symexec, verification,
  proof, and certificate APIs remain in their own domains. Warning-denied
  rustdoc measures 338→276 all-feature root items and 70 theory-subtree
  entries; minimal `qfbv` remains at 26 root items with no theory module.
  Representative compatibility tests cover all seven submodules, all 891
  solver-library tests pass, and strict all-target clippy is clean under the
  bounded profile. The next R4 decision requires a separate census of remaining
  cross-cutting root domains, not a broader theory bucket.

- **2026-07-20 — ADR-0306 accepts the array/quantified certificate namespace.**
  The exact catalog leakage named by the architecture review now lives under
  `certificates::{arrays, quantifiers}` with every historical root path retained
  as a hidden compatibility alias. Two finite-quantifier Alethe emitters join
  `proofs::alethe`; `check_model`, `check_model_with_assignment`, and array
  theory entry points remain at the root. Warning-denied rustdoc measures
  442→338 all-feature root items, 105 entries in the certificate subtree, and
  an unchanged 26-item minimal profile. Compatibility tests cover representative
  types and functions across both catalogs. All 891 library tests and strict
  all-target clippy pass under the bounded profile. Next: a separate measured
  theory API census.

- **2026-07-20 — ADR-0305 accepts the first measured root-API namespace.** The
  new `proofs` facade is the canonical documentation home for minimal UNSAT
  proof export plus full-profile Alethe, end-to-end certification, checked
  evidence, faithfulness, and Lean reconstruction. Historical root paths remain
  source-compatible hidden aliases, including the minimal Glaurung consumer
  imports. Rustdoc measures 549→442 all-feature root items and 36→26 minimal
  root items, with 113 entries organized below `proofs`. Default-`qfbv` and
  all-feature compatibility tests prove representative path identity; all 891
  solver-library tests, strict all-target clippy, and warning-denied rustdoc
  pass under the bounded one-job profile. R4 continues with separate measured
  theory and certificate groupings, not a broad breaking rename.

- **2026-07-20 — Split cohesive arithmetic reconstruction ownership and close
  R3.** The complete 4,970-line LRA/SOS family now lives in
  `reconstruct/arithmetic.rs`: exact-linear forms, the arithmetic kernel
  context, Farkas folds, SOS ring normalization, and disjunctive-LRA scanning
  remain together. The three public entry points are unchanged. Four
  production-only functions plus the private exact-linear form serve parent
  classification/dispatch; two additional Farkas helpers are visible only to
  existing tests. Representative LRA and single-square SOS Lean modules remain
  byte-identical at 7,747 bytes / FNV-1a `232852107906522853` and 1,088 bytes /
  `9042568084332375518`. All 891 solver tests pass; all-target/all-feature
  clippy and strict rustdoc are clean under the bounded one-job profile. The
  parent is now 2,793 lines / 122,834 bytes, with the thin ABV orchestrator
  intentionally retained. Next: R4 visibility/root-API audit, without mixing
  public renaming or solver behavior into the structural review.

- **2026-07-20 — Split bit-blast/QF_BV reconstruction ownership.** The complete
  1,956-line family now lives in `reconstruct/bitblast.rs`; all five public entry
  points are unchanged. Five production-only parent seams serve CNF or
  quantified-BV, and three additional parent-visible audit items preserve the
  existing datatype-projection no-assumed-axiom test. Pointwise BVAND and
  width-2 ripple-carry-add generated Lean modules remain byte-identical at 6,171
  bytes / FNV-1a `6475695101939760022` and 19,619 bytes /
  `1281267001421498970`; all 890 solver tests pass, and full-profile clippy plus
  focused rustdoc are clean under the bounded one-job profile. The parent is now
  7,748 lines / 346,174 bytes. Next R3 work is an arithmetic-family dependency
  and source-stability census, not a broad unmeasured move.

- **2026-07-20 — Split Tseitin CNF reconstruction ownership.** The distinct
  1,578-line gate-introduction family now lives in `reconstruct/cnf.rs`; its
  public rule entry point is unchanged. Eight shared context methods, one
  assignment type/constructor, and six proof helpers are `pub(super)` only with
  existing resolution-test, quantified-BV, direct-certificate, or bit-blast
  consumers. Specialized n-ary `and_pos` and general `xor_neg1` generated Lean
  modules remain byte-identical at 3,358 bytes / FNV-1a
  `14531428178443531371` and 4,504 bytes / `11358181693276788078`; all 889
  solver tests pass, and full-profile clippy plus focused rustdoc are clean
  under the bounded one-job profile. The parent is now 9,680 lines / 433,992
  bytes. Next R3 work is a measured bit-blast dependency/source census.

- **2026-07-20 — Split propositional resolution reconstruction ownership.** The
  2,150-line resolution/RUP/CPS family now lives in
  `reconstruct/resolution.rs`; the separate CNF gate-introduction family remains
  parent-owned for the next R3 slice. The existing public entry point is
  unchanged, and all cross-family context, type, and helper seams are
  `pub(super)` with measured consumers in CNF, quantified-BV, direct-certificate,
  or bit-blast code. A representative multi-step generated Lean module remains
  byte-identical at 1,651 bytes / FNV-1a `3433224910840366031`; all 888 solver
  tests pass, and full-profile clippy plus focused rustdoc are clean under the
  bounded one-job profile. The parent is now 11,225 lines / 498,127 bytes.

- **2026-07-20 — Split quantifier reconstruction ownership.** The cohesive
  853-line general universal-instantiation and existential-elimination family
  now lives in `reconstruct/quantifier.rs`; the specialized quantified-BV
  instance-set module remains separate. Both public entry points are unchanged,
  shared clause/resolution/kernel machinery stays parent-owned, and the only
  added cross-seam visibility is a test-only forall-axiom helper. Universal and
  existential generated Lean source snapshots remain byte-identical, all 887
  solver tests pass, and full-profile clippy plus focused rustdoc are clean under
  the bounded one-job profile. The parent is now 13,350 lines / 580,831 bytes.

- **2026-07-20 — Split datatype reconstruction ownership.** The cohesive
  2,313-line axiom-free tester/distinctness/injectivity/acyclicity family now
  lives in `reconstruct/datatype.rs`; the parent retains datatype-aware term
  translation and one four-route dispatch import. Four generated Lean source
  snapshots remain byte-identical, all 886 solver tests pass, and full-profile
  clippy plus focused rustdoc are clean under the bounded one-job profile.
  The remaining ABV reconstructor is only orchestration and stays parent-owned.

- **2026-07-20 — Split equality reconstruction ownership.** R3's first proof
  family now lives in `reconstruct/equality.rs`: reflexivity, both symmetry
  forms, binary/n-ary transitivity, and n-ary congruence. Shared literal parsers
  and the universal kernel gate stay parent-owned; the existing public entry
  point and three narrow clausal-walk seams preserve the surface. Two generated
  Lean source snapshots remain byte-identical, and all 885 solver library tests
  plus full-profile clippy pass under the bounded one-job profile.

- **2026-07-20 — Split direct structural reconstruction ownership.** The
  34-variant lane moves to `reconstruct/direct.rs` behind one dispatch seam;
  main reconstruction drops below 17,000 lines with byte output, kernel gates,
  884 tests, and clippy unchanged.

- **2026-07-20 — Parameterized 29 direct structural Lean wrappers.** A measured
  reconstruction inventory and exhaustive legacy-equivalence test precede the
  change. Twenty-six repeated emission tails now use the existing three-row
  helper; named certificate validation and kernel checking remain unchanged.

- **2026-07-20 — Deduplicated binary conjunction walkers.** One crate-private
  helper replaces 15 identical `collect_top_conjuncts` implementations; the two
  semantically different walkers remain local. The full 883-test solver library
  suite and full-profile clippy pass.

- **2026-07-20 — Accepted the corrected engine-cache factorial.** The fresh
  ADR-0304 successor passes all 120 producer reports and the unchanged analyzer.
  Warm reuse is additive in 2/4 exact and 3/4 structural driver cells, but the
  engine cache slows every variance-qualified already-warm comparison and costs
  7.6%--67.3% mean maximum RSS. The cache remains experimental; no pooled
  headline or rejected ADR-0303 timing is reported.

- **2026-07-20 — Rejected the first engine-cache factorial and froze the exact-
  identity correction.** All 120 producer reports pass, but the independent
  analyzer correctly rejects because opportunity v1 classified exact hits by
  textual query SHA instead of ADR-0303's canonical assertion set. No eviction,
  bypass, or replay failure permits a bounded-delta exception. The rejected
  campaign retains zero accepted ratios. Opportunity v2 moves 2,133 occurrences
  from implication to exact (8,001 exact; 8,563 structural unchanged), and
  ADR-0304 freezes a fresh otherwise-identical zero-row rerun.

- **2026-07-20 — Froze the executable engine-cache factorial at zero rows.**
  Glaurung `202786c` implements the sound bounded cache and complete v2 replay
  telemetry; Axeyum `14834d2f` provides the six-mode runner/analyzer. Eighteen
  focused Rust tests and seven tooling tests pass. A clean-source one-job build
  produced the registered pure-Rust replay executable, and read-only preflight
  validates all 20 traces plus every source, artifact, tool, executable, library,
  environment, CPU, and cgroup binding. The first cold-off pilot produced no
  report and failed its terminal owner gate; the retained failure selected a
  tested cold-owner-lifecycle correction before any timing row or ratio existed.

- **2026-07-20 — Preregistered the engine-cache/warm-state factorial.** ADR-0303
  freezes six fixed-stream modes, sound exact/SAT-superset/UNSAT-subset rules,
  bounded deterministic eviction, separate-process memory attribution, and the
  criterion for calling warm state additive under each cache policy. The
  implementation and timing registration remain deliberately absent at the
  zero-row boundary.

- **2026-07-20 — Measured the structural ceiling for a GREEN-style cache.** The
  accepted six-cell traces show 45.48% exact and 66.37% exact-plus-implication
  cache-addressable checks across one four-driver pass. Five focused analyzer
  tests reject exact-verdict conflicts, unsound implication directions, and
  fork-scope aliasing. The artifact explicitly makes no performance or
  additivity claim.

- **2026-07-20 — Recorded the first symbolic-CVE reproducibility machine.** The
  preregistered Axeyum/Z3 rotation passes exact within-authority stability and
  backend-invariant finding/work identity over 32 executions. The analyzer
  correctly refuses the cross-machine claim until a second genuine machine
  contributes; model diversity remains visible rather than being normalized
  away. A separately tested deterministic pack/verify/unpack tool closes the
  artifact-transfer gap without committing binaries or changing the protocol.

- **2026-07-20 — Preregistered symbolic-CVE reproducibility as three explicit
  projections.** ADR-0302 and its versioned runner require two rotated Axeyum/
  Z3 repetitions per real machine, exact authority-report stability, exact
  backend finding/work/stop identity, replay-valid witnesses, and at least two
  distinct machines. The isolated Glaurung producer now has canonical object
  identity, correct backend labels, and a git-pinned QF_BV Axeyum dependency.
  Six runner/analyzer tests and both producer authority tests pass. No full
  matrix row is counted before the preregistration commit.

- **2026-07-20 — Consolidated the strict consumer-boundary methods result.** A
  new verification note gives the exact empty-model, declared-extension,
  declared-concat, and W128-adapter failure shapes; identifies which layer
  exposed each; records the Glaurung fix revisions; and binds them to Axeyum's
  named negative, normalized-positive, model-state, replay, and four-oracle
  gates. The Glaurung width-contract regression now checks exact `IrError`
  variants and complete actionable messages instead of loose substrings.

- **2026-07-20 — ADR-0300 closes dense memo indexing as negative evidence.**
  Six frozen order-balanced pairs preserve every decision, oracle/manifest
  agreement, model replay, and AIG/CNF structure identity. Dense indexing has a
  favorable bit-blast point estimate (paired geometric mean 0.9222, exhaustive
  bootstrap upper 0.9774), while cold total (0.9927, upper 1.0183), qualifying
  families, and paired RSS (maximum 1.0052) also pass. The candidate is still
  rejected exactly as preregistered because baseline bit-blast CV is 3.0023%
  and candidate CV is 6.8664%, above the 3% ceiling. The exact 12-run artifact
  and analysis are retained; production is restored to BTree. An earlier
  incorrectly parallelized Cargo invocation is separately discarded after the
  kernel recorded a 4 GiB cgroup OOM; all accepted Rust validation uses one
  Cargo/build job inside the cap. No timing rerun is authorized to select a
  quieter sample.

- **2026-07-20 — ADR-0300 freezes representation-neutral BTree memo telemetry
  before observation.** Artifact v39 adds per-instance and aggregate full-lowering
  memo representation, source/slot/occupancy, lookup/hit/write, payload length/
  capacity, conservative native logical bytes, actual/expected root bits, and
  explicit invariants. Profile-only deterministic FNV-1a digests cover the
  ordered AIG, roots, term/symbol lift maps, CNF clauses/roots, and CNF lift map;
  they are regression detectors, not cryptographic evidence. The independent
  analyzer validates the exact fixed configuration/population/family partition,
  manifest and in-process Z3 agreement, model replay, every row and re-summed
  aggregate, then permits only the preregistered BTree-to-dense storage delta.
  Synthetic mutation tests reject malformed digests, failed invariants,
  structural drift, and >110% logical storage. Profiled BTree accounting and
  explicit unprofiled/demanded unavailability are covered from lowering through
  typed solver stats and JSON. Focused tests, Clippy, rustdoc, QF_BV profile,
  scalar and simd128 WASM builds, analyzer tests, formatting, and docs links pass
  serialized inside 4 GiB with zero swap. The clean 162-query BTree artifact is
  next; no dense code has been admitted yet.

- **2026-07-20 — ADR-0300 preregisters dense full-lowering memo indexing.** The
  zero-row decision corrects the candidate note's missing scratch reproduction
  and tests only `Vec<Option<Vec<AigLit>>>` against the current BTree baseline.
  Artifact-v39 telemetry must land before either fixed-corpus observation;
  exact AIG/CNF/verdict/replay and memo accounting precede six balanced timing
  pairs. Bit-blast improvement, cold-total non-regression, stable families/
  variance, and <=5% RSS are all required. Strict sorts, lift maps, warm
  semantics, and the correctness/deployability publication frame do not change.

- **2026-07-20 — ADR-0299 accepts checked MIR checksum composition.** The
  implementation stays in the located non-panicking typed executor, verifies
  the shared relation and panic freedom against the checked MIR body before
  discarding it, and gives the caller a distinct internal result plus separate
  assumption. Cross-IR modular equivalence, weak-contract countermodels,
  100,000 valid plus 100,000 invalid choices per IR, strict mutation/`Unknown`
  failures, 81 variants / 17 groups / ten binaries / 114 tests, and the full
  package/doctest gate pass. The complete route peaks at 1.8 GiB with zero swap
  inside the 4 GiB cap. General panic contracts, annotations, effects, loops,
  memory calls, and performance claims remain open.

- **2026-07-20 — ADR-0298 accepts relational checksum-call havoc.** A fresh
  internal return, its LLVM definedness, and its asserted postcondition remain
  distinct. Exact `sum16` body verification/discard, modular/inlined MIR+LLVM
  proofs, 100,000 valid plus 100,000 violating choices, strict sort/namespace/
  mutation gates, and the replayed weak-contract countermodel all pass. The
  standing gate is 76 variants / 16 groups / ten binaries / 108 tests; complete
  package tests/doctests pass under the 4 GiB cap with test debug metadata
  disabled. The earlier parallel invocation OOM and stopped full-debug retry
  are disclosed but not counted. MIR calls, loop havoc, annotations, and
  effects remain open.

- **2026-07-20 — ADR-0297 accepts scalar call-requirement bad states.** The
  frozen `prefix && args_defined && !requires` rule passes exact formula,
  path-prefix/later-UB, site/span, depth-1 BMC, defined PAC source replay, and
  balanced 100,000-row gates: 33,334 valid / 33,334 defined violation / 33,332
  source undefined, 16,666 omission controls, zero disagreement, zero dropped.
  Focused 17/17, standing nine-binary/98, and full package/doctests pass under
  memory caps. Relational results, annotations, and MIR calls remain open.

- **2026-07-20 — ADR-0296 accepts verified scalar contracts.** The exact
  `leaf` summary is checked against its body once and caller lowering stores
  only the verified summary. Normalized formulas, 100,000 differential rows,
  bounded/unbounded verdicts, component/body mutations, precise failures, and
  live provenance pass. A rejected general proof route's 67.4 GiB anonymous-RSS
  OOM is retained; the small exact checker and bounded fallback replace it. The
  standing gate expands to nine binaries / 94 tests at that checkpoint;
  ADR-0297 subsequently lands the explicit call-site obligation route.

- **2026-07-20 — ADR-0295 accepts checked direct-body calls.** The exact PAC
  source/module/functions reproduce from registered Glaurung and clang-21
  provenance. An explicit resolver supplies only a checked scalar,
  straight-line, memory/call-free `leaf` body; both loops reflect opt-in while
  ordinary and external calls remain rejected by default. Independent
  value+definedness/transition formulas, 100,000 tuples at zero disagreement,
  eager-UB/lazy-poison semantics, source replay, canonical syntax, semantic
  mutation, and fail-closed boundary tests pass. The standing gate expands to
  63 variants, 15 groups, and nine binaries / 88 tests. This is P5.2's inlined
  comparison baseline; explicit contract composition remains next.

- **2026-07-20 — ADR-0294 accepts the corrected semantic census.** The fresh
  artifact creates then reproduces exactly and a separate validator recomputes
  12/12 rows plus source-qualified selection. All 12 stop at typed CFG; precise
  causes split across wide memory, calls, `alloca`, and a non-scalar result, so
  the selected T5.1.2 audit lane authorizes no catch-all implementation.

- **2026-07-20 — ADR-0294 rejects its first artifact and freezes a reproducible
  correction.** Semantic rows were stable at 12 typed-CFG
  `unsupported_instruction` declines, but byte reproduction failed solely in 12
  path-bearing extracted hashes. The first artifact and failure report are
  retained. The correction excludes only the required ModuleID comment from the
  hash and fixes function identity to source+name before rerun.

- **2026-07-20 — ADR-0294 preregisters the Glaurung loop semantic census.** The
  exact zero-row producer and private classifier preserve every parser/reflector
  rejection and require 12/12 accounting. Both admitted fixtures, precise
  rejection mutations, strict Clippy, manifest/selection tests, pinned tools,
  and real LLVM extraction pass before formal observation.

- **2026-07-20 — ADR-0293 accepts a negative loop-shape selection.** The exact
  result was created then reproduced byte-for-byte: 11/12 loop rows match the
  existing self-loop structure and the sole rejected early-exit row is confined
  to one function/source. It fails the frozen diversity gate, so no capability
  is added. The retained-result validator recomputes every identity and total;
  semantic eligibility remains the next evidence step.

- **2026-07-20 — ADR-0293 preregisters a real Glaurung LLVM loop-shape
  census.** The zero-row manifest, fail-closed analyzer, captured-output unit
  tests, exact source/tool identities, and diversity-gated selection rule are
  frozen before the 12-source result. The earlier three-source pilot is
  disclosed and cannot authorize an implementation.

- **2026-07-20 — ADR-0292 accepts the first checked single-latch LLVM natural
  loop.** The registered `capdiv` fixture now yields two deterministic checked
  path relations with simultaneous latch PHIs and path-local division UB.
  Independent formulas, 50,000 concrete tuples, a wrong eager-UB refutation,
  k-induction/BMC, source replay, precise profile negatives, and non-panicking
  mutations pass. The existing BMC engine supplies bounded k-unrolling; no
  duplicate CFG semantics engine was added. The standing runner is now eight
  binaries / 81 tests with all 62 enum variants still exactly owned.

- **2026-07-20 — ADR-0291 accepts the first typed LLVM loop bridge.** The exact
  `capsum8` compiler fixture now parses with a strict implicit-entry identity,
  round-trips canonically, and automatically yields a checked PHI/parameter
  `TransitionSystem`. Unbounded/bounded safety, independent formulas, 20,000
  recurrence tuples, poison/UB/shape negatives, and separate source replay for
  abstract reachability pass in the expanded standing semantics gate. The
  historical parser is only a differential control; broader loops and unroll
  fallback remain open.

- **2026-07-20 — ADR-0290 accepts the T5.1.6 semantics admission gate.** The
  source-derived manifest owns 62/62 checked variants with proof plus
  deterministic fuzz/replay evidence. Independent scalar truth tables prove 96
  guarded goals and exhaust 11,248 rows; 11 MIR/LLVM pairs agree on 110,000
  tuples; `lut3` stays hypothesis-bounded; five wrong transforms still refute
  with replayed models. Ten checker mutations and the exact seven-binary,
  60-test runner pass through one `just`/CI command.

- **2026-07-20 — ADR-0289 accepts the Cargo-owned MIR selection seam.** A
  standalone locked fixture now reaches the checked reflector from its own
  explicit Cargo build in one command. Two runs reproduce 1,438 raw bytes and
  identical typed/term summaries; exact store/load safety and final-memory
  proofs plus source replay pass. The command is no-clobber/no-partial, exact-
  compiler CI is mandatory, and precise target/syntax/reflection failures stay
  visible. Fixing selected-name scanning permits unrelated unsupported
  functions without softening the selected function's types.

- **2026-07-20 — ADR-0288 accepts authenticated checked MIR byte memory.** The
  exact rustc fixture grows to five functions / 3,262 raw bytes with a
  conditional store and reproduces byte-for-byte. New `reflect::mir::{syntax,
  checked}` modules select and type one named function without source-driven
  panics, reject unsupported profiles through stable located classes, derive
  bounds panic at every access, execute stores, and join branch-local result,
  panic, and final bytes. Exact straight-line/conditional memory proofs,
  absent/wrong-assert tests, deterministic terms, source replay, an execution-
  limit gate, the migrated authenticated bounds proofs, and the shared MIR/LLVM
  roundtrip specification pass. The legacy line reflector remains unchanged;
  general places, aliases, wide memory, and whole-crate extraction stay open.

- **2026-07-20 — ADR-0285 rejected at the fixed storage gate; no timing.** One
  clean artifact-v38 process reproduces 162/162 decisions, 88 SAT replays,
  manifest/Z3 agreement, every legacy construction count, and all 162 flat-
  offset invariants. Aggregate logical storage is 54.08% of the legacy lower
  bound, but only 157/162 rows meet the preregistered per-instance <=80% rule;
  the five misses are singleton clauses with 32 or 64 literals. The analyzer's
  nonzero exit is retained as the decision, not repaired by a post-observation
  threshold change. Artifact SHA-256 is `fe0c9cde...2069f`; rejection-summary
  SHA-256 is `e62800f4...08086`. Commits `56936920` and `f3456365` restore the
  prior production representation.

- **2026-07-20 — ADR-0285 pre-observation implementation and validator gate
  complete (`725858b1`, `a57d5ace`).** At this historical checkpoint the
  candidate CNF formula was flat, all consumers used borrowed clause slices,
  and Tseitin canonicalization reused one scratch allocation. Artifact v38 made
  offset/storage evidence explicit;
  the independent analyzer requires and re-sums it under the frozen <=80%
  logical-byte gate while retaining v36/v37 historical compatibility. Native,
  QF_BV/no-default, ordinary wasm32, SIMD wasm32, correctness, profile,
  formatting, Clippy, rustdoc, and link gates passed. No fixed-corpus observation
  had occurred when the checkpoint was committed; the next structural process
  is the rejected result recorded above.

- **2026-07-19 — ADR-0269--0271 accept byte-reproduced bounded symbolic-CVE
  recall after preserving two protocol failures.** V1 ran eight cells and
  rejected Applicom's uniform 4 GiB synthetic target relocation. V2 ran four
  cells and rejected its own wrong telemetry field. V3 reads
  `path_stops.concrete_access_addresses`, retains all sites/counts/aliasing,
  permits only the registered per-row uniform delta, and reproduces exactly in
  two output directories. The retained SHA-256 is `13f8d286...bbb0e8`; result:
  2/2 selected pairs detected, 2/2 fixed sides clean, 0/2 fixed-side false
  positives, 8/8 cells acceptable. Scope remains the two artifact-admitted
  preselected positives. The next integration action is warm in-process
  Bitwuzla, not more concretization or frontend expansion.

- **2026-07-19 — ADR-0268 accepts corrected admitted-LLVM surface measurement.**
  The tested analyzer narrows each module to the registered handler and
  recursively defined direct callees, strips debug-only inflation, and reports
  complete operation/call/global/memory blockers without executing a frontend,
  detector, or solver. Exact four-side execution waits for a committed
  analyzer/tool registration. A first exact v1 output was deleted before
  acceptance when rerun exposed scratch-path-dependent `ModuleID` hashes; v2
  normalizes only that line; two exact v2 runs are byte-identical. The measured
  memory/global/helper/inline-assembly surface rejects a general LLVM parser as
  the minimum campaign route and selects Glaurung's existing AArch64 ELF→LLIR
  seam for the separately gated frontend.

- **2026-07-19 — ADR-0267 retains 4/12 paired artifact admission.** The exact
  campaign attempts all twelve sides and restores the worktree. PCI endpoint
  and Applicom pass both sides; UVC/DRM fail ordinary-vs-embedded executable
  identity and both block handlers lack standalone ordinary-ELF text symbols.
  No flags or membership change. The minimum frontend denominator is two pairs;
  no frontend or detector row has run.

- **2026-07-19 — ADR-0266 accepts the tested symbolic-CVE artifact builder and
  exact selected campaign.** Twelve unit gates and a two-side noncandidate LLVM-18 pilot validate
  non-overwriting Kbuild command replay, complete executable-section byte
  identity, exact handler presence across ELF/IR, tool hash checks, explicit
  failures, and clean worktree restoration. The exact six-candidate/twelve-side
  campaign then passes builder, preflight, commit-parent, clean-worktree, and
  tool-identity validation with zero builds. No selected side has run.

- **2026-07-19 — ADR-0265 accepts the paired symbolic-CVE artifact/frontend
  preflight.** Exact translation units, handlers, entry ABIs,
  attacker inputs, environment obligations, clean Linux source/Makefile joins,
  and a clean no-Linux-detector Glaurung baseline are bound before candidate
  build. The pilot selects per-TU embedded-bitcode command replay with
  executable-byte identity. The exact committed preflight validates all six
  rows and the 1/2/1/2 entry partition with zero selected build, frontend, or
  detector executions; no executability or recall claim is made.

- **2026-07-19 — ADR-0264 accepts the corrected symbolic-CVE handler identity
  before execution.** The external `CVE-2024-49994` row names
  `blk_ioctl_discard`, but its `BLKSECDISCARD` overflow and fixed guard are in
  `blk_ioctl_secure_erase`. V1 is preserved as invalidated history. V2 records
  declared/effective handlers and searches the effective symbol. The committed
  run accepts all 22 rows, the unchanged 6/16 partition, and the sole
  secure-erase correction; no artifact, frontend, detector, recall, or
  performance row was observed.

- **2026-07-19 — ADR-0263 historically accepted symbolic-CVE corpus
  qualification; ADR-0264 later invalidates its handler join.** The committed
  v1 validator accepts all 22 source-hash-bound census rows, unique
  fixing commits, vulnerable parents, patch hashes, corrected changed files,
  and handlers. Six direct scalar/address-safety rows are candidates and 16
  remain explicitly outside the current fragment. This is population
  qualification only; paired artifact materialization, frontend executability,
  detector scoring, and the eventual recall artifact remain open. Its
  file-level presence gate does not bind the effective CVE entry and must not
  feed execution.

- **2026-07-19 — ADR-0262 accepts wider authority timeout/policy sensitivity.**
  All 36 processes and six cells pass. Timeout changes nothing on the fixed
  first-20 prefix; AnyModel remains raw-divergent while LeastUnsigned restores
  exact raw parity at about 25x solve work and material time/RSS cost. All rows
  remain zero-high and unlabeled.

- **2026-07-19 — ADR-0262 preregisters wider authority timeout/policy
  sensitivity.** A non-overwriting runner and independent analyzer bind six
  first-20 tcpip cells, exact clean identities, N=3 order balance, corrected
  high-confidence output, and the v6 hidden-work gate before observation.

- **2026-07-19 — PLAN/STATUS/Pareto strategy reconcile ADR-0233 and the A0
  reframe.** Neutral timeout-sensitive formula breadth is complete. The active
  publication gap is now consistently named as wider v6 sole-authority finding
  evidence; strict typing is restored as the lead methods contribution, scalar
  concretization remains one measured knob, and symbolic memory remains the
  sole conditional architectural item.

- **2026-07-19 — ADR-0261 rejects private parity-leaf elision before timing.**
  Clean detached `8b95d42a` preserves all 162 correctness and structural-shape
  gates but changes attempts, duplicates, and attempted literals by zero. The
  analysis is byte-identical to ADR-0260, so the preregistered structural gate
  rejects the candidate and the no-op code is removed.

- **2026-07-19 — ADR-0261 implements private parity-leaf elision before
  observation.** One positive-root-only post-collection pass normalizes parity
  keys and removes later identical leaves without filtering helper nodes. The
  focused test began red; all affected CNF/solver/bench suites and strict
  Clippy pass. Commit before the fixed structural run.

- **2026-07-19 — ADR-0260 accepts duplicate origins; ADR-0261 preregisters
  private parity-leaf elision.** The fixed clean-detached artifact-v36 run
  passes all 162 correctness/identity gates and attributes 107,000 of 119,260
  duplicates to one same-owner positive-root forward-parity cell across 29
  queries. Counts select only the bounded ADR-0261 experiment; repeated
  unprofiled end-to-end timing remains mandatory before acceptance.

- **2026-07-19 — ADR-0260 implements duplicate-clause origin attribution before
  observation.** Artifact v36 retains actual first-clause provenance, later
  emission site, same/cross owner, and exact length/literal counts only in the
  profiled monomorph. Solver and analyzer identities fail closed, and the
  independent analyzer evaluates the fixed dominance/distribution gate. All
  focused/full affected suites, strict targeted Clippy, rustdoc, feature
  profiles, and a real micro artifact round trip pass. Commit before the fixed
  corrected-wide-v3 run.

- **2026-07-19 — ADR-0259 accepts cold CNF construction attribution; ADR-0260
  preregisters duplicate origins.** The fixed 162-query clean-detached run
  passes every decision/oracle/replay/invariant gate and finds 119,260 exact
  primary duplicates, concentrated 73.4572%/26.0230% in
  slice-partial/register-slice. Collision, repeated-literal, and complement
  work is zero. Preserve the raw artifact and analyzer; select no optimization
  before the profile-only first-origin/duplicate-origin follow-up.

- **2026-07-19 — ADR-0258 retains the capped external-DRAT no-selection.** All
  32 fixed hash-order exports succeed but produce only the same two-byte empty-
  clause proof. The complete attempt record is preserved, the cap is not
  widened, and no nontrivial-trace claim is made.

- **2026-07-19 — ADR-0257 preregisters nontrivial external DRAT selection.** A
  tested fixed-cap selector retains every hash-ordered attempt and requires a
  multi-line proof plus a failing empty-proof control over the same CNF before
  selection. No remaining real proof shape was observed before this protocol.

- **2026-07-19 — ADR-0256 accepts bounded external DRAT interoperability.**
  The unchanged real proof verifies with pinned `drat-trim`; the same proof
  against ADR-0255's fixed satisfiable CNF exits 1 with `s NOT VERIFIED`.
  ADR-0254's rejected final-line mutation remains recorded, and the accepted
  two-byte proof is explicitly not a nontrivial learned-clause trace.

- **2026-07-19 — ADR-0255 rejects ADR-0254's no-op tamper and preregisters a
  satisfiable-CNF control.** The real standard DIMACS/DRAT pair is externally
  verified, but deleting its only proof line cannot test rejection because the
  input CNF is already unit-refutable. Both outcomes and all hashes are
  preserved; the corrected checker sanity input is fixed before observation.

- **2026-07-19 — ADR-0254 preregisters neutral DRAT consumption.** A new
  fail-closed file exporter emits standard DIMACS/DRAT plus a hash-bound
  manifest after self-recheck. Before real export, the protocol fixes the
  lowest-hash holdout UNSAT, pinned `drat-trim` source/binary, positive
  verification, and a dropped-final-step negative control. Access-controlled
  query and proof bytes remain outside Git.

- **2026-07-19 — ADR-0253 accepts the wider real-query proof holdout.** Both
  clean fixed-policy runs decide and agree on all 1,024 rows, replay all 515 SAT
  models, and recheck all 509 CNF DRAT proofs. Stronger end-to-end coverage is
  stably 508/509 with one retained `slice-partial` hard timeout and no other
  alarm. The corrected real-query union is now 1,186 unique queries with 603
  SAT replays, 583 CNF proofs, and 582 stronger certificates.

- **2026-07-19 — ADR-0252 preserves a zero-query proof-holdout packaging
  rejection and preregisters exact materialization.** The full corpus root
  violated the selected manifest's exact-membership contract, so the benchmark
  stopped before producing an artifact or observing a holdout result. The new
  tested materializer retains the same 1,024 hashes and every ADR-0251 bound;
  it verifies exact source membership and bytes, copies into a new isolated
  root, and rechecks exact destination membership before corrected execution.

- **2026-07-19 — ADR-0251 preregisters a wider real-query proof holdout.** A
  tested selector excludes all 162 accepted representative hashes before
  taking fixed content-hash-first family/verdict quotas from the corrected full
  manifest. The committed 1,024-row result is exactly 515 SAT / 509 UNSAT,
  byte-reproducible, and disjoint. Two artifact-v34 runs under ADR-0235's
  unchanged killable certificate policy are next; no holdout query was observed
  before registration.

- **2026-07-19 — ADR-0250 makes hidden inner work fail closed.** The v6
  authoritative-finding contract requires one internally consistent worklist-
  stop partition per process, rejects deadline/timeout stops, and requires
  stable per-backend partitions. Twenty-six producer and eight validator tests
  pass, and the parser accepts the real one-function Dptf footer from isolated
  Glaurung `ff3c0a7`.
  Historical/default v5 reports remain unchanged; full v6 campaigns await
  owner-coordinated Glaurung integration.

- **2026-07-19 — ADR-0249 rejects the executed usbprint resource frontier.**
  The exact point-major run executes all 15 cells and preserves a common
  five-policy prefix of 10, but prefix-15/site-hash-one fails fixed-work
  reproduction despite identical 91/0 raw/high output. Post-result-only
  Glaurung candidate `ff3c0a7` partitions the hidden inner stops as 36 complete,
  three state-budget, and one wall-deadline. The result has no resource bracket;
  future evidence must reject deadline/timeout worklists explicitly.

- **2026-07-19 — ADR-0248 accepts exhaustive policy-difference review.** The
  fail-closed validator re-reads all 43 source/instruction sites from 14 clean,
  exact IOCTLance files and closes all 54 frozen rows: 30 ordinary request-
  plumbing rows, 24 duplicate sink presentations, zero independent primitives,
  and zero indeterminate. No scalar policy has a validated finding difference
  or residual gap, so symbolic-address memory remains gated off.

- **2026-07-18 — ADR-0248 preregisters exhaustive policy-difference review.**
  The accepted v3 source-backed raw union/intersection yields a bounded 54-row,
  43-site difference. A tested freezer binds every row to exact reports and
  source/binary identities and leaves every label pending before review.

- **2026-07-18 — ADR-0246 repairs stack-region semantics and ADR-0247 accepts
  the corrected v3 sweep.** Three preserved maximum-policy controls distinguish
  an `rsp`-only miss, an `rsp`/`rbp` free-symbol miss, and the accepted non-leaf
  expression-DAG rule. The final control restores 14/14 exact source-backed
  findings with no unexpected high row and exact authority parity. The exact
  preregistered run at Glaurung `7f682e5` accepts every scalar policy at 14/14.
  Tcpip remains zero-high/unlabeled; deterministic populations vary 84--110 and
  site-hash-one reaches roughly 264 seconds / 235 MiB under Axeyum. Symbolic
  memory remains deferred pending independently validated coverage headroom.

- **2026-07-18 — ADR-0243 accepts a source-backed nonzero finding control.**
  A new fail-closed join verifies exact IOCTLance source/binary identity and
  source-plus-disassembly evidence before comparing Glaurung's v5 producer-high
  population. Two repetitions per authority across nine planted WDM fixtures
  retain all 14 expected rows, no misses or unexpected high rows, identical
  work, and 108 separately visible diagnostics. The control is explicitly not
  a real-world recall or performance sample. A0 advances to sweep
  preregistration; symbolic memory remains conditional.

- **2026-07-18 — ADR-0238 accepts bounded two-extremum authority union
  parity while preserving the negative overlap result.** On the exact
  preregistered tcpip prefix, greatest-unsigned produces the same 84 findings,
  34,659 solves, and complete 513-choice/33,858-probe telemetry under both
  authorities in all repetitions. The least/greatest union has 125 rows (69
  common, 41 least-only, 15 greatest-only), but comparison with the 128-row
  arbitrary-model combined union leaves 33 arbitrary-only and 30
  extremal-only. Both policies remain opt-in; wider fixed work or genuinely
  broader model exploration is required before any preservation claim.

- **2026-07-18 — ADR-0236 records the first canonical tcpip authority
  policy.** The same-source N=3 any-model control preserves two stable Z3-only
  double-fetch rows on prefix 15. Opt-in unsigned minimization then gives both
  authorities the same 110 sinks, solve count, and complete model-choice
  telemetry with zero inconclusive choice. The artifact retains both cells and
  the exact four-patch Glaurung series. Canonicalization changes the shared
  population, so it remains opt-in. ADR-0238 later accepts a bounded
  two-extremum union but leaves 33 arbitrary-model-only rows.

- **2026-07-18 — ADR-0235 records killable whole-certificate isolation.**
  Artifact v34 isolates each representative UNSAT certificate in a
  source-hashed one-query worker. Two clean runs certify 74/74 under a 1500 ms
  process wall, while a same-source 1 ms control retains all 74 rows as hard-
  timeout non-certifications with zero dropped row or alarm. Wider real
  manifests remain open.

- **2026-07-18 — ADR-0234 records representative real-query end-to-end
  faithfulness.** Artifact v33 attempts every primary UNSAT and fail-closed
  repetition analysis joins two clean, identity-matched runs. Both decide the
  exact corrected 162-query manifest as 88 SAT / 74 UNSAT, replay every SAT
  model, and independently recheck both CNF DRAT and stronger end-to-end
  certificates for all 74 UNSAT rows under the named cooperative deadline.
  ADR-0235 subsequently closes whole-call process isolation for this
  representative denominator; wider real manifests remain open.

- **2026-07-18 — ADR-0233 records the repeated three-solver timeout
  frontier.** Artifact v32 runs Z3 after primary nondecision and reports all
  four populations. Twenty clean Axeyum/Z3 artifacts and 1,040 cvc5 rows over
  the same 52 hashes close the formula-level sensitivity gate with no wrong
  verdict or replay/operational failure; the all-decided 1000 ms tier favors
  cold one-shot Axeyum without changing the retained-warm claim boundary.

- **2026-07-18 — ADR-0232 records source-owner-retained cvc5 breadth.** A new
  fail-closed mode emits one solver session per contiguous source owner,
  persistent push/pop deltas from exact assertion-byte LCP, and temporary
  `check-sat-assuming` suffixes. All four accepted drivers preserve every
  verdict and model-output count over N=5; the compatible cold-reset mode still
  reproduces ADR-0222's exact Dptf batch hash.

- **2026-07-17 — ADR-0231 makes generated proof widening deadline-aware.** A
  shared absolute proof-search deadline removes seed 83's indefinite block
  without producing a verdict or excluding the row. All 1,505 selected
  width<=8 UNSAT formulas carry rechecked CNF DRAT; 1,487 carry stronger
  rechecked end-to-end certificates and 18 exact seeds remain visibly
  uncovered under 100 ms. Construction/checking and real-query faithfulness
  remain explicit follow-ups.

- **2026-07-17 — ADR-0230 records the real Glaurung QF_BV DRAT
  denominator.** The complete 128-query representative manifest decides and
  agrees with Z3 and expected results; 64 SAT models replay, and all 64 UNSAT
  rows carry independently rechecked inline DRAT with zero missing. The record
  explicitly separates CNF refutation from ADR-0226's stronger term-to-CNF
  faithfulness route and excludes proof-core timings from speed claims.

- **2026-07-17 — ADR-0229 records bounded four-driver authoritative finding
  parity.** Three order-balanced sole-authority repetitions per backend and
  driver preserve 302 byte-identical raw sinks across Dptf, vwififlt, IntcSST,
  and SurfacePen. Different solve counts on two drivers keep exploration
  equivalence and wider/timeout parity explicitly open; no canonical model
  policy is added without measured output divergence.

- **2026-07-17 — ADR-0228 records the bounded-warm time/RSS Pareto.** Current
  Dptf and SurfacePen controls preserve fixed Z3-authoritative work and findings
  while exposing 14.77--25.58% adaptive RSS overhead, greater than 98% retained
  owner hits, and zero fallback. Cumulative Axeyum work is reported only as a
  whole-policy metric; four-cell per-occurrence evidence remains the solver
  claim.

- **2026-07-17 — ADR-0227 executes and measures QF_BV WebAssembly.** The first
  runtime smoke exposed and fixed a wasm32-only AIG hash conversion trap that a
  green build missed. CI now executes SAT/UNSAT, and the accepted stable release
  artifact records explicit browser bundle/dependency size plus Node and real
  Chromium latency without claiming native parity or minimum parser footprint.

- **2026-07-17 — ADR-0226 records the first generated proof denominator.** A
  declared 169-row subset of 2,513 generated UNSAT formulas is 169/169 for
  rechecked CNF DRAT and end-to-end faithfulness certificates. Seed 83 exposes
  the no-deadline boundary for honest widening.

- **2026-07-17 — ADR-0225 completes the full-cvc5 QF_BV seed round.** All
  4,000 generated formulas decide and agree three ways; all SAT models replay;
  and the test now enforces five widths plus 35 operator classes. The cheaper
  250-row cvc5 sample remains the routine lane.

- **2026-07-17 — ADR-0224 lands fail-closed QF_BV multi-oracle fuzzing.** The
  standing 4,000-row Axeyum/Z3 generator now adds 250 deterministic cvc5 rows,
  original-model replay, strict/named Glaurung regressions, and a full-width
  linked-Z3 control. All accepted rows agree; separating cvc5 `unknown` from
  process/parser failure found and fixed invalid `!=` reproducer syntax.

- **2026-07-17 — ADR-0223 lands four-driver neutral cvc5 breadth.** Dptf,
  vwififlt, IntcSST, and SurfacePen preserve all 9,526 verdicts and exact model
  output over N=5, with 0.16--0.42% timing CV. The different cvc5 difficulty
  ordering strengthens regime characterization and closes neutral cold-reset
  breadth without claiming topology-equivalent warm performance.

- **2026-07-17 — ADR-0222 lands the neutral cvc5 ordered-SMT baseline.** The
  exact 561-check Dptf stream replays through cvc5 1.3.4 with full per-query
  resets and model output. N=5 preserves 317 SAT / 244 UNSAT / 0 Unknown and
  byte-identical stdout; CPU-pinned median is 2.593056 s at 0.4222% CV. This is
  accepted as a cold-reset external integration point, not a warm/in-process
  ratio.

- **2026-07-17 — ADR-0221 lands the ordered persistent-CNF core control.** A
  corrected all-decision capture excludes 130 replay-cache hits and replays all
  431 actual Dptf SAT-core calls through retained BatSat and Z3 Boolean over
  N=5. Every verdict and append-only prefix agrees. BatSat wins by a 3.5527x
  per-call solve geomean, moving the native warm-Z3 reversal to word-level
  representation/integration and rejecting Dptf as a reason for custom-core
  priority.

- **2026-07-17 — ADR-0220 lands retained-CNF capture and the fresh cross-core
  control.** All 244 Dptf warm-UNSAT DIMACS snapshots agree across BatSat,
  proof core, Z3 Boolean, and Kissat over N=5. Proof generation is 2.627x faster
  than BatSat before checking and every DRAT recheck passes. Fresh Z3 is much
  slower, so the warm loss moves to persistent learned state/topology rather
  than an intrinsic same-CNF core claim.

- **2026-07-17 — ADR-0219 lands the four-driver internal profile join.** One
  diagnostic run per driver pairs cold/warm phase records with all 9,526
  checks. Retention removes 98--99% of repeated AIG/CNF work and makes SAT the
  largest Axeyum warm phase everywhere. Dptf UNSAT has the highest retained
  structural additions and a CNF/SAT-dominated loss. Profile output overhead
  forbids a new speed ratio; the artifact selects an unprofiled identical-CNF
  neutral-core control next.

- **2026-07-17 — ADR-0218 lands fail-closed query-feature attribution.** The
  analyzer revalidates 20 raw traces and emits a 9,526-row join. SAT favors
  Axeyum on all four drivers; UNSAT behavior, consumer purpose, and exact-query
  reuse materially shape aggregate results. Retained-only wins remain on
  IntcSST/SurfacePen, while size alone fails to order the drivers. Exact JSON
  and CSV are committed; marginal reweighting is labeled descriptive.
  ADR-0219 subsequently completes the internal attribution gate.

- **2026-07-17 — ADR-0217 accepts the small-driver fair regime map.** Five
  fixed-work four-cell runs each preserve every decision and zero fallback on
  vwififlt, IntcSST, and SurfacePen. Warm Axeyum wins IntcSST 1.5315x and
  SurfacePen 1.5584x, while vwififlt is parity; combined with Dptf, the map is
  two Axeyum wins, one tie, and one Z3 win. The exact reports and CDFs are
  committed. Because cold outcomes split too, PLAN selects a query-feature
  join before naming the causal regime; ADR-0218 completes that join.

- **2026-07-17 — ADR-0212 defers wider direct-delta admission after the exact
  dxgkrnl no-op control fails stability.** The complete 85,449-event /
  17,400-check trace and independent 13,577-query / 8,816-model-read replay
  pass. All six ordinary-core reports have exact work, outcomes, cache
  behavior, zero continuation traffic, and zero correctness/lifecycle alarms,
  but time CV is 14.430%/8.306% versus the declared 3% limit. Slower-core
  calibration changes bounded outcomes and is rejected too. A new comparator
  `noop` expectation enforces that boundary. Direct delta stays opt-in;
  `win32k` moves from IOCTL evidence to a future service/callout frontend.
  The complete direct verification surface is green; the only unavailable
  wrapper-level coverage is nine recipe-rendering tests because this host does
  not provide `just`.

- **2026-07-17 — ADR-0211 accepts the native timeout-continuation default
  inside direct delta.** The 326,364-event / 71,136-check tcpip artifact passes
  producer validation and complete independent query/model replay. Three
  interleaved native pairs reproduce exact topology, findings, and
  implementation identity with zero correctness or lifecycle alarms.
  Continuation recovers 18/29 bounded nondecisions; p50 Axeyum time/RSS changes
  +2.027%/+1.021% with sub-0.4% timing CV. Glaurung `9ace064` makes missing=on
  with a fail-closed off override only within its still-opt-in direct route.

- **2026-07-16 — ADR-0210 accepts exact-stream timeout continuation.** The
  shared-DAG Glaurung `3c3c77e` producer and independent validator publish one
  301,852-event / 70,823-check tcpip stream under 4 GiB. Matched control and
  candidate replays preserve exact work, retained structure, complete model
  evaluation, and zero decided disagreements. One same-instance retry recovers
  7/14 initial timeouts, repeats 7, and errors 0; warm time/RSS change
  +1.97%/+0.034%. The mechanism passes while the native default remains gated
  on a production-topology exact-traffic/finding repeat.

- **2026-07-16 — PLAN integrates the latest ten-item Glaurung consumer
  feedback as standing invariants.** Strict/no-implicit coercion, warm/cold
  separation, lowering-before-SAT priority, warm-only `assert_configured`,
  actionable `IrError`, lean scalar model lift, bounded shared replay memo,
  honest cause-partitioned `Unknown`, self-rechecked DRAT, and pure-Rust/
  fast-failure-resistant measurement are now explicit. The reported “all
  decided within 250 ms” and generic WASM claims remain gated by actual
  counters/target builds rather than copied past contradictory evidence.
- **2026-07-16 — ADR-0209 keeps same-session timeout continuation opt-in.**
  Glaurung `6e5b255` reuses retained SAT state and recovers 5/14 full-budget
  tcpip timeouts at +1.98% Axeyum time/+0.034% RSS, with zero disagreements,
  errors, or resets. The candidate executes 19 additional queries and retains
  all 780 control findings plus two later null dereferences before the common
  analysis deadline, so fixed-work/repeated exact-output evidence is required
  before default admission. A later fixed-156-function pair still differs by
  176 queries because Z3 bounded nondecisions steer the live worklist;
  continuation recovers 3/11 at +1.47% time/+0.18% RSS, but exact ordered replay
  is now mandatory. Axeyum's same-instance fresh-deadline regression and all
  298 CNF tests pass.
- **2026-07-16 — ADR-0208 defers fresh cold retry after warm timeout.**
  Glaurung `35b25ab` recovers 4/15 tcpip occurrences with exact counters and no
  errors/disagreements, but leaves 11 unknowns and raises RSS 10.46%; the
  dxgkrnl zero-timeout control is inert. The diagnostic stays explicit/off.
- **2026-07-16 — ADR-0207 accepts Glaurung's declared-concat soundness fix.**
  Strict replay turns 733 tcpip Axeyum errors into one 57-bit concat root cause;
  Glaurung `d60ed0f` now honors both declared halves in text/Z3/Axeyum. Post-fix
  tcpip/dxgkrnl have zero adapter errors, resets, or SAT/UNSAT disagreements and
  remain 1.9x/2.7x faster. All nine residual Z3-decided tcpip formulas decide
  cold; four exceed 250 ms and are explicit timeouts. Pre/post LFS corpora plus
  Axeyum manifests are pushed at Glaurung `0249d44`/`7b1671e`.
- **2026-07-16 — ADR-0206 accepts exact Glaurung shadow-split capture.** A
  full-budget `tcpip` run exposes 973 decided/nondecided splits, 925 warm resets,
  and 480 assertion fallbacks across 70,639 queries, so the 33,501-query sweep
  is explicitly truncated rather than admitted. Glaurung `a6a5cc0` atomically
  captures exact split SMT-LIB bytes and stable result classes; four combined-
  feature tests pass. Build the 60-second tcpip/dxgkrnl corpora next.
- **2026-07-16 — ADR-0205 accepts the source-prefix production gate.** Glaurung
  `29031f8` commits 92,721 exact checks and a passing serial-snapshot comparison:
  SurfacePen time/ratio/RSS improve 16.11%/17.39%/0.36%; NETwtw10 improve
  6.07%/6.61%/1.72%. The exclusive control remains rejected on +4.06% Z3 drift.
  Direct stays opt-in while `tcpip`/`dxgkrnl` enter the repeated gate; zero-query
  `win32k` is tracked as dispatch coverage, not solver evidence.
- **2026-07-16 — ADR-0204 accepts source-identity direct sibling prefixes.**
  Glaurung `aee3418` uses immutable `Arc` ancestry to find the exact common
  source prefix before direct-session pop/push, without trusting depth,
  cloned-pool `ExprId`, hashes, or cloned solver state. Backend 42/42, explorer
  12/12, and Axeyum-only plus combined Z3+Axeyum regressions pass under 4 GiB.
  Direct remains opt-in; fail-closed gate calibration and repeated real-driver
  production measurement are next.
- **2026-07-16 — ADR-0203 defers the Glaurung direct-delta default.** The
  repeated 92,721-check candidate passes every correctness/identity gate and
  improves Axeyum time 10.98%/5.08% against equivalent transfer-only snapshot.
  It fails replacement of serial snapshot on SurfacePen time/ratio and
  NETwtw10 RSS (+16.73%). Glaurung `12925e9` commits all three clean artifacts
  and downstream ADR-012. Direct remains opt-in; source-identity/COW sibling-
  prefix sharing is the next GQ7 implementation target.
- **2026-07-16 — real direct-delta gate catches and contains sibling aliasing.**
  The first SurfacePen run reports 497/2,551 verdict disagreements when a
  depth-only direct marker shares ADR-0199's serial snapshot owner across
  opposite siblings. Glaurung `f4da0eb` disables that incompatible lease for
  direct mode; 11/11 explorer tests pass and the identical stream becomes
  2,551/2,551 agreed with zero unknowns/replay failures. The first causal
  numbers favor direct over transfer-only snapshot but not the serial-snapshot
  production policy, so the route remains opt-in and the repeated dual-control
  gate is next.
- **2026-07-16 — ADR-0202 accepts direct-delta warm-profile v7.** Glaurung
  `00bd660` emits explicit entry mode plus persistent/temporary query,
  translation, and root-encoding partitions without adding unprofiled solver-
  stats reads. Direct 4/4 and snapshot 6/6 producer smokes strictly validate;
  all 41 backend tests, combined-feature adapter coverage, 53 script tests,
  Ruff, and links pass. GQ7 now moves to the repeated ordered time/RSS gate.
- **2026-07-16 — Glaurung wires opt-in first-class explorer deltas.** Commit
  `f5a3b7a` replaces prefix rediscovery on the candidate route with explicit
  confirmed retain depth, persistent suffixes, and temporary assumptions.
  Missing/invalid/error lifecycle paths fail closed, cache/session gauges are
  released exactly, and stale acknowledgements cannot advance explorer state.
  Backend 41/41, explorer ownership 2/2, Axeyum-only direct tests 4/4, and the
  selected combined Z3+Axeyum adapter test pass under the 4 GiB wrapper. The
  change is pushed; per-check direct profiling and repeated ordered gates are
  still required before default enablement.
- **2026-07-16 — ADR-0201 accepts the first-class incremental solver trait.**
  `1058cf84` exports an object-safe retained assert/push/pop/check/assume
  contract and implements it for `IncrementalBvSolver`, while keeping one-shot
  snapshot facades distinct. Generic and trait-object tests, the 11-test warm
  suite, strict Clippy, and rustdoc pass under full and minimal `qfbv` profiles.
  Downstream direct-delta wiring and real-stream measurement remain explicit.
- **2026-07-16 — Glaurung lands the matching P5 direct-delta session contract.**
  Glaurung ADR-011/`8d8cd6f` adds object-safe IR-level incremental operations
  and an Axeyum session that translates only newly asserted roots while keeping
  symbol/model maps aligned with scopes and assumptions. Its complete 37-test
  backend group passes; explorer event wiring subsequently lands in
  `f5a3b7a` under the same strict opt-in.
- **2026-07-16 — ADR-0200 rejects the direct CNF open-addressing transfer.**
  Five clean 162-query processes per revision preserve all decisions, replay,
  and AIG/clause counters, but candidate mean CNF/total time regress
  8.55%/3.67%. The full tier is skipped by contract and `90e298f2` restores the
  accepted primary map. First-class incremental push/pop/assume returns to the
  front of the structural API queue while GQ5 awaits a larger attributed slice.
- **2026-07-16 — ADR-0192 accepts the bounded Glaurung cache default.** Clean
  repeated SurfacePen/NETwtw10 off/on artifacts preserve 185,442 combined
  decisions and findings while cache-on improves both drivers' Axeyum time,
  ratio, and median RSS within stable Z3 controls. Glaurung `e177142` defaults
  path-owned warm sessions on and preserves explicit off; generic Axeyum stays
  opt-in.
- **2026-07-16 — ADR-0191 lands the GQ8 client measurement control.** Glaurung
  `d5475f6` adds a default-off path-owned cache policy, fixed bounds, complete
  counters, fail-closed artifact validation, and a named off→on comparator.
  The 2,551-check SurfacePen smoke has 183 replay-checked hits and zero replay
  failures but is not acceptance evidence because it is dirty, single-run, and
  breaches the Z3-drift alarm. Clean repeated two-driver gating is next.
- **2026-07-16 — ADR-0188 accepts corrected shard variance and alarms.** Two
  complete 30,628-query raw/canonical composites establish sub-1% total/ratio
  CV except raw RSS and canonical word time, both still <1.9%. Fail-closed
  3%/3%/5% + 2% cross-commit guards and 46 tests are executable.
- **2026-07-16 — ADR-0187 accepts the corrected wide cold corpus.** Five
  drivers produce 30,628 zero-exclusion scripts, including 7,953 with wide
  roots. Exact clean raw/canonical shard sets are 0.446x/0.269x Z3 with all
  decisions and SAT model replays green; the corrected 162-query tier is now
  the regular semantic pin.
- **2026-07-16 — ADR-0186 accepts the pressure-adaptive Glaurung default.**
  Clean 92,721-check repetition clears every alarm; Glaurung `ca12028` defaults
  only path-owned Axeyum explorer solves and preserves an explicit off override.
- **2026-07-16 — ADR-0185 lands pressure-adaptive admission opt-in.** Glaurung
  `95c43cb` rejects purpose/fixed-small-cap alternatives, starts at two live
  sessions, and expands at 128 pressure events. Single SurfacePen/NETwtw10
  calibrations clear alarms with 30,907/30,907 agreement; repeat remains open.
- **2026-07-16 — ADR-0184 corrects wide assertion exports.** Glaurung
  `fcc2de5` preserves arbitrary-width native truthiness in text/trace output.
  The corrected SurfacePen trace validates; regenerate stale cold corpus hashes
  and reclassify 2,225 producer-malformed dumps.
- **2026-07-16 — ADR-0183 defers detected-reuse as default.** Repeated exact
  auto evidence saves 16--21% RSS but breaches the 3% time alarm on both
  families. Glaurung `ab3b27b` commits the artifact; auto stays explicit.

- **2026-07-16 — ADR-0182 lands detected-reuse warm admission opt-in.**
  Glaurung `4ae5469` promotes only repeated live paths. SurfacePen/NETwtw10
  remain fully agreed; auto reduces lineage RSS 16--21% at a 4.5--8.7% time
  cost. Repeat through the versioned gate before a default.

- **2026-07-16 — ADR-0181 publishes the clean lineage baseline.** Glaurung
  `51666a9` commits the clean six-process artifact: 92,721/92,721 checks agree,
  SurfacePen/NETwtw10 run at 0.242x/0.360x Z3, and median RSS is
  82,432/257,632 KiB. Validation, comparison, four tests, Ruff, and whitespace
  checks pass. Begin GQ9 topology/cost fitting; warm remains opt-in.

- **2026-07-15 — ADR-0180 lands lineage regression alarms.** Glaurung
  `a0e5f9f` adds post-identity 3% Axeyum, 3% ratio, 5% median-RSS, and 2%
  absolute-Z3-drift failures. Four tests and self-compare pass. Publish a clean
  baseline next; correctness/work gates remain non-configurable.

- **2026-07-15 — ADR-0179 lands fail-closed held-out lineage automation.**
  Glaurung `89aea59` versions source/environment/driver/policy/work/findings/
  resources, hard-limits children to 4 GiB, validates exact traffic, publishes
  atomically, and compares homogeneous artifacts. Three focused tests and a
  real SurfacePen run/validate/self-compare pass. Publish clean baseline and
  alarms next; solver semantics and GQ8/GQ9 authorization are unchanged.

- **2026-07-15 — ADR-0178 accepts repeated held-out 9/512 variance.** Three
  exact SurfacePen streams run at 0.243x Z3 / 0.34% Axeyum CV; three fixed-work
  NETwtw10 streams run at 0.360x / 0.44%, with identical 28,356 checks, 8,325
  path fallbacks, zero assertion fallbacks/resets, and 257,736 KiB median RSS.
  Glaurung `eb938ae` records the gate. Automate per-commit identity next; GQ8/
  GQ9 remain separate decisions.

- **2026-07-15 — ADR-0177 widens assertion admission to held-out depth.** Exact
  SurfacePen profiles reach 479 roots; 512 eliminates 965 avoidable fallbacks
  and improves Axeyum 34.9% versus 128 with flat RSS. A 23,797-check bounded
  NETwtw10 stream retains nine live sessions as the memory/time choice and has
  zero assertion fallback. Glaurung `90df708` defaults explicit lineage to
  9/512. Repeat held-out variance before GQ9; replay/cache boundaries unchanged.

- **2026-07-15 — ADR-0176 accepts bounded opt-in lineage admission.** Three
  order-balanced cap-9/cap-12 rounds preserve all 20,958 decisions per policy
  and weighted Axeyum time (5.088/5.091 s), while cap 9 lowers median RSS 8.0%
  on vwififlt and 6.3% on IntcSST. Glaurung `1f24d5d` defaults explicit lineage
  mode to 9 live paths/128 assertions with visible one-shot fallback and limit
  identity. Automatic warm selection and caching remain open; widen GQ10 next.

- **2026-07-15 — ADR-0174 defers bounded internal positive-AND flattening.**
  The exact/off-by-default candidate passes all semantic gates, but Dptf later
  helper reuse turns 83,544 immediately avoided clauses into a +17.62% retained
  clause regression and raises three-run unprofiled Axeyum mean 3.65%. Keep it
  off; move GQ5 to AIG construction cost per added node.

- **2026-07-15 — ADR-0173 accepts native-lineage CNF gate attribution.**
  Glaurung `21c01ce` adds exact per-check gate/root deltas to the 6,986-record
  v2 stream. Definitions own 71.75% of 11.73M clauses and AND-tree shapes own
  53.89% of halves; root fusion is saturated and duplicate/tautology counters
  are zero. Select one future-reuse-safe positive internal AND-tree flattening
  experiment and require lower repeated unprofiled native time.

- **2026-07-15 — ADR-0172 accepts exact native-lineage phase attribution.**
  Glaurung `13f4bbe` emits opt-in exact hash/path/delta records; Axeyum's new
  fail-closed summarizer accepts 6,986/6,986 decided records. CNF is 43.78%, bit
  blast 22.86%, and SAT 17.45%; translation is 3.74% and session creation 0.21%.
  The stream adds 11.73M clauses. Profiled time remains diagnostic; target
  causal warm gate/root encoding next under ADR-0171's unprofiled native gate.

- **2026-07-15 — native lineage receives deterministic capacity fallback.**
  Glaurung `49f1fe2` adds atomic process-wide live-path and per-snapshot
  assertion caps. Over-limit checks run one-shot, counters expose every reason,
  and over-limit retained owners close first. Dptf cap-zero/cap-one smokes stay
  561/561 agreed and finish with zero live paths. Calibrate memory-safe limits
  and phase-profile before GQ9 admission; this remains downstream plumbing.

- **2026-07-15 — ADR-0171 accepts native path-owned warm reuse, still opt-in.**
  Glaurung `b9febbd`/`950cca4` isolates one retained solver per explorer path.
  Three alternating three-driver rounds preserve all 41,916 combined shadow
  checks with zero disagreement/unknown/reset/finding changes. Weighted lineage
  is 0.746x Z3 versus snapshot 2.093x and cuts Axeyum time 65.5%, but median RSS
  rises 6.3%--31.0%. Bound lifecycle/memory/fallback, phase-profile the live
  path, and widen drivers before GQ8/GQ9 or default admission.

- **2026-07-15 — ADR-0170 accepts clean multi-driver warm-policy evidence.**
  At Glaurung `dbdc6bf`, all 3,769 occurrences across three drivers decide,
  agree, and replay. Weighted exact-cold/snapshot/lineage ratios are
  1.591x/1.049x/0.698x Z3, but snapshot wins only `vwififlt` and lineage wins
  Dptf/IntcSST. A universal snapshot or depth-only rule is rejected. Native
  per-lineage/delta ownership with snapshot comparison is next; warm remains
  opt-in. Glaurung's SAT-only choice and explicit extension-width repairs are
  downstream correctness fixes and preserve Axeyum's strict formal boundary.

- **2026-07-15 — ADR-0169 accepts complete assertions and separated backend
  timing.** Glaurung `497b1c6` and Axeyum `f272627e` preserve every traced root
  with producer-declared symbols and independently validate per-check Z3/Axeyum
  time. The clean one-driver artifact is 776/776 agreed with all 180 assertions
  materialized. Native Axeyum/Z3 is 2.095/0.808 s (2.593x); snapshot replay plus
  build is 0.476 s (0.590x Z3), while naive lineage is 1.291 s (1.598x). This
  selects snapshot for multi-driver repetition and native integration. The
  machine-readable depth gate is 45/46 faster buckets with a descriptive
  monotone threshold of 13; it does not authorize a default, cache, or product
  claim.

- **2026-07-15 — ADR-0168 accepts opt-in identical-occurrence policy
  controls.** Separate capped processes run exact-byte fresh cold,
  consecutive-snapshot LCP, and explicit-lineage replay after the same mandatory
  T2 checks. All remain 784/784 agreed. Timed replay is 2.737/0.545/1.371 s;
  snapshot high-water RSS is 38.4 MB versus lineage's 83.9 MB and avoids 7,378
  fork-root replays. Snapshot is selected for repetition, not default use. The
  captured `backend_nanos` wraps both shadow backends, so per-backend producer
  timing, complete assertion bytes, and multi-driver break-even remain T4.

- **2026-07-15 — ADR-0167 accepts opt-in per-lineage warm replay.** The ordered
  consumer owns one retained solver per path and replays only a validated parent
  prefix into a fresh fork; it never shares mutable SAT state. The bounded trace
  remains 784/784 agreed with original-model replay, and all 243 model reads are
  explicit (242 recorded-value matches, one valid divergence). The naive fork
  strategy replays 7,378 roots across 232 children and spends ~813 ms there,
  selecting identical-byte T4 controls and complete assertion/RSS capture next.
  Warm remains opt-in; GQ8/GQ9 remain downstream.

- **2026-07-15 — the post-ordered-trace aggregate gate finds and closes a
  package-entry regression.** The 4 GiB run passes the complete workspace
  verification/test/doc prefix, but the pinned Glaurung recipe initially cannot
  select between the established harness and the new ordered-trace replayer.
  `f6fcd81f` restores all unqualified harness recipes with an explicit package
  default. The repaired 128-query raw/canonical gates are 100% decided with zero
  errors, disagreements, or replay failures; foundational resources,
  rules-as-code generation/drift, and links pass. The refreshed frontier files
  contain timing-only changes. This does not alter the GQ7-first roadmap.

- **2026-07-15 — ADR-0166 accepts bounded ordered-trace T1/T2 functionality.**
  Glaurung's opt-in producer and external validator are pushed at `7a11c29` and
  `32cabb0`. Axeyum's independent `axeyum-bench` replayer verifies untrusted
  artifact identity, lineage and scopes; strictly parses and re-solves exact
  QF_BV scripts with original-model replay; and checks recorded choice values
  by satisfiability. The bounded real trace is green on 3,309 events, 235
  paths, 784 checks, 508 unique queries, and 243 choices. It measures 35.2%
  duplicate occurrences and 271 prefix extensions. T3 explicit per-lineage
  warm replay is next; no product dependency, default-policy, or speed claim is
  introduced.

- **2026-07-15 — the complete post-ADR-0165 workspace gate is green.** The
  first aggregate run correctly exposed stale motive-universe arguments in
  downstream `Or.rec`/`Exists.rec` reconstruction. Commit `de249d48` repairs
  those call sites; 874 solver unit tests pass, followed by the complete
  serialized `just check` under the 4 GiB wrapper. The gate covers format,
  strict Clippy, all workspace tests/doctests, warning-free docs, QF_BV profile
  checks, the pinned 128-row Glaurung regular corpus (100% decided, zero
  disagreements/replay failures), foundational/rules resource generation and
  validation, and link checking. Resume GQ7 ordered/multi-driver warm reuse.

- **2026-07-15 — ADR-0165 contains the Lean-kernel large-elimination P0.**
  `d26ad887` implements Lean's exact syntactic-subsingleton boundary and turns
  the full former proof-of-`False` into an active trusted-gate rejection. The
  positive/negative suite includes exact versus nested index exposure,
  potentially-Prop universe polymorphism, prelude recursor arities, and a
  generated constructor/proof/data-field matrix. `a10c8cde` pins Lean 4.30.0
  and makes a real-inductive/iota cross-check mandatory in CI; the pinned local
  run passes. This repairs one demonstrated class, not a blanket claim of full
  Lean-kernel equivalence.

- **2026-07-15 — the Lean-kernel large-elimination incident is a P0 soundness
  stop.** Concurrent commit `2cb298e2` records a direct derivation admitted as
  `theorem bad : False`. PLAN and the P3.6 phase table now put the
  `Prop`-subsingleton elimination fix, inverted exploit, adversarial universe
  coverage, and non-vacuous real-Lean inductive gate ahead of new assurance
  claims.

- **2026-07-15 — ADR-0164 accepts opt-in Glaurung snapshot-incremental
  reuse.** Structural assertion-prefix scopes retain arena/AIG/CNF/SAT state
  safely across cloned sibling pools. Three 13,126-query pairs remain fully
  agreed with zero unknown splits/resets and unchanged findings; median Axeyum
  falls 17.784→9.426 seconds and paired ratio 2.648x→1.462x. Keep it opt-in
  pending ordered lineage, multi-driver, latency/memory, and GQ9 policy gates.

- **2026-07-15 — PLAN/STATUS adopt the latest ten-item Glaurung order.** GQ7
  ordered warm integration, profiled real-client/bench overhead, and a dual
  pre-parsed-vs-real-Z3 baseline lead. AIG cost-per-node, measured CNF,
  causal rewrite policy, GQ8 reuse, now-material SAT tuning, non-regressing
  auto policy, and deeper capture follow in that order. GQ4 remains off after
  its failed gates; further cold work requires causal native evidence.

- **2026-07-15 — ADR-0163 accepts exact root-context dedup and rejects
  clause-level root indexing.** Opt-in residual attribution assigns 64,637 of
  69,632 post-ADR-0162 excess clauses to prior-root duplicates. Skipping 1,981
  repeated exact root/selector contexts cuts clauses 615,537→558,787 and the
  one-shot residual to 2.36%; two native pairs improve mean Axeyum 2.10% and
  normalized ratio 2.51%, with 13,126/13,126 agreement. Per-clause indexing
  reaches 550,900 clauses but regresses native Axeyum 2.16%, so it is removed.
  Move the primary client lane to GQ1 publication and GQ7 ordered warm reuse.

- **2026-07-15 — ADR-0162 accepts incremental direct positive-root fusion.**
  Selector-guarded positive AND leaves and structural XOR truth clauses bypass
  root/helper definitions without consuming global single-use assumptions;
  later polarity/scope reuse still emits ordinary definitions. The pinned gate
  cuts clauses 782,716→615,537 (-21.36%) with unchanged AIG and 128/128 clean
  verdict/replay gates. Two alternating native Glaurung pairs cut mean Axeyum
  time 18.484→17.648 seconds (-4.52%) and normalized Axeyum/Z3 4.0%. Attribute
  the remaining 12.75% one-shot clause residual before another fusion.

- **2026-07-15 — ADR-0160 accepts opt-in native Glaurung phase attribution.**
  Axeyum commit `c8ffb43d` adds overhead-free-by-default incremental stats;
  Glaurung commit `f201448` emits exact-hash ordered JSONL under an explicit
  environment switch; and the fail-closed Axeyum summarizer preserves
  occurrences, validates manifest overlap, and reports p50/p95, phases, and
  structure. The first 13,126-query Z3-authoritative stream is 100%
  decided/agreed and attributes 80.39% to bit blast+incremental CNF versus
  7.23% SAT. Its 6,061 duplicates prioritize the ordered GQ7 handoff, while
  exact AIG preservation plus clause inflation selects GQ5 gate fusion next.

- **2026-07-14 — ADR-0159 accepts fail-closed paired rewrite ablation and
  closes the current GQ3 tranche.** A new comparator and repeated recipe reject
  any source/environment/corpus/non-rewrite/configuration/correctness drift,
  pair by manifest path, and separate exact structural deltas from timing
  samples. Five clean rounds over four rules keep all 3,200 executions valid.
  Disabling `extract_extend` adds 6,259 term bits and 1.657 ms mean affected
  cold time, but none of the four rules changes an AIG node or CNF clause.
  Keep the rules; move optimization effort to native Glaurung entry-path
  attribution instead of adding more fire-count-driven extract rewrites.

- **2026-07-14 — ADR-0155 equality cancellation is accepted and makes Axeyum
  faster than Z3 on the full cold Glaurung corpus.** Default rewrite identity v4 adds only
  `bv.eq_add_constant_cancel.v1`: `s + c = k` becomes `s = k - c` modulo width,
  for either equality orientation and scalar or arbitrary-width constants.
  Exhaustive evaluation through width 3, wrap/129-bit/multiplicity/non-match
  fixtures, 110 rewrite tests, 31 benchmark tests, and strict Clippy pass under
  4 GiB. Five clean representative runs improve mean total/ratio 61.7%/61.3%.
  Five full runs improve mean Axeyum total 13.946 → 5.625 s and ratio
  1.829x → 0.730x Z3, with AIG nodes/clauses down 76.7%/75.4%. Every one of
  67,310 full-run executions decides and replays cleanly; the exact v3→v4
  guarded comparator passes with 1.07% Z3 drift.

- **2026-07-14 — the Glaurung ordered warm-trace v1 handoff is defined.** The
  contract preserves exact content-addressed query bytes while adding every
  occurrence, process/worker/path order and lineage, push/assert/check/pop
  deltas, unknown/error outcomes, and the model reads that steer exploration.
  Per-process capture plus an atomic validating finalizer avoids the current
  shared-index ambiguity; trace-wide serialization does not claim a false
  cross-process semantic order. The next GQ7 gate is a small Glaurung-produced
  sample whose hashes, sorts, scopes, lineage, and consumed choices all replay.

- **2026-07-14 — ADR-0153 affine `bvadd` constant-chain folding is accepted.**
  Exact scalar/wide modular folding fires 52,858 times on the full tier, 93.9%
  in `slice-partial`. Five full processes improve mean Axeyum total 9.80% to
  14.111 s, ratio 8.37% to 1.852x Z3, AIG requests 12.13%, clauses 17.23%, and
  SAT 17.53%; `slice-partial` improves 24.4% and sheds 35.3% of clauses. Every
  run decides/replays 13,462/13,462 with zero errors or disagreements. A new
  fail-closed comparator verifies that v3 is exactly v2 plus
  `bv.add_constant_chain.v1` before applying the 3%/3%/2% alarms; all pass.

- **2026-07-14 — full family attribution selects proposed ADR-0153.** Canonical
  run 003 shows `slice-partial` is 11.8% of rows but 39.7% of Axeyum time and
  3.82x behind Z3; it creates 16.91M AIG nodes and 22.87M clauses. A source and
  canonicalizer audit localizes the next experiment to mixed `bvadd` chains:
  AC sorting currently preserves every constant leaf. ADR-0153 specifies exact
  modular/wide constant combination, stable rule telemetry, rewrite identity
  v3, semantic gates, and representative/full stop-go gates. Ordered
  worker/path/scope capture remains the separate GQ7 functionality prerequisite.

- **2026-07-14 — GQ10 full-tier variance and guarded comparison land.** Five
  clean canonical processes decide and agree on 13,462/13,462 rows each. Mean
  Axeyum/Z3/ratio are 15.644/7.738 seconds/2.0217x with
  0.514%/0.310%/0.510% CV; every stage is below 1%. A new guarded recipe applies
  provisional same-environment 3% ratio, 3% Axeyum-total, and 2% absolute-Z3-
  drift alarms. The audit also fixes the comparator's accidental
  `preprocess=true` restriction so raw, canonical, and configured artifacts are
  all valid while exact policy identity remains mandatory across commits.

- **2026-07-14 — GQ10 real-lifter semantics enter the regular gate.** `just
  check` now runs raw/current-integration and canonical-candidate policies over
  the pinned or explicitly configured access-controlled representative pack.
  Missing unconfigured data is a visible skip; incomplete explicit data fails.
  Both policies require all 128 decisions, manifest and in-process Z3
  agreement, deterministic resource limits, and zero operational/model-replay
  failures. The first real run passes every gate (raw 1.23x, canonical 1.04x in
  this diagnostic trial); ignored target artifacts preserve stage attribution
  without mislabeling a dirty-worktree regular check as release timing.

- **2026-07-14 — ADR-0152 range-backed term memo is rejected.** The candidate
  removes duplicate ordered memo ownership and passes 21 BV, 10 interpolation,
  and 31 SAT-BV tests. Five representative processes preserve all AIG/CNF and
  replay invariants, but bit blast improves only 0.57% while total p50/mean
  regress 0.02%/0.38%, CNF p50 regresses 0.88%, and variance triples. The exact
  ADR-0151 implementation is restored; no full run is warranted.

- **2026-07-14 — ADR-0151 replaces the per-bit ordered lift index and is
  accepted.** Dense term ranges index the authoritative binding vector while
  preserving public lookup, incremental growth, interpolation, and replay.
  Five representative processes improve total/bit-blast p50 5.59%/15.51%.
  Full total falls 16.540→15.596 s, bit blast 5.884→4.939 s, and ratio
  2.136x→1.992x with identical AIG/CNF structure and all 13,462 decisions/replay
  green.

- **2026-07-14 — ADR-0150 removes common fingerprint-bucket allocations and is
  accepted.** The CNF index now stores the first formula index inline, uses one
  entry probe for a new fingerprint, and allocates a side vector only for a
  genuine collision; exact equality remains mandatory. Five representative
  processes improve total/CNF p50 13.0%/29.0%. The 13,462-query full run
  improves total 18.691→16.540 s, CNF 7.231→5.177 s, gate/root emission
  3.186/1.391→2.400/1.083 s, and ratio 2.399x→2.136x. All runs preserve the
  exact 49,199,541 clauses and every decision/replay gate. Bit blast becomes
  the largest residual stage.

- **2026-07-14 — ADR-0149 formula-header pre-sizing is rejected.** Isolating
  the bounded hint to `Vec<CnfClause>` leaves the exact-dedup table unchanged
  and passes 284 CNF tests, 30 SAT-BV tests, strict Clippy, and every semantic
  gate. Across five clean representative processes it preserves 507,195
  clauses and all decisions/replay, but CNF median/mean regress 0.83%/0.67%.
  Total median improves only 0.16% while mean regresses 0.07% and variance
  rises. Ordinary vector growth is restored, ADR-0149 is deferred without a
  full run, and capacity micro-work yields to shared normalization/ownership
  attribution.

- **2026-07-14 — ADR-0148 bounded CNF container pre-sizing is rejected.** A
  capped no-pass variable/root hint covers every full-tier formula and passes
  284 CNF tests, 30 SAT-BV tests, strict Clippy, and all representative semantic
  gates. Pre-sizing both the formula vector and fingerprint index nevertheless
  regresses median total 2.5%, CNF 10.0%, and gate emission 23.5%; the sparse
  table's lookup cost overwhelms avoided growth. Empty-container growth is
  restored, ADR-0148 is deferred without a full run, and any capacity follow-up
  must isolate the contiguous formula-header vector.

- **2026-07-14 — ADR-0147 planning-copy removal is locally positive but
  globally rejected.** Exposing `Aig::nodes()`' existing double-ended iterator
  contract removes the temporary full-node vector from reverse private-tree
  planning and passes nine AIG tests, 283 CNF tests, and strict Clippy. Five
  clean representative processes improve median planning 2.5%, but regress
  median total 0.5% and median CNF 3.6% with identical formula/verdict/replay
  shape. The code/API is restored, ADR-0147 is deferred without a full run, and
  planning micro-work yields to shared gate/root clause ownership.

- **2026-07-14 — ADR-0146 direct-root scratch is rejected by the client gate.**
  An encoder-local reusable OR-leaf buffer removed unused helper ownership from
  the second negative-direct-root traversal and passed exhaustive two-root
  semantics, all 284 CNF tests, 30 SAT-BV tests, and strict Clippy. Five clean
  representative processes retained identical CNF/verdict/replay shape but
  regressed median total 1.1%, median CNF 4.9%, and the matched root subphase
  2.0%. The implementation is restored, ADR-0146 is deferred, and no full-tier
  run is spent on it. Planning attribution is next.

- **2026-07-14 — ADR-0145 removes not-AND clause temporaries.** The sparse
  encoder now emits the bounded two-factor not-AND forward/reverse clauses from
  fixed stack arrays and four exact shape matches instead of per-factor vectors
  and a cloned Cartesian expansion. An exhaustive 32-row internal-gate truth
  table, all 283 CNF tests, 30 SAT-BV integration tests, and strict Clippy pass
  under 4 GiB. Five clean representative processes improve median CNF/total
  6.6%/2.0%. The full 13,462-query confirmation improves CNF 7.66→7.23 s,
  gate emission 3.56→3.19 s, total 19.22→18.69 s, and ratio 2.47x→2.40x
  with 100% decided, zero errors/disagreements/replay failures, and the same
  49,199,541 clauses. ADR-0145 is accepted; residual root emission and planning
  are the next measured GQ5 investigation.

- **2026-07-14 — real Glaurung capture, artifact v26, and corrected roadmap.**
  Regenerated the three-driver Z3 capture sequentially, reconciled 15,710 rows
  to 15,687 unique hashes plus 23 non-conflicting duplicates, isolated 2,225
  then-ill-sorted producer dumps, and generated strict byte-complete representative
  and 13,462-query well-typed full manifests. Five-process representative raw/
  canonical/configured runs and raw/canonical proof companions pass every
  validity gate; same-revision full raw/canonical runs decide 13,462/13,462.
  Artifact v26 now charges canonical rewrite elapsed, repetition tooling accepts
  v26, and canonical v2 is a measured 48.5%/57.1% representative/full Axeyum
  time win. The full attribution finds the always-on observational demand pass
  consuming 29.57/50.75 s. ADR-0184 later invalidates this capture's byte
  identity by fixing the producer renderer; the historical performance result
  remains documented, but the corpus must be regenerated. The next task at the
  time was to make it opt-in, rerun production
  timing, and only then choose affine word or CNF work. Evidence and digests are
  committed in `bench-results/glaurung-qfbv-2026-07-14.md`.

- **2026-07-14 — ADR-0142 completes the exact GQ3 rewrite implementation.**
  The default manifest now composes nested extracts, splits straddling concat
  slices, returns exact whole concat operands, and reduces low/high/straddling
  regions of zero and sign extension. Replacement roots receive a bounded
  eight-application exact reprocessing loop; `RewriteReport` exposes actual
  local fuel exhaustion and returns a safe partial result. New stable rule IDs
  retain per-class attribution, fixed local fresh-node tests bound growth, and
  the benchmark rule-set identity advances to `axeyum-rewrite-default-v2`.
  Exhaustive small-width cases, 96 seeded wider cases, manifest fixtures, a
  forced one-step fuel test, and lifter-shaped Z3 SAT/UNSAT original/rewritten
  model replay pass under the 4 GiB cap. GQ3 remains WIP only at its real-corpus
  performance exit: no AIG/CNF or cold-time win is claimed without the missing
  Glaurung payload.

- **2026-07-14 — artifact v25 measures the GQ4 relevant-bit opportunity.** A
  public `BitDemandStats` profile now propagates conservative structural demand
  from roots, exactly through extract, concat, zero/sign extension, pointwise
  BV operations, `ite`, rotations, and FP bit reinterpretation, with a
  full-operand fallback elsewhere. It records request, unique-demanded,
  available, and actually lowered term/symbol bits plus nested analysis time.
  Typed solver stats and per-instance/corpus artifacts expose the counts,
  demanded/available and lowered/demanded ratios, and coverage invariants. The
  focused `extract(7,0,x64) == c8` regression measures 25/81 demanded term bits
  and 8/64 demanded symbol bits while current lowering materializes 81/81 and
  64/64, turning GQ4's hypothesis into a falsifiable baseline without changing
  lowering or model semantics. Repetition/comparison tooling is version-locked
  to v25. Focused BV/solver/benchmark tests and strict Clippy pass under the
  4 GiB cap. From clean commit `b69b9480`, raw/canonical/configured recipes each
  emitted v25 and passed 2/2 decisions, manifest/Z3 agreement, zero errors/
  disagreements/replay failures, and every AIG/CNF/bit-demand invariant. The
  generic micro tier demanded all of its bits, as expected; it validates schema
  plumbing and makes no relevant-bit or client-performance claim. The real
  payload remains the optimization admission gate.

- **2026-07-14 — artifact v24 attributes AIG and CNF construction.** The AIG
  now counts primitive AND requests and classifies each as a trivial identity/
  complement simplification, absorption/consensus simplification, structural-
  hash hit, or new node. The sparse CNF encoder now records planning,
  retained-variable allocation, gate encoding, and root encoding time;
  reachable/skipped-helper/direct-root nodes; recognized XOR/not-ITE/not-AND/
  private-tree/binary-AND gates; and attempted, tautological, duplicate, and
  emitted clauses. Typed `BvLayerStats`, raw backend telemetry, per-instance
  records, and corpus summaries carry the evidence. Explicit outcome-partition
  invariants guard counter completeness, and the artifact marks CNF subphases
  as nested inside total encode time. Repetition/comparison tools are
  version-locked to v24. AIG/CNF/solver/benchmark tests and strict Clippy pass
  under the 4 GiB cap; the real Glaurung payload remains required before these
  counters can authorize a GQ5 optimization. From clean commit `e17069f2`, the
  raw/canonical/configured client recipes each emitted v24 and passed 2/2
  decided, manifest/Z3 agreement, zero-error/disagreement/replay gates, and
  both construction partitions on the committed micro tier. Raw reported 53
  primitive AIG requests (18 trivial, 35 new nodes) and 37 emitted CNF clauses;
  these tiny values validate schema/recipe plumbing only, not client timing.

- **2026-07-14 — artifact v23 measures the residual GQ3 opportunity set.** The
  benchmark now profiles both the untouched query and the exact assertion DAG
  remaining after the selected raw/canonical/configured word policy. Instance
  and corpus artifacts report before/after/removed/added counts for broad
  extract-over-concat/nested-extract/zero-extension/sign-extension classes;
  concat low/high/straddling and whole-operand regions; extension low/high/
  straddling regions; exact low zero/sign cancellations; and maximum nested
  extract depth. Raw can now prove it changed nothing, while canonical and
  configured modes expose the residual terms that actually reach bit lowering.
  Repetition tooling is version-locked to v23. Three focused classification and
  transition tests plus all 27 benchmark tests, the 15 script tests, formatting,
  and links pass under the 4 GiB cap. This is behavior-preserving diagnostic
  evidence, not a Glaurung speed result; the real payload remains required.

- **2026-07-14 — Glaurung cold policy matrix is executable.** Replaced the
  ambiguous full-preprocessing client recipe with explicit raw, canonical-only,
  and configured single-run, repeated-run, and proof-companion recipes. The
  unsuffixed compatibility entries now select raw, matching both Glaurung's
  current one-shot backend and the producer's artifact-v17 command; each policy
  has a separate default artifact path. The embedding and benchmark guides now
  warn that configured preprocessing measured about 1.3--2x slower on the cold
  Glaurung path and must be measured rather than assumed. Four direct `just
  --dry-run` regression tests pin all policy flags, proof pairing, repeated
  series, and raw aliases; the complete 15-test benchmark-script suite and link
  gate pass. No client timing claim is made without the missing query bytes.

- **2026-07-14 — Glaurung capture and execution-plan audit.** Inspected the
  committed producer capture, current one-shot backend, Axeyum rewrite/lowering/
  AIG/CNF implementations, and the official Z3/Bitwuzla counterparts. Recorded
  the dependency-ordered
  [Glaurung QF_BV execution plan](docs/research/08-planning/glaurung-qfbv-execution-plan.md).
  The audit localizes a likely cross-process duplicate explanation for the
  producer's 23-row count discrepancy, requires conflict-checking and a strict
  hash-free capture index, and identifies a benchmark-mode mismatch: the
  producer/current Glaurung path is raw while Axeyum's recipe forces full
  preprocessing. The baseline is now explicitly raw vs canonical-only vs
  configured. GQ3 is reclassified as a partial foundation, GQ4 as a true
  demand-lowering contract because raw extracts lower full children, and GQ5 as
  profile-first work over an already sophisticated AIG/CNF stack. The warm lane
  now requires an ordered trace and controlled model-based concretization before
  caching or performance claims.

- **2026-07-14 — close ADR-0129 Lean reconstruction under 4 GiB.** Open AIG
  gate propositions are now explicit witness-scoped lets consumed directly by
  compact CPS clause types. The trusted kernel retains let-local values for
  context-aware zeta equality without substituting them across the proof DAG;
  positive/negative application-boundary regressions and all 174 kernel tests plus the
  doctest pass. The 64/256 export cap is removed. The public paired row emits a
  106,809,049-byte module and passes in 19.69 s at 2,078,224 KiB peak with
  genuine `Exists.rec`/`Exists.intro` and no `sorryAx`; all 10 paired tests pass.
  Quantified-BV Lean UNSAT coverage rises 16→17/18. ADR-0127 is next.

- **2026-07-14 — repair ADR-0129 paired-body scoping; localize the remaining
  export blow-up.** A public-shaped 4-bit regression proved that whole-body AIG
  lowering was not definitionally identical to independently lowered
  conjunction leaves. The paired source, elimination, projection, rebuilding,
  and introduction path now shares one structural conjunction encoding; small
  identity, generic, signed, and multiplication cases kernel-check. Removing the
  64/256 cap lets the real public proof pass scoped closure and reach export in
  211.18 s at 2,062,692 KiB peak, where its expanded open gate propositions
  exceed 14 GiB of temporary storage. The cap returns as a fail-closed export
  gate pending scoped gate-proposition sharing; coverage stays 16/18.

- **2026-07-14 — compact RUP construction lands behind the ADR-0129 public
  scoping gate.** CPS clauses and direct unit-propagation continuations replace
  growing binary resolvents; normalized forms are cached once; wide/deferred
  positive and corrupted-conflict mutation gates kernel-check. The public row's
  open proof now builds in about 30 seconds under 4 GiB, exposing a fail-closed
  nested predicate/body `TypeMismatch` at scoped closure. The 64/256 cap remains
  until that source-binder mismatch is repaired; coverage stays 16/18.

- **2026-07-14 — ADR-0129 bounded source reconstruction checkpoint.** Exact
  paired existential elimination/transfer/introduction kernel-checks for the
  identity and generic QF-proof cases, with direct/router equality and no
  `sorryAx`. The public signed row is measured at 2,430 commands with one
  86-literal/411-premise RUP step; a fail-closed 64/256 cap replaces the prior
  guarded 2.18 GiB allocation failure. DAG-aware conjunction leaves,
  empty-clause backward slicing, and cached clause suffixes land as bounded
  foundations. Coverage stays 16/18 pending compact reflected RUP.

- **2026-07-14 — ADR-0124/0125 Lean alternation reconstruction closes.** The
  kernel now type-checks marked open lambda skeletons with exact lexical scope
  and returns their single-pass closed term; application-spine and expected-type
  checking avoid quadratic dependent-type copies. Streaming exact module
  comparison restores the direct/router equality gates without retaining two
  outputs. `small-pipeline-fixpoint-3` passes in 81.57 s at 3,756,104 KiB and
  530-binder `bug802` in 45.28 s at 2,186,192 KiB under 4 GiB. Quantified-BV
  Lean UNSAT rises 14→16/18; the remaining families are ADR-0127 and ADR-0129.

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
  reproducible Glaurung recipe requires the external query payload; the visible
  producer-side artifact-v17 result does not replace an artifact-v25 rerun and
  therefore carries no current parity claim.
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
