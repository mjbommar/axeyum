# Roadmap

Status: **foundation phases (0–7) landed**; active execution has moved to the
multi-track Z3 + Lean parity plan.
Last updated: 2026-06-22

> **Where the live plan is now.** This file is the *research/foundation* roadmap
> (Phases 0–7 — the decidable finite-domain + arithmetic foundation, now built).
> The end-to-end push to **Z3 + Lean parity** is decomposed into tracks → phases →
> tasks in **[PLAN.md](../../../PLAN.md)** and [`docs/plan/`](../../../docs/plan/README.md)
> (Track 1 engine/perf · Track 2 theories · Track 3 proofs/Lean · Track 4
> use-cases · Track 5 verified systems / IR reflection —
> [ADR-0056](../09-decisions/adr-0056-verified-systems-track.md)), with the
> current honest gap analysis in PLAN.md's
> "the gap to Z3/cvc5, itemized" section. Live per-session state is in
> **[STATUS.md](../../../STATUS.md)**. Read those for "what's next"; read this for
> "how the foundation was sequenced."

## Purpose

Turn the research notes into an implementation sequence with explicit exit
criteria and decision gates, so "done" and "justified" are checkable rather
than felt.

## Scope

In scope:

- Phased plan from empty repo to useful reasoning stack.
- Exit criteria per phase and gates for expensive bets.
- Foundational dependencies from semantics to evidence, as routed through the
  [foundational DAG](foundational-dag.md).

Out of scope:

- Time estimates and release commitments.

## Core Claims

- A thin end-to-end vertical slice comes before broadening any layer
  (see [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)).
- Checkability and differential testing are continuous workstreams present in
  every phase, not phases themselves.
- Every phase exit must prove the relevant arrows in the
  [foundational DAG](foundational-dag.md), not just deliver code.
- Expensive bets (custom CDCL, lazy techniques) are gated on the benchmarking
  methodology note, not on enthusiasm.

## Continuous Workstreams

These run through every phase below:

- Evidence: every new layer ships with its check (evaluator, CNF evaluator,
  round trips, lift-map validation).
- Differential testing: every transformation gains an oracle comparison when
  an oracle exists.
- Benchmarks: the harness and corpora grow with each layer
  (see [benchmarking methodology](benchmarking-and-performance-methodology.md)),
  including the self-checking, oracle-free scenario tier (`axeyum-scenarios`,
  ADR-0008) that measures optimizations on realistic, scalable workloads.
- Decisions: questions close as ADRs in `09-decisions/` as phases force them.
- DAG audit: before a phase is marked done, check that each new term,
  transformation, encoding, backend result, and artifact has a semantics
  source, model/proof-lift story, and replay or checker route.

## Foundational Gate

The phase list below is subordinate to the
[foundational logic and math DAG](foundational-dag.md). A phase is not complete
when its crate compiles; it is complete when the layer contract is checkable:

```text
semantics -> typed IR -> evaluator -> import/export -> oracle baseline
  -> rewrites/query planning -> bit lowering -> circuit -> CNF -> SAT
  -> pure Rust BV backend -> evidence -> later theories
```

When these conflict, preserve the DAG. For example, do not add an
equisatisfiability-only rewrite before model projection exists, do not let an
unsupported feature fall through to Z3 silently, and do not expose a new logic
fragment without an evidence story.

## Phase 0: Repository Foundation

- Workspace skeleton, license, README, contribution conventions.
- CI for formatting, linting, tests.
- Decision: start with two crates (`axeyum-ir`, `axeyum-solver`); split later.

Exit criteria: CI green on an empty workspace; ADR process in place.

## Milestone M0: Vertical Slice

- IR subset (Bool, BV constants/symbols, core ops), arena, sort checking.
- Ground evaluator.
- Solver trait plus Z3 feature backend with model lifting to Axeyum symbols.
- Model check-by-evaluation on every `sat`.

Exit criteria: doctest asserts `x + 1 == 5` over `BV(8)`, solves via Z3,
lifts the model, and the evaluator confirms it. Cancellation/timeout plumbing
exists in the trait.

## Phase 1: Typed Term Core (Broaden)

- Full scalar QF_BV operator set with SMT-LIB edge-case semantics
  (see [BV semantics note](../01-foundations/bv-semantics-and-partial-operations.md)).
- Pretty printer and stable debug format.
- Exhaustive small-width evaluator tests for div/rem/shift/rotate.

Exit criteria: every operator has evaluator tests; exhaustive width <= 8
coverage for edge-case operators runs in CI.

## Phase 2: Native Solver Oracle (Harden)

- Backend conformance suite (results, models, state retention, cancellation).
- SMT-LIB export for debugging; SMT-LIB benchmark import for the QF_BV slice
  (see [formats note](../02-ecosystems/formats-and-interchange.md)).
- Optional second backend (Bitwuzla) to validate the trait is not Z3-shaped.

Exit criteria: conformance suite passes on Z3; SMT-LIB QF_BV benchmarks
ingest and solve through the trait; benchmark harness records baseline runs
with source hashes, backend version, shape metrics, agreement counts,
unsupported/error triage, and model replay for every `sat`.

## Phase 3: Rewriting And Query Planning

- `axeyum-rewrite` cheap canonicalizer with rule IDs and per-rule tests.
- Query object with assertions, assumptions, scopes
  (assumptions-first; see [incrementality note](../03-architecture/incrementality-and-solver-lifecycle.md)).
- Constraint slicing and structural cache keys.
- Differential rewrite tests against the oracle on ingested corpora.
- Stable rewrite manifest: rule ID, precondition, exact-denotation vs
  equisatisfiability classification, and model-projection requirements.
- Query projection tests proving sliced/planned models still satisfy the
  original query contract.

Entry contract: accepted in
[ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
`axeyum-query` and `axeyum-rewrite` now provide the query and manifest
boundaries; default Phase 3 rules must stay denotation-preserving until model
projection is implemented and tested.

Implementation note: the first default canonicalizer is implemented as an
exact-denotation rule set with stable rule IDs, focused and deterministic
generated evaluator-equivalence tests, Z3 differential checks on handcrafted
and micro-corpus queries, and a public QF_BV rewrite-measurement artifact with
original-vs-rewritten oracle comparison and model replay against original
assertions. Query planning now has structural cache keys and target-support
slicing; sliced `sat` models must pass identity-projection replay against the
original query before acceptance. The
[Phase 3 exit audit](phase3-exit-audit.md) records the hardening evidence and
the Phase 4 handoff obligations.

Exit criteria: rewriter is evaluator-equivalent on random inputs and
oracle-equisatisfiable on the public corpus; measured rewrite win (size or
solve time) is recorded, not assumed; every non-denotational rewrite has a
model-projection test or remains disabled by default. The current audit records
these criteria as satisfied for the default exact-denotation Phase 3 surface;
Phase 4 must still record the bit-order convention before lowering starts.

## Phase 4: Circuit And CNF Layers

- AIG layer with structural hashing; AIGER export for debugging.
- `axeyum-cnf` with Tseitin encoding and DIMACS I/O.
- Model lifting from SAT vars to wires to terms; CNF evaluator.
- Recorded bit-order convention and shared value-to-wires conversion routines.
- Per-operator bit-lowering tests against the ground evaluator.

Entry contract: accepted in
[ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
Phase 4 uses LSB-first BV wire vectors, shared value/model conversion helpers,
an AIG layer before simple Tseitin CNF, and explicit lift maps from original
terms through AIG literals and CNF variables back to model replay.

Implementation note: the first Phase 4 slice adds shared LSB-first
value-to-bits and bits-to-value helpers in `axeyum-ir`, plus `axeyum-aig` for
constant/input/AND literals, deterministic structural hashing, derived OR/XOR
and mux construction, circuit evaluation tests, and deterministic ASCII AIGER
debug export. `axeyum-bv` now lowers Bool/BV
constants, symbols, Boolean connectives, BV bitwise operators, equality, `ite`,
`bvcomp`, concat/extract, zero/sign extension, `bvneg`, `bvadd`, `bvsub`, and
unsigned/signed comparisons, `bvshl`, `bvlshr`, `bvashr`, and constant rotates
to AIG with explicit term-bit and symbol-input maps, then checks AIG replay
against the ground evaluator. `axeyum-cnf` now adds simple Tseitin encoding
from AIG, DIMACS parse/write, CNF evaluation, and CNF-variable-to-AIG lift
maps. The SAT adapter slice chooses `rustsat-batsat` through RustSAT
([ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md)), exposes
an Axeyum CNF SAT trait/result/assignment surface, solves raw CNF through the
adapter, and replay-checks satisfying assignments through CNF variables, AIG
node values, reconstructed symbol models, and original-term evaluator replay.
UNSAT through this adapter is capability-marked lower assurance until proof
logging and proof checking are added.

Exit audit: [Phase 4 exit audit](phase4-exit-audit.md) records the completed
gates, the committed DIMACS micro corpus, the default-dependency evidence, and
the explicit deferral of pure-Rust benchmark artifact telemetry to Phase 5.

Exit criteria: round-trip and lift-map tests pass; DIMACS corpus solves via
an adapted Rust SAT solver behind the SAT trait; CNF assignments lift through
wires to original terms and replay against the original formula.

## Phase 5: Pure Rust BV Backend

- Bit-blasting for the scalar subset; per-operator lowering pluggable.
- Existing Rust SAT adapter (evaluate batsat/splr/varisat against the
  methodology note's criteria; varisat's proof output weighs in its favor).
- Differential tests against the native backend on all corpora.
- Structured unsupported results for operators/logics outside the pure Rust
  subset; no silent oracle fallback in the default backend.
- Layer-attributed artifact fields for parse, rewrite, bit-blast, CNF, SAT,
  and model lifting.

Implementation note: the first Phase 5 slice adds `SatBvBackend` in
`axeyum-solver`, available in the default native-free build. It composes the
existing query terms, `axeyum-bv` lowering, `axeyum-cnf` Tseitin encoding, the
`rustsat-batsat` adapter, model reconstruction, model completion for
unconstrained symbols, and evaluator replay before returning `sat`.
The full scalar QF_BV operator set now lowers (2026-06-13): multiplication
(`bvmul`, truncated shift-and-add), unsigned division/remainder
(`bvudiv`/`bvurem`, a combinational restoring divider with SMT-LIB
divide-by-zero totality), and signed division/remainder/modulo
(`bvsdiv`/`bvsrem`/`bvsmod`, sign-handling wrappers over the unsigned divider),
each verified exhaustively against the evaluator. No scalar operator returns
`SolverError::Unsupported`; that path is reserved for future non-scalar
constructs (arrays, UF) with no oracle fallback. The benchmark harness now
selects `--backend sat-bv|z3`; artifact version 4 introduced backend kind and
per-instance backend stats, artifact version 5 adds node-budget provenance plus
optional Z3 oracle comparison for pure-Rust runs, artifact version 6 adds CNF
variable/clause admission budgets plus submitted query-plan mode and replay
policy, artifact version 7 adds replay-refinement configuration and
per-instance refinement telemetry, and artifact version 8 records the harness
`jobs` setting for deterministic corpus-level parallel runs. Artifact version
9 records replay-refinement batch size for exact-target refinement runs, and
artifact version 10 records adaptive-batch policy plus backoff counts.
Artifact version 11 records replay-refinement selection policy. The
artifact version 12 line records the bounded plan-aware selection option and
the current root-direct assertion CNF encoder behavior. The
committed micro corpus agrees with expected statuses through both the pure Rust
backend and the Z3 oracle. The
first public-slice
pure-Rust-vs-Z3 measurement is recorded in
`bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json`:
113 files, 1 public `sat` decided by `sat-bv`, 112 node-budget `unknown`s,
0 unsupported, 0 errors, 0 model replay failures, 1 Z3 decision agreement, and
0 oracle disagreements. A guarded admission run is recorded in
`bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json`:
node budget 5000, CNF variable budget 7000, CNF clause budget 20000, 113 files,
the same 1 public `sat`, 111 node-budget `unknown`s, 1 encoding-budget
`unknown`, 0 unsupported/errors/model replay failures/oracle disagreements.
That run proves the wider gate is bounded and diagnostic; it does not yet
expand public decisions. A replay-refinement diagnostic run is recorded in
`bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json`:
16 replay-refinement rounds, the same 1 public `sat`, 95 encoding-budget
`unknown`s, 17 node-budget `unknown`s, 0 unsupported/errors/model replay
failures/oracle disagreements. Replay refinement soundly recovers the known
decision after full replay, but it does not expand the public decisions under
the current CNF caps and BatSat timeout. Legacy-guided sparse-CNF passes now
add directional signed-comparison lowering plus sparse CNF variables/clauses
for private XOR, mux, private AND-tree, OR-of-private-AND, and positive
root-only parity/equality helper shapes, informed by cvc5's ITE
simplification/removal stage and Bitwuzla's AIG-to-CNF ITE recognition. The
guarded and replay-refine artifacts were regenerated with the same public
decision count and zero soundness alarms; the immediate MobileDevice
replay-refine target now reaches the seventh support set before stopping at
5,353 CNF variables and 20,784 clauses, still above the committed
7000/20000 caps. A relaxed-admission artifact is recorded in
`bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json`:
10s timeout, node budget 5000, CNF variable budget 7000, CNF clause budget
30000, 8 corpus workers, 2 public `sat` decisions, 94 encoding-budget
`unknown`s, 17 node-budget `unknown`s, 0 unsupported/errors/model replay
failures/oracle disagreements, and 2 Z3 oracle agreements. This proves the
MobileDevice target is replay-checkable under a modest clause-cap and timeout
increase, but its 6.4s BatSat solve time under the 8-worker public run versus
0.9s Z3 time keeps CNF/SAT cost as the next optimization target. A follow-up
exact-target relaxed diagnostic is recorded in
`bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json`:
artifact version 9, exact-target replay refinement, 64 rounds, batch size 64,
10s timeout, node budget 5000, CNF variable budget 8000, CNF clause budget
30000, and 8 corpus workers. It records the same 2 public `sat` decisions with
Z3 agreement and no soundness alarms, reduces submitted public DAG shape to
237,924 nodes, and leaves all 111 remaining unknowns as `EncodingBudget`
rather than `NodeBudget`. This improves the diagnostic surface but does not
expand the supported slice beyond the relaxed support-slice run. A version 10
adaptive-batch exact-target diagnostic keeps the same two public decisions but
turns the remaining `EncodingBudget` cases into precise near-cap frontiers; an
8,500-variable sweep still leaves 111 `EncodingBudget` unknowns. A
smallest-DAG failed-assertion selector lowers several near-cap frontiers but
still leaves the public slice at two decisions, with 111 `EncodingBudget`
unknowns at both 8,000 and 8,500 variable caps. The v12 root-direct assertion
CNF pass removes assertion-only root variables and adds a bounded
plan-aware selector diagnostic, but the current public sweeps still remain at
two decisions and 111 `EncodingBudget` unknowns under both caps. The remaining
Phase 5 work is to reduce the exposed CNF/SAT cost or improve the bit-vector
encodings so the supported public slice grows without only buying decisions
with timeout and admission increases.

Exit criteria: pure Rust path agrees with the oracle on the public QF_BV
slice it supports; layer-attributed timing identifies the dominant cost; Z3 is
demoted to differential-oracle/CI-cross-check role for that supported slice.
The first criterion is satisfied for the currently admitted public slice; the
second and third remain open because guarded admission and replay refinement
now decide two public instances only under relaxed admission, while the next
admitted candidates are still stopped by CNF size and the MobileDevice decision
remains materially slower than Z3.

## Phase 6: SAT Core (Identity; Priority Gated)

The custom CDCL core is part of the project identity
([ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md)):
it will be built. The methodology note's gate decides *when* — it takes
priority over encoding work only once SAT time dominates end-to-end time on
the corpus tiers.

- SAT trait stabilization with proof-logging hook (IPASIR-superset shape). A
  warm incremental SAT layer (`IncrementalSat`: monotone clauses + native
  assumptions) already exists per
  [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md) stage 1;
  Phase 6 stabilizes the trait shape across adapter and custom core and adds
  proof logging.
- Clause arena, propagation, CDCL prototype with DRAT output.
- Profiling against the adapters that justified the work.
- ADR for proof logging target, checker route, deterministic clause database
  behavior, and adapter baseline.

Exit criteria: prototype beats the best adapter on the client tier or the
attempt is written up as an ADR documenting why not.

## Phase 7: Arrays, EUF, And Client Libraries

- Array and UF terms in IR; native backend support for QF_ABV/QF_AUFBV.
- Bounded/lazy memory encodings; lemmas-on-demand research per the
  [beyond-bit-blasting note](../05-algorithms/beyond-bit-blasting.md).
- Client examples for math, verification, and infosec workflows.
- ADR for select/store, extensionality, congruence closure, model replay, and
  proof/evidence commitments before public arrays/EUF surface expands.

Progress update (2026-07-09): ADR-0071 adds a true abstraction-only array
boundary and replay-guided base-select congruence on canonical `CdclT`, composed
with dynamic UFBV interfaces and function-then-array model projection. Public
QF_ABV/QF_AUFBV runs remain DISAGREE=0 with zero replay failures. This is the
first live-bus slice, not phase exit: lazy store axioms, diff-skolem
extensionality, scalable array defaults, and the warm memory path remain.

Implementation note: a first infosec-workflow client example landed early
(2026-06-13), ahead of arrays — a register-VM symbolic executor over
`IncrementalBvSolver` that forks at branches, prunes infeasible paths, and
cross-checks every found input by concrete re-execution
(`axeyum-solver/tests/symbolic_execution.rs`). It is memory-free; memory-using
programs are the motivation for the array work above.

Exit criteria: one real client example per audience runs end to end with
checked evidence. The infosec example exists for the memory-free fragment;
math/verification examples and a memory-using infosec example remain.

## Beyond Phase 7: The Proving Horizon

The phases above build the decidable finite-domain foundation. The north
star ([north-star note](../00-orientation/north-star.md)) continues past it.
**Most of these markers are now landed or in active flight** (2026-06-22) — they
are tracked concretely in the [parity plan](../../../PLAN.md) (tracks/phases) and
[STATUS.md](../../../STATUS.md), not loosely here:

- Arithmetic theories (QF_LIA/QF_LRA): **landed** — exact-rational simplex +
  Farkas (QF_LRA), bit-blast + branch-and-bound + Gomory cuts (QF_LIA). Next:
  native LIA cut portfolio + an unbounded-completeness backstop
  ([P2.4](../../../docs/plan/track-2-theories/P2.4-lia-cuts.md)).
- Nonlinear arithmetic (QF_NRA/NIA): **CAD decision side complete** (single-var
  real-algebraic + coupled grid + strict/non-strict CAD, rational *or* algebraic
  coordinates); sound-incomplete tail tracked at
  [P2.5](../../../docs/plan/track-2-theories/P2.5-nra-cad.md).
- Theory combination (Nelson-Oppen): conjunctive EUF+LIA/LRA **landed**; the
  online e-graph + CDCL(T) keystone is [P1.4/P1.5](../../../docs/plan/track-1-engine/README.md).
- Quantified fragments: finite expansion + e-matching + MBQI **landed**;
  maturity at [P2.6](../../../docs/plan/track-2-theories/P2.6-quantifiers.md).
- Proof production: DRAT (clausal) + Alethe + an in-tree **Lean-grade kernel**
  with reconstruction **landed**; the trust ledger drives "modulo trusted
  reduction" toward zero ([Track 3](../../../docs/plan/track-3-proof-lean/README.md)).
- Proof-assistant interop: Alethe→Lean reconstruction is the
  [Track 3 capstone](../../../docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md).
- **Newly scoped categorical engines** (the honest remaining gap vs Z3): CHC/Horn
  PDR ([P4.6](../../../docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md)),
  Craig interpolation ([P3.8](../../../docs/plan/track-3-proof-lean/P3.8-interpolation.md)),
  synthesis/abduction ([P4.7](../../../docs/plan/track-4-usecases-frontend/P4.7-synthesis.md)).

Entering any horizon item gets its own ADR with prerequisites and exit
criteria; none may begin while it would starve a foundation phase.

## Open Questions

- [x] Should Phase 2 include the second backend or defer it to Phase 5's
      differential needs?
  - Answer: defer it until there is a concrete differential-testing or
    trait-design need; see
    [ADR-0004](../09-decisions/adr-0004-defer-second-native-backend.md).
- [x] Where does the SMT-LIB parser crate boundary land (`axeyum-smtlib` vs
      CLI module)?
      Answer: `axeyum-smtlib`, now exercised by solver tests and
      `axeyum-bench`.
- [ ] Should proof logging (DRAT from adapters that support it) be surfaced
      before Phase 6?

## Source Pointers

- Cargo workspaces: https://doc.rust-lang.org/cargo/reference/workspaces.html
- SMT-LIB FixedSizeBitVectors: https://smt-lib.org/theories-FixedSizeBitVectors.shtml
- z3.rs: https://github.com/prove-rs/z3.rs
- RustSAT: https://github.com/chrjabs/rustsat
- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
- cvc5 proof production: https://cvc5.github.io/docs/latest/proofs/proofs.html
