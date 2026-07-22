# Roadmap

Status: **foundation phases (0–7) landed**; active execution has moved to the
multi-track Z3 + Lean parity plan.
Last updated: 2026-07-21

> **Where the live plan is now.** This file is the *research/foundation* roadmap
> (Phases 0–7 — the decidable finite-domain + arithmetic foundation, now built).
> The end-to-end push to **Z3 + Lean parity** is decomposed into tracks → phases →
> tasks in **[PLAN.md](../../../PLAN.md)** and [`docs/plan/`](../../../docs/plan/README.md)
> (Track 1 engine/perf · Track 2 theories · Track 3 proofs/Lean · Track 4
> use-cases · Track 5 verified systems / IR reflection —
> [ADR-0056](../09-decisions/adr-0056-verified-systems-track.md)), with the
> current scoped gap analysis in
> [`docs/plan/gap-analysis-z3-lean-2026-07-21.md`](../../../docs/plan/gap-analysis-z3-lean-2026-07-21.md).
> Its [target evidence audit](../../../docs/plan/parity-target-evidence-audit-2026-07-21.md)
> prevents one “distance” label from crossing targets: selected fragment cells
> can be competitive; general Z3 solving-power distance is unmeasured;
> production Z3 compatibility is demonstrably far; solver-proof export to Lean
> now has a bounded local 71/71 official-Lean acceptance result after four
> hidden export failures were exposed and fixed, while remote CI and exhaustive
> acceptance remain open. Full Lean language/toolchain compatibility is a
> separate long-horizon implementation program, while selected declaration
> import, certificate tactics, and optional workflow adapters remain the first
> value-bearing stages in the
> [Lean-system compatibility roadmap](../../../docs/plan/lean-system-compatibility-roadmap-2026-07-21.md)
> under accepted ADR-0345. The complete native work breakdown is the
> [Lean-system implementation plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md).
> Its
> [completion audit](../../../docs/plan/lean-system-roadmap-completion-audit-2026-07-21.md)
> verifies every named environment gap and the current Axeyum/Lean/mathlib
> inventories while keeping the L0-L10 implementation program explicitly open.
> TL0.4 now freezes the actual reconstruction-prelude trust boundary in a
> [runtime-derived 65-row ledger](../../../docs/plan/generated/lean-axiom-ledger.md):
> real 30, integer 34, string 1, with canonical type digests and mutation-tested
> population drift checks. The former 64-row helper-call census omitted the
> directly inserted string `append` axiom. Classification and discharge remain
> open under TL3.2; inventory is not truth.
> Live per-session state is in
> **[STATUS.md](../../../STATUS.md)**. Read those for "what's next"; read this for
> "how the foundation was sequenced."

> **Current downstream checkpoint.** Track 5's T5.4.3 implementation is pushed
> at `3d75d407` under proposed ADR-0340: proof, replayed refutation, and sampled
> `Unknown` follow-up are distinct public outcomes. Acceptance remains gated on
> exact fixtures, the full fail-closed rejection/mutation matrix, and the capped
> package/documentation/profile/resource checks recorded in PLAN/STATUS. This
> does not reopen concretization or symbolic memory, and it does not replace the
> separate multi-oracle publication campaign.

> **Current compatibility checkpoint.** P4.4 now has a machine-readable,
> source/test-checked 30-row
> [SMT-LIB/API conformance matrix](../../../docs/plan/generated/smtlib-api-conformance.md).
> It records six absent command families, seven accepted parser no-ops, and
> zero ordered interactive-text outputs alongside the bounded Rust helpers that
> already exist. The follow-up
> [session contract](../../../docs/plan/generated/smtlib-session-contract.md)
> freezes 14 invariants and 20 abstract fixtures / 107 commands under proposed
> ADR-0342. It also finds a deeper signature gap: declarations/definitions must
> be scoped by default, `reset-assertions` is conditional on
> `:global-declarations`, full reset needs a fresh arena epoch, and continued
> errors must be atomic. The next frontend increment is capture-only complete
> command/event IR (S1), not a renderer. Do not add another isolated output
> helper or report a direct interpolation/Horn/abduction API as textual
> conformance.

> **Current measurement-durability checkpoint.** G1's failed 52-shard
> candidate run receives zero result credit, and proposed ADR-0344 now freezes
> the prerequisite resume protocol. The generated v2 contract checks 18
> invariants across 28 scenarios and proves deterministic interrupted/resumed
> scoring-projection equivalence. V2 supersedes the thin v1 process schema
> before integration. E1a subsequently passes 8/8 real `SIGKILL` record-recovery
> cells on local tmpfs and ext-family storage, but the active runner, solver,
> leases, shared storage, and resources are untouched. Production stages E1b-E3
> must integrate completion-last output, strict duplicate rejection,
> typed termination, observed/admitted verdict preservation, output-sidecar
> validation, single-owner recovery, aggregate resource enforcement, and multi-host
> loss/retry on a tiny corpus before the 64,345-file candidate may be rerun. This is measurement
> infrastructure under G1, not a new solver or foundation phase.

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

Progress update (2026-07-10): ADR-0071 adds replay-guided base-select congruence
on canonical `CdclT`; ADR-0072 reuses the shared ROW abstraction and materializes
only candidate-violated store hit/miss axioms. Both compose with dynamic UFBV
interfaces and replay-gated projection. Public QF_ABV/QF_AUFBV runs
remain DISAGREE=0 with zero replay failures. This is not phase exit: structural
parent/ROW/default scheduling on class merges, non-symbol class models, dynamic
in-search insertion, and the warm memory path remain.

ADR-0073 adds candidate-guided array equality: one bounded diff witness per
equality flag plus observed query/store indices, with only violated congruence or
witness instances materialized. ADR-0076 expands the 768-comparison matrix to
456 equality-bearing cases and it remains clean. ADR-0077 subsequently makes
ordinary equality live on `EufTheory`. Full phase exit still requires parent-
select scheduling beyond direct base symbols, scalable non-symbol class models,
warm reuse, and proof integration.

ADR-0074 adds deterministic majority-default array projection shared by the
canonical and fallback routes. Votes count distinct observed indices; stable
ties and normalized overrides preserve deterministic output. A 16-read model
compresses to four overrides with replay intact. ADR-0077 shares one such model
across true direct-symbol classes; non-symbol ownership and warm reuse remain.

ADR-0075 advances the parallel proof spine: a direct equal-array/same-index
select conflict now emits literal SMT-LIB `select` and standard equality rules,
checking in-tree, in Carcara, and in real Lean with no reduction trust step.
This is select congruence, not the diff-witness direction of extensionality; ROW,
diff-witness, equality-chain, and canonical online proof logging remain.

ADR-0076 adds deterministic new/delayed/applied cross-equality state across
canonical rounds. A false equality observes its diff index only along one
candidate-true BFS path, closing transitive equality without eager quadratic
preparation. Disconnected SAT stays delayed/replayed, store/UF paths compose with
ROW, and all existing caps remain explicit. It is retained as the historical
precursor that exposed opaque array flags.

ADR-0077 supersedes the cross-diff queue by aligning each flag with its original
array equality in `EufTheory`. The live backtrackable e-graph now closes
reflexive/transitive/congruent array conflicts directly, including the former
512-observation stress case in one round. Candidate-true direct-symbol classes
also share one majority-default projected model, closing transitive SAT replay
with disjoint reads. Parent-select merge scheduling, non-symbol/warm class model
ownership, and proof integration remain before phase exit.

ADR-0078 adds explanation-guarded base-parent select scheduling. Read parents are
pre-registered on `EufTheory`; final candidate e-classes schedule only violated
equal-index/unequal-result pairs. Cross-parent lemmas carry the exact equality
explanation as a guard, so rebuilt rounds and Boolean backtracking remain sound.
Direct-symbol equality no longer prepares every query index, and an 80-array/read
gate stays below the previous 4,096-site failure boundary. All 794 solver tests,
768 comparisons, and public QF_ABV 187/193 / QF_AUFBV 49/53 decisions remain
clean. ADR-0080 subsequently adds structural store parents and ADR-0081 inserts
bounded local ROW inside one search. ADR-0082 subsequently moves pair-generated
UF/select/extensionality scalar interfaces into that retained search. Structural
ITE/default/UF events that require new e-graph terms, warm reuse, non-symbol
models, and proof integration remain before phase exit.

ADR-0079 admits every finite Bool/BitVec array component combination to the same
canonical route. Generic mixed-component models replay, Bool-only UF+array
dispatches, and non-finite-scalar components still decline. Public `issue5925`
and `issue4240` move unknown→unsat/sat; the expanded 1,152-comparison array belt
is clean. A low-load 1 s aggregate remeasure remains because the current host
run moved four unrelated boundary rows to timeout under sustained I/O wait.

ADR-0080 extends final-class parent scheduling from direct symbols to original
store terms. Store reads now receive explanation-guarded select congruence while
remaining independently subject to lazy ROW. Same-parent, congruent-parent,
alternate-branch, unrelated-parent, UF-index, and 80-parent scaling gates pass;
the expanded 1,536-comparison belt and all 802 solver tests are clean. Dynamic
pair-generating insertion, array-valued ITE/default/UF and merge-triggered ROW
events, non-symbol/warm models, proof integration, and the low-load aggregate
remain.

ADR-0081 adds the first same-search array final-check refinement. Each store site
reserves three local ROW atoms dormant; a violated candidate inserts the two
valid permanent clauses and resumes the same `CdclT` instance with learned
clauses, phase state, and activities retained. Hit/miss and two nested ROW sites
close in one outer round, replayed branch changes and the exact shared cap are
pinned, and a UF-bearing index reuses the aligned e-graph atom. The expanded
1,920-comparison belt and all 807 solver tests are clean. Pair-generating
UF/select/extensionality events still rebuild outer rounds; array-valued
ITE/default/UF events, general dynamic atom growth, non-symbol/warm models, proof
integration, and the low-load aggregate remain.

ADR-0082 generalizes retained-search growth to pair-generated scalar interface
equalities. `CdclT` now maps SAT variables explicitly to theory atoms, so an atom
appended after Tseitin auxiliaries does not renumber existing state. `EufTheory`
registers equality atoms only over pre-observed terms, the exact BV component
owns the arena clone needed to intern abstract equalities, and both remain atom-
index aligned with the driver. Function congruence, explanation-guarded base/
store-parent select clauses, and bounded array-equality observations now refine
inside one canonical search; the previous two/three-round mechanism gates pin
one round. The expanded 2,304-comparison belt, all 809 solver tests, and the 11-
test differential binary are clean. Array-valued ITE/default/UF and merge-
triggered events requiring new e-graph nodes, non-symbol/warm models, proof
integration, and the low-load aggregate remain.

ADR-0084 closes the array-valued UF-result event and its cyclic model boundary.
Finite Bool/BitVec array results are first-class in IR/SMT-LIB and abstraction;
original applications remain semantic e-graph parents, while observed entries
project into fresh result arrays grouped by final parent class. Arrays are built
before function tables, so array results and array-valued function keys are both
concrete before replay. Same/different arguments, split observations, direct
equality/disequality, stores, array ITEs, and nested scalar-UF use pass 288
analytic/front-door/Z3 comparisons with zero disagreement. Structural store/ITE/
default class ownership, warm reuse, and online proof logging remain before
phase exit.

ADR-0085 closes the bounded structural class-equation slice. Exact pre-search
array-ITE equality decomposition gives the selected branch a normal e-graph
equality; observed-read-preserving fixed-point realization constructs total leaf
arrays for true store/ITE/constant equations before function projection and
replay. Leaf/depth/step/deadline caps are explicit. A 16-shape matrix contributes
192 direct/front-door/Z3 comparisons with zero disagreement; all 816 solver
units and the prior AUFBV belts remain clean. Warm reuse, nested/extended arrays,
and online array proof logging remain before phase exit.

ADR-0086 begins the incremental warm-reuse boundary. Supported observed reads
over stores, constant arrays, and array ITEs now receive exact private scalar
definitions installed once in `IncrementalBvSolver`'s persistent CNF; scoped
roots retract, only direct leaves project models, and original replay gates SAT.
Exact 512-node/256-depth limits and 192 warm/check-auto/Z3 comparisons pass. The
EVM depth sweep remains slower than frontend ITE folding, motivating ADR-0087
below. Broader warm equality/extensionality/UF, certified memory reachability,
and proofs remain before phase exit.

ADR-0087 makes that retained structural boundary candidate-triggered. Each
observed structural owner keeps one exact transitive scalar summary as dormant
metadata; candidate-false summaries become permanent roots and resume the same
incremental SAT instance under a shared deadline. Replayable misses can install
zero summaries, while nested violated store chains close through one compact
summary rather than one definition per parent. The 192-comparison matrix and
all prior replay gates remain clean. Release EVM depth 32 improves from 30.933
ms to 11.257 ms, but frontend ITE folding remains faster at 0.405 ms. Warm
equality/extensionality, the remaining performance gap, certified memory
reachability, and proofs remain before phase exit.

ADR-0088 retains scalar-keyed array-valued UF applications as warm leaves.
Their finite-scalar arguments and observed indices reuse existing abstraction;
conditional argument/index congruence constrains private read owners; and one
private array result per concrete argument tuple projects into a full-value
function table before original replay. Exact 64/65-parent admission, ten focused
tests, and 192 warm/`check_auto`/Z3 comparisons pass with zero disagreement.
ADR-0090/0091/0092/0093/0094 subsequently add retained structural equality,
Boolean relation flags, direct array-valued UF parameters, supported structural
array-valued UF parameters, and nested array-valued application keys; memory-aware
k-induction subsequently adds array/symbolic-memory safety proving through eager
memory elimination. Nested/extended arrays, certified memory k-induction, memory
PDR/IMC, and proofs remain before phase exit. The EVM corpus does not exercise
array-valued UFs, so no performance change is claimed here.

ADR-0089 adds retained warm array relations. Positive equality merges direct or
array-result-UF projection owners before function construction; top-level
disequality over symbol/store/constant/ITE/application parents receives one
private diff index whose two reads reuse candidate-triggered summaries. Eight
default/nine all-feature gates and 192 warm/`check_auto`/Z3 comparisons pass.
Positive structural equality, Boolean relation flags, direct and supported
structural array-valued parameters and nested array-valued application keys now
follow in ADR-0090/0091/0092/0093/0094. Memory BMC, nested/extended arrays, and
proofs remain. The EVM
corpus has no whole-array relation root, so this increment makes no timing
claim.

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
  with reconstruction **landed**; current measured coverage is substantial but
  uneven, so the trust ledger and generated proof-gap matrix—not capability
  presence—drive "modulo trusted reduction" toward zero
  ([Track 3](../../../docs/plan/track-3-proof-lean/README.md)).
- Proof-assistant interop: Alethe→Lean reconstruction is the
  [Track 3 capstone](../../../docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md).
  The bounded selected-evidence prototype now routes five of eight measured
  reconstruction-only rows through existing consumers. The remaining three are
  measured as separate scoped-kernel-closure (>4 GiB), post-closure compact-
  spooling (<600 MiB), and CPS-tail-reconstruction (<525 MiB) cost lanes under a
  30-second bound. The next boundary is evidence-aware production dispatch plus
  mechanism-specific profiling under the existing hard cap, not a new theorem
  family or a larger memory allowance.
- Lean-system interoperability: the independent Rust checker remains the
  default TCB; the separate pinned format-3.1 `lean4export` reader now admits the
  official flat fixture as eight checked declarations and the direct-recursive
  `MiniNat`/`MiniList` fixture as 11 declarations with no axioms. It compares
  independently generated recursors after binder-correct universe alpha-renaming
  under eleven mutation/negative tests. A four-root official dependency census
  makes projection the first product decline for the structure, Nat-literal,
  and String-literal roots and isolates quotient as a separate closure. Broader
  dependency-closed kernel admission precedes selected Init/Std/mathlib slices,
  Track 6 goals/tactics, and official Lean/Lake/editor adapters. Native source,
  elaboration, modules/Lake, a version-specific untrusted `.olean` reader, LSP,
  compiler/runtime, and full pinned-mathlib compatibility are later staged
  phases with their own gates; none enters the checker TCB or blocks the earlier
  useful profiles. See the
  [compatibility roadmap](../../../docs/plan/lean-system-compatibility-roadmap-2026-07-21.md),
  [implementation plan](../../../docs/plan/lean-system-implementation-plan-2026-07-21.md),
  [completion audit](../../../docs/plan/lean-system-roadmap-completion-audit-2026-07-21.md),
  [measured import result](../../../docs/plan/lean4export-rust-import-prototype-2026-07-21.md),
  and [ADR-0345](../09-decisions/adr-0345-preregister-lean-system-interoperability.md).
- **Categorical-engine depth, not green-field breadth:** the
  [source-backed audit](../../../docs/plan/categorical-engine-depth-audit-2026-07-21.md)
  confirms 125/125 focused tests across six interpolation families, a substantial
  direct CHC/Horn engine, and bounded verified abduction. These are seeded
  capabilities, not absent engines. Advance textual conformance, representative
  Z3/cvc5/Spacer corpora, Horn theory/nonlinear depth, and portable certification
  ([P3.8](../../../docs/plan/track-3-proof-lean/P3.8-interpolation.md),
  [P4.6](../../../docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md),
  [P4.7](../../../docs/plan/track-4-usecases-frontend/P4.7-synthesis.md)). General
  SyGuS remains absent and separately demand-gated.

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
