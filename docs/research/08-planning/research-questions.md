# Research Questions

Status: draft
Last updated: 2026-06-13

## Purpose

Track the questions that should drive experiments and architecture decisions.

## Scope

In scope:

- Open questions across logic, architecture, data structures, algorithms, verification,
  and Rust implementation.

Out of scope:

- Issue tracker replacement.

## Core Claims

- Research questions should be written down before implementation choices harden.
- Each question should eventually resolve into an ADR, benchmark, implementation
  result, or explicit deferral.

## Questions

### Logic And IR

- [x] Should `Bool` and `BV(1)` be distinct in every layer?
  - Answer: yes for the current public IR and backend surface; see
    [ADR-0003](../09-decisions/adr-0003-m0-ir-representation.md).
- [x] Should arrays be in the first public IR?
  - Answer: arrays were added after the scalar core was solid, not in the very
    first IR. The IR now has an `Array` sort and `select`/`store` with a direct
    read-over-write evaluator; see
    [ADR-0010](../09-decisions/adr-0010-arrays-via-eager-elimination.md).
- [x] Should uninterpreted functions be first-class early?
  - Answer: yes, as a first-class IR construct (declarations with a scalar
    signature, `Op::Apply`, and a `FuncValue` interpretation in the model that
    the evaluator honors), eliminated to `QF_BV` by Ackermann reduction — the
    same eager strategy as arrays. Sub-increments 1 (IR + evaluator) and 2
    (`eliminate_functions` + `check_with_function_elimination` end-to-end
    `QF_UFBV` solving with `FuncValue` model projection) are done, as is the
    SMT-LIB I/O round-trip (n-ary `declare-fun` + applications) and `QF_AUFBV`
    theory composition (`check_with_arrays_and_functions`: array then function
    elimination with combined model projection and replay) and oracle-free
    `QF_UFBV` scenarios (`function_catalog`). The EUF rollout now matches the
    array track end to end. Array equality is no longer wholly deferred:
    canonical ABV/AUFBV has bounded diff witnesses, candidate-guided observed
    reads, and candidate-triggered transitive equality paths (ADR-0073/0076),
    with replayed models. Live in-search merge hooks, class-owned models, and
    broader array operators remain. See
    [ADR-0013](../09-decisions/adr-0013-uninterpreted-functions.md).
- [ ] How should undefined or partial operations be represented?
- [ ] What public support matrix should define the first release boundary
      across IR, evaluator, SMT-LIB, oracle, pure Rust backend, and evidence?

### Rewriting

- [x] Which rewrites are always-on?
  - Answer: the first default set is exact-denotation only: Boolean/BV
    constant folds, simple Boolean identities, equality and ITE identities,
    and BV zero/one/all-ones, shift-zero, whole-extract, zero-extension, and
    rotate-zero identities. Equisatisfiability-only rewrites remain disabled
    until model projection exists.
- [x] How are rewrite proofs or obligations represented?
  - Answer: the Phase 3 manifest records stable rule IDs, preconditions,
    preservation class, projection obligations, and required test routes; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
- [ ] Should equality saturation be an optional optimizer?
- [x] Are equisatisfiability-only rewrites allowed before model projection is
      implemented, or must the first default rule set be denotation-preserving?
  - Answer: they may be recorded while disabled, but default rewrites must be
    denotation-preserving until model projection is implemented and tested; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).

### Solvers

- [x] What is the first native backend?
  - Answer: Z3 as a feature-gated oracle; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md) and
    [ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md).
- [x] Which pure Rust SAT solver is the first adapter?
  - Answer: `rustsat-batsat` through RustSAT; see
    [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md).
- [x] When is a custom CDCL implementation justified?
  - Answer: a first *proof-producing* core is justified now by proof production
    (not performance) — DPLL with conflict-cube learning that emits DRAT,
    verified by `check_drat`, giving end-to-end checked `unsat`; see
    [ADR-0012](../09-decisions/adr-0012-proof-producing-sat-core.md). The core
    now uses **1-UIP** conflict analysis and **two-watched-literal**
    propagation (validated by a randomized differential test vs the adapter);
    restarts/heuristics and becoming the default solver remain gated by the
    benchmarking methodology on SAT time dominating.
- [x] What is the minimum incremental-solving API?
  - Answer (stage 1): a warm SAT layer with monotone clause addition plus
    one-shot assumption literals, and a high-level `Solver` façade exposing
    `assert`/`push`/`pop`/`check`/`check_assuming` over it; `push`/`pop` map to
    selector (assumption) literals. Implemented as `IncrementalSat`
    (`axeyum-cnf`) and the `Solver` façade (`axeyum-solver`); see
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md). Stage 2
    (incremental bit-blasting through the same warm layer) is planned there.
- [x] Should Phase 2 include a second native SMT backend?
  - Answer: defer it until a concrete Phase 5 differential-testing or
    trait-design need appears; see
    [ADR-0004](../09-decisions/adr-0004-defer-second-native-backend.md).

### Encodings

- [x] AIG first, or direct CNF?
  - Answer: AIG first, then simple Tseitin CNF; direct term-to-CNF lowering is
    not a public Phase 4 path. See
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] What bit-order convention is public across evaluator values, wire
      vectors, DIMACS lift maps, and model reconstruction?
  - Answer: LSB-first. A `BV(w)` lowers to wires where element `i` is SMT-LIB
    bit index `i` with numeric weight `2^i`; constants, models, and lift maps
    all use the same shared conversion routines. See
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [ ] How are symbolic shifts encoded?
- [x] When do multiplication and division enter the supported subset?
  - Answer: all entered in Phase 5 (2026-06-13). Multiplication (`bvmul`,
    truncated shift-and-add), unsigned division/remainder (`bvudiv`/`bvurem`, a
    combinational restoring divider with SMT-LIB divide-by-zero totality), and
    signed division/remainder/modulo (`bvsdiv`/`bvsrem`/`bvsmod`, sign-handling
    wrappers over the unsigned divider) all lower, each verified exhaustively
    against the ground evaluator. This completes the **full scalar QF_BV
    operator set** for the pure-Rust backend; see the roadmap Phase 5 note and
    [foundational DAG](foundational-dag.md).
- [x] What array lowering comes first?
  - Answer: eager elimination to QF_BV — read-over-write plus Ackermann
    reduction — reusing the bit-blasting pipeline, with array-model projection;
    a lazy lemmas-on-demand procedure is deferred until eager blow-up is
    measured. See
    [ADR-0010](../09-decisions/adr-0010-arrays-via-eager-elimination.md).

### Evidence

- [x] What is the first checkable evidence artifact?
  - Answer: `sat` model replay through the ground evaluator, implemented in
    the solver tests and benchmark harness; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md).
- [ ] Should unsat proof checking be required in high-assurance mode?
  - In progress: an independent in-tree DRAT checker exists (RUP + RAT,
    `axeyum_cnf::check_drat`,
    [ADR-0011](../09-decisions/adr-0011-drat-unsat-proof-checking.md)), and a
    proof-producing SAT core (`solve_with_drat_proof`,
    [ADR-0012](../09-decisions/adr-0012-proof-producing-sat-core.md)) emits DRAT
    that the checker verifies — end-to-end checked `unsat` exists for the
    proof-core path. Making it the *required* high-assurance mode (and wiring it
    into `SatBvBackend` for QF_BV `unsat`) is the remaining step.
- [ ] How are model-lift maps serialized?
- [x] What evidence envelope should carry semantics version, rewrite-rule
      version, bit-blaster version, CNF encoder version, SAT backend version,
      seed, resource limits, corpus hash, model replay, lift maps, and future
      proof artifacts?
  - Answer: use a layered, versioned envelope with source/query provenance,
    logic and semantics version, query schema, rule-set and later layer
    versions, resource config, replay results, projection/lift-map references,
    proof/checker references, and separated triage; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
    A first concrete `Evidence` type now realizes this:
    `axeyum_solver::Evidence` pairs a result with its justification (a `sat`
    model or an `unsat` DIMACS+DRAT certificate) and self-checks via
    `Evidence::check` (model replay / `check_drat` re-run). Versioned provenance
    fields are the remaining extension.

### Incrementality And API

- [x] Assumptions-first or push/pop-first public API?
  - Answer: assumptions-first. `axeyum-query` carries assertions,
    assumptions, and scopes; one-shot solvers enforce assumptions as assertions,
    while future incremental backends can map them to native assumptions; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
- [x] What survives across queries: learned clauses, bit-blast caches, phases?
  - Answer: both. Stage 1 keeps the SAT clause database and learned clauses warm
    across solves (`IncrementalSat`); stage 2 keeps the bit-blast caches warm —
    a persistent AIG + term memo (`IncrementalLowering`) and per-node Tseitin
    (`IncrementalCnf`), driven by `IncrementalBvSolver`. Both implemented
    2026-06-13; see
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md).
- [x] Should solver cancellation support memory budgets as well as time?
  - Answer: yes; `SolverConfig` carries timeout, deterministic resource,
    memory, and node budgets. Memory-budget exhaustion is an `Unknown`
    classification, not an error.
- [ ] Frozen-arena type-state or runtime single-writer discipline?

### Formats

- [x] Full SMT-LIB script support or benchmark-slice parsing first?
  - Answer: benchmark-slice parsing first, with explicit Unsupported errors
    for arrays, UF, and incremental commands; implemented in `axeyum-smtlib`.
- [ ] Which SMT-LIB standard/theory versions should be pinned in artifacts
      and tests before adding conversion operators or future logics?
- [ ] When does BTOR2 import earn its keep?
- [x] Where does the format parser crate boundary land?
  - Answer: `axeyum-smtlib` is a dedicated crate because parsing/writing is
    exercised by solver tests and the benchmark harness, not just a CLI.

### Parallelism

- [ ] Is portfolio dispatch in scope for the first public release?
- [ ] What must be `Send`/`Sync` to make portfolio solving natural?

### Horizon: General Reasoning And Proving

- [x] What binder representation (de Bruijn, locally nameless, named with
      alpha-canonicalization) should the IR adopt when quantifiers arrive,
      and which arena/interning decisions today would foreclose options?
  - Answer (first slice): **named bound variables, reusing `SymbolId`** —
    `Op::Forall(SymbolId)`/`Op::Exists(SymbolId)` over a `Bool` body, so the
    ground evaluator works immediately by binding the symbol over its finite
    domain. Alpha-canonical interning is deferred (an efficiency, not soundness,
    concern); the binder representation may migrate to de Bruijn when
    capture-avoiding instantiation is built. See
    [ADR-0016](../09-decisions/adr-0016-quantifiers-binder-representation.md).
- [x] Which arithmetic enters first: QF_LRA simplex or QF_LIA on top of it?
  - Answer: **`QF_LIA` (integers) first, via bounded bit-blasting** onto the
    existing `QF_BV` pipeline — the cheapest trust-preserving first procedure
    (reuses model replay and the proof core); `sat` is sound and replayable,
    out-of-range is honest `unknown`, never `unsat`. Reals/simplex follow under a
    later ADR. The `Int` sort + evaluator and the bounded bit-blasting procedure
    (`check_with_int_blasting`: blast → solve → exact-integer replay) are both
    done. See [ADR-0014](../09-decisions/adr-0014-first-arithmetic-fragment.md).
    **Reals (`QF_LRA`) follow with an exact-rational simplex** (not a BV
    reduction): the `Real` sort + `Rational` + evaluator are done; the simplex
    procedure is next. See
    [ADR-0015](../09-decisions/adr-0015-linear-real-arithmetic.md).
- [x] What proof format covers theory lemmas once proofs extend beyond
      clausal DRAT/LRAT — adopt Alethe/CPC or design Axeyum-native?
  - Answer: **Alethe is the SMT-level interchange and reconstruction format**;
    DRAT/LRAT remains the clausal substrate. Emit standard rules where possible,
    self-check in-tree, cross-check with Carcara, and keep any Axeyum-only rule a
    narrow, named residual rather than inventing a parallel proof language. The
    trust ledger records unsupported reductions, while Alethe→Lean reconstructs
    checked artifacts into kernel terms. ADR-0011 established the format ladder,
    ADR-0031 made the residual trust countable, and ADR-0075 demonstrates the
    policy on array `select`: one standard-rule artifact checks in-tree, in
    Carcara, and in Lean with no array-elimination trust step.
- [ ] Should the proof-assistant bridge export obligations to Lean, import
      checked rewrite rules from Lean, or both — and how early is a
      Lean-checked rewrite-rule library worth prototyping?
- [x] When two theories exist, is Nelson-Oppen combination implemented
      directly or via a CDCL(T) core from the start?
  - Answer: expose each live combined theory through the shared `TheorySolver`
    contract and let canonical `CdclT` own Boolean structure, interface-variable
    branching, propagation, and conflict learning. A direct conjunctive
    Nelson-Oppen search remains the replay/model-reconstruction oracle and a
    conservative fallback, not a second production Boolean loop. QF_UFLIA,
    QF_UFLRA, and the bounded scalar QF_UFBV route now follow this architecture;
    the latter combines an e-graph with exact warm BV checks over explicit
    argument/result interface equalities. See
    [ADR-0060](../09-decisions/adr-0060-arith-online-cdclt-default-dispatch.md),
    [ADR-0066](../09-decisions/adr-0066-canonical-online-qf-ufbv-combination.md),
    and [P1.6](../../plan/track-1-engine/P1.6-theory-combination.md).

### Rust And Packaging

- [x] How many crates should exist in the first implementation?
  - Answer: start with two crates per
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md); later
    `axeyum-smtlib` and `axeyum-bench` splits were introduced after the
    format and benchmark boundaries were exercised by use.
- [ ] Should optional native backends be separate crates or features?
- [ ] Is `no_std` relevant for any low-level crate?

## Resolution Process

When a question is answered, write a decision record in
[`09-decisions/`](../09-decisions/README.md) using its template
(Context / Decision / Evidence / Alternatives / Consequences), and link it
from the question entry above.

## Open Questions

This file is itself the current open-question register. When individual items are
resolved, keep the resolved question in place long enough to preserve context and
link to the decision note or implementation PR that closed it.

## Source Pointers

- Axeyum research index: ../README.md
