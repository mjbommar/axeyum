# Research Questions

Status: draft
Last updated: 2026-06-11

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
- [ ] Should arrays be in the first public IR?
- [ ] Should uninterpreted functions be first-class early?
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
- [ ] When is a custom CDCL implementation justified?
- [ ] What is the minimum incremental-solving API?
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
- [ ] When do multiplication and division enter the supported subset?
- [ ] What array lowering comes first?

### Evidence

- [x] What is the first checkable evidence artifact?
  - Answer: `sat` model replay through the ground evaluator, implemented in
    the solver tests and benchmark harness; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md).
- [ ] Should unsat proof checking be required in high-assurance mode?
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

### Incrementality And API

- [x] Assumptions-first or push/pop-first public API?
  - Answer: assumptions-first. `axeyum-query` carries assertions,
    assumptions, and scopes; one-shot solvers enforce assumptions as assertions,
    while future incremental backends can map them to native assumptions; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
- [ ] What survives across queries: learned clauses, bit-blast caches, phases?
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

- [ ] What binder representation (de Bruijn, locally nameless, named with
      alpha-canonicalization) should the IR adopt when quantifiers arrive,
      and which arena/interning decisions today would foreclose options?
- [ ] Which arithmetic enters first: QF_LRA simplex or QF_LIA on top of it?
- [ ] What proof format covers theory lemmas once proofs extend beyond
      clausal DRAT/LRAT — adopt Alethe/CPC or design Axeyum-native?
- [ ] Should the proof-assistant bridge export obligations to Lean, import
      checked rewrite rules from Lean, or both — and how early is a
      Lean-checked rewrite-rule library worth prototyping?
- [ ] When two theories exist, is Nelson-Oppen combination implemented
      directly or via a CDCL(T) core from the start?

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
