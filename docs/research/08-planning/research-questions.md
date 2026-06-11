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

### Rewriting

- [ ] Which rewrites are always-on?
- [ ] How are rewrite proofs or obligations represented?
- [ ] Should equality saturation be an optional optimizer?

### Solvers

- [x] What is the first native backend?
  - Answer: Z3 as a feature-gated oracle; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md) and
    [ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md).
- [ ] Which pure Rust SAT solver is the first adapter?
- [ ] When is a custom CDCL implementation justified?
- [ ] What is the minimum incremental-solving API?

### Encodings

- [ ] AIG first, or direct CNF?
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

### Incrementality And API

- [ ] Assumptions-first or push/pop-first public API?
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
