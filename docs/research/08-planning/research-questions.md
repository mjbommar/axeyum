# Research Questions

Status: draft
Last updated: 2026-06-10

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

- [ ] Should `Bool` and `BV(1)` be distinct in every layer?
- [ ] Should arrays be in the first public IR?
- [ ] Should uninterpreted functions be first-class early?
- [ ] How should undefined or partial operations be represented?

### Rewriting

- [ ] Which rewrites are always-on?
- [ ] How are rewrite proofs or obligations represented?
- [ ] Should equality saturation be an optional optimizer?

### Solvers

- [ ] What is the first native backend?
- [ ] Which pure Rust SAT solver is the first adapter?
- [ ] When is a custom CDCL implementation justified?
- [ ] What is the minimum incremental-solving API?

### Encodings

- [ ] AIG first, or direct CNF?
- [ ] How are symbolic shifts encoded?
- [ ] When do multiplication and division enter the supported subset?
- [ ] What array lowering comes first?

### Evidence

- [ ] What is the first checkable evidence artifact?
- [ ] Should unsat proof checking be required in high-assurance mode?
- [ ] How are model-lift maps serialized?

### Incrementality And API

- [ ] Assumptions-first or push/pop-first public API?
- [ ] What survives across queries: learned clauses, bit-blast caches, phases?
- [ ] Should solver cancellation support memory budgets as well as time?
- [ ] Frozen-arena type-state or runtime single-writer discipline?

### Formats

- [ ] Full SMT-LIB script support or benchmark-slice parsing first?
- [ ] When does BTOR2 import earn its keep?
- [ ] Where does the format parser crate boundary land?

### Parallelism

- [ ] Is portfolio dispatch in scope for the first public release?
- [ ] What must be `Send`/`Sync` to make portfolio solving natural?

### Rust And Packaging

- [ ] How many crates should exist in the first implementation?
  - Proposed answer in [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md): start with two.
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
