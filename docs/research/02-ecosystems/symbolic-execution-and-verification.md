# Symbolic Execution And Verification Ecosystems

Status: draft
Last updated: 2026-06-10

## Purpose

Capture lessons from systems that consume solver infrastructure.

## Scope

In scope:

- Symbolic execution, concolic execution, bounded model checking, and program verification.

Out of scope:

- Detailed architecture of every tool.

## Core Claims

- Solver quality is necessary but not sufficient; query generation and state
  management dominate many real workloads.
- Mature systems separate semantics, symbolic state, memory model, solver query
  construction, search strategy, and evidence/reporting.
- Infosec users need concrete witnesses, provenance, and replay more than abstract
  `sat` answers.
- Math and CS users may need lower-level access to terms, encodings, and proofs.

## Common Architecture

```text
frontend semantics
  -> symbolic state
  -> term/query generation
  -> simplification and slicing
  -> solver backend
  -> model/proof/evidence
  -> replay/report/checker
```

## Lessons For Axeyum

- Keep the core solver stack independent from a particular frontend.
- Make query slicing and dependency tracking first-class, not an afterthought.
- Preserve enough names and provenance for models to be human-usable.
- Treat path search as a client/tactic layer over the solver core.
- Support deterministic replay for concrete witnesses.

## Risks

- Frontend semantics bugs can be misdiagnosed as solver bugs.
- The fastest solver backend may not compensate for poor memory modeling.
- General clients need APIs that are lower-level than a vulnerability-finding tool.

## Open Questions

- [ ] Should Axeyum include a generic symbolic-state crate?
- [ ] Should path exploration live in Axeyum or in clients like binary analyzers?
- [ ] What common model format works for both math users and infosec replay?

## Source Pointers

- KLEE: https://klee-se.org/
- CBMC: https://www.cprover.org/cbmc/
- Kani: https://model-checking.github.io/kani/
- Crux-MIR: https://github.com/GaloisInc/crucible/tree/master/crux-mir

