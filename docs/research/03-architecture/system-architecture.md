# System Architecture

Status: draft
Last updated: 2026-06-10

## Purpose

Describe the ideal Axeyum stack from typed terms down to SAT and evidence.

## Scope

In scope:

- Layering, responsibilities, and data flow.

Out of scope:

- Final crate APIs and exact type definitions.

## Core Claims

- Axeyum should be layered around owned intermediate representations, not direct
  foreign solver AST objects.
- The stack should support both native SMT backends and a pure Rust bit-blast to
  SAT backend.
- Every layer should have a small, testable contract.
- Evidence flows upward: assignments, models, proof traces, rewrite provenance,
  and replayable witnesses.

## Target Stack

```text
client frontends
  -> typed term IR
  -> canonicalization and rewriting
  -> query planning and slicing
  -> solver trait
      -> native SMT backends
      -> word-level BV solver path
          -> bit-blaster
          -> AIG/circuit layer
          -> CNF encoder
          -> SAT backend
  -> model/proof/evidence lifting
  -> checker/replay interfaces
```

## Layer Responsibilities

| Layer | Responsibility |
|---|---|
| Term IR | Sorts, operators, interning, stable IDs, provenance hooks. |
| Rewriter | Local simplification, canonicalization, normalization. |
| Query planner | Assumptions, scopes, slicing, caching, backend selection. |
| Solver trait | Stable result/model interface independent of backend details. |
| Native backends | Z3/cvc5/Bitwuzla/Yices/etc. translation and model lifting. |
| BV backend | Word-level lowering to bits and circuits. |
| Circuit/CNF | AIG or gate graph, Tseitin encoding, variable maps. |
| SAT backend | CDCL or adapter to existing SAT solvers. |
| Evidence | Models, proof traces, certificates, replay artifacts. |

## Design Implications

- Solver-specific contexts should not leak into `axeyum-ir`.
- IDs should be compact and stable within arenas.
- Query caches should key on normalized structure, not string-rendered formulas.
- Backends should report capabilities and limits.

## Risks

- Too many crates too early can slow iteration.
- Too much coupling to one high-level use case can block general adoption.

## Open Questions

- [ ] Should `axeyum-core` contain shared IDs/results or should those live in `axeyum-ir`?
- [ ] Should query planning be a separate crate from rewriting?
- [ ] Should AIG be the first circuit representation or should the first backend lower directly to CNF?

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- Bitwuzla: https://bitwuzla.github.io/docs/
- RustSAT: https://github.com/chrjabs/rustsat

