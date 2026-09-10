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
- The first pure-Rust SAT adapter *was* `rustsat-batsat` through RustSAT
  ([ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md)). The
  engine on every shipping route is now the in-tree native CDCL core, and the
  adapter is a differential yardstick behind the optional `batsat-reference`
  feature
  ([ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)).
- The first composed pure Rust BV backend is `SatBvBackend` in
  `axeyum-solver`: it lowers supported QF_BV queries through AIG and CNF,
  solves with the native CDCL core, reconstructs Axeyum models, and replays
  original terms before accepting `sat`.

## Risks

- Too many crates too early can slow iteration.
- Too much coupling to one high-level use case can block general adoption.

## Open Questions

- [ ] Should `axeyum-core` contain shared IDs/results or should those live in `axeyum-ir`?
- [x] Should query planning be a separate crate from rewriting?
  - Answer: yes for the Phase 3 contract boundary. `axeyum-query` owns
    assertions, assumptions, scopes, stable labels, structural cache keys, and
    replay-checked target-support slicing; `axeyum-rewrite` owns rewrite
    manifests and canonicalization
    ([ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)).
- [x] Should AIG be the first circuit representation or should the first backend lower directly to CNF?
  - Answer: AIG first, then simple Tseitin CNF, with explicit lift maps across
    original terms, AIG literals, CNF variables, and SAT assignments; see
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] Which pure Rust SAT solver is the first adapter?
  - Answer: `rustsat-batsat` through RustSAT; see
    [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md).
    Superseded as the *engine* by
    [ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md);
    the answer to the question as asked still stands.

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- Bitwuzla: https://bitwuzla.github.io/docs/
- RustSAT: https://github.com/chrjabs/rustsat
- BatSat: https://github.com/c-cube/batsat
