# ADR-0007: First Pure Rust SAT Adapter

Status: accepted
Date: 2026-06-11

## Context

Phase 4 now has AIG lowering and simple Tseitin CNF, so the open solver
question in
[research-questions](../08-planning/research-questions.md) must be closed
before CNF solving becomes public surface. The foundational DAG requires a
current comparison before choosing the first Rust SAT adapter, and ADR-0002
keeps the custom CDCL core as the product while allowing an existing Rust SAT
solver as a near-term adapter.

The choice must preserve the default-build rule: no required native C/C++
dependency. It must also produce assignments that Axeyum can replay through
CNF variables, AIG literals, original term bits, and the ground evaluator.

## Decision

Use `rustsat-batsat` through RustSAT as the first pure-Rust CNF/SAT adapter.

The adapter lives in `axeyum-cnf` for now because the exercised boundary is
CNF solving and assignment replay, not a standalone SAT crate. It exposes a
small Axeyum SAT trait, result type, capability metadata, and a typed CNF
assignment. `sat` results are accepted only after the assignment satisfies the
CNF formula and replays through the encoded AIG. `unsat` results from this
adapter are explicitly lower-assurance until a proof-producing path and checker
exist.

## Evidence

- Current crate refresh on 2026-06-11 found `rustsat` 0.7.5 and
  `rustsat-batsat` 0.7.5 on crates.io with declared Rust 1.76 MSRV, which fits
  Axeyum's Rust 1.85 MSRV.
- RustSAT provides common SAT types, solver traits, and solver wrappers; its
  BatSat wrapper exposes `solve`, `solution`, assumptions, and incremental
  interfaces through one trait family.
- RustSAT's solver docs describe BatSat as fully implemented in Rust and
  suitable for restricted compilation scenarios, matching Axeyum's default
  no-native-solver rule.
- The implementation adds tests for raw DIMACS/CNF SAT, raw CNF UNSAT with
  unchecked evidence, and full model replay from an original Axeyum term through
  bit lowering, AIG, Tseitin CNF, BatSat, CNF assignment, AIG node values,
  reconstructed symbol model, and the ground evaluator.

## Alternatives

- Direct `batsat`: pure Rust and MIT licensed, but the RustSAT wrapper gives a
  common SAT trait and assignment types that better match the future adapter
  boundary.
- `splr`: modern pure Rust CDCL and useful as a benchmark/reference solver, but
  the default crate enables an `unsafe_access` feature and has MPL-2.0 licensing
  implications. Keep it as a benchmark candidate, not the first default adapter.
- `varisat`: valuable as a design/proof-output reference, but local project
  guidance treats it as effectively unmaintained and not a guaranteed
  dependency. Revisit when the proof path is being selected.
- RustSAT wrappers for CaDiCaL, Kissat, Minisat, or Glucose: useful comparison
  points, but they pull native solver code into the adapter path and therefore
  cannot be the default pure-Rust route.

## Consequences

- Phase 4 can now solve CNF through a pure-Rust adapter and replay `sat`
  assignments through the existing lift maps.
- UNSAT from this path remains capability-marked lower assurance; high-assurance
  UNSAT still requires a proof-format and checker decision.
- A standalone `axeyum-sat` crate remains deferred until the SAT trait shape is
  exercised by at least one more adapter, assumptions/incrementality, proof
  logging, or the custom CDCL core.
- Phase 6 still owns the custom CDCL implementation. This ADR chooses the
  adapter baseline to beat or replace; it does not demote the custom SAT core
  from the project identity.
