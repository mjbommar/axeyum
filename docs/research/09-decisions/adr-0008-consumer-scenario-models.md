# ADR-0008: Consumer Scenario Models For Testing And Optimization

Status: accepted
Date: 2026-06-13

## Context

Phase 5 optimization work has stalled against a single public academic slice
(`QF_BV/20221214-p4dfa-XiaoqiChen`): roughly fifteen consecutive encoding and
refinement-selection passes all land at "2 `sat` decisions, 111
`EncodingBudget` unknowns". Two problems compound:

1. The slice is not representative of how a real solver *consumer* (symbolic
   execution, program/binary analysis, bit-twiddling verification) builds
   queries. Tuning against it risks chasing a frontier that no downstream use
   actually cares about.
2. The slice's ground truth is the Z3 oracle. ADR-0002 makes Z3 bootstrap
   scaffolding, and the foundational DAG forbids Z3 from becoming part of the
   trusted base; leaning on it as the only "is this answer right" signal is the
   weakest part of the trust story.

We need a corpus that is realistic in *shape*, lives inside the supported
pure-Rust lowering subset (so it actually exercises `SatBvBackend` rather than
bouncing off unsupported `bvmul`/`bvudiv`), scales in difficulty for
optimization measurement, and carries its own ground truth *without* a solver.

## Decision

Add an `axeyum-scenarios` crate that generates self-checking consumer scenario
models whose ground truth comes from the `axeyum-ir` evaluator, never from a
native oracle.

A scenario is a `(TermArena, Query, Expectation)` triple plus provenance.
Ground truth is established by two oracle-free constructions:

- **SAT by concrete execution (the emulation principle).** Choose concrete
  inputs from an explicit seed, run a concrete computation over the supported
  BV operators, and assert constraints the concrete run satisfies by
  construction. The concrete input is carried as a *witness* `Assignment`. The
  scenario self-checks by evaluating every query term under the witness with
  the ground evaluator; all must evaluate to `true`. A solver's `sat` answer is
  then cross-checked against a known-good model, and a solver's `unsat` answer
  is a soundness alarm.
- **UNSAT by bounded-verified identity.** Assert the negation of a bit-vector
  identity. The scenario self-checks by exhaustively evaluating the identity
  over all inputs at the scenario width (feasible at small widths) or, above an
  exhaustive-width threshold, over a deterministic sample (lower assurance,
  recorded as such). If the identity holds for every checked input, its
  negation has no satisfying assignment over that domain, so a solver's `unsat`
  is expected and a solver's `sat` is a soundness alarm.

Scenarios are parameterized (width, rounds, steps, seed) so a family scales
from trivially decidable to currently out-of-reach, giving a measurement
substrate for the abstraction/optimization architecture work.

## Evidence

- The evaluator (`axeyum_ir::eval`) is the project's executable semantic
  reference, total on the QF_BV fragment, and already the level-1 evidence
  check for every `sat`. Using it as the scenario oracle reuses the trusted
  base rather than adding a new trust dependency.
- The initial families stay strictly inside the `axeyum-bv` lowering subset
  (bitwise, `add`/`sub`/`neg`, shifts, constant rotates, `eq`, comparisons,
  `ite`, concat/extract, extensions), confirmed against
  `axeyum_bv::first_unsupported_op` in tests, so they run through the default
  native-free backend.
- Construction-by-concrete-execution is the standard concolic/symbolic-execution
  pattern (pick inputs, execute, collect the path condition); it mirrors the
  realistic consumer this stack is ultimately for.
- Implementation evidence (2026-06-13): `axeyum-scenarios` ships three families
  (`mixing`, `machine`, `identity`) with deterministic seeds. The crate's own
  tests run `self_check` over the catalog; the full-adder UNSAT scenario at
  width 4 is verified exhaustively over all 256 inputs. A new
  `axeyum-solver` differential test runs the entire catalog through
  `SatBvBackend`: all scenarios are decided in ~1.7s with zero unknowns and
  zero soundness alarms, agreeing with the oracle-free ground truth. The
  self-check additionally caught a real generator bug during bring-up (a
  mis-wired two's-complement identity), demonstrating the safety net works.

## Alternatives

- **More public SMT-LIB families.** Useful later, but most non-trivial QF_BV
  benchmarks need multiplication/division (outside the current subset) and
  still depend on an oracle for ground truth. Deferred, not rejected.
- **Random fuzz terms.** Cheap, but random terms have no known status without a
  solver and do not resemble consumer workloads, so they neither strengthen the
  trust story nor guide optimization.
- **Put generators in `axeyum-bench` instead of a new crate.** Rejected:
  scenarios are consumed by unit tests across crates and by the bench harness;
  a leaf crate keeps the dependency direction clean (`scenarios` depends on
  `ir`/`query`, and `bench`/tests depend on `scenarios`). This follows the
  ADR-0001 rule of splitting a crate only when a boundary is exercised by use;
  the boundary here is "shared, oracle-free, self-checking workload generation".

## Consequences

- Optimization and interface work gains a realistic, scalable, oracle-free
  corpus that exercises the pure-Rust path and can run in default CI.
- The trust story improves: scenario ground truth is independent *in kind* from
  the search path (evaluation vs. bit-blasting-to-SAT), so oracle agreement is
  no longer the only correctness signal.
- New maintenance surface: scenario generators are code and must themselves be
  tested (the self-check is that test). Generators must stay inside the
  supported subset until lowering expands.
- This does not add public solver operators, rewrites, or encodings, so it does
  not move the foundational DAG; it adds a testing/measurement boundary only.
- Revisited when lowering gains `bvmul`/division (new scenario families) and
  when an incremental backend lands (scenarios gain multi-check sequences).
