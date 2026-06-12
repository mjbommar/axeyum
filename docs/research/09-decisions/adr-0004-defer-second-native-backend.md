# ADR-0004: Defer The Second Native Backend

Status: accepted
Date: 2026-06-11

## Context

Phase 2 listed an optional second native SMT backend, such as Bitwuzla, to check
that the solver trait is not accidentally Z3-shaped. The public QF_BV baseline
is now recorded, and Phase 3 needs the project to move into rewrites and query
planning without expanding linked-solver surface area prematurely.

This closes the Phase 2 roadmap question about whether the second backend must
land before Phase 3.

## Decision

Defer the second native backend until a concrete Phase 5 differential-testing or
trait-design need appears.

Z3 remains the only linked native SMT oracle in the Phase 2/3 path. It stays a
feature-gated leaf dependency and must not become part of the trusted core.

## Evidence

- ADR-0002 establishes that the pure Rust stack is the product and linked
  solvers are bootstrap scaffolding.
- The Phase 2 baseline artifact
  `bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json` records 113 public
  QF_BV files through the trait with no unsupported cases, no parse/solver
  errors, no status disagreements, and no model replay failures.
- Current public APIs expose lifetime-free Axeyum handles, symbol-keyed models,
  structured `unknown`, and capability metadata rather than Z3 FFI types.
- A second linked solver would add native dependency and CI complexity before
  the project has bit-blasting, CNF, or a second theory layer whose behavior
  needs cross-oracle validation.

## Alternatives

- Add Bitwuzla during Phase 2. This would give earlier trait-shape pressure, but
  it expands native dependency surface before there is a pure Rust backend to
  compare against and before query planning creates realistic backend pressure.
- Never add another native backend. That would reduce dependency surface, but it
  would leave too much differential evidence concentrated in one oracle.

## Consequences

Phase 3 can start with the current Z3 oracle baseline. The risk that the trait is
too Z3-shaped is carried explicitly and revisited when Phase 5 starts, or sooner
if query planning, assumptions, arrays/EUF, or model replay expose a concrete
backend abstraction problem.
