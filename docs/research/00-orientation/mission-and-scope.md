# Mission And Scope

Status: draft
Last updated: 2026-06-10

## Purpose

Define Axeyum at the broadest level so the project is not accidentally scoped as
only a binary-reachability tool or only a SAT solver.

## North Star

The long-horizon goal is a complete framework for general reasoning, logic,
and proving. The decidable finite-domain core (SAT, QF_BV, arrays, EUF) is
the first foundation layer, not the destination: the trajectory continues
through arithmetic theories, theory combination, quantifiers, and proof
production toward a system where automated search and checkable proof are
two faces of one framework. The expansion ladder and its landmarks are
recorded in [north-star.md](north-star.md). Phase scoping below bounds what
is built *now*; nothing below bounds what Axeyum *is*.

## Scope

In scope:

- Automated reasoning over finite and symbolic structures.
- Typed term representation for logic, bit-vectors, arrays, and related theories.
- Solver interfaces and native backends.
- Pure Rust SAT and bit-vector research paths.
- Program-analysis and infosec use cases built on the same substrate.
- Evidence production and independent checking.

Out of scope for the first implementation phase:

- A fully general proof assistant.
- A complete replacement for mature SMT solvers.
- Higher-order dependent type theory as the hot-path execution model.
- Full floating-point, nonlinear arithmetic, or quantified reasoning as initial targets.

## Core Claims

- Axeyum is a general reasoning infrastructure project, not a single analyzer.
- The first high-value decidable target is quantifier-free bit-vectors, then arrays
  and uninterpreted functions.
- A practical system should support both fast native solver backends and a growing
  pure Rust path.
- Results should be checkable whenever possible: models by replay, unsat by proof
  or external oracle, rewrites by local proof or differential testing.

## Design Implications

- The lowest crates should not depend on any binary-analysis project.
- The core IR should be domain-neutral: math, CS, verification, and infosec users
  should all be able to express problems without importing a program-analysis API.
- The API should expose enough structure for research: terms, rewrites, circuits,
  clauses, assumptions, proof artifacts, and models should be inspectable.
- Backends are replaceable policy, not the identity of the project.

## Risks

- A too-general scope can delay useful implementation.
- A too-narrow QF_BV identity can make the system hard to extend.
- Solver performance depends on many heuristics that are easy to underestimate.

## Open Questions

- [ ] Should the public identity be "automated reasoning toolkit" or "solver infrastructure"?
- [ ] Should the first release expose a SAT solver, a BV solver, or only the IR and backend interface?
- [ ] What artifact format should be stable first: SMT-LIB, DIMACS, AIGER, DRAT/LRAT, or Axeyum-native JSON/bincode?

## Source Pointers

- Z3 theorem prover: https://github.com/Z3Prover/z3
- Lean proof assistant: https://lean-lang.org/
- RustSAT: https://github.com/chrjabs/rustsat

