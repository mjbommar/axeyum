# Mission And Scope

Status: draft
Last updated: 2026-06-10

## Purpose

Define Axeyum at the broadest level so the project is not accidentally scoped as
only a binary-reachability tool or only a SAT solver.

## North Star

The long-horizon goal is a **usable, ideally pareto-dominant system for
constrained program optimization and software verification**, built on a
pure-Rust reasoning substrate where automated search and checkable proof are
two faces of one framework. The trajectory is an explicit sequence of
destinations:

1. **Foundation (current).** Decidable finite-domain core (SAT, QF_BV, arrays,
   EUF), bounded `QF_LIA`/`QF_LRA`, first-cut quantifiers, theory combination,
   and a checkable-evidence envelope (models by replay; `unsat` by DRAT/Farkas;
   bit-blasting faithfulness by independent-reference miter).
2. **Complete solver replacement.** A drop-in alternative to mature SMT solvers
   (Z3 / cvc5 class) — full SMT-LIB theory coverage (floating point, strings,
   datatypes/sequences, nonlinear and unbounded arithmetic, mature quantifier
   instantiation) **and competitive performance** (CDCL(T), preprocessing,
   encoding/SAT-core engineering). Performance on real corpora, not theory
   breadth alone, is the gate.
3. **Lean / angr as first-class functionality.** Program analysis in the spirit
   of angr/unicorn — a real binary/IR frontend, memory model, and symbolic
   execution + emulation as first-class APIs (not a test-only consumer) for
   constrained program optimization and verification; and proving in the spirit
   of Lean — kernel-checkable proofs, proof-assistant interop, and the
   evidence / kernel-diversity thesis carried all the way up.

The decidable core is the first layer, **not** the destination. The expansion
ladder and its landmarks are in [north-star.md](north-star.md). Phase scoping
below bounds what is built *now*; nothing below bounds what Axeyum *is*.

**Honest status (2026-06-13):** Axeyum is at destination (1). It is **not yet** a
solver replacement (the pure-Rust path decides only a small slice of real public
QF_BV instances; performance is the open gate) and **not yet** a Lean/angr-class
system (the symbolic-execution consumer is a hand-built register-VM used for
testing, not a binary frontend). Destinations (2) then (3) are the work ahead.

## Scope

In scope (the whole trajectory, sequenced — see destinations above):

- Automated reasoning over finite and symbolic structures.
- Typed term representation for logic, bit-vectors, arrays, and related theories.
- Solver interfaces and native backends.
- Pure Rust SAT and bit-vector research paths, growing to a **complete,
  performance-competitive SMT solver** (destination 2).
- **Program analysis / infosec (angr/unicorn class) and proof assistance (Lean
  class) as first-class functionality** (destination 3), not just consumers
  layered on top.
- Evidence production and independent checking, at every rung.

Out of scope **for the current phase** (destination 1) — these are *later
destinations*, not permanent exclusions:

- A complete replacement for mature SMT solvers (destination 2).
- A fully general / dependent-type proof assistant, and angr-class binary
  frontends (destination 3).
- Full floating-point, nonlinear arithmetic, or production quantified reasoning
  as *current* targets.

## Core Claims

- Axeyum is a general reasoning infrastructure project, not a single analyzer —
  and its endgame is a usable program-optimization / verification system, with
  SMT solving and proof assistance as first-class capabilities, not just a
  library.
- The first high-value decidable target is quantifier-free bit-vectors, then
  arrays and uninterpreted functions; the gate from "foundation" to "solver
  replacement" is **performance on real corpora**, measured against an
  angr+Z3-style baseline, not feature checkboxes.
- A practical system should support both fast native solver backends and a
  growing pure Rust path; the pure-Rust path must eventually *win*, not just run.
- Results should be checkable whenever possible: models by replay, unsat by proof
  or external oracle, rewrites by local proof or differential testing — and this
  evidence thesis is the bridge to the Lean-class destination.

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

