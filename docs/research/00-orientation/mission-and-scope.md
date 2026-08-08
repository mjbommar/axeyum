# Mission And Scope

Status: maintained long-horizon orientation; current status lives elsewhere
Last updated: 2026-08-07

> This note defines product identity and scope, not current implementation
> coverage or execution priority. For those, use
> [Project State](../../PROJECT-STATE.md), the generated
> [capability matrix](../08-planning/capability-matrix.md), and root
> [PLAN.md](../../../PLAN.md).

## Purpose

Define Axeyum at the broadest level so the project is not accidentally scoped as
only a binary-reachability tool or only a SAT solver.

## North Star

The long-horizon goal is a **usable, ideally pareto-dominant system for
constrained program optimization and software verification**, built on a
pure-Rust reasoning substrate where automated search and checkable proof are
two faces of one framework. The trajectory is an explicit sequence of
destinations:

1. **Foundation.** Decidable finite-domain core (SAT, QF_BV, arrays, EUF),
   arithmetic, first-cut quantifiers, theory combination, and a
   checkable-evidence envelope. This original foundation is now joined by
   partial higher-rung work.
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

**Current boundary (2026-08-07):** Axeyum spans the foundation and selected
higher-rung solver, evidence, Lean-kernel, CAS, and consumer work. It is
**not yet** a drop-in Z3/cvc5 replacement or a replacement for Lean, angr, or
Unicorn. Floating point, nonlinear arithmetic, strings, datatypes,
quantifiers, reconstruction, and program-analysis routes exist at differing
maturity and assurance levels; their presence is not destination-level parity.

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

Not claimed by the current product — these remain destination requirements,
not permanent exclusions:

- A complete replacement for mature SMT solvers (destination 2).
- A fully general / dependent-type proof assistant, and angr-class binary
  frontends (destination 3).
- Complete, uniformly certified floating-point, nonlinear, string, datatype,
  or quantified reasoning across their full standardized surfaces.

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

- [ ] See the maintained
      [research-questions register](../08-planning/research-questions.md). A
      first stable release boundary and artifact promise remain explicit
      release decisions; the project identity is the broader automated-
      reasoning stack stated above.

## Source Pointers

- Z3 theorem prover: https://github.com/Z3Prover/z3
- Lean proof assistant: https://lean-lang.org/
- RustSAT: https://github.com/chrjabs/rustsat
