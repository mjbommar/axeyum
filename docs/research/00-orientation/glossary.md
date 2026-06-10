# Glossary

Status: draft
Last updated: 2026-06-10

## Purpose

Provide common vocabulary for Axeyum design notes.

## Scope

In scope:

- Terms used across solver, verification, and symbolic execution notes.

Out of scope:

- Complete textbook definitions.

## Core Terms

- Ackermannization: Eliminating uninterpreted functions by introducing fresh
  variables plus pairwise consistency constraints.
- AIG: And-inverter graph, a Boolean circuit representation using AND nodes and
  complemented edges.
- BCP: Boolean constraint propagation, the unit-propagation hot path of CDCL.
- Bit-blasting: Translation from fixed-width bit-vector operations to Boolean
  circuits or CNF.
- BMC: Bounded model checking. A finite unrolling of a transition system into a
  satisfiability query.
- BTOR2: Word-level transition-system format from the Boolector lineage.
- CDCL: Conflict-driven clause learning, the dominant architecture for modern SAT solvers.
- CNF: Conjunctive normal form, a conjunction of clauses where each clause is a
  disjunction of literals.
- DPLL(T): SAT search plus theory solvers that explain conflicts in background theories.
- DRAT / LRAT: Clausal unsat proof formats; LRAT adds hints for fast checking.
- E-graph / equality saturation: Data structure and technique for exploring
  many equivalent rewrites simultaneously.
- EUF: Equality with uninterpreted functions.
- Hash-consing: Interning structurally equal terms so equal syntax shares one ID.
- Inprocessing: Simplification interleaved with CDCL search (subsumption,
  vivification, blocked clause elimination).
- IPASIR: De facto C API standard for incremental SAT solving.
- LBD: Literal block distance ("glue"), a learned-clause quality score.
- Model: A satisfying assignment, usually mapped back to user variables or symbols.
- PAR-2: Competition scoring metric; timeouts count as twice the time limit.
- QF_BV: Quantifier-free fixed-size bit-vector logic.
- SAT: Boolean satisfiability.
- SMT: Satisfiability modulo theories.
- Tseitin encoding: Translation from circuits to CNF with auxiliary variables.
- UIP: Unique implication point, used in CDCL conflict analysis.
- Unsat core: A subset of assertions/assumptions that is already unsatisfiable.

## Design Implications

- Axeyum should name public concepts according to established solver vocabulary.
- Internal names should distinguish `Term`, `Wire`, `Lit`, `Var`, `Clause`, and
  `Model`; these are related but not interchangeable.

## Open Questions

- [ ] Should Axeyum expose both `Bool` and `BV(1)` or force an explicit bridge?
- [ ] Should "term" or "expr" be the public name for the high-level IR?

## Source Pointers

- SMT-LIB initiative: https://smt-lib.org/
- SAT Competition: https://satcompetition.github.io/

