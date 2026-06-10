# Automated Reasoning Foundations

Status: draft
Last updated: 2026-06-10

## Purpose

Place Axeyum in the broader math and CS landscape.

## Scope

In scope:

- Automated reasoning, decision procedures, model finding, and verification.
- Relationship between program behavior and logic.

Out of scope:

- Full proof theory or type theory treatment.

## Core Claims

- Axeyum is an instance of automated reasoning: represent a problem as logic,
  transform it, solve it, and return evidence.
- For program analysis, the common abstraction is transition-system reachability.
- For bit-vector-heavy program semantics, fixed-width finite domains make many
  useful questions decidable and reducible to SAT.
- Solver automation should be treated as heuristic unless accompanied by a
  checkable certificate.

## Conceptual Stack

```text
domain problem
  -> formal model
  -> logical formula
  -> simplification and normalization
  -> decision procedure
  -> model, proof, or unknown
  -> checker or replay
```

Examples:

- Math user: finite algebraic constraint -> satisfying model or contradiction.
- CS user: transition system -> reachability or invariant counterexample.
- Infosec user: input bytes -> path condition -> concrete witness.

## Design Implications

- Axeyum should provide a clean bridge from domain models into a typed logical core.
- It should separate trusted checking from untrusted search.
- `unknown` is a first-class result, not an error.
- The system should keep enough provenance to map solver evidence back to user concepts.

## Risks

- Users may expect complete theorem proving when the early target is decidable,
  finite-domain constraint solving.
- Optimization can obscure provenance unless evidence tracking is designed early.

## Open Questions

- [ ] Which proof/certificate formats should be supported before a custom SAT core exists?
- [ ] How much provenance should be stored in the default term arena?

## Source Pointers

- Handbook-style background: SAT, SMT, model checking, term rewriting, abstract interpretation.
- Z3: https://github.com/Z3Prover/z3
- cvc5: https://cvc5.github.io/
- Lean: https://lean-lang.org/

