# ADR-0573: Proof SAT branches only on active variables

Status: accepted
Date: 2026-08-26
Index-summary: Exclude declared-but-unused CNF variables from proof-producing SAT decisions

## Context

Axeyum CNF formulas retain an explicit declared variable count. That is necessary for DIMACS
round trips and total model construction, but the internal proof-producing SAT engine used the
count as its decision universe: it seeded its VSIDS heap with every declared variable, including
variables absent from every clause.

This became a concrete compositional-search defect. A checked cover over two semantic job-shop
order selectors inherited the parent formula's 175,170-variable namespace. Its four clauses
mentioned only selector variables 174,786 and 175,151, yet proof search spent more than two
minutes deciding irrelevant lower-numbered variables before it was stopped. The logical problem
has only two active variables.

## Decision

The proof SAT engine records whether each declared variable occurs in an original clause and
seeds its decision heap with only those active variables. Backtracking likewise reinserts only
active variables. Variables absent from all clauses remain assigned false when the solver emits
its total SAT model.

Clause propagation, conflict analysis, DRAT emission, variable numbering, formula serialization,
and public model width are unchanged. Activity is determined from the original formula rather
than learned clauses: a learned clause can contain only variables already present in the formula's
resolution problem.

## Evidence

- A regression formula declares 200,000 variables but contains the four exhaustive clauses over
  only variables 199,999 and 200,000. The decision heap contains exactly those two variables and
  the emitted two-step UNSAT proof is accepted by the independent DRAT checker.
- The real 175,170-variable machine-order cover now emits and checks in 3.55 seconds, with four
  clauses and two proof steps. Before this change the same cover ran for more than two minutes
  without reaching those two high-numbered decisions.
- The complete `axeyum-cnf` test suite and all-target/all-feature Clippy cover the changed route.

## Consequences

Sparse projections may preserve a parent formula's stable variable identities without making
runtime proportional to the unused prefix of that namespace. This is particularly important for
cube-cover proofs, assumptions, and independently composable partitions over semantic selectors.

The change is a search optimization, not a stronger proof rule. UNSAT remains acceptable only
when the generated proof checks against the exact projected formula; SAT models remain total and
assign every declared-but-unused variable false deterministically.
