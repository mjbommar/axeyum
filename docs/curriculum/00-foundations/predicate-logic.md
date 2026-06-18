# Predicate Logic

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: Quantifiers (finite domain) · status: `covered`

## What it is

First-order logic: propositions enriched with **predicates**, **variables**, and
the **quantifiers** ∀ (for all) and ∃ (there exists) ranging over a domain of
discourse. "Every natural number has a successor", "there is a prime greater
than n" are predicate-logic statements.

## Role in the tour

The language in which essentially all of mathematics is stated. Quantifiers are
what separate a finite truth-table check from genuine mathematical generality —
and the point at which full automation stops being guaranteed.

## Prerequisites

- [Propositional Logic](propositional-logic.md) — connectives and validity.
- [Sets](sets.md) — the domain a quantifier ranges over.

## Unlocks

- [Proof Methods](proof-methods.md)

## Testable in axeyum

Validity of first-order formulas is **undecidable** in general (Church–Turing).
But over a **finite domain** a quantifier is a finite conjunction/disjunction, so
the formula becomes decidable by expansion. axeyum's quantifier support
(`Op::Forall`/`Op::Exists`, finite-domain enumeration) decides exactly this
fragment, and E-matching instantiation handles many more.

Example exercise: over `BitVec(4)`, `∀x. ∀y. (x + y = y + x)` expands to a
decidable conjunction and is `valid`; `∃x. x + x = 1` is `unsat` (mod any `2ⁿ`
the left side `2x` is even, so it never equals the odd `1`) — a good place to
teach that a quantified claim's answer is fully determined by the finite domain.

**Built** (`Family::Predicate`, closed formulas the evaluator decides by
finite-domain expansion): `forall_additive_identity` (∀x. x+0=x),
`forall_exists_inverse` (∀x ∃y. x+y=0 — genuine quantifier *alternation*), and
`exists_square_root` (∃x. x²=4, satisfiable, the evaluator finding x=2). Teaches
∀/∃ and why finite domains keep first-order validity decidable.

## Lean-horizon

Quantification over infinite domains in the general case (e.g. `∀n ∈ ℕ. P(n)`
without an induction handle) is undecidable — proof-assistant territory.

## References

- Enderton, *A Mathematical Introduction to Logic* (ch. 2).
- axeyum: `check_with_quantifiers`, e-matching keystone (P2.6); ADR-0016.
