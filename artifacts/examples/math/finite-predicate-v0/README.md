# Finite Predicate Logic

Audience: learners and proof/solver contributors who need a concrete first
step from propositional truth tables to quantified mathematical language.

This pack checks first-order predicate formulas only over explicit finite
universes. A universal quantifier is replayed as a finite conjunction and an
existential quantifier as a finite disjunction. That makes the examples
decidable without claiming general first-order validity.

## Concept Rows

- `curriculum_predicate_logic`
- `curriculum_relations_and_functions`
- `field_logic_and_proof`
- `field_set_theory_and_foundations`

## Claims

- A unary predicate table can witness `forall x. P(x)` over a finite universe.
- A unary predicate table can witness `exists x. P(x)`.
- Over a non-empty finite universe, `forall x. P(x)` implies
  `exists x. P(x)`; the fixed two-element refutation row is also tied to a
  source CNF with checked DRAT/LRAT evidence.
- `exists x. P(x)` does not imply `forall x. P(x)`, and the validator replays a
  counterexample.
- A finite binary predicate table can witness failure of relation symmetry.
- General first-order validity remains a Lean/proof-assistant horizon.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
```

The validator checks the finite predicate tables against the listed universes,
enumerates unary predicate valuations for the bounded UNSAT row, verifies the
source DIMACS artifact for that row, and keeps the general first-order theorem
row marked `lean-horizon`.

## Limitations

This pack is about finite model replay and bounded quantifier expansion. It
does not prove completeness, compactness, Lowenheim-Skolem, or validity over
infinite domains. Those need a named proof-assistant route before graduation.
