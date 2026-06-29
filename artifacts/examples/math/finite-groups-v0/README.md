# Finite Groups V0

This pack covers the first core-structure slice for `groups`: finite carriers,
Cayley tables, identity elements, inverses, and associativity.

The examples are finite table artifacts:

- replay the Cayley table for `Z/4Z` under addition;
- replay the inverse table for the same group;
- reject subtraction modulo `3` as a group operation.

These checks are small finite artifacts. They do not claim Lagrange's theorem,
classification results, Sylow theory, or quantified group theory.

## Concepts

- `curriculum_groups`
- `curriculum_relations_and_functions`
- `field_abstract_algebra`

## Trust Story

The validator checks table shape, closure, identity, inverses, and associativity
over the listed finite carrier. For the rejected row, it recomputes the same
axioms and confirms the fixed operation fails to be a group operation.

This pack does not yet emit Axeyum BV/EUF terms or proof certificates. The
graduation route is deterministic finite-table lowering plus checked evidence
for failed axiom claims and universal table identities.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
```
