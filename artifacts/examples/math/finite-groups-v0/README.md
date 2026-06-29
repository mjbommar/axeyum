# Finite Groups V0

This pack covers the first core-structure slice for `groups`: finite carriers,
Cayley tables, identity elements, inverses, and associativity.

The examples are finite table artifacts:

- replay the Cayley table for `Z/4Z` under addition;
- replay the inverse table for the same group;
- reject subtraction modulo `3` as a group operation;
- certify binary-operation congruence with QF_UF/Alethe evidence.

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

This pack also includes one proof-object row: the SMT-LIB artifact in
`smt2/group-operation-congruence-conflict.smt2` treats the group operation as a
binary uninterpreted function and certifies that equal operands force equal
products. The resource regression requires a pure EUF `Evidence::UnsatAletheProof`
and rechecks it independently.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
```
