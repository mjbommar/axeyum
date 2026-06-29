# Algebra And Number Theory

Concept rows:

- `field_abstract_algebra` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_modular_arithmetic`, `curriculum_divisibility_and_euclid`, and
  `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)

## What Axeyum Checks

The current algebra path is finite and exact. It checks CRT witnesses, modular
inverses, composite non-units with no inverse, and a Fermat-style finite unit
enumeration. The complex pack adds algebraic real-pair arithmetic and a fixed
polynomial-root witness.

These examples teach algebra as data that can be replayed: a candidate inverse
either multiplies to `1` modulo `n`, or it does not.

## Encode / Check Walkthrough

Start with a witness small enough to check by hand:

```text
3 * 5 = 15 == 1 mod 7
```

The `modular-arithmetic-v0` pack encodes that as `a = 3`, `modulus = 7`, and
`inverse = 5`. The validator recomputes the product modulo `7`; no theorem
about all moduli is needed to trust this witness.

For a polynomial-flavored algebra example, the complex pack encodes `i` as the
real pair `[0, 1]`. The validator squares the pair and checks:

```text
i^2 + 1 = [-1, 0] + [1, 0] = [0, 0]
```

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

## Horizon

General group, ring, field, module, and algebraic-number-theory theorems need
Lean-backed concept rows. Near-term resource gaps are `finite-groups-v0`,
`finite-rings-v0`, `finite-fields-v0`, and richer polynomial identity packs.
