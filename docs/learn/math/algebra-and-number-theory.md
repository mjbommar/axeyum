# Algebra And Number Theory

Concept rows:

- `field_abstract_algebra` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_modular_arithmetic`, `curriculum_divisibility_and_euclid`, and
  `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [finite-groups-v0](../../../artifacts/examples/math/finite-groups-v0/)
- [finite-rings-v0](../../../artifacts/examples/math/finite-rings-v0/)
- [modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [finite-fields-v0](../../../artifacts/examples/math/finite-fields-v0/)
- [polynomial-identities-v0](../../../artifacts/examples/math/polynomial-identities-v0/)
- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)

## What Axeyum Checks

The current algebra path is finite and exact. It checks finite group Cayley
tables, finite ring operation tables, CRT witnesses, modular inverses,
composite non-units with no inverse, and a Fermat-style finite unit enumeration.
The finite-rings pack adds distributivity checks and a `Z/4Z` zero-divisor
witness. The finite-fields pack adds a complete inverse table for `F_7`,
exhaustive distributivity checking in `F_5`, and a `Z/6Z` non-field contrast.
The polynomial pack adds exact coefficient replay, factor-theorem witnesses, and
fixed false-root rejection. The complex pack adds algebraic real-pair arithmetic
and a fixed polynomial-root witness.

These examples teach algebra as data that can be replayed: a candidate inverse
either multiplies to `1` modulo `n`, or it does not.

## Encode / Check Walkthrough

Start with a finite group table small enough to check by hand:

```text
Z/4Z under addition
0 + 1 = 1
1 + 3 = 0
2 + 2 = 0
```

The `finite-groups-v0` pack checks closure, identity, inverses, and
associativity for the full Cayley table. For a finite ring example, use `Z/4Z`:

```text
2 * 2 = 0 mod 4
```

The `finite-rings-v0` pack checks the addition and multiplication tables, then
replays `2` and `2` as nonzero zero divisors. Then move to a modular inverse
witness:

```text
3 * 5 = 15 == 1 mod 7
```

The `modular-arithmetic-v0` pack encodes that as `a = 3`, `modulus = 7`, and
`inverse = 5`. The validator recomputes the product modulo `7`; no theorem
about all moduli is needed to trust this witness.

For a field-flavored example, the `finite-fields-v0` pack lists every nonzero
inverse in `F_7`:

```text
2 * 4 = 8 == 1 mod 7
3 * 5 = 15 == 1 mod 7
6 * 6 = 36 == 1 mod 7
```

It also checks that no residue `b` satisfies `2*b == 1 mod 6`, showing the
fixed composite modulus is not a field.

For a polynomial-flavored algebra example, the polynomial pack encodes
`x^2 - 5x + 6` as `[6, -5, 1]`, checks `p(2) = 0`, and verifies:

```text
x^2 - 5x + 6 = (x - 2)(x - 3)
```

The complex pack then encodes `i` as the real pair `[0, 1]`. The validator
squares the pair and checks:

```text
i^2 + 1 = [-1, 0] + [1, 0] = [0, 0]
```

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rings-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-fields-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

## Horizon

General group, ring, field, module, and algebraic-number-theory theorems need
Lean-backed concept rows. Near-term resource gaps are richer polynomial
factorization packs, `gcd-bezout-v0` / `number-theory-v0`, and stronger BV/CNF
evidence for finite group, finite ring, finite-field, and fixed-degree
polynomial universal rows.
