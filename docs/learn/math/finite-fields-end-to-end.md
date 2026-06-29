# End To End: Finite Fields

This lesson follows one finite field resource from modular arithmetic data to
replayed result and proof/evidence status. It uses the
[finite-fields-v0](../../../artifacts/examples/math/finite-fields-v0/) pack.

Concept rows:

- `curriculum_fields`, `curriculum_modular_arithmetic`, and `curriculum_rings`
  in the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `prime-field-inverse-table` | `sat` | replay-only |
| `prime-field-distributivity-no-counterexample` | `unsat` | checked |
| `composite-modulus-nonfield` | `unsat` | checked |

The checked rows are fixed finite residue computations. The pack does not
claim general field theory, field extensions, algebraic closure, or
quantification over all fields.

## Encode

Each row works in a finite residue set:

```text
{0, 1, ..., n-1}
```

with operations:

```text
a + b = (a + b) mod n
a * b = (a * b) mod n
```

For prime `p`, the nonzero residues of `F_p` should have multiplicative
inverses. For composite moduli, a nonzero residue may fail to have an inverse.

## Replay The Inverse Table

The pack lists a complete inverse table for `F_7`:

```text
1 -> 1
2 -> 4
3 -> 5
4 -> 2
5 -> 3
6 -> 6
```

The checker verifies coverage of every nonzero residue and replays each
product:

```text
2 * 4 = 8 = 1 mod 7
3 * 5 = 15 = 1 mod 7
6 * 6 = 36 = 1 mod 7
```

The row is accepted because the fixed table checks out, not because the checker
trusts the producer's assertion that `7` is prime-field arithmetic.

## Check No Distributivity Counterexample In F5

The second row asks for a counterexample to distributivity in `F_5`:

```text
a * (b + c) != a*b + a*c
```

The validator enumerates every triple:

```text
a, b, c in {0, 1, 2, 3, 4}
```

There are only `5^3 = 125` cases. Since none violate distributivity, the
existence claim is checked `unsat`.

This is a finite refutation of one fixed counterexample search, not a proof of
all field axioms for every prime modulus.

## Check The Composite-Modulus Failure

The final row checks the false claim that `2` has an inverse modulo `6`:

```text
exists b in Z/6Z. 2*b = 1 mod 6
```

The checker enumerates all residues:

```text
2*0 = 0 mod 6
2*1 = 2 mod 6
2*2 = 4 mod 6
2*3 = 0 mod 6
2*4 = 2 mod 6
2*5 = 4 mod 6
```

None equals `1`, so the inverse-existence claim is checked `unsat`. This is the
smallest practical lesson in why composite residue rings can fail to be fields.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-fields-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite field arithmetic:

```text
untrusted fast search -> inverse table or counterexample candidate
trusted small checking -> modular products and bounded enumeration
```

General field theory, field extensions, algebraic closure, Galois theory, and
statements quantified over all fields require stronger proof routes or
Lean/mathlib-scale proof support.
