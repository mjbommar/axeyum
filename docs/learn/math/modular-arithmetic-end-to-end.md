# End To End: Modular Arithmetic

This lesson follows one modular-arithmetic resource from concrete congruence
witnesses to finite residue search. It uses the
[modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
pack.

Concept rows:

- `curriculum_modular_arithmetic`, `curriculum_divisibility_and_euclid`, and
  `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` and `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `crt-coprime-witness` | `sat` | replay-only |
| `modular-inverse-witness` | `sat` | replay-only |
| `composite-nonunit-no-inverse` | `unsat` | replay-only |
| `fermat-units-mod-prime` | `unsat` | replay-only |

The validator recomputes the arithmetic, but the pack does not yet carry
solver-level proof artifacts. Its status stays `replay-only` until the finite
search and congruence checks have checked evidence routes.

## Replay A CRT Witness

The CRT row records:

```text
x = 8
x == 2 mod 3
x == 3 mod 5
```

The validator checks:

```text
8 mod 3 = 2
8 mod 5 = 3
gcd(3, 5) = 1
```

This proves the listed witness satisfies the two congruences. It does not
prove the full Chinese remainder theorem.

## Replay A Modular Inverse

The inverse row records:

```text
a = 3
modulus = 7
inverse = 5
```

The validator checks:

```text
gcd(3, 7) = 1
3 * 5 = 15 == 1 mod 7
```

This is the concrete witness shape for an inverse modulo a fixed modulus.

## Search A Composite Non-Unit

The composite-modulus row asks for:

```text
2 * b == 1 mod 6
```

The validator enumerates residues `b = 0..5` and finds no inverse for `2`
modulo `6`. This is finite residue search, not a general theorem about all
composite moduli.

## Search Fermat Counterexamples

The Fermat-style row asks for a unit modulo `5` with:

```text
a^4 != 1 mod 5
```

The validator enumerates the units modulo `5` and finds no counterexample.
The row is a fixed finite check of the theorem shape, not a proof of Fermat's
little theorem for every prime.

## Name The Proof Gap

The pack's graduation criteria are explicit:

```text
encode as Bool/BV or LIA formulas
replay SAT witnesses through Axeyum model evaluation
add checked proof evidence for UNSAT finite-search claims
```

Until then, the row-level arithmetic is replayed but the evidence status
remains `replay-only`.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current modular-arithmetic resource pattern:

```text
untrusted fast search -> congruence witness or residue-search claim
trusted small checking -> exact modular arithmetic replay
remaining gap -> checked solver/proof evidence for the finite-search rows
```

The natural graduation target is deterministic BV/LIA encoding with checked
evidence for the replayed `sat` rows and finite-search `unsat` rows.
