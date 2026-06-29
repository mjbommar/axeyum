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
| `qf-lia-nonunit-diophantine` | `unsat` | checked |
| `fermat-units-mod-prime` | `unsat` | replay-only |

The finite rows still recompute arithmetic directly. The
`qf-lia-nonunit-diophantine` row is the first promoted solver-form proof
artifact in this pack: Axeyum emits and checks an `UnsatDiophantine`
certificate for the nonunit inverse obstruction.

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

## Check A Diophantine Non-Unit Obstruction

The QF_LIA row rewrites the same inverse question into an integer equation:

```text
2*b == 1 mod 6
```

means there are integers `b` and `k` with:

```text
2*b - 6*k = 1
```

The coefficients on the left have gcd `2`, so every integer value of
`2*b - 6*k` is even. The right-hand side is `1`, which is not divisible by
`2`.

Axeyum records that as an `UnsatDiophantine` certificate. The checker
recombines the original equality and verifies the gcd non-divisibility
obstruction; it does not trust the search result alone.

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
trusted small checking -> exact modular arithmetic replay,
                          QF_LIA/Diophantine certificate checking
remaining gap -> checked solver/proof evidence for the remaining finite-search rows
```

The next graduation target is deterministic BV/LIA encoding with checked
evidence for the replayed `sat` rows and the remaining finite-search `unsat`
rows.
