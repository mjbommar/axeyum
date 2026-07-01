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
| `qf-lia-incompatible-crt-diophantine` | `unsat` | checked |
| `fermat-units-mod-prime` | `unsat` | replay-only |
| `fermat-units-mod-prime-qf-bv-drat` | `unsat` | checked |

The finite rows still recompute arithmetic directly. The
`qf-lia-nonunit-diophantine` and `qf-lia-incompatible-crt-diophantine` rows are
the promoted solver-form proof artifacts in this pack: Axeyum emits and checks
`UnsatDiophantine` certificates for the nonunit inverse and incompatible CRT
obstructions. The Fermat-unit QF_BV row is a fixed-width proof artifact for the
same modulo-5 finite search: Axeyum bit-blasts the residue formula and rechecks
the emitted DIMACS/DRAT refutation.

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

## Check An Incompatible CRT Pair

The checked CRT obstruction asks for:

```text
x == 1 mod 4
x == 2 mod 6
```

A shared solution would give integers `a,b` with:

```text
x = 1 + 4*a
x = 2 + 6*b
4*a - 6*b = 1
```

But every value of `4*a - 6*b` is divisible by `gcd(4,6)=2`, and `1` is not.
The SMT-LIB artifact encodes that derived integer equation and the
`UnsatDiophantine` checker replays the gcd obstruction.

## Search Fermat Counterexamples

The Fermat-style row asks for a unit modulo `5` with:

```text
a^4 != 1 mod 5
```

The validator enumerates the units modulo `5` and finds no counterexample.
The row is a fixed finite check of the theorem shape, not a proof of Fermat's
little theorem for every prime.

The promoted QF_BV row represents the candidate as a 3-bit word with
`0 < a < 5`, computes `a^4` at 9-bit width so `4^4 = 256` is exact, reduces
modulo `5`, and asserts the impossible branch `a^4 mod 5 != 1`. The checked
object is the DRAT refutation of that fixed-width formula; the modular
exponent lowering and bit-blast/Tseitin steps remain explicit trust steps.

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
cargo test -p axeyum-solver --test math_resource_lia_routes modular_incompatible_crt_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_bv_routes modular_arithmetic_fermat_units_mod5_emits_checked_bv_drat
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
                          QF_LIA/Diophantine certificate checking,
                          QF_BV DIMACS/DRAT proof checking
remaining gap -> checked solver/proof evidence for replayed sat rows and broader theorems
```

The next graduation target is deterministic evidence for replayed `sat` rows
or a Lean theorem route for the general number-theory statements.
