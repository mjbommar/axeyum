# End To End: Finite Rings

This lesson follows one finite ring resource from addition and multiplication
tables to replayed result and proof/evidence status. It uses the
[finite-rings-v0](../../../artifacts/examples/math/finite-rings-v0/) pack.

Concept rows:

- `curriculum_rings` and `curriculum_groups` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `z4-ring-table` | `sat` | replay-only |
| `z4-zero-divisor-witness` | `sat` | replay-only |
| `non-distributive-table-rejected` | `unsat` | checked |
| `non-distributive-table-qf-bv-drat` | `unsat` | checked DRAT |

The checked rows start from finite table replay. The QF_BV row additionally
records the bad distributivity counterexample as a fixed-width bit-vector
contradiction whose generated CNF carries a rechecked DRAT certificate. The pack
does not claim ideal theory, Noetherian/PID/UFD structure, integral-domain
theory in general, or quantified ring theory.

## Encode

The ring witness is `Z/4Z`:

```text
carrier = {0, 1, 2, 3}
zero = 0
one = 1
```

The pack lists two operation tables:

```text
add[row][col] = row + col mod 4
mul[row][col] = row * col mod 4
```

The checker treats these tables as data. It does not trust that the producer
really encoded modular addition and multiplication.

## Replay The Ring Table

The validator checks the finite ring obligations by enumerating table entries:

```text
addition:       abelian group with zero
multiplication: closure and associativity
one:            two-sided multiplicative identity
distributivity: a*(b+c) = a*b + a*c
distributivity: (a+b)*c = a*c + b*c
```

For example:

```text
2 + 3 = 1 mod 4
3 * 3 = 1 mod 4
2 * (1 + 3) = 2 * 0 = 0
2*1 + 2*3 = 2 + 2 = 0
```

The row is accepted only because all finite additive, multiplicative, and
distributive checks pass.

## Replay A Zero Divisor

The pack also lists a zero-divisor witness:

```text
left = 2
right = 2
```

The checker verifies both factors are nonzero and replays the product:

```text
2 != 0
2 * 2 = 0 mod 4
```

So `Z/4Z` is a finite ring with a zero divisor. This fixed witness is enough to
reject an integral-domain claim for this ring, but it is not a theorem about
all rings.

## Check The Refutation

The bad row uses the carrier `{0,1}` with XOR-like addition:

```text
0 + 0 = 0
0 + 1 = 1
1 + 1 = 0
```

Multiplication is left projection:

```text
0*x = 0
1*x = 1
```

Left distributivity fails. With `a = 1`, `b = 0`, and `c = 0`:

```text
a*(b + c) = 1*(0 + 0) = 1*0 = 1
a*b + a*c = 1*0 + 1*0 = 1 + 1 = 0
```

Because `1 != 0`, the fixed claim that this table satisfies distributivity is
rejected.

## Check The Bit-Blast Certificate

The pack also records the same failing table row as a QF_BV artifact:

```text
artifacts/examples/math/finite-rings-v0/smt2/non-distributive-table-bitblast-conflict.smt2
```

The formula asserts that the same one-bit table cell is both `#b1` and `#b0`.
The resource regression parses that SMT-LIB file, proves it `unsat`, exports the
bit-blasted DIMACS plus DRAT refutation, and runs `UnsatProof::recheck` on the
saved text. This checks the clausal refutation; the finite table-to-term
lowering and bit-blast/Tseitin lowering remain named trust steps until a Lean
reconstruction covers the original formula directly.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rings-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_rings_bad_distributivity_emits_checked_drat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite algebraic structures:

```text
untrusted fast search -> candidate addition table, multiplication table, witness
trusted small checking -> ring axioms, zero-divisor replay, counterexample row
trusted small checking -> DIMACS/DRAT recheck for the bit-blasted contradiction
```

General ideal theory, quotient-ring theorems, domain/field structure theorems,
Noetherian/PID/UFD theory, and quantified ring reasoning require stronger
proof routes or Lean/mathlib-scale proof support.
