# End To End: Bounded Number Theory

This lesson follows one bounded number-theory resource from CRT compatibility
to residue, square-sum, and Diophantine checks. It uses the
[number-theory-v0](../../../artifacts/examples/math/number-theory-v0/) pack.

Concept rows:

- `curriculum_number_theory`, `curriculum_divisibility_and_euclid`, and
  `curriculum_modular_arithmetic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `crt-compatible-noncoprime-witness` | `sat` | checked |
| `quadratic-residue-witness` | `sat` | checked |
| `quadratic-nonresidue-rejected` | `unsat` | checked |
| `sum-two-squares-witness` | `sat` | checked |
| `sum-two-squares-mod4-rejected` | `unsat` | checked |
| `bounded-diophantine-witness` | `sat` | checked |

The pack is a bounded compute-and-check surface. It does not claim the full
Chinese remainder theorem, quadratic reciprocity, the two-squares theorem, or
the infinitude of primes.

## Replay A Non-Coprime CRT Witness

The CRT row records:

```text
x = 8
x == 2 mod 6
x == 8 mod 10
```

The validator checks both congruences and checks compatibility modulo the gcd:

```text
gcd(6, 10) = 2
2 == 8 mod 2
```

The witness works even though the moduli are not coprime.

## Replay And Reject Quadratic Residues

The residue witness records:

```text
4^2 == 5 mod 11
```

The validator recomputes `16 mod 11 = 5`. The negative row asks for:

```text
x^2 == 3 mod 7
```

The validator enumerates all residues modulo `7` and finds no square root for
`3`.

## Replay And Reject Two-Squares Claims

The positive row records:

```text
65 = 1^2 + 8^2
```

The validator recomputes the equality exactly. The negative row asks for:

```text
7 = a^2 + b^2
```

The trusted check uses the fixed mod-4 obstruction:

```text
7 == 3 mod 4
squares mod 4 are only 0 or 1
```

So no sum of two integer squares can equal `7`.

## Replay A Diophantine Witness

The linear Diophantine witness records:

```text
14*x + 21*y = 7
x = -1
y = 1
```

The validator checks:

```text
14*(-1) + 21*1 = 7
```

This row complements the gcd/Bezout and integer-LIA obstruction rows: here the
gcd divisibility condition is satisfiable, and the pack gives a concrete
solution.

## Name The Lean Horizon

The pack explicitly leaves deeper number theory to proof reconstruction:

```text
quadratic reciprocity
full two-squares theorem
unique factorization
infinitely many primes
```

The bounded rows are still useful because each has a small checkable artifact:
a witness, a finite residue enumeration, or a modular obstruction.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current number-theory resource pattern:

```text
untrusted fast search -> residue, square-sum, or Diophantine candidate
trusted small checking -> exact integer replay, finite enumeration, mod obstruction
```

The graduation route is deterministic BV/enumeration evidence for residue
searches and QF_LIA evidence for Diophantine rows.
