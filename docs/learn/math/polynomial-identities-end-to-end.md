# End To End: Polynomial Identities

This lesson follows one polynomial resource from coefficient multiplication to
root/factor replay and a checked false-root rejection. It uses the
[polynomial-identities-v0](../../../artifacts/examples/math/polynomial-identities-v0/)
pack.

Concept rows:

- `curriculum_polynomials` and `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra`, `field_real_analysis`, and
  `field_complex_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `binomial-square-identity` | `sat` | replay-only |
| `factor-theorem-root-witness` | `sat` | replay-only |
| `false-rational-root-rejected` | `unsat` | checked |

The positive rows replay exact coefficient arithmetic. The negative row is
checked by exact polynomial evaluation at one listed rational candidate.

## Replay Coefficient Multiplication

The binomial row records:

```text
factor = [1, 1]       means 1 + x
expanded = [1, 2, 1]  means 1 + 2x + x^2
```

The validator multiplies the factor by itself:

```text
(1 + x) * (1 + x) = 1 + 2x + x^2
```

and compares normalized coefficient vectors exactly.

## Replay A Factor-Theorem Witness

The factor row records:

```text
p(x) = x^2 - 5x + 6
root = 2
factor = x - 2
quotient = x - 3
```

The validator checks both parts of the witness:

```text
p(2) = 0
(x - 2)(x - 3) = x^2 - 5x + 6
```

This is a fixed root and factorization replay, not a proof of the full factor
theorem for all polynomials.

## Reject A False Rational Root

The false-root row asks whether `1` is a root of:

```text
x^2 + 1
```

The validator evaluates:

```text
1^2 + 1 = 2
```

Since the value is not zero, the claimed root is rejected by exact arithmetic.

## Name The Lean Horizon

The pack does not claim broad polynomial theory:

```text
irreducibility over all fields
algebraic closure
general factorization algorithms
quantification over all polynomials
```

Those need stronger proof routes or Lean artifacts. This pack only checks the
fixed coefficient data it records.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current polynomial-identity resource pattern:

```text
untrusted fast search -> coefficient, root, or factor candidate
trusted small checking -> exact rational coefficient arithmetic
remaining horizon -> proof evidence for general polynomial theorems
```

The graduation route is deterministic Axeyum term encoding plus model replay
and checked evidence for fixed-degree no-counterexample claims.
