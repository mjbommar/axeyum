# End To End: Matrix Invariants

This lesson follows one exact matrix-invariant resource from trace and
determinant replay to characteristic roots, Cayley-Hamilton replay, Gershgorin
intervals, and a checked bad characteristic-polynomial rejection. It uses the
[matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_polynomials`,
  `curriculum_rationals`, and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_abstract_algebra`,
  `field_real_analysis`, and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `trace-determinant-characteristic-polynomial` | `sat` | replay-only |
| `characteristic-roots-witness` | `sat` | replay-only |
| `cayley-hamilton-replay` | `sat` | replay-only |
| `gershgorin-interval-witness` | `sat` | replay-only |
| `bad-characteristic-polynomial-rejected` | `unsat` | checked |

The positive rows replay exact rational matrix arithmetic. The negative row
recomputes the actual characteristic polynomial and rejects a bad claimed one.

## Replay Trace, Determinant, And Characteristic Polynomial

The fixed matrix is:

```text
A = [[2, 1],
     [1, 2]]
```

The witness records:

```text
trace(A) = 4
det(A) = 3
chi_A(lambda) = lambda^2 - 4*lambda + 3
```

The validator recomputes all three quantities over exact rationals.

## Replay Characteristic Roots

The listed roots are:

```text
lambda = 1
lambda = 3
```

The validator evaluates:

```text
chi_A(1) = 0
chi_A(3) = 0
```

This is root evaluation for the fixed characteristic polynomial, not a general
eigenvalue theorem.

## Replay Cayley-Hamilton

The witness includes:

```text
A^2 = [[5, 4],
       [4, 5]]
```

The validator checks the matrix polynomial:

```text
A^2 - 4*A + 3*I = 0
```

entry by entry.

## Replay Gershgorin Intervals

For each row, the center is the diagonal entry and the radius is the sum of the
off-diagonal absolute values:

```text
centers = 2, 2
radii = 1, 1
intervals = [1, 3], [1, 3]
```

The validator recomputes the intervals and checks the listed eigenvalues lie
inside them.

## Reject A Bad Characteristic Polynomial

The bad row claims:

```text
lambda^2 - 5*lambda + 6
```

for the same matrix. The validator recomputes the actual characteristic
polynomial:

```text
lambda^2 - 4*lambda + 3
```

and rejects the claimed polynomial. The row also records that the bad claim
evaluates to `2` at `lambda = 1`.

## Name The Horizon

The pack does not claim broad spectral theory:

```text
general spectral theorems
algebraic multiplicity theory
higher-dimensional determinant algorithms
numerical eigensolver correctness
```

Those require stronger proof routes or bounded numerical-analysis metadata.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current matrix-invariant resource pattern:

```text
untrusted fast search -> matrix invariant, root, or interval candidate
trusted small checking -> exact rational matrix and polynomial replay
remaining horizon -> general spectral proof and numerical algorithm routes
```

The graduation route is deterministic exact-rational matrix obligations plus
reusable matrix-invariant utilities once more dimensions and examples justify
that boundary.
