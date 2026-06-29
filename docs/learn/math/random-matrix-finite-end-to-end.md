# End To End: Finite Random Matrices

This lesson follows one exact finite random-matrix resource from
matrix-valued atom tables to moments, expected Gram matrices, rank
probabilities, and a checked bad trace-square moment. It uses the
[random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/)
pack.

Concept rows:

- `curriculum_counting`, `curriculum_rationals`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_statistics`, `field_linear_algebra`,
  and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `sign-diagonal-moments` | `sat` | replay-only |
| `expected-gram-matrix` | `sat` | replay-only |
| `rank-mixture-probabilities` | `sat` | replay-only |
| `bad-trace-moment-rejected` | `unsat` | checked |

Every row is a finite probability table over exact rational matrices. The pack
does not claim asymptotic random matrix theory, spectral laws, or numerical
simulation validity.

## Replay Diagonal Sign Moments

The first distribution is uniform over four diagonal sign matrices:

```text
pp = [[ 1, 0], [0,  1]]
pn = [[ 1, 0], [0, -1]]
np = [[-1, 0], [0,  1]]
nn = [[-1, 0], [0, -1]]
probability of each atom = 1/4
```

The validator first checks that the probabilities sum to `1`. It then
recomputes the trace and determinant of each atom:

```text
trace:        2,  0,  0, -2
trace^2:      4,  0,  0,  4
determinant:  1, -1, -1,  1
```

The exact expectations are:

```text
E[trace(A)] = (2 + 0 + 0 - 2) / 4 = 0
E[trace(A)^2] = (4 + 0 + 0 + 4) / 4 = 2
E[det(A)] = (1 - 1 - 1 + 1) / 4 = 0
P(A is invertible) = 1
```

This is finite enumeration over a matrix-valued probability space.

## Replay The Expected Gram Matrix

For every diagonal sign matrix in this distribution:

```text
A^T * A = I
```

The validator recomputes each `A^T*A` and the weighted expectation:

```text
E[A^T*A] = I = [[1, 0],
                [0, 1]]
```

This is an exact finite Gram-matrix expectation, not a limit law.

## Replay Rank Probabilities

The rank-mixture distribution is uniform over:

```text
zero      = [[0, 0], [0, 0]]   rank 0
rank-one  = [[1, 1], [1, 1]]   rank 1
identity  = [[1, 0], [0, 1]]   rank 2
```

The validator recomputes the ranks and checks:

```text
P(rank = 0) = 1/3
P(rank = 1) = 1/3
P(rank = 2) = 1/3
E[rank] = (0 + 1 + 2) / 3 = 1
```

This is the resource pattern for finite rank-distribution claims.

## Reject A Bad Trace-Square Moment

The bad row uses the same diagonal sign distribution but claims:

```text
E[trace(A)^2] = 1
```

The trusted checker recomputes the exact value:

```text
E[trace(A)^2] = 2
```

The claimed value is inconsistent with the finite atom table, so the false
moment claim is checked `unsat`.

## Name The Horizon

The pack does not claim broad random matrix theory:

```text
asymptotic spectral laws
concentration inequalities for matrix ensembles
high-dimensional limits
floating-point simulation correctness
numerical eigensolver behavior on random inputs
```

Those require Lean-backed probability/linear-algebra proofs or explicit
reproducibility metadata for numerical experiments. This pack only checks
finite exact-rational matrix-valued probability tables.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current random-matrix resource pattern:

```text
untrusted fast search -> atom table, moment, Gram, rank, or counterexample row
trusted small checking -> exact probability sums and finite matrix replay
remaining horizon -> asymptotic random matrix theory and numerical experiments
```

The graduation route is deterministic finite enumeration plus checked proof
objects for false finite claims before asymptotic or floating-point random
matrix claims are promoted.
