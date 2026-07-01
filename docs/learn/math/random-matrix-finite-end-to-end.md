# End To End: Finite Random Matrices

This lesson follows one exact finite random-matrix resource from
matrix-valued atom tables to moments, expected Gram matrices, rank
probabilities, and checked bad trace-square and expected-rank claims. It uses the
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
| `bad-expected-rank-rejected` | `unsat` | checked |
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

## Reject A Bad Expected Rank

The bad rank row uses the rank-mixture distribution but claims:

```text
E[rank(A)] = 2
```

The trusted checker recomputes the exact value:

```text
E[rank(A)] = (0 + 1 + 2) / 3 = 1
```

The pack exposes that mismatch as another small `QF_LRA` contradiction:

```text
expected_rank = 1
expected_rank = 2
```

The route regression requires independently rechecked `UnsatFarkas` evidence,
so the false expected-rank value is rejected after exact finite row-reduction
replay.

## Reject A Bad Trace-Square Moment

The bad row uses the same diagonal sign distribution but claims:

```text
E[trace(A)^2] = 1
```

The trusted checker recomputes the exact value:

```text
E[trace(A)^2] = 2
```

The pack exposes that mismatch as the small `QF_LRA` contradiction:

```text
expected_trace_square = 2
expected_trace_square = 1
```

The resource regression sends those constraints through Axeyum's LRA evidence
path and requires independently rechecked `UnsatFarkas` evidence. The claimed
value is inconsistent with the finite atom table, so the false moment claim is
checked `unsat` without trusting the search procedure.

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
cargo test -p axeyum-solver --test math_resource_lra_routes random_matrix_bad_expected_rank_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
test random_matrix_bad_expected_rank_artifact_emits_checked_farkas ... ok
```

## Trust Boundary

This lesson shows Axeyum's current random-matrix resource pattern:

```text
untrusted fast search -> atom table, moment, Gram, rank, or counterexample row
trusted small checking -> exact probability sums and finite matrix replay
proof upgrade -> QF_LRA/Farkas certificate for false trace-square and expected-rank claims
remaining horizon -> asymptotic random matrix theory and numerical experiments
```

The graduation route is deterministic finite enumeration plus checked proof
objects for false finite claims before asymptotic or floating-point random
matrix claims are promoted.
