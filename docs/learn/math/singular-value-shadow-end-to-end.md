# End To End: Finite Singular-Value Shadow

This lesson follows one exact singular-value resource from `A^T A` replay to
singular-vector equations, SVD reconstruction, norm identities, a two-norm
condition-number shadow, and a checked bad-bound rejection. It uses the
[finite-singular-value-shadow-v0](../../../artifacts/examples/math/finite-singular-value-shadow-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_eigenpair`, `bridge_inner_product_projection`, and
  `bridge_exact_vs_floating_arithmetic` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `ata-gram-replay` | `sat` | replay-only |
| `singular-vector-replay` | `sat` | replay-only |
| `svd-reconstruction-replay` | `sat` | replay-only |
| `spectral-norm-replay` | `sat` | replay-only |
| `condition-number-two-norm-replay` | `sat` | replay-only |
| `bad-singular-value-bound-rejected` | `unsat` | replay-only |
| `qf-lra-bad-singular-value-bound` | `unsat` | checked |
| `general-svd-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational arithmetic only. It does not certify
floating-point SVD algorithms, perturbation theory, rank-revealing stability,
or the general SVD theorem.

## Replay The Gram Matrix

The fixed matrix is:

```text
A = [[3, 0],
     [0, 1]]
```

The validator recomputes:

```text
A^T = [[3, 0],
       [0, 1]]

A^T A = [[9, 0],
         [0, 1]]
```

This turns a singular-value claim into exact rational matrix multiplication.

## Replay Singular Vectors

The listed singular data is:

```text
sigma_1 = 3, v_1 = [1,0], u_1 = [1,0]
sigma_2 = 1, v_2 = [0,1], u_2 = [0,1]
```

The validator checks:

```text
A^T A v_i = sigma_i^2 v_i
A v_i = sigma_i u_i
```

It also checks that the listed left and right vectors are orthonormal. For this
diagonal matrix, every computation is just exact integer arithmetic.

## Replay SVD Reconstruction

The decomposition row uses identity orthogonal factors:

```text
U = I
Sigma = [[3, 0],
         [0, 1]]
V = I
```

The validator checks:

```text
U^T U = I
V^T V = I
U * Sigma * V^T = A
```

This is a finite SVD shadow. It is not a proof that every matrix has an SVD.

## Replay Norms And Conditioning

The exact singular values make the finite norm rows small:

```text
||A||_2 = sigma_max = 3
||A||_F^2 = 3^2 + 1^2 = 10
kappa_2(A) = sigma_max / sigma_min = 3
```

The trusted checker recomputes both the squared-entry sum and the sum of
squared singular values.

## Reject A Bad Singular-Value Bound

The malformed row claims:

```text
sigma_max(A) <= 2
```

Exact replay computes:

```text
sigma_max(A) = 3
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
sigma_max = 3
sigma_max <= 2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows how spectral-norm and condition-number
language can be grounded in one exact finite matrix. The checked claim is only
the rational matrix, Gram matrix, singular vectors, reconstruction, norm
identities, and final scalar contradiction.

General SVD existence, the spectral theorem, singular-value perturbation
theory, pseudospectra, rank-revealing algorithms, and IEEE floating-point
stability remain theorem or numerical-honesty horizons.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-singular-value-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_singular_value_shadow_bad_bound_artifact_emits_checked_farkas
```
