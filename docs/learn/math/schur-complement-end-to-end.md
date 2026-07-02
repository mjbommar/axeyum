# End To End: Finite Schur Complement

This lesson follows one exact Schur-complement resource from block-matrix
replay to determinant and inverse checks, a positive-definite shadow, a
conditional-variance shadow, and a checked bad-scalar rejection. It uses the
[finite-schur-complement-v0](../../../artifacts/examples/math/finite-schur-complement-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`,
  `field_optimization_and_convexity`, and `field_statistics` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_lu_replay`, `bridge_schur_complement`, and
  `bridge_residual_bound` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `schur-complement-replay` | `sat` | replay-only |
| `block-determinant-replay` | `sat` | replay-only |
| `block-inverse-replay` | `sat` | replay-only |
| `positive-definite-schur-replay` | `sat` | replay-only |
| `conditional-variance-replay` | `sat` | replay-only |
| `bad-schur-complement-rejected` | `unsat` | replay-only |
| `qf-lra-bad-schur-complement` | `unsat` | checked |
| `general-schur-complement-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational arithmetic only. It does not certify pivoting,
floating-point stability, SDP theory, Gaussian conditioning, or the general
Schur-complement theorem.

## Replay The Schur Complement

The fixed matrix is:

```text
A = [[4, 2],
     [2, 3]]
```

Split it into one-by-one blocks:

```text
B = [[4]]
C^T = [[2]]
C = [[2]]
D = [[3]]
```

The validator first checks the leading-block inverse:

```text
B^-1 = [[1/4]]
B*B^-1 = [[1]]
```

Then it recomputes:

```text
S = D - C*B^-1*C^T
  = 3 - 2*(1/4)*2
  = 2
```

That is the finite Schur-complement witness.

## Replay Determinant And Inverse Rows

For this two-by-two matrix, exact arithmetic gives:

```text
det(A) = 4*3 - 2*2 = 8
det(B) = 4
det(S) = 2
det(B)*det(S) = 8
```

The inverse row lists:

```text
A^-1 = [[ 3/8, -1/4],
        [-1/4,  1/2]]
```

The validator recomputes both products:

```text
A*A^-1 = I
A^-1*A = I
```

This checks a fixed rational block matrix. It does not prove the block inverse
formula for arbitrary matrices.

## Replay Positive-Definite And Conditional-Variance Shadows

The positive-definite row checks the finite one-by-one criterion:

```text
B = 4 > 0
S = 2 > 0
det(A) = 8 > 0
```

The conditional-variance row reads the same matrix as a covariance matrix:

```text
Var(X) = 4
Cov(Y,X) = 2
Var(Y) = 3
Var(Y | X) shadow = 3 - 2*(1/4)*2 = 2
```

That row is a scalar exact-rational shadow. It is not a Gaussian conditioning
theorem.

## Reject A Bad Schur-Complement Value

The malformed row claims:

```text
S = 3/2
```

Exact replay computes:

```text
S = 2
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
schur_complement = 2
schur_complement = 3/2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because the Schur complement is a shared shape across
block Gaussian elimination, determinant and inverse formulas, positive-definite
tests, SDP/KKT blocks, and covariance conditioning. The checked claim is only
the fixed rational matrix, block split, scalar Schur complement, determinant,
inverse, positive-definite shadow, conditional-variance shadow, and final
scalar contradiction.

General Schur-complement identities, arbitrary block inverse proofs,
Gaussian-elimination correctness, pivoting and stability claims, SDP
duality/Slater theory, and conditional Gaussian covariance theorems remain
theorem or numerical-honesty horizons.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-schur-complement-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_schur_complement_bad_value_artifact_emits_checked_farkas
```
