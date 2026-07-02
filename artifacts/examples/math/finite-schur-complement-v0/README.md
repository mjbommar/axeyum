# Finite Schur Complement

This pack records one exact rational Schur-complement computation for a fixed
two-by-two block matrix. It is a finite matrix replay resource, not a theorem
about arbitrary block matrices, pivoting, covariance conditioning, or numerical
stability.

The fixed matrix is:

```text
A = [[4, 2],
     [2, 3]]
```

with block split:

```text
B = [[4]]
C = [[2]]
D = [[3]]
B^-1 = [[1/4]]
```

Exact replay computes:

```text
S = D - C*B^-1*C^T = [[2]]
det(A) = det(B)*det(S) = 4*2 = 8
```

The inverse row checks:

```text
A^-1 = [[ 3/8, -1/4],
        [-1/4,  1/2]]
A*A^-1 = I
A^-1*A = I
```

The checked QF_LRA/Farkas row isolates one malformed claim:
`S = 3/2`, even though exact replay computes `S = 2`.

## Boundary

This resource checks one exact rational Schur complement, determinant
factorization, inverse, positive-definite shadow, and conditional-variance
shadow. It does not prove the general Schur-complement theorem, block inverse
theorem, Gaussian-elimination correctness, pivoting strategy, Slater-style SDP
criteria, or statistical conditioning theorem.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-schur-complement-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_schur_complement_bad_value_artifact_emits_checked_farkas
```
