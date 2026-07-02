# Finite Singular-Value Shadow Checks

This pack checks a tiny exact-rational singular-value decomposition shadow for
a diagonal `2x2` matrix. It is intentionally finite: the trusted work is exact
matrix arithmetic and a checked `QF_LRA` contradiction for one false singular
value bound.

It does not claim the general SVD theorem, numerical SVD algorithm
correctness, floating-point stability, or perturbation theory.

## Resource Shape

- fixed matrix `A = [[3, 0], [0, 1]]`;
- exact `A^T A = [[9, 0], [0, 1]]`;
- right and left singular vectors `e1`, `e2`;
- singular values `3` and `1`;
- exact reconstruction `U*Sigma*V^T = A`;
- spectral norm `3`, Frobenius norm squared `10`, and two-norm condition number
  `3`;
- replay-only rejection of the malformed bound `sigma_max <= 2`;
- checked `QF_LRA/Farkas` artifact for the scalar contradiction
  `sigma_max = 3` and `sigma_max <= 2`;
- Lean-horizon row for general SVD, spectral theorem, stability, and
  perturbation guarantees.

## Trust Boundary

```text
untrusted fast search -> candidate singular vectors, singular values, bounds
trusted small checking -> exact rational matrix replay and Farkas certificate
remaining horizon -> general SVD theorem and numerical stability claims
```

## Validate

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-singular-value-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_singular_value_shadow_bad_bound_artifact_emits_checked_farkas
```
