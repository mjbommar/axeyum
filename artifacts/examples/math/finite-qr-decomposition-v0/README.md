# Finite QR Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a small exact matrix-factorization example that uses orthogonality without
floating point, square roots, or numerical-stability claims.

It fixes a rational orthogonal matrix `Q`, an upper-triangular matrix `R`, and
their product `A`:

```text
Q = [  3/5  4/5 ]
    [ -4/5  3/5 ]

R = [ 5  1 ]
    [ 0  2 ]

A = Q R = [  3  11/5 ]
          [ -4   2/5 ]
```

The trusted checker recomputes:

- `Q^T Q = I`;
- the upper-triangular shape of `R`;
- the product `Q R = A`;
- a malformed product-entry claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove QR existence, uniqueness, Householder or
Gram-Schmidt algorithm correctness, conditioning, backward stability, or
least-squares theory. Those remain theorem or numerical-honesty work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_optimization_and_convexity`
- `bridge_lu_replay`
- `bridge_inner_product_projection`

## Trust Boundary

```text
untrusted fast search -> candidate Q/R factors or malformed product entry
trusted small checking -> exact rational orthogonality/product replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-qr-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_qr_decomposition_bad_product_entry_artifact_emits_checked_farkas
```
