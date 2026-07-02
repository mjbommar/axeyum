# Finite Cholesky Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a small exact positive-definite matrix-factorization example without
floating point, conditioning, or algorithmic-stability claims.

It fixes a lower-triangular rational matrix `L` with positive diagonal entries
and its symmetric product `A`:

```text
L = [ 2  0 ]
    [ 1  3 ]

A = L L^T = [ 4   2 ]
            [ 2  10 ]
```

The trusted checker recomputes:

- the lower-triangular shape of `L`;
- positivity of the fixed diagonal entries;
- the product `L L^T = A`;
- the two-by-two positive-definite shadow through leading principal minors;
- a malformed product-entry claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove Cholesky existence, uniqueness conventions,
algorithm correctness, pivoting-free applicability, conditioning, or
floating-point stability. Those remain theorem or numerical-honesty work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_optimization_and_convexity`
- `bridge_lu_replay`

## Trust Boundary

```text
untrusted fast search -> candidate lower-triangular factor or malformed product entry
trusted small checking -> exact rational product/minor replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cholesky-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cholesky_decomposition_bad_product_entry_artifact_emits_checked_farkas
```
