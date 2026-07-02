# Exact Finite Covariance Matrix Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a small covariance-matrix example with no floating point, simulation, or
asymptotic statistics claims.

It fixes three two-dimensional rational observations:

```text
(1, 0), (2, 1), (4, 1)
```

The trusted checker recomputes:

- the sample mean vector `(7/3, 2/3)`;
- the centered sample matrix;
- the centered Gram matrix;
- the population covariance matrix;
- a two-by-two positive-semidefinite shadow through leading principal minors;
- a malformed covariance-entry claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove statistical inference, covariance-estimator
consistency, PCA, random-matrix asymptotics, or floating-point covariance
algorithms. Those remain theorem or numerical-honesty work.

## Concept Rows

- `curriculum_counting`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `field_linear_algebra`
- `field_probability_theory`
- `field_statistics`
- `bridge_inner_product_projection`
- `bridge_random_matrix_finite_moment`

## Trust Boundary

```text
untrusted fast search -> candidate mean, covariance, or malformed covariance entry
trusted small checking -> exact rational sample/Gram/covariance replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-covariance-matrix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_covariance_matrix_bad_entry_artifact_emits_checked_farkas
```
