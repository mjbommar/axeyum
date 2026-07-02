# Finite Walsh-Hadamard Transform Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want an exact orthogonal-transform example without floating point, complex
roots of unity, or asymptotic FFT claims.

It fixes the 4 by 4 Sylvester Hadamard matrix:

```text
H = [ 1  1  1  1
      1 -1  1 -1
      1  1 -1 -1
      1 -1 -1  1 ]
```

and one rational vector `x = [1, 2, -1, 0]`. The trusted checker recomputes:

- `H^T H = 4I`;
- the transform `y = Hx = [2, -2, 4, 0]`;
- inverse reconstruction `x = H y / 4`;
- the exact energy identity `||y||^2 = 4 ||x||^2`;
- a malformed transform-coefficient claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove the general Walsh-Hadamard transform theorem,
orthogonal-transform theory, FFT complexity, numerical stability, or Fourier
analysis. Those remain theorem-horizon work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_functional_analysis_and_operator_theory`
- `field_real_analysis`
- `bridge_inner_product_projection`

## Trust Boundary

```text
untrusted fast search -> transform output, inverse output, or malformed coefficient claim
trusted small checking -> exact rational matrix/vector replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-walsh-hadamard-transform-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_walsh_hadamard_bad_transform_coefficient_artifact_emits_checked_farkas
```
