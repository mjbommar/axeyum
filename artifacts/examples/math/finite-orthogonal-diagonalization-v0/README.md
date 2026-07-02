# Finite Orthogonal Diagonalization Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a finite spectral-theorem shadow that stays entirely in exact rational
arithmetic. It complements the older spectral, singular-value, and power
iteration packs without claiming a general eigensolver or stability theorem.

It fixes one rational orthogonal diagonalization:

```text
Q = [  3/5  4/5 ]   D = [ 1  0 ]
    [ -4/5  3/5 ]       [ 0  4 ]

A = Q*D*Q^T = [ 73/25  36/25 ]
              [ 36/25  52/25 ]
```

The trusted checker recomputes:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `D` is diagonal;
- `A` is symmetric;
- `Q*D*Q^T = A`;
- each column of `Q` satisfies `A*q_i = lambda_i*q_i`;
- `trace(A) = sum(lambda_i)` and `det(A) = product(lambda_i)`;
- a malformed eigenvalue claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove the spectral theorem, eigenvalue existence,
diagonalization criteria, multiplicity theory, perturbation bounds, eigensolver
convergence, or floating-point stability. Those remain theorem or
numerical-honesty work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_functional_analysis_and_operator_theory`
- `bridge_eigenpair`
- `bridge_exact_vs_floating_arithmetic`

## Trust Boundary

```text
untrusted fast search -> candidate orthogonal basis, diagonal spectrum, or bad row
trusted small checking -> exact rational spectral replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-orthogonal-diagonalization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_orthogonal_diagonalization_bad_eigenvalue_artifact_emits_checked_farkas
```
