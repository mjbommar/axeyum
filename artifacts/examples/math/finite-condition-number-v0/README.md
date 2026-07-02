# Finite Condition Number

This pack records one exact rational condition-number computation for a fixed
diagonal matrix. It is a finite numerical-linear-algebra shadow, not a theorem
about arbitrary matrices or floating-point stability.

The fixed matrix is:

```text
A = [[2, 0],
     [0, 1/3]]
```

Exact replay computes:

```text
A^-1 = [[1/2, 0],
        [0, 3]]

||A||_infinity = 2
||A^-1||_infinity = 3
kappa_infinity(A) = 6
```

The perturbation row uses:

```text
x = [1, 1]
b = A*x = [2, 1/3]
delta_b = [0, 1/30]
delta_x = A^-1*delta_b = [0, 1/10]
```

So:

```text
||delta_b||_infinity / ||b||_infinity = 1/60
||delta_x||_infinity / ||x||_infinity = 1/10
kappa_infinity(A) * (1/60) = 1/10
```

The checked QF_LRA/Farkas row isolates one malformed claim:
`kappa_infinity(A) <= 5`, even though exact replay computes `6`.

## Boundary

This resource checks one exact rational condition-number and one exact
perturbation-bound shadow for one diagonal matrix. It does not prove general
condition-number theory, backward stability, algorithmic stability, singular
value conditioning, pseudospectra, IEEE floating-point roundoff, or error
analysis for arbitrary solvers.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-condition-number-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_condition_number_bad_condition_artifact_emits_checked_farkas
```
