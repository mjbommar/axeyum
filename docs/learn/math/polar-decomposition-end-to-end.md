# End To End: Finite Polar Decomposition

This lesson follows one rational polar decomposition from data row to replayed
result. It uses
[finite-polar-decomposition-v0](../../../artifacts/examples/math/finite-polar-decomposition-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory`
- `bridge_eigenpair` and `bridge_exact_vs_floating_arithmetic`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `polar-shape-witness` | `sat` | replay-only |
| `polar-product-witness` | `sat` | replay-only |
| `polar-normal-equation-witness` | `sat` | replay-only |
| `polar-invariant-witness` | `sat` | replay-only |
| `bad-polar-diagonal-rejected` | `unsat` | replay-only |
| `qf-lra-bad-polar-diagonal` | `unsat` | checked |
| `general-polar-decomposition-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row isolates
the final scalar contradiction in a source SMT-LIB artifact and requires
rechecked `UnsatFarkas` evidence.

## Encode

The fixed polar decomposition is:

```text
U = [[ 3/5, 4/5],
     [-4/5, 3/5]]

P = [[2, 0],
     [0, 5]]

A = [[ 6/5, 4],
     [-8/5, 3]]
```

The checker verifies:

```text
U^T*U = I
U*U^T = I
U*P = A
```

The positive factor is the exact square root shadow of `A^T*A`:

```text
A^T*A = [[4, 0],
         [0, 25]]

P^2 = [[4, 0],
       [0, 25]]
```

The invariant row checks:

```text
trace(P) = 7 = 2 + 5
det(A) = 10 = det(U) * det(P)
```

## Replay

The malformed row is intentionally tiny:

```text
P[1,1] = 4
```

Exact replay reads `P[1,1] = 5`. The source SMT-LIB artifact forces one
real-valued symbol to equal both `5` and `4`, and the route regression requires
independently rechecked Farkas evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-polar-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_polar_decomposition_bad_diagonal_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for a polar factorization, a positive factor, or
a bad claim. The trusted checker recomputes the small exact rational arithmetic
and checks the final linear contradiction. General polar decomposition
existence, uniqueness, rank-deficient partial-isometry forms, square-root
functional calculus, SVD theorem coverage, iterative polar algorithms,
perturbation theory, and floating-point stability stay out of this checked
claim.
