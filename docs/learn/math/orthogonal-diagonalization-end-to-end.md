# End To End: Finite Orthogonal Diagonalization

This lesson follows one rational orthogonal diagonalization from data row to
replayed result. It uses
[finite-orthogonal-diagonalization-v0](../../../artifacts/examples/math/finite-orthogonal-diagonalization-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory`
- `bridge_eigenpair` and `bridge_exact_vs_floating_arithmetic`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `orthogonal-matrix-witness` | `sat` | replay-only |
| `orthogonal-diagonalization-witness` | `sat` | replay-only |
| `spectral-eigenpair-witness` | `sat` | replay-only |
| `spectral-invariant-witness` | `sat` | replay-only |
| `bad-spectral-eigenvalue-rejected` | `unsat` | replay-only |
| `qf-lra-bad-spectral-eigenvalue` | `unsat` | checked |
| `general-orthogonal-diagonalization-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row isolates
the final scalar contradiction in a source SMT-LIB artifact and requires
rechecked `UnsatFarkas` evidence.

## Encode

The fixed orthogonal diagonalization is:

```text
Q = [[ 3/5, 4/5],
     [-4/5, 3/5]]

D = [[1, 0],
     [0, 4]]

A = [[73/25, 36/25],
     [36/25, 52/25]]
```

The checker verifies:

```text
Q^T*Q = I
Q*Q^T = I
Q*D*Q^T = A
```

The columns of `Q` are the listed eigenvectors:

```text
A*[3/5, -4/5] = 1*[3/5, -4/5]
A*[4/5,  3/5] = 4*[4/5,  3/5]
```

The invariant row checks:

```text
trace(A) = 5 = 1 + 4
det(A) = 4 = 1 * 4
```

## Replay

The malformed row is intentionally tiny:

```text
lambda_1 = 5
```

Exact replay reads the second diagonal entry of `D` as `4`. The source SMT-LIB
artifact forces one real-valued symbol to equal both `4` and `5`, and the route
regression requires independently rechecked Farkas evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-orthogonal-diagonalization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_orthogonal_diagonalization_bad_eigenvalue_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for a diagonalization, an orthogonal basis, or a
bad claim. The trusted checker recomputes the small exact rational arithmetic
and checks the final linear contradiction. The spectral theorem, eigenvalue
existence, multiplicity theory, residual-to-eigenvalue error bounds, eigensolver
convergence, perturbation theory, and floating-point stability stay out of this
checked claim.
