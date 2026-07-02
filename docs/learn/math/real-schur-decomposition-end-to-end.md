# End To End: Finite Real Schur Decomposition

This lesson follows one rational real Schur decomposition from data row to
replayed result. It uses
[finite-real-schur-decomposition-v0](../../../artifacts/examples/math/finite-real-schur-decomposition-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory`
- `bridge_eigenpair` and `bridge_exact_vs_floating_arithmetic`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `schur-shape-witness` | `sat` | replay-only |
| `schur-reconstruction-witness` | `sat` | replay-only |
| `schur-vector-relation-witness` | `sat` | replay-only |
| `schur-invariant-witness` | `sat` | replay-only |
| `bad-schur-superdiagonal-rejected` | `unsat` | replay-only |
| `qf-lra-bad-schur-superdiagonal` | `unsat` | checked |
| `general-real-schur-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row isolates
the final scalar contradiction in a source SMT-LIB artifact and requires
rechecked `UnsatFarkas` evidence.

## Encode

The fixed Schur decomposition is:

```text
Q = [[ 3/5, 4/5],
     [-4/5, 3/5]]

T = [[1, 2],
     [0, 4]]

A = [[97/25, 54/25],
     [ 4/25, 28/25]]
```

The checker verifies:

```text
Q^T*Q = I
Q*T*Q^T = A
A*Q = Q*T
```

The first column of `Q` is an eigenvector:

```text
A*[3/5, -4/5] = 1*[3/5, -4/5]
```

The second column has Schur triangular coupling:

```text
A*[4/5, 3/5] = 2*[3/5, -4/5] + 4*[4/5, 3/5]
```

The invariant row checks:

```text
trace(A) = 5 = 1 + 4
det(A) = 4 = 1 * 4
```

## Replay

The malformed row is intentionally tiny:

```text
T[0,1] = 3
```

Exact replay reads `T[0,1] = 2`. The source SMT-LIB artifact forces one
real-valued symbol to equal both `2` and `3`, and the route regression requires
independently rechecked Farkas evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-real-schur-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_real_schur_decomposition_bad_superdiagonal_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for a triangular form, an orthogonal basis, or a
bad claim. The trusted checker recomputes the small exact rational arithmetic
and checks the final linear contradiction. Real/complex Schur existence,
eigenvalue ordering, multiplicity theory, QR-iteration convergence,
perturbation theory, and floating-point stability stay out of this checked
claim.
