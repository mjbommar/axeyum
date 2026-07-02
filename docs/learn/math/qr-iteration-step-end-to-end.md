# End To End: Finite QR Iteration Step

This lesson follows one exact QR-iteration resource from a rational QR
factorization to the next matrix, the matching orthogonal similarity replay,
invariant checks, and a checked bad-entry rejection. It uses the
[finite-qr-iteration-step-v0](../../../artifacts/examples/math/finite-qr-iteration-step-v0/)
pack.

The purpose is narrow: show how Axeyum can check one finite rational QR step.
It is not a proof that QR iteration converges, that a shift rule is correct, or
that a floating-point eigensolver is stable.

## What Axeyum Checks

The pack fixes:

```text
Q = [[3/5, 4/5], [-4/5, 3/5]]
R = [[5, 2], [0, 1]]
A0 = Q*R = [[3, 2], [-4, -1]]
A1 = R*Q = [[7/5, 26/5], [-4/5, 3/5]]
```

It then records:

| Row | Result | Trust |
|---|---|---|
| `qr-step-shape-witness` | `sat` | replay-only |
| `qr-step-factorization-witness` | `sat` | replay-only |
| `qr-step-update-witness` | `sat` | replay-only |
| `qr-step-similarity-witness` | `sat` | replay-only |
| `qr-step-invariant-witness` | `sat` | replay-only |
| `bad-qr-step-entry-rejected` | `unsat` | replay-only |
| `qf-lra-bad-qr-step-entry` | `unsat` | checked |
| `general-qr-iteration-theory-lean-horizon` | `not-run` | Lean horizon |

## Replay The Shape

The first row checks only finite matrix arithmetic:

```text
Q^T*Q = I
Q*Q^T = I
R[1,0] = 0
diag(R) = [5, 1]
```

This proves that the source data really has the shape of a QR factorization.
It does not prove that an algorithm found `Q` and `R`.

## Replay The Step

The factorization row recomputes:

```text
Q*R = [[3, 2], [-4, -1]] = A0
```

The QR-step row recomputes:

```text
R*Q = [[7/5, 26/5], [-4/5, 3/5]] = A1
```

For unshifted QR iteration, the same step is an orthogonal similarity:

```text
A1 = Q^T*A0*Q
```

The pack checks that equality directly for the fixed rational matrices.

## Replay The Invariants

Similarity should preserve trace and determinant. The finite row checks the
two scalar equalities by recomputing both sides:

```text
trace(A0) = 2 = trace(A1)
det(A0) = 5 = det(A1)
```

This is useful as a compact eigensolver shadow: a later theorem resource can
explain when repeated QR steps approach Schur or diagonal form. This pack only
checks the one step in front of it.

## Reject A Bad Entry

The malformed source row claims:

```text
A1[0,0] = 2
```

Exact replay computes:

```text
A1[0,0] = 7/5
```

The replay-only row rejects the source claim. The checked row isolates the
scalar contradiction in QF_LRA:

```text
qr_step_a00 = 7/5
qr_step_a00 = 2
```

The regression emits `UnsatFarkas` evidence from the source SMT-LIB artifact
and independently checks the certificate.

## Boundary

The resource does not cover:

- convergence of QR iteration;
- shifted QR iteration;
- Hessenberg reductions and deflation criteria;
- Schur theorem reconstruction;
- eigenvalue ordering or multiplicity theory;
- finite-precision loss of orthogonality;
- floating-point stability.

Those are separate Lean theorem or numerical-honesty resources. The current
pack is deliberately smaller:

```text
untrusted fast search -> candidate QR step or malformed entry
trusted small checking -> exact rational replay plus checked Farkas evidence
```

## Run The Checks

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-qr-iteration-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_qr_iteration_step_bad_entry_artifact_emits_checked_farkas
```
