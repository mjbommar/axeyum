# End To End: Finite Shifted QR Step

This lesson follows one exact shifted QR-step resource from a rational
factorization of `A0 - mu*I` to the shifted next matrix, the matching
orthogonal similarity replay, invariant checks, and a checked bad-entry
rejection. It uses the
[finite-shifted-qr-step-v0](../../../artifacts/examples/math/finite-shifted-qr-step-v0/)
pack.

The purpose is narrow: show how Axeyum can check one finite rational shifted
QR step. It is not a proof that a shift is well chosen, that QR iteration
converges, or that a floating-point eigensolver is stable.

## What Axeyum Checks

The pack fixes:

```text
mu = 1
Q = [[3/5, 4/5], [-4/5, 3/5]]
R = [[5, 2], [0, 1]]
A0 = Q*R + mu*I = [[4, 2], [-4, 0]]
A1 = R*Q + mu*I = [[12/5, 26/5], [-4/5, 8/5]]
```

It then records:

| Row | Result | Trust |
|---|---|---|
| `shifted-qr-shape-witness` | `sat` | replay-only |
| `shifted-qr-factorization-witness` | `sat` | replay-only |
| `shifted-qr-update-witness` | `sat` | replay-only |
| `shifted-qr-similarity-witness` | `sat` | replay-only |
| `shifted-qr-invariant-witness` | `sat` | replay-only |
| `bad-shifted-qr-entry-rejected` | `unsat` | replay-only |
| `qf-lra-bad-shifted-qr-entry` | `unsat` | checked |
| `general-shifted-qr-theory-lean-horizon` | `not-run` | Lean horizon |

## Replay The Shifted Factorization

The first row checks the fixed QR shape:

```text
Q^T*Q = I
Q*Q^T = I
R[1,0] = 0
diag(R) = [5, 1]
```

The shifted factorization row then recomputes:

```text
A0 - mu*I = [[3, 2], [-4, -1]]
Q*R = [[3, 2], [-4, -1]]
```

So the resource checks the exact data needed for one shifted step, not an
algorithm that discovered the shift or factorization.

## Replay The Step

The shifted update is:

```text
R*Q = [[7/5, 26/5], [-4/5, 3/5]]
A1 = R*Q + mu*I = [[12/5, 26/5], [-4/5, 8/5]]
```

The same step is an orthogonal similarity:

```text
A1 = Q^T*A0*Q
```

The pack checks that equality directly for the fixed rational matrices.

## Replay The Invariants

Similarity preserves trace and determinant. The finite row checks the two
scalar equalities by recomputing both sides:

```text
trace(A0) = 4 = trace(A1)
det(A0) = 8 = det(A1)
```

This is useful as a compact eigensolver shadow. A theorem resource can later
explain when shifted QR steps converge or deflate. This pack only checks the
one shifted step in front of it.

## Reject A Bad Entry

The malformed source row claims:

```text
A1[1,1] = 2
```

Exact replay computes:

```text
A1[1,1] = 8/5
```

The replay-only row rejects the source claim. The checked row isolates the
scalar contradiction in QF_LRA:

```text
shifted_qr_a11 = 8/5
shifted_qr_a11 = 2
```

The regression emits `UnsatFarkas` evidence from the source SMT-LIB artifact
and independently checks the certificate.

## Boundary

The resource does not cover:

- shift-selection theory;
- convergence of shifted QR iteration;
- deflation and splitting criteria;
- Hessenberg reduction correctness;
- Schur theorem reconstruction;
- eigenvalue ordering or multiplicity theory;
- finite-precision loss of orthogonality;
- floating-point stability.

Those are separate Lean theorem or numerical-honesty resources. The current
pack is deliberately smaller:

```text
untrusted fast search -> candidate shifted QR step or malformed entry
trusted small checking -> exact rational replay plus checked Farkas evidence
```

## Run The Checks

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shifted-qr-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_shifted_qr_step_bad_entry_artifact_emits_checked_farkas
```
