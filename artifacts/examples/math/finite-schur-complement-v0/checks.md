# Checks

| Check | Expected | Evidence |
|---|---|---|
| `schur-complement-replay` | `sat` | replay-only |
| `block-determinant-replay` | `sat` | replay-only |
| `block-inverse-replay` | `sat` | replay-only |
| `positive-definite-schur-replay` | `sat` | replay-only |
| `conditional-variance-replay` | `sat` | replay-only |
| `bad-schur-complement-rejected` | `unsat` | replay-only |
| `qf-lra-bad-schur-complement` | `unsat` | checked |
| `general-schur-complement-theory-lean-horizon` | `not-run` | Lean horizon |

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-schur-complement-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_schur_complement_bad_value_artifact_emits_checked_farkas
```

The replay rows recompute the Schur complement, determinant factorization,
matrix inverse, positive-definite shadow, and conditional-variance shadow over
exact rationals. The checked row parses the pack-local SMT-LIB artifact,
requires `Evidence::UnsatFarkas`, and independently checks the certificate.
