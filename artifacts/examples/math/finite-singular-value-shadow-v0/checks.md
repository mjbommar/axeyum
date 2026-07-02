# Checks

| Check | Expected | Evidence |
|---|---|---|
| `ata-gram-replay` | `sat` | replay-only |
| `singular-vector-replay` | `sat` | replay-only |
| `svd-reconstruction-replay` | `sat` | replay-only |
| `spectral-norm-replay` | `sat` | replay-only |
| `condition-number-two-norm-replay` | `sat` | replay-only |
| `bad-singular-value-bound-rejected` | `unsat` | replay-only |
| `qf-lra-bad-singular-value-bound` | `unsat` | checked |
| `general-svd-theory-lean-horizon` | `not-run` | Lean horizon |

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-singular-value-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_singular_value_shadow_bad_bound_artifact_emits_checked_farkas
```

The replay rows recompute all matrix products, vector products, orthogonality
facts, norms, and scalar ratios over exact rationals. The checked row parses
the pack-local SMT-LIB artifact, requires `Evidence::UnsatFarkas`, and
independently checks the certificate.
