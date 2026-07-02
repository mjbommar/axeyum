# Checks

| Check | Expected | Evidence |
|---|---|---|
| `jordan-eigenvector-replay` | `sat` | replay-only |
| `generalized-eigenvector-replay` | `sat` | replay-only |
| `nilpotent-part-replay` | `sat` | replay-only |
| `jordan-reconstruction-replay` | `sat` | replay-only |
| `bad-jordan-chain-rejected` | `unsat` | replay-only |
| `qf-lra-bad-jordan-chain` | `unsat` | checked |
| `general-jordan-theory-lean-horizon` | `not-run` | Lean horizon |

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-jordan-chain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_jordan_chain_bad_component_artifact_emits_checked_farkas
```

The replay rows recompute the eigenvector equation, generalized-eigenvector
equation, nilpotent square, and Jordan reconstruction over exact rationals. The
checked row parses the pack-local SMT-LIB artifact, requires
`Evidence::UnsatFarkas`, and independently checks the certificate.
