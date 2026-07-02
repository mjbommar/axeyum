# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `hadamard-orthogonality-witness` | `sat` | replay-only | Recompute `H^T H` and check it equals `4I`. |
| `walsh-transform-witness` | `sat` | replay-only | Recompute `Hx` and check the listed transform coefficients. |
| `inverse-transform-witness` | `sat` | replay-only | Recompute `H y / 4` and check it reconstructs `x`. |
| `parseval-energy-witness` | `sat` | replay-only | Recompute both squared norms and check `||y||^2 = 4 ||x||^2`. |
| `bad-transform-coefficient-rejected` | `unsat` | replay-only | Recompute the second coefficient as `-2` and reject the malformed `-1` claim. |
| `qf-lra-bad-transform-coefficient` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-walsh-hadamard-theorem-lean-horizon` | `not-run` | lean-horizon | General orthogonal-transform facts, fast algorithms, numerical stability, and Fourier-analysis results need theorem-prover artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-walsh-hadamard-transform-v0/smt2/bad-transform-coefficient-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_walsh_hadamard_bad_transform_coefficient_artifact_emits_checked_farkas
```
