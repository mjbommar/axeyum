# Finite Power Iteration Checks

This pack records one exact rational power-iteration transcript for
`A = diag(2, 1)`.

The checked slice is deliberately small:

- replay `A * [1, 1] = [2, 1]`;
- replay `A * [2, 1] = [4, 1]`;
- replay the finite `l1` normalization `[4, 1] / 5 = [4/5, 1/5]`;
- replay the Rayleigh quotient of `[2, 1]` as `9/5`;
- replay the residual `[2/5, -4/5]`;
- replay the exact dominant eigenpair shadow `2, [1, 0]`;
- reject the false second-iterate coordinate claim `3` after exact replay
  computes `4`;
- check the corresponding `QF_LRA` contradiction through Farkas evidence.

It does not claim convergence of power iteration, spectral-gap sufficiency,
deflation correctness, block iteration, conditioning, or floating-point
stability.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-power-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_power_iteration_bad_coordinate_artifact_emits_checked_farkas
```
