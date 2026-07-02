# Finite Chebyshev Systems V0

This pack adds exact finite checks for the Chebyshev-system gap in the math
field spine. It uses rational sample points and small polynomial bases to
replay finite unisolvence, interpolation, and alternation-style sign evidence.

The examples are:

- a Vandermonde unisolvence witness for the basis `1, x, x^2`;
- an interpolation replay from coefficients to sample values;
- an alternating residual sign-pattern witness on three sample points;
- replay-only rejection of a degenerate duplicate-node interpolation grid;
- replay-only rejection of a false interpolation sample value;
- replay-only rejection of a false alternating-residual uniform error;
- separate QF_LRA/Farkas proof-route rows for the duplicate-node determinant,
  bad interpolation-sample, and bad alternation-magnitude conflicts;
- a general Chebyshev-space Lean-horizon row.

## Concepts

- `field_functional_analysis_and_operator_theory`
- `field_numerical_analysis`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_linear_algebra`
- `curriculum_polynomials`
- `curriculum_reals`
- `curriculum_rationals`

## Trust Story

The validator recomputes polynomial-basis evaluation matrices, exact rational
determinants, interpolation matrix-vector products, residual values, signs, and
degenerate-grid null vectors. The bad-grid row is checked by showing the
evaluation matrix has determinant zero and a nonzero coefficient vector that
vanishes on all listed sample points.

The malformed duplicate-node, interpolation-sample, and alternating-residual
rows are replay-only source checks. Separate `qf-lra-*` rows own the
proof-object path.

The duplicate-node QF_LRA row uses:
[`smt2/bad-duplicate-node-grid-farkas-conflict.smt2`](smt2/bad-duplicate-node-grid-farkas-conflict.smt2).
It isolates the final false determinant claim as `determinant = 0` and
`determinant = 1`; Axeyum emits `Evidence::UnsatFarkas`, and
`Evidence::check` independently rechecks the certificate.

The bad interpolation-sample QF_LRA row has the same route:
[`smt2/bad-interpolation-sample-farkas-conflict.smt2`](smt2/bad-interpolation-sample-farkas-conflict.smt2).
It follows exact coefficient replay for `p(1)=4` and rejects the final
malformed claim `p(1)=5` with checked Farkas evidence.

The bad alternating-residual QF_LRA row follows the finite residual replay
`1/2, -1/2, 1/2`, then checks the malformed uniform-error claim:
[`smt2/bad-alternating-residual-farkas-conflict.smt2`](smt2/bad-alternating-residual-farkas-conflict.smt2).
It isolates the final exact-linear conflict `uniform_error = 1/2` and
`uniform_error = 2/3`, and Axeyum emits checked `UnsatFarkas` evidence.

This pack is finite checked evidence. It is not a proof of general Chebyshev
systems, Haar spaces, minimax approximation, alternation theorems, compactness
arguments, or infinite-dimensional functional analysis.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_chebyshev_duplicate_node_grid_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_chebyshev_bad_interpolation_sample_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_chebyshev_bad_alternating_residual_artifact_emits_checked_farkas
```
