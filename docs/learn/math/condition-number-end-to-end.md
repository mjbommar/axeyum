# End To End: Finite Condition Number

This lesson follows one exact condition-number resource from matrix inverse
replay to a perturbation-bound shadow and a checked bad-bound rejection. It
uses the
[finite-condition-number-v0](../../../artifacts/examples/math/finite-condition-number-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_residual_bound` and `bridge_exact_vs_floating_arithmetic` in the
  atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `matrix-inverse-replay` | `sat` | replay-only |
| `infinity-norm-replay` | `sat` | replay-only |
| `condition-number-replay` | `sat` | replay-only |
| `perturbation-bound-replay` | `sat` | replay-only |
| `bad-condition-number-rejected` | `unsat` | replay-only |
| `qf-lra-bad-condition-number` | `unsat` | checked |
| `general-conditioning-stability-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational arithmetic only. It does not certify
floating-point roundoff, backward stability, or a general perturbation theorem.

## Replay The Inverse And Norms

The source matrix is:

```text
A = [[2, 0],
     [0, 1/3]]
```

The validator checks:

```text
A^-1 = [[1/2, 0],
        [0, 3]]
A*A^-1 = I
A^-1*A = I
```

Using the infinity norm as maximum absolute row sum:

```text
||A||_infinity = 2
||A^-1||_infinity = 3
kappa_infinity(A) = 6
```

This is a small finite-dimensional operator-norm computation. The trusted work
is exact matrix multiplication and exact rational row sums.

## Replay A Perturbation Bound

The perturbation row starts from:

```text
x = [1, 1]
b = A*x = [2, 1/3]
delta_b = [0, 1/30]
```

The validator recomputes:

```text
delta_x = A^-1*delta_b = [0, 1/10]
x + delta_x = [1, 11/10]
b + delta_b = [2, 11/30]
A*(x + delta_x) = b + delta_b
```

The exact relative quantities are:

```text
||delta_b||_infinity / ||b||_infinity = 1/60
||delta_x||_infinity / ||x||_infinity = 1/10
```

So the fixed-row condition-number inequality checks:

```text
1/10 <= 6 * 1/60
```

The example intentionally saturates the bound, which makes the arithmetic easy
to audit.

## Reject A Bad Condition-Number Bound

The malformed row claims:

```text
kappa_infinity(A) <= 5
```

The trusted replay computes:

```text
kappa_infinity(A) = 6
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
kappa_infinity = 6
kappa_infinity <= 5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows how a topic that is usually taught with
floating-point intuition can be grounded as an exact finite shadow. The checked
claim is only the rational matrix, inverse, norms, perturbation response, and
final scalar contradiction. General condition-number theory, singular-value
conditioning, pseudospectra, backward stability, and IEEE floating-point error
analysis remain theorem or numerical-honesty horizons.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-condition-number-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_condition_number_bad_condition_artifact_emits_checked_farkas
```
