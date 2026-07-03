# End To End: Finite Rounding Shadow

This lesson follows one exact rational rounding-shadow resource from a tiny
addition to a checked bad equality claim. It uses the
[finite-rounding-shadow-v0](../../../artifacts/examples/math/finite-rounding-shadow-v0/)
pack.

Concept rows:

- `curriculum_rationals` and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis` and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_exact_vs_floating_arithmetic` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `exact-increment-replay` | `sat` | replay-only |
| `rounding-grid-replay` | `sat` | replay-only |
| `rounded-increment-loss-replay` | `sat` | replay-only |
| `bad-rounded-equals-exact-rejected` | `unsat` | replay-only |
| `qf-lra-bad-rounded-equals-exact` | `unsat` | checked |
| `general-floating-roundoff-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational arithmetic only. It checks a fixed three-decimal
rounding grid, not IEEE floating-point behavior.

## Replay The Exact Increment

The exact rational calculation is:

```text
x = 1
y = 1/10000

exact_sum   = x + y = 10001/10000
exact_delta = exact_sum - x = 1/10000
```

The trusted replay recomputes those two equalities directly over rational
numbers. There is no tolerance and no decimal approximation in this check.

## Replay The Rounding Grid

The rounded transcript uses a fixed three-decimal grid:

```text
decimal_places = 3
scale = 1000
```

The validator checks each rounded value by scaling to grid units and checking
that the residual is inside the nearest-grid cell:

```text
scaled_x   = 1000
scaled_y   = 1/10
scaled_sum = 10001/10

rounded_x_units   = 1000
rounded_y_units   = 0
rounded_sum_units = 1000
```

So the rounded values are:

```text
round3(x)         = 1
round3(y)         = 0
round3(exact_sum) = 1
```

The residual for `exact_sum` is `1/10`, which is strictly below `1/2`, so the
listed rounded grid unit is justified for this fixed transcript.

## Reject A Bad Exact-Vs-Rounded Claim

The rounded increment after summing is:

```text
round3(exact_sum) - round3(x) = 0
```

The exact increment is:

```text
exact_delta = 1/10000
```

The malformed row claims the two deltas are equal. The separate checked row
isolates the final contradiction as `QF_LRA`:

```text
exact_delta = 1/10000
rounded_delta = 0
exact_delta = rounded_delta
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows a numerical-analysis idea without letting
rounded arithmetic blur into proof evidence. The checked claim is only the
fixed rational addition, the fixed three-decimal rounding transcript, and the
final scalar contradiction.

Actual IEEE floating-point semantics, rounding modes, accumulation-error
theorems, and stability proofs need a separate `QF_FP`, bit-vector, or Lean
route before they can be treated as checked resources.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rounding-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_rounding_shadow_bad_rounded_delta_artifact_emits_checked_farkas
```
