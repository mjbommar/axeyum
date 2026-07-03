# End To End: Finite Interval Arithmetic Shadow

This lesson follows one exact rational interval-arithmetic resource from
endpoint replay to a checked bad upper-bound claim. It uses the
[finite-interval-arithmetic-shadow-v0](../../../artifacts/examples/math/finite-interval-arithmetic-shadow-v0/)
pack.

Concept rows:

- `curriculum_rationals` and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis` and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_rational_interval_replay` and
  `bridge_exact_vs_floating_arithmetic` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `interval-shape-witness` | `sat` | replay-only |
| `interval-sum-witness` | `sat` | replay-only |
| `interval-product-witness` | `sat` | replay-only |
| `interval-width-witness` | `sat` | replay-only |
| `bad-product-upper-rejected` | `unsat` | replay-only |
| `qf-lra-bad-interval-product-upper` | `unsat` | checked |
| `general-interval-arithmetic-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational endpoint arithmetic. It does not model
floating-point outward rounding or prove a general interval-analysis theorem.

## Replay The Intervals

The fixed input intervals are:

```text
X = [1, 10001/10000]
Y = [1, 10001/10000]
```

The validator checks that both intervals are closed, nonnegative, and have
width:

```text
width(X) = width(Y) = 1/10000
```

## Replay Sum And Product

Interval addition is endpoint-wise:

```text
X + Y = [2, 10001/5000]
```

Because both intervals are nonnegative, the product enclosure is also the
endpoint product:

```text
X * Y = [1, (10001/10000)^2]
      = [1, 100020001/100000000]
```

The product width is:

```text
100020001/100000000 - 1 = 20001/100000000
```

## Reject A Bad Shortcut Bound

A first-order shortcut would stop at:

```text
1 + width(X) + width(Y) = 5001/5000
```

The exact product upper endpoint is:

```text
100020001/100000000
```

The difference is the second-order term:

```text
width(X) * width(Y) = 1/100000000
```

The malformed row claims:

```text
product_upper <= 5001/5000
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
product_upper = 100020001/100000000
product_upper <= 5001/5000
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows how interval arithmetic can be replayed
exactly for a fixed rational row while still rejecting a tempting shortcut.
The checked claim is only the listed intervals, endpoint operations, width
arithmetic, and final scalar contradiction.

General interval arithmetic, dependency management, mixed-sign multiplication,
outward rounding for floating-point endpoints, and interval-package soundness
need separate theorem, `QF_FP`, bit-vector, or numerical-honesty resources.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-interval-arithmetic-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_interval_arithmetic_bad_product_upper_artifact_emits_checked_farkas
```
