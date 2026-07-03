# Finite Interval Arithmetic Shadow Checks

This pack is for learners, solver contributors, and proof-route reviewers who
need a tiny exact interval-arithmetic example. It checks one closed rational
interval product and a bad upper-bound claim. It does not prove general
interval-analysis soundness, floating-point interval arithmetic, dependency
management, or numerical stability.

The fixed input interval is:

```text
X = Y = [1, 10001/10000]
```

Exact replay computes:

```text
X + Y = [2, 10001/5000]

X * Y = [1, (10001/10000)^2]
      = [1, 100020001/100000000]
```

The useful teaching point is the small second-order term:

```text
linearized upper bound = 5001/5000
actual product upper   = 100020001/100000000
difference             = 1/100000000
```

The trusted checker recomputes:

- closed interval shape and widths;
- interval sum endpoints;
- positive interval product endpoints;
- the second-order excess over the linearized upper-bound shortcut;
- a malformed product-upper-bound claim, separately checked through
  QF_LRA/Farkas evidence.

The resource stays in exact rational arithmetic. It is not a claim about IEEE
floating-point interval packages, outward rounding, dependency blowup, or a
general interval-analysis theorem.

## Concept Rows

- `curriculum_rationals`
- `curriculum_reals`
- `field_real_analysis`
- `field_numerical_analysis`
- `bridge_rational_interval_replay`
- `bridge_exact_vs_floating_arithmetic`

## Trust Boundary

```text
untrusted fast search -> candidate interval enclosure or bad bound
trusted small checking -> exact rational interval replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-interval-arithmetic-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_interval_arithmetic_bad_product_upper_artifact_emits_checked_farkas
```
