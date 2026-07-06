# Finite Hard-Margin SVM

This pack checks one finite, exact-rational hard-margin support-vector-machine
primal-dual pair. It is meant for learners, proof contributors, solver
contributors, and downstream consumers who need a small example of:

```text
training points -> margin constraints -> KKT multipliers -> zero duality gap -> checked rejection
```

The checked object is a fixed six-point linearly separable training set with
a committed maximum-margin hyperplane `w = (1/2, 1/2)`, `b = -1`, dual
multipliers `1/4` on the two support vectors, and a zero primal-dual
objective gap `1/4 = 1/4`. Every coordinate, weight, multiplier, margin, and
objective is rational, so the whole primal-dual pair replays with exact
arithmetic. The pack does not prove strong duality, KKT sufficiency,
maximum-margin optimality in general, or anything about floating-point
training.

## Concept Rows

- `field_statistics`
- `field_optimization_and_convexity`
- `field_linear_algebra`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_hard_margin_svm_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Data

Training points with labels:

| Point | Coordinates | Label | Multiplier |
|---|---|---:|---:|
| `s1` | `(2, 2)` | `+1` | `1/4` |
| `s2` | `(0, 0)` | `-1` | `1/4` |
| `p2` | `(3, 3)` | `+1` | `0` |
| `p3` | `(1, 4)` | `+1` | `0` |
| `n2` | `(-1, -1)` | `-1` | `0` |
| `n3` | `(0, -2)` | `-1` | `0` |

The committed hyperplane `w = (1/2, 1/2)`, `b = -1` gives functional margins
`y * (w . x + b)`:

| Point | Margin |
|---|---:|
| `s1` | `1` |
| `s2` | `1` |
| `p2` | `2` |
| `p3` | `3/2` |
| `n2` | `2` |
| `n3` | `2` |

Every margin is at least `1`, and only the support vectors `s1`, `s2` sit
exactly on the margin. The KKT identities replay exactly: stationarity
`1/4*(2,2) - 1/4*(0,0) = (1/2, 1/2)`, balance `1/4 - 1/4 = 0`, and
complementary slackness `alpha * (margin - 1) = 0` for every point. The
primal objective `(1/2)*||w||^2 = 1/4` equals the dual objective
`sum(alpha) - (1/2)*||w||^2 = 1/4`, so the committed pair has zero duality
gap.

Functional margins and squared norms are exact rationals. The geometric
margin `1/||w|| = sqrt(2)` is irrational, so it stays out of scope.

## Checked Row

The malformed row claims:

```text
maximum-margin bias = -1/2
```

Exact replay of the support-vector margin equalities at `w = (1/2, 1/2)`
computes `b = -1`. The source SMT-LIB artifact isolates the scalar
contradiction:

```text
svm_b = -1
svm_b = -1/2
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training set, hyperplane, and multipliers;
- exact rational replay of every functional margin and the hard-margin
  feasibility constraints;
- exact replay of the KKT stationarity, balance, and complementary-slackness
  identities and the zero primal-dual gap;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- strong duality and KKT sufficiency theorems for the SVM quadratic program;
- maximum-margin optimality and uniqueness in general;
- geometric margins, which divide by an irrational norm;
- soft-margin/hinge-loss, kernel, and non-separable variants;
- SMO/working-set solver behavior and statistical generalization;
- floating-point dot-product and training behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hard-margin-svm-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_hard_margin_svm_bad_bias_artifact_emits_checked_farkas
```
