# End To End: Finite Hard-Margin SVM

The hard-margin support vector machine is a convex quadratic program over a
finite labeled point set:

```text
minimize (1/2)*||w||^2   subject to   y * (w . x + b) >= 1 for every point
```

This resource checks one exact-rational primal-dual pair for that program: a
committed hyperplane, its dual multipliers, every margin constraint, the KKT
identities, and a zero duality gap, replayed over exact rationals. It is not
a proof of strong duality, KKT sufficiency, maximum-margin optimality in
general, or floating-point training behavior.

## Source Data

The pack
[`finite-hard-margin-svm-v0`](../../../artifacts/examples/math/finite-hard-margin-svm-v0/README.md)
uses six points with the committed hyperplane `w = (1/2, 1/2)`, `b = -1`:

| Point | Coordinates | Label | Multiplier |
|---|---|---:|---:|
| `s1` | `(2, 2)` | `+1` | `1/4` |
| `s2` | `(0, 0)` | `-1` | `1/4` |
| `p2` | `(3, 3)` | `+1` | `0` |
| `p3` | `(1, 4)` | `+1` | `0` |
| `n2` | `(-1, -1)` | `-1` | `0` |
| `n3` | `(0, -2)` | `-1` | `0` |

## Margins, KKT, And The Zero Gap

Every coordinate, weight, and multiplier is rational, so the whole
primal-dual pair is exact arithmetic — no rounding, no tolerance. The
functional margins `y * (w . x + b)` are:

```text
s1: 1    s2: 1    p2: 2    p3: 3/2    n2: 2    n3: 2
```

All constraints hold with minimum margin `1`, and exactly the two support
vectors `s1`, `s2` sit on the margin. The KKT identities replay exactly:

```text
stationarity: 1/4*(2, 2) - 1/4*(0, 0) = (1/2, 1/2) = w
balance:      1/4 - 1/4 = 0
slackness:    alpha * (margin - 1) = 0 for every point
```

The primal objective `(1/2)*||w||^2 = 1/4` equals the dual objective
`sum(alpha) - (1/2)*||sum(alpha*y*x)||^2 = 1/2 - 1/4 = 1/4`, so the committed
pair has zero duality gap. The zero gap is replayed as committed data; the
strong-duality and KKT-sufficiency theorems that turn a zero gap into an
optimality proof stay in the horizon row.

Functional margins and squared norms are exact rationals. The *geometric*
margin `1/||w|| = sqrt(2)` is irrational — that stays out of scope, the same
way the perceptron pack excludes geometric margins and the nearest-neighbor
pack excludes non-squared distances.

## What Axeyum Checks

The validator checks four replay rows:

- the finite training set, labels, classes, and the committed hyperplane;
- every functional margin, the hard-margin feasibility constraints, and the
  support-vector margin equalities;
- the KKT stationarity, multiplier-balance, and complementary-slackness
  identities;
- the squared norm, the primal and dual objectives, and the zero gap.

Then it rejects a malformed claim:

```text
maximum-margin bias = -1/2
```

Exact replay of the support-vector margin equalities at `w = (1/2, 1/2)`
computes `b = -1`. The separate checked proof row isolates the arithmetic
contradiction:

```text
svm_b = -1
svm_b = -1/2
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training set, hyperplane, and multipliers;
- exact rational replay of every functional margin and feasibility
  constraint;
- exact replay of the KKT identities and the zero primal-dual gap;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- strong duality and KKT sufficiency for the SVM quadratic program;
- maximum-margin optimality and uniqueness in general;
- geometric margins, which involve an irrational norm;
- soft-margin/hinge-loss, kernel, and non-separable variants;
- SMO/working-set solver behavior, generalization, or margin bounds;
- floating-point dot-product, kernel-evaluation, and training behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hard-margin-svm-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_hard_margin_svm_bad_bias_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hard-margin-svm-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_hard_margin_svm_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text svm \
  --require-any
```
