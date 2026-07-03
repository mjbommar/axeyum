# Finite Perceptron

This pack checks one finite, exact-rational perceptron training trace. It is
meant for learners, proof contributors, solver contributors, and downstream
consumers who need a small example of:

```text
training points -> dot products -> mistake updates -> converged weights -> checked rejection
```

The checked object is a fixed four-point linearly separable training set in
augmented coordinates (a constant bias component `1`), trained from the zero
weight vector with the classic perceptron rule. Both the data and the updates
are integers, so the entire trace — every dot product, mistake flag, weight
update, and final margin — replays with exact rational arithmetic. The pack
does not prove the Novikoff mistake bound, convergence for other datasets or
presentation orders, or anything about floating-point training.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `field_linear_algebra`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_perceptron_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Data

Training points in augmented coordinates `(x1, x2, 1)`:

| Point | Coordinates | Label |
|---|---|---:|
| `p1` | `(1, 2, 1)` | `+1` |
| `n1` | `(2, -1, 1)` | `-1` |
| `p2` | `(2, 3, 1)` | `+1` |
| `n2` | `(1, -2, 1)` | `-1` |

The perceptron rule: present a point `x` with label `y`; if
`y * (w . x) <= 0`, update `w <- w + y*x`, otherwise leave `w` unchanged.

The committed trace from `w = (0, 0, 0)`:

| Step | Point | Score `w . x` | `y * score` | Mistake | Weights After |
|---|---|---:|---:|---|---|
| 1 | `p1` | `0` | `0` | yes | `(1, 2, 1)` |
| 2 | `n1` | `1` | `-1` | yes | `(-1, 3, 0)` |
| 3 | `p2` | `7` | `7` | no | `(-1, 3, 0)` |
| 4 | `n2` | `-7` | `7` | no | `(-1, 3, 0)` |

The final weights `(-1, 3, 0)` classify every point with strictly positive
functional margin: `5, 5, 7, 7`. A further full pass makes no updates, so the
trace has converged after exactly two mistakes.

Functional margins `y * (w . x)` are exact integers. Geometric margins divide
by `||w|| = sqrt(10)`, which is irrational, so they stay out of scope.

## Checked Row

The malformed row claims:

```text
first weight coordinate after step 2 = 1
```

Exact replay computes `1 + (-1)*2 = -1`. The source SMT-LIB artifact isolates
the scalar contradiction:

```text
perceptron_w1 = -1
perceptron_w1 = 1
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training set and initial weights;
- exact rational replay of every dot product, mistake condition, and weight
  update in the trace;
- exact replay of the final weights, update count, and strictly positive
  functional margins;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- the Novikoff mistake bound and perceptron convergence theorems;
- geometric margins, which divide by an irrational norm;
- other presentation orders, datasets, learning rates, or initialization;
- averaged, voted, or kernel perceptron variants;
- non-separable data behavior and statistical generalization;
- floating-point dot-product and training behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-perceptron-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_perceptron_bad_weight_update_artifact_emits_checked_farkas
```
