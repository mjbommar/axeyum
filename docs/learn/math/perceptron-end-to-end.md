# End To End: Finite Perceptron

Perceptron training is an iterative loop over a finite labeled point set:

```text
present a point -> dot product -> mistake? -> update weights -> repeat
```

This resource checks one exact-rational version of that loop: a complete
committed training trace over integer data, replayed step by step. It is not
a proof of the Novikoff mistake bound, perceptron convergence in general, or
floating-point training behavior.

## Source Data

The pack
[`finite-perceptron-v0`](../../../artifacts/examples/math/finite-perceptron-v0/README.md)
uses four points in augmented coordinates `(x1, x2, 1)` — the constant third
component folds the bias into the weight vector:

| Point | Coordinates | Label |
|---|---|---:|
| `p1` | `(1, 2, 1)` | `+1` |
| `n1` | `(2, -1, 1)` | `-1` |
| `p2` | `(2, 3, 1)` | `+1` |
| `n2` | `(1, -2, 1)` | `-1` |

## The Rule And The Trace

Present a point `x` with label `y` against the current weights `w`. If
`y * (w . x) <= 0`, the point is misclassified (or on the boundary) and the
perceptron updates `w <- w + y*x`; otherwise it leaves `w` alone.

Every coordinate here is an integer, so the whole trace is exact arithmetic —
no rounding, no tolerance. From `w = (0, 0, 0)`:

| Step | Point | Score | `y * score` | Mistake | Weights After |
|---|---|---:|---:|---|---|
| 1 | `p1` | `0` | `0` | yes | `(1, 2, 1)` |
| 2 | `n1` | `1` | `-1` | yes | `(-1, 3, 0)` |
| 3 | `p2` | `7` | `7` | no | `(-1, 3, 0)` |
| 4 | `n2` | `-7` | `7` | no | `(-1, 3, 0)` |

After two mistakes the weights are `(-1, 3, 0)`, and the final functional
margins `y * (w . x)` are:

```text
p1: 5    n1: 5    p2: 7    n2: 7
```

All strictly positive with minimum `5`, so a further full pass makes no
updates: the trace has converged.

Functional margins are exact integers. The *geometric* margin divides by
`||w|| = sqrt(10)`, which is irrational — that stays out of scope, the same
way the entropy pack excludes non-dyadic logarithms and the nearest-neighbor
pack excludes non-squared distances.

## What Axeyum Checks

The validator checks four replay rows:

- the finite training set, labels, bias components, and zero initial weights;
- every presented step: score, mistake condition, and weight update;
- the strict-margin convergence pass at the final weights;
- the final margins and the minimum margin.

Then it rejects a malformed claim:

```text
first weight coordinate after step 2 = 1
```

Exact replay computes `1 + (-1)*2 = -1`. The separate checked proof row
isolates the arithmetic contradiction:

```text
perceptron_w1 = -1
perceptron_w1 = 1
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training set and the full training trace;
- exact rational replay of every dot product, mistake flag, and update;
- exact replay of the final weights, update count, and strict margins;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- the Novikoff mistake bound `(R/gamma)^2` and convergence theorems;
- geometric margins, which involve an irrational norm;
- other presentation orders, datasets, learning rates, or initializations;
- averaged, voted, kernel, and non-separable perceptron variants;
- generalization, confidence intervals, or statistical consistency;
- floating-point dot-product and training behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-perceptron-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_perceptron_bad_weight_update_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-perceptron-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_perceptron_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text perceptron \
  --require-any
```
