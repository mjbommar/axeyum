# End To End: Finite K Nearest Neighbors

A k-nearest-neighbor classification starts with a finite labeled point set:

```text
training points -> distances -> neighbor ranking -> majority vote
```

This resource checks one exact-rational version of that calculation by
working entirely with *squared* Euclidean distances, so no square root enters
the arithmetic. It is not a proof about nearest-neighbor consistency,
Bayes-risk bounds, or floating-point distance computation.

## Source Data

The pack
[`finite-k-nearest-neighbors-v0`](../../../artifacts/examples/math/finite-k-nearest-neighbors-v0/README.md)
uses six labeled points and `k = 3`:

| Point | `x` | `y` | Class |
|---|---:|---:|---|
| `t1` | `0` | `0` | `positive` |
| `t2` | `1` | `0` | `positive` |
| `t3` | `0` | `1` | `positive` |
| `t4` | `4` | `4` | `negative` |
| `t5` | `5` | `4` | `negative` |
| `t6` | `4` | `5` | `negative` |

## Why Squared Distances

The Euclidean distance `sqrt((qx-tx)^2 + (qy-ty)^2)` is irrational in
general, so a generic distance table cannot be replayed with exact rational
arithmetic. Squaring removes the root, and because squaring is monotone on
nonnegative values, ranking by squared distance selects exactly the same
neighbors. Every value in the pack is therefore an exact rational, and the
comparison logic is pure rational arithmetic.

## Queries

Query `q1 = (1, 1)`:

| Point | Squared Distance |
|---|---:|
| `t1` | `2` |
| `t2` | `1` |
| `t3` | `1` |
| `t4` | `18` |
| `t5` | `25` |
| `t6` | `25` |

The three nearest neighbors are `t1, t2, t3`. The largest neighbor distance
`2` is strictly below the smallest non-neighbor distance `18`, so the
neighbor set needs no tie-breaking policy. The vote is `3-0` and the
prediction is `positive`.

Query `q2 = (3, 3)` has squared distances `18, 13, 13, 2, 5, 5`, neighbors
`t4, t5, t6` (gap `5 < 13`), vote `3-0`, prediction `negative`.

## What Axeyum Checks

The validator checks four replay rows:

- the finite training set, query points, and `k`;
- every squared Euclidean distance;
- the neighbor sets and their strict rank gaps;
- the vote counts and strict-majority predictions.

Then it rejects a malformed claim:

```text
squared distance from q1 to t4 = 16
```

Exact replay computes `(4-1)^2 + (4-1)^2 = 18`. The separate checked proof
row isolates the arithmetic contradiction:

```text
knn_distance = 18
knn_distance = 16
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training and query coordinates;
- exact rational replay of every squared distance;
- exact neighbor ranking with strict rank gaps;
- exact majority-vote counting;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- Euclidean (non-squared) distances, which require square roots;
- boundary tie-breaking, weighted voting, and metric or scaling policy;
- cross-validated or theoretical choice of `k`;
- nearest-neighbor consistency, Bayes-risk bounds, and
  curse-of-dimensionality behavior;
- generalization, confidence intervals, or statistical consistency;
- floating-point distance and ranking behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-k-nearest-neighbors-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_k_nearest_neighbors_bad_squared_distance_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-k-nearest-neighbors-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_nearest_neighbor_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text neighbor \
  --require-any
```
