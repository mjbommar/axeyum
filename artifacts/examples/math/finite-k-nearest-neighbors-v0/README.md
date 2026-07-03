# Finite K Nearest Neighbors

This pack checks one finite, exact-rational k-nearest-neighbor classification.
It is meant for learners, proof contributors, solver contributors, and
downstream consumers who need a small example of:

```text
training points -> squared distances -> neighbor ranking -> majority vote -> checked rejection
```

The checked object is a fixed six-point two-class training set with two
rational query points and `k = 3`. All distances are *squared* Euclidean
distances, so no square root enters the arithmetic and every comparison is
exact rational replay. Both queries have a strict rank gap between the k-th
and (k+1)-th distances, so no tie-breaking policy is needed. The pack does
not prove nearest-neighbor consistency, Bayes-risk bounds, or anything about
floating-point distance computation.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `field_discrete_math`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_nearest_neighbor_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Data

Training points:

| Point | `x` | `y` | Class |
|---|---:|---:|---|
| `t1` | `0` | `0` | `positive` |
| `t2` | `1` | `0` | `positive` |
| `t3` | `0` | `1` | `positive` |
| `t4` | `4` | `4` | `negative` |
| `t5` | `5` | `4` | `negative` |
| `t6` | `4` | `5` | `negative` |

Query `q1 = (1, 1)` has squared distances `2, 1, 1, 18, 25, 25`. The three
nearest neighbors are `t1, t2, t3` (all within squared distance `2`, strictly
below the next distance `18`), and the vote is `3-0` for `positive`.

Query `q2 = (3, 3)` has squared distances `18, 13, 13, 2, 5, 5`. The three
nearest neighbors are `t4, t5, t6` (all within squared distance `5`, strictly
below the next distance `13`), and the vote is `3-0` for `negative`.

## Checked Row

The malformed row claims:

```text
squared distance from q1 to t4 = 16
```

Exact replay computes `(4-1)^2 + (4-1)^2 = 18`. The source SMT-LIB artifact
isolates the scalar contradiction:

```text
knn_distance = 18
knn_distance = 16
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed training and query coordinates;
- exact rational replay of every squared Euclidean distance;
- exact neighbor ranking with a strict gap between the k-th and (k+1)-th
  distances;
- exact majority-vote counting for the committed predictions;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- Euclidean (non-squared) distances, which require square roots;
- tie-breaking policy at the neighbor boundary and weighted voting;
- metric choice, feature scaling, and dimensionality behavior;
- cross-validated or theoretical choice of `k`;
- consistency, Bayes-risk bounds, sampling guarantees, or statistical
  generalization;
- continuous feature spaces and floating-point distance or ranking behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-k-nearest-neighbors-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_k_nearest_neighbors_bad_squared_distance_artifact_emits_checked_farkas
```
