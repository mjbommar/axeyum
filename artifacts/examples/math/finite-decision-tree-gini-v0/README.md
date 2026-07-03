# Finite Decision Tree Gini

This pack checks one finite, exact-rational decision-tree split calculation.
It is meant for learners, proof contributors, solver contributors, and
downstream consumers who need a small example of:

```text
training table -> class counts -> Gini impurity -> split score -> checked rejection
```

The checked object is a fixed eight-row binary-classification table with two
binary features. The pack does not prove that a learned tree generalizes, that
greedy splitting is globally optimal, or that any implementation of floating
point tree training is correct.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `field_discrete_math`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_decision_tree_gini_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Table

| Row | `color` | `shape` | Class |
|---|---|---|---|
| `r1` | `red` | `square` | `positive` |
| `r2` | `red` | `square` | `positive` |
| `r3` | `red` | `circle` | `positive` |
| `r4` | `red` | `circle` | `negative` |
| `r5` | `blue` | `square` | `negative` |
| `r6` | `blue` | `square` | `negative` |
| `r7` | `blue` | `circle` | `negative` |
| `r8` | `blue` | `circle` | `positive` |

The root has four positive and four negative rows, so its Gini impurity is
`1/2`.

Splitting on `color` gives two children with counts `(3,1)` and `(1,3)`.
Each child has Gini impurity `3/8`, so the weighted split impurity is `3/8`
and the impurity gain is `1/8`.

Splitting on `shape` gives two children with counts `(2,2)` and `(2,2)`.
Each child has Gini impurity `1/2`, so the weighted split impurity is `1/2`
and the impurity gain is `0`.

## Checked Row

The malformed row claims:

```text
color weighted Gini impurity = 1/2
```

Exact replay computes `3/8`. The source SMT-LIB artifact isolates the scalar
contradiction:

```text
8 * gini_color = 3
2 * gini_color = 1
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed finite table;
- exact rational replay of the root impurity and split impurities;
- exact rational replay of the selected best split;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- greedy-tree optimality beyond the fixed candidate features;
- pruning, depth selection, feature-search policy, or tie-breaking policy;
- entropy/information-gain variants that require logarithms;
- generalization, VC bounds, confidence intervals, sampling guarantees, or
  statistical consistency;
- continuous feature thresholds and floating-point tree-training behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-decision-tree-gini-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_decision_tree_gini_bad_weighted_gini_artifact_emits_checked_farkas
```
