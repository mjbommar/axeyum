# Finite Entropy Information Gain

This pack checks one finite, exact-rational entropy and information-gain split
calculation. It is meant for learners, proof contributors, solver
contributors, and downstream consumers who need a small example of:

```text
training table -> class counts -> dyadic entropy -> information gain -> checked rejection
```

The checked object is a fixed eight-row binary-classification table whose root
and split nodes all have class proportions in `{0, 1/2, 1}`. On those dyadic
nodes `log2` takes integer values (`log2(1) = 0`, `log2(1/2) = -1`), so every
entropy value is an exact rational number of bits and no logarithm
approximation is needed. The pack does not prove anything about entropy at
non-dyadic proportions, greedy split optimality, statistical generalization,
or floating-point logarithm behavior.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `field_discrete_math`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_entropy_information_gain_shadow`
- `bridge_finite_decision_tree_gini_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Table

| Row | `color` | `shape` | Class |
|---|---|---|---|
| `r1` | `red` | `square` | `positive` |
| `r2` | `red` | `circle` | `positive` |
| `r3` | `green` | `square` | `negative` |
| `r4` | `green` | `circle` | `negative` |
| `r5` | `blue` | `square` | `positive` |
| `r6` | `blue` | `square` | `negative` |
| `r7` | `blue` | `circle` | `positive` |
| `r8` | `blue` | `circle` | `negative` |

The root has four positive and four negative rows, so its entropy is `1` bit.

Splitting on `color` gives three children with counts `(2,0)`, `(0,2)`, and
`(2,2)`. The pure children have entropy `0`, the balanced child has entropy
`1`, so the weighted split entropy is `1/2` and the information gain is `1/2`.

Splitting on `shape` gives two children with counts `(2,2)` and `(2,2)`. Each
child has entropy `1`, so the weighted split entropy is `1` and the
information gain is `0`.

## Checked Row

The malformed row claims:

```text
color weighted entropy = 3/4
```

Exact replay computes `1/2`. The source SMT-LIB artifact isolates the scalar
contradiction:

```text
2 * entropy_color = 1
4 * entropy_color = 3
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed finite table and the dyadic-proportion
  restriction;
- exact rational replay of the root entropy and split entropies over pure or
  exactly balanced nodes;
- exact rational replay of the information gains and the selected best split;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- entropy at non-dyadic proportions, where `log2` is irrational;
- log-loss, mutual-information, or gain-ratio variants;
- greedy-tree optimality beyond the fixed candidate features;
- pruning, depth selection, feature-search policy, or tie-breaking policy;
- generalization, VC bounds, confidence intervals, sampling guarantees, or
  statistical consistency;
- continuous feature thresholds and floating-point logarithm or tree-training
  behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-entropy-information-gain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_entropy_information_gain_bad_weighted_entropy_artifact_emits_checked_farkas
```
