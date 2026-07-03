# End To End: Finite Decision Tree Gini

A decision tree split starts with a finite training table:

```text
features + labels -> class counts -> Gini impurity -> split score
```

This resource checks one exact-rational version of that calculation. It is not
a proof that greedy decision-tree learning is globally optimal, statistically
consistent, or implemented correctly with floating-point arithmetic.

## Source Data

The pack
[`finite-decision-tree-gini-v0`](../../../artifacts/examples/math/finite-decision-tree-gini-v0/README.md)
uses eight classified rows:

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

There are four positive rows and four negative rows.

## Gini Impurity

For a node with `p` positives and `n` negatives:

```text
Gini(p, n) = 1 - (p / (p+n))^2 - (n / (p+n))^2
           = 2*p*n / (p+n)^2
```

The root has counts `(4,4)`, so:

```text
Gini(root) = 1/2
```

## Candidate Splits

Splitting on `color` gives:

| Child | Rows | Counts | Gini | Weighted Term |
|---|---|---:|---:|---:|
| `red` | `r1`, `r2`, `r3`, `r4` | `(3,1)` | `3/8` | `3/16` |
| `blue` | `r5`, `r6`, `r7`, `r8` | `(1,3)` | `3/8` | `3/16` |

So:

```text
weighted_color = 3/16 + 3/16 = 3/8
gain_color = 1/2 - 3/8 = 1/8
```

Splitting on `shape` gives:

| Child | Rows | Counts | Gini | Weighted Term |
|---|---|---:|---:|---:|
| `square` | `r1`, `r2`, `r5`, `r6` | `(2,2)` | `1/2` | `1/4` |
| `circle` | `r3`, `r4`, `r7`, `r8` | `(2,2)` | `1/2` | `1/4` |

So:

```text
weighted_shape = 1/2
gain_shape = 0
```

Among these two fixed candidate features, `color` is the better split.

## What Axeyum Checks

The validator checks four replay rows:

- the finite table, feature domains, and class counts;
- the root Gini impurity;
- the child impurities, weighted split impurities, and gains;
- the best split among the committed candidates.

Then it rejects a malformed claim:

```text
color weighted Gini impurity = 1/2
```

Exact replay computes `3/8`. The separate checked proof row isolates the
arithmetic contradiction:

```text
8 * gini_color = 3
2 * gini_color = 1
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed finite training table;
- exact rational replay of the Gini impurity formulas;
- exact rational comparison of the two committed candidate splits;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- greedy split optimality beyond the two committed candidates;
- tree depth, pruning, or tie-breaking policy;
- entropy or information-gain variants;
- continuous threshold search;
- missing-value or categorical-encoding policy;
- generalization, confidence intervals, or statistical consistency;
- floating-point decision-tree training behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-decision-tree-gini-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_decision_tree_gini_bad_weighted_gini_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-decision-tree-gini-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_decision_tree_gini_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text decision-tree \
  --require-any
```
