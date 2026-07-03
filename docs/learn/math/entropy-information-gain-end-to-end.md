# End To End: Finite Entropy Information Gain

An entropy-based decision-tree split starts with a finite training table:

```text
features + labels -> class counts -> entropy -> information gain
```

This resource checks one exact-rational version of that calculation by
restricting every node to dyadic class proportions, where the logarithm is
exact. It is not a proof about entropy at general proportions, greedy
information-gain optimality, statistical consistency, or floating-point
logarithm behavior.

## Source Data

The pack
[`finite-entropy-information-gain-v0`](../../../artifacts/examples/math/finite-entropy-information-gain-v0/README.md)
uses eight classified rows:

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

There are four positive rows and four negative rows.

## Why Dyadic Proportions

For a node with `p` positives and `n` negatives, the binary entropy in bits
is:

```text
H(p, n) = -(p/(p+n))*log2(p/(p+n)) - (n/(p+n))*log2(n/(p+n))
```

with `0 * log2(0) = 0`. In general `log2` is irrational — `H(3,1)` already
involves `log2(3)` — so a generic entropy table cannot be replayed with exact
rational arithmetic. This pack commits only nodes whose class proportion is
`0`, `1/2`, or `1`:

```text
H(pure node)     = 0    because log2(1)   =  0
H(balanced node) = 1    because log2(1/2) = -1
```

Every entropy in the pack is therefore an exact rational number of bits, and
the validator rejects any table that breaks the restriction. Entropy at
non-dyadic proportions stays on the Lean horizon.

## Candidate Splits

The root has counts `(4,4)`, so `H(root) = 1`.

Splitting on `color` gives:

| Child | Rows | Counts | Entropy | Weighted Term |
|---|---|---:|---:|---:|
| `red` | `r1`, `r2` | `(2,0)` | `0` | `0` |
| `green` | `r3`, `r4` | `(0,2)` | `0` | `0` |
| `blue` | `r5`, `r6`, `r7`, `r8` | `(2,2)` | `1` | `1/2` |

So:

```text
weighted_color = 0 + 0 + 1/2 = 1/2
gain_color = 1 - 1/2 = 1/2
```

Splitting on `shape` gives:

| Child | Rows | Counts | Entropy | Weighted Term |
|---|---|---:|---:|---:|
| `square` | `r1`, `r3`, `r5`, `r6` | `(2,2)` | `1` | `1/2` |
| `circle` | `r2`, `r4`, `r7`, `r8` | `(2,2)` | `1` | `1/2` |

So:

```text
weighted_shape = 1
gain_shape = 0
```

Among these two fixed candidate features, `color` is the better split.

## What Axeyum Checks

The validator checks four replay rows:

- the finite table, feature domains, class counts, and the dyadic-proportion
  restriction;
- the root entropy;
- the child entropies, weighted split entropies, and information gains;
- the best split among the committed candidates.

Then it rejects a malformed claim:

```text
color weighted entropy = 3/4
```

Exact replay computes `1/2`. The separate checked proof row isolates the
arithmetic contradiction:

```text
2 * entropy_color = 1
4 * entropy_color = 3
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed finite training table and its dyadic
  restriction;
- exact rational replay of the entropy values over pure or exactly balanced
  nodes;
- exact rational comparison of the two committed candidate splits;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- entropy at non-dyadic proportions, where `log2` is irrational;
- log-loss, mutual-information, or gain-ratio split criteria;
- greedy split optimality beyond the two committed candidates;
- tree depth, pruning, or tie-breaking policy;
- continuous threshold search;
- missing-value or categorical-encoding policy;
- generalization, confidence intervals, or statistical consistency;
- floating-point logarithm and decision-tree training behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-entropy-information-gain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_entropy_information_gain_bad_weighted_entropy_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-entropy-information-gain-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_entropy_information_gain_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text entropy \
  --require-any
```
