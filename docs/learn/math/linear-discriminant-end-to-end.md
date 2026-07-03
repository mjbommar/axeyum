# Linear Discriminant End To End

This page follows `finite-linear-discriminant-v0`, a fixed exact-rational
two-class Fisher-style discriminant example. It is a statistics and
linear-algebra resource, not a claim about statistical generalization or
floating-point classifier implementations.

```text
untrusted fast search -> discriminant direction, finite threshold, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

## Source Data

The two classes are:

```text
A = [[0,0], [2,0]]
B = [[1,2], [1,4]]
```

Exact replay computes:

```text
mu_A = [1,0]
mu_B = [1,3]
mu_B - mu_A = [0,3]
```

The within-class scatter matrices are:

```text
S_A = [[2,0],[0,0]]
S_B = [[0,0],[0,2]]
S_w = [[2,0],[0,2]]
```

## Replay The Direction

The finite Fisher direction row solves:

```text
S_w w = mu_B - mu_A
[[2,0],[0,2]] * [0,3/2] = [0,3]
```

So the listed direction is:

```text
w = [0,3/2]
```

The validator also replays the fixed finite Fisher ratio:

```text
(w . (mu_B - mu_A))^2 = 81/4
w . S_w w = 9/2
ratio = 9/2
```

## Replay The Threshold

Projecting class means gives:

```text
w . mu_A = 0
w . mu_B = 9/2
threshold = 9/4
```

The four training scores are:

```text
scores(A) = [0, 0]
scores(B) = [3, 6]
```

That proves separation only for this finite listed training sample. It does
not prove future-sample accuracy, Bayes optimality, Gaussian modeling
assumptions, or any floating-point classifier behavior.

## Check The Bad Direction

The malformed row claims:

```text
wy = 1
```

Exact replay already computed `wy = 3/2`, so the replay row rejects the source
claim. The checked row isolates the same conflict as QF_LRA:

```text
2*wy = 3
wy = 1
```

The source artifact lives at:

```text
artifacts/examples/math/finite-linear-discriminant-v0/smt2/bad-fisher-direction-farkas-conflict.smt2
```

The route regression parses that artifact, emits `UnsatFarkas` evidence, and
checks it independently:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_linear_discriminant_bad_direction_artifact_emits_checked_farkas
```

## What This Does Not Prove

The pack does not prove:

- Fisher LDA optimality for arbitrary datasets;
- Gaussian class-model or equal-covariance assumptions;
- Bayes-risk or generalization guarantees;
- regularized, multiclass, or high-dimensional LDA theory;
- floating-point covariance estimates or classifier implementations.

Those belong in Lean theorem work or numerical-honesty/QF_FP resources.

## Resource Commands

Validate the pack:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-linear-discriminant-v0
```

Find the checked row through the public resource query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-linear-discriminant-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```
