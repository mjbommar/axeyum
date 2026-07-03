# Checks

## `class-mean-witness`

Recomputes `mu_A = [1,0]` and `mu_B = [1,3]` from the two finite class tables.

Proof route: exact rational finite replay.

## `within-scatter-witness`

Recomputes centered rows, class scatter matrices, and the total within-class
scatter matrix:

```text
S_w = [[2,0],[0,2]]
```

Proof route: exact rational finite replay.

## `fisher-direction-witness`

Checks that the listed direction satisfies the fixed normal equation:

```text
S_w * [0, 3/2] = [0, 3] = mu_B - mu_A
```

It also replays the finite Fisher ratio `9/2`.

Proof route: exact rational finite replay.

## `finite-threshold-classification-witness`

Projects every training row onto the Fisher direction and checks the midpoint
threshold `9/4`. The two class-A scores are below the threshold and the two
class-B scores are above it, with minimum margin `3/4`.

Proof route: exact rational finite replay. This is a finite training-set
separation check, not a generalization or Bayes-optimality theorem.

## `bad-fisher-direction-rejected`

Rejects the malformed claim that the Fisher direction has `wy = 1`. Exact
replay computes `wy = 3/2`.

Proof route: replay-only. The next row owns the checked certificate.

## `qf-lra-bad-fisher-direction`

The resource-backed Axeyum regression parses:

```text
artifacts/examples/math/finite-linear-discriminant-v0/smt2/bad-fisher-direction-farkas-conflict.smt2
```

and checks the exact rational conflict:

```text
2*wy = 3
wy = 1
```

Proof route: checked QF_LRA/Farkas.

## `general-linear-discriminant-theory-lean-horizon`

General Fisher LDA optimality, Gaussian generative assumptions, Bayes-risk
claims, regularized and multiclass variants, statistical generalization,
floating-point covariance estimates, and numerical classifier implementations
need future theorem or numerical-honesty artifacts.
