# End To End: Finite Ridge Regression

This lesson follows
[finite-ridge-regression-v0](../../../artifacts/examples/math/finite-ridge-regression-v0/)
through exact rational regularized normal equations, replayed residual and
penalty arithmetic, a checked bad coefficient row, and the theorem/numerical
horizon around general ridge regression.

Concept rows:

- `curriculum_rationals`, `curriculum_reals`, and `curriculum_linear_algebra`
  in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_statistics`, `field_linear_algebra`, `field_optimization_and_convexity`,
  and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_residual_bound`, `bridge_inner_product_projection`, and
  `bridge_exact_vs_floating_arithmetic`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `ridge-normal-equations-witness` | `sat` | replay-only |
| `ridge-shrinkage-witness` | `sat` | replay-only |
| `ridge-objective-comparison-witness` | `sat` | replay-only |
| `bad-ridge-beta0-rejected` | `unsat` | replay-only |
| `qf-lra-bad-ridge-beta0` | `unsat` | checked |
| `general-ridge-regression-theory-lean-horizon` | `not-run` | lean-horizon |

These rows use one finite exact rational dataset. They do not claim statistical
inference, cross-validation, floating-point solver correctness, or general
regularization theory.

## Replay The Regularized Normal Equations

The fixed data is:

```text
X = [[1,0],
     [1,1],
     [1,2]]
y = [1,2,4]
lambda = 1
```

The validator recomputes:

```text
X^T X = [[3,3],
         [3,5]]
X^T y = [7,10]
X^T X + I = [[4,3],
             [3,6]]
```

The exact ridge coefficients are:

```text
beta = [4/5, 19/15]
```

and they satisfy:

```text
4*beta0 + 3*beta1 = 7
3*beta0 + 6*beta1 = 10
```

This is exact finite matrix replay.

## Replay Residuals And Penalty

The validator recomputes:

```text
fitted = [4/5, 31/15, 10/3]
residuals = [1/5, -1/15, 2/3]
RSS = 22/45
||beta||^2 = 101/45
ridge objective = 41/15
```

The ordinary least-squares coefficients for the same sample are `[5/6, 3/2]`.
Under the ridge objective, those coefficients have objective `28/9`, so this
fixed ridge row improves the regularized objective by `17/45`.

## Reject The Bad Coefficient

The bad replay row claims:

```text
beta0 = 1
```

Exact replay has already computed `beta0 = 4/5`, so the replay row rejects the
malformed coefficient.

The checked QF_LRA row keeps only the final linear conflict:

```text
4*beta0 + 3*beta1 = 7
3*beta0 + 6*beta1 = 10
beta0 = 1
```

Axeyum emits `UnsatFarkas` evidence for this source SMT-LIB artifact and checks
the certificate independently.

## Boundary

This pack proves nothing about arbitrary ridge regression. General existence,
uniqueness, shrinkage theorems, bias/variance tradeoffs, regularization paths,
rank-deficient design matrices, cross-validation, and floating-point solvers
belong in future Lean or numerical-honesty resources.
