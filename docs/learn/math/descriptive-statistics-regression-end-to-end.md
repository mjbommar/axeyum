# End To End: Descriptive Statistics And Regression

This lesson follows two exact finite statistics resources from mean/variance
and count-table replay to least-squares normal equations, residual
orthogonality, and checked bad regression coefficients. It uses
[descriptive-statistics-v0](../../../artifacts/examples/math/descriptive-statistics-v0/)
and
[least-squares-regression-v0](../../../artifacts/examples/math/least-squares-regression-v0/).

Concept rows:

- `curriculum_rationals`, `curriculum_counting`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_statistics`, `field_probability_theory`, `field_linear_algebra`,
  and `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `mean-variance-identity` | `sat` | replay-only |
| `contingency-table-margins` | `sat` | replay-only |
| `qf-lia-bad-contingency-total` | `unsat` | checked |
| `simpson-paradox-witness` | `sat` | replay-only |
| `perfect-line-normal-equations` | `sat` | replay-only |
| `least-squares-residual-orthogonality` | `sat` | replay-only |
| `mean-baseline-rss-comparison` | `sat` | replay-only |
| `bad-regression-coefficients-rejected` | `unsat` | checked |
| `general-regression-statistics-lean-horizon` | `not-run` | lean-horizon |

These rows use finite data, integer count tables, and exact rational matrix
arithmetic. They do not claim statistical inference, floating-point estimation,
confidence intervals, or asymptotic regression theory.

## Replay Mean And Variance

The finite sample is:

```text
1, 2, 3, 4
```

The validator recomputes:

```text
mean = (1 + 2 + 3 + 4) / 4 = 5/2
second moment = (1^2 + 2^2 + 3^2 + 4^2) / 4 = 15/2
population variance = 15/2 - (5/2)^2 = 5/4
```

This is exact rational replay of a fixed finite sample.

## Replay Count-Table Margins

The contingency table is:

```text
[[8, 2],
 [1, 9]]
```

The validator recomputes:

```text
row sums = 10, 10
column sums = 9, 11
total = 20
```

This is integer table arithmetic, not a statistical significance claim.

## Check The Bad Total Certificate

The solver-form row isolates a false margin claim for the same table. The row
sums force:

```text
total = 10 + 10 = 20
```

The bad claim requires:

```text
total = 19
```

Axeyum emits an `UnsatDiophantine` certificate for the inconsistent integer
equalities and checks it independently. The positive table row remains finite
replay; this negative row is the first checked QF_LIA margin/count certificate
for descriptive statistics.

## Replay Simpson's Paradox

The two-stratum count table records:

```text
small: A = 81/87,  B = 234/270
large: A = 192/263, B = 55/80
```

The validator checks the within-stratum comparisons by cross-multiplication:

```text
81*270 > 234*87
192*80 > 55*263
```

So `A` wins within both strata. Aggregating the counts gives:

```text
A = (81 + 192) / (87 + 263) = 273/350
B = (234 + 55) / (270 + 80) = 289/350
```

The aggregate winner is `B`. The row is a finite count-table witness for
Simpson's paradox.

## Replay Perfect-Line Normal Equations

The perfect-line regression sample uses:

```text
X = [[1,0],
     [1,1],
     [1,2]]
y = [1,3,5]
beta = [1,2]
```

The validator recomputes:

```text
X*beta = [1,3,5]
residuals = [0,0,0]
X^T*X = [[3,3],
         [3,5]]
X^T*y = [9,13]
(X^T*X)*beta = [9,13]
```

That checks the normal equations for an exact affine fit.

## Replay Least-Squares Projection

The non-perfect sample keeps the same design matrix but uses:

```text
y = [1,2,4]
beta = [5/6, 3/2]
```

The validator checks:

```text
fitted = [5/6, 7/3, 23/6]
residuals = [1/6, -1/3, 1/6]
X^T*residuals = [0,0]
RSS = 1/6
```

Orthogonality to the columns of `X` is the finite linear-algebra certificate
for this least-squares projection.

## Compare To The Mean Baseline

The mean-only baseline for `y = [1,2,4]` uses:

```text
mean = 7/3
baseline residuals = [-4/3, -1/3, 5/3]
baseline RSS = 14/3
model RSS = 1/6
RSS improvement = 9/2
```

The validator recomputes both residual-sum-of-squares values exactly.

## Reject Bad Coefficients

The bad row claims that:

```text
beta = [1,1]
```

solves the non-perfect least-squares problem. The validator recomputes:

```text
claimed fitted = [1,2,3]
claimed residuals = [0,0,1]
X^T*y - X^T*X*beta = [1,2]
```

The normal-equation residual is nonzero, so the coefficient claim is checked
`unsat`.

The resource regression checks the first failed normal equation as `QF_LRA`:

```text
beta0 = 1
beta1 = 1
3*beta0 + 3*beta1 = 7
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Name The Horizon

The packs do not claim broad statistical theory:

```text
sampling distributions
confidence intervals
Gauss-Markov theorem
model selection
regularization paths
floating-point regression implementations
asymptotic consistency
```

Those require Lean-backed probability/statistics resources or explicit
numerical-honesty metadata. These packs only check finite exact-rational data
and matrix obligations.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/least-squares-regression-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current exact statistics/regression resource
pattern:

```text
untrusted fast search -> statistic, table, coefficient, or counterexample row
trusted small checking -> exact rational arithmetic, count tables, matrix replay, Diophantine certificates, and Farkas certificates
remaining horizon -> inference, asymptotics, floating point, and model theory
```

The graduation route is deterministic finite replay plus checked proof objects
for false coefficient or table claims before inference or numerical regression
claims are promoted.
