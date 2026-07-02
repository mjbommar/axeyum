# KKT Sufficiency Theorem Boundary

This page separates Axeyum's finite KKT resource from general KKT necessity,
KKT sufficiency, constraint-qualification, duality, sensitivity, SDP/KKT, and
optimization-convergence theorem claims.

Primary pack:

- [finite-kkt-v0](../../../artifacts/examples/math/finite-kkt-v0/)

Companion lessons and maps:

- [End To End: Finite KKT Checks](finite-kkt-end-to-end.md)
- [Hyperplane Separation Theorem Boundary](hyperplane-separation-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one constrained rational quadratic:

```text
minimize (x - 2)^2
subject to x <= 1
candidate x = 1
multiplier lambda = 2
```

The displayed sample grid is finite:

```text
x = -1 -> f(x) = 9
x =  0 -> f(x) = 4
x =  1 -> f(x) = 1
```

The KKT witness is exact:

```text
f'(x) = 2x - 4
f'(1) = -2
constraint normal = 1
stationarity residual = -2 + 2*1 = 0
constraint value = 1 - 1 = 0
complementarity = 2 * 0 = 0
```

Those rows check the displayed finite witness. They do not prove global
optimality over every feasible point except where a future theorem supplies
the missing convexity, constraint-qualification, and sufficiency route.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `finite-quadratic-grid-minimum-replay` | `sat` | replay-only | The listed finite feasible grid has its smallest listed objective value at `x = 1`. |
| `kkt-stationarity-replay` | `sat` | replay-only | Exact differentiation and multiplier arithmetic make the stationarity residual zero. |
| `complementary-slackness-replay` | `sat` | replay-only | The active constraint and nonnegative multiplier make the complementary-slackness product zero. |
| `bad-kkt-stationarity-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false multiplier `1`, which leaves stationarity residual `-1` and error `1`. |
| `bad-kkt-complementarity-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false complementary-slackness product `1`; exact replay computes `0`. |
| `general-kkt-sufficiency-lean-horizon` | `not-run` | lean-horizon | General KKT necessity/sufficiency and constraint-qualification theorems remain future Lean work. |

The checked rows are finite exact-linear contradictions after replay computes
the offending residual or product. They are not proofs of general constrained
optimization theory.

## What Is Not Proved Yet

The current pack does not prove:

- KKT necessity for arbitrary differentiable constrained problems;
- KKT sufficiency for convex programs;
- constraint qualifications such as Slater, LICQ, MFCQ, or KKT regularity;
- global optimality beyond the displayed finite grid and fixed KKT witness;
- strong duality, sensitivity, envelope, or perturbation theorems;
- SDP/KKT specializations or semidefinite complementarity theory;
- active-set, interior-point, SQP, or first-order method convergence;
- floating-point stability, conditioning, or solver-library behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. Finite KKT rows are
examples and regression seeds, not theorem evidence for the general KKT
family.

## Query The Boundary

Find KKT theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text KKT \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --route Farkas \
  --proof-status checked \
  --text stationarity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --route Farkas \
  --proof-status checked \
  --text complementarity \
  --require-any
```

## Graduation Criteria

General KKT resources graduate only when they add:

1. precise Lean theorem statements for KKT necessity, KKT sufficiency, convex
   KKT conditions, or duality-specialized KKT corollaries;
2. explicit hypotheses for differentiability, convexity, feasibility,
   constraint qualifications, regularity, active sets, cone constraints, or
   Slater-style assumptions;
3. no-`sorry` proofs with an axiom audit;
4. links from finite KKT packs to theorem statements as examples, not as proof
   evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, KKT rows remain bounded/computable resources:

```text
untrusted fast search -> proposed active point, multiplier, residual, or malformed claim
trusted small checking -> exact derivative/replay arithmetic and Farkas evidence
theorem horizon       -> KKT necessity/sufficiency, constraint qualifications, duality, and convergence
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-kkt-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text KKT --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-kkt-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-kkt-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-kkt-sufficiency row remains `lean-horizon`.
