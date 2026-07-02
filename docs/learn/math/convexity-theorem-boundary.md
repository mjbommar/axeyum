# Convexity Theorem Boundary

This page separates Axeyum's exact finite convexity resource from general
convex-analysis, separation, duality, and convex-optimization theorem claims.

Primary pack:

- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)

Companion lessons and maps:

- [End To End: Rational Convexity](convexity-rational-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Hyperplane Separation Theorem Boundary](hyperplane-separation-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [Gradient Descent Convergence Theorem Boundary](gradient-descent-convergence-theorem-boundary.md)

## Current Finite Resource

The pack works over exact rational samples. Its midpoint Jensen witness fixes:

```text
f(x) = x^2
left = -1
right = 3
midpoint = 1
f(left) = 1
f(right) = 9
f(midpoint) = 1
(f(left) + f(right)) / 2 = 5
```

The validator checks only this finite inequality:

```text
1 <= 5
```

The finite-grid row samples the same quadratic on an equally spaced grid:

```text
x:     -2  -1   0   1   2
f(x):   4   1   0   1   4
second differences: 2, 2, 2
```

The affine-threshold row fixes one rational affine function:

```text
g(x) = 3*x - 2
threshold input = 1
threshold output = 1
sample points = 1, 3/2, 2
sample values = 1, 5/2, 4
```

All of these are finite exact-rational rows. They are useful examples and
regression seeds, but they do not prove Jensen's inequality, global convexity,
separation theorems, duality, or convergence of convex optimization methods.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `quadratic-midpoint-jensen-witness` | `sat` | replay-only | The displayed midpoint Jensen inequality for `x^2` is recomputed exactly. |
| `finite-convex-grid-second-differences` | `sat` | replay-only | The listed equally spaced finite grid has nonnegative second differences. |
| `affine-monotone-threshold-witness` | `sat` | replay-only | The displayed samples of `g(x)=3*x-2` satisfy the finite threshold implication. |
| `bad-midpoint-convexity-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false finite midpoint-convexity inequality `2*f(0) <= f(-1)+f(1)` when the values are `0,1,0`. |
| `bad-affine-threshold-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false threshold sample `x=1/2` after exact replay computes `g(1/2)=-1/2`. |
| `general-convex-analysis-lean-horizon` | `not-run` | lean-horizon | General convex analysis, duality, separation, SDP, and convergence theorems remain future proof-assistant work. |

The checked rows are small exact-linear contradictions after replay computes
the finite value or threshold shortfall. They are not proofs of convexity for
arbitrary functions or sets.

## What Is Not Proved Yet

The current pack does not prove:

- Jensen's inequality for arbitrary convex functions or arbitrary finite
  convex combinations;
- equivalence between midpoint convexity, continuity, and convexity;
- convexity over general vector spaces, normed spaces, cones, or epigraphs;
- subgradient, supporting-hyperplane, separation, or Hahn-Banach theorems;
- Farkas theorem as a general theorem, beyond individual checked certificates;
- Fenchel duality, KKT sufficiency, SDP duality, or Slater-style conditions;
- descent lemmas, first-order optimality, convergence rates, or stopping
  criteria for algorithms;
- nonsmooth, proximal, projected, stochastic, or constrained method theory;
- floating-point stability, conditioning, numerical robustness, or benchmark
  performance.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite rows can
serve as examples for those theorem routes, but they are not theorem evidence
by themselves.

## Query The Boundary

Find the convex-analysis theorem-horizon row and its finite checked shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text convex-analysis \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text midpoint \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text threshold \
  --require-any
```

## Graduation Criteria

General convex-analysis resources graduate only when they add:

1. precise Lean theorem statements for Jensen inequalities, convexity
   equivalences, separation/supporting-hyperplane theorems, convex duality,
   KKT sufficiency, SDP duality, and convex optimization convergence;
2. explicit hypotheses for domains, convex sets, convex functions, topology,
   closure, compactness, continuity, differentiability, subgradients, cones,
   constraint qualifications, and algorithm step rules;
3. no-`sorry` proofs with an axiom audit;
4. links from finite convexity packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. separate numerical-honesty metadata for floating-point, conditioning,
   tolerances, implementation behavior, or performance claims;
6. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, convexity rows remain bounded/computable resources:

```text
untrusted fast search -> proposed midpoint, grid, threshold, or malformed claim
trusted small checking -> exact rational replay and Farkas evidence
theorem horizon       -> Jensen, convexity, separation, duality, and convergence theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text convex-analysis --require-any
python3 scripts/query-foundational-resources.py checks --pack convexity-rational-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack convexity-rational-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-convex-analysis row remains `lean-horizon`.
