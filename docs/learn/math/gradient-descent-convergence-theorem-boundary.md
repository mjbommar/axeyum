# Gradient Descent Convergence Theorem Boundary

This page separates Axeyum's finite gradient-descent resource from general
gradient-descent convergence, descent-lemma, smooth-convex rate, stopping
criterion, stochastic-gradient, acceleration, and numerical-stability theorem
claims.

Primary pack:

- [finite-gradient-descent-v0](../../../artifacts/examples/math/finite-gradient-descent-v0/)

Companion lessons and maps:

- [End To End: Finite Gradient Descent Checks](finite-gradient-descent-end-to-end.md)
- [Root-Finding Convergence Theorem Boundary](root-finding-convergence-theorem-boundary.md)
- [Hyperplane Separation Theorem Boundary](hyperplane-separation-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [SDP Duality Theorem Boundary](sdp-duality-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational quadratic:

```text
f(x, y) = x^2 + 2*y^2
```

and one gradient-descent step:

```text
start point = (1, 1)
gradient    = (2, 4)
step size   = 1/4
next point  = (1/2, 0)
```

The validator checks the displayed arithmetic:

```text
Hessian              = [[2, 0], [0, 4]]
start objective      = 3
next objective       = 1/4
objective decrease   = 11/4
||gradient||^2       = 20
finite descent bound = 5/2
descent slack        = 1/4
```

Those rows check one exact rational descent step. They do not prove that
gradient descent converges, that a step-size policy is correct, or that a rate
bound holds over an arbitrary smooth convex function.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `quadratic-gradient-replay` | `sat` | replay-only | The gradient `(2,4)` and Hessian `diag(2,4)` are recomputed from the listed quadratic. |
| `gradient-descent-step-replay` | `sat` | replay-only | The exact update `(1,1) - (1/4)*(2,4) = (1/2,0)` is replayed. |
| `descent-bound-replay` | `sat` | replay-only | Objective values, decrease, gradient norm, finite descent lower bound, and positive slack are recomputed. |
| `bad-descent-value-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false decrease `2` after replay computes error `3/4`. |
| `bad-step-coordinate-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false next x-coordinate `3/4` after replay computes `1/2`. |
| `bad-descent-bound-slack-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false nonpositive slack claim after replay computes slack `1/4`. |
| `general-gradient-descent-convergence-lean-horizon` | `not-run` | lean-horizon | Smooth-convex descent lemmas, convergence, step-size conditions, stopping criteria, and rates remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
decrease error, step-coordinate value, or descent-bound slack. They are not
proofs of a convergence theorem.

## What Is Not Proved Yet

The current pack does not prove:

- convergence of gradient descent on arbitrary convex or strongly convex
  functions;
- smoothness, Lipschitz-gradient, coercivity, or bounded-level-set hypotheses;
- fixed-step, diminishing-step, Armijo, Wolfe, or exact-line-search correctness;
- sublinear, linear, or accelerated convergence rates;
- stopping criteria, stationarity guarantees, or iterate-complexity bounds;
- projected-gradient, proximal-gradient, stochastic-gradient, momentum, or
  nonconvex variants;
- floating-point stability, conditioning, roundoff, or implementation
  tolerance behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite gradient
rows are exact examples and regression seeds, not theorem evidence for the
general method.

## Query The Boundary

Find gradient-descent theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text gradient \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked decrease, coordinate, and descent-bound contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --text decrease \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --text coordinate \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --text bound \
  --require-any
```

## Graduation Criteria

General gradient-descent resources graduate only when they add:

1. precise Lean theorem statements for descent lemmas, convergence,
   fixed-step or line-search conditions, stopping criteria, or rate theorems;
2. explicit hypotheses for convexity, smoothness, Lipschitz gradients, strong
   convexity, step-size bounds, bounded sublevel sets, or stationarity targets;
3. no-`sorry` proofs with an axiom audit;
4. links from finite gradient-descent packs to theorem statements as examples,
   not as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, gradient-descent rows remain bounded/computable resources:

```text
untrusted fast search -> proposed gradient, step size, next point, bound, or malformed claim
trusted small checking -> exact gradient/step/objective/slack replay and Farkas evidence
theorem horizon       -> descent lemmas, convergence, rates, stopping criteria, variants, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gradient-descent-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text gradient --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-gradient-descent-convergence row remains `lean-horizon`.
