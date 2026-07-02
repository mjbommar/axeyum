# Proximal Gradient Convergence Theorem Boundary

This page separates Axeyum's finite proximal-gradient resource from general
proximal-gradient convergence, nonsmooth convex-analysis, proximal-map,
subdifferential, rate, stochastic, active-set, and numerical-stability theorem
claims.

Primary pack:

- [finite-proximal-gradient-v0](../../../artifacts/examples/math/finite-proximal-gradient-v0/)

Companion lessons and maps:

- [End To End: Finite Proximal Gradient Checks](finite-proximal-gradient-end-to-end.md)
- [Projected Gradient Convergence Theorem Boundary](projected-gradient-convergence-theorem-boundary.md)
- [Gradient Descent Convergence Theorem Boundary](gradient-descent-convergence-theorem-boundary.md)
- [Line Search Convergence Theorem Boundary](line-search-convergence-theorem-boundary.md)
- [Wolfe Line Search Theorem Boundary](wolfe-line-search-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [Active-Set Method Theorem Boundary](active-set-method-theorem-boundary.md)
- [SDP Duality Theorem Boundary](sdp-duality-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational composite objective:

```text
F(x) = f(x) + g(x)
f(x) = 1/2 * (x - 3)^2
g(x) = |x|
```

and one proximal-gradient step:

```text
start point = 0
gradient    = -3
step size   = 1/2
trial point = 3/2
prox point  = 1
```

The validator checks the displayed arithmetic:

```text
soft-threshold       = 1/2
optimality residual  = 0
start composite      = 9/2
prox composite       = 3
composite decrease   = 3/2
bad decrease error   = 1/2
```

The pack also fixes one box-plus-L1 proximal subproblem over `[0, 3/4]`:

```text
unconstrained prox point = 1
box prox point           = 3/4
box projection distance  = 1/4
upper multiplier         = 1/2
stationarity residual    = 0
```

Those rows check exact rational proximal arithmetic for one L1 example. They
do not prove proximal-map existence in general, maximal monotonicity,
subdifferential calculus, convergence of proximal gradient, or a rate theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `proximal-gradient-gradient-replay` | `sat` | replay-only | The derivative of `1/2 * (x - 3)^2` is recomputed at `x = 0`, giving `-3`. |
| `proximal-trial-step-replay` | `sat` | replay-only | The ordinary trial step `0 - (1/2) * (-3) = 3/2` is replayed. |
| `soft-threshold-prox-replay` | `sat` | replay-only | The L1 proximal map sends trial point `3/2` and threshold `1/2` to prox point `1`. |
| `composite-decrease-replay` | `sat` | replay-only | Composite values `F(0) = 9/2` and `F(1) = 3` give decrease `3/2`. |
| `box-plus-l1-prox-replay` | `sat` | replay-only | The constrained prox point clips the unconstrained point `1` to upper bound `3/4` with active multiplier `1/2`. |
| `bad-proximal-point-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects prox point `1/4` because its positive-branch optimality residual is nonzero. |
| `bad-composite-decrease-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false composite decrease `2` after replay computes decrease `3/2`. |
| `bad-box-proximal-point-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false box prox point `1` because it violates the upper bound `3/4` by `1/4`. |
| `general-proximal-gradient-convergence-lean-horizon` | `not-run` | lean-horizon | General convergence, nonsmooth convex analysis, proximal-map theory, and rates remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
proximal optimality residual, composite-decrease value, or box-bound
violation. They are not proofs of a general proximal-gradient method theorem.

## What Is Not Proved Yet

The current pack does not prove:

- existence, uniqueness, or firm nonexpansiveness of proximal maps for
  arbitrary proper closed convex functions;
- subdifferential calculus, normal-cone rules, Moreau decomposition, or
  resolvent identities;
- convergence under convexity, lower-semicontinuity, smoothness,
  Lipschitz-gradient, coercivity, or strong-convexity hypotheses;
- fixed-step, backtracking, Armijo, inertial, accelerated, or adaptive
  proximal-gradient policies;
- composite-gradient mapping stationarity or variational-inequality
  characterizations;
- sublinear, linear, accelerated, or error-bound convergence rates;
- group-lasso, constrained, active-set, stochastic, coordinate, mirror,
  primal-dual, ADMM, or nonconvex variants;
- floating-point stability, proximal-solver tolerance, roundoff, or
  implementation robustness.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
proximal-gradient rows are exact examples and regression seeds, not theorem
evidence for the general method.

## Query The Boundary

Find proximal-gradient theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text proximal-gradient \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked proximal-point, composite-decrease, and box-bound
contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text proximal \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text decrease \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text box \
  --require-any
```

## Graduation Criteria

General proximal-gradient resources graduate only when they add:

1. precise Lean theorem statements for proximal-map properties,
   subdifferential optimality, convergence, stationarity, or rate theorems;
2. explicit hypotheses for proper closed convex nonsmooth terms, smooth
   functions with Lipschitz gradients, step-size bounds, normal cones,
   constraint sets, strong convexity, or error-bound assumptions;
3. no-`sorry` proofs with an axiom audit;
4. links from finite proximal-gradient packs to theorem statements as
   examples, not as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, proximal-gradient rows remain bounded/computable resources:

```text
untrusted fast search -> proposed gradient, trial point, prox point, decrease, multiplier, or malformed claim
trusted small checking -> exact derivative/trial/prox/composite/box replay and Farkas evidence
theorem horizon       -> proximal-map theory, subdifferentials, convergence, rates, variants, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-proximal-gradient-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text proximal-gradient --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-proximal-gradient-convergence row remains `lean-horizon`.
