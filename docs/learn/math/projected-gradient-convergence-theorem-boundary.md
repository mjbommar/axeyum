# Projected Gradient Convergence Theorem Boundary

This page separates Axeyum's finite projected-gradient resource from general
projected-gradient convergence, projection theorem, variational-inequality,
rate, proximal, stochastic, active-set, and numerical-stability theorem
claims.

Primary pack:

- [finite-projected-gradient-v0](../../../artifacts/examples/math/finite-projected-gradient-v0/)

Companion lessons and maps:

- [End To End: Finite Projected Gradient Checks](finite-projected-gradient-end-to-end.md)
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

The pack fixes one exact rational quadratic and one interval constraint:

```text
f(x) = (x - 2)^2
C = [0, 1]
```

and one projected-gradient step:

```text
start point       = 0
gradient          = -4
step size         = 1/2
unconstrained x   = 2
projected x       = 1
```

The validator checks the displayed arithmetic:

```text
projection distance = 1
start objective     = 4
projected objective = 1
projected decrease  = 3
bad point violation = 1/2
bad decrease error  = 1
```

Those rows check one exact rational interval projection and objective
decrease. They do not prove projection existence for arbitrary closed convex
sets, nonexpansiveness of projection, convergence of projected gradient, or a
rate theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `projected-gradient-gradient-replay` | `sat` | replay-only | The derivative of `(x - 2)^2` is recomputed at `x = 0`, giving `-4`. |
| `unconstrained-step-replay` | `sat` | replay-only | The exact trial step `0 - (1/2) * (-4) = 2` is replayed. |
| `interval-projection-replay` | `sat` | replay-only | The trial point `2` is clamped to the interval endpoint `1`, with distance `1`. |
| `projected-descent-replay` | `sat` | replay-only | Objective values `f(0) = 4` and `f(1) = 1` give projected decrease `3`. |
| `bad-projected-point-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false projected point `3/2` because it violates the interval upper bound by `1/2`. |
| `bad-projected-decrease-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false decrease `4` after replay computes decrease `3`. |
| `general-projected-gradient-convergence-lean-horizon` | `not-run` | lean-horizon | General convergence, constraint qualifications, projection theory, and rates remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
projection boundary or projected-decrease value. They are not proofs of a
general projected-gradient method theorem.

## What Is Not Proved Yet

The current pack does not prove:

- existence and uniqueness of projections onto arbitrary closed convex sets;
- projection optimality, nonexpansiveness, or firm nonexpansiveness;
- variational-inequality or fixed-point characterizations of projected
  gradient;
- convergence under convexity, smoothness, Lipschitz-gradient, or
  strong-convexity hypotheses;
- constant-step, diminishing-step, Armijo, Wolfe, or exact-line-search
  projected-gradient policies;
- active-set identification, constraint qualifications, normal-cone
  conditions, or KKT sufficiency for projected iterates;
- sublinear, linear, or accelerated convergence rates;
- proximal-gradient, stochastic-gradient, coordinate, mirror-descent, or
  nonconvex variants;
- floating-point stability, projection tolerance, roundoff, or implementation
  robustness.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
projected-gradient rows are exact examples and regression seeds, not theorem
evidence for the general method.

## Query The Boundary

Find projected-gradient theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text projected-gradient \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked projection and decrease contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text projection \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text decrease \
  --require-any
```

## Graduation Criteria

General projected-gradient resources graduate only when they add:

1. precise Lean theorem statements for projection properties, fixed-point or
   variational-inequality characterizations, convergence, stationarity, or
   rate theorems;
2. explicit hypotheses for closed convex feasible sets, smoothness,
   Lipschitz gradients, strong convexity, step-size bounds, normal cones,
   active sets, or constraint qualifications;
3. no-`sorry` proofs with an axiom audit;
4. links from finite projected-gradient packs to theorem statements as
   examples, not as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, projected-gradient rows remain bounded/computable resources:

```text
untrusted fast search -> proposed gradient, trial point, projection, decrease, or malformed claim
trusted small checking -> exact derivative/trial/projection/objective replay and Farkas evidence
theorem horizon       -> projection theory, convergence, rates, active sets, variants, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-projected-gradient-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text projected-gradient --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-projected-gradient-convergence row remains `lean-horizon`.
