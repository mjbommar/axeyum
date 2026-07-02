# Wolfe Line Search Theorem Boundary

This page separates Axeyum's finite Wolfe line-search resource from general
Wolfe and strong-Wolfe existence, descent, convergence, rate, stochastic, and
numerical-stability theorem claims.

Primary pack:

- [finite-wolfe-line-search-v0](../../../artifacts/examples/math/finite-wolfe-line-search-v0/)

Companion lessons and maps:

- [End To End: Finite Wolfe Line Search Checks](finite-wolfe-line-search-end-to-end.md)
- [Line Search Convergence Theorem Boundary](line-search-convergence-theorem-boundary.md)
- [Gradient Descent Convergence Theorem Boundary](gradient-descent-convergence-theorem-boundary.md)
- [Root-Finding Convergence Theorem Boundary](root-finding-convergence-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [SDP Duality Theorem Boundary](sdp-duality-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational quadratic:

```text
f(x) = x^2
```

and one Wolfe line-search witness:

```text
start point       = 1
gradient          = 2
direction         = -2
phi'(0)           = -4
Wolfe c1          = 1/4
Wolfe c2          = 1/2
accepted step     = 1/2
accepted point    = 0
```

The validator checks the displayed arithmetic:

```text
accepted value                 = 0
accepted gradient              = 0
accepted directional der.      = 0
sufficient-decrease rhs        = 1/2
sufficient-decrease slack      = 1/2
curvature bound                = 2
curvature slack                = 2
bad full-step curvature gap    = 2
```

Those rows check one exact rational Wolfe instance. They do not prove Wolfe
step existence for arbitrary objectives, strong-Wolfe variants, Zoutendijk
convergence, rate theorems, or numerical behavior.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `wolfe-descent-direction-replay` | `sat` | replay-only | The derivative and directional derivative are recomputed, giving `2 * (-2) = -4`. |
| `exact-line-minimizer-replay` | `sat` | replay-only | The exact line minimizer is replayed as `alpha = 1/2`, `x = 0`, and `phi'(1/2) = 0`. |
| `wolfe-sufficient-decrease-replay` | `sat` | replay-only | The accepted step satisfies sufficient decrease with slack `1/2`. |
| `wolfe-curvature-replay` | `sat` | replay-only | The accepted step satisfies the Wolfe curvature bound with slack `2`. |
| `bad-line-minimizer-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false exact-minimizer claim `alpha = 1`, `x = -1`. |
| `bad-wolfe-sufficient-decrease-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false nonpositive sufficient-decrease slack claim. |
| `bad-wolfe-curvature-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that the full step satisfies the curvature bound. |
| `general-wolfe-line-search-lean-horizon` | `not-run` | lean-horizon | Wolfe existence, strong-Wolfe variants, Zoutendijk-style convergence, and rate theorems remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a line
minimizer, sufficient-decrease slack, or curvature violation. They are not
proofs of Wolfe line-search existence or convergence.

## What Is Not Proved Yet

The current pack does not prove:

- existence of a Wolfe or strong-Wolfe step for arbitrary smooth functions;
- bracketing, zoom, interpolation, or line-search algorithm termination;
- Zoutendijk-style convergence theorems;
- global convergence of steepest descent, Newton, quasi-Newton, or nonlinear
  conjugate-gradient methods using Wolfe search;
- convergence rates, complexity bounds, or stationarity guarantees;
- nonconvex, stochastic, constrained, projected, or proximal Wolfe variants;
- floating-point stability, tolerance policy, interpolation robustness, or
  implementation-level safeguards.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite Wolfe
rows are exact examples and regression seeds, not theorem evidence for the
general method.

## Query The Boundary

Find Wolfe theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "Wolfe line-search" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked minimizer, sufficient-decrease, and curvature
contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text minimizer \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text sufficient-decrease \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text curvature \
  --require-any
```

## Graduation Criteria

General Wolfe resources graduate only when they add:

1. precise Lean theorem statements for Wolfe existence, strong-Wolfe existence,
   descent lemmas, Zoutendijk convergence, stationarity, or rate theorems;
2. explicit hypotheses for smoothness, Lipschitz gradients, bounded level
   sets, descent directions, curvature constants, step bracketing, and method
   update rules;
3. no-`sorry` proofs with an axiom audit;
4. links from finite Wolfe packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, Wolfe rows remain bounded/computable resources:

```text
untrusted fast search -> proposed step, minimizer, Wolfe slack, curvature value, or malformed claim
trusted small checking -> exact derivative/minimizer/Wolfe replay and Farkas evidence
theorem horizon       -> Wolfe existence, strong Wolfe, Zoutendijk convergence, rates, variants, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-wolfe-line-search-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "Wolfe line-search" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-wolfe-line-search row remains `lean-horizon`.
