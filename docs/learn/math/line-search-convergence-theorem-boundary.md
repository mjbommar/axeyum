# Line Search Convergence Theorem Boundary

This page separates Axeyum's finite Armijo line-search resource from general
line-search termination, sufficient-decrease, Wolfe-condition, convergence-rate,
stochastic-variant, and numerical-stability theorem claims.

Primary pack:

- [finite-line-search-v0](../../../artifacts/examples/math/finite-line-search-v0/)

Companion lessons and maps:

- [End To End: Finite Line Search Checks](finite-line-search-end-to-end.md)
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

and one Armijo backtracking trace:

```text
start point      = 1
gradient         = 2
direction        = -2
directional der. = -4
Armijo c         = 1/4
initial step     = 1
accepted step    = 1/2
```

The validator checks the displayed arithmetic:

```text
initial candidate       = -1
initial objective       = 1
initial Armijo rhs      = 0
initial violation       = 1
accepted candidate      = 0
accepted objective      = 0
accepted Armijo rhs     = 1/2
accepted Armijo slack   = 1/2
```

Those rows check one exact rational line-search trace. They do not prove that
backtracking terminates on every smooth objective, that Wolfe conditions hold,
or that any descent method converges.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `descent-direction-replay` | `sat` | replay-only | The derivative and directional derivative are recomputed, giving `2 * (-2) = -4`. |
| `armijo-rejection-replay` | `sat` | replay-only | The trial step `alpha = 1` is replayed and shown to violate Armijo by `1`. |
| `armijo-acceptance-replay` | `sat` | replay-only | The backtracked step `alpha = 1/2` is replayed and shown to satisfy Armijo with slack `1/2`. |
| `bad-armijo-acceptance-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that the rejected trial step satisfies Armijo. |
| `bad-descent-direction-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false nonnegative directional-derivative claim. |
| `bad-accepted-candidate-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false accepted candidate `x = 1/4` after replay computes `x = 0`. |
| `general-line-search-convergence-lean-horizon` | `not-run` | lean-horizon | Termination, sufficient-decrease lemmas, Wolfe-condition variants, convergence, and rates remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
directional derivative, Armijo violation, or accepted candidate. They are not
proofs of line-search termination or convergence.

## What Is Not Proved Yet

The current pack does not prove:

- existence of a step satisfying Armijo for arbitrary smooth functions;
- finite termination of backtracking under Lipschitz-gradient hypotheses;
- weak or strong Wolfe condition correctness;
- global convergence of steepest descent, Newton, quasi-Newton, or nonlinear
  conjugate-gradient methods using line search;
- convergence rates, complexity bounds, or stationarity guarantees;
- stochastic, projected, proximal, constrained, or nonmonotone line-search
  variants;
- floating-point stability, tolerance policy, or implementation robustness.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
line-search rows are exact examples and regression seeds, not theorem evidence
for the general method.

## Query The Boundary

Find line-search theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text line-search \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked Armijo, direction, and candidate contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text Armijo \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text direction \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text candidate \
  --require-any
```

## Graduation Criteria

General line-search resources graduate only when they add:

1. precise Lean theorem statements for Armijo termination, sufficient-decrease
   lemmas, Wolfe-condition variants, convergence, stationarity, or rate
   theorems;
2. explicit hypotheses for smoothness, Lipschitz gradients, bounded level
   sets, descent directions, step shrinkage, curvature constants, and method
   update rules;
3. no-`sorry` proofs with an axiom audit;
4. links from finite line-search packs to theorem statements as examples, not
   as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, line-search rows remain bounded/computable resources:

```text
untrusted fast search -> proposed direction, step size, candidate, or malformed claim
trusted small checking -> exact derivative/candidate/Armijo replay and Farkas evidence
theorem horizon       -> termination, sufficient decrease, Wolfe variants, convergence, rates, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-line-search-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text line-search --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-line-search-convergence row remains `lean-horizon`.
