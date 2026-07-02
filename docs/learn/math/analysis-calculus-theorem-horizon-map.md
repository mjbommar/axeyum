# Analysis And Calculus Theorem Horizon Map

This map is for learners, proof contributors, and solver contributors who need
to know what the analysis-adjacent resources prove today and what they only
point toward.

The rule is strict: a finite or exact-rational check is a useful shadow, not
the theorem. Axeyum can replay the shadow with small trusted checkers; the
general theorem graduates only when a Lean route states the theorem, checks it
without `sorry`, and records the axiom boundary.

Concept rows:

- `bridge_bounded_theorem_shadow`
- `bridge_bounded_epsilon_delta_shadow`
- `bridge_metric_ball`
- `bridge_compactness_shadow`
- `bridge_connectedness_shadow`
- `bridge_continuity_preimage`
- `bridge_rational_convexity_shadow`
- `bridge_finite_measure_additivity`
- `bridge_finite_product_integration`
- `bridge_inner_product_projection`
- `bridge_finite_operator_chebyshev`
- `bridge_lean_horizon`

Companion pages:

- [Rational And Real Algebra](rational-real-algebra.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Real Completeness Theorem Boundary](real-completeness-theorem-boundary.md)
- [Monotone Convergence Theorem Boundary](monotone-convergence-theorem-boundary.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Hitting-Time Theorem Boundary](hitting-time-theorem-boundary.md)
- [Matrix Computation Index](matrix-computation-index.md)

## How To Read The Map

| Column | Meaning |
|---|---|
| Theorem family | The university-math theorem cluster learners expect. |
| Current finite resources | Packs that provide executable shadows today. |
| What is checked now | The exact bounded claim Axeyum can replay or certify. |
| Missing theorem route | The Lean/theory work needed before the general theorem is proved. |
| Next build artifact | The next resource that would make the horizon more concrete. |

## Horizon Crosswalk

| Theorem Family | Current Finite Resources | What Is Checked Now | Missing Theorem Route | Next Build Artifact |
|---|---|---|---|---|
| Real completeness: least upper bounds, Cauchy completeness, monotone convergence | `real-analysis-rational-v0`, `sequence-limit-shadow-v0`, `bounded-monotone-sequence-v0`, `reals-rcf-shadow-v0` | Exact rational intervals, finite epsilon-tail rows, finite monotone prefixes, finite prefix suprema, replay-only bad monotone-bound rows, and separate QF_LRA/Farkas bad-bound certificates. | A Lean real-number development tying ordered fields, suprema, Cauchy sequences, and monotone convergence together. | [Real Completeness Theorem Boundary](real-completeness-theorem-boundary.md) plus [Monotone Convergence Theorem Boundary](monotone-convergence-theorem-boundary.md), then separate no-`sorry` Lean theorem stubs for least-upper-bound, Cauchy, and monotone convergence. |
| Continuity and limits: epsilon-delta, sequential limits, IVT, MVT | `real-analysis-rational-v0`, `metric-continuity-v0`, `sequence-limit-shadow-v0`, `finite-root-finding-v0`, `calculus-algebraic-shadow-v0` | Fixed rational epsilon/delta samples, finite metric balls, finite output-bound checks, polynomial derivative replay, and one bisection/Newton step. | Fully quantified continuity and differentiability theorems over intervals, with compactness/completeness imports and no finite-sample overclaiming. | A continuity theorem-dependency ledger linking epsilon-delta shadows to IVT and MVT prerequisites. |
| Fundamental theorem of calculus and integration limits | `calculus-riemann-sum-v0`, `calculus-algebraic-shadow-v0`, `finite-integration-v0`, `finite-product-measure-v0` | Exact finite Riemann sums, midpoint/trapezoid replay, polynomial antiderivative endpoint checks, finite simple-function integrals, and finite Fubini-style sums. | Riemann or Lebesgue integration theory, limits of partitions, dominated/monotone convergence where needed, and theorem-level FTC statements. | A finite-sum-to-integral horizon note that separates antiderivative endpoint replay from FTC proof obligations. |
| Compactness, connectedness, separation, and continuous-image theorems | `finite-topology-v0`, `finite-specialization-order-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `metric-continuity-v0` | Finite topology axiom replay, finite specialization-preorder replay, finite `T0`/antisymmetry checks, finite open-cover/subcover replay, clopen-subset enumeration, finite open-preimage continuity, and checked Bool/CNF or QF_UF/Alethe bad-row evidence. | General topological compactness, Heine-Borel, separation-axiom and specialization-order theorems, continuous-image compactness, connected image theorems, and homeomorphism invariance in Lean. | A topology theorem-horizon ledger that names each preservation and separation theorem separately from finite topology replay. |
| Sequence, recurrence, and asymptotic convergence | `sequence-limit-shadow-v0`, `bounded-monotone-sequence-v0`, `finite-recurrence-prefix-v0`, `generating-functions-v0`, `graph-search-runtime-v0` | Finite sequence tails, finite Cauchy-tail enumeration, recurrence prefixes, companion-matrix state replay, replay-only bad recurrence rows plus separate QF_LRA/Farkas recurrence certificates, coefficient extraction, and finite BFS/DFS cost counters. | Inductive recurrence proofs, closed-form solving, generating-function convergence, asymptotic analysis, and big-O theorem reconstruction. | A recurrence/asymptotic boundary page joining finite prefix replay with graph-search runtime horizons. |
| Root-finding convergence and numerical stability | `finite-root-finding-v0`, `reals-rcf-shadow-v0`, `numerical-linear-algebra-v0`, `bounded-dynamics-v0`, `finite-euler-method-v0` | One exact bisection update, one exact Newton update, residual-decrease replay, exact residual bounds, recurrence traces, Euler-step replay, finite Euler error tables, replay-only bad dynamics/Euler rows, and separate QF_LRA/Farkas bad-transition, bad-threshold, bad-width, error-bound, and terminal-error certificates. | Bisection convergence, Newton local convergence, fixed-point contraction arguments, error bounds over all steps, floating-point roundoff, and ODE discretization convergence. | A numerical-honesty template for exact iteration replay versus convergence/stability claims. |
| Convex analysis, KKT sufficiency, duality, and optimization convergence | `linear-optimization-v0`, `convexity-rational-v0`, `finite-separation-v0`, `finite-kkt-v0`, `finite-active-set-qp-v0`, `finite-sdp-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0`, `finite-projected-gradient-v0`, `finite-proximal-gradient-v0` | Exact LP witnesses, Farkas threshold conflicts, finite midpoint/Jensen checks, separator replay, finite KKT residual and complementarity checks, active-face slack replay, two-by-two SDP slack/objective/gap/slack-entry replay, and one-step descent, step-coordinate, accepted-candidate, exact-minimizer, line-search, projection, projected-decrease, or proximal composite-decrease checks. | Convex separation theorems, KKT sufficiency, strong duality, descent lemma, convergence rates, projected/proximal convergence, and non-smooth subgradient theory. | A convex-optimization theorem ledger that groups each algorithm-step pack by the exact theorem needed to graduate it. |
| Measure and probability convergence | `finite-measure-v0`, `finite-measure-monotonicity-v0`, `finite-product-measure-v0`, `finite-integration-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-martingales-v0`, `finite-concentration-v0`, `finite-stochastic-kernels-v0`, `finite-hitting-times-v0` | Finite sigma-algebra replay, exact atom sums, finite product tables, finite Fubini sums, simple-function expectations, finite conditional expectations, martingale table and bounded stopped-expectation checks, finite hitting-time equations, and finite tail-bound replay. | Countable additivity, measure completion, product-measure existence, monotone/dominated convergence, Radon-Nikodym, regular conditional probabilities, martingale convergence, optional stopping, recurrence/transience theory, and limit theorems. | [Hitting-Time Theorem Boundary](hitting-time-theorem-boundary.md), plus a broader measure-convergence horizon map that assigns each finite table pack to its measure-theoretic theorem dependency. |
| Functional analysis and operator theory | `inner-product-spaces-rational-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0`, `spectral-linear-algebra-v0`, `matrix-invariants-v0`, `finite-dual-spaces-v0` | Exact Gram matrices, finite projections, Gram-Schmidt replay, operator norm bounds, Chebyshev recurrence and bad-prefix rejection, interpolation matrices, fixed eigenpair replay, and finite characteristic-polynomial checks. | Hilbert projection theorem, Riesz representation, Hahn-Banach, Banach/Hilbert completeness, compact-operator theory, spectral theorem, Haar spaces, minimax approximation, and infinite-dimensional approximation theory. | [Chebyshev Theorem Boundary](chebyshev-theorem-boundary.md), then a broader finite-operator horizon page separating matrix/operator replay from Banach and Hilbert theorem targets. |
| Differential equations and dynamical systems | `bounded-dynamics-v0`, `finite-euler-method-v0`, `finite-recurrence-prefix-v0`, `finite-stochastic-kernels-v0`, `finite-markov-chain-v0`, `finite-hitting-times-v0` | Bounded recurrence traces, finite invariants, threshold reachability, replay-only bad transition-step, bad threshold-step, invariant-bound, finite error-bound, terminal-error, and Euler-step rows, separate checked QF_LRA/Farkas dynamics, Euler, and Markov refutations, finite stochastic transitions, stationary distributions, and hitting-time equations. | Existence/uniqueness, continuous flow invariants, stability, Gronwall-style estimates, Euler convergence, PDE theory, infinite-state Markov processes, and recurrence/transience classifications. | [Hitting-Time Theorem Boundary](hitting-time-theorem-boundary.md), plus a dynamics theorem-horizon ledger that groups deterministic, numerical, and stochastic finite shadows separately. |

## Graduation Pattern

Every theorem family above needs the same promotion shape:

1. State the theorem precisely, including hypotheses and target conclusion.
2. Link the finite shadow packs as examples, not evidence for the theorem.
3. Identify the Lean imports or local lemmas needed to state the theorem.
4. Build a no-`sorry` Lean artifact and record the axiom audit.
5. Keep solver regressions tied to the finite shadow unless the theorem proof
   itself becomes part of the trusted route.

## Current Trust Boundary

The small trusted side today is exact replay and certificate checking:
finite-table enumeration, rational arithmetic, matrix/vector recomputation,
finite topology and measure table checks, DRAT/LRAT, QF_LRA/Farkas,
QF_LIA/Diophantine, QF_UF/Alethe, and QF_BV/DRAT where the pack says so.

The large untrusted side is everything that searches, guesses, lowers,
linearizes, samples, or numerically iterates. A finite Newton step can be
replayed. Newton convergence requires theorem reconstruction. A finite product
table can be replayed. Fubini/Tonelli requires theorem reconstruction. A finite
projection can be replayed. Hilbert-space projection requires theorem
reconstruction.

## Validation

From the repository root:

```sh
./scripts/check-links.sh
python3 scripts/query-foundational-resources.py summary
```

Expected resource boundary for this page: counts should not change unless the
atlas adds new concept rows or example packs. The page is a navigation and
planning resource over existing validated packs.
