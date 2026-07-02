# Theorem Horizon Queries

This is the consumer-facing query guide for Lean/theorem-horizon rows. It is
the companion to the proof-route summary in
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md) and the learner-facing
[Lean Horizon](../proof-cookbook/recipes/lean-horizon-template.md) recipe.

The horizon rows are deliberately negative claims about current evidence:

```text
finite check exists -> useful bounded shadow
general theorem     -> not proved here yet; needs Lean/theorem reconstruction
```

Use this guide when a consumer wants to find which mathematical claims are
explicitly out of scope for the current finite resource and should not be
treated as SMT, replay, benchmark, or solver-parity evidence.

## Start Here

Summarize the Lean-horizon route:

```sh
python3 scripts/query-foundational-resources.py routes \
  --route lean \
  --require-any
```

Find packs that declare the route:

```sh
python3 scripts/query-foundational-resources.py packs \
  --route lean-horizon-template \
  --proof-status lean-horizon \
  --require-any
```

Find the actual horizon rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status lean-horizon \
  --require-any
```

Pack route summaries use the recipe name `lean-horizon-template`; individual
row discovery should usually filter by `--proof-status lean-horizon`, because
horizon rows are metadata rows rather than checked proof-object rows.

## Direct Horizon Frontier

List theorem-horizon rows with the finite checked and replay rows that live in
the same pack:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --field topology \
  --require-any
```

This answers: "Which finite checked examples are the bounded shadows, and which
general theorem row marks the boundary?" Rows include the pack, fields,
curriculum nodes, horizon row ids, finite checked/replay counts,
`shadow_state`, sample finite row ids, and pack path.

The `shadow_state` column summarizes the finite contrast in the same pack:

- `checked-finite-shadow`: at least one checked finite row lives beside the
  horizon row.
- `replay-only-finite-shadow`: finite replay rows exist, but no checked finite
  row is present in that pack.
- `no-finite-shadow`: the horizon row currently has no finite checked or replay
  contrast in the same pack.

This state is a display and planning hint. It does not mean the general theorem
is proved; it only says how much finite-resource context is available next to
the boundary row.

Curriculum-scoped and machine-readable versions use the same public JSON
contract:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --curriculum-node calculus \
  --format json \
  --require-any
```

Topic text filters are useful for cross-field theorem themes:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text convergence \
  --require-any
```

## Finite-Shadow Triage

Start with theorem boundaries that already have checked finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --shadow-state checked-finite-shadow \
  --require-any
```

Use this when a learner page or downstream UI needs to show the bounded
evidence first and the theorem boundary second.

Rows without a checked finite shadow should be inspected before they are shown
as polished learner cards:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --shadow-state replay-only-finite-shadow \
  --format json

python3 scripts/query-foundational-resources.py horizon-frontier \
  --shadow-state no-finite-shadow \
  --format json
```

An empty result for these two queries is a maintenance signal: the current
public corpus has no horizon row that lacks finite checked/replay contrast
under this coarse same-pack query.

## Field-Scoped Horizon Queries

Logic and proof horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field logic_and_proof \
  --proof-status lean-horizon \
  --require-any
```

Topology and algebraic-topology horizons:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field topology \
  --route lean-horizon-template \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --proof-status lean-horizon \
  --require-any
```

Finite topology, compactness, connectedness, continuous-map, quotient, and
specialization horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-compactness-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-connectedness-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-continuous-maps-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-quotient-topology-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-specialization-order-v0 \
  --require-any
```

Real-analysis and optimization horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field real_analysis \
  --proof-status lean-horizon \
  --require-any
```

Complex-analysis and factorization horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --field complex_analysis \
  --shadow-state checked-finite-shadow \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack complex-plane-transforms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack polynomial-factorization-rational-v0 \
  --require-any
```

Measure/probability horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --proof-status lean-horizon \
  --require-any
```

Random-variable, distribution-law, and measurability horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text random-variable \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --proof-status lean-horizon \
  --require-any
```

Stochastic-kernel, disintegration, and measurable-Markov-kernel horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text stochastic-kernel \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --proof-status lean-horizon \
  --require-any
```

Concentration and asymptotic-statistics horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text concentration \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-concentration-v0 \
  --proof-status lean-horizon \
  --require-any
```

ODE, Euler-method, and numerical-dynamics horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text ODE \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-euler-method-v0 \
  --proof-status lean-horizon \
  --require-any
```

Monotone convergence horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text monotone \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --proof-status lean-horizon \
  --require-any
```

Recurrence, closed-form, asymptotic-growth, and stability horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text recurrence \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --proof-status lean-horizon \
  --require-any
```

Root-finding convergence, error-bound, and numerical-stability horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text root-finding \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --proof-status lean-horizon \
  --require-any
```

Hyperplane-separation, Farkas-duality, and Hahn-Banach horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text separation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --proof-status lean-horizon \
  --require-any
```

KKT necessity/sufficiency and constraint-qualification horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text KKT \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --proof-status lean-horizon \
  --require-any
```

Active-set method, degeneracy, and convergence horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text active-set \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --proof-status lean-horizon \
  --require-any
```

SDP duality, Slater-condition, and cone-KKT horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text SDP \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --proof-status lean-horizon \
  --require-any
```

Gradient-descent convergence, descent-lemma, and rate horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --proof-status lean-horizon \
  --require-any
```

Line-search termination, sufficient-decrease, Wolfe-condition, and convergence
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text line-search \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --proof-status lean-horizon \
  --require-any
```

Wolfe line-search existence, strong-Wolfe, Zoutendijk-style convergence, and
rate horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "Wolfe line-search" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --proof-status lean-horizon \
  --require-any
```

Projected-gradient projection theory, convergence, active-set, and rate
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text projected-gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --proof-status lean-horizon \
  --require-any
```

Proximal-gradient proximal-map, nonsmooth-convex, convergence, and rate
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text proximal-gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --proof-status lean-horizon \
  --require-any
```

Cantor diagonalization, Cantor-Schroeder-Bernstein, countability, choice, and
infinite cardinal-arithmetic horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Cantor \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --proof-status lean-horizon \
  --require-any
```

Max-flow/min-cut, integrality, residual-network, and algorithm-correctness
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "max-flow" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status lean-horizon \
  --require-any
```

Shortest-path optimality, negative-cycle, all-pairs, and algorithm-correctness
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text shortest \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status lean-horizon \
  --require-any
```

Topological-sort, finite DAG linear-extension, and cycle-obstruction horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "topological-sort" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status lean-horizon \
  --require-any
```

Graph-search BFS/DFS runtime, graph-family lower-bound, average-case,
heuristic, and parallel-search horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text BFS \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --proof-status lean-horizon \
  --require-any
```

Affine-geometry affine-combination, incidence, ratio, projective, and
synthetic-geometry horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "affine geometry" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Circle-geometry tangent, chord, power-of-a-point, cyclic, and inversion
horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "circle geometry" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Inversion-geometry circle-line, angle-preservation, power-of-a-point, and
generalized-circle horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "inversion geometry" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Cyclic-geometry inscribed-angle, Ptolemy, angle-chasing, and circle-line
correspondence horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "cyclic geometry" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Hitting-time, recurrence/transience, and stochastic-process horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text hitting \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --proof-status lean-horizon \
  --require-any
```

Martingale, optional-stopping, and stochastic-integration horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text martingale \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --proof-status lean-horizon \
  --require-any
```

Graph/asymptotic horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --proof-status lean-horizon \
  --require-any
```

Convergence horizons across fields:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text convergence \
  --proof-status lean-horizon \
  --require-any
```

Vector-space, duality, tensor, module, and homological-algebra horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-vector-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-dual-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-modules-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-tensor-products-v0 \
  --require-any
```

Algebra homomorphism, quotient, isomorphism, and ideal-theory horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-algebra-homomorphisms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-ideals-v0 \
  --require-any
```

Chebyshev/Haar/minimax horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Chebyshev \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-chebyshev-systems-v0 \
  --proof-status lean-horizon \
  --require-any
```

## Read With The Learner Maps

The main learner maps that explain these boundaries are:

- [Analysis And Calculus Theorem Horizon Map](../learn/math/analysis-calculus-theorem-horizon-map.md)
- [Real Completeness Theorem Boundary](../learn/math/real-completeness-theorem-boundary.md)
- [Monotone Convergence Theorem Boundary](../learn/math/monotone-convergence-theorem-boundary.md)
- [Recurrence And Asymptotic Theorem Boundary](../learn/math/recurrence-asymptotic-theorem-boundary.md)
- [Complex Analysis Theorem Boundary](../learn/math/complex-analysis-theorem-boundary.md)
- [Topology Theorem Boundary](../learn/math/topology-theorem-boundary.md)
- [Root-Finding Convergence Theorem Boundary](../learn/math/root-finding-convergence-theorem-boundary.md)
- [Hyperplane Separation Theorem Boundary](../learn/math/hyperplane-separation-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](../learn/math/kkt-sufficiency-theorem-boundary.md)
- [Active-Set Method Theorem Boundary](../learn/math/active-set-method-theorem-boundary.md)
- [SDP Duality Theorem Boundary](../learn/math/sdp-duality-theorem-boundary.md)
- [Gradient Descent Convergence Theorem Boundary](../learn/math/gradient-descent-convergence-theorem-boundary.md)
- [Line Search Convergence Theorem Boundary](../learn/math/line-search-convergence-theorem-boundary.md)
- [Wolfe Line Search Theorem Boundary](../learn/math/wolfe-line-search-theorem-boundary.md)
- [Projected Gradient Convergence Theorem Boundary](../learn/math/projected-gradient-convergence-theorem-boundary.md)
- [Proximal Gradient Convergence Theorem Boundary](../learn/math/proximal-gradient-convergence-theorem-boundary.md)
- [Cardinality Theorem Boundary](../learn/math/cardinality-theorem-boundary.md)
- [Algebra Homomorphism And Quotient Theorem Boundary](../learn/math/algebra-homomorphism-quotient-theorem-boundary.md)
- [Linear Algebra Structure Theorem Boundary](../learn/math/linear-algebra-structure-theorem-boundary.md)
- [Max-Flow Min-Cut Theorem Boundary](../learn/math/max-flow-min-cut-theorem-boundary.md)
- [Shortest Path Theorem Boundary](../learn/math/shortest-path-theorem-boundary.md)
- [Topological Sort Theorem Boundary](../learn/math/topological-sort-theorem-boundary.md)
- [Graph Search Runtime Theorem Boundary](../learn/math/graph-search-runtime-theorem-boundary.md)
- [Affine Geometry Theorem Boundary](../learn/math/affine-geometry-theorem-boundary.md)
- [Circle Geometry Theorem Boundary](../learn/math/circle-geometry-theorem-boundary.md)
- [Inversion Geometry Theorem Boundary](../learn/math/inversion-geometry-theorem-boundary.md)
- [Cyclic Geometry Theorem Boundary](../learn/math/cyclic-geometry-theorem-boundary.md)
- [Random Variable Theorem Boundary](../learn/math/random-variable-theorem-boundary.md)
- [Stochastic Kernel Theorem Boundary](../learn/math/stochastic-kernel-theorem-boundary.md)
- [Hitting-Time Theorem Boundary](../learn/math/hitting-time-theorem-boundary.md)
- [Martingale Theorem Boundary](../learn/math/martingale-theorem-boundary.md)
- [Chebyshev Theorem Boundary](../learn/math/chebyshev-theorem-boundary.md)
- [Concentration Theorem Boundary](../learn/math/concentration-theorem-boundary.md)
- [Euler Method Theorem Boundary](../learn/math/euler-method-theorem-boundary.md)
- [Analysis And Topology Proof Horizons](../learn/math/analysis-topology-proof-horizons.md)
- [Matrix Corpus And Benchmark Boundary](../learn/math/matrix-corpus-benchmark-boundary.md)
- [Finite Countermodel Replay](../learn/math/finite-countermodel-replay.md)

Those pages state the finite or computable slice first, then name the missing
general theorem route. This is the intended reading order: bounded check before
horizon.

## Boundary

A horizon row proves neither the theorem nor its negation. It is a resource
boundary marker. Consumers may use it to:

- warn that a finite example does not prove a general theorem;
- route future work toward Lean or another kernel-checked theorem path;
- keep theorem claims out of solver-performance and benchmark summaries;
- explain why a pack contains `not-run` rows alongside checked finite rows.

Do not count Lean-horizon rows as checked SMT evidence, checked replay
evidence, or parity with Z3/cvc5/Lean. They are explicit work items for future
proof reconstruction.
