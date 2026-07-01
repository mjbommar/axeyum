# Matrix Corpus And Benchmark Boundary

This note separates three things that are easy to conflate:

- educational matrix resources that teach exact replay;
- solver regressions that guard a route against future breakage; and
- benchmark corpus rows that can support performance or parity claims.

Axeyum's matrix resources are valuable because they show the project identity in
small, checkable form: untrusted fast search, trusted small checking. They are
not, by themselves, evidence that Axeyum is faster than Z3, cvc5, LAPACK,
specialized numerical solvers, or proof assistants.

## Audience

This page is for resource authors, solver contributors, and readers who want to
reuse matrix examples without overstating what the examples prove.

Use it when adding or promoting rows for:

- LU, rank/nullity, kernel/image, and exact rational linear systems;
- residuals, projections, normal equations, and finite numerical shadows;
- eigenpairs, characteristic polynomials, finite operators, and Chebyshev rows;
- finite random matrices and matrix-valued probability tables;
- chain-complex boundary matrices, module actions, and tensor/Kronecker rows;
- optimization rows whose constraints are matrix-shaped.

## Artifact Levels

| Level | What It Contains | What It Can Claim | What It Cannot Claim |
|---|---|---|---|
| Educational resource row | A source pack row with exact finite data, expected result, validation route, and learner link. | The fixed example can be replayed or rejected by the named checker. | Solver performance, general theorem coverage, numerical stability, or parity. |
| Solver regression row | A compact source-linked artifact plus a deterministic cargo or script regression that checks the same route. | A specific route should keep accepting or rejecting this family correctly. | Corpus-wide decide-rate, PAR-2, or solver-vs-solver performance. |
| Benchmark corpus row | Fixed corpus membership, pinned config, resource limits, oracle/differential comparison, replay policy, hardware note, and stored results artifact. | Measured performance on that corpus under that configuration. | General parity beyond the measured corpus and configuration. |
| Theorem-horizon row | A finite shadow plus the missing Lean/theorem dependency. | The finite example motivates a future theorem artifact. | That the general theorem has been proved or benchmarked. |

## Current Matrix Families

| Family | Source Packs | Checked Today | Boundary |
|---|---|---|---|
| Exact linear systems and LU | [`linear-algebra-rational-v0`](../../../artifacts/examples/math/linear-algebra-rational-v0/), [`linear-optimization-v0`](../../../artifacts/examples/math/linear-optimization-v0/) | Fixed `A*x = b`, `L*U = A`, inconsistent rational systems, and LP threshold conflicts through finite replay plus QF_LRA/Farkas. | Regression source only until a named linear-system corpus, limits, oracle comparison, and PAR-2 artifact exist. |
| Residuals and least squares | [`numerical-linear-algebra-v0`](../../../artifacts/examples/math/numerical-linear-algebra-v0/), [`least-squares-regression-v0`](../../../artifacts/examples/math/least-squares-regression-v0/), [`inner-product-spaces-rational-v0`](../../../artifacts/examples/math/inner-product-spaces-rational-v0/) | Exact residuals, solution boxes, normal equations, orthogonal residuals, RSS improvement, projections, Gram matrices, and bad rational bounds. | No floating-point accuracy, conditioning, convergence, or stability claim without numerical-honesty metadata and a separate experimental protocol. |
| Finite vector, module, and tensor tables | [`finite-vector-spaces-v0`](../../../artifacts/examples/math/finite-vector-spaces-v0/), [`finite-dual-spaces-v0`](../../../artifacts/examples/math/finite-dual-spaces-v0/), [`finite-modules-v0`](../../../artifacts/examples/math/finite-modules-v0/), [`finite-tensor-products-v0`](../../../artifacts/examples/math/finite-tensor-products-v0/) | Finite carrier replay, kernel/image membership, rank/nullity equality, dual maps, scalar actions, bilinear maps, and Kronecker rows. | No arbitrary-field theorem, basis-extension proof, or module-structure theorem claim until a Lean/no-sorry route exists. |
| Spectral and invariant rows | [`spectral-linear-algebra-v0`](../../../artifacts/examples/math/spectral-linear-algebra-v0/), [`matrix-invariants-v0`](../../../artifacts/examples/math/matrix-invariants-v0/) | Exact eigenpair replay, Rayleigh quotients, fixed spectral reconstruction, trace, determinant, characteristic roots, Cayley-Hamilton rows, and bad Rayleigh/eigenpair/polynomial certificates. | No eigenvalue algorithm benchmark, diagonalization theorem, spectral theorem, or algebraic-closure claim. |
| Finite random matrices | [`random-matrix-finite-v0`](../../../artifacts/examples/math/random-matrix-finite-v0/) | Exact finite matrix-valued distributions, trace/determinant moments, expected Gram matrices, and rank-mixture probabilities. | No simulation-quality, asymptotic law, concentration theorem, universality, or random-matrix performance claim. |
| Boundary matrices and homology | [`finite-simplicial-homology-v0`](../../../artifacts/examples/math/finite-simplicial-homology-v0/) | Boundary matrices, `boundary^2 = 0`, Betti-rank replay, and a checked bad oriented-boundary coefficient. | No homology invariance theorem or general chain-complex proof beyond the fixed finite complex. |
| Operator and Chebyshev matrices | [`finite-operator-v0`](../../../artifacts/examples/math/finite-operator-v0/), [`finite-chebyshev-systems-v0`](../../../artifacts/examples/math/finite-chebyshev-systems-v0/) | Exact operator action/norm rows, Chebyshev recurrence replay, bad Chebyshev-prefix rejection, Vandermonde unisolvence, interpolation values, duplicate-node failures, bad interpolation samples, and alternating residuals. | No Banach/Hilbert theorem, compact-operator theorem, Haar theorem, minimax theorem, or approximation-theory graduation. |
| Optimization matrix shadows | [`finite-kkt-v0`](../../../artifacts/examples/math/finite-kkt-v0/), [`finite-active-set-qp-v0`](../../../artifacts/examples/math/finite-active-set-qp-v0/), [`finite-sdp-v0`](../../../artifacts/examples/math/finite-sdp-v0/), [`finite-gradient-descent-v0`](../../../artifacts/examples/math/finite-gradient-descent-v0/), [`finite-line-search-v0`](../../../artifacts/examples/math/finite-line-search-v0/), [`finite-wolfe-line-search-v0`](../../../artifacts/examples/math/finite-wolfe-line-search-v0/), [`finite-projected-gradient-v0`](../../../artifacts/examples/math/finite-projected-gradient-v0/), [`finite-proximal-gradient-v0`](../../../artifacts/examples/math/finite-proximal-gradient-v0/) | Fixed stationarity, complementarity, slack, degenerate active-bound multiplier, objective, duality-gap, descent, step-coordinate, Armijo accepted-candidate, Wolfe exact-minimizer, projection, projected-decrease, and soft-threshold steps over exact rationals. | No optimization-method convergence, duality, sufficiency, strong-duality, or algorithmic performance claim. |

## Promotion Checklist

A matrix row may become a solver regression only when all of these are true:

1. The source pack validates from committed data.
2. The exact checked route is named: finite replay, QF_LRA/Farkas,
   QF_UF/Alethe, QF_LIA/Diophantine, QF_BV bit-blast, or Lean horizon.
3. The artifact is compact, deterministic, and stored under the source pack or
   a clearly linked solver-test fixture.
4. The route-specific regression cites the source pack and artifact.
5. The pack metadata cites the regression through `solver_reuse` before any
   dashboard calls it promoted solver reuse.
6. The expected verdict is replayed against the original source claim, not only
   a lowered artifact.

A promoted regression may become a benchmark corpus row only after the benchmark
methodology requirements are met: fixed corpus membership, pinned solver config,
explicit time and size limits, deterministic ordering and seed, oracle or
differential comparison where applicable, model replay policy, hardware note,
stored results artifact, and PAR-2 or an explicitly documented alternative
metric.

## Do Not Claim Yet

Do not use the current matrix resources to claim:

- Z3/cvc5 parity or superiority on linear algebra workloads;
- performance against numerical linear algebra libraries;
- floating-point stability, conditioning, or roundoff correctness;
- general rank-nullity, spectral theorem, Cayley-Hamilton, homology
  invariance, Hilbert projection, or Chebyshev minimax theorem coverage;
- random-matrix asymptotics, simulation quality, or concentration theorem
  coverage;
- optimization convergence or duality theorem coverage.

Those claims need either benchmark artifacts under the project benchmarking
methodology or no-sorry theorem artifacts under the proof/Lean route.

## Validation

Use these commands from the repository root when touching this boundary:

```sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
python3 scripts/query-foundational-resources.py packs --field linear_algebra --solver-reuse promoted
python3 scripts/query-foundational-resources.py packs --route Farkas --solver-reuse promoted
python3 scripts/query-foundational-resources.py packs --route Alethe --solver-reuse promoted
./scripts/check-links.sh
```

For performance claims, also cite a stored benchmark result produced under
[`Benchmarking And Performance Methodology`](../../research/08-planning/benchmarking-and-performance-methodology.md).
