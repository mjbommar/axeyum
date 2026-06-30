# Math Curriculum Resource Buildout Roadmap

## Purpose

This is the detailed operating plan for building the full foundational-resource
ecosystem from the math curriculum spine. It complements:

- [Math Curriculum Resource Buildout](MATH-CURRICULUM-BUILDOUT.md), the phase
  contract and landed-history log.
- [Math Curriculum Implementation Matrix](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md),
  the commit-sized gate matrix.
- [Curriculum Resource Execution Plan](CURRICULUM-RESOURCE-EXECUTION-PLAN.md),
  the current forward plan.
- [University Math Field Taxonomy](MATH-FIELDS.md), the 18-field university
  field spine.

The invariant is:

```text
curriculum node -> concept row -> example pack -> learner page -> proof route
-> solver reuse -> consumer boundary
```

The product is not a textbook and not a formal-library clone. It is a system of
small resources that make Axeyum's identity concrete:

```text
untrusted fast search, trusted small checking
```

## Current Baseline

The current committed data boundary reports:

- 23 curriculum-node concept rows.
- 18 math-field concept rows.
- 22 bridge-concept rows.
- 2 example-family rows.
- 84 non-template math example packs.
- 413 expected checks.
- 195 checked proof/evidence rows.
- 171 replay-only rows.
- 47 Lean-horizon rows.
- 16 promoted solver-reuse packs.

This is broad enough that the next work is not "create a few examples." The
next work is to make the resource system deep, navigable, and reusable:

- split broad curriculum nodes into reusable concept rows;
- upgrade representative rows from replay-only to checked certificates;
- turn selected examples into solver regressions and fuzz seeds;
- make every lesson expose the trust boundary;
- keep consumer/API boundaries JSON-first until repeated use proves a library
  split is worth it.

## Source Of Truth

Build from the sources in this order:

1. [curriculum.toml](../curriculum/curriculum.toml): authoritative 23-node math
   prerequisite DAG.
2. [MATH-FIELDS.md](MATH-FIELDS.md): 18-field university expansion taxonomy.
3. Existing non-template packs under `artifacts/examples/math/`.
4. [SMT Fragment Atlas](../atlas/README.md): fragment and support vocabulary.
5. [Proof Certificate Cookbook](../proof-cookbook/README.md): evidence-route
   vocabulary.
6. [Rules-as-Code Verification Lab](../rules-as-code/README.md): downstream
   pattern reuse for policy/law/rule reasoning.

If a generated dashboard disagrees with prose, fix the source JSON/metadata or
the generator. Do not hand-edit generated views.

## Resource Layers

### R1: Concept Atlas

Audience: learners, proof contributors, solver contributors, and downstream
consumers.

Build plan:

- Keep one row per curriculum node and one row per math field.
- Add bridge-concept rows only when multiple packs need the same vocabulary.
- Add example-family rows for repeated solver/proof shapes, not for every pack.
- Add field-specific concept rows when a broad curriculum node hides materially
  different ideas, such as quotient maps, kernels/images, compactness shadows,
  Farkas infeasibility, or finite model replay.

Minimum row content:

- curriculum or field anchor;
- decidability scope;
- Axeyum fragment route;
- example packs;
- proof routes;
- open gaps;
- graduation criteria.

Near-term concept-row families:

| Family | Why It Matters | First Rows |
|---|---|---|
| finite model replay | Repeated witness-check story across most packs | model replay, counterexample replay, bounded enumeration |
| proof object anatomy | Explains checked UNSAT beyond "solver says no" | CNF/LRAT, Farkas, Alethe, QF_BV DRAT |
| algebraic structure maps | Current algebra packs are broad | homomorphism, kernel/image, quotient, action, ideal, module, tensor |
| analysis/topology boundaries | Prevents overclaiming bounded examples | metric ball, epsilon-delta shadow, compactness shadow, connectedness shadow, continuity preimage |
| matrix computation | Bridges education and solver corpora | LU replay, rank/nullity, residual bound, eigenpair, characteristic polynomial, finite random-matrix moment |
| probability/statistics tables | Many packs share finite probability structure | pushforward, kernel, expectation, conditioning, tail-count obstruction |
| rules/law transfer | Reuses math concepts for policies | finite predicate, threshold, exception, precedence, temporal version |

Graduation signal: `python3 scripts/validate-foundational-concepts.py` passes
and the generated dashboards expose the row without manual prose.

### R2: Example Packs

Audience: learners, educators, proof contributors, and solver contributors.

Every pack should have:

- `README.md`: audience, scope, limitations, and lesson links;
- `metadata.json`: fields, concepts, fragments, proof routes, validator command,
  and optional `solver_reuse`;
- `model.md`: finite model and symbols;
- `checks.md`: expected SAT/UNSAT/UNKNOWN rows and trust story;
- `expected.json`: machine-readable expected outcomes;
- optional `cnf/` or `smt2/` artifacts only when small and stable.

Pack build sequence:

1. Define one exact finite or computable claim.
2. Add at least one positive witness row and one negative/counterexample row
   when the concept naturally supports both.
3. Replay every witness against the mathematical source object.
4. For UNSAT, use checked evidence when available; otherwise mark the proof
   route explicitly as replay-only, gap, or Lean horizon.
5. Add a focused learner page once the pack validates and teaches a distinct
   workflow.
6. Promote one representative row into a solver regression only after the pack
   replay is deterministic.

Graduation signal: `python3 scripts/validate-foundational-example-pack.py
artifacts/examples/math/<pack>` passes, and the pack appears in learner and
proof dashboards.

### R3: Learner Pages

Audience: learners and educators.

Each page should be a small proof/checking walkthrough, not a generic textbook
chapter.

Required structure:

1. State the concept.
2. State the finite or computable slice Axeyum checks.
3. Name the exact pack and check rows.
4. Show the model, counterexample, or certificate route.
5. State the proof horizon and current missing dependency.
6. Include a runnable validation command.

Build plan:

- Keep the nine cluster pages as the table of contents.
- Keep focused end-to-end pages for packs that have enough substance to teach a
  complete loop.
- Prefer route notes over duplicated pack metadata.
- Never imply a finite bounded check proves a general theorem.

Graduation signal: `./scripts/check-links.sh` passes and the learner/proof
dashboard shows no missing learner link for the pack.

### R4: Proof And Evidence

Audience: proof contributors, reviewers, and users who need assurance.

Route plan:

| Route | Use For | Immediate Work |
|---|---|---|
| finite replay | SAT witnesses, finite table checks, computed witnesses | Make every replay row state what is recomputed independently. |
| Boolean CNF DRAT/LRAT | finite Boolean refutations, graph/search/set-family conflicts | Promote small topology and graph rows that are source-level obvious. |
| QF_BV DRAT | fixed-width residue, bit-vector, and finite algebra conflicts | Promote only when width is part of the educational claim. |
| QF_LIA/Diophantine | integer equations, counts, modular obstructions, rank coefficients | Group recurring gcd/divisibility obstructions as cookbook examples. |
| QF_LRA/Farkas | exact rational infeasibility, LP, residuals, probability tables | Continue promoting bad table and bad bound rows with independent Farkas checks. |
| QF_UF/Alethe | equality-heavy finite functions, quotients, homomorphisms | Use table replay for objects, Alethe for congruence conflicts. |
| Lean horizon | induction schemas, completeness, topology, measure, asymptotics | Record theorem shape and dependencies; do not benchmark as finite checks. |

Graduation signal: route-specific cargo test passes, the pack links the recipe,
and the trust boundary is described in the learner page.

### R5: Solver Reuse

Audience: solver contributors and benchmark maintainers.

The educational resources become solver assets only after their mathematical
meaning is stable.

Build plan:

- Add `solver_reuse.status = candidate` only when a row pressures a real solver
  fragment.
- Promote to `promoted` only after a regression, fuzz seed, benchmark slice, or
  explicit non-benchmark-horizon back-link exists.
- Keep source-level artifacts under the pack folder when possible.
- Name the solver pressure in metadata: clause learning, bit-blast lowering,
  LIA divisibility, Farkas certificate, EUF congruence, array extensionality,
  quantifier finite expansion, or Lean reconstruction.

Good promotion candidates:

- one small Bool/CNF row per graph/topology/set-family pattern;
- one LIA row per recurring integer obstruction pattern;
- one LRA row per probability/statistics/optimization bad table;
- one QF_UF row per equality-heavy algebra family;
- one QF_BV row per fixed-width residue or finite algebra pattern.

Graduation signal: the regression or corpus source cites the pack, and the pack
metadata links back to the regression.

### R6: Consumer Boundary

Audience: downstream tools, sibling projects, and future libraries.

Keep the boundary boring until real use proves otherwise:

- committed JSON schemas;
- committed JSON metadata;
- generated Markdown dashboards;
- `scripts/consume-foundational-resources.py`;
- `scripts/query-foundational-resources.py`.

Do not split a crate or repo because the plan is large. Split only when there
are at least three duplicated consumers or one external consumer that needs an
independent release cadence.

Likely future packages:

| Boundary | Trigger | Contents |
|---|---|---|
| `axeyum-foundational-data` | typed accessors are duplicated | concept rows, pack rows, proof routes, dashboard data |
| `axeyum-math-examples` | encoders are duplicated across tests/apps | finite graph, algebra, matrix, topology, probability encoders |
| standalone resource repo | data grows too large for core reviews | examples, lessons, generated site, public release cadence |
| rules/law sibling | rule packs become independently useful | norm graph, citations, temporal rules, eligibility/policy examples |

## Curriculum-Layer Build Plan

### Layer 0: Foundations

Nodes: propositional logic, predicate logic, proof methods, induction, sets,
relations/functions, cardinality.

Current resource surface:

- Boolean SAT and CNF examples.
- Finite predicate expansion.
- Proof-method patterns.
- Bounded induction obligations.
- Finite set, relation, function, lattice, and cardinality packs.

Build next:

- Add concept rows for proof by refutation, proof by cases, finite quantifier
  expansion, finite countermodel replay, induction obligation, and induction
  schema horizon.
- Promote small Boolean refutations to checked DRAT/LRAT where the source
  formula is clear enough for a learner.
- Add reusable schemas for finite relation/function tables, quotient maps,
  finite partitions, image/preimage, and inverse tables.
- Keep full first-order validity, full induction, and infinite cardinality as
  Lean-horizon rows.

Solver/proof pressure:

- Bool/CNF and DRAT/LRAT for finite refutations.
- QF_UF/Alethe for finite function consistency and congruence.
- Lean reconstruction for proof methods and induction schemas.

### Layer 1: Number Systems

Nodes: naturals, integers, rationals, reals, complex numbers.

Current resource surface:

- Bounded natural arithmetic.
- Integer LIA.
- Exact rational LRA.
- Algebraic real/RCF shadows.
- Bounded real-analysis and metric-continuity examples.
- Complex arithmetic as real-pair algebra.

Build next:

- Add concept rows for exact-vs-floating arithmetic, total operations, bounded
  natural prefixes, integer divisibility obstructions, rational order, real
  algebraic shadow, metric ball, epsilon-delta shadow, and analytic horizon.
- Promote representative bad arithmetic rows into LIA, LRA, or QF_BV proof
  routes according to the source concept.
- Add lesson notes that separate exact rationals and algebraic real shadows
  from real completeness.
- Keep complex analysis, holomorphic functions, and analytic continuation as
  Lean-horizon material until proof reconstruction exists.

Solver/proof pressure:

- QF_LIA/Diophantine for integer facts.
- QF_LRA/Farkas for rational order/infeasibility.
- QF_NRA/RCF for algebraic real shadows.
- Lean horizon for completeness and analytic theorems.

### Layer 2: Core Structures And Tools

Nodes: divisibility, modular arithmetic, groups, rings, fields, polynomials,
sequences/limits, counting.

Current resource surface:

- GCD/Bezout, CRT/residue checks, finite groups, monoids, permutation groups,
  actions, rings, fields, ideals, modules, tensor products, polynomial
  identities/factorization, generating functions, counting, and bounded
  sequence/limit shadows.

Build next:

- Split algebra concepts into kernels/images, quotients, ideals, modules,
  tensor universal-property shadows, orbit-stabilizer, Burnside, unit/idempotent
  replay, and homomorphism preservation.
- Add polynomial concept rows for coefficient extraction, division with
  remainder, GCD, square-free decomposition, factor theorem, and generating
  functions.
- Promote equality-heavy conflicts through QF_UF/Alethe and fixed-width
  algebra conflicts through QF_BV only when the encoding matches the concept.
- Keep arbitrary group/ring/field theory, general factorization, and full
  convergence theory as Lean-horizon.

Solver/proof pressure:

- QF_UF/Alethe for equality and congruence.
- QF_BV for fixed finite tables and residue arithmetic.
- QF_LIA for divisibility and coefficient obstructions.
- Lean horizon for general algebra and sequences.

### Layer 3: Destinations

Nodes: number theory, linear algebra, calculus.

Current resource surface:

- Bounded number-theory checks.
- Exact rational linear algebra.
- Finite vector/dual/module/tensor resources.
- Inner-product, spectral, matrix-invariant, numerical-linear-algebra, and
  random-matrix finite packs.
- Algebraic calculus, finite Riemann sums, and multivariable rational calculus.

Build next:

- Treat number theory as arithmetic-certificate pressure: bounded Diophantine,
  residue, CRT, quadratic residue, sum-of-squares, and modular obstruction
  families.
- Treat linear algebra as the bridge from education to solver-friendly matrix
  corpora: LU, rank/nullity, residual bounds, eigenpair checks, characteristic
  polynomial, tensor maps, and finite-field linear algebra.
- Treat calculus as exact algebraic shadow plus explicit proof horizon:
  derivative identities, Jacobian/Hessian replay, finite sums, bounded
  epsilon-delta samples, and theorem targets for FTC, convergence, and
  differentiability.

Solver/proof pressure:

- QF_LIA and QF_BV for bounded number theory.
- QF_LRA/Farkas for rational matrix infeasibility, residual bounds, and LP.
- QF_NRA for polynomial calculus shadows.
- Lean horizon for analytic calculus theorems.

## Field-By-Field Build Plan

### 1. Logic And Proof

Current packs:

- `logic-basics-v0`
- `finite-predicate-v0`
- `proof-methods-refutation-v0`
- `proof-methods-patterns-v0`
- `induction-obligations-v0`
- `induction-patterns-v0`

Build next:

- Add concept rows for refutation, natural-deduction pattern, finite
  countermodel, bounded induction obligation, and Lean induction schema.
- Add a proof-object anatomy lesson that starts from a tiny CNF, emits
  DRAT/LRAT, tampers with it, and shows checker rejection.
- Promote one small proof-method contradiction row to the Boolean CNF route if
  it is not already represented by a checked route.

Graduation:

- At least one learner page traces formula -> untrusted search -> certificate
  -> checker rejection of a corrupted certificate.

### 2. Set Theory And Foundations

Current packs:

- `finite-sets-v0`
- `relations-functions-v0`
- `equivalence-classes-v0`
- `function-composition-v0`
- `finite-order-lattices-v0`
- `finite-cardinality-v0`
- `cardinality-principles-v0`

Build next:

- Add concept rows for finite Boolean algebra, partition, quotient map,
  image/preimage, inverse table, injection/surjection/bijection, and
  finite/infinite cardinality boundary.
- Promote small false set/lattice/cardinality claims to Bool/CNF or QF_UF
  routes when the source encoding is obvious.
- Keep Cantor, choice, ordinal/cardinal arithmetic, and infinite set theory as
  Lean-horizon rows.

Graduation:

- Each false finite claim has checked evidence or an explicit route gap; each
  infinite claim is visibly excluded from solver benchmarks.

### 3. Discrete Math

Current packs:

- `counting-v0`
- `generating-functions-v0`
- graph packs listed under `graph_theory`
- finite permutation/action packs shared with algebra.

Build next:

- Add concept rows for finite enumeration, pigeonhole, double counting,
  coefficient extraction, recurrence prefix, and asymptotic horizon.
- Add one reusable "bounded family vs asymptotic theorem" bridge row for graph
  search and recurrences.
- Promote finite counting contradictions through CNF/LRAT or LIA when they
  produce small certificates.

Graduation:

- Learner pages state exactly which finite family size is checked and what
  remains asymptotic proof work.

### 4. Graph Theory

Current packs:

- `graph-coloring-v0`
- `graph-reachability-v0`
- `graph-search-runtime-v0`
- `graph-matching-v0`
- `graph-cut-v0`
- `graph-d-separation-v0`

Build next:

- Add concept rows for coloring, reachability, BFS/DFS traversal, matching,
  cut, separation, d-separation, and graph-counterexample replay.
- Promote one representative bad row per graph family into a small regression
  artifact if it produces a compact CNF/LIA/BV check.
- Add proof-route notes for when graph claims are Boolean SAT, finite replay,
  LIA cost counters, or Lean-horizon asymptotics.

Graduation:

- A solver contributor can filter graph resources by fragment and immediately
  find source-linked regression candidates.

### 5. Number Theory

Current packs:

- `gcd-bezout-v0`
- `modular-arithmetic-v0`
- `number-theory-v0`
- `integer-lia-v0`
- `natural-arithmetic-v0`
- `finite-fields-v0`
- `finite-ideals-v0`

Build next:

- Add concept rows for gcd witness, Bezout certificate, modular inverse,
  CRT compatibility, quadratic residue, Diophantine obstruction, bounded
  residue enumeration, and deep theorem horizon.
- Promote recurring integer obstructions into QF_LIA/Diophantine examples.
- Use QF_BV only when fixed-width residue semantics is the point of the lesson.

Graduation:

- Every modular or Diophantine row says whether it is a bounded residue check,
  an integer proof route, or a theorem-horizon placeholder.

### 6. Linear Algebra

Current packs:

- `linear-algebra-rational-v0`
- `finite-vector-spaces-v0`
- `finite-dual-spaces-v0`
- `inner-product-spaces-rational-v0`
- `finite-modules-v0`
- `finite-tensor-products-v0`
- `numerical-linear-algebra-v0`
- `spectral-linear-algebra-v0`
- `matrix-invariants-v0`
- `random-matrix-finite-v0`
- `least-squares-regression-v0`
- `multivariable-calculus-rational-v0`

Build next:

- The first generated bridge rows now cover LU replay, rank/nullity replay,
  residual bounds, eigenpair witnesses, characteristic-polynomial replay, and
  finite random-matrix moments.
- Add narrower concept rows for matrix multiplication, kernel/image, dual basis,
  transpose, tensor bilinear map, Gram matrix, projection, and finite-field
  linear algebra when one row can serve multiple packs.
- Promote rational infeasibility rows through QF_LRA/Farkas and finite-field
  table rows through replay or QF_UF/Alethe.
- Add a matrix corpus note that explains which rows can become solver
  regressions without turning education examples into performance claims.

Graduation:

- Matrix rows can be queried by computation type: witness replay, Farkas
  infeasibility, finite-field replay, or Lean horizon.

### 7. Abstract Algebra

Current packs:

- `finite-groups-v0`
- `finite-monoids-v0`
- `finite-permutation-groups-v0`
- `finite-group-actions-v0`
- `finite-rings-v0`
- `finite-fields-v0`
- `finite-algebra-homomorphisms-v0`
- `finite-ideals-v0`
- `finite-modules-v0`
- `finite-vector-spaces-v0`
- `finite-dual-spaces-v0`
- `finite-tensor-products-v0`
- `polynomial-identities-v0`
- `polynomial-factorization-rational-v0`

Build next:

- The first generated algebra-map bridge rows now cover homomorphism
  preservation, kernel/image replay, quotient maps, ideal closure, module
  actions, tensor bilinearity, and finite group actions.
- Split remaining broad finite algebra topics only when a new row can serve
  multiple packs: table axiom replay, orbit/stabilizer refinements, Burnside,
  units/idempotents, polynomial factorization, and representation-theory
  horizons.
- Use `family_finite_algebra_alethe` as the first family row and add narrower
  children only when dashboards need better routing.
- Keep structure theorems, arbitrary groups/rings/modules, representation
  theory, and category-level facts as Lean-horizon.

Graduation:

- Equality-heavy algebra conflicts have checked Alethe or a named missing
  Alethe-to-Lean route; table replay remains distinct from theorem proof.

### 8. Real Analysis

Current packs:

- `rationals-lra-v0`
- `reals-rcf-shadow-v0`
- `real-analysis-rational-v0`
- `sequence-limit-shadow-v0`
- `metric-continuity-v0`
- `calculus-algebraic-shadow-v0`
- `calculus-riemann-sum-v0`
- `multivariable-calculus-rational-v0`
- `finite-compactness-v0`
- `finite-connectedness-v0`
- `finite-continuous-maps-v0`

Landed:

- Bridge rows for metric ball, bounded epsilon-delta shadow, compactness
  shadow, connectedness shadow, and continuity-by-preimage.

Build next:

- Add concept rows for rational interval, sequence tail, Cauchy shadow,
  squeeze shadow, derivative identity, and integration horizon.
- Promote exact rational bad-bound rows through QF_LRA/Farkas.
- Keep completeness, Bolzano-Weierstrass, Heine-Borel, IVT, MVT, FTC, and
  general convergence as Lean-horizon.

Graduation:

- Every analysis lesson carries a "finite/bounded shadow vs theorem" statement.

### 9. Complex Analysis

Current packs:

- `complex-algebraic-v0`
- `complex-plane-transforms-v0`

Build next:

- Add concept rows for complex-as-real-pair, conjugation, norm, unit roots,
  Mobius transform, fixed polynomial root, and analytic-function horizon.
- Route algebraic claims through real-pair LRA/NRA or finite replay.
- Keep holomorphicity, contour integration, residues, analytic continuation,
  and algebraic closure as Lean-horizon.

Graduation:

- Complex rows cannot be mistaken for analytic theorem coverage.

### 10. Topology

Current packs:

- `finite-topology-v0`
- `metric-continuity-v0`
- `finite-compactness-v0`
- `finite-connectedness-v0`
- `finite-continuous-maps-v0`
- `finite-simplicial-homology-v0`

Build next:

- Add concept rows for topology axioms, open/closed set, closure/interior,
  metric ball, continuous preimage, compact open cover, connected clopen
  witness, homeomorphism, simplicial complex, chain complex, boundary squared
  zero, and homology rank.
- Promote source-level-obvious bad topology rows to Bool/CNF or LIA only when
  the mathematical object is fixed and tiny.
- Keep general compactness, connectedness, homotopy, homology invariance, and
  topological spaces as Lean-horizon.

Graduation:

- Topology dashboards distinguish finite set-family replay from general
  topological theorem proof.

### 11. Measure Theory

Current packs:

- `finite-measure-v0`
- `finite-integration-v0`
- `finite-product-measure-v0`
- `finite-random-variables-v0`
- `finite-conditional-expectation-v0`
- `finite-martingales-v0`
- `finite-stochastic-kernels-v0`
- probability packs shared with `probability_theory`

Build next:

- Add concept rows for finite sigma algebra, finite additivity, simple-function
  integral, product measure, marginal, Fubini finite replay, random-variable
  pushforward, conditioning by partition, and convergence-theorem horizon.
- Promote false finite measure/probability tables through QF_LRA/Farkas.
- Keep Lebesgue measure, dominated convergence, monotone convergence, and
  almost-everywhere reasoning as Lean-horizon.

Graduation:

- Finite measure rows show the exact finite universe and never imply
  sigma-finite or Lebesgue theorem coverage.

### 12. Probability Theory

Current packs:

- `finite-probability-v0`
- `finite-random-variables-v0`
- `finite-conditional-expectation-v0`
- `finite-martingales-v0`
- `finite-stochastic-kernels-v0`
- `finite-hitting-times-v0`
- `finite-concentration-v0`
- `finite-markov-chain-v0`
- `finite-product-measure-v0`

Build next:

- Add concept rows for probability table, conditional probability, Bayes
  update, pushforward distribution, independence, stochastic kernel, Markov
  transition, hitting-time equation, martingale condition, stopping-time
  replay, and concentration bound shadow.
- Promote bad normalization, posterior, kernel-row, expected-time, and
  concentration rows through QF_LRA/Farkas or QF_LIA when exact counts are the
  natural source.
- Keep continuous distributions, stochastic-process limit theorems, optional
  stopping in general, and asymptotic concentration as Lean-horizon.

Graduation:

- Probability rows can be queried by finite table shape and proof route.

### 13. Statistics

Current packs:

- `descriptive-statistics-v0`
- `least-squares-regression-v0`
- `exact-statistical-tests-v0`
- `finite-concentration-v0`
- `finite-probability-v0`
- `random-matrix-finite-v0`

Build next:

- Add concept rows for finite sample statistic, variance identity,
  contingency table, exact binomial tail, Fisher table, least-squares normal
  equations, residual orthogonality, finite sampling, and numerical-honesty
  status.
- Promote bad count/table rows through QF_LIA and bad rational coefficient or
  residual rows through QF_LRA/Farkas.
- Mark simulations, MCMC, VI, asymptotic normality, and calibration claims as
  numerical or proof-horizon, never checked proof.

Graduation:

- Every statistics row says whether it is exact finite enumeration,
  certificate-backed infeasibility, or numerical experiment metadata.

### 14. Optimization And Convexity

Current packs:

- `linear-optimization-v0`
- `convexity-rational-v0`
- `least-squares-regression-v0`
- `multivariable-calculus-rational-v0`
- `numerical-linear-algebra-v0`

Build next:

- Add concept rows for LP feasibility, Farkas certificate, objective threshold,
  rational midpoint convexity, affine monotonicity, gradient, Hessian minor,
  KKT horizon, and duality horizon.
- Promote small infeasible LP/convexity rows through QF_LRA/Farkas.
- Keep general convex analysis, SDP, KKT sufficiency, and algorithm convergence
  as Lean-horizon until proof support exists.

Graduation:

- At least one standalone learner page traces an LP claim to a Farkas
  certificate and checker.

### 15. Numerical Analysis

Current packs:

- `numerical-linear-algebra-v0`
- `finite-euler-method-v0`
- `bounded-dynamics-v0`
- `matrix-invariants-v0`
- `spectral-linear-algebra-v0`
- `finite-operator-v0`

Build next:

- Add concept rows for residual bound, solution box, iterative one-step
  contraction, Euler step, fixed-step error, interval bound, stability horizon,
  and floating-point honesty.
- Use exact rational shadows where possible; treat floating-point rows as
  reproducibility checks with explicit tolerance/seed metadata.
- Promote false residual/error rows through QF_LRA/Farkas when they are exact.

Graduation:

- Numerical rows distinguish exact rational certificate, finite deterministic
  computation, and approximate experiment.

### 16. Differential Equations And Dynamical Systems

Current packs:

- `bounded-dynamics-v0`
- `finite-euler-method-v0`
- `finite-hitting-times-v0`
- `finite-markov-chain-v0`

Build next:

- Add concept rows for recurrence trace, bounded invariant, threshold
  reachability, Euler transition, discrete flow, absorbing Markov chain, and
  existence/uniqueness horizon.
- Promote bad finite transitions, expected-time equations, and invariant
  failures through LRA/LIA or replay according to source shape.
- Keep continuous dynamics, PDEs, chaos, and existence/uniqueness theory as
  Lean-horizon.

Graduation:

- Dynamics pages state whether a row is a discrete bounded system, numerical
  step, stochastic finite system, or continuous theorem target.

### 17. Geometry

Current packs:

- `coordinate-geometry-v0`
- `affine-geometry-v0`
- `orientation-area-geometry-v0`
- `complex-plane-transforms-v0`

Build next:

- Add concept rows for midpoint, distance, collinearity, affine map, incidence,
  barycentric coordinate, signed area, orientation, determinant scaling,
  isometry shadow, and rigidity horizon.
- Promote false affine/distance/orientation claims through QF_LRA/Farkas or
  NRA when exact rational polynomial constraints suffice.
- Keep differential geometry, algebraic geometry, global geometry, and
  topology-heavy geometry as Lean-horizon.

Graduation:

- Geometry rows expose whether they are coordinate algebra checks or theorem
  reconstruction targets.

### 18. Functional Analysis And Operator Theory

Current packs:

- `finite-operator-v0`
- `inner-product-spaces-rational-v0`
- `finite-dual-spaces-v0`
- `finite-chebyshev-systems-v0`
- `spectral-linear-algebra-v0`
- `numerical-linear-algebra-v0`

Build next:

- Add concept rows for finite-dimensional norm, matrix operator, dual space,
  projection, Gram matrix, Chebyshev system, interpolation matrix,
  alternating residual, spectral decomposition, and Banach/Hilbert horizon.
- Promote finite-dimensional bad norm/operator/interpolation rows through
  QF_LRA/Farkas where exact rational constraints apply.
- Keep Banach-space theorems, compact operators, general Chebyshev spaces,
  projection theorem, and topological duals as Lean-horizon.

Graduation:

- Functional-analysis rows make finite-dimensional shadows useful without
  implying infinite-dimensional theorem coverage.

## Cross-Resource Build Plan

### SMT Fragment Atlas

Use the math curriculum as a source of fragment demand:

- Bool/CNF: logic, finite sets, graph coloring, topology set families.
- QF_BV: bounded naturals, residue arithmetic, finite fields, bit-level graph
  encodings.
- QF_LIA: integer equations, modular obstructions, exact counts, rank/count
  constraints.
- QF_LRA: rational inequalities, LP, probability tables, residual bounds.
- QF_NRA/RCF: algebraic real/complex/geometry/calculus shadows.
- QF_UF/Alethe: finite functions, congruence, homomorphisms, quotient maps.
- Quantifier finite expansion: finite predicate logic and bounded first-order
  examples.
- Lean horizon: induction, completeness, topology, measure, asymptotics.

Next work:

- Add fragment-demand back-links from field dashboards to atlas rows.
- Keep the generated
  [curriculum-pressure-by-fragment](generated/curriculum-pressure-by-fragment.md)
  view fresh as new route metadata and proof statuses land.

### Proof Certificate Cookbook

Use curriculum examples as canonical tiny recipes:

- CNF/LRAT: proposition refutation, graph non-colorability, finite cover miss.
- QF_BV: residue nonresidue, finite field/ring fixed-width contradiction.
- QF_LIA: gcd obstruction, exact count contradiction, rank coefficient miss.
- QF_LRA: infeasible linear system, LP threshold, bad probability table.
- QF_UF/Alethe: function single-valuedness, homomorphism preservation, quotient
  congruence.
- Lean horizon: induction schema, completeness theorem, compactness,
  measure-convergence theorem.

Next work:

- Add one tamper/rejection fixture per major route.
- Add a "math example using this route" section to each recipe.

### Rules, Law, And Policy Resources

The rules/law lane should reuse the math curriculum instead of inventing a
separate logic story:

| Math Resource | Rules/Law Reuse |
|---|---|
| finite predicates | eligibility conditions, facts, actors, resources |
| sets and relations | membership, roles, jurisdictions, obligations |
| graph reachability | workflow states, dependency chains, delegated authority |
| orders/lattices | precedence, hierarchy, classification levels |
| linear arithmetic | thresholds, benefits, tax brackets, deadlines |
| optimization | minimum/maximum entitlement, allocation, caps |
| probability/statistics | audit sampling, risk scoring, statistical evidence |
| proof routes | consistency, coverage, equivalence, monotonicity checks |

Detailed mapping:
[RULES-LAW-CROSSWALK.md](RULES-LAW-CROSSWALK.md) records the reusable check
shapes, source math packs, Axeyum fragments, proof routes, and the current
`benefit-eligibility-v0` mapping.

Next work:

- Extend the `benefit-eligibility-v0` Bool/QF_LIA proof harness from the landed
  consistency and monotonicity fixtures to coverage and bounded implementation
  equivalence.
- Reuse pack schema ideas before creating law-specific schema fields.
- Keep citations and source provenance mandatory for legal/policy examples.

### Complementary Software Libraries

Only build libraries after repeated manual work proves the need.

Candidate library modules:

| Library | Source Of Demand | First Contents |
|---|---|---|
| finite graph encoders | graph packs and solver regressions | coloring, reachability, cuts, matching |
| finite algebra encoders | algebra packs and QF_UF/BV tests | tables, homomorphisms, quotient maps |
| exact matrix fixtures | linear algebra, optimization, numerical rows | LU, rank, residual, eigenpair fixtures |
| finite probability tables | probability, statistics, measure rows | normalization, conditioning, kernels |
| proof-route fixtures | cookbook and resource regressions | tiny CNF, LIA, LRA, UF, BV examples |
| resource data accessors | repeated consumer scripts | typed concept/pack/proof-route views |

Boundary rule: do not create a crate until there are at least three duplicated
call sites or one external consumer.

## Prioritized Execution Queue

Pick one item per commit unless the change is purely navigational.

1. Landed: add concept rows for linear algebra computation families: LU,
   rank/nullity, residual bound, eigenpair, characteristic polynomial, and
   random-matrix finite moment.
2. Landed: add concept rows for algebra maps: homomorphism, kernel/image,
   quotient, ideal, module, tensor bilinearity, and group action.
3. Landed: add "math example using this route" sections to the six active
   proof cookbook recipes.
4. Landed: promote `finite-stochastic-kernels-v0` for a small exact-rational
   QF_LRA/Farkas bad-row normalization contradiction with strong learner value.
5. Landed: promote `finite-ideals-v0` for a quotient-ring representative
   congruence row that exercises equality of induced quotient addition beyond
   the existing bad-ideal closure family row.
6. Landed: add a rules/law crosswalk doc that maps finite predicates,
   arithmetic thresholds, graph reachability, precedence, and proof routes to
   policy/rule checks.
7. Add a consumer-query recipe for "find all packs for a field and route".
8. Add negative validator fixtures for one resource schema once the schema
   shape stops changing.
9. Audit `planned` vs `covered` statuses in the curriculum DAG and generated
    dashboards so status means current resource maturity, not historical state.
10. Add one route-specific tamper/rejection test per proof certificate route.
11. Revisit the library boundary decision after the next five solver-reuse
    promotions and at least one downstream consumer use.

## Validation Checklist

For plan-only documentation:

```sh
git diff --check
./scripts/check-links.sh
```

For ontology, pack, or dashboard changes:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For proof-route promotions, add the focused route-specific cargo regression
before updating metadata or status.

## What Not To Do

- Do not add broad textbook prose without a checkable pack or horizon row.
- Do not call a bounded example a general theorem.
- Do not promote solver reuse without a regression, fuzz seed, benchmark slice,
  or explicit non-benchmark-horizon back-link.
- Do not split a new crate or repository before repeated consumers exist.
- Do not let law/policy/rules examples become legal advice or unsupported
  natural-language parsing claims.
