# University Math Field Taxonomy

This is the planning spine for the mathematics side of the
[Foundational Resource Expansion](README.md). It defines the fields that the
Foundational Concept Atlas should cover before we start adding many individual
concept rows or example packs.

The taxonomy is deliberately coarse. It is not a replacement for MSC2020,
Mathlib, or a university course catalog; it is the Axeyum-facing layer between
those sources and our concrete artifacts:

```text
math field -> concept row -> runnable example -> replay/proof status
```

## Source Grounding

Use these sources as checks against local taste:

- The existing Axeyum [formal mathematics curriculum](../curriculum/README.md)
  and [curriculum graph](../curriculum/curriculum.toml).
- [MSC2020](https://mathscinet.ams.org/mathscinet/msc/msc2020.html), maintained by
  Mathematical Reviews and zbMATH, as the broad research taxonomy.
- The MIT Mathematics department and catalog pages as a university curriculum
  sanity check: undergraduate and graduate mathematics span pure areas such as
  algebra, analysis, geometry, and topology plus applied areas such as
  combinatorics, computational science, theoretical CS, and probability and
  statistics.
  - [MIT Mathematics department overview](https://catalog.mit.edu/schools/science/mathematics/)
  - [MIT Course 18 catalog](https://catalog.mit.edu/subjects/18/)
- [Lean Mathlib overview](https://leanprover-community.github.io/mathlib-overview.html)
  and [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  as formalization and proof-assistant curriculum cross-checks.

## Field Set

| ID | Field | Curriculum Role | First Axeyum Slice | Proof Horizon / Limits |
|---|---|---|---|---|
| `logic_and_proof` | Logic and proof | Foundation for every other field | Propositional logic, SAT, finite proof-pattern checks, finite order counterexamples, tiny SMT examples, proof object anatomy | Quantified logic, induction-heavy metatheory, and full proof-assistant automation need the Lean bridge. |
| `set_theory_and_foundations` | Set theory and foundations | Foundation / early proof course / graduate logic | Finite sets, relations, functions, monoids as closed function-composition tables, permutation groups as bijective function tables, group actions as function tables, equivalence classes, partitions, order/lattice tables, small cardinality constraints | ZFC, ordinals, cardinals, choice, infinite set facts, and complete-lattice theorems are proof-horizon material. |
| `discrete_math` | Discrete mathematics and combinatorics | Core undergraduate bridge into CS and proof | Finite counting identities, finite permutations/cycle types, finite transformation monoids, group-action orbit counts, bounded pigeonhole checks, recurrence examples, finite order/lattice checks, combinatorial search | General asymptotic enumeration and deep extremal/order-theoretic combinatorics usually require theorem proving. |
| `graph_theory` | Graph theory | Core undergraduate / graduate combinatorics | Coloring, reachability, traversal cost counters, matching, cuts, small counterexample graphs, causal d-separation | Graph minors, extremal graph theory, and asymptotic families are mostly proof-horizon. |
| `number_theory` | Number theory | Core undergraduate / graduate algebra and arithmetic | Modular arithmetic, congruences, finite-field examples, finite ideals in modular rings, bounded Diophantine checks | Analytic and algebraic number theory are not near-term SMT targets. |
| `linear_algebra` | Linear algebra | Core undergraduate / graduate prerequisite | Matrix identities, LU decomposition, rank, inconsistent systems, finite vector spaces, finite dual spaces, exact rational inner products, finite modules, tensor products, subspaces, finite-field linear algebra, Jacobians, and Hessians | Spectral theorems, general vector-space/dual-space/inner-product/module/tensor theorems, and conditioning/stability need proof or numerical tracks. |
| `abstract_algebra` | Abstract algebra | Core undergraduate / graduate algebra | Finite groups, permutation groups, monoids, group actions, rings, fields, ideals, modules, dual spaces, tensor products, homomorphism tables, polynomial factorization slices, Cayley-table validators | General group/permutation/monoid/ring/ideal/module/duality/tensor/category, arbitrary group-action theory, and arbitrary-field factorization theory belongs in Lean-backed concept rows. |
| `real_analysis` | Real analysis | Core proof-based undergraduate / graduate analysis | Rational witnesses, inequalities, algebraic real constraints, rational polynomial factorization shadows, bounded epsilon-delta templates, and exact multivariable polynomial derivative shadows | General completeness, limits, continuity, compactness, differentiability, and convergence proofs need Lean reconstruction. |
| `complex_analysis` | Complex analysis | Graduate bridge from real analysis and algebra | Polynomial identities, finite evaluations, rational factorization shadows, algebraic constraints over real/imaginary parts | Holomorphicity, contour integration, residues, analytic continuation, and algebraic closure need proof-horizon support. |
| `topology` | Topology | Graduate bridge for analysis and geometry | Finite topologies, metric-ball examples, closure/interior checks, continuous-map preimages, and finite simplicial-homology rank replay | General topological spaces, compactness, connectedness, homotopy, and homology invariance are proof-horizon. |
| `measure_theory` | Measure theory | Graduate analysis / probability foundation | Finite measures, sigma-algebra sanity checks, product measures, random variables, conditional expectations, finite stochastic kernels, finite martingales, finite hitting times, finite concentration/tail bounds, simple-function integrals, and exact finite probability | Lebesgue measure, convergence theorems, and almost-everywhere reasoning need Lean. |
| `probability_theory` | Probability theory | Undergraduate / graduate applied and pure math | Finite probability tables, random variables, conditional expectation, finite stochastic kernels, finite martingales, finite hitting times, finite concentration/tail bounds, conditional probability, Bayes rule, finite expectations, product tables, and exact discrete distributions | Continuous distributions, stochastic processes, concentration inequalities, and limit theorems are mostly proof or numerical-honesty tracks. |
| `statistics` | Statistics | Undergraduate / graduate applied math and data science | Descriptive statistics, contingency tables, exact finite tests, finite stochastic-kernel checks, finite hitting-time checks, finite martingale checks, finite concentration checks, small Bayesian tables | Floating-point inference, MCMC, VI, and model calibration are reproducibility claims, not proof claims. |
| `optimization_and_convexity` | Optimization and convexity | Undergraduate / graduate applied math | LP feasibility, linear certificates, finite rational convexity checks, gradients, Hessian minors, small quadratic checks, monotonicity/threshold examples | General convex analysis, SDP, duality theorems, and algorithm convergence need broader proof support. |
| `numerical_analysis` | Numerical analysis | Undergraduate / graduate applied math | Interval bounds, fixed-step error recurrences, Jacobian/Hessian replay, floating-point sanity checks, exact rational shadows | Stability and convergence theorems need proof support; floating-point experiments need tolerances and seeds. |
| `differential_equations_and_dynamical_systems` | Differential equations and dynamical systems | Undergraduate / graduate applied math | Bounded transition systems, linear recurrences, invariant checks, discretized systems | Existence/uniqueness, continuous dynamics, chaos, and PDE theory are proof-horizon. |
| `geometry` | Geometry | Undergraduate / graduate pure and applied math | Coordinate geometry, incidence constraints, distances, rigid small configurations | Differential, algebraic, and global geometry are mostly proof-assistant material. |
| `functional_analysis_and_operator_theory` | Functional analysis and operator theory | Graduate analysis / numerical analysis foundation | Finite-dimensional normed spaces, finite inner-product/projection examples, finite dual-space and operator-matrix examples, approximation examples, Chebyshev polynomial slices, finite Chebyshev-system grids | Banach/Hilbert-space theorems, Hilbert projection theorem, topological duals, compact operators, and general Chebyshev spaces need Lean/mathlib-scale support. |

## Priority Bands

### Band A: Build First

These fields have immediate finite, quantifier-free, or certificate-friendly
examples that reinforce Axeyum's current strengths:

- `logic_and_proof`
- `set_theory_and_foundations` for finite sets and relations
- `discrete_math`
- `graph_theory`
- `number_theory` for modular arithmetic and finite fields
- `linear_algebra` for fixed exact matrices
- `probability_theory` for finite probability
- `statistics` for exact finite/descriptive examples
- `optimization_and_convexity` for LP-style examples

### Band B: Build After The Atlas Validator Exists

These fields are valuable soon, but they need tighter schemas so we do not
overstate bounded examples as general theorems:

- `abstract_algebra`
- `real_analysis`
- `numerical_analysis`
- `differential_equations_and_dynamical_systems`
- `geometry`

### Band C: Mark As Proof Horizon First

These fields should appear in the atlas early so users see the shape of the
roadmap, but most interesting claims are not near-term solver claims:

- `complex_analysis`
- `topology`
- `measure_theory` beyond finite universes
- `functional_analysis_and_operator_theory` beyond finite-dimensional slices

## Impact On The Concept Atlas

Every math concept row in the planned `foundational-concepts.json` should carry:

- `field_id`: one of the IDs above;
- `curriculum_tier`: foundation, core-undergrad, grad-bridge, graduate, or
  applied;
- `decidability`: decidable, computable, bounded, numerical, or proof-horizon;
- `axeyum_fragments`: SMT/IR/proof routes used for concrete checks;
- `example_packs`: runnable examples or planned example packs;
- `proof_routes`: replay, SAT proof, Farkas certificate, Lean reconstruction,
  or explicit proof gap;
- `source_refs`: local docs plus upstream references;
- `open_gaps`: what must be built before broader claims are honest.

The atlas should not contain a bare concept name. Each concept needs at least
one of:

- a concrete runnable example;
- a planned example pack with an owner and validation rule;
- a proof-horizon marker with the missing proof/reconstruction dependency.

## Backwards From Representative Questions

| Question Family | Fields | What Axeyum Can Do First | What We Still Need |
|---|---|---|---|
| Delta-epsilon balls and limits | `real_analysis`, `topology`, `logic_and_proof` | Check `real-analysis-rational-v0` bounded rational interval/ball inclusions, finite epsilon-delta witnesses/counterexamples, and algebraic side-conditions. | A quantified-real story, Lean-backed limit/topology lemmas, and examples that separate bounded evidence from general epsilon-delta theorems. |
| Chebyshev spaces | `functional_analysis_and_operator_theory`, `numerical_analysis`, `linear_algebra`, `real_analysis` | Check `finite-chebyshev-systems-v0` finite-dimensional polynomial bases, interpolation matrices, sign-pattern examples, and small approximation identities. | General function-space definitions, Haar/Chebyshev-system theorems, compactness/continuity lemmas, and proof-assistant reconstruction. |
| Graph coloring | `graph_theory`, `discrete_math`, `logic_and_proof` | Encode finite coloring as SAT/SMT, produce colorings as models, and produce unsat evidence for small non-colorability examples when proof routes exist. | A graph example-pack schema, graph-to-SMT compiler metadata, and proof recipes for unsat coloring certificates. |
| BFS vs DFS pathological runtime | `discrete_math`, `graph_theory`; companion CS algorithms track | Check `graph-search-runtime-v0` finite shortcut-tail families, replay BFS/DFS target-discovery orders, compare visited-node counters, and reject false finite cost bounds. | A CS algorithms resource track, asymptotic/runtime-proof rows, and Lean-backed recurrence/asymptotic lemmas. |
| Random matrix theory | `probability_theory`, `statistics`, `linear_algebra`, `functional_analysis_and_operator_theory` | Check exact small random-matrix distributions by enumeration, determinant/rank/eigenvalue constraints for fixed matrices, and finite sampling invariants. | Measure/probability formalization, asymptotic limit-theorem rows, numerical experiment metadata, and clear "not proof" status for simulations. |
| LU decomposition | `linear_algebra`, `numerical_analysis` | Verify `A = L * U` for exact fixed matrices, find singular/pivoting counterexamples, and check inconsistent linear systems with certificates. | Matrix example packs, pivoting/stability metadata, determinant/rank theorem reconstruction, and numerical error-bound resources. |
| Simplicial homology | `topology`, `set_theory_and_foundations`, `linear_algebra`, `abstract_algebra` | Check `finite-simplicial-homology-v0` face-closure, oriented-boundary, `boundary^2 = 0`, and fixed Betti-rank rows by exact finite replay. | Lean-backed chain-complex and homology-functor formalization, homology invariance, exact sequences, homotopy equivalence, and proof reconstruction from rank certificates. |

## First Example Packs To Create

1. `artifacts/examples/math/graph-coloring-v0/`
   - Fields: `graph_theory`, `discrete_math`, `logic_and_proof`.
   - Checks: satisfiable coloring witness, unsatisfiable small coloring claim,
     model replay, proof-route status.
2. `artifacts/examples/math/graph-search-runtime-v0/`
   - Fields: `graph_theory`, `discrete_math`, `logic_and_proof`.
   - Checks: finite BFS/DFS target-discovery costs, shortcut-tail family
     counters, bad DFS-bound rejection, and an asymptotic-runtime Lean-horizon
     row.
3. `artifacts/examples/math/linear-algebra-rational-v0/`
   - Fields: `linear_algebra`, `numerical_analysis`.
   - Checks: matrix multiplication identity, LU factorization replay,
     inconsistent system certificate.
4. `artifacts/examples/math/finite-probability-v0/`
   - Fields: `probability_theory`, `statistics`, `measure_theory`.
   - Checks: total mass, conditional probability, Bayes table, exact rational
     replay.
5. `artifacts/examples/math/descriptive-statistics-v0/`
   - Fields: `statistics`, `probability_theory`, `linear_algebra`.
   - Checks: mean/variance identity, checked bad-variance rejection,
     contingency-table margins, checked bad total-count rejection, Simpson's
     paradox count-table witness.
6. `artifacts/examples/math/linear-optimization-v0/`
   - Fields: `optimization_and_convexity`, `linear_algebra`, `real_analysis`.
   - Checks: LP feasibility witness, objective-threshold replay, Farkas
     infeasibility certificate.
7. `artifacts/examples/math/coordinate-geometry-v0/`
   - Fields: `geometry`, `linear_algebra`, `real_analysis`.
   - Checks: midpoint, collinearity determinant, squared-distance replay,
     checked bad squared-distance rejection.
8. `artifacts/examples/math/finite-topology-v0/`
   - Fields: `topology`, `set_theory_and_foundations`, `real_analysis`.
   - Checks: finite topology axioms, closure/interior, metric-ball replay,
     checked missing-empty-set rejection.
9. `artifacts/examples/math/finite-measure-v0/`
   - Fields: `measure_theory`, `probability_theory`, `set_theory_and_foundations`.
   - Checks: finite sigma-algebra axioms, finite additivity, event/complement
     measure replay.
10. `artifacts/examples/math/finite-product-measure-v0/`
   - Fields: `measure_theory`, `probability_theory`, `statistics`, `real_analysis`.
   - Checks: finite product probability tables, marginals, rectangle measures,
     finite Fubini replay, bad product-probability rejection, and bad
     marginal rejection.
11. `artifacts/examples/math/finite-random-variables-v0/`
    - Fields: `probability_theory`, `statistics`, `measure_theory`,
      `real_analysis`, `set_theory_and_foundations`.
    - Checks: finite random-variable pushforwards, expectation through
      pushforward distributions, independence checks, bad pushforward
      rejection, and bad expectation-through-pushforward rejection.
12. `artifacts/examples/math/finite-conditional-expectation-v0/`
    - Fields: `probability_theory`, `statistics`, `measure_theory`,
      `real_analysis`, `set_theory_and_foundations`.
    - Checks: finite partition conditional expectations, law of total
      expectation, tower property replay, bad conditional-expectation
      rejection, and bad tower-property rejection.
13. `artifacts/examples/math/finite-martingales-v0/`
    - Fields: `probability_theory`, `statistics`, `measure_theory`,
      `real_analysis`, `set_theory_and_foundations`.
    - Checks: finite filtration adaptedness, martingale conditional
      expectations, square submartingale inequalities, bounded stopping-time
      replay, and bad martingale rejection.
14. `artifacts/examples/math/finite-stochastic-kernels-v0/`
    - Fields: `probability_theory`, `statistics`, `measure_theory`,
      `linear_algebra`, `differential_equations_and_dynamical_systems`,
      `set_theory_and_foundations`.
    - Checks: finite kernel normalization, pushforward distributions, joint
      factorization/disintegration, kernel composition, and QF_LRA/Farkas bad
      kernel-row rejection.
15. `artifacts/examples/math/finite-hitting-times-v0/`
    - Fields: `probability_theory`, `differential_equations_and_dynamical_systems`,
      `linear_algebra`, `statistics`, `measure_theory`,
      `set_theory_and_foundations`.
    - Checks: finite first-hit distributions, survival probabilities,
      absorption-probability equations, expected hitting-time equations, and
      bad expected-time rejection.
16. `artifacts/examples/math/finite-concentration-v0/`
    - Fields: `probability_theory`, `statistics`, `measure_theory`,
      `real_analysis`, `set_theory_and_foundations`.
    - Checks: finite Markov, Chebyshev, and union-bound replays, bad
      concentration-bound rejection, and a concentration/limit-theorem
      Lean-horizon row.
17. `artifacts/examples/math/bounded-dynamics-v0/`
    - Fields: `differential_equations_and_dynamical_systems`,
      `numerical_analysis`, `linear_algebra`.
    - Checks: recurrence trace replay, bounded invariant witness, threshold
      reachability witness.
18. `artifacts/examples/math/finite-operator-v0/`
    - Fields: `functional_analysis_and_operator_theory`, `linear_algebra`,
      `numerical_analysis`, `real_analysis`.
    - Checks: finite-dimensional norm replay, matrix operator bound,
      checked QF_LRA/Farkas bad `l1` norm and bad operator-bound rejection,
      and Chebyshev recurrence witness.
19. `artifacts/examples/math/finite-chebyshev-systems-v0/`
    - Fields: `functional_analysis_and_operator_theory`, `numerical_analysis`,
      `linear_algebra`, `real_analysis`.
    - Checks: finite Vandermonde unisolvence, interpolation replay,
      alternating residual signs, duplicate-node rejection, and a general
      Chebyshev-system Lean-horizon row.
20. `artifacts/examples/math/modular-arithmetic-v0/`
    - Fields: `number_theory`, `abstract_algebra`.
    - Checks: modular inverse examples, small finite-field equations,
      bounded Diophantine examples.
21. `artifacts/examples/math/real-analysis-rational-v0/`
    - Fields: `real_analysis`, `logic_and_proof`.
    - Checks: rational interval/ball inclusions, bounded epsilon-delta
      samples, polynomial side conditions, bad-delta rejection, and a
      general real-analysis Lean-horizon row.
22. `artifacts/examples/math/complex-algebraic-v0/`
    - Fields: `complex_analysis`, `linear_algebra`, `real_analysis`,
      `abstract_algebra`.
    - Checks: real-pair complex arithmetic, conjugate norm replay, checked
      QF_LRA/Farkas bad norm-squared rejection, and fixed polynomial-root
      witness.
23. `artifacts/examples/math/finite-simplicial-homology-v0/`
    - Fields: `topology`, `set_theory_and_foundations`, `linear_algebra`,
      `abstract_algebra`.
    - Checks: finite simplicial-complex closure, oriented-boundary replay,
      boundary-squared-zero replay, fixed Betti-rank replay, bad-boundary
      rejection, and a general homology Lean-horizon row.
24. `artifacts/examples/math/finite-algebra-homomorphisms-v0/`
    - Fields: `abstract_algebra`, `set_theory_and_foundations`.
    - Checks: finite group and ring homomorphism replay, kernel/image
      recomputation, quotient/induced-map replay, bad-homomorphism rejection,
      QF_UF/Alethe preservation and concrete bad-map rows, and a general
      isomorphism-theorem Lean-horizon row.
25. `artifacts/examples/math/finite-vector-spaces-v0/`
    - Fields: `linear_algebra`, `abstract_algebra`,
      `set_theory_and_foundations`.
    - Checks: finite vector-space table replay over `F2`, subspace/span
      replay, linear-map kernel/image replay, rank-nullity replay,
      bad-subspace rejection, and a general vector-space/module Lean-horizon
      row.
26. `artifacts/examples/math/finite-modules-v0/`
    - Fields: `abstract_algebra`, `linear_algebra`,
      `set_theory_and_foundations`.
    - Checks: finite module table replay over `Z/4Z`, submodule/span replay,
      module-homomorphism kernel/image replay, quotient-module replay,
      bad-submodule rejection, and a general module-theory Lean-horizon row.
27. `artifacts/examples/math/finite-ideals-v0/`
    - Fields: `abstract_algebra`, `number_theory`,
      `set_theory_and_foundations`.
    - Checks: finite ideal table replay over `Z/6Z`, principal ideal
      generation, ring-homomorphism kernel/image replay, quotient-ring replay,
      checked bad-ideal rejection, checked quotient representative congruence,
      and a general ideal-theory Lean-horizon row.
28. `artifacts/examples/math/finite-order-lattices-v0/`
    - Fields: `set_theory_and_foundations`, `discrete_math`,
      `logic_and_proof`.
    - Checks: finite partial-order replay, Boolean-lattice meet/join table
      replay, distributivity replay, monotone-map fixed-point replay,
      bad-order rejection, checked Bool/CNF bad top-element rejection, and a
      general order/lattice Lean-horizon row.
29. `artifacts/examples/math/multivariable-calculus-rational-v0/`
    - Fields: `real_analysis`, `linear_algebra`,
      `optimization_and_convexity`, `numerical_analysis`.
    - Checks: exact bivariate-polynomial value/gradient replay,
      directional derivative as a gradient dot product, Jacobian chain-rule
      replay, Hessian positive-definiteness by leading principal minors,
      bad-gradient rejection, and a general multivariable-calculus
      Lean-horizon row.
30. `artifacts/examples/math/finite-tensor-products-v0/`
    - Fields: `linear_algebra`, `abstract_algebra`,
      `set_theory_and_foundations`.
    - Checks: finite tensor-product basis/dimension replay over `F2`,
      bilinear-map table replay, universal-factorization shadow through a
      linear map, Kronecker-product replay, bad-bilinear-map rejection, and a
      general tensor-theory Lean-horizon row.
31. `artifacts/examples/math/finite-dual-spaces-v0/`
    - Fields: `linear_algebra`, `abstract_algebra`,
      `set_theory_and_foundations`,
      `functional_analysis_and_operator_theory`.
    - Checks: finite dual-space covector linearity over `F2`, pointwise dual
      operations, dual-basis pairings, annihilator recomputation,
      transpose-map replay, bad-covector rejection, and a general
      duality/functional-analysis Lean-horizon row.
32. `artifacts/examples/math/inner-product-spaces-rational-v0/`
    - Fields: `linear_algebra`, `functional_analysis_and_operator_theory`,
      `numerical_analysis`, `optimization_and_convexity`, `real_analysis`.
    - Checks: exact rational Gram matrices, positive-definite principal
      minors, fixed Cauchy-Schwarz replay, orthogonal projection replay,
      Gram-Schmidt replay, bad-inner-product and bad projection-orthogonality
      rejection, and a general
      Hilbert/inner-product-space Lean-horizon row.
33. `artifacts/examples/math/polynomial-factorization-rational-v0/`
    - Fields: `abstract_algebra`, `real_analysis`, `complex_analysis`.
    - Checks: exact rational factor-list product replay, polynomial long
      division, Euclidean GCD replay, square-free decomposition replay,
      irreducible-quadratic rejection by discriminant, and a general
      polynomial-factorization Lean-horizon row.
34. `artifacts/examples/math/finite-group-actions-v0/`
    - Fields: `abstract_algebra`, `discrete_math`,
      `set_theory_and_foundations`.
    - Checks: finite group-action law replay, orbit/stabilizer
      recomputation, orbit-stabilizer cardinality replay, Burnside fixed-point
      average replay, bad-action rejection, and a general group-action
      Lean-horizon row.
35. `artifacts/examples/math/finite-monoids-v0/`
    - Fields: `abstract_algebra`, `discrete_math`,
      `set_theory_and_foundations`.
    - Checks: finite monoid identity/associativity replay, transformation
      composition table replay from finite functions, unit and idempotent
      recomputation, bad non-associative table rejection, and a general
      monoid/semigroup Lean-horizon row.
36. `artifacts/examples/math/finite-permutation-groups-v0/`
    - Fields: `abstract_algebra`, `discrete_math`,
      `set_theory_and_foundations`.
    - Checks: `S3` permutation group law replay, composition-table replay from
      bijective function maps, cycle-length and sign homomorphism replay,
      natural action orbit/stabilizer replay, bad non-bijection rejection, and
      a general permutation-group Lean-horizon row.

## Graduation Criteria

This taxonomy becomes more than a planning note when:

- `foundational-concepts.schema.json` validates `field_id` against this list;
- at least one Band A example pack validates end to end;
- each field has at least one concept row, even if the row is proof-horizon;
- every Band A field has one runnable example or an explicit near-term backlog
  item;
- generated dashboards can report coverage by field, decidability status, and
  proof/replay route.
