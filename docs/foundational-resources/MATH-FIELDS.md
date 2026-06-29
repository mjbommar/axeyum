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
| `logic_and_proof` | Logic and proof | Foundation for every other field | Propositional logic, SAT, tiny SMT examples, proof object anatomy | Quantified logic, induction-heavy metatheory, and full proof-assistant automation need the Lean bridge. |
| `set_theory_and_foundations` | Set theory and foundations | Foundation / early proof course / graduate logic | Finite sets, relations, functions, partitions, small cardinality constraints | ZFC, ordinals, cardinals, choice, and infinite set facts are proof-horizon material. |
| `discrete_math` | Discrete mathematics and combinatorics | Core undergraduate bridge into CS and proof | Finite counting identities, bounded pigeonhole checks, recurrence examples, combinatorial search | General asymptotic enumeration and deep extremal combinatorics usually require theorem proving. |
| `graph_theory` | Graph theory | Core undergraduate / graduate combinatorics | Coloring, reachability, matching, cuts, small counterexample graphs, causal d-separation | Graph minors, extremal graph theory, and asymptotic families are mostly proof-horizon. |
| `number_theory` | Number theory | Core undergraduate / graduate algebra and arithmetic | Modular arithmetic, congruences, finite-field examples, bounded Diophantine checks | Analytic and algebraic number theory are not near-term SMT targets. |
| `linear_algebra` | Linear algebra | Core undergraduate / graduate prerequisite | Matrix identities, LU decomposition, rank, inconsistent systems, finite-field linear algebra | Spectral theorems, general vector-space theorems, and conditioning/stability need proof or numerical tracks. |
| `abstract_algebra` | Abstract algebra | Core undergraduate / graduate algebra | Finite groups, rings, fields, homomorphism tables, Cayley-table validators | General group/ring/module/category theory belongs in Lean-backed concept rows. |
| `real_analysis` | Real analysis | Core proof-based undergraduate / graduate analysis | Rational witnesses, inequalities, algebraic real constraints, bounded epsilon-delta templates | General completeness, limits, continuity, compactness, and convergence proofs need Lean reconstruction. |
| `complex_analysis` | Complex analysis | Graduate bridge from real analysis and algebra | Polynomial identities, finite evaluations, algebraic constraints over real/imaginary parts | Holomorphicity, contour integration, residues, and analytic continuation are proof-horizon. |
| `topology` | Topology | Graduate bridge for analysis and geometry | Finite topologies, metric-ball examples, closure/interior checks in finite spaces | General topological spaces, compactness, connectedness, and homotopy are proof-horizon. |
| `measure_theory` | Measure theory | Graduate analysis / probability foundation | Finite measures, sigma-algebra sanity checks over finite universes, exact finite probability | Lebesgue measure, integration, convergence theorems, and almost-everywhere reasoning need Lean. |
| `probability_theory` | Probability theory | Undergraduate / graduate applied and pure math | Finite probability tables, conditional probability, Bayes rule, exact discrete distributions | Continuous distributions, stochastic processes, and limit theorems are mostly proof or numerical-honesty tracks. |
| `statistics` | Statistics | Undergraduate / graduate applied math and data science | Descriptive statistics, contingency tables, exact finite tests, small Bayesian tables | Floating-point inference, MCMC, VI, and model calibration are reproducibility claims, not proof claims. |
| `optimization_and_convexity` | Optimization and convexity | Undergraduate / graduate applied math | LP feasibility, linear certificates, small quadratic/convexity checks, monotonicity/threshold examples | General convex analysis, SDP, duality theorems, and algorithm convergence need broader proof support. |
| `numerical_analysis` | Numerical analysis | Undergraduate / graduate applied math | Interval bounds, fixed-step error recurrences, floating-point sanity checks, exact rational shadows | Stability and convergence theorems need proof support; floating-point experiments need tolerances and seeds. |
| `differential_equations_and_dynamical_systems` | Differential equations and dynamical systems | Undergraduate / graduate applied math | Bounded transition systems, linear recurrences, invariant checks, discretized systems | Existence/uniqueness, continuous dynamics, chaos, and PDE theory are proof-horizon. |
| `geometry` | Geometry | Undergraduate / graduate pure and applied math | Coordinate geometry, incidence constraints, distances, rigid small configurations | Differential, algebraic, and global geometry are mostly proof-assistant material. |
| `functional_analysis_and_operator_theory` | Functional analysis and operator theory | Graduate analysis / numerical analysis foundation | Finite-dimensional normed spaces, operator matrices, approximation examples, Chebyshev polynomial slices | Banach/Hilbert-space theorems, compact operators, and general Chebyshev spaces need Lean/mathlib-scale support. |

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
| Delta-epsilon balls and limits | `real_analysis`, `topology`, `logic_and_proof` | Check bounded rational witnesses/counterexamples, metric-ball inclusions in finite/rational examples, and algebraic side-conditions. | A quantified-real story, Lean-backed limit/topology lemmas, and examples that separate bounded evidence from general epsilon-delta theorems. |
| Chebyshev spaces | `functional_analysis_and_operator_theory`, `numerical_analysis`, `linear_algebra`, `real_analysis` | Check finite-dimensional polynomial bases, interpolation matrices, sign-pattern examples, and small approximation identities. | General function-space definitions, Haar/Chebyshev-system theorems, compactness/continuity lemmas, and proof-assistant reconstruction. |
| Graph coloring | `graph_theory`, `discrete_math`, `logic_and_proof` | Encode finite coloring as SAT/SMT, produce colorings as models, and produce unsat evidence for small non-colorability examples when proof routes exist. | A graph example-pack schema, graph-to-SMT compiler metadata, and proof recipes for unsat coloring certificates. |
| BFS vs DFS pathological runtime | `discrete_math`, `graph_theory`; companion CS algorithms track | Generate finite graph families, replay traversal traces, compare visited orders/cost counters, and find small worst-case witnesses. | A CS algorithms resource track, executable traversal semantics, asymptotic/runtime-proof rows, and Lean-backed recurrence/asymptotic lemmas. |
| Random matrix theory | `probability_theory`, `statistics`, `linear_algebra`, `functional_analysis_and_operator_theory` | Check exact small random-matrix distributions by enumeration, determinant/rank/eigenvalue constraints for fixed matrices, and finite sampling invariants. | Measure/probability formalization, asymptotic limit-theorem rows, numerical experiment metadata, and clear "not proof" status for simulations. |
| LU decomposition | `linear_algebra`, `numerical_analysis` | Verify `A = L * U` for exact fixed matrices, find singular/pivoting counterexamples, and check inconsistent linear systems with certificates. | Matrix example packs, pivoting/stability metadata, determinant/rank theorem reconstruction, and numerical error-bound resources. |

## First Example Packs To Create

1. `artifacts/examples/math/graph-coloring-v0/`
   - Fields: `graph_theory`, `discrete_math`, `logic_and_proof`.
   - Checks: satisfiable coloring witness, unsatisfiable small coloring claim,
     model replay, proof-route status.
2. `artifacts/examples/math/linear-algebra-rational-v0/`
   - Fields: `linear_algebra`, `numerical_analysis`.
   - Checks: matrix multiplication identity, LU factorization replay,
     inconsistent system certificate.
3. `artifacts/examples/math/finite-probability-v0/`
   - Fields: `probability_theory`, `statistics`, `measure_theory`.
   - Checks: total mass, conditional probability, Bayes table, exact rational
     replay.
4. `artifacts/examples/math/descriptive-statistics-v0/`
   - Fields: `statistics`, `probability_theory`, `linear_algebra`.
   - Checks: mean/variance identity, contingency-table margins, Simpson's
     paradox count-table witness.
5. `artifacts/examples/math/linear-optimization-v0/`
   - Fields: `optimization_and_convexity`, `linear_algebra`, `real_analysis`.
   - Checks: LP feasibility witness, objective-threshold replay, Farkas
     infeasibility certificate.
6. `artifacts/examples/math/modular-arithmetic-v0/`
   - Fields: `number_theory`, `abstract_algebra`.
   - Checks: modular inverse examples, small finite-field equations,
     bounded Diophantine examples.
7. `artifacts/examples/math/real-analysis-rational-v0/`
   - Fields: `real_analysis`, `logic_and_proof`.
   - Checks: rational inequalities, interval inclusions, bounded
     epsilon-delta templates with proof-horizon labels.

## Graduation Criteria

This taxonomy becomes more than a planning note when:

- `foundational-concepts.schema.json` validates `field_id` against this list;
- at least one Band A example pack validates end to end;
- each field has at least one concept row, even if the row is proof-horizon;
- every Band A field has one runnable example or an explicit near-term backlog
  item;
- generated dashboards can report coverage by field, decidability status, and
  proof/replay route.
