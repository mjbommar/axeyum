# Foundational Resource Expansion

This folder plans a broader sibling-resource ecosystem for foundational
mathematics, computer science, logic, and statistics.

It extends the existing [formal mathematics curriculum](../curriculum/README.md)
without replacing it. The curriculum remains the current machine-readable math
DAG; this folder is the expansion plan for adjacent resource families,
schemas, examples, and validation workflows.

## Files

- [SOURCES.md](SOURCES.md) records the web, GitHub, and shallow-clone research
  used to ground the plan.
- [MATH-FIELDS.md](MATH-FIELDS.md) defines the university-style mathematics
  field taxonomy that seeds the Foundational Concept Atlas.
- [MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) is the detailed
  buildout plan from the current curriculum DAG to atlas rows, example packs,
  lessons, proof hooks, dashboards, and eventual library boundaries.
- [ROADMAP.md](ROADMAP.md) is the implementation roadmap.
- [../learn/math/README.md](../learn/math/README.md) is the learner-facing
  math path built from the curriculum, concept atlas, and validated packs.
- [generated/math-coverage.md](generated/math-coverage.md) is generated
  curriculum-node coverage from the current concept atlas.
- [generated/math-field-dashboard.md](generated/math-field-dashboard.md) is
  generated field coverage from the current concept atlas.
- [generated/proof-gap-dashboard.md](generated/proof-gap-dashboard.md) is the
  generated proof/evidence gap view.

## Current Machine-Readable Artifacts

- [`artifacts/ontology/foundational-concepts.schema.json`](../../artifacts/ontology/foundational-concepts.schema.json)
  defines the seed concept-atlas row shape.
- [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json)
  currently contains 23 curriculum rows and 18 math-field rows.
- [`scripts/gen-foundational-concepts.py`](../../scripts/gen-foundational-concepts.py)
  regenerates the seed atlas from the curriculum DAG and field/buildout maps.
- [`scripts/validate-foundational-concepts.py`](../../scripts/validate-foundational-concepts.py)
  validates row shape, curriculum alignment, field IDs, links, and proof/pack
  metadata.
- [`scripts/gen-foundational-dashboards.py`](../../scripts/gen-foundational-dashboards.py)
  regenerates the Markdown dashboards under `generated/`.
- [`artifacts/ontology/foundational-example-pack.schema.json`](../../artifacts/ontology/foundational-example-pack.schema.json)
  defines the example-pack metadata and expected-result shape.
- [`scripts/validate-foundational-example-pack.py`](../../scripts/validate-foundational-example-pack.py)
  validates foundational math example-pack folders.
- [`artifacts/examples/math/template-v0/`](../../artifacts/examples/math/template-v0/)
  is the validating template for future math packs.
- [`artifacts/examples/math/logic-basics-v0/`](../../artifacts/examples/math/logic-basics-v0/)
  validates propositional SAT witness replay, tautology/contradiction
  truth-table checks, De Morgan equivalence, and a tiny CNF refutation by
  enumeration.
- [`artifacts/examples/math/finite-predicate-v0/`](../../artifacts/examples/math/finite-predicate-v0/)
  validates finite-domain universal and existential predicate replay, a bounded
  non-empty `forall -> exists` enumeration row, finite relation asymmetry, and a
  general first-order Lean-horizon row.
- [`artifacts/examples/math/proof-methods-refutation-v0/`](../../artifacts/examples/math/proof-methods-refutation-v0/)
  is the first substantive math pack: proof-by-refutation over finite
  pigeonhole examples, with `PHP(2,2)` witness replay and `PHP(3,2)` checked
  by deterministic CNF truth-table enumeration. LRAT/DRAT remains the
  proof-object graduation target.
- [`artifacts/examples/math/induction-obligations-v0/`](../../artifacts/examples/math/induction-obligations-v0/)
  validates bounded induction base, step, and conclusion obligations while
  keeping the full induction schema under Lean horizon.
- [`artifacts/examples/math/finite-sets-v0/`](../../artifacts/examples/math/finite-sets-v0/),
  [`artifacts/examples/math/relations-functions-v0/`](../../artifacts/examples/math/relations-functions-v0/),
  and [`artifacts/examples/math/finite-cardinality-v0/`](../../artifacts/examples/math/finite-cardinality-v0/)
  validate the finite foundations path: finite set identities, relation and
  function tables, finite bijections, finite cardinal inequalities, bounded
  injection/surjection refutations, and an explicit infinite-cardinality
  Lean-horizon row.
- [`artifacts/examples/math/natural-arithmetic-v0/`](../../artifacts/examples/math/natural-arithmetic-v0/),
  [`artifacts/examples/math/integer-lia-v0/`](../../artifacts/examples/math/integer-lia-v0/),
  [`artifacts/examples/math/gcd-bezout-v0/`](../../artifacts/examples/math/gcd-bezout-v0/),
  and [`artifacts/examples/math/number-theory-v0/`](../../artifacts/examples/math/number-theory-v0/)
  validate the core arithmetic path with bounded natural arithmetic, integer
  LIA witnesses, gcd/Bezout replay, and bounded number-theory checks.
- [`artifacts/examples/math/modular-arithmetic-v0/`](../../artifacts/examples/math/modular-arithmetic-v0/)
  validates small CRT, modular inverse, composite non-unit, and Fermat-style
  finite checks by replay/exhaustive search.
- [`artifacts/examples/math/rationals-lra-v0/`](../../artifacts/examples/math/rationals-lra-v0/)
  validates exact rational density, additive inverse, trichotomy, and
  transitivity checks using rational replay.
- [`artifacts/examples/math/reals-rcf-shadow-v0/`](../../artifacts/examples/math/reals-rcf-shadow-v0/)
  validates exact ordered-field replay, nonlinear product replay, a quadratic
  real-root witness, two tiny quadratic infeasibility checks, and a
  real-completeness Lean-horizon row.
- [`artifacts/examples/math/sequence-limit-shadow-v0/`](../../artifacts/examples/math/sequence-limit-shadow-v0/)
  validates bounded epsilon-tail replay, finite limit counterexamples,
  monotone bounded prefixes, a fixed geometric partial-sum identity, a bounded
  finite Cauchy-tail check, and a general convergence Lean-horizon row.
- [`artifacts/examples/math/calculus-algebraic-shadow-v0/`](../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
  validates polynomial derivative replay, a product-rule polynomial identity,
  tangent-line replay, a convex quadratic critical point, false-derivative
  rejection, and a general calculus Lean-horizon row.
- [`artifacts/examples/math/linear-algebra-rational-v0/`](../../artifacts/examples/math/linear-algebra-rational-v0/)
  validates exact rational matrix-vector solution replay, LU factorization
  replay, and a row-scaling inconsistency certificate for a singular system.
- [`artifacts/examples/math/numerical-linear-algebra-v0/`](../../artifacts/examples/math/numerical-linear-algebra-v0/)
  validates exact residual bounds, rational solution boxes, Jacobi one-step
  contraction replay, and checked rejection of a false residual bound.
- [`artifacts/examples/math/finite-groups-v0/`](../../artifacts/examples/math/finite-groups-v0/),
  [`artifacts/examples/math/finite-rings-v0/`](../../artifacts/examples/math/finite-rings-v0/),
  [`artifacts/examples/math/finite-fields-v0/`](../../artifacts/examples/math/finite-fields-v0/),
  [`artifacts/examples/math/polynomial-identities-v0/`](../../artifacts/examples/math/polynomial-identities-v0/),
  and [`artifacts/examples/math/counting-v0/`](../../artifacts/examples/math/counting-v0/)
  validate the finite algebra and discrete core: finite group/ring/field table
  checks, fixed polynomial identities, and finite counting/pigeonhole rows.
- [`artifacts/examples/math/graph-coloring-v0/`](../../artifacts/examples/math/graph-coloring-v0/)
  validates finite graph coloring witnesses, invalid-coloring replay, and an
  exhaustive two-colorability refutation for `K3`.
- [`artifacts/examples/math/graph-reachability-v0/`](../../artifacts/examples/math/graph-reachability-v0/)
  validates finite BFS shortest-distance replay, deterministic DFS traversal
  replay, disconnected no-path refutation, and edge-cut separation replay.
- [`artifacts/examples/math/graph-matching-v0/`](../../artifacts/examples/math/graph-matching-v0/)
  validates finite matching witnesses, invalid-overlap rejection,
  augmenting-path flip replay, and a perfect-matching obstruction by
  exhaustive enumeration.
- [`artifacts/examples/math/graph-d-separation-v0/`](../../artifacts/examples/math/graph-d-separation-v0/)
  validates finite DAG d-separation checks for chains, forks, colliders, and
  descendant-opened colliders.
- [`artifacts/examples/math/graph-cut-v0/`](../../artifacts/examples/math/graph-cut-v0/)
  validates finite minimum edge-cut and vertex-cut certificates, plus checked
  rejection of non-separating one-edge and one-vertex cuts.
- [`artifacts/examples/math/finite-probability-v0/`](../../artifacts/examples/math/finite-probability-v0/)
  validates exact finite probability mass tables, conditional probability, and
  Bayes posterior replay.
- [`artifacts/examples/math/descriptive-statistics-v0/`](../../artifacts/examples/math/descriptive-statistics-v0/)
  validates exact mean/variance identities, contingency-table margins, and a
  Simpson's paradox count-table witness.
- [`artifacts/examples/math/linear-optimization-v0/`](../../artifacts/examples/math/linear-optimization-v0/)
  validates exact LP feasibility witnesses, objective-threshold replay, and a
  tiny checked Farkas infeasibility certificate.
- [`artifacts/examples/math/coordinate-geometry-v0/`](../../artifacts/examples/math/coordinate-geometry-v0/)
  validates exact midpoint, collinearity, and squared-distance coordinate
  checks.
- [`artifacts/examples/math/finite-topology-v0/`](../../artifacts/examples/math/finite-topology-v0/)
  validates finite topology axioms, closure/interior computation, and exact
  finite metric-ball replay.
- [`artifacts/examples/math/finite-measure-v0/`](../../artifacts/examples/math/finite-measure-v0/)
  validates finite sigma-algebra axioms, exact finite additivity, and
  event/complement measure replay.
- [`artifacts/examples/math/bounded-dynamics-v0/`](../../artifacts/examples/math/bounded-dynamics-v0/)
  validates exact rational recurrence traces, bounded invariant witnesses, and
  threshold reachability replay.
- [`artifacts/examples/math/finite-operator-v0/`](../../artifacts/examples/math/finite-operator-v0/)
  validates exact finite-dimensional norm, matrix-operator, and Chebyshev
  recurrence checks.
- [`artifacts/examples/math/complex-algebraic-v0/`](../../artifacts/examples/math/complex-algebraic-v0/)
  validates exact complex arithmetic, conjugate/norm replay, and a fixed
  polynomial-root witness using real-pair algebra.

Validation commands:

```sh
python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/gen-foundational-dashboards.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

## Principle

Every resource should reinforce Axeyum's core identity:

```text
untrusted fast search, trusted small checking
```

For educational and knowledge artifacts, that means:

- distinguish concept maps from executable examples;
- mark decidable, bounded, computable, and proof-assistant-only material;
- replay every concrete witness;
- require checkable evidence for `unsat` examples when possible;
- keep generated or machine-readable data validated by scripts.
