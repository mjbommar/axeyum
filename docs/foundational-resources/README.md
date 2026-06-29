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
- [`artifacts/examples/math/proof-methods-refutation-v0/`](../../artifacts/examples/math/proof-methods-refutation-v0/)
  is the first substantive math pack: proof-by-refutation over finite
  pigeonhole examples, with the UNSAT proof route still marked as a proof gap.
- [`artifacts/examples/math/modular-arithmetic-v0/`](../../artifacts/examples/math/modular-arithmetic-v0/)
  validates small CRT, modular inverse, composite non-unit, and Fermat-style
  finite checks by replay/exhaustive search.
- [`artifacts/examples/math/rationals-lra-v0/`](../../artifacts/examples/math/rationals-lra-v0/)
  validates exact rational density, additive inverse, trichotomy, and
  transitivity checks using rational replay.
- [`artifacts/examples/math/linear-algebra-rational-v0/`](../../artifacts/examples/math/linear-algebra-rational-v0/)
  validates exact rational matrix-vector solution replay, LU factorization
  replay, and a row-scaling inconsistency certificate for a singular system.
- [`artifacts/examples/math/graph-coloring-v0/`](../../artifacts/examples/math/graph-coloring-v0/)
  validates finite graph coloring witnesses, invalid-coloring replay, and an
  exhaustive two-colorability refutation for `K3`.
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

Validation commands:

```sh
python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/gen-foundational-dashboards.py
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
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
