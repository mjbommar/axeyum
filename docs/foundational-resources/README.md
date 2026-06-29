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

Validation commands:

```sh
python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/gen-foundational-dashboards.py
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
