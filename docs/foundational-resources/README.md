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
