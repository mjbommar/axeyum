# 249 — Separated concept coverage projection

The first F5 coverage view is derived from three distinct sources: the frozen
Mathlib fact catalog, the reviewed family-topic crosswalk, and fact-level
`formalizes` links in the overlay. It reports their dimensions separately.

The current view has 14 pinned concepts. Nine have family-topic coverage across
214 catalog facts; seven have at least one qualified fact-level formalization,
covering ten facts. These are intentionally not summed into a completion score.
A family classification tells retrieval what a cluster is about; a qualified
fact-level edge identifies a precise formal law; neither makes a pedagogical
concept fully covered.

The projection records source digests and rejects duplicate concepts, invented
counts, and a topic-only concept marked as fact-formalized. It is a reporting
and ranking input only.

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_concept_coverage_projection
python3 scripts/validate-autogenesis-concept-coverage-projection.py
python3 scripts/gen-autogenesis-concept-coverage-projection.py --check
just autogenesis-concept-coverage
```
