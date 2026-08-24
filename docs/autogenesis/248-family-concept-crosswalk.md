# 248 — Reviewed family-to-concept crosswalk

`family-concept-crosswalk-v1.json` joins the twelve frozen, outcome-blind
Mathlib fact families to pinned `math-education` concept identifiers. It is
deliberately a **family-topic** classification: it says that the `natural-gcd`
family concerns greatest-common-divisor mathematics, not that every individual
fact is a complete formalization of that concept.

The crosswalk is a small human-reviewed bridge between two existing sources:
the frozen fact catalog and the pinned read-only education graph. It records
both source identities, requires exactly one mapping for every catalog family,
and rejects unknown families, duplicate classifications, or a changed external
revision. It neither reads proof bodies nor changes facts, operations, or the
external project.

The capability-gap projection consumes this bridge only to label its existing
family/shape clusters. That gives planning and retrieval a stable mathematical
topic without promoting a pedagogical association into a proof or admission
claim.

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_family_concept_crosswalk
python3 scripts/validate-autogenesis-family-concept-crosswalk.py
just autogenesis-family-concepts
```
