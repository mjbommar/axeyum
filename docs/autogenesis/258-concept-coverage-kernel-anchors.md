# 258 — Three-dimensional concept coverage

Date: 2026-08-24

## Result

The generated concept-coverage projection now has three deliberately separate
dimensions:

| Dimension | Source population | Current count |
|---|---|---:|
| Family-topic membership | Train/development fact families | 157 fact memberships |
| Qualified fact formalization | Train/development fact ledger | 10 fact links across 7 concepts |
| Reviewed kernel semantic anchors | Accepted empty-footprint kernel theorems | 6 anchors across 4 concepts/encounters |

The four kernel-anchored targets are `C:circle`, `C:complex-number`,
`C:excluded-middle`, and `C:equivalence-relation@understand`. The last also
has a separate fact-ledger formalization, which is why its coverage state is
fact-formalization-present rather than a blended “complete” status.

## Safety properties

Kernel anchors never enter a fact-ID field, a producer-credit count, a
transport-chain count, or the train/development evaluation frontier. Conversely,
the held-out isolation boundary remains exactly where it belongs: only the two
fact-derived dimensions are partitioned and their held-out rows remain excluded.

The projection validator now rejects:

- an incorrect kernel-anchor count;
- an invented or omitted kernel anchor relative to active overlay links;
- conflating the three coverage dimensions into an unsupported state.

The generated view therefore makes the semantic work visible while retaining
the hard distinction between a theorem in the kernel, a fact admitted through
an operation, and a pedagogical/conceptual interpretation.

## Reproduction

```sh
python3 scripts/gen-autogenesis-concept-coverage-projection.py --check
python3 scripts/validate-autogenesis-concept-coverage-projection.py
python3 -m unittest scripts.tests.test_validate_autogenesis_concept_coverage_projection
```
