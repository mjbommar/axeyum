# Mathlib dependency-component result

Date: 2026-08-18

## Verdict

**The 240 statement candidates now have a proof-derived leakage graph, but no
evaluation split has been frozen.** The projection is useful split metadata;
it is not an answer set, an Axeyum proof, or evidence that the nursery is ready.

Exact Mathlib v4.30.0 produced 9,729 Nat/Int dependency rows. The immutable
external NDJSON is 2,417,444 bytes with SHA-256
`dcaed0c85525d24c9e14bb67df5c0de1784af83fcb83e5968796132fe2b00e87`.
Its three allowed fields are theorem name, defining module, and sorted direct
theorem dependency names. It is stored outside Git under
`/nas3/data/axeyum/autogenesis/sources/`.

The tracked [source manifest](../../artifacts/autogenesis/mathlib-dependency-source-v1.json),
[evaluation-only Lean extractor](../../scripts/lean/autogenesis_mathlib_dependency_inventory.lean),
and [component builder](../../scripts/create-autogenesis-mathlib-dependency-components.py)
bind and validate those bytes. Git retains the small
[candidate projection](../../artifacts/autogenesis/mathlib-nat-int-dependency-components-v1.json),
not the bulk source.

## Measured graph

The induced graph keeps an edge only when both the dependent theorem and the
directly used theorem are among the 240 candidates. Its measured shape is:

| Measure | Value |
|---|---:|
| candidate rows found | 240 / 240 |
| direct candidate-to-candidate edges | 95 |
| weak components | 146 |
| isolated candidates | 108 |
| largest component | 9 |
| cross-theme edges | 2 |
| cross-module edges | 2 |

Component sizes are 108 singletons, sixteen pairs, eight triples, three groups
of four, six groups of five, three groups of six, one group of seven, and one
group of nine. The two cross-theme edges connect the Int and Nat Fibonacci
families. That is direct evidence that family quotas cannot be applied before
component integrity: a whole component must go to one split even when it spans
two author-labelled themes.

The projection intentionally omits dependencies outside the candidate set.
Including every common foundation theorem would conflate answer leakage with
shared language and collapse most of the population into a giant component.
The retained edge means the upstream proof of candidate A directly used
candidate B; it does not mean B is the only route to A or that Axeyum should use
that proof.

## Isolation and controls

This is the one source extractor permitted to inspect `TheoremVal.value`. That
access is confined to an offline evaluation process. Neither the proof value
nor any tactic trace is emitted. Proposers, proof search, route selection, and
episode workers may consume the statement-only catalog, but may not consume
this extractor or its upstream environment.

The checker rehashes the external artifact, requires exactly three fields,
rejects duplicate, unsorted, self, or cyclic candidate edges, and verifies that
the committed components partition all 240 candidates exactly once. Mutation
tests show that changing one candidate edge changes the projection digest; a
proof-bearing output field fails the schema rather than being ignored.

## What remains before a nursery freeze

The current artifact state is deliberately
`dependency-metadata-not-frozen-split`. The next increment should:

1. review candidate statements and remove aliases, trivialities, or unsuitable
   theorem-strength outliers without consulting Axeyum outcomes;
2. author statement-strength mutations and group each mutation with its source;
3. add proof-shape risk labels derived from statements, not imported tactics;
4. assign whole dependency/mutation groups to train, development, and held-out
   partitions while preserving family-level leakage controls; and
5. materialize reviewed fact-ledger rows before running any fixed-budget
   episode.

The 108 isolated candidates are not assumed independent in a stronger sense.
They merely have no direct edge to another selected candidate under this exact
extractor and source revision. Family, proof-shape, mutation, and longitudinal
controls therefore remain mandatory.

The next outcome-blind review increment is recorded in the
[review result](14-mathlib-outcome-blind-review-result.md).
