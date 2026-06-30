# Foundational Resource Library Boundary Decision

Date: 2026-06-29

Reviewed: 2026-06-30; counts refreshed after 68 promoted solver-reuse packs
and 6 explicit non-benchmark-horizon packs.

## Decision

Keep the foundational-resource ecosystem inside the Axeyum repository for now.
Do not add a new workspace crate and do not split a separate repository yet.

The current boundary is a data contract:

- `artifacts/ontology/foundational-concepts.json`
- `artifacts/ontology/foundational-concepts.schema.json`
- `artifacts/ontology/foundational-example-pack.schema.json`
- `artifacts/examples/math/*/metadata.json`
- `artifacts/examples/math/*/expected.json`
- `docs/foundational-resources/generated/*.md`

The stable consumer surface is validated by
[`scripts/consume-foundational-resources.py`](../../scripts/consume-foundational-resources.py),
which reads only the committed JSON/metadata paths and imports none of the
generator or validator internals. Common consumer lookups are demonstrated by
[`scripts/query-foundational-resources.py`](../../scripts/query-foundational-resources.py)
and [Foundational Resource Consumer Queries](CONSUMER-QUERIES.md).

The 2026-06-30 review keeps the same decision. The consumer-query layer now
reads promoted solver-reuse metadata directly, including the promoted
probability/measure QF_LRA/Farkas rows, equality-heavy QF_UF/Alethe rows, and
integer-count and coefficient QF_LIA/Diophantine rows, plus fixed-width
QF_BV/DRAT rows, but this is still an in-repository downstream-consumer stand-in
rather than an external release consumer.

## Evidence

The Phase M8 threshold is met for size and repeated structure:

| Requirement | Current Evidence |
|---|---|
| At least 40 validated concept rows | 65 atlas rows: 23 curriculum rows, 18 field rows, 22 bridge-concept rows, and 2 example-family rows. |
| At least 12 validated example packs | 84 non-template math packs are listed through the atlas data contract. |
| At least 6 packs with checked proof/evidence routes | 78 non-template packs contain at least one `checked` expected-result row. |
| At least one consumer can read the data without repository-internal knowledge | `scripts/consume-foundational-resources.py` reads the atlas and example-pack JSON directly and cross-checks pack coverage; `scripts/query-foundational-resources.py` answers summary, pack, check, and concept queries without importing validators or generators. |
| At least one consumer can read promoted solver-reuse rows | `scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any` is part of `scripts/check-foundational-resources.sh` and currently finds 68 promoted packs. |

The current pack-level evidence mix is still intentionally conservative:

- `checked`: 195 expected-result rows
- `replay-only`: 171 expected-result rows
- `lean-horizon`: 47 expected-result rows
- `not-run`: 47 expected-result rows
- `solver_reuse`: 68 promoted packs, 6 non-benchmark-horizon packs, and 10
  unclassified packs

That distribution argues for keeping the resource lane close to the proof
cookbook, validators, and solver evidence work. A premature crate would mostly
freeze a data shape that is still learning from proof-route upgrades.

The 2026-06-30 review also confirms that the new solver-reuse metadata is still
evolving. The latest promotions mostly add source-linked regression back-links
to existing example packs, while the first explicit non-benchmark-horizon rows
document useful educational replay packs that are not yet solver assets. They
do not yet create a repeated public API need.

## What Not To Extract Yet

Do not create `axeyum-foundational-data` yet. A crate makes sense only after at
least one non-repo consumer wants semver, versioned artifacts, or generated Rust
types. The current query helper proves the JSON contract is usable; it does not
prove that a semver Rust API is needed.

Do not create `axeyum-math-examples` yet. The validators contain repeated
finite-set, graph, matrix, and probability logic, but those routines are still
pack-specific checks rather than stable encoders. Extract only after a second
consumer needs to construct Axeyum terms from these packs, not merely validate
or query the resource data.

Do not split a standalone repository yet. The resources still rely on Axeyum's
fragment vocabulary, proof-route vocabulary, docs link checks, and active
planning files. Splitting now would add release-process overhead before there is
an independent audience or corpus lifecycle.

## Revisit Triggers

Reopen the boundary decision when one of these becomes true:

- An external site, course, benchmark viewer, or downstream app consumes the
  JSON data and needs versioned releases.
- At least three independent tools need generated Rust/Python types for the
  concept atlas or example-pack schema.
- At least three example-pack validators duplicate an encoder that builds
  Axeyum terms, not just local replay checks.
- The example packs become a large corpus with separate storage, download, or
  release requirements.
- The generated dashboards become an application rather than committed Markdown.

## Next Boundary Work

The next practical boundary step is not a crate. It is to keep the data contract
boring and auditable:

1. Keep `scripts/check-foundational-resources.sh` as the required freshness gate.
2. Keep `scripts/consume-foundational-resources.py` small and dependency-free.
3. Keep `scripts/query-foundational-resources.py` as a sample consumer, not a
   validator or typed API layer.
4. Add generated schema examples only when a real consumer asks for them.
5. Promote repeated replay logic into library code only after it becomes an
   encoder or checker used by multiple non-test consumers.
