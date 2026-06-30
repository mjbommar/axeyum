# Foundational Resource Library Boundary Decision

Date: 2026-06-29

Reviewed: 2026-06-30; counts refreshed after all 102 current math packs carry
promoted solver-reuse metadata and no explicit non-benchmark-horizon packs
remain.

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
and [Foundational Resource Consumer Queries](CONSUMER-QUERIES.md). The compact
[Field Readiness Query Matrix](FIELD-READINESS-QUERY-MATRIX.md) summarizes the
same public query surface across all 18 math fields.
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md) summarizes the same
surface by proof/evidence route.
[Matrix Computation Consumer Queries](MATRIX-COMPUTATION-QUERIES.md) narrows
that same surface for bridge-concept-plus-route discovery over matrix packs.

The 2026-06-30 review keeps the same decision. The consumer-query layer now
reads promoted solver-reuse metadata directly, including the promoted
probability/measure QF_LRA/Farkas rows, equality-heavy QF_UF/Alethe rows, and
integer-count and coefficient QF_LIA/Diophantine rows, plus fixed-width
QF_BV/DRAT rows. It also exposes field-level curriculum-readiness summaries
over the same JSON files, but this is still an in-repository
downstream-consumer stand-in rather than an external release consumer.
The all-field matrix is documentation over that same stand-in; it improves
navigability but does not create a new API boundary.
The matrix computation query guide and `--concept` filters are likewise still
documentation plus a dependency-free query-helper surface over committed JSON,
not a typed library boundary.
The route matrix and `routes` summary command likewise summarize committed
recipe links; they do not add a route checker or library API.

## Evidence

The Phase M8 threshold is met for size and repeated structure:

| Requirement | Current Evidence |
|---|---|
| At least 40 validated concept rows | 94 atlas rows: 23 curriculum rows, 18 field rows, 48 bridge-concept rows, and 5 example-family rows. |
| At least 12 validated example packs | 102 non-template math packs are listed through the atlas data contract. |
| At least 6 packs with checked proof/evidence routes | 102 non-template packs contain at least one `checked` expected-result row. |
| At least one consumer can read the data without repository-internal knowledge | `scripts/consume-foundational-resources.py` reads the atlas and example-pack JSON directly and cross-checks pack coverage; `scripts/query-foundational-resources.py` answers summary, pack, check, concept, and field-readiness queries without importing validators or generators. |
| At least one consumer can read promoted solver-reuse rows | `scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any` is part of `scripts/check-foundational-resources.sh` and currently finds 102 promoted packs. |
| At least one documentation surface maps consumer queries by field | `FIELD-READINESS-QUERY-MATRIX.md` records the smoke-checked route, bridge lookup, checked-row drilldown, and theorem boundary for all 18 math fields without adding a typed API. |
| At least one documentation surface maps consumer queries by proof route | `PROOF-ROUTE-QUERY-MATRIX.md` records route-summary, pack-drilldown, and checked-row queries for the active proof/evidence routes, and `check-foundational-resources.sh` smoke-checks representative `routes --route ...` commands. |
| At least one documentation surface maps resources by bridge concept and route | `MATRIX-COMPUTATION-QUERIES.md` records concept-plus-route matrix queries, and `check-foundational-resources.sh` smoke-checks representative `packs/checks --concept ... --route ...` commands. |

The current pack-level evidence mix is still intentionally conservative:

- `checked`: 222 expected-result rows
- `replay-only`: 229 expected-result rows
- `lean-horizon`: 65 expected-result rows
- `not-run`: 65 expected-result rows
- `solver_reuse`: 102 promoted packs, 0 non-benchmark-horizon packs, and 0
  unclassified packs

That distribution argues for keeping the resource lane close to the proof
cookbook, validators, and solver evidence work. A premature crate would mostly
freeze a data shape that is still learning from proof-route upgrades.

The 2026-06-30 review also confirms that the new solver-reuse metadata is still
evolving. The latest promotions mostly add source-linked regression back-links
to existing example packs, and the former explicit non-benchmark-horizon rows
have now either graduated or left no active pack in that bucket. They do not
yet create a repeated public API need.

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
