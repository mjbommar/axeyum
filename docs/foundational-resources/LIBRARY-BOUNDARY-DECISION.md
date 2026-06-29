# Foundational Resource Library Boundary Decision

Date: 2026-06-29

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
generator or validator internals.

## Evidence

The Phase M8 threshold is met for size and repeated structure:

| Requirement | Current Evidence |
|---|---|
| At least 40 validated concept rows | 41 atlas rows: 23 curriculum rows and 18 field rows. |
| At least 12 validated example packs | 65 non-template math packs are listed through the atlas data contract. |
| At least 6 packs with checked proof/evidence routes | 53 non-template packs contain at least one `checked` expected-result row. |
| At least one consumer can read the data without repository-internal knowledge | `scripts/consume-foundational-resources.py` reads the atlas and example-pack JSON directly and cross-checks pack coverage. |

The current pack-level evidence mix is still intentionally conservative:

- `checked`: 129 expected-result rows
- `replay-only`: 131 expected-result rows
- `lean-horizon`: 28 expected-result rows
- `proof-gap`: 1 expected-result row

That distribution argues for keeping the resource lane close to the proof
cookbook, validators, and solver evidence work. A premature crate would mostly
freeze a data shape that is still learning from proof-route upgrades.

## What Not To Extract Yet

Do not create `axeyum-foundational-data` yet. A crate makes sense only after at
least one non-repo consumer wants semver, versioned artifacts, or generated Rust
types.

Do not create `axeyum-math-examples` yet. The validators contain repeated
finite-set, graph, matrix, and probability logic, but those routines are still
pack-specific checks rather than stable encoders. Extract only after a second
consumer needs to construct Axeyum terms from these packs, not merely validate
the resource data.

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
3. Add generated schema examples only when a real consumer asks for them.
4. Promote repeated replay logic into library code only after it becomes an
   encoder or checker used by multiple non-test consumers.
