# The import backlog becomes a produced artifact

Date: 2026-08-27

Decision: [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md) SS3

Generator: [`scripts/gen-import-backlog.py`](../../scripts/gen-import-backlog.py)
Artifact: [`artifacts/import-backlog.json`](../../artifacts/import-backlog.json)

Note on the filename: ADR-0601's own brief asked for
`docs/autogenesis/263-import-backlog-artifact.md`, but `263` was already
claimed by `263-holdout-contamination-by-ordinary-development.md` by the time
this lane landed (concurrent numbering; this directory has no uniqueness
gate). This document is `288`, the next free number at commit time.

## What this is

`python3 scripts/validate-facts.py` has always COUNTED the population of
facts that are settled in the wider mathematical literature but not yet
established by this project's own kernel:

```
external: 164 settled elsewhere but not here (import backlog), 8 unclassified
```

Nothing consumed that count. This generator turns it into a produced,
deterministic, committed artifact -- `artifacts/import-backlog.json` -- so a
selector (the autogenesis frontier, or a future import-scheduling lane) can
walk it directly instead of re-deriving the population from
`artifacts/facts/*.json` itself.

## What a row is

A fact with `epistemic_status == "open"` AND `external_status == "proved"`.
This is deliberately the SAME two-field test `validate-facts.py`'s own
backlog counter uses -- not a broader "closed elsewhere" notion -- so the
artifact's `count` always equals that counter's number on the same tree.
That equality is itself a cheap correctness check: `python3
scripts/validate-facts.py 2>&1 | grep -oE '[0-9]+ settled elsewhere'` and
`jq .count artifacts/import-backlog.json` must agree.

Each row carries:

| field | meaning |
|---|---|
| `id` | the fact id |
| `statement` | the fact's prose `statement` field (not `formal.statement`) |
| `depends_on` | the fact's `depends_on` edges, sorted for determinism |
| `dependency_ready` | true iff every id in `depends_on` names a fact whose `epistemic_status` is one of `{proved, computed, refuted}` (`OURS_SETTLED`, imported from `scripts/validate-facts.py` rather than re-typed) |
| `curriculum_node` | a `docs/curriculum/curriculum.toml` node id, or `null` |
| `curriculum_layer` | that node's `layer`, or `null` |
| `curriculum_title` | that node's `title`, or `null` |

## Curriculum mapping is exact, not fuzzy, and mostly absent

A fact carries no direct edge to a curriculum node. `concept_refs` point at
the separate `math-education` concept graph (ids like `C:commutativity`,
`C:fermats-last-theorem`), which is a different vocabulary from curriculum
node ids (`propositional-logic`, `modular-arithmetic`, `integers`, ...).

The two vocabularies overlap only where a concept ref's id, with its `C:`
prefix stripped, happens to equal a curriculum node id VERBATIM. Measured on
this tree: 4 of the curriculum's 23 nodes have this property at all
(`counting`, `integers`, `modular-arithmetic`, `predicate-logic`), and among
the 164 backlog facts exactly **one** (`F:fol-validity-undecidable`, via
`C:predicate-logic`) actually carries a matching ref.

This script uses exactly that exact match and nothing broader. A
substring/title-similarity heuristic would score higher on paper -- more rows
"mapped" -- and would be measuring nothing, per CLAUDE.md's standing lesson
that a crude classifier flagging a whole shape is not a measurement. A fact
with no exact match gets `curriculum_node: null`, which is the honest,
current, and overwhelming majority case (163 of 164). Extending the mapping
(a real `curriculum` concept graph on facts, or a maintained crosswalk table)
is future work and is out of this generator's scope; this document says so
rather than papering over it with a fuzzier matcher.

## The ordering is the design content

Rows are sorted, in order of precedence:

1. **`dependency_ready` before blocked.** A ready row can be imported without
   first importing anything else.
2. **`curriculum_node`-mapped before unmapped**, within the readiness tier.
   A curriculum-reachable import extends a DAG a reader (or a selector) can
   navigate; an unmapped one is an island.
3. **`(curriculum_layer, curriculum_node)` ascending**, within the mapped
   population -- foundations-first, the same order the curriculum tour
   itself uses.
4. **Fact id ascending**, as the final tiebreak and as the SOLE ordering key
   for the (currently 163-of-164) unmapped population.

Measured on the current ledger: 164 rows, 117 `dependency_ready`, 1
`curriculum_node`-mapped.

## For a consumer (the frontier selector)

`scripts/fact-frontier.py` is owned by a different, concurrently running
lane and is deliberately **not modified by this generator or this document's
author** -- ADR-0601 assigns route-2/route-3 work (this generator) and
selector integration to separate lanes. A future selector change can read
`artifacts/import-backlog.json` directly:

```python
import json
backlog = json.load(open("artifacts/import-backlog.json"))
for row in backlog["rows"]:
    if row["dependency_ready"]:
        ...  # first dependency_ready rows are import candidates NOW
```

The file's own `ordering` field states the same guarantee in prose, so a
consumer never has to re-derive it from the code.

## Regeneration and the gate

```sh
python3 scripts/gen-import-backlog.py          # regenerate
python3 scripts/gen-import-backlog.py --check  # fail if the committed file has drifted
```

`--check` mirrors `scripts/gen-plan.py --check`'s convention -- the standard
generated-artifact gate in this repository -- and is wired into
`scripts/check.sh` and the `justfile` alongside it.

Mutation-tested: `python3 scripts/tests/mutation_controls.py
import-backlog-classification` deletes each of the two classification
guards (the `math-education` graph check, the dependency-settled check) and
confirms each kills exactly one test.
