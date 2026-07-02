# Public Data Contract

This is the R6 consumer boundary for the foundational-resource system. It tells
downstream tools which committed files are public, which fields are stable
enough to query, and which claims must stay out of UI copy unless separate
evidence exists.

The contract is deliberately small:

```text
public JSON -> tiny consumer/query scripts -> generated or downstream views
```

It is not a Rust API, not a benchmark corpus, and not a theorem library. Keep
using JSON until repeated external consumers prove that typed accessors or a
separate library boundary are worth maintaining.

## Public Files

| File or glob | Role | Schema |
|---|---|---|
| `artifacts/ontology/foundational-concepts.json` | Concept, field, bridge, and example-family atlas. | `artifacts/ontology/foundational-concepts.schema.json` |
| `artifacts/examples/math/*/metadata.json` | Pack-level identity, owners, fragments, trust status, validation command, and solver-reuse disposition. | `artifacts/ontology/foundational-example-pack.schema.json#/metadata` |
| `artifacts/examples/math/*/expected.json` | Witnesses and expected check rows. | `artifacts/ontology/foundational-example-pack.schema.json#/expected` |
| `scripts/consume-foundational-resources.py` | Minimal external-consumer smoke test. | no imports from validators/generators |
| `scripts/query-foundational-resources.py` | Copyable query interface over committed JSON. | public CLI output |

Generated dashboards under `docs/foundational-resources/generated/` are useful
views, but the JSON files above are the data boundary. If a generated dashboard
disagrees with JSON, fix the JSON, metadata, generator, or prose source rather
than treating the dashboard as an independent source of truth.

## Current Contract Snapshot

The consumer smoke currently reports:

```text
concept_rows=121
curriculum_rows=23
field_rows=18
non_template_packs=110
packs_with_checked_evidence=110
schema_versions=atlas:1,metadata:1,expected:1
expected_result_counts=not-run:73,sat:340,unsat:285
proof_status_counts=checked:330,lean-horizon:73,replay-only:295
row_label_counts=checked_refutation:242,checked_witness:88,finite_rejection_replay:43,finite_witness_replay:252,theorem_horizon:73
pack_label_counts=checked_evidence_pack:110,mixed_trust_story:99,theorem_boundary_included:73
```

Regenerate this snapshot with:

```sh
python3 scripts/consume-foundational-resources.py
```

Machine-readable output is available for downstream smoke tests:

```sh
python3 scripts/consume-foundational-resources.py --format json
```

## Stable Consumer Fields

Concept rows expose:

- `id`, `kind`, `title`, and `domain`;
- `field_ids`, `curriculum_node`, `curriculum_layer`, `curriculum_area`,
  `curriculum_status`, and `curriculum_family`;
- `resource_status`, `decidability`, and `axeyum_fragments`;
- `example_packs`, `proof_routes`, `source_refs`, `open_gaps`, and
  `graduation`.

Pack metadata exposes:

- `id`, `title`, `domain`, `claim_status`, and `trust_status`;
- `concept_ids`, `field_ids`, `curriculum_nodes`, and `axeyum_fragments`;
- `validator_command`, `source_refs`, `expected_results`, and
  `graduation_criteria`;
- optional `solver_reuse` with `status`, `target`, `pressure`, `evidence`, and
  `next_step`.

Expected rows expose:

- `schema_version`, `pack_id`, `witnesses`, and `checks`;
- per-check `id`, `claim`, `expected_result`, `validation`, `proof_status`,
  optional `witnesses`, optional `data`, and `notes`.

Consumers should tolerate additional rows and packs. They should not assume a
fixed order beyond the query script's sorted table output.

## Status Semantics

`expected_result` and `proof_status` are separate axes.

| Field | Stable values used now | Meaning |
|---|---|---|
| `expected_result` | `sat`, `unsat`, `not-run` | The expected outcome for the finite row or theorem boundary. |
| `proof_status` | `checked`, `replay-only`, `lean-horizon` | The trust story for that row. |
| `solver_reuse.status` | `promoted`, `non-benchmark-horizon` | The pack has a deliberate solver/proof feedback disposition. |

The schemas also reserve values such as `unknown`, `template`, `proof-gap`,
`not-required`, and `candidate`. If one appears in the non-template public
corpus, update this contract and the query guides in the same commit.

Use [CLAIM-LABEL-MATRIX.md](CLAIM-LABEL-MATRIX.md) for display wording. The
executable audit is:

```sh
python3 scripts/query-foundational-resources.py labels
```

Certificate-upgrade candidate discovery is also queryable without importing
validators or solver crates:

```sh
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas
```

This command is advisory. It lists replay-only `unsat` rows in packs that
already advertise a certificate route, plus checked-row contrast in the same
pack. It does not assert that every replay row needs promotion.
Use `--promotion-state no-route-contrast`, `partial-route-contrast`, or
`covered-by-route-contrast` to triage whether a row family has no, partial, or
already sufficient same-pack checked-route contrast. Use `--curriculum-node`
or `--solver-reuse` when the review starts from the curriculum DAG or the R5
solver-reuse boundary.

Coverage-frontier discovery ranks resource-builder pressure over the same
dependency-free JSON boundary:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier --by field
```

This command is also advisory. It groups rows by field, fragment, curriculum
node, or decidability class and reports checked evidence, replay-only rows,
replay-only refutations, and theorem horizons for work selection. It does not
define corpus totals, benchmark claims, or parity claims.
Its action labels distinguish `proof-upgrade` from `proof-review`: the latter
means replay-only refutations exist but current same-pack route contrast already
covers the proof shape. Consumers can filter those labels directly with
`--action proof-review`, `--action proof-upgrade`, `--action theorem-horizon`,
or the other documented action values.

Pack-frontier discovery drills from those group-level rankings to concrete
pack-level worklists:

```sh
python3 scripts/query-foundational-resources.py pack-frontier --field real_analysis
```

This command reports checked evidence, replay-only refutations, theorem
horizons, checked-row density, action labels, route-promotion states, and
finite-shadow state per pack. It is advisory work selection only.

Theorem-boundary discovery has the same dependency-free shape:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier --field topology
```

This command lists `lean-horizon` rows with finite checked/replay contrast from
the same pack. It is for routing and display boundaries, not for proof,
benchmark, or parity claims.
Use `--shadow-state checked-finite-shadow`, `replay-only-finite-shadow`, or
`no-finite-shadow` to triage whether the same pack has checked finite context,
only replay context, or no finite shadow beside the horizon row.

## Compatibility Rules

A compatible additive change may:

- add concept rows, packs, witnesses, or checks;
- add optional fields only after updating the schema and consumer docs;
- add query subcommands or columns if existing output remains usable;
- increase counts, proof-route coverage, or display-label counts.

A breaking change includes:

- removing or renaming a public field;
- changing the meaning of `expected_result`, `proof_status`, or
  `solver_reuse.status`;
- changing schema version without documenting migration behavior;
- making `consume-foundational-resources.py` import validators, generators, or
  solver crates;
- promoting replay-only, Lean-horizon, solver-reuse, benchmark, or parity
  claims without the corresponding evidence gate.

When a breaking change is intentional, land it with a plan update and a new
schema-version/migration note.

## Required Checks

Before committing data-boundary or query changes:

```sh
git diff --check
./scripts/check-links.sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/consume-foundational-resources.py --format json
python3 scripts/query-foundational-resources.py summary
python3 scripts/query-foundational-resources.py coverage --by field --require-any
python3 scripts/query-foundational-resources.py coverage --by proof-status --require-any
python3 scripts/query-foundational-resources.py coverage-frontier --by field --require-any
python3 scripts/query-foundational-resources.py coverage-frontier --by field --action proof-review --require-any
python3 scripts/query-foundational-resources.py coverage-frontier --by fragment --min-replay-unsat 1 --format json --require-any
python3 scripts/query-foundational-resources.py coverage-frontier --by curriculum-node --field topology --min-horizon 1 --require-any
python3 scripts/query-foundational-resources.py pack-frontier --field real_analysis --require-any
python3 scripts/query-foundational-resources.py pack-frontier --field topology --action theorem-horizon --shadow-state checked-finite-shadow --require-any
python3 scripts/query-foundational-resources.py pack-frontier --field measure_theory --max-checked-ratio 0.35 --require-any
python3 scripts/query-foundational-resources.py pack-frontier --field real_analysis --action proof-review --format json --require-any
python3 scripts/query-foundational-resources.py labels
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --require-any
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --curriculum-node linear-algebra --promotion-state covered-by-route-contrast --require-any
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --solver-reuse promoted --format json --require-any
python3 scripts/query-foundational-resources.py upgrade-frontier --route Alethe --promotion-state covered-by-route-contrast --require-any
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --promotion-state no-route-contrast --format json
python3 scripts/query-foundational-resources.py horizon-frontier --field topology --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --field topology --shadow-state checked-finite-shadow --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --shadow-state no-finite-shadow --format json
```

For command examples and drilldowns, use
[CONSUMER-QUERIES.md](CONSUMER-QUERIES.md). For trust wording, use
[TRUST-BOUNDARY-QUERIES.md](TRUST-BOUNDARY-QUERIES.md) and
[CLAIM-LABEL-MATRIX.md](CLAIM-LABEL-MATRIX.md).
