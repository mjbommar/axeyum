# Foundational Resource Consumer Queries

This page shows how a downstream consumer can ask useful questions about the
foundational-resource data contract without importing Axeyum internals.

The query surface is intentionally boring:

- [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json)
- [`artifacts/examples/math/*/metadata.json`](../../artifacts/examples/math/)
- [`artifacts/examples/math/*/expected.json`](../../artifacts/examples/math/)
- [`scripts/query-foundational-resources.py`](../../scripts/query-foundational-resources.py)

The script reads only committed JSON files. It does not import validators,
generators, solver crates, or dashboard code, so it acts like a small external
consumer would.

## Contract Summary

```sh
python3 scripts/query-foundational-resources.py summary
```

Use this first when checking that a checkout exposes the expected public data
shape. It reports concept-row counts, non-template pack counts,
expected-result counts, proof-status counts, and solver-reuse status counts.

JSON output is available when another tool needs stable parsing:

```sh
python3 scripts/query-foundational-resources.py summary --format json
```

## Solver-Reuse Candidates

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse candidate
```

This answers: "Which validated education packs are ready to consider for
regression, fuzz, or benchmark reuse?"

Candidate status is not the same as R5 promotion. A candidate is still R4 until
a regression, fuzz seed, benchmark slice, or explicit non-benchmark-horizon
back-link exists. It is valid for this query to return no rows after a candidate
batch has been fully promoted.

To list rows that already have solver-regression back-links:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --require-any
```

## Field-Focused Pack Discovery

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --format table
```

This answers: "What packs should a graph-theory consumer display or mine first?"
The row includes the pack path, trust status, expected-result mix, proof-status
mix, and solver-reuse status.

For machine consumers:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --format json
```

## Field And Proof-Route Discovery

```sh
python3 scripts/query-foundational-resources.py packs \
  --field probability_theory \
  --route Farkas \
  --require-any
```

This answers: "Which probability packs use or point at the exact-rational
Farkas route?" The route filter is a case-insensitive substring over public
route-bearing fields: fragments, proof-cookbook source refs, validation labels,
proof statuses, solver-reuse metadata, evidence metadata, and route notes. Pack
rows include `route_checks` and `route_validations` when a specific check row
matches; `pack-metadata` means the pack advertises that route at the metadata
level even if no individual check label contains the substring.
Hyphen and underscore spellings are normalized for substring search, so
`qf-bv` and `QF_BV` match the same route text.

For a narrower row-level view, query checks directly:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --route qf-bv \
  --expected-result unsat \
  --require-any
```

Use this when a consumer needs concrete rows to display as checked examples,
rather than a list of route-relevant packs.

## Curriculum Field Readiness

```sh
python3 scripts/query-foundational-resources.py fields \
  --field probability_theory \
  --require-any
```

This answers: "For one university-curriculum field, how many packs and checks
are ready, which proof routes do they exercise, and which packs still carry
Lean-horizon rows?" The table includes pack and check counts, proof-status
counts, proof-cookbook route counts, solver-reuse status counts, sample packs,
and horizon packs.

Route filtering works over the same public route text used by pack discovery:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route boolean \
  --format json \
  --require-any
```

Use this view for curriculum navigation, dashboards, or external sites that
need a field-level readiness summary before drilling into individual packs or
checks.

For a field where the useful finite slice crosses several recent learner pages,
query the exact-rational route directly:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --require-any
```

That gives a compact readiness row for recurrence traces, Euler-step examples,
stochastic-kernel/hitting-time equations, and invariant-bound conflicts without
requiring a consumer to know which pack owns each topic. To display concrete
checked rows for a lesson or catalog card, drill into the check table:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For measure theory, use the same field-readiness query to keep finite
event-algebra, product-measure, integration, random-variable, conditioning, and
stochastic-process examples grouped without treating the finite rows as
Lebesgue or convergence theorem coverage:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field measure_theory \
  --route Farkas \
  --require-any
```

The bridge rows are visible through the atlas query surface:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field measure_theory \
  --text finite \
  --require-any
```

To display concrete checked finite-measure or finite-integration examples, drill
into checked Farkas rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For optimization and convexity, query the Farkas route to keep exact LP
thresholds, finite convexity shadows, regression normal equations, residual
bounds, gradient/Hessian replay, finite KKT stationarity, finite SDP
objective/slack replay, finite gradient-descent replay, and finite
line-search replay, finite projected-gradient replay, and finite
proximal-gradient replay together while
leaving duality, KKT sufficiency, SDP strong duality, line-search convergence,
projected-gradient convergence, proximal-gradient convergence, and convergence
claims in the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field optimization_and_convexity \
  --route Farkas \
  --require-any
```

Use atlas lookups for the two reusable bridge concepts:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field optimization_and_convexity \
  --text objective \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field optimization_and_convexity \
  --text convexity \
  --require-any
```

To display concrete checked optimization, convexity, finite SDP, finite
gradient-descent, finite line-search, finite projected-gradient, finite
proximal-gradient, least-squares, gradient, residual, or eigenpair rows, drill
into checked Farkas examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field optimization_and_convexity \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Proof And Check Mining

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

This answers: "Which checked graph-theory negative examples can be shown as
trusted-small-checking examples?"

Other useful filters:

```sh
python3 scripts/query-foundational-resources.py checks --fragment QF_LRA --proof-status checked
python3 scripts/query-foundational-resources.py checks --validation farkas --expected-result unsat
python3 scripts/query-foundational-resources.py checks --pack logic-basics-v0
python3 scripts/query-foundational-resources.py checks --text counterexample
```

The table output truncates long claims for readability. Use `--format json` for
the full row text.

## Atlas Concept Queries

```sh
python3 scripts/query-foundational-resources.py concepts \
  --kind example-family \
  --format json \
  --require-any
```

This answers: "Which reusable cross-pack families already exist in the atlas?"

Other useful filters:

```sh
python3 scripts/query-foundational-resources.py concepts --field linear_algebra
python3 scripts/query-foundational-resources.py concepts --decidability proof-horizon
python3 scripts/query-foundational-resources.py concepts --pack finite-cardinality-v0
python3 scripts/query-foundational-resources.py concepts --text Lean
```

## What These Queries Prove

These queries prove the public JSON contract is readable and useful for common
consumer workflows:

- locating packs by field, curriculum node, fragment, or proof status;
- mining checked `sat` and `unsat` rows for learner or benchmark views;
- finding candidate and promoted solver-reuse rows without scanning prose;
- listing reusable concept families from the atlas.
- summarizing field-level curriculum readiness before drilling into packs.

They do not prove solver correctness, proof-certificate validity, or general
mathematical theorem coverage. Those remain the job of the example-pack
validators, route-specific cargo regressions, proof-cookbook checks, and future
Lean reconstruction work.

## CI Smoke Coverage

[`scripts/check-foundational-resources.sh`](../../scripts/check-foundational-resources.sh)
runs a small query smoke set after validating concepts and packs:

```sh
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field differential_equations_and_dynamical_systems --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field measure_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field measure_theory --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field measure_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field optimization_and_convexity --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text objective --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text convexity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field optimization_and_convexity --route Farkas --proof-status checked --require-any >/dev/null
```

That keeps the examples on this page aligned with the committed data boundary
without turning the query helper into a replacement validator.
