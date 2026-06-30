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
  --solver-reuse candidate \
  --require-any
```

This answers: "Which validated education packs are ready to consider for
regression, fuzz, or benchmark reuse?"

Candidate status is not the same as R5 promotion. A candidate is still R4 until
a regression, fuzz seed, benchmark slice, or explicit non-benchmark-horizon
back-link exists.

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
- finding R4-to-R5 solver-reuse candidates without scanning prose;
- listing reusable concept families from the atlas.

They do not prove solver correctness, proof-certificate validity, or general
mathematical theorem coverage. Those remain the job of the example-pack
validators, route-specific cargo regressions, proof-cookbook checks, and future
Lean reconstruction work.

## CI Smoke Coverage

[`scripts/check-foundational-resources.sh`](../../scripts/check-foundational-resources.sh)
runs a small query smoke set after validating concepts and packs:

```sh
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse candidate --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
```

That keeps the examples on this page aligned with the committed data boundary
without turning the query helper into a replacement validator.
