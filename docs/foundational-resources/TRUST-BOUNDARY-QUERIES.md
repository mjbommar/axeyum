# Trust Boundary Queries

This is the consumer-facing query guide for proof-status and result-status
boundaries across the foundational-resource corpus. It complements the
route-specific guides:

- [Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md)
- [Theorem Horizon Queries](THEOREM-HORIZON-QUERIES.md)
- [Solver Reuse Queries](SOLVER-REUSE-QUERIES.md)
- [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md)
- [Curriculum Node Queries](CURRICULUM-NODE-QUERIES.md)
- [Claim Label Matrix](CLAIM-LABEL-MATRIX.md)

Use this guide when a downstream consumer needs to decide what can be shown as
checked evidence, what is finite replay, and what is only a theorem/proof
horizon.
Use the claim-label matrix when the same consumer needs exact badge or card
wording for those statuses.

## Boundary

The core statuses are intentionally simple:

- `checked`: the row has a named checked evidence route, proof object,
  regression, or replay route strong enough for the specific finite claim.
- `replay-only`: the row is validated by recomputing a finite witness,
  counterexample, table, or arithmetic trace. This is often the right trust
  story and is not automatically a gap.
- `lean-horizon`: the row marks a general theorem boundary. It is not checked
  SMT evidence and not finite replay.

Result status is separate from proof status:

- `sat`: a witness, model, or counterexample exists for the finite claim.
- `unsat`: the finite claim or malformed row is refuted by replay or checked
  evidence.
- `not-run`: a deliberate boundary marker, currently used for Lean/theorem
  horizons.

Do not mix these axes. A `not-run`/`lean-horizon` row is future proof work, not
a failed solver run. A `sat`/`replay-only` row can be a perfectly good
counterexample resource. An `unsat`/`checked` row can be displayed as checked
evidence only for the finite or encoded claim it actually states.

## Start Here

Summarize the public data boundary:

```sh
python3 scripts/query-foundational-resources.py summary
```

Machine consumers can read the same summary as JSON:

```sh
python3 scripts/query-foundational-resources.py summary --format json
```

Use this before any status-specific query so consumer tests can notice count
drift.

## Checked Evidence

List all checked rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --require-any
```

Split checked rows by result:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --expected-result unsat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --expected-result sat \
  --require-any
```

Find packs that contain checked evidence:

```sh
python3 scripts/query-foundational-resources.py packs \
  --proof-status checked \
  --require-any
```

Use checked rows for examples that need a strong finite trust story. Still read
the route, validation label, and pack limitations before making theorem,
benchmark, or parity claims.

## Replay-Only Rows

List all replay-only rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status replay-only \
  --require-any
```

Separate replayed witnesses from replayed refutations:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status replay-only \
  --expected-result sat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any
```

Find packs that still contain replay-only rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --require-any
```

Replay-only rows should stay replay-only unless a certificate teaches a new
proof shape, trust boundary, solver pressure point, or downstream query shape.
Use [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) before promoting one.

## Lean-Horizon Rows

List theorem-boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status lean-horizon \
  --expected-result not-run \
  --require-any
```

Find packs that carry theorem horizons:

```sh
python3 scripts/query-foundational-resources.py packs \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Use [Theorem Horizon Queries](THEOREM-HORIZON-QUERIES.md) for route, field, and
topic drilldowns. These rows explain what the current resource does not prove.

## Field-Scoped Examples

Checked finite refutations in graph resources:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

Replay-only probability witnesses:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field probability_theory \
  --proof-status replay-only \
  --expected-result sat \
  --require-any
```

Topology theorem boundaries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --proof-status lean-horizon \
  --expected-result not-run \
  --require-any
```

These examples are deliberately status-first. Use field and route guides after
choosing which trust level the consumer is allowed to display.

## JSON Drilldown

For a UI, static-site generator, or downstream resource index:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --format json \
  --limit 5
```

The JSON rows include pack id, check id, result, proof status, fields,
fragments, validation label, and claim text. Treat those fields as display
metadata, not as a replacement for reading the pack when making a stronger
claim.

## Consumer Rules

- Count `checked` rows as checked evidence only for their stated finite or
  encoded claim.
- Count `replay-only` rows as validated finite resources, not as missing proofs
  by default.
- Count `lean-horizon` rows as theorem-boundary markers, not as solver results.
- Do not benchmark `not-run` rows.
- Do not turn educational rows into parity claims without the solver
  measurement gates in [PLAN.md](../../PLAN.md).
- Keep the identity intact: untrusted fast search, trusted small checking.
