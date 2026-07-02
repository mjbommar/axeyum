# Rejection Case Queries

This is the consumer-facing query guide for malformed-claim and rejection rows
in the foundational math resources. It complements:

- [Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md)
- [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md)
- [Trust Boundary Queries](TRUST-BOUNDARY-QUERIES.md)
- [Fragment Demand Queries](FRAGMENT-DEMAND-QUERIES.md)
- [Proof Certificate Cookbook](../proof-cookbook/README.md)

Use this guide when a reviewer, proof contributor, or educator wants examples
where Axeyum rejects a false finite claim and states which small check backs
the rejection.

## Boundary

There are two different rejection layers:

- **Resource-row rejection**: committed JSON rows whose mathematical claim is
  false for a fixed finite object or exact encoding. These are queryable with
  `scripts/query-foundational-resources.py`.
- **Checker tamper rejection**: route-specific cargo tests where a proof object,
  certificate, or witness artifact is corrupted and the checker rejects it.
  Those tests are documented in the proof-cookbook recipes, not in the public
  resource JSON.

Do not conflate them. A row named `bad-*` or `*-rejected` shows a malformed
source claim. A tamper test shows that a checker refuses corrupted evidence.
Both matter for the identity:

```text
untrusted fast search, trusted small checking
```

## Start Here

List checked finite rejection rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text rejected \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

List replay-only malformed source rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text rejected \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any
```

Find packs that contain checked rejection rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --text rejected \
  --proof-status checked \
  --require-any
```

Find packs that still contain replay-only rejected source rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --text rejected \
  --proof-status replay-only \
  --require-any
```

## Route-Scoped Rejection Rows

QF_LRA/Farkas malformed exact-rational rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text bad \
  --route Farkas \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

QF_UF/Alethe malformed equality or congruence rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text bad \
  --route Alethe \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

QF_BV/DRAT malformed fixed-width rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text bad \
  --route qf-bv \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

Boolean CNF/LRAT malformed finite refutations:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text bad \
  --route boolean \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

QF_LIA/Diophantine malformed integer/count rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text bad \
  --route Diophantine \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

These queries are intentionally row-level. Use pack-level route queries only
after checking which concrete row is malformed and which route owns the
rejection.

## JSON Drilldown

For a UI, lesson generator, or audit script:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text rejected \
  --proof-status checked \
  --expected-result unsat \
  --format json \
  --limit 5
```

The JSON rows include pack id, check id, result, proof status, fields,
fragments, validation label, and claim text. Use those fields to display the
rejected claim, then link to the pack and proof-cookbook route for details.

## Tamper Tests

Public resource JSON does not expose checker-tamper fixtures as rows. Follow
the proof-cookbook recipes for the focused cargo commands:

- [Boolean CNF DRAT/LRAT Evidence](../proof-cookbook/recipes/boolean-cnf-lrat.md)
- [QF_BV Bit-Blast Evidence](../proof-cookbook/recipes/qf-bv-bitblast.md)
- [QF_LIA Diophantine Evidence](../proof-cookbook/recipes/qf-lia-diophantine.md)
- [QF_LRA Farkas Evidence](../proof-cookbook/recipes/qf-lra-farkas.md)
- [QF_UF Congruence And Alethe Evidence](../proof-cookbook/recipes/qf-uf-congruence-alethe.md)
- [Finite Model Replay Evidence](../proof-cookbook/recipes/finite-model-replay.md)

Use this guide to find source rows. Use the cookbook to check corrupted
evidence rejection.

## Consumer Rules

- Prefer `--proof-status checked` when teaching certificate-backed rejections.
- Use `--proof-status replay-only` when teaching finite source-data replay.
- Do not treat every replay-only malformed row as a proof-upgrade gap; check
  [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) first.
- Do not describe a route as tamper-tested unless the linked cookbook recipe
  names the focused cargo test.
- Keep theorem and benchmark claims out of rejection-row displays.
