# Glaurung parity-leaf clause overlap — 2026-07-19

Status: accepted fixed-population diagnostic; one bounded follow-on selected

ADR-0276 preregistered the parity-leaf identity/shape partition and its
50% / 10-query / 50% rule before artifact-v37 implementation or corpus
observation. The implementation is commit `b02b6ab4`; the clean detached
measurement source is `6ff05905131b58a8cfa1c15e91ea97c9304f5ead`.

## Population and gates

- corrected-wide-v3 representative manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- 162 raw QF_BV queries: 88 SAT and 74 UNSAT;
- family counts 36 arithmetic, 12 comparison, 7 mixed, 52 register-slice,
  54 slice-partial, and 1 trivial;
- 162/162 manifest and in-process Z3 agreements, 88/88 original-model replays,
  and zero Unknown/unsupported/error/disagreement; and
- exact equality with ADR-0260's retained construction, family, and origin
  aggregates plus every new overlap invariant.

Artifact identity is version 37, config hash `b6809235b93d6f96`, corpus hash
`23932b876da74bd1`, and environment hash
`83bf3161219d530aa28d371cdea9596c0292978b883f5d67ac82540394ce4543`.

Retained accepted files:

- [`artifact.json`](artifact.json), SHA-256
  `e61f6a61e168ab87ce111557b703621a7c738387d8018cfa7a34f9e9c556421a`;
- [`analysis.json`](analysis.json), SHA-256
  `4dc29c7ce4bd6d5e37956bc5d775bf64ab2fe47be99705959947656cae8c608c`.

## Exact result

All 107,000 parity/parity duplicates occupy one cell:

| Relation | Shape | Duplicates | Literals | Queries | Largest-query share |
|---|---|---:|---:|---:|---:|
| `within_leaf` | `a2-f0-t0-d2-r0-x0` | 107,000 | 214,000 | 29 | 9.9738% |

Every clause is binary. The leaf has two distinct nonconstant AIG nodes, no
constants, no repeated literal, and no complementary pair. Cross-leaf and
cross-owner parity overlap are both zero. The cell partitions into 83,172
slice-partial SAT, 14,894 register-slice SAT, and 8,934 register-slice UNSAT
duplicates.

This rejects another duplicate-leaf interpretation. ADR-0277 alone is selected:
memoize emission of an already-visited positive direct-root parity leaf, then
require the exact 107,000-attempt structural delta before any unprofiled timing.

## Rejected wrong-population attempt

The checkout also contained an unrelated untracked 128-query manifest at
`corpus/glaurung-qfbv/manifest-representative-v1.json`, SHA-256
`0556f77bad1ca74e49f57ef0ad01d2967391c9937fbe0cfd805e24d8fce2e68d`.
The first corrected command mistakenly used that path. Its
[`rejected-wrong-manifest-artifact.json`](rejected-wrong-manifest-artifact.json)
has SHA-256
`ba713d77ad0cae921ccdbf626b485838723c82d052877050fa1943374f007a4e`.
It is excluded by the preregistered file-count and manifest-hash gates; its
overlap cells were not inspected and did not influence selection.

## Claim limits

Profiled timing is diagnostic. This result identifies a repeated-emission
mechanism on one fixed client corpus; it establishes neither an end-to-end
speedup nor a general parity-encoding advantage. Strict typing, original-term
model replay, complete-work accounting, and neutral-oracle agreement remain
mandatory.
