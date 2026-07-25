# SMT-COMP stale s4 final artifact audit

Status: final read-only diagnostic snapshot; zero measurement and correctness
credit

Date: 2026-07-25

Parent:
[full-library work stream](smtcomp-full-library-workstream/README.md)

Prior failure record:
[candidate-run handoff](smtcomp-full-library-candidate-run-handoff-2026-07-21.md)

## Scope and verdict

The historical eight-shard s4 run resumed outside the credited workstream and
eventually reached every selected path. A read-only audit at
`2026-07-25T03:31:10-04:00` found no surviving `compete.py` or
`axeyum-smtcomp` process. Every log ends at its exact shard cardinality and is
followed by a `wrote raw results .../raw_N.json` line.

This completion does **not** turn the run into measurement evidence. It used
the stale pre-repair Axeyum binary and the superseded end-of-shard harness; it
has no E1--E3 attempt, lease, typed terminal, output-sidecar, aggregate-resource,
completion-last, official-selection, or model/proof-replay evidence. The raw
schema also represents execution failure only as a null reported status.
Nothing below is a decide-rate, correctness, solver-comparison, or performance
claim.

## Selection and completeness checks

The frozen selection remains:

- seed: `20260721`;
- corpus: SMT-LIB 2024 non-incremental tree;
- manifest: 84 logics, 438,631 pooled files, 64,345 selected files;
- selected list: 64,345 lines, SHA-256
  `1f988de6efd8b0dd47ccbc14d7c61739f6e47f55a675fc705e7f58c7baf47609`;
- selection manifest: 8,911 bytes, SHA-256
  `964693be6cd1953b815c24ab8411d0ee234bc74608c8713c2b41a7f93cfe31b5`.

`raw_0.json` contains 8,044 benchmark keys and each of `raw_1.json` through
`raw_7.json` contains 8,043, totaling 64,345. The combined raw keys are unique,
their sorted set is byte-equal to the sorted selected list, and every inner
record names solver `axeyum` and repeats its outer benchmark key exactly.
All eight JSON objects parse successfully.

The 16 final files total 44,786,341 bytes: 38,185,096 raw bytes and 6,601,245
log bytes. The last shard artifact, `raw_7.json`, was written at
`2026-07-25 02:24:38.256933290 -0400`.

## Raw status census

The legacy raw fields yield this descriptive census:

| Reported status | Rows |
|---|---:|
| `sat` | 15,337 |
| `unsat` | 12,035 |
| `unknown` | 31,119 |
| null | 5,854 |
| **total** | **64,345** |

Of the 5,854 null-status rows, 5,411 recorded at least 299 seconds of wall
time and 443 recorded less. The schema carries no typed termination or error
field, so the audit does not relabel either group as timeout, crash, resource
exhaustion, or unsupported.

The selected files contain 43,870 non-null expected statuses. Exact string
comparison reports 22,767 agreements, 16,472 `unknown` responses, 4,575 null
responses, and the same 56 opposite `sat`/`unsat` markers already known from
the logs. Those markers remain 25 expected-`sat`/reported-`unsat` and 31
expected-`unsat`/reported-`sat`. The other 20,475 selected files have no
expected status in this legacy population. These are triage counts only; the
stale binary and missing evidence contracts prevent correctness credit even
for the matching strings.

## Final artifact identities

| Raw artifact | Bytes | SHA-256 |
|---|---:|---|
| `raw_0.json` | 4,773,117 | `62e8aa705bf0af771f8b10ef30884cd83db7c5a53169f5bd66dd535f8dccfc2f` |
| `raw_1.json` | 4,773,369 | `1e1b8a858dc75ad56bf0c3a42f76ec4c1a6195c4e407a9036ef84b65cb2438b8` |
| `raw_2.json` | 4,773,165 | `d4ff4f2f528f8c4613877cc58f2cd43b553d7ddd17a50b3ec13361ee908be162` |
| `raw_3.json` | 4,772,941 | `ef54773a9112f816249f79bb6839e61befa12cea75ef9abf7691a03be729cf1c` |
| `raw_4.json` | 4,773,792 | `e7ca92a27f3977075f347b788833d7cda7108f963c24e06df5be9ecc0e28f4ea` |
| `raw_5.json` | 4,772,750 | `cda6093e8cf75e3236334b36670a2ad4d1a7d9eff3acb3ba3bf4ad3a1bb53b9d` |
| `raw_6.json` | 4,774,040 | `222c048d72f1e38823c0fc2bf87728e78bb916fe54f27ca9e748f5cd1cb30ca6` |
| `raw_7.json` | 4,771,922 | `07de7085e5ebc38166e52c6cf505cddd0dce6148cb57e406b69f28d73a53711a` |

| Log artifact | SHA-256 |
|---|---|
| `log_0.log` | `a60ac69413f48071a19878e1935190a50a4a0734e984cdf70f8d1179e659a4de` |
| `log_1.log` | `aa61b7b55aacd642f4e46e4f123294ffbdf03ff9b519c1a270c14a6325299ba8` |
| `log_2.log` | `20a25ce027597bda64519cbf79fdf29d2491cf8262297d7ee9fcf82f7dd2e996` |
| `log_3.log` | `7fbe81c09a754726de19272b039d9e9f4d1a38d6b4ea92124f74f34cb43b703a` |
| `log_4.log` | `b637ecd95e3cc6716d62af171d3c32e6000f1fecdd112b28e4d5ba5c08700843` |
| `log_5.log` | `6c800b084338707335976fcccce0a21a725e4012b185b0f4e3fd18cf9525abb9` |
| `log_6.log` | `e2698c4fe21c3ae618e744da6567ffbae2689568a62c1f1235d7cbf319803fb9` |
| `log_7.log` | `991e919e0449a222d54f19cae20c8e48d2ef964407ac482e0881f48773585cbd` |

These hashes bind this audit snapshot only. The external directory is not an
immutable accepted root, so later byte drift must reject reproduction of this
snapshot rather than silently updating it.

## Operational boundary

No file in the external directory was changed, moved, merged, or scored during
this audit. No host process was stopped because none remained. The current
credited path continues from the accepted 45,905-file official selection and
the integrated E1--E3/F1/F2 mechanisms. This stale 64,345-file run must not be
fed into F3/F4, parity dashboards, public decide rates, or performance claims.
