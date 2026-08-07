# QF_NIA A3 causal census v2 result — 2026-08-07

## Verdict

The repaired v2 census is **complete and admissible**. All 67 frozen
reference-only rows were captured from row 1 in committed-list order under the
preregistered 8 GiB process ceiling and 24,000 ms per-query budget. The process
exited 0; every row is either a schema-1 route trace or the one permitted typed
SMT-LIB ingest resource decline. There was no crash, missing row, identity
drift, wrong verdict, or continuation from the invalid v1 prefix.

The retained machine-readable result is
[`causal-census-v2.json`](evidence/qf-nia-a3/causal-census-v2.json): 67 cases,
3,761 lines, 159,223 bytes, SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`.
It binds the raw 67-line JSONL capture by SHA-256
`d38a94e41bbc5a41994fcd33f9983327f1247e164ef143fee038a10c25b7592d`.
The raw capture is not required for interpretation because the retained JSON
contains every complete trace and decline detail, but its digest prevents a
different capture from being substituted.

## Frozen identities

| Authority | Rows | SHA-256 |
|---|---:|---|
| `bench-results/parity-lists/QF_NIA.txt` | 200 | `19b334d3b91090c87f90bf542a7eaa353915cc8c0220e4fd3e483b41aa71bd61` |
| `evidence/qf-nia-a3/retained-sidecar-v1.tsv` | 200 + header | `392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524` |
| `evidence/qf-nia-a3/reference-only-v1.txt` | 67 | `488a13334d26020461cf7e357e55d8c35630f822a931f5db4577eb6ef3c18e16` |
| raw v2 trace JSONL | 67 | `d38a94e41bbc5a41994fcd33f9983327f1247e164ef143fee038a10c25b7592d` |
| retained v2 census JSON | 67 | `2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a` |

The capture used parser/solver repair commit `63c82a6ef113bba8cf80fa6871674d9c4514c1f9`
and release `explain_corpus` binary SHA-256
`cfb8bcba086d8bd7d60df9c645405dc42857861d18472e4d553e2d012d4c5a08`.
The extraction rerun reproduced the frozen reference-only list byte-for-byte
and reproduced the retained census digest exactly.

## Causal partition

| First causal route | Reason | Kind | Cases |
|---|---|---|---:|
| `nia-linearize` | `budget` | — | 52 |
| `nia-linearize` | `incomplete` | `incomplete` | 13 |
| `nia-linearize` | `verifier-rejected` | — | 1 |
| `smtlib-ingest` | `resource-limit` | `ResourceLimit` | 1 |

All 67 final verdicts remain `unknown`; this artifact is causal measurement,
not a breadth gain. The 13-case incomplete bucket has one identical first
decline: `arith DPLL candidate failed full model replay`. It contains seven
reference-SAT and six reference-UNSAT rows. This mixed population is the first
bounded implementation cluster: the SAT members are possible recovery targets,
while the UNSAT members are compulsory near-miss controls against accepting an
unfaithful linearized candidate.

The 52 budget cases are not one mechanism: their downstream failures include
pre-lowering clause estimates above 64,000,000, width-ladder timeouts, and exact
width/model-overflow declines. They remain deferred until the replay cluster is
resolved. The one ingest-resource row is a permanent process-survival control
under ADR-0378 and is never a score target or permission to raise the
`distinct` ceiling.

## Next boundary

The exact replay-failure cluster and its controls are preregistered in
[`qf-nia-a3-model-replay-cluster-preregistration-v1-2026-08-07.md`](qf-nia-a3-model-replay-cluster-preregistration-v1-2026-08-07.md).
The first action is diagnostic: distinguish a false assertion from evaluation
failure, bind the first failing assertion by input ordinal and term ID, and
identify whether the reconstructed integer model omits a symbol or violates a
selected arithmetic literal. No SAT policy changes until that diagnosis exists.

