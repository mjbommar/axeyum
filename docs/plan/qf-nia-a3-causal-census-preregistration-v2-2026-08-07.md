# QF_NIA A3 causal census preregistration v2 — 2026-08-07

## Purpose and repair boundary

This supersedes the execution protocol—not the frozen population or extraction
predicate—of the v1 preregistration. V1 aborted after 59 of 67 records on the
row-60 `distinct` ingest blow-up and is inadmissible. The failure and repair are
recorded in the
[`v1 attempt note`](qf-nia-a3-causal-census-attempt-v1-2026-08-07.md) and
[ADR-0378](../research/09-decisions/adr-0378-bounded-smtlib-distinct-expansion.md).

The fixed code boundary is
`63c82a6ef113bba8cf80fa6871674d9c4514c1f9`. The release
`target/release/examples/explain_corpus` built from that exact code has SHA-256
`cfb8bcba086d8bd7d60df9c645405dc42857861d18472e4d553e2d012d4c5a08`.
The v2 run must verify both identities before starting. No solver, parser,
resource, route-order, or trace-policy change is permitted during the run.

## Frozen population

The population remains the accepted 2026-08-06 QF_NIA entry: Axeyum 34/200,
cvc5 89/200, 22 both, 12 Axeyum-only, 67 reference-only, 99 neither, and zero
disagreements.

| Input | Rows | SHA-256 |
|---|---:|---|
| `bench-results/parity-lists/QF_NIA.txt` | 200 | `19b334d3b91090c87f90bf542a7eaa353915cc8c0220e4fd3e483b41aa71bd61` |
| `docs/plan/evidence/qf-nia-a3/retained-sidecar-v1.tsv` | 200 + header | `392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524` |
| `docs/plan/evidence/qf-nia-a3/reference-only-v1.txt` | 67 | `488a13334d26020461cf7e357e55d8c35630f822a931f5db4577eb6ef3c18e16` |

The residual predicate remains exactly:

```text
axeyum == unsolved AND reference IN {sat, unsat}
```

The 12 Axeyum-only rows remain outside the diagnostic target population.

## V2 trace protocol

Run a new sequential process from row 1; do not reuse the v1 prefix:

```sh
test "$(git rev-parse 63c82a6ef^{commit})" = \
  "63c82a6ef113bba8cf80fa6871674d9c4514c1f9"
test "$(sha256sum target/release/examples/explain_corpus | cut -d' ' -f1)" = \
  "cfb8bcba086d8bd7d60df9c645405dc42857861d18472e4d553e2d012d4c5a08"
MEM_LIMIT_GB=8 timeout 1900 ./scripts/mem-run.sh \
  target/release/examples/explain_corpus \
  --list docs/plan/evidence/qf-nia-a3/reference-only-v1.txt \
  24000 --json > /tmp/axeyum-qf-nia-a3-trace-v2.jsonl
```

The per-query timeout is 24,000 ms; the process-wide memory ceiling is 8 GiB;
the 1,900-second outer bound is only a runaway guard. No `AXEYUM_*` lever may
be set.

## Complete-record contract

The analyzer requires exactly 67 objects in committed-list order. Every object
must be one of:

1. `status=decided`, with a `sat`/`unsat`/`unknown` verdict and route-trace
   schema 1; or
2. `status=ingest-resource-limit`, with verdict `unknown`, a nonempty detail,
   and no route trace because typed route dispatch never began.

Read, syntax, scoped-session, generic parse, or operational errors invalidate
the entire artifact. An ingest resource record is complete causal evidence and
maps to bucket
`(smtlib-ingest, resource-limit, ResourceLimit)`. For a decided row, the first
causal decline remains the first ordered declined attempt after the probe whose
reason is neither `not-applicable` nor `unsupported`. Full trace/detail data is
retained per row; buckets are deterministic and sorted.

The v2 analyzer schema is `axeyum-qf-nia-a3-causal-census-v2`. After capture:

```sh
python3 scripts/qf_nia_a3_census.py \
  --population bench-results/parity-lists/QF_NIA.txt \
  --sidecar docs/plan/evidence/qf-nia-a3/retained-sidecar-v1.tsv \
  --population-sha256 19b334d3b91090c87f90bf542a7eaa353915cc8c0220e4fd3e483b41aa71bd61 \
  --sidecar-sha256 392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524 \
  --expected-rows 200 --expected-reference-only 67 \
  --output-list /tmp/axeyum-qf-nia-a3-reference-only-v2.txt \
  --trace-jsonl /tmp/axeyum-qf-nia-a3-trace-v2.jsonl \
  --output-census /tmp/axeyum-qf-nia-a3-census-v2.json
cmp docs/plan/evidence/qf-nia-a3/reference-only-v1.txt \
  /tmp/axeyum-qf-nia-a3-reference-only-v2.txt
```

## Selection and stop rules

Only a complete validated v2 artifact may select one bounded implementation
cluster. Selection must name a nontrivial shared mechanism and preregister exact
target rows, a satisfiable control, a mechanism-near-miss control, and all 34
retained Axeyum decisions as the no-loss set.

The ingest-resource row is a permanent process-survival control, not an A3
score target and not permission to raise the `distinct` ceiling. Any incomplete
capture, wrong verdict, identity drift, parser/solver policy change, or absent
bounded cluster stops A3 without implementation credit. Final retention still
requires a fresh 200-row run, all 34 decisions preserved, every SAT model
replayed on original terms, and zero disagreements.
