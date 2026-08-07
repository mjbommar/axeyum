# QF_NIA A3 causal census preregistration — 2026-08-07

## Purpose and boundary

This is A3's descriptive census, not an implementation result and not a new
parity score. It freezes the exact retained population, extraction rule, trace
budget, and first-decline classification before the complete 67-row trace is
observed. No solver policy, cap, or route order may change during this census.

The source measurement is the accepted 2026-08-06 QF_NIA entry: Axeyum 34/200,
cvc5 89/200, 22 both, 12 Axeyum-only, 67 reference-only, 99 neither, and zero
disagreements. Its solver stamp is `a505e67e7`. The historical parity sidecar
directory is ignored by Git; A3 therefore retains the exact hash-bound input at
[`evidence/qf-nia-a3/retained-sidecar-v1.tsv`](evidence/qf-nia-a3/retained-sidecar-v1.tsv)
before doing any diagnosis.

## Frozen inputs

| Input | Rows | SHA-256 |
|---|---:|---|
| `bench-results/parity-lists/QF_NIA.txt` | 200 | `19b334d3b91090c87f90bf542a7eaa353915cc8c0220e4fd3e483b41aa71bd61` |
| `docs/plan/evidence/qf-nia-a3/retained-sidecar-v1.tsv` | 200 + header | `392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524` |
| `docs/plan/evidence/qf-nia-a3/reference-only-v1.txt` | 67 | `488a13334d26020461cf7e357e55d8c35630f822a931f5db4577eb6ef3c18e16` |

`scripts/qf_nia_a3_census.py` validates both input digests, exact 200-row
population equality, unique full paths, unique basename binding for the legacy
sidecar, status vocabulary, the complete status matrix, and the exact 67-row
residual count. The residual predicate is fixed as:

```text
axeyum == unsolved AND reference IN {sat, unsat}
```

The emitted residual list preserves committed-list order. Axeyum-only rows are
not diagnostic targets and cannot enter this population.

## Trace protocol

Build `explain_corpus` from the clean preregistration commit, then run one
sequential process over the frozen list:

```sh
cargo build --release -p axeyum-bench --example explain_corpus
MEM_LIMIT_GB=8 timeout 1900 ./scripts/mem-run.sh \
  target/release/examples/explain_corpus \
  --list docs/plan/evidence/qf-nia-a3/reference-only-v1.txt \
  24000 --json > /tmp/axeyum-qf-nia-a3-trace-v1.jsonl
```

The per-query solver timeout is 24,000 ms and the process-wide memory ceiling
is 8 GiB, matching the retained parity protocol. The outer 1,900-second bound
is only a runaway guard. No `AXEYUM_*` lever may be set. This is a diagnostic
run through the verdict-invariant `check_auto_explained` path over QF_NIA flat
queries; it does not replace the shipped-front-door parity result.

Exact-list mode is fail-closed before solving: missing, duplicate, or non-SMT2
entries abort, and JSON `file` identity is the complete list entry rather than
an ambiguous basename. The analyzer then requires exactly 67 JSON objects in
the same order, `status=decided`, route-trace schema 1, and one trace per row.

## Frozen classification

For each ordered trace, the **first causal decline** is the first attempt after
the probe whose outcome is `declined` and whose reason is neither
`not-applicable` nor `unsupported`. Those two reasons describe route shape or
fragment exclusion rather than the first mechanism that spent work and failed
to decide. The bucket key is `(route, reason, kind)`; the complete unnormalized
detail and trace remain attached to every case. If no attempt qualifies, the
row is explicitly classified as `(none, no-causal-decline)`.

The analyzer must retain:

- the raw JSONL SHA-256;
- all 67 exact paths and full traces;
- the classification rule verbatim;
- deterministic bucket counts sorted by key;
- each row's verdict and first causal decline.

## Selection and stop rules

The census may select one implementation cluster only after the complete
artifact validates. Selection must name a single bounded mechanism shared by a
nontrivial bucket, then preregister exact target rows, at least one satisfiable
control, at least one mechanism-near-miss control, and all 34 retained Axeyum
decisions as the no-loss set. A broad cap increase, route reordering, targeting
the 12 Axeyum-only rows, or choosing a file outside the frozen 67 is rejected.

If trace capture is incomplete, identities drift, a wrong verdict appears, or
the first-decline buckets do not support a bounded sound mechanism, A3 stops at
the census and records that result. A candidate is not retained unless a fresh
whole 200-row run preserves all 34 decisions, every SAT answer replays on the
original terms, and the ledger remains disagreement-free.
