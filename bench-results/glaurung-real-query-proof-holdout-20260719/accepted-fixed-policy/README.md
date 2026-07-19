# Accepted fixed-policy proof holdout

Two clean processes at Axeyum `d8da4a4534c2b9dc8073bbfb110773e8f39ead3b`
execute ADR-0251's exact 1,024-query manifest after ADR-0252's exact
materialization. Both use CPU 3, artifact v34, raw/full queries, proof-producing
SAT-BV, in-process Z3, deterministic resources, one worker, a 1,000 ms
cooperative certificate deadline, and a 1,500 ms killable whole-worker wall.

## Accepted result

Both repetitions have the same complete population and exact per-query status:

| Gate | Per run | Result |
|---|---:|---|
| Selected queries | 1,024 | 1,024 decided; 0 Unknown, unsupported, or error |
| SAT | 515 | 515 original-query model replays; 0 failure |
| UNSAT | 509 | 509 independently checked CNF DRAT proofs; 0 missing |
| Manifest comparison | 1,024 | 1,024 agree; 0 disagreement |
| Z3 comparison | 1,024 | 1,024 agree; 0 disagreement or skip |
| End-to-end attempts | 509 | all partitioned; 508 certified, 1 not-certified |
| Hard whole-worker timeout | 509 | the same one row in both repetitions |
| Recheck/contradiction/worker alarms | 509 | 0 |

The fixed stronger-certificate coverage is therefore 508/509, or
99.80353634577604%. The retained miss is the `slice-partial` UNSAT query with
content hash
`10efa33d48cb8a87ecea95ed32605d42e912c0b23cb4e12ba3ec61fd5fd71f82`.
Its primary Axeyum result agrees with both the manifest and Z3 and its CNF DRAT
rechecks; only the separate whole-certificate worker reaches the fixed 1,500 ms
wall. It remains in the denominator and is not a proof failure, solver verdict,
or omitted row.

The fail-closed analyzer accepts the join: source, manifest, configuration, and
environment identities match; every fatal correctness gate passes; and the
per-query certification partition is stable. Whole-certificate timing is
descriptive assurance work only. Run 1 has p50 6.530 ms / p95 339.365 ms; run 2
has p50 6.544 ms / p95 335.290 ms. Neither distribution is solver-performance
evidence.

Together with ADR-0235's disjoint 162-query representative, the accepted real
denominator now contains 1,186 unique queries: 603 SAT model replays and 583
UNSAT CNF DRAT rechecks. Stronger end-to-end coverage is 582/583
(99.828473413379%), with this one stable fixed-policy miss.

## Artifacts

- [`analysis.json`](analysis.json) is the accepted two-run join.
- [`execution-manifest.json`](execution-manifest.json) binds source, binary,
  materialization, raw artifacts, deterministic compressed artifacts, and logs.
- [`materialization.json`](materialization.json) records exact 1,024-file
  membership and byte verification.
- [`raw/artifact-v34-run1.json.gz`](raw/artifact-v34-run1.json.gz) and
  [`raw/artifact-v34-run2.json.gz`](raw/artifact-v34-run2.json.gz) are
  deterministic `gzip -n -9` encodings of the complete raw JSON artifacts.
  Decompress them before passing them back to the analyzer.
- [`run-summary.stderr.log`](run-summary.stderr.log) is the byte-identical
  one-line process summary from both repetitions; both stdout streams are
  empty.

## Claim boundary

This result establishes complete primary decision, oracle, replay, and CNF
proof agreement on the registered holdout and measures stronger certification
coverage under one fixed resource policy. The hash-stratified verdict-balanced
selection is not prevalence-weighted. Do not infer a speedup, a full-corpus
proof rate, a concretization finding-recall claim, or permission to reopen
symbolic memory.
