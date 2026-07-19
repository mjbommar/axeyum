# ADR-0253: Accept the wider real-query proof holdout with one retained miss

Status: accepted
Date: 2026-07-19

## Context

ADR-0251 preregistered a disjoint, verdict-balanced 1,024-query real QF_BV
holdout with 515 SAT and 509 UNSAT rows. ADR-0252 preserved a zero-query
membership rejection and preregistered exact materialization. The corrected
campaign now has two clean detached artifact-v34 repetitions under the unchanged
1,000 ms cooperative and 1,500 ms whole-certificate process policies.

The decision must distinguish complete primary correctness/proof evidence from
resource-bounded stronger certification. A stable hard timeout is retained
coverage, not permission to omit a row, call it a proof failure, or claim full
stronger certification.

## Decision

Accept the holdout as a complete primary correctness and CNF-proof denominator,
and accept 508/509 (99.80353634577604%) as the measured stronger end-to-end
certificate coverage under the preregistered fixed policy.

Both repetitions decide all 1,024 rows as the exact 515 SAT / 509 UNSAT
manifest split. All 1,024 decisions agree with both the manifest and in-process
Z3. Every SAT model replays against the original query. Every UNSAT produces an
independently checked CNF DRAT proof. There are zero Unknown, unsupported,
error, disagreement, skipped-oracle, replay-failure, missing-proof,
satisfiable-contradiction, certificate-recheck-failure, or worker-error rows.

Every UNSAT enters the separate end-to-end attempt partition. Exactly one
`slice-partial` row, content hash
`10efa33d48cb8a87ecea95ed32605d42e912c0b23cb4e12ba3ec61fd5fd71f82`,
hits the 1,500 ms whole-worker wall in both repetitions. It remains a primary
UNSAT with agreeing Z3 and checked CNF DRAT; its stronger status is
`not-certified` plus `hard_timeout`. The analyzer confirms exact per-query
status stability and matching source, manifest, configuration, and environment
identities.

Together with ADR-0235's disjoint 162-query representative, the accepted real
denominator is now 1,186 unique queries: 603 SAT model replays, 583 UNSAT CNF
DRAT rechecks, and 582/583 stronger end-to-end certificates
(99.828473413379%).

## Evidence

The preserved bundle is
`bench-results/glaurung-real-query-proof-holdout-20260719/`. Its corrected
execution records:

- clean source revision `d8da4a4534c2b9dc8073bbfb110773e8f39ead3b`;
- selected manifest SHA-256
  `67c7f14f5f2f8db1eaa1bb17649cf3623e268e3f7ea678cbe53326bfa8cd899b`;
- exact materialized query-set SHA-256
  `51942a9de70485d77cba32ef75701d721a990662c07451c0a72b500e92897ad2`;
- raw artifact SHA-256 values `b6d74d75...` and `8bc8822b...`; and
- a fail-closed analyzer exit of zero with stable per-query coverage.

The complete raw JSON artifacts are retained as deterministic gzip streams
alongside raw and compressed hashes. The first full-root attempt remains a
separate pre-execution rejection and contributes no result.

## Consequences

The concrete DRAT deployability claim now covers every UNSAT in a materially
wider, preregistered real-query population, while the stronger certificate
claim is precisely 508/509 under one fixed policy. Do not tune the deadline and
retroactively call the adapted result this experiment. Any diagnostic follow-up
on the retained row is separate work and cannot remove it from this denominator.

This result is not performance evidence and the hash-stratified selection is
not prevalence-weighted. It does not change the concretization policy,
establish finding recall, or reopen symbolic memory. Publication work should
move to an independent/standardized proof consumer, timeout-sensitive neutral
breadth, and a genuinely broader labeled finding population rather than another
scalar concretization setting.
