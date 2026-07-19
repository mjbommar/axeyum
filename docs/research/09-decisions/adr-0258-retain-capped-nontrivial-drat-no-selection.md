# ADR-0258: Retain capped nontrivial DRAT no-selection

Status: accepted
Date: 2026-07-19

## Context

ADR-0257 preregistered a proof-shape-conditioned but deterministic scan before
another holdout proof was observed. It fixed the first 32 remaining expected-
UNSAT rows in ascending content-hash order, retained every attempt, and required
a multi-line proof whose CNF did not externally verify with an empty proof.

The scan ran from clean detached Axeyum `10ee9795` with selector SHA-256
`472b96ff...`, exporter binary SHA-256 `41d764a4...`, and the pinned checker
binary SHA-256 `c0b9bd6a...`.

## Decision

Accept and retain the preregistered `no-selection` result. Do not widen the
32-row cap.

All 32 source hashes match, and all 32 exports succeed and self-recheck. Every
exported DRAT is the same two-byte, one-line empty-clause text with SHA-256
`9a271f2a...`. Therefore no row reaches the independent `>2 bytes` and `>1
line` gates, regardless of checker behavior.

Pinned `drat-trim` prints an exact `s VERIFIED` line on both the real and empty
proof for all 32 rows. Five rows are classified as input-unit propagation, 11
as complementary unit clauses, and 16 as trivial UNSAT. The first 16 paths
exit zero; the 16 trivial-UNSAT paths exit one despite the marker. Preserve
both exit code and marker rather than normalizing this checker behavior away.

## Evidence

The committed result under
`bench-results/glaurung-external-drat-20260719/nontrivial-scan-no-selection/`
retains every ordered attempt with source, DIMACS, and proof hashes/sizes;
export/checker exit and timeout states; exact stream hashes; and normalized
checker classifications. The result-record SHA-256 is `3821b66d...`. The raw
execution report is 146,797 bytes at SHA-256 `fe0b2dc7...` and remains outside
Git with the access-controlled source and derived proof artifacts.

## Consequences

The real-query publication claim stays deliberately narrow: Axeyum exports
standard DRAT consumed by an independent checker, but this bounded population
does not furnish a nontrivial learned-clause trace. Do not describe the 32-row
scan as proof prevalence, and do not imply that external clausal checking
certifies source-to-CNF lowering.

Further hash-order scanning is closed by the preregistered cap. Reopen
nontrivial external proof evidence only for a separately motivated workload
whose UNSAT route actually exercises proof-producing SAT search; do not keep
mining this holdout. Return publication effort to the broader labeled-finding
population and timeout-sensitive neutral breadth while symbolic memory remains
gated.
