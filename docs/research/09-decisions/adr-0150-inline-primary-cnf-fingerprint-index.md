# ADR-0150: Inline primary CNF fingerprint index

Status: proposed
Date: 2026-07-14

## Context

ADR-0144's collision-safe hash index is an accepted real-client win, but its
value remains `Vec<usize>`. Every new fingerprint first performs a membership
lookup, then performs an entry lookup, creates an empty vector, and allocates on
the first index push. Genuine 64-bit fingerprint collisions need a list; the
ordinary one-clause bucket does not.

The accepted full Glaurung artifact makes 53,748,044 clause attempts and emits
49,199,541 clauses. Its `register-slice` and `slice-partial` families account
for 53,247,640 attempts (99.1%) and 48,702,009 emitted clauses (99.0%). This is
a larger shared ownership target than ADR-0146--0149's rejected root, planning,
and capacity micro-experiments, and it directly serves the lifter distribution.

## Decision

Replace the bucket-per-fingerprint representation with an inline primary
formula index and a collision-only side table, subject to the Glaurung
acceptance benchmark.

- Store the first formula clause index directly as `fingerprint -> usize`.
- Use the hash-map entry operation once for the common new-fingerprint path.
- On an occupied fingerprint, compare the primary formula-owned clause exactly.
  Only if it differs, inspect or allocate a secondary `fingerprint ->
  Vec<usize>` collision bucket.
- Suppress a clause only after exact full-slice equality against the primary or
  collision indices. A fingerprint collision may cost time and memory but can
  never drop a distinct clause.
- Keep normalization, fingerprints, formula ownership, clause/literal order,
  solver submission, lift maps, and replay unchanged.
- Add a forced-fingerprint-collision regression that inserts two distinct
  clauses and suppresses exact repeats of each.

The decision becomes accepted only if CNF/SAT tests and strict Clippy pass and
five clean representative processes improve both CNF and end-to-end medians
with identical counts, decisions, and replay. A 4 GiB full-tier confirmation is
then required; otherwise restore the ADR-0145 representation and defer this ADR.

## Evidence

The structural and corpus attribution above selects the experiment. Performance
evidence is pending implementation and the predeclared representative/full
gates.

## Alternatives

- **Pre-size the existing fingerprint buckets.** Rejected: ADR-0148/0149 close
  capacity-hint work, and eager allocation is the cost being removed.
- **Store fingerprints only.** Rejected as unsound: a collision could suppress
  a distinct clause.
- **Use an inline-vector dependency.** Deferred: one scalar primary plus a rare
  side table needs no new dependency and keeps the common map entry smaller.
- **Remove duplicate filtering.** Rejected: the full tier skips 4,248,964 exact
  duplicates, and changing downstream CNF is outside this ownership experiment.

## Consequences

The common distinct fingerprint retains one scalar index with no per-bucket
heap allocation and one map entry probe. True collisions pay a second lookup
and side-vector allocation while remaining exact. The real corpus decides
whether the reduced allocator and hash-table work is material end to end.
