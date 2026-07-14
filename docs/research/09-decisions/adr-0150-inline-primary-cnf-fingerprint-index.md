# ADR-0150: Inline primary CNF fingerprint index

Status: accepted
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

The structural and corpus attribution above selects the experiment. The
implementation passes all 283 `axeyum-cnf` tests, 31 SAT-BV integration tests,
strict Clippy, formatting, and documentation-link checks under the 4 GiB cap.
Its forced-collision regression inserts two distinct clauses under the same
fingerprint, retains both in formula order, and suppresses exact repeats of
both.

The five-process representative gate against accepted revision `c139d73b`
reports:

- total p50 0.189851 → 0.165169 s (-13.00%) and mean 0.189702 → 0.165105 s
  (-12.97%);
- CNF p50 0.072978 → 0.051845 s (-28.96%) and mean 0.073648 → 0.051885 s
  (-29.55%);
- gate/root p50 improve 24.94%/23.07%; and
- total CV falls 0.570% → 0.212%.

All five trials remain 128/128 decided (64 SAT / 64 UNSAT), with zero errors,
disagreements, or replay failures and the exact same 549,350 attempts, 40,998
duplicates, 507,195 clauses, and 1,911 direct roots.

The 4 GiB full-tier confirmation at revision `4d66fc0e` remains 13,462/13,462
decided (1,774 SAT / 11,688 UNSAT), with zero errors, disagreements, or replay
failures. Against `c139d73b`:

- total falls 18.6909 → 16.5397 s (-11.51%);
- CNF falls 7.2313 → 5.1768 s (-28.41%);
- gate/root emission falls 3.1861/1.3910 → 2.3999/1.0835 s
  (-24.68%/-22.11%); and
- Axeyum/Z3 falls 2.399x → 2.136x while Z3 is stable at 7.79/7.74 s.

Both full artifacts make 53,748,044 attempts, skip 4,248,964 duplicates, and
emit exactly 49,199,541 clauses. The accepted artifact SHA-256 is
`43ff5944eacd8e511a0c4656b3cdd99f0794ba376f6580a9883527684618075e`.

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
and side-vector allocation while remaining exact. The real corpus confirms the
reduced allocator and hash-table work is material end to end. Bit blast is now
the largest full stage at 5.88 seconds, narrowly ahead of CNF at 5.18 seconds;
future work returns to measured residual lowering/AIG construction rather than
more capacity micro-tuning.
