# ADR-0260: Preregister cold duplicate-clause origin attribution

Status: accepted
Date: 2026-07-19

Result state: measurement protocol selected; implementation and observation
not yet started

## Context

ADR-0259's fixed 162-query profile finds 119,260 exact duplicate clauses,
30.4817% of all non-tautological attempts. Every duplicate hits the primary
fingerprint entry; collision-bucket work is zero. Slice-partial queries own
73.4572% of duplicates and register-slice owns 26.0230%, but the existing
counters do not identify which emission site first produced a canonical clause
and which later site reproduced it.

Changing the fingerprint index would therefore attack a path that did no work.
Deleting a gate clause or root assertion without origin evidence risks changing
CNF semantics. The next measurement must name the redundant producer while
retaining exact first-producer provenance.

## Decision

Extend only the opt-in detailed construction profiler. Every attempted clause
receives a stable origin containing:

- phase: ordinary gate encoding or root encoding;
- encoder family: XOR, not-ITE, not-AND, AND tree, parity implication, binary
  AND, direct negative-AND distribution, or root unit;
- implication direction: forward, reverse, direct distribution, or assertion;
- stable template slot within the family/direction; and
- owner AIG node identity for same-owner versus cross-owner classification.

For each emitted primary clause, the enabled profiler retains its origin in a
profile-only vector indexed by the existing formula-clause index. On every
primary or collision exact duplicate, it records the first-origin/duplicate-
origin pair, canonical clause-length bucket, same-owner/cross-owner relation,
and duplicate canonical-literal count. The disabled profiler remains a zero-
sized monomorph with no metadata allocation or retained origin table.

Artifact v36 will expose exact aggregate and per-instance origin totals. The
independent analyzer must re-sum all rows and publish:

- duplicate attempts and duplicate canonical literals by duplicate origin;
- the complete nonzero first-origin by duplicate-origin matrix;
- same-owner and cross-owner partitions for every matrix cell;
- empty/unit/binary/ternary/larger duplicate-length partitions;
- per-family and SAT/UNSAT partitions; and
- for each nonzero duplicate-origin cell, participating-instance count and the
  largest single-instance share.

Fail closed unless origin-attributed duplicate attempts exactly equal
ADR-0259's `duplicate_clauses_skipped`, origin-attributed duplicate literals
equal the sum of length-aware duplicate literals, same-owner plus cross-owner
equals every origin-matrix cell, and the detailed construction identities still
hold. Collision duplicates remain supported and must carry the origin of the
actual first equal clause, even though ADR-0259 observed none.

Focused tests must start red and then prove:

- ordinary and profiled encoders remain byte-identical, root-identical, and
  replay-identical;
- the disabled store is zero-sized and has no origin metadata;
- crafted same-template/same-owner, same-template/cross-owner, cross-template,
  root-versus-gate, and forced-fingerprint-collision duplicates land in exactly
  one expected matrix cell; and
- aggregate, matrix, owner-relation, literal, length, family, outcome, and
  instance-participation sums fail closed under independent mutation tests.

## Fixed real-query measurement

Commit implementation and all tests before observing the corpus. Then run one
clean detached release process over the unchanged ADR-0259 population and
policy:

- corrected-wide-v3 representative manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- exactly 162 queries, 88 SAT / 74 UNSAT, with family counts 36/12/7/52/54/1;
- raw rewrite-off `sat-bv`, in-process Z3, one job;
- 10,000 ms wall, 2,000,000 resource units, 300,000 nodes, 3,000,000 CNF
  variables, and 8,000,000 clauses; and
- 100% decisions, manifest/Z3 agreements, and original-model replay.

Profiled timing remains diagnostic. Preserve the raw artifact and independent
analysis. Do not choose an optimization in this ADR.

## Follow-on selection rule

After observation, a duplicate-origin cell may motivate one separately
preregistered generator-elision experiment only if it:

- owns at least 50% of all exact duplicate attempts;
- appears in at least 10 queries; and
- is not made to cross the threshold by one query owning more than 50% of the
  cell.

The later implementation still needs byte-identical/replay-identical tests and
repeated unprofiled end-to-end wall-time evidence; operation counts alone never
establish a speedup. If no cell passes, close this cold duplicate-origin lane
for the current population rather than combining unrelated cells post hoc.

## Consequences

The follow-up is another bounded diagnostic, not a new CNF architecture. It
keeps ordinary production behavior and storage unchanged, rejects another
index redesign, and prevents the large family-level duplicate count from being
mistaken for a known optimization. GQ5 remains measured and cold-only; retained
warm work, SAT tuning, demand slicing, and Glaurung concretization policy are
unaffected.
