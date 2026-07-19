# ADR-0260: Preregister cold duplicate-clause origin attribution

Status: accepted
Date: 2026-07-19

Result state: fixed artifact-v36 observation accepted; exactly one follow-on
cell passes the preregistered rule

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

## Implementation boundary

`CnfClauseOriginPhase`, `CnfClauseOriginTemplate`, and
`CnfClauseOriginSite` give every emission site a stable
`phase/family/direction/template` identity. The profiled encoder carries the
owner node separately. `EnabledDuplicateOriginStore` retains one origin per
emitted formula clause and a deterministic sparse matrix keyed by first site,
duplicate site, and same/cross-owner relation. Collision-bucket duplicates use
the origin attached to the actual equal collision entry rather than the primary
fingerprint entry.

The disabled store remains zero-sized. Ordinary `tseitin_encode` neither
allocates origin metadata nor emits origin stats. The explicitly profiled
`tseitin_encode_profiled_with_origins` route returns exact per-cell clause,
canonical-literal, and empty/unit/binary/ternary/larger counts. The solver
fails closed unless the origin total equals the existing duplicate count and
both profiles satisfy their independent identities.

Artifact v36 publishes the sparse cells per instance and in the corpus
aggregate. The analyzer independently re-sums every cell, length/literal
partition, family/outcome partition, participating-instance count, and largest
single-instance share. It evaluates the fixed 50% / 10-query / 50% selection
rule without selecting an optimization itself.

Pre-observation gates pass:

- all 304 `axeyum-cnf` library tests, including same-owner root duplicates,
  same-template cross-owner, cross-template, root-versus-gate, and forced-
  fingerprint-collision provenance;
- all 880 `axeyum-solver` library tests;
- all 43 `axeyum-bench` binary tests;
- all five analyzer positive/fail-closed tests;
- strict all-target/all-feature Clippy and warnings-as-errors rustdoc for the
  three affected crates;
- qfbv/no-default solver and benchmark checks; and
- a two-query manifest/Z3/replay-complete artifact-v36 micro round trip through
  the independent analyzer.

No corrected-wide-v3 query was run through the origin profiler while this
implementation was developed. The implementation was committed as `1bce10fd`
before the fixed detached measurement began.

## Observed result

The fixed run accepts all 162 decisions (88 SAT / 74 UNSAT), all 162 manifest
and in-process Z3 agreements, all 88 SAT original-model replays, every exact
family count, and every construction/origin identity. Artifact v36 has config
hash `3031046d19deeb81`, corpus hash `23932b876da74bd1`, and clean source
revision `1bce10fd5eb6b96fc6eff692434e7d8e7d79a14b`.

All 119,260 exact duplicates and 229,651 duplicate canonical literals are
attributed. The length partition is 11,997 unit, 107,117 binary, and 146 larger
clauses, with zero empty or ternary duplicates.

Exactly one matrix cell passes the fixed selection rule:

| First/duplicate origin | Owner relation | Duplicates | Share | Queries | Largest-query share |
|---|---|---:|---:|---:|---:|
| `root/and_tree/forward/parity` | same | 107,000 | 89.7199% | 29 | 9.9738% |

All 107,000 selected-cell duplicates are binary and contain 214,000 canonical
literals. They partition as 83,172 slice-partial SAT, 14,894 register-slice
SAT, and 8,934 register-slice UNSAT duplicates. The next cells are same-owner
root AND-tree literals (11,309; 9.4826%) and cross-owner root AND-tree literals
(675; 0.5660%).

The retained
[`artifact.json`](../../../bench-results/glaurung-cnf-duplicate-origin-profile-20260719/artifact.json)
has SHA-256 `aeba00c5...f15`; the independently re-summed
[`analysis.json`](../../../bench-results/glaurung-cnf-duplicate-origin-profile-20260719/analysis.json)
has SHA-256 `17134ac5...066`.

ADR-0260 still selects no production optimization. Its rule authorizes only
ADR-0261's separately preregistered repeated-private-parity-leaf elision
experiment. Counts remain diagnostic and do not establish a wall-time win.

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
