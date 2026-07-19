# ADR-0259: Preregister cold CNF construction attribution

Status: accepted
Date: 2026-07-19

Result state: fixed 162-query measurement accepted; no optimization selected

## Context

The durable Glaurung feedback assigns the cold one-shot optimization target to
term-to-AIG-to-CNF lowering, not SAT. Existing post-ADR-0175 attribution times
CNF planning, variable allocation, gate encoding, and root encoding, and counts
attempted, tautological, duplicate, and emitted clauses. It does not distinguish
the literal-canonicalization and fingerprint-index work inside gate/root
encoding.

ADR-0200 already rejected replacing the primary clause fingerprint map with
linear-probed open addressing: identical structure accompanied an 8.55% CNF
regression. Another data-structure or encoding change without finer evidence
would repeat that guess.

## Decision

Add an explicitly opt-in cold CNF construction profile with no counters or hot-
loop branches in the ordinary monomorphized encoder. Keep `tseitin_encode` as
the production route and add a separately selected profiled instantiation.
Thread the opt-in through `SolverConfig`, `BvLayerStats`, and `axeyum-bench` as
`--profile-cnf-construction`; bind it into artifact configuration identity.

The complete profile must report:

- declared clause literals and actually visited literals;
- false constants and repeated literals dropped;
- tautologies split by true constants versus complementary literals;
- canonical literal total plus empty, unit, binary, ternary, and larger-clause
  buckets;
- primary fingerprint-index vacant and occupied probes;
- primary exact duplicates;
- collision-bucket exact comparisons and exact duplicates; and
- genuine equal-fingerprint/distinct-clause collision inserts.

Fail closed unless these identities hold:

- non-tautological attempts equal the sum of canonical-length buckets;
- the same attempts equal primary vacant plus occupied probes;
- occupied probes partition into primary duplicates, collision duplicates, and
  collision inserts;
- duplicate clauses equal primary plus collision duplicates;
- emitted clauses equal primary vacant plus collision inserts; and
- total tautologies equal the two named tautology causes.

Focused tests must prove that the ordinary route marks the detailed profile
unavailable/zero, the profiled route preserves byte-identical CNF and roots,
and crafted constant, repeated-literal, complementary-literal, duplicate-clause,
and forced-fingerprint-collision cases satisfy exact counters.

## Fixed real-query measurement

After the implementation commit, run one clean detached release process over
the accepted corrected-wide-v3 representative population:

- manifest SHA-256 `7818686b...`;
- exactly 162 queries: 88 SAT / 74 UNSAT;
- exact families: arithmetic 36, comparison 12, mixed 7, register-slice 52,
  slice-partial 54, trivial 1;
- raw policy (`--rewrite off`), `sat-bv`, in-process Z3 comparison, one job;
- 10,000 ms wall, 2,000,000 resource units, 300,000 nodes, 3,000,000 CNF
  variables, and 8,000,000 CNF clauses; and
- 100% decided, manifest/Z3 agreement, and original-model replay required.

Timing from the profiled process is diagnostic only. Preserve exact aggregate
and per-family counters and every invariant. Select no optimization in this ADR;
use the result to preregister one isolated follow-on or to close the lane if no
material category is exposed.

## Implementation boundary

The implementation preserves two distinct monomorphs. The ordinary encoder
uses a zero-sized `DisabledConstructionProfile`; its forced-inline no-op methods
and counter storage disappear at the hot call sites. The opt-in encoder carries
`CnfConstructionProfile` and is selected only by
`tseitin_encode_profiled`/`SolverConfig::profile_cnf_construction`.

Artifact v35 binds `--profile-cnf-construction` into configuration identity and
publishes every counter and invariant both per instance and in the corpus
aggregate. `scripts/analyze-cnf-construction-profile.py` independently re-sums
the instance rows, rejects any failed invariant or incomplete verdict/oracle/
replay population, and emits exact per-family partitions. The paired Just
recipes pin the 162-query population and all six expected family counts.

Pre-observation gates pass:

- all 302 `axeyum-cnf` library tests;
- all 880 `axeyum-solver` library tests;
- all 42 `axeyum-bench` binary tests;
- strict all-target/all-feature Clippy for those three crates; and
- all four analyzer positive/fail-closed tests.

No corrected-wide-v3 profile was read or run while implementing this boundary.
The implementation was committed as `d29470cf` before the fixed clean-detached
release process began.

## Observed result

The fixed process and independent analyzer both completed successfully. The
artifact contains exactly 162 decisions (88 SAT / 74 UNSAT), 162 manifest
agreements, 162 in-process Z3 agreements, 88 original-model replays, zero
Unknown/unsupported/error/disagreement, the six exact family counts, and all
six construction identities true.

Of 396,270 clause attempts, 5,019 were true-constant tautologies and 391,251
were canonicalized. The encoder emitted 271,991 clauses and rejected 119,260
exact duplicates, or 30.4817% of non-tautological attempts. Every duplicate was
a primary exact hit. Collision-bucket comparisons, collision duplicates,
genuine equal-fingerprint/distinct-clause collisions, repeated-literal drops,
and complementary-literal tautologies were all exactly zero. The 1,085,685
visited literals include 186,123 false constants; canonical attempts partition
as 34 empty, 22,730 unit, 255,330 binary, 112,144 ternary, and 1,013 larger.

Duplicate ownership is concentrated by corpus family:

| Family | Non-taut attempts | Exact duplicates | Duplicate rate | Share of all duplicates |
|---|---:|---:|---:|---:|
| arithmetic | 32,111 | 128 | 0.3986% | 0.1073% |
| comparison | 1,305 | 492 | 37.7011% | 0.4125% |
| mixed | 132 | 0 | 0% | 0% |
| register-slice | 137,078 | 31,035 | 22.6404% | 26.0230% |
| slice-partial | 220,625 | 87,605 | 39.7076% | 73.4572% |
| trivial | 0 | 0 | n/a | 0% |

Slice-partial SAT rows contain 87,525 of that family's 87,605 duplicates;
this is a descriptive stratum, not evidence of cause or wall-time benefit.

The retained
[`artifact.json`](../../../bench-results/glaurung-cnf-construction-profile-20260719/artifact.json)
has SHA-256 `7125de24...003b`; the independently re-summed
[`analysis.json`](../../../bench-results/glaurung-cnf-construction-profile-20260719/analysis.json)
has SHA-256 `e7c8bcda...116f`. Artifact identity is version 35, config hash
`18d81c58b58db304`, corpus hash `23932b876da74bd1`, and clean source revision
`d29470cfe02696a7675efeff295030597a183c10`.

This closes collision-table, repeated-literal, and complementary-literal work
for this population. It exposes upstream exact duplicate clause generation as
the only material measured category, but counts are not timing and do not
authorize an optimization. ADR-0260 preregisters first-origin/duplicate-origin
attribution before any generator-elision change.

## Consequences

The next GQ5 decision will distinguish the first producer of an emitted clause
from the later producer of its exact duplicate rather than extrapolating from
the historical 84% aggregate or a failed map analogy. Production semantics and
ordinary benchmark identity remain unchanged. SAT tuning, demand slicing,
internal AND flattening, and another open-addressed CNF index remain out of
scope.
