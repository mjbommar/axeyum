# ADR-0259: Preregister cold CNF construction attribution

Status: accepted
Date: 2026-07-19

Result state: measurement protocol and artifact-v35 telemetry implemented;
not yet observed on the real corpus

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
The next action is one clean detached release process from the implementation
commit, followed by the fixed analyzer. Timing remains diagnostic and this ADR
still selects no optimization.

## Consequences

The next GQ5 decision will be based on causal work ownership rather than the
historical 84% aggregate or a failed map analogy. Production semantics and
ordinary benchmark identity remain unchanged. SAT tuning, demand slicing,
internal AND flattening, and another open-addressed CNF index remain out of
scope.
