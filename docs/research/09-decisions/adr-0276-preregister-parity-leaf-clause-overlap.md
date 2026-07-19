# ADR-0276: Preregister parity-leaf clause-overlap attribution

Status: accepted
Date: 2026-07-19

Result state: zero-row diagnostic preregistration; no fixed-population result

## Context

ADR-0259 attributes 119,260 exact duplicate clause attempts on the fixed
162-query corrected-wide-v3 representative. ADR-0260 then identifies one
dominant cell: 107,000 binary duplicates are emitted by the same positive-root
AND-tree owner and the same forward-parity template. ADR-0261 tests the only
mechanism that origin evidence could justify: remove repeated normalized parity
*leaves* under one owner. The candidate changes every selected counter by zero.

That rejection proves the origin cell did not represent repeated enclosing
leaves. It does not distinguish clauses repeated within one parity leaf from
clauses shared by distinct leaves. The current origin key stops at owner and
emission template, so either mechanism produces the same ADR-0260 cell. A new
implementation inferred from that cell would repeat ADR-0261's mistake.

The durable Glaurung feedback keeps cold term-to-AIG-to-CNF construction as the
measured one-shot target, but also requires complete decisions, exact work,
strict errors, and original-term replay. This ADR therefore adds observation
only. It does not alter IR semantics, clause generation, replay, solving, or the
ordinary encoder.

## Decision

Extend only the opt-in CNF construction profiler with stable parity-leaf
identity and shape. A parity clause origin records:

- the leaf's zero-based order within its AND-tree owner;
- raw input arity;
- false-constant and true-constant input occurrences;
- distinct nonconstant AIG-node count;
- repeated equal-literal pair count; and
- complementary-literal pair count.

The input cap is already three, so every count is exact and bounded. Shape is
observational: do not cancel repeated inputs, fold complementary inputs, or
normalize the production leaf while collecting it.

For every exact duplicate whose first and later origins are both
`and_tree/forward/parity`, record one deterministic overlap row containing the
first and later leaf shapes and exactly one relation:

- `within_leaf`: same owner and same leaf order;
- `cross_leaf_same_owner`: same owner and different leaf order; or
- `cross_owner`: different owners.

Each row carries duplicate clauses, canonical literals, and the existing
empty/unit/binary/ternary/larger clause-and-literal partition. The disabled
profiler remains zero-sized and retains no leaf metadata.

## Accounting invariants

The enabled profile must fail closed unless:

- every parity-overlap row has a valid relation and both shapes satisfy their
  bounded identities;
- row clauses and literals equal their respective length buckets;
- aggregate parity-overlap clauses and literals equal the sum of rows;
- the parity-overlap total equals the complete duplicate-origin matrix filtered
  to parity-first/parity-later cells; and
- the ADR-0259 construction and ADR-0260 duplicate-origin invariants still hold.

Focused tests must begin red and then cover:

- repeated clauses generated within one parity leaf;
- overlapping clauses from two distinct leaves under one owner;
- equal parity clauses from different owners;
- false/true constants, repeated equal literals, complementary literals, and
  distinct nonconstant-node counting;
- ordinary/profiled byte-identical CNF, roots, lift maps, and replay; and
- independent analyzer rejection of relation, shape, row-total, length-bucket,
  instance/summary, verdict, oracle, and replay drift.

## Implementation boundary

Commit `b02b6ab4` implements only the opt-in diagnostic. The disabled
construction-profiler monomorph retains no parity-leaf metadata. The enabled
route records stable leaf order and bounded shape at parity emission sites,
classifies exact parity/parity duplicates into the three frozen relations, and
fails closed when the overlap rows differ from the legacy origin subset.

Artifact v37 publishes the new rows per instance and in the exact corpus sum.
The independent analyzer requires the overlap block for v37, retains read-only
compatibility with artifact v36, checks that the fixed 107,000 same-owner
duplicates are all binary, and compares the complete construction, family, and
origin aggregates byte-for-structure with ADR-0260's retained v2 analysis.

Pre-observation gates pass:

- all 307 `axeyum-cnf` library tests;
- all 21 focused `axeyum-solver` library tests;
- all 44 `axeyum-bench` binary tests;
- all 10 independent analyzer tests, including v36 compatibility and v37
  fail-closed absence/drift cases;
- strict all-target/all-feature Clippy and warnings-as-errors rustdoc for the
  three affected crates;
- `axeyum-solver`'s no-default `qfbv` check and `axeyum-bench`'s no-default
  check; and
- real retained artifact-v36 reanalysis plus an artifact-v37 two-query
  manifest/Z3/replay-complete micro round trip.

The recipe test cannot execute in this checkout because `just` is unavailable;
manual inspection confirms the recipe pins raw rewriting, the complete
decision/oracle/resource gates, the exact fixed population, the 107,000-binary
gate, and the retained ADR-0260 analysis path. No corrected-wide-v3 query has
been observed through v37.

## Fixed real-query measurement

Commit the implementation, artifact schema, analyzer, and tests before reading
the fixed population through the new profile. Then run one clean detached
release process over exactly ADR-0259/0260's unchanged boundary:

- corrected-wide-v3 representative manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- exactly 162 queries, 88 SAT / 74 UNSAT, with family counts 36 arithmetic,
  12 comparison, 7 mixed, 52 register-slice, 54 slice-partial, and 1 trivial;
- raw rewrite-off `sat-bv`, in-process Z3, one job;
- 10,000 ms wall, 2,000,000 BatSat progress checks, 300,000 term-DAG nodes,
  3,000,000 CNF variables, and 8,000,000 CNF clauses; and
- 162/162 decisions, manifest agreement, Z3 agreement, all 88 original-model
  replays, exact source/environment identity, and every construction/origin/
  overlap invariant.

The analyzer must independently re-sum every instance and publish relation,
shape, family, outcome, participating-instance, and largest-instance-share
partitions. It must additionally require that the same-owner parity/parity
subset remains exactly 107,000 binary duplicates and that the complete legacy
construction and origin aggregates reproduce ADR-0260. Profiled timing is
diagnostic and excluded.

## Follow-on selection rule

This ADR selects no optimization. After the fixed observation, at most one
relation-plus-shape cell may motivate a separately preregistered generator
experiment, and only if it:

- owns at least 50% of the complete parity/parity duplicate population;
- occurs in at least 10 queries; and
- is not made to pass by one query contributing more than 50% of that cell.

A qualifying `within_leaf` cell can authorize only local suppression of exact
canonical clauses already generated earlier by the same leaf. A qualifying
`cross_leaf_same_owner` cell can authorize only an owner-local overlap
mechanism. A `cross_owner` result cannot authorize owner-local leaf rewriting.
The follow-on must preregister its exact structural delta, byte/replay identity,
and repeated unprofiled timing gates before implementation. If no cell passes,
close this leaf-overlap lane.

## Consequences

ADR-0261 remains rejected and removed. ADR-0276 does not reinterpret equal
origin labels as equal leaves, does not reopen demand slicing or SAT tuning,
and does not weaken strict sort errors or model replay. The next permissible
step is the one fixed detached v37 observation, not a production optimization
or an unregistered corpus/timing experiment.
