# ADR-0144: Collision-safe CNF clause deduplication index

Status: accepted
Date: 2026-07-14

## Context

Artifact v27 makes CNF encoding the largest measured stage on the canonical
Glaurung full tier: 9.40 of 21.07 Axeyum seconds. Gate and root emission account
for 4.79 and 1.91 seconds. Every clause attempt currently normalizes a fresh
`Vec<CnfLit>`, clones it, and searches a `BTreeSet<Vec<CnfLit>>`; unique clauses
then retain both the formula vector and the set's cloned vector. The full tier
makes 53.75 million attempts, emits 49.20 million clauses, and rejects 4.25
million duplicates.

The set exists only for exact membership. It is never iterated to determine CNF
or artifact order, so retaining complete clause copies in an ordered tree is not
part of the deterministic encoding contract.

This is the first bounded GQ5 implementation experiment after
[ADR-0143](adr-0143-opt-in-structural-bit-demand-profiling.md) corrected the
production timing boundary.

## Decision

Replace the cloned-clause ordered set with a deterministic fingerprint-to-formula
index, subject to the Glaurung acceptance benchmark.

- Normalize clauses exactly as before and append accepted clauses in the same
  deterministic gate/root traversal order.
- Compute a stable FNV-1a fingerprint over the complete sorted signed-literal
  sequence. Map that fingerprint to formula clause indices.
- Treat a clause as duplicate only after exact full-slice equality against a
  clause in the fingerprint bucket. A fingerprint collision can cost time but
  cannot drop a distinct clause or change satisfiability.
- Store no second copy of an emitted clause. The `CnfFormula` remains the sole
  owner; the index stores only integer references.
- Do not expose or iterate the index. DIMACS, solver submission, lift maps, and
  artifact order remain byte-deterministic.

The decision is accepted because focused encoding equivalence tests pass
and clean artifact-v27 representative repetitions improve end-to-end canonical
time without changing variable/clause counts, decisions, or replay. A full-tier
confirmation is then required. Otherwise this ADR is deferred and the ordered
set remains.

## Evidence

The collision-safe implementation passes all 282 `axeyum-cnf` unit tests,
including an explicit forced-bucket test showing that a distinct full clause is
not suppressed, plus the SAT-BV and benchmark integration suites and strict
Clippy under the 4 GiB cap.

The first ordered scalar-index experiment was rejected: representative
canonical median total rose from 0.2069 to 0.2450 seconds and CNF encoding from
0.0922 to 0.1286 seconds. Replacing that ordered map with the deterministic
membership-only hash table passed the same five-process gate:

- representative canonical median total: 0.2069 → 0.1938 seconds (-6.31%);
- representative median CNF: 0.0922 → 0.0781 seconds (-15.29%);
- full canonical total: 21.070 → 19.217 seconds (-8.79%);
- full CNF: 9.397 → 7.659 seconds (-18.49%); and
- full Axeyum/Z3 ratio: 2.715x → 2.470x.

Every run is 100% decided with zero errors, manifest/oracle disagreements, or
model-replay failures. The full before/after artifacts emit the same 49,199,541
clauses and have identical CNF-variable distributions. The accepted full
artifact SHA-256 is
`0b1a956a5d92171fa9b822a93006517f2f251aafb46e2c5663d12adfa7087523`;
raw artifacts remain beside the access-controlled capture. The compact result
is recorded in `bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **A randomized `HashSet<Vec<CnfLit>>`.** Rejected: it still stores a second
  clause copy and introduces process-random lookup behavior into bounded runs.
- **Fingerprint-only duplicate suppression.** Rejected: a collision would make
  the encoding unsound by dropping a distinct clause.
- **Remove duplicate suppression.** Rejected: the current full tier observes
  4.25 million duplicate attempts, and downstream SAT cost/size would change.
- **Change gate encodings simultaneously.** Rejected: this experiment isolates
  the measured data-structure/ownership cost before changing clause semantics.

## Consequences

Successful lookup still performs exact equality, but the common non-collision
case uses one scalar fingerprint lookup and retains only an index. The formula
uses less memory and avoids one allocation/copy per attempted unique clause.
Fingerprint computation adds linear work over each short normalized clause;
the real-corpus benchmark demonstrates that this trade is worthwhile.
