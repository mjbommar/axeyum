# ADR-0144: Collision-safe CNF clause deduplication index

Status: proposed
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

The decision becomes accepted only if focused encoding equivalence tests pass
and clean artifact-v27 representative repetitions improve end-to-end canonical
time without changing variable/clause counts, decisions, or replay. A full-tier
confirmation is then required. Otherwise this ADR is deferred and the ordered
set remains.

## Evidence

Pending implementation measurement. The motivating artifact is recorded in
`bench-results/glaurung-qfbv-2026-07-14.md`.

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
case compares one scalar tree key and retains only an index. The formula should
use less memory and avoid one allocation/copy per attempted unique clause.
Fingerprint computation adds linear work over each short normalized clause;
the real-corpus benchmark decides whether that trade is worthwhile.
