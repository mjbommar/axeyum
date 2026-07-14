# ADR-0147: Zero-copy reverse AIG node iteration

Status: proposed
Date: 2026-07-14

## Context

After accepted ADR-0145, CNF planning costs 1.21 seconds on the full canonical
Glaurung tier. Planning performs ordered whole-AIG passes for reachability,
use-counts, compound-gate recognition, private-tree collection, and direct-root
selection. The private AND-tree pass must visit dense node IDs in reverse so a
parent claims eligible helpers before a nested candidate.

`Aig::nodes()` is backed by a copied slice iterator that is already exact-size
and double-ended, but its public opaque return type promises only `Iterator`.
The CNF planner therefore collects every `(AigNodeId, AigNode)` into a temporary
`Vec` solely to call `rev()`. The full tier visits about 43 million AIG nodes,
making this a measured planning-only copy/allocation site.

## Decision

Expose the iterator's existing `DoubleEndedIterator + ExactSizeIterator`
capabilities and consume it directly in reverse, subject to the Glaurung
acceptance benchmark.

- Preserve the exact descending dense-ID visitation order used by the temporary
  vector.
- Do not change AIG node ownership, construction, hashing, gate recognition,
  skip guards, clause generation, or public item types.
- Add a forward/reverse dense-ID contract test in `axeyum-aig`.
- Preserve AIG evaluation, CNF content/order, variable/lift maps, and original
  model replay.

The decision becomes accepted only if the AIG/CNF/SAT suites and strict Clippy
pass and five clean representative canonical processes improve planning and
end-to-end time with identical formula and verdict shape. A full-tier
confirmation is then required; otherwise the temporary vector is restored and
the ADR is deferred.

## Evidence

Pending implementation measurement. The accepted pre-change baseline is
recorded in `bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **Add a separate `nodes_rev()` API.** Rejected: it duplicates an iteration
  surface when the existing iterator already has the required standard traits.
- **Index nodes by integer in `axeyum-cnf`.** Rejected: `AigNodeId` construction
  is intentionally private, and leaking index reconstruction across the crate
  boundary weakens ownership.
- **Fuse all planning passes.** Deferred: gate-recognition dependencies and
  reverse private-tree ownership make that a larger semantic change. Remove the
  isolated copy before considering pass fusion.

## Consequences

The public iterator contract becomes more specific but remains backward
compatible. The planner performs the same reverse pass without per-query node
copying. The real-corpus gate decides whether that copy was material.
