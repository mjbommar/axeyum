# ADR-0147: Zero-copy reverse AIG node iteration

Status: deferred
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

The experiment was admitted only if the AIG/CNF/SAT suites and strict Clippy
pass and five clean representative canonical processes improve planning and
end-to-end time with identical formula and verdict shape. A full-tier
confirmation would then be required. Planning improved, but end-to-end time did
not, so the temporary vector and narrower iterator contract are restored and no
full run is authorized.

## Evidence

The implementation passed all nine `axeyum-aig` tests, all 283 `axeyum-cnf`
tests, and strict Clippy under the 4 GiB cap. All five representative processes
were 100% decided with zero errors, manifest/oracle disagreements, or replay
failures, and formula shape stayed identical.

Against accepted ADR-0145:

- median planning improves 0.01207 → 0.01177 seconds (-2.49%);
- median total regresses 0.18985 → 0.19083 seconds (+0.51%);
- mean total regresses 0.18970 → 0.19122 seconds (+0.80%); and
- median CNF regresses 0.07298 → 0.07557 seconds (+3.55%).

The isolated planning saving projects to roughly 0.03 seconds on the 1.21-second
full planning stage and does not satisfy the end-to-end acceptance rule. The
candidate revision is `99e93a08`; artifacts remain beside the access-controlled
capture. The compact negative result is recorded in
`bench-results/glaurung-qfbv-2026-07-14.md`.

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

The candidate is not retained. Although removing the copy measurably improves
planning, the saving is too small and did not improve the whole pipeline.
Further planning work should require a larger structural reduction or wait
until later changes make planning material; a local subphase win is not enough.
