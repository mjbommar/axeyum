# ADR-0146: Reusable direct-root OR-leaf scratch

Status: deferred
Date: 2026-07-14

## Context

After ADR-0145, full canonical Glaurung CNF encoding costs 7.23 seconds. Root
emission accounts for 1.39 seconds, of which `register-slice` and
`slice-partial` account for 1.379 seconds. Per-query root time correlates with
direct-root count (0.920) and reachable AIG nodes (0.953), while those two
families contain 169,758 direct roots.

Planning a distributable negated-AND root already traverses its private OR tree,
collects its leaves and helper nodes, and marks the helpers as skipped. Root
emission traverses the same skipped tree again. The second traversal allocates
fresh leaf and helper vectors even though emission never reads the helper list;
it needs only the leaves long enough to emit the direct clauses.

## Decision

Reuse one encoder-local `Vec<AigLit>` as scratch for the second traversal,
subject to the Glaurung acceptance benchmark.

- Clear the scratch before every candidate side and before returning no plan.
- Require the same skipped private-OR root recognized by planning; do not widen
  the direct-root encoding surface.
- Collect only leaves during emission. Planning remains the sole owner of the
  helper-node list used to establish skip safety.
- Copy each leaf out before ordinary clause emission so mutable encoder work
  cannot retain a borrow into scratch storage.
- Keep clause construction, normalization, exact deduplication, order, variable
  allocation, lift maps, and replay unchanged.

The experiment was admitted only if a multi-root exhaustive regression proved
that scratch contents never leak between roots, the CNF/SAT suites pass, and
five clean representative canonical processes improve end-to-end time with
identical clauses, variables, decisions, and replay. A full-tier confirmation
would then be required. The representative performance gate failed, so the
owned second-traversal vectors are restored and no full run is authorized.

## Evidence

The implementation passed the exhaustive 128-row two-root isolation regression,
all 284 `axeyum-cnf` tests, all 30 SAT-BV integration tests, and strict Clippy
under the 4 GiB cap. All five representative processes were 100% decided with
zero errors, manifest/oracle disagreements, or model-replay failures, and CNF
content stayed identical.

Performance nevertheless regressed against accepted ADR-0145:

- representative median total: 0.18985 → 0.19187 seconds (+1.06%);
- representative mean total: 0.18970 → 0.19242 seconds (+1.43%);
- representative median CNF: 0.07298 → 0.07656 seconds (+4.91%); and
- the matched third run's root subphase: 0.01427 → 0.01456 seconds (+2.05%).

The candidate therefore failed before full-tier admission. Its clean revision
is `6ccc8984`, and the artifacts remain beside the access-controlled capture.
The compact negative result is recorded in
`bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **Retain the complete planning object until root emission.** Deferred: a
  node-indexed option vector is prohibitive on 40.7 million reachable nodes,
  while a separate map/arena adds ownership and lookup complexity before the
  smaller scratch experiment is measured.
- **Skip the second traversal entirely with a compact plan arena.** Deferred as
  the next step only if traversal, rather than allocation, remains material.
- **Use one scratch vector for all clause normalization.** Deferred: that is a
  broader 53.75-million-attempt ownership change and should be measured
  separately from direct-root collection.

## Consequences

The candidate is not retained. Reusable leaf capacity plus the revised second
traversal did not compensate for its overhead on the real corpus. Future direct
root work must avoid the second traversal entirely or target common clause
normalization with a separately measured ownership design; it should not retry
this scratch shape without new evidence.
