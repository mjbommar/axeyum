# ADR-0146: Reusable direct-root OR-leaf scratch

Status: proposed
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

The decision becomes accepted only if a multi-root exhaustive regression proves
that scratch contents never leak between roots, the CNF/SAT suites pass, and
five clean representative canonical processes improve end-to-end time with
identical clauses, variables, decisions, and replay. A full-tier confirmation
is then required; otherwise the ADR is deferred and the owned second-traversal
vectors are restored.

## Evidence

Pending implementation measurement. The source and corpus attribution are
recorded in `bench-results/glaurung-qfbv-2026-07-14.md`.

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

The encoder retains capacity equal to the largest private OR tree in one query
instead of allocating two vectors per distributable root. The tree is still
traversed twice, keeping planning and emission ownership simple. The real-corpus
gate decides whether the saved allocation is material.
