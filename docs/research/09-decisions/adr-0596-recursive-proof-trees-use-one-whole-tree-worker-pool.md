# ADR-0596: Recursive proof trees use one whole-tree worker pool

Status: accepted
Date: 2026-08-27

## Context

ADR-0590 bounded concurrent checking by parallelizing only the root split. That bound was sound,
but it was not work-conserving. In the live `PRIMATEs^-1` MC=7 tree, 30 root children completed
and the nominal four-worker checker fell to two busy threads because each of the two remaining
root children contained a large nested tree that the worker had to traverse sequentially. The
process consumed about 228% CPU while two requested worker slots remained permanently idle.

Recursive thread pools or one process per leaf would obscure the global worker bound. Retaining a
fully reconstructed formula for every tree node would instead make memory proportional to tree
size, up to the command's 65,536-node input ceiling.

## Decision

`axeyum-cnf` adds `check_cube_refutation_reader_tree_fully_parallel` and its progress-callback
variant. A pre-order traversal consumes the reader tree into a depth-first sequence of independent
proof obligations: every leaf DRAT proof, followed by each ancestor's covering DRAT proof after its
children. An obligation retains its reader, child-index path, and literal-cube path, not a formula.
One bounded worker pool reconstructs each obligation formula directly from the trusted root and
checks it with the unchanged file-backed backward DRAT checker.

The ordering matches the sequential checker exactly. Results are sorted by obligation index, so a
scheduling race cannot change the first returned error. Progress advances only over the contiguous
completed prefix and is therefore deterministic. Structural failures are represented at their
depth-first position rather than being accepted or reordered. A reader panic is resumed. Memory for
formula copies and active DRAT checkers is bounded by the explicit worker count; tree metadata and
cube paths remain proportional to the already-loaded certificate tree.

The old root-only APIs remain available. The Boolean-product tree command uses the whole-tree route
when `--workers` is greater than one and names progress as checked obligations, not root children.

## Evidence

The focused cube suite has 20 passing tests. A new two-level positive control checks all five
ordered obligations and observes the deterministic progress sequence `(1,5)` through `(5,5)` with
four workers. A two-failure control still returns the sequentially first path `[0]`. The prior
root-parallel and sequential controls remain green. Warning-denied all-target/all-feature Clippy for
`axeyum-cnf` passes.

The live retained S-box proof tree is the operational target. Replacing its root-only checker is not
a mathematical result: the MC=7 lower bound earns credit only if every leaf and every covering proof
reaches a terminal accepted verdict.

## Consequences

Deep adaptive certificate trees can keep an explicit bounded CPU allocation busy even after broad
upper levels become imbalanced. Each obligation reconstructs the root formula, trading small
repeated CNF construction for bounded memory and dynamic load balancing. The native-only API remains
unavailable on `wasm32`; the unchanged sequential checker is the portable route.
