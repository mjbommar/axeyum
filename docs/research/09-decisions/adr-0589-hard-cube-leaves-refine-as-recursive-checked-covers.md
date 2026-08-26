# ADR-0589: Hard cube leaves refine as recursive checked covers

Status: accepted
Date: 2026-08-26

## Context

ADR-0543 composes one flat cube layer and ADR-0587 checks a single retained leaf. In the
`PRIMATEs^-1` MC=7 search, top-level cube 8 took 79 minutes to decide and its proof-producing
replay grew past a gigabyte before completion. A second five-selector split closed 30 of 32
children immediately; the work was concentrated in two children. Requiring one flat depth or
one monolithic leaf would either multiply easy work or retain an artifact that may outgrow the
backward checker.

## Decision

`axeyum-cnf` admits a recursive reader tree. Each node is either an ordinary textual DRAT leaf
or a split containing literal cubes, one child tree per cube, and a DRAT proof that those cubes
cover the node. The checker starts from one trusted root formula, reconstructs every child as
`parent AND cube`, checks leaves with the file-backed backward checker, and independently
reconstructs and checks every covering formula. Errors carry the exact zero-based child path.

The external front door reads the deterministic manifests emitted by
`emit_boolean_product_cover`. It checks schema, formula dimensions, selector bounds, cube count,
every literal row, and resource caps before building the reader tree. A nested directory wins
only by the explicit `cube-NNNNNN-subcover-v1` convention; otherwise the corresponding DRAT leaf
must exist. Optional prefix selectors and an index let a subtree be bound to a cube regenerated
from an independently supplied outer base formula.

## Evidence

A two-level seven-leaf control over the retained `R_3(x-y=z)` DIMACS checks end to end. Removing
one leaf proof exits 2 before checking. Library tests accept a valid nested composition and
reject a cube/child count mismatch. On the live S-box tree, two completed 32-leaf third-level
subtrees independently pass the existing flat checker; the full cube-8 recursive tree remains
in progress and carries no leaf or target verdict until every branch checks.

## Alternatives

- Let a hard leaf emit one monolithic proof: retained as a competing run, but not required for
  the artifact route.
- Uniformly deepen the entire cover: rejected because measured work is sharply concentrated.
- Trust directory completeness or solver exit codes: rejected; exhaustiveness and every leaf
  remain proof obligations.

## Consequences

An adaptive producer can preserve easy checked regions and refine only hard leaves without a
bespoke proof-stitching format. Recursive checking may still be expensive. Proof metadata is
validated while constructing the tree, but each file is opened lazily only when its branch is
checked; explicit node, depth, per-proof, and aggregate-byte caps make resource limits fail
closed rather than silently certify partial work or exhaust file descriptors.
