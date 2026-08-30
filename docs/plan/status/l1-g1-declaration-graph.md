# L1 G1 -- declaration graph (lane `l1-g1-declaration-graph`)

Status: IN PROGRESS -- first commit, scaffolding only.

## Task

Execute C1 of `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`
and G1 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`: extract
and measure the Mathlib **declaration** graph (below G0's module graph),
reusing ADR-0800's type/proof-separation mechanism.

## Plan

1. Population registry (`artifacts/declaration-graph/populations/
   mathlib-group-defs-v1.json`) committed first -- 7 real roots from
   `Mathlib.Algebra.Group.Defs` + core `Nat.add_comm`. This is the authority;
   coverage is checked against it, never against the graph's own counts.
2. `scripts/lib/declaration_graph.py` -- a lean4export format-3.1 ndjson
   parser (names/levels/exprs tables, const-collection walk, canonical text
   renderer) that imports `compute_closure` / `compute_type_digest` /
   `compute_identity_digest` / `project_type_only` directly from
   `scripts/check-library-artifact-contract.py` (ADR-0800's reader A) via
   `importlib` -- reusing that mechanism rather than re-deriving it.
3. `scripts/gen-declaration-graph.py` -- shells out to the pinned toolchain
   (`/data0/axeyum/lean-import-toolchain`) per root, merges by declaration
   name, computes transitive closures, edges, and cycle classification, and
   writes the pack-shaped `graph/<population_id>.rows.json`, plus
   `.typeproj.json` / `.edges.json` / `.cycles.json`.
4. `scripts/check-declaration-graph.py` -- the aggregate-gate validator. Runs
   ADR-0800's five guards against the rows file (which is shaped as a valid
   pack) plus three new guards: ENDPOINT_RESOLUTION (row-deletion), EDGES_
   CONSISTENT (edge-deletion), CYCLE_CLASSIFICATION (every multi-node SCC
   must be a subset of a recorded `mutual_group`).
5. Mutation tests, guard -> test kill table.

## Status

Extraction verified live against the pinned toolchain (mathlib4 commit
`c5ea0035`, lean4export commit `a3e35a58`): `Semigroup` and `mul_left_cancel`
roots exported and parsed in under 3s each. Full pipeline build in progress.
This file will be updated with final counts, the kill table, and the honest
scope statement before the lane closes out.
