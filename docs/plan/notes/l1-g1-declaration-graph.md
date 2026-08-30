# Notes: l1-g1-declaration-graph

Detail moved out of [`../status/l1-g1-declaration-graph.md`](../status/l1-g1-declaration-graph.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Population, committed first**:
  `artifacts/declaration-graph/populations/mathlib-group-defs-v1.json` --
  seven real roots (`Semigroup`, `CommMagma`, `Monoid`, `mul_left_cancel`,
  `mul_comm`, `mul_assoc` from `Mathlib.Algebra.Group.Defs`, plus core
  `Nat.add_comm`), named BEFORE any extraction ran.
- **Extraction**: bounded, stated as such -- **446 declarations, 2,451
  edges**, from 7 real roots via the pinned lean4export toolchain
  (mathlib4 `c5ea0035`, lean4export `a3e35a58`), NOT all of Mathlib
  (a full `lean4export Mathlib` dump is ~680,925 records per
  `docs/formalized-math-2026-08/diary-import-scale.md`). Two independent
  regenerations are byte-identical (verified with `diff`).
- **Type vs proof, enforced structurally**: `scripts/lib/declaration_graph.py`
  imports `compute_closure`/`compute_type_digest`/`compute_value_digest`/
  `compute_identity_digest`/`compute_pack_digest`/`project_type_only`
  directly from `scripts/check-library-artifact-contract.py` (ADR-0800) via
  `importlib` -- the SAME mechanism, run on real data, not reimplemented.
  `*.typeproj.json` is the producer-facing file; `*.rows.json` (archival,
  carries `value`/`direct_value_deps`/`transitive_value_deps`) is not.
- **Cycles**: 49 real cycles found, ALL classified `mutual_inductive`
  (Nat<->{zero,succ}, Mul<->Mul.mk, etc.), **0 unexpected**, both in the
  type-only graph and the full (type+value) graph. Real Mathlib data
  produced no naturally-occurring mutual-RECURSION example and no
  naturally-occurring unexpected cycle; both classification branches are
  separately proven correct against synthetic fixtures in
  `scripts/tests/test-declaration-graph.py` (`CycleClassificationTests`),
  independent of what a bounded real population happens to contain.
- **Deletion mutations, different guards**: row deletion is caught by
  `check_endpoint_resolution` (a dangling dependency name); edge deletion is
  caught by `check_edges_consistent` (materialized edges.json disagreeing
  with rows.json's own dependency fields). Confirmed structurally distinct:
  deleting a leaf row does NOT change `edges.json` vs `rows.json` agreement
  and does NOT change any OTHER row's recorded transitive closure (the
  deleted leaf had no further dependencies), so only ENDPOINT_RESOLUTION
  fires; deleting one edges.json entry does not touch any row's own
  `direct_*_deps`, so only EDGES_CONSISTENT fires.
- **Eight guards total**, all mutation-verified 1:1 in
  `scripts/tests/test-declaration-graph-mutations.sh`: five reused verbatim
  from ADR-0800 (MISSING, DUPLICATE, REORDERED, TRUNCATED, VALUE_EXPOSED)
  plus three new (ENDPOINT_RESOLUTION, EDGES_CONSISTENT,
  CYCLE_CLASSIFICATION). Kill table:

  ```
  MISSING              -> missing
  DUPLICATE            -> duplicate
  REORDERED            -> reordered
  TRUNCATED            -> truncated
  VALUE_EXPOSED        -> value_exposed
  ENDPOINT_RESOLUTION  -> row_deleted
  EDGES_CONSISTENT     -> edge_deleted
  CYCLE_CLASSIFICATION -> unexpected_cycle
  ```

- Gate registered in both `justfile` (`declaration-graph` recipe, appended
  to the `check:` dependency line) and `scripts/check.sh` (three `step`
  lines: `declaration-graph`, `declaration-graph-tests`,
  `declaration-graph-mutations`). `just declaration-graph` and
  `AXEYUM_CHECK_LIST=1 bash scripts/check.sh` both verified to include the
  new steps without restructuring either file's existing dependency list.

## What this does not capture

Per-declaration module attribution is only the requesting root's own
module, not a true declaration-to-file map (that is G0's job). Recursor
`rules[*].rhs` bodies are not walked into edges -- Recursor is a trusted
kind by construction, carrying zero value/proof edges regardless of what
lean4export's export happens to include. A measured, documented fix during
extraction: lean4export's macro hygiene assigns per-elaboration-session
numeric suffixes to internal binder names, so two independent exports of
the identical declaration disagreed byte-for-byte on binder display names
alone; the renderer now drops binder names entirely (alpha-invariant,
de Bruijn indices only), which is what makes byte-identical reproduction
across independent runs hold.

## Files

- `artifacts/declaration-graph/populations/mathlib-group-defs-v1.json`
- `artifacts/declaration-graph/graph/mathlib-group-defs-v1.{rows,typeproj,edges,cycles}.json`
- `scripts/lib/declaration_graph.py` (parser + graph utilities)
- `scripts/gen-declaration-graph.py` (extractor, needs the pinned toolchain)
- `scripts/check-declaration-graph.py` (gate, needs no toolchain)
- `scripts/tests/declaration_graph_mutations.py` (fixture builder)
- `scripts/tests/test-declaration-graph.py` (in-process assertions, 7 tests)
- `scripts/tests/test-declaration-graph-mutations.sh` (guard-deletion kill table)
- `docs/research/09-decisions/adr-0820-the-declaration-graph-reuses-the-artifact-contracts-type-proof-separation.md`

## Next (not this lane's scope)

G2 (join Axeyum state: resolve Mathlib declarations to fact IDs, kernel
declarations, statement vocabulary) and G3 (publish the infrastructure
frontier queues) both consume this graph as a checked precondition. A wider
population (more roots, or a size-bounded BFS over Mathlib's own hub list
from ADR-0805) is a straightforward re-run of `gen-declaration-graph.py`
against a new population file -- nothing in the pipeline is specific to the
seven roots chosen here.
