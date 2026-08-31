# Lane status: l3-d2-structural-index

Owner: `l3-d2-structural-index`
Phase: L3 D2 — structural theorem and proof index
(`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`)
ADR: ADR-0905

## Status: in progress (initial commit; scaffolding + extractor landed)

## What exists

- `crates/axeyum-lean-kernel/examples/structural_index_extract.rs` — new
  extractor. Builds the same prelude groups `shape_search.rs` does, and for
  every declaration in `kernel.environment()` emits namespace, binder
  role classification, `concl_head`, `type_constants`,
  `definitions_used`/`theorem_dependencies`/`recursors_used` (from
  `Kernel::declaration_type_dependencies`/`declaration_dependencies`/
  `theorem_dependencies`), a best-effort `rewrite_direction` for `Eq`/`Iff`
  conclusions, a `proof_skeleton_digest`, and an
  `external_dependency_fingerprint` (dependency names outside the
  declaration's own namespace — the field aimed at the
  `Int.prodRange_permute`/`Nat.countRange_permute` case). No literal proof
  values are ever emitted, only declaration names and digests over them.
- ADR-0905 records the field provenance and scope cuts.

## Still to land (this session)

- `artifacts/structural-index/theorems.json` — committed extractor output.
- `artifacts/structural-index/mathlib-goal-features.json` +
  `held-out-exclusion-manifest.json` — held-out-excluded join.
- `artifacts/structural-index/queries.json` — fixed queries + committed
  expected rankings.
- `scripts/gen-structural-index.py`, `scripts/check-structural-index.py`.
- `scripts/tests/test-structural-index-mutations.sh` +
  `scripts/tests/library` mutation fixtures, guard-to-test kill table.
- `justfile`/`scripts/check.sh` gate registration (append-only).

## Known scope cuts (see ADR-0905 §2)

- "Proof skeleton" is a dependency-role fingerprint (sorted, role-tagged
  union of type/def/thm/rec names), not a term-tree structural hash. A true
  term-tree hash is a follow-on, not built this session.
- "Rewrite direction" is a heuristic (elaborated node-count comparison of
  the conclusion's last two applied arguments), not a rewrite-system
  analysis.
- Binder role classification (carrier/connective/hypothesis) is a fixed
  lookup table over head constants, not a sort-level judgement.

## Hiding place this index still cannot reach

Hiding place 2 from the roadmap brief — a reusable step built INLINE inside
a larger declaration and never given a name — has no declaration to index.
No index over `kernel.environment()` can ever see it; this is stated in
ADR-0905 and in the extractor's own module doc, not silently assumed away.
