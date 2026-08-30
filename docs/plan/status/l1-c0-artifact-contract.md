# Lane: l1-c0-artifact-contract — ADR-0717 L1 phase C0, freeze the library-artifact contract

<!-- plan-section: lane-status -->

**Done, l1-c0-artifact-contract, 2026-08-30.** [ADR-0800](../../research/09-decisions/adr-0800-the-library-artifact-record-splits-type-and-proof-into-different-files.md)
records the design decisions. Summary:

`artifacts/library-artifact/` freezes the pack record shape from
`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C0:
Lean/Mathlib version+commit identity, per-declaration content digests, four
SEPARATE dependency fields (`direct_type_deps`, `direct_value_deps`,
`transitive_type_deps`, `transitive_value_deps`), derived
`trusted_declaration_identities`, normalization/renderer versions, and a
`source_population` block. A 9-declaration positive pack
(`packs/nat-add-comm-v1.pack.json`: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`,
`Eq`, `Eq.refl`, `id`, `Nat.add`, `Nat.add_comm`) is hand-authored — real
Lean-core declarations, this contract's own canonical rendering of their
types/values, digests mechanically derived and independently re-derived by
both readers. C1 (`artifact-extract`) owns wiring a real pinned Lean-side
extractor at scale; this phase is the contract those extracted packs must
satisfy, not the extractor.

Measured, not asserted:

Detail moved to [`../notes/l1-c0-artifact-contract.md`](../notes/l1-c0-artifact-contract.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | l1-c0-artifact-contract | Library-artifact pack contract (`artifacts/library-artifact/`: README spec, JSON Schema doc, 9-declaration positive pack + type-only projection + external population registry) + two independent readers (`scripts/check-library-artifact-contract{,-reader-b}.py`) + 14-test suite + 5-guard 1:1 mutation table (`scripts/tests/test-library-artifact-contract*`), registered in justfile and check.sh; ADR-0800. |
