# Lane: fact-gen-nat — running the mechanical generator on nat and creal

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, fact-gen-nat, 2026-08-27).** [298](../../autogenesis/298-mechanical-fact-registration.md)
piloted `scripts/gen-kernel-facts.py` on `string` (0/64 → 64/64) and
deliberately stopped, pending the two-counter ratchet ADR-0607 calls for.
[142](142-ledger-ratchet.md) landed `curated` in `gen-ledger-coverage.py`,
which unblocks bulk generation without letting it masquerade as review. This
lane runs the (unmodified) generator on `nat` and `creal` and registers what
it emits — no changes to the generator, the coverage script, or the
validator.

**Headline (`gen-ledger-coverage.py`'s own per-prelude counts): nat
86/329 → 327/329 (2 permanently unregistered under this join — see below),
creal 132/379 → 379/379, full coverage. 497 facts generated (250 nat + 247
creal), 0 declined for creal, 2 declined for nat. Overall ledger coverage
538/1,409 (38.5%) → 1,026/1,409 (72.8%).** `curated` is unmoved at **474**,
exactly as designed — every one of the 497 new facts carries
`provenance.curation = "generated-unreviewed"`. `validate-facts.py`:
882 → 1,379 facts, 0 errors, at every checkpoint.

**The two nat declines are the interesting part.** `Nat.le_refl` and
`Nat.le_succ` are NOT already "registered" by this ledger's `kernel-lean`
join — they are curated facts on `proof_route = "imported-kernel-lean"` (the
Lean-import route, ADR-0601), a different producer proving the same theorem
name. The generator's slug collision guard caught this correctly and declined
rather than overwrite: `F:nat-le-refl` / `F:nat-le-succ` already exist as
files, so `slug_for` collides and the theorem is skipped. This is the
generator working as designed, not a defect — but it is worth naming, because
it means "already registered" and "already has a file at this slug" are two
different predicates, and only the second one gates emission.

Detail moved to [`../notes/143-fact-gen-nat.md`](../notes/143-fact-gen-nat.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | fact-gen-nat | Ran `scripts/gen-kernel-facts.py` (unmodified) over `nat` (250 planned, 2 declined) and `creal` (247 planned, 0 declined); registered 497 generated facts; coverage 538/1,409 (38.5%) → 1,026/1,409 (72.8%), `curated` unmoved at 474; found and traced a 9-theorem `Nat.Peano.*` gap between `kernel_declaration_projection` and `prelude_theorem_inventory` |
