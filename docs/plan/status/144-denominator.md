# Lane: denominator — closing the `Nat.Peano`/`Int.Characterization` gap between the two theorem inventories

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, denominator, 2026-08-27).**
[143-fact-gen-nat](143-fact-gen-nat.md) found and reported, without fixing, a
9-theorem gap between `kernel_declaration_projection` (338 `Nat.*` theorems)
and `prelude_theorem_inventory --include-constructed` (329) — the ledger
coverage denominator. This lane found the root cause, fixed the tool that was
actually wrong, and added a standing check so it cannot silently recur.

**Root cause, read from `kernel.environment()`, not from either tool's
output or from the name.** `Nat.Peano.*` (10 declarations: 1 `Definition`
— `iter` — and 9 `Theorem`s) and `Int.Characterization.*` (24 declarations:
1 `Definition` — also named `iter` — and 23 `Theorem`s) are declared by
`build_characterization()`
(`crates/axeyum-lean-kernel/src/characterization.rs`), which
`kernel_declaration_projection.rs` has always built (as the `characterization`
group) and `prelude_theorem_inventory.rs`'s `build_groups` **never called at
all** — not one of that tool's documented, deliberate kind exclusions
(`Axiom`/`Definition`/`Opaque`/`Inductive`/`Constructor`/`Recursor`/
`Quotient`), just a whole prelude group nobody wired in. Confirmed directly:
every `Nat.Peano.*`/`Int.Characterization.*` name in the kernel is
`Declaration::Theorem` (9 + 23 = 32 rows, one `Definition` each for `iter`,
correctly excluded by both tools) with an empty `axiom_footprint` — genuine,
axiom-free, already-proved theorems, exactly the population this ledger's
denominator claims to count.

**Verdict: `prelude_theorem_inventory` was the tool at fault, not the
generator.** `kernel_declaration_projection` was already correct.

Detail moved to [`../notes/144-denominator.md`](../notes/144-denominator.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | denominator | Added the missing `characterization` group (`Nat.Peano.*`, `Int.Characterization.*`, 32 axiom-free theorems) to `prelude_theorem_inventory`'s `build_groups`, confirming `kernel_declaration_projection` was already correct; updated `gen-theorem-production-ledger.py`'s `EXPECTED_PRELUDES` and regenerated its ledger doc; regenerated `artifacts/ledger-coverage.json` (kernel_theorems 1,416→1,448, registered 1,026→1,035, curated unmoved at 474); added `scripts/check-theorem-inventory-completeness.py` + 9 unit tests, mutation-verified, so the two tools' theorem-name-set agreement is a standing, checkable guard rather than a fact-generation lane's accidental find |
