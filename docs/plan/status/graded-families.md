# Lane: graded-families — ADR-0603's four remaining graded statement families

<!-- plan-section: lane-status -->

**Done (`DONE`, graded-families, 2026-08-27).** Stated the four rows —
constructive general form, boundary refutation, exact decidable-fragment
form, labeled import — for MVT, LUB/completeness, Taylor remainder, and FTA
(the four theorems the 2026-08-27 architecture review §4 named as owed this
treatment, IVT/EVT already having it). Deliverable:
[`docs/curriculum/graded-statement-families.md`](../../curriculum/graded-statement-families.md),
linked from `spivak.md` (rows 8, 11, 20, 25–27) and from ADR-0603.

Measured with `prelude_theorem_inventory --release --include-constructed`
(theorem rows) and `kernel_declaration_projection --require-declaration`
(definitions; exits non-zero on absence), both rebuilt fresh this session
(`scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
prelude_theorem_inventory --example kernel_declaration_projection`), plus
`cargo test -p axeyum-cas --lib extremum::` (20 passed) and
`python3 scripts/validate-facts.py` (806 facts). Every negative was paired
with a positive control of the same declaration kind before being trusted.

**Headline findings** (see the doc for full citations):

Detail moved to [`../notes/graded-families.md`](../notes/graded-families.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `DONE` | ADR-0603's four remaining graded statement families (MVT, LUB, Taylor remainder, FTA) stated as measured rows in `docs/curriculum/graded-statement-families.md`; two stale `spivak.md` claims corrected (`Complex.abs`/`CReal.sqrt` no longer absent; `Complex.polyMul` no longer blocked); ADR-0603 given a pointer postscript. |
