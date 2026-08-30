# Lane: shard-inventory — shard `creal_tests.rs`'s single pinned inventory

<!-- plan-section: lane-status -->

**Sharded the 432-entry `creal_tests.rs` inventory into per-module `Vec`s
(`done`, shard-inventory, 2026-08-27).** `05-throughput.md`'s C1 ("shard the
library so lanes compose instead of collide") for the single pinned array
that made every pair of concurrent `creal` lanes collide on one file
(conflicted or merge-damaged eight-plus times in one day per `CLAUDE.md`).

Design: one shard file per `creal/` source module under
`crates/axeyum-lean-kernel/src/creal/inventory/<module>.rs` (33 files: 32
mirroring `creal/*.rs` submodules, plus `base.rs` for the algebra declared
directly in `creal.rs`), each exposing `pub(crate) fn entries(p:
CRealPrelude) -> Vec<(&'static str, NameId, &'static str)>`. Registered from
a new `crates/axeyum-lean-kernel/src/creal/inventory.rs` (one `mod` line +
one `all.extend(...)` line per shard, alphabetical so two new-module
additions land on different lines). `creal.rs` itself gained exactly one
additive line, `#[cfg(test)] mod inventory;`, beside the existing `mod
creal_tests;` — no existing `creal/*.rs` module file was touched, so the
several lanes live in `uniform_convergence.rs`/`ratio_test.rs`/etc. are
unaffected.

Mapping every one of the original 432 entries to its owning module was done
by grepping each field's actual `Declaration::{Theorem,Definition,...}`
construction site (`name: p.<field>,` or the small number of helper-call
exceptions, e.g. `lattice.rs`'s `declare_operation`/`projection`), not by
hand-guessing — verified zero ambiguous/unresolved mappings before writing
any shard file.

Detail moved to [`../notes/135-shard-inventory.md`](../notes/135-shard-inventory.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Sharded `creal_tests.rs`'s single 432-entry pinned inventory array into 33 per-module `Vec`s under new `crates/axeyum-lean-kernel/src/creal/inventory/`, registered from a new `creal/inventory.rs`; `creal_tests.rs` now derives coverage from the union plus a new duplicate-across-shards check, both mutation-verified; no per-shard pin (superseded by the environment-derived assertion). Purely additive one-line change to `creal.rs` (`mod inventory;`); no existing `creal/*.rs` module content touched. Updated `scripts/recount-pinned-inventory.py`/its test controls and `CLAUDE.md`'s pin-guidance sections for the new shape. |
