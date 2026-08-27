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

**Pins dropped, deliberately.** Each shard returns a `Vec`, not a
`[T; N]` — no per-shard length pin. The pin's only job was catching a
forgotten registration, which
`creal_tests::every_creal_declaration_is_checked_and_axiom_free`'s
environment-derived coverage assertion already does better (both
directions), plus a NEW duplicate-across-shards check the single array could
never need (impossible to name one `NameId` twice in one array without the
existing per-entry loop just checking it twice; now possible across 33
files). Updated `scripts/recount-pinned-inventory.py` and its controls
(`scripts/tests/test-recount-pinned-inventory.sh`) since `creal_tests.rs` was
the only real file in the tree matching that pin shape; `nat_prelude_tests.rs`
and `complex_tests.rs` use unrelated shapes (`theorem_names()`/`named`) and
needed no change.

**Verified, not just argued:**
- `cargo test -p axeyum-lean-kernel --lib creal::creal_tests::` — 106 passed,
  0 failed, 48.5 s wall (baseline noise-dominated, same order as the ~31 s
  pre-shard baseline).
- Union count printed by the test itself (temporary instrumentation, reverted
  before commit): **432 before, 432 after** — exact parity with the original
  pin, confirmed by the test runtime, not by re-counting my own extraction.
- Mutation-verified both new/changed guards in isolation, reverted after each:
  removing one entry from `inventory/archimedean.rs` kills exactly the
  coverage assertion, naming `CReal.archimedean`; duplicating
  `CReal.archimedean` into `inventory/archimedean_squeeze.rs` kills exactly
  the new duplicate-across-shards assertion, naming the shared `NameId`.
- `scripts/check-deep-stack-call-sites.py`: OK, 223 files, 0 unprotected
  sites (no `#[test]`/`on_a_deep_stack` moved).
- `cargo clippy -p axeyum-lean-kernel --tests -- -D warnings`: 25 pre-existing
  errors, ALL in files this lane did not touch
  (`creal/convergence.rs`, `creal/integral.rs`,
  `creal/uniform_convergence.rs`, `creal_model/creal_model_tests.rs`) —
  confirmed by grepping the output for `inventory`/`creal_tests.rs`/`creal.rs`
  paths (zero hits). Not this lane's to fix; other lanes are live in those
  files.
- `rustfmt --edition 2024 --check` on every touched/new `.rs` file: clean.

**Two-lane disjointness, demonstrated.** A lane adding a declaration to
`creal/trig.rs` today touches `creal/trig.rs` +
`creal/inventory/trig.rs` only. A lane adding a declaration to
`creal/geometric.rs` today touches `creal/geometric.rs` +
`creal/inventory/geometric.rs` only. Zero files in common — where before,
both touched the same `creal_tests.rs` array. `CLAUDE.md`'s pin-recounting
and zero-conflict-trap sections were updated to describe the sharded shape
while keeping the incident history (kept, not deleted, since the failure
mode is general to any similarly-shaped pin elsewhere).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Sharded `creal_tests.rs`'s single 432-entry pinned inventory array into 33 per-module `Vec`s under new `crates/axeyum-lean-kernel/src/creal/inventory/`, registered from a new `creal/inventory.rs`; `creal_tests.rs` now derives coverage from the union plus a new duplicate-across-shards check, both mutation-verified; no per-shard pin (superseded by the environment-derived assertion). Purely additive one-line change to `creal.rs` (`mod inventory;`); no existing `creal/*.rs` module content touched. Updated `scripts/recount-pinned-inventory.py`/its test controls and `CLAUDE.md`'s pin-guidance sections for the new shape. |
