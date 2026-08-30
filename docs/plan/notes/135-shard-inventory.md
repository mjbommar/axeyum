# Notes: 135-shard-inventory

Detail moved out of [`../status/135-shard-inventory.md`](../status/135-shard-inventory.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
