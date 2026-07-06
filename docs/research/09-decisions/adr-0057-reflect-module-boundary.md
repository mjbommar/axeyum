# ADR-0057: The IR reflectors are an `axeyum-verify::reflect` module, not a new crate (yet)

Status: accepted
Date: 2026-07-06

## Context

[ADR-0056](adr-0056-verified-systems-track.md) adopted the verified-systems
trajectory as Track 5, whose P5.1 task T5.1.1 says: promote the prototype
reflectors — living as test scaffolding in
`crates/axeyum-verify/tests/reflect_common/{mod,mir,llvm}.rs` — "behind a public
API", explicitly deferring the crate-vs-module choice to this ADR.

The scaffold is a `mod reflect_common;` that **eight integration-test binaries
each recompile a private copy of** (`checked_bounds`, `checked_division`,
`checked_reflection`, `checksum_module`, `cross_ir_equivalence`,
`cross_ir_refutation`, `llvm_reflection`, `mir_reflection`). That is
source-level DRY, but not a consumable API: the reflectors cannot be called by
`axeyum-verify`'s own library code (the eventual `#[verify]` contract and
kernel-obligation surface, P5.2/P5.3), and each test binary pays the compile
cost again.

The governing rule is CLAUDE.md / [ADR-0001](adr-0001-vertical-slice-first.md):
*"Crate split is deliberately minimal; add crates only after a boundary is
proven by use."* The reflectors have exactly one consumer today —
`axeyum-verify` and its tests. A separate `axeyum-reflect` crate would also mean
editing the workspace `Cargo.toml` (a file other lanes touch), for no present
second consumer.

## Decision

**The reflectors become a public module `axeyum_verify::reflect` (submodules
`reflect::mir`, `reflect::llvm`), not a new crate.** The prototype files move
`tests/reflect_common/{mod,mir,llvm}.rs` → `src/reflect/{mod,mir,llvm}.rs`
verbatim (the submodules already reference the shared vocabulary via `super::`,
which is unchanged), `src/lib.rs` gains `pub mod reflect;`, and the eight test
binaries switch from `mod reflect_common;` + `use reflect_common::…` to
`use axeyum_verify::reflect::…`.

Public surface (the reflector API):

- `reflect::{width_of, is_int_ty, binop, compare}` — the shared op vocabulary.
- `reflect::{prove_goal, is_proved, is_disproved, eval_bv}` — the proof/eval
  harness (convenience over `axeyum_solver::prove` / `axeyum_ir::eval`).
- `reflect::mir::{MirParam, reflect_mir_params_checked, reflect_mir_into_checked,
  reflect_mir_into, reflect_mir_unary}` — the MIR symbolic executor,
  `*_checked` returning `(value, panic)`.
- `reflect::llvm::{Reflected, reflect_ll, reflect_into, reflect_unary_into,
  lower_fn, lower_body, lower_rhs, resolve, param_decls, is_reg}` — the LLVM
  symbolic executor + the lower-level pieces the loop/buffer reflectors reuse.

**The `axeyum-reflect` crate split is deferred, not rejected.** It becomes an
ADR the moment a *second* consumer appears — a standalone `cargo axeyum-reflect`
driver, `axeyum-property` needing reflection, or the crate's compile weight
becoming a measured problem. Until then the module is the honest boundary.

## Evidence

- One consumer today (`axeyum-verify` + its tests); ADR-0001 minimality.
- Zero change to shared/other-lane files (no workspace `Cargo.toml` edit),
  which also keeps the migration off the concurrent solver/strings lane.
- The move is mechanical (verbatim files, `super::`-relative internals
  unchanged); the exit criterion — all pre-existing reflection test binaries
  green against the module API — is directly checkable.

## Consequences

- `crates/axeyum-verify/src/reflect/` exists; `pub mod reflect;` in `lib.rs`;
  `tests/reflect_common/` removed.
- The reflectors now compile into the `axeyum-verify` *library*, so P5.2
  (contracts) and P5.3 (kernel obligations) can call them directly.
- T5.1.1's remaining halves (full `.ll` token parser, build-time MIR
  extraction) proceed against this module boundary.
- Supersedes the "source-level DRY, not a public API" framing in
  [`reflect-common-abstraction.md`](../../consumer-track/verify/reflect-common-abstraction.md)
  (that note's "Honest scope" paragraph).
