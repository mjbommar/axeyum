# axeyum-property — STATUS

Live tracker for the bounded-property SDK (App B). See [PLAN.md](PLAN.md).

## Current focus

- **2026-06-25 — scaffolded.** Crate `crates/axeyum-property` created on the
  `consumer-track` worktree (off committed HEAD): `Cargo.toml` (deps `axeyum-ir` +
  `axeyum-solver` path), `src/lib.rs` linking smoke test (`solver_linked()`),
  added to `[workspace].members`. **`cargo check -p axeyum-property` is green**
  (compiles against the stable committed `axeyum-solver`, 6.3 s) — the isolated
  worktree build pipeline is proven.

## Next actions (v0)
1. Add the typed-handle module: `Bv<const W: u32>`, `Int`, `Bool` over `Copy`
   `TermId`; std operator traits + comparison methods → `TermArena` builders.
2. `PropertyBuilder` + `Forall<T>` + `assuming`/`check` → `evidence::prove`.
3. `Outcome<T>` + `Certificate` (re-checked `EvidenceReport` + best-effort
   `to_lean_module`); scalar BV/Int counterexample lifting via `Model::get`.
4. Worked examples + doc tests; gate fmt + clippy `-D warnings`.

## Gates / discipline
- `#![forbid(unsafe_code)]`; fmt + clippy `-D warnings` per increment.
- No core edits; consume `axeyum-solver` as a black box.
- DISAGREE = 0 once the SDK corpus/scoreboard exists.

## Changelog
- **2026-06-25** — crate scaffolded; links solver; `cargo check` green. PLAN/STATUS
  written. Next: the typed-handle layer (v0).
