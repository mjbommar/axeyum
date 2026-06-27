# axeyum-property STATUS.md

## Current focus

- **2026-06-27 — v0 typed proof slice landed.**
  `crates/axeyum-property` is now a workspace crate. It provides typed
  `Bool`, `Bv<W>`, and `Int` handles over `TermArena`, assumptions, default and
  custom `SolverConfig`, proof calls through `prove`, minimized
  counterexamples through `prove_minimized`, scalar model lifting, and typed
  unsigned BV overflow helper predicates. Focused tests cover a proved BV
  identity, an integer implication under assumptions, minimized BV8
  counterexample lifting, and a BV256 overflow-helper surface check.

## Verification

- `cargo fmt --all --check`
- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-property -j1 -- --nocapture`
- `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-property --all-targets -j1 -- -D warnings`
- `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-property --no-deps -j1`

## Next actions

1. Add ergonomic expression construction without compromising fallible builder
   errors.
2. Add `Symbolic` and derive support for structs.
3. Add counterexample-to-`#[test]` output.
4. Add a graduated SDK property corpus and scoreboard gate.
