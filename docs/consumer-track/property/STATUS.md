# axeyum-property STATUS.md

## Current focus

- **2026-06-27 — Scalar and tuple `Symbolic` trait landed.**
  `Symbolic` is now the macro-free typed input path for the SDK:
  `Property::symbolic::<T>("name")` declares values, and
  `Property::concrete::<T>(&expr, &model)` lifts them from replay-checked
  models. Built-in implementations cover `bool`, unsigned Rust integer widths
  (`u8` through `u128` as BV8 through BV128), `i128` as Int, unit, and 2-/3-tuples
  with field names like `input.0`, `input.1`, etc. Struct derive and signed
  fixed-width two's-complement policy are still pending.

- **2026-06-27 — Native scalar counterexample-to-test rendering landed.**
  `Property::counterexample` and `counterexample_from_outcome` now extract a
  deterministic `Counterexample` over SDK-declared symbols from a model or
  disproved proof outcome. `InputBinding` records the Axeyum symbol, original
  name, sanitized Rust identifier, declared sort, and value. The renderer emits
  Rust `let` bindings and complete `#[test]` skeletons for Bool, Int, and
  BV<=128 values, while explicitly rejecting arrays, Reals, datatypes,
  uninterpreted carriers, and wide BV values until a frontend supplies a domain
  representation.

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
2. Add `Symbolic` derive support for structs and decide signed fixed-width Rust
   integer policy.
3. Extend counterexample-to-`#[test]` output for structured inputs and
   frontend-specific replay bodies.
4. Add a graduated SDK property corpus and scoreboard gate.
