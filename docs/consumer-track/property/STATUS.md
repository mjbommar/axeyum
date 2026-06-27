# axeyum-property STATUS.md

## Current focus

- **2026-06-27 — Expression ergonomics first slice landed.**
  The typed handles now expose `.equals()` aliases for Bool, BV, and Int
  equality, avoiding the Rust `Eq::eq` naming friction while preserving the
  existing fallible `&mut Property` builder contract. `Property::all` and
  `Property::any` now fold Boolean conditions with SMT identity values for
  empty input (`true` and `false` respectively), giving frontends a compact way
  to build conjunctions and disjunctions without introducing an implicit arena
  or hiding construction errors. Broader operator traits / richer builder syntax
  remain open.

- **2026-06-27 — Structured Rust counterexample snippets landed.**
  `Counterexample` now renders aggregate Rust bindings for direct symbolic
  input bundles: `render_rust_named_struct_let` emits `Type { field: value_id }`
  initializers for direct named fields such as `transfer.amount`, and
  `render_rust_tuple_struct_let` emits tuple-struct constructors for contiguous
  numeric fields such as `pair.0`, `pair.1`. The helpers deliberately reuse the
  replay-checked scalar let-bindings and reject nested aggregate inference
  (`transfer.limits.fee`) until a frontend supplies its domain shape.

- **2026-06-27 — Signed-order minimization metadata landed.**
  `Property::prove_minimized` now preserves signed symbolic intent during
  counterexample minimization. The solver exposes metadata-aware objectives
  (`ModelMinimizeObjective::{Symbol,SignedBv}`) plus
  `minimize_model_objectives` / `prove_minimized_with_objectives`; the property
  SDK maps `signed_bv` and `Symbolic` `i8`/`i16`/`i32`/`i64` inputs to
  `SignedBv` objectives. Raw `Property::bv::<W>` inputs still minimize in
  unsigned order. A focused regression confirms the same signed BV8 feasible set
  minimizes to raw `0` in unsigned order and raw `0xfd` (`-3_i8`) in signed
  order.

- **2026-06-27 — Signed fixed-width `Symbolic` policy landed.**
  `i8`/`i16`/`i32`/`i64` now implement `Symbolic` as two's-complement
  `Bv<8>`/`Bv<16>`/`Bv<32>`/`Bv<64>` terms, while `i128` remains mathematical
  Int. Model lifting sign-extends replay-checked BV values back to Rust signed
  integers, and counterexample rendering preserves the signed intent for those
  SDK-declared symbols (`let x: i8 = -1_i8; // BV8 two's-complement`). Raw
  `Property::bv::<W>` inputs still render and minimize as unsigned Rust
  integers.

- **2026-06-27 — `#[derive(Symbolic)]` landed.**
  `axeyum-property` now re-exports `#[derive(axeyum_property::Symbolic)]` from
  the new pure-Rust `axeyum-property-macros` crate. The derive supports named,
  tuple, and unit structs, adds
  `field_type: Symbolic<Concrete = field_type>` bounds for generic fields,
  declares fields through `Property::symbolic_struct` / deterministic numeric
  tuple suffixes, and lifts concrete struct values from replay-checked models.
  The generated code references only `axeyum_property::*`, so downstream users
  do not need to depend on `axeyum-solver` directly for the macro.

- **2026-06-27 — Macro-free named-field symbolic structs landed.**
  `Property::symbolic_struct("name", |fields| ...)` now lets SDK users build
  struct-shaped input bundles with deterministic Axeyum names such as
  `transfer.amount` without invoking a proc-macro derive. `SymbolicStruct::field`
  composes the existing scalar/tuple `Symbolic` implementations, and
  `struct_field` supports nested named bundles. Counterexample rendering
  sanitizes those names into stable Rust identifiers such as `transfer_amount`.

- **2026-06-27 — Scalar and tuple `Symbolic` trait landed.**
  `Symbolic` is now the macro-free typed input path for the SDK:
  `Property::symbolic::<T>("name")` declares values, and
  `Property::concrete::<T>(&expr, &model)` lifts them from replay-checked
  models. Built-in implementations cover `bool`, unsigned Rust integer widths
  (`u8` through `u128` as BV8 through BV128), signed Rust integer widths
  (`i8` through `i64` as two's-complement BV8 through BV64), `i128` as Int, unit,
  and 2-/3-tuples with field names like `input.0`, `input.1`, etc. The follow-up
  derive entry covers struct derivation.

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
- `git diff --check`
- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-property -j1 -- --nocapture`
- `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-property --all-targets -j1 -- -D warnings`
- `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-property --no-deps -j1`

## Next actions

1. Broaden expression construction ergonomics, especially operator-trait or
   builder syntax that still makes fallible term construction visible.
2. Extend counterexample-to-`#[test]` output for frontend-specific replay
   bodies and nested/domain aggregate shapes.
3. Add a graduated SDK property corpus and scoreboard gate.
