# axeyum-property STATUS.md

## Current focus

- **2026-06-27 — Prelude-aware replay tests landed.**
  `Counterexample::render_rust_test_with_prelude` now emits caller-owned
  imports/module prelude, replay-checked scalar bindings, caller-owned setup
  snippets, then the replay/assertion body.
  Frontends can render nested/domain aggregate initializers with
  `render_rust_named_struct_let` /
  `render_rust_named_struct_let_with_fields` and insert those snippets before
  assertions without the SDK inventing domain semantics. The generated nested
  aggregate corpus row now checks the complete `#[test]` skeleton, including a
  caller-owned `use` prelude before setup snippets and
  `assert!(replay_transfer(transfer))`; totals remain 8 cases, 2 proved, 6
  disproved, 0 unknown, DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27 — Explicit nested aggregate replay landed.**
  `Counterexample::render_rust_named_struct_let_with_fields` now lets
  frontends compose caller-owned nested/domain Rust replay shapes without the
  SDK inferring those shapes. Direct scalar children still come from
  replay-checked model bindings, nested descendants are ignored until the
  caller supplies an explicit field expression such as `limits:
  transfer_limits`, duplicate field initialization is rejected, and the older
  direct aggregate helper still rejects implicit nested inference. The generated
  PROP.6 corpus now includes a nested `transfer.limits` replay workflow; totals
  are 8 cases, 2 proved, 6 disproved, 0 unknown, DISAGREE=0, and 1/1
  Lean-required coverage.

- **2026-06-27 — Corpus broadened to overflow and derive workflows.**
  This slice broadened the PROP.6 corpus from five to seven generated SDK
  workflows. The new rows exercise the typed `uadd_overflows` helper with a
  minimized `(x=1,y=255)` witness and `#[derive(Symbolic)]` concrete struct
  lifting for a `TransferInput` counterexample.
  `tests/support/corpus_cases.rs` remains the shared source for the integration
  test, committed JSON, and generated Markdown snapshot. The explicit nested
  replay slice above has since moved current totals to 8 cases, 2 proved, 6
  disproved, 0 unknown, 0 mismatches / DISAGREE, and 1/1 Lean-required case
  available. External proptest/Kani-style baselines and broader corpus coverage
  remain open.

- **2026-06-27 — Generated corpus artifacts landed.**
  The PROP.6 corpus is now shared by the integration test and the generator
  example instead of duplicated in docs. `tests/support/corpus_cases.rs`
  executes the SDK workflows, `tests/corpus.rs` checks the live results against
  committed JSON and Markdown snapshots, and
  `examples/property_corpus_scoreboard.rs` regenerates both
  `docs/consumer-track/property/corpus.json` and `SCOREBOARD.md`. This closes
  the generated-artifact gap for the first SDK gate; external proptest/Kani-style
  baselines and broader corpus coverage remain open.

- **2026-06-27 — Graduated SDK corpus scoreboard first slice landed.**
  `crates/axeyum-property/tests/corpus.rs` is now the committed PROP.6 app-level
  corpus gate, with a matching `SCOREBOARD.md`. The initial slice covered five
  graduated SDK workflows: BV proof with checked evidence and a required Lean
  module,
  integer implication under assumptions, unsigned minimized counterexamples,
  signed two's-complement minimized counterexamples, and struct-shaped
  counterexample rendering. The generated gate above has since broadened this
  to 8 cases, 2 proved, 6 disproved, 0 unknown, 0 mismatches / DISAGREE, and
  1/1 Lean-required case available. External proptest/Kani-style baselines are
  still the next measurement step, so this is a first gate rather than a full
  SOTA comparison.

- **2026-06-27 — Certificate summary surface landed.**
  `ProofCertificate::summary()` now gives frontends a compact owned view over a
  proof attempt: proved/disproved/unknown status, stable evidence-kind label,
  backend/provenance assertion count, per-run trust-step labels and certification
  bits, and Lean reconstruction availability or diagnostics. The solver evidence
  enum now exposes `Evidence::kind_label()` so SDK/UI text does not depend on
  Rust debug formatting. Focused property tests cover proved summaries with Lean
  modules and disproved summaries that intentionally have no evidence/Lean
  artifact.

- **2026-06-27 — Lean certificate surface first slice landed.**
  `axeyum-property` now re-exports `EvidenceReport`, `ProofFragment`, and
  `ReconstructError`, and exposes a `ProofCertificate` envelope for proof calls.
  `Property::prove_with_certificate` and
  `prove_minimized_with_certificate` return the ordinary checked
  `ProofOutcome`, expose the proved `EvidenceReport`, and attach a
  best-effort standalone Lean module when `prove_unsat_to_lean_module` covers
  the `hypotheses ∧ ¬goal` refutation fragment. Disproved and unknown outcomes
  deliberately return no Lean module, so the SDK does not fabricate proof
  artifacts for non-refutations.

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
- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-property --test corpus -j1 -- --nocapture`
- `CARGO_BUILD_JOBS=2 cargo run -p axeyum-property --example property_corpus_scoreboard -- json >/tmp/axeyum-property-corpus.json`
- `diff -u docs/consumer-track/property/corpus.json /tmp/axeyum-property-corpus.json`
- `CARGO_BUILD_JOBS=2 cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown >/tmp/axeyum-property-scoreboard.md`
- `diff -u docs/consumer-track/property/SCOREBOARD.md /tmp/axeyum-property-scoreboard.md`
- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-property -j1 -- --nocapture`
- `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-property --all-targets -j1 -- -D warnings`
- `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-property --no-deps -j1`
- `./scripts/check-links.sh`

## Next actions

1. Broaden expression construction ergonomics, especially operator-trait or
   builder syntax that still makes fallible term construction visible.
2. Extend counterexample-to-`#[test]` output toward frontend-specific replay
   assertions and helper adapters while keeping domain semantics caller-owned.
3. Keep broadening the SDK property corpus and add the external
   proptest/Kani-style baseline comparison.
