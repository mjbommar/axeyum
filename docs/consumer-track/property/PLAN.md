# axeyum-property PLAN.md

Bounded-property SDK plan. This app is the lowest-friction consumer surface:
users build typed bounded properties directly, then receive
`Proved | Disproved(counterexample) | Unknown` from the same checked evidence
machinery as the solver crate.

## Goal
Ship an idiomatic Rust SDK for bounded verification over Bool, bit-vectors, and
integers:

- typed term handles with compile-time BV widths;
- proof calls backed by replay-checked Axeyum evidence;
- minimized, typed counterexamples for disproved goals;
- optional Lean module output when reconstruction supports the fragment;
- reusable counterexample-to-test output for the EVM and Rust verifier apps.

## Current Scope
The committed v0 slice is intentionally thin and additive:

- `Property` owns a `TermArena`, hypotheses, solver config, and deterministic
  counterexample-objective order;
- `Bool`, `Bv<W>`, and `Int` wrap raw `TermId`s without lifetimes;
- `Symbolic` declares and lifts scalar Bool/unsigned-BV/signed-BV/Int-backed
  values plus 2-/3-tuples with deterministic field names;
- `Property::symbolic_struct` gives macro-free named-field bundles for
  struct-shaped inputs, and `#[derive(axeyum_property::Symbolic)]` lowers named
  and tuple structs to that surface;
- proof calls delegate to `axeyum_solver::{prove, prove_minimized}`; minimized
  proofs use signed two's-complement objective metadata for signed symbolic BV
  inputs;
- `ProofCertificate` wraps the ordinary `ProofOutcome`, exposes the checked
  `EvidenceReport` for proved outcomes, and attaches a best-effort standalone
  Lean module when `prove_unsat_to_lean_module` covers the refutation fragment;
  `ProofCertificate::summary()` turns the raw report into stable
  frontend-facing outcome, evidence-route, trust-ledger, and Lean-status fields;
- scalar model lifting reads values from `Model`;
- typed unsigned BV overflow predicates expose the core overflow builders.
- expression ergonomics include `.equals()` aliases for Bool/BV/Int equality,
  context-owned Bool/BV/Int builder aliases such as `Property::bv_add`,
  `Property::int_le`, and `Property::bool_implies`, plus `Property::all` /
  `Property::any` Boolean folds, while keeping construction errors explicit.
- `Counterexample` / `InputBinding` render native scalar model values as Rust
  let-bindings or a `#[test]` skeleton with caller-provided prelude/setup/replay
  code, preserving signed two's-complement Rust integer intent for signed
  symbolic BV inputs; direct named/tuple symbolic bundles can also render
  aggregate Rust initializer statements over those scalar bindings, and nested
  aggregate replay can compose caller-supplied field expressions explicitly and
  place prelude/setup snippets before helper-rendered Boolean or
  Result-returning replay assertions; `render_rust_test_module` wraps
  caller-owned imports/helpers and generated tests in a deterministic
  `#[cfg(test)]` module, and `render_rust_test_file` assembles caller-owned
  top-level prelude blocks plus multiple generated modules/items into
  deterministic multi-case fixture files.
- `tests/support/corpus_cases.rs` is the shared graduated SDK corpus. The
  `tests/corpus.rs` gate checks the executed corpus against both committed
  artifacts, and `examples/property_corpus_scoreboard.rs` regenerates
  `SCOREBOARD.md` plus `corpus.json`: 12 cases, 4 proved, 8 disproved, 0
  unknown, 0 mismatches, and 1/1 Lean-required case available, including a
  mixed Bool/BV/Int expression-builder alias proof plus deterministic
  executable baseline comparisons for one minimized scalar BV counterexample,
  one minimized struct counterexample, and one proved BV assertion.

## Tasks
| id | task | exit |
|---|---|---|
| PROP.1 | Typed scalar proof SDK | DONE — Bool/BV/Int handles, assumptions, proof/minimized proof calls, scalar model lifting, overflow predicates |
| PROP.2 | Ergonomic expression syntax | WIP — `.equals()` aliases for Bool/BV/Int, property-owned Bool/BV/Int builder aliases, and `Property::all` / `Property::any` Boolean folds landed; broader operator traits or richer chaining style remains open |
| PROP.3 | `Symbolic` trait and derive | WIP — scalar Bool/uN/iN/i128 plus 2-/3-tuples declare and lift deterministically; `i8`/`i16`/`i32`/`i64` use two's-complement BV terms and signed counterexample minimization while `i128` remains mathematical Int; `symbolic_struct` covers macro-free named-field bundles; `#[derive(Symbolic)]` supports named/tuple/unit structs |
| PROP.4 | Counterexample-to-test layer | WIP — native Bool/Int/BV<=128 bindings render as deterministic Rust let-bindings and `#[test]` skeletons, including signed two's-complement Rust literals for signed symbolic BV inputs; direct named/tuple symbolic bundles render Rust aggregate initializer statements; explicit nested aggregate field expressions plus prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, and deterministic multi-case fixture file assembly let frontends compose caller-owned domain replay shapes before assertions |
| PROP.5 | Lean certificate surface | WIP — `EvidenceReport` is re-exported, `ProofCertificate` exposes proved evidence, `prove_with_certificate` / `prove_minimized_with_certificate` attach best-effort standalone Lean modules, and `ProofCertificate::summary()` surfaces stable evidence/trust/Lean diagnostics |
| PROP.6 | SDK measurement gate | WIP — committed graduated corpus, generated `SCOREBOARD.md`, and machine-readable `corpus.json` cover 12 cases with DISAGREE=0, 1/1 Lean-required coverage, a mixed Bool/BV/Int expression-builder alias proof, and deterministic executable baseline comparisons for scalar counterexamples, struct counterexamples, and a proved assertion; broader external proptest/Kani-style baseline comparison remains open |

## Guardrails
- The crate must remain solver-logic-free: it builds terms and delegates.
- Unsupported proof or minimization fragments must remain explicit `Unknown` or
  `Unsupported`, never a fake proof or fake minimum.
- Model lifting must stay replay-backed by the solver outcome; no independent
  interpretation of solver results.
- Test rendering may provide inputs and a skeleton, but domain replay code must
  still come from the caller/frontend.
