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
- scalar model lifting reads values from `Model`;
- typed unsigned BV overflow predicates expose the core overflow builders.
- `Counterexample` / `InputBinding` render native scalar model values as Rust
  let-bindings or a `#[test]` skeleton with caller-provided replay code,
  preserving signed two's-complement Rust integer intent for signed symbolic BV
  inputs.

## Tasks
| id | task | exit |
|---|---|---|
| PROP.1 | Typed scalar proof SDK | DONE — Bool/BV/Int handles, assumptions, proof/minimized proof calls, scalar model lifting, overflow predicates |
| PROP.2 | Ergonomic expression syntax | TODO — operator traits or a small builder style that does not hide fallible construction |
| PROP.3 | `Symbolic` trait and derive | WIP — scalar Bool/uN/iN/i128 plus 2-/3-tuples declare and lift deterministically; `i8`/`i16`/`i32`/`i64` use two's-complement BV terms and signed counterexample minimization while `i128` remains mathematical Int; `symbolic_struct` covers macro-free named-field bundles; `#[derive(Symbolic)]` supports named/tuple/unit structs |
| PROP.4 | Counterexample-to-test layer | WIP — native Bool/Int/BV<=128 bindings render as deterministic Rust let-bindings and `#[test]` skeletons, including signed two's-complement Rust literals for signed symbolic BV inputs; richer structured/domain replay remains |
| PROP.5 | Lean certificate surface | TODO — expose `EvidenceReport` plus best-effort standalone Lean module when available |
| PROP.6 | SDK measurement gate | TODO — committed graduated corpus and scoreboard vs proptest/Kani-style baselines, DISAGREE=0 |

## Guardrails
- The crate must remain solver-logic-free: it builds terms and delegates.
- Unsupported proof or minimization fragments must remain explicit `Unknown` or
  `Unsupported`, never a fake proof or fake minimum.
- Model lifting must stay replay-backed by the solver outcome; no independent
  interpretation of solver results.
- Test rendering may provide inputs and a skeleton, but domain replay code must
  still come from the caller/frontend.
