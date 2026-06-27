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
- `Symbolic` declares and lifts scalar Bool/unsigned-BV/Int-backed values plus
  2-/3-tuples with deterministic field names;
- `Property::symbolic_struct` gives macro-free named-field bundles for
  struct-shaped inputs, and `#[derive(axeyum_property::Symbolic)]` lowers named
  and tuple structs to that surface;
- proof calls delegate to `axeyum_solver::{prove, prove_minimized}`;
- scalar model lifting reads values from `Model`;
- typed unsigned BV overflow predicates expose the core overflow builders.
- `Counterexample` / `InputBinding` render native scalar model values as Rust
  let-bindings or a `#[test]` skeleton with caller-provided replay code.

## Tasks
| id | task | exit |
|---|---|---|
| PROP.1 | Typed scalar proof SDK | DONE — Bool/BV/Int handles, assumptions, proof/minimized proof calls, scalar model lifting, overflow predicates |
| PROP.2 | Ergonomic expression syntax | TODO — operator traits or a small builder style that does not hide fallible construction |
| PROP.3 | `Symbolic` trait and derive | WIP — scalar Bool/uN/i128 plus 2-/3-tuples declare and lift deterministically; `symbolic_struct` covers macro-free named-field bundles; `#[derive(Symbolic)]` supports named/tuple/unit structs; signed fixed-width Rust integers remain |
| PROP.4 | Counterexample-to-test layer | WIP — native Bool/Int/BV<=128 bindings render as deterministic Rust let-bindings and `#[test]` skeletons; richer structured/domain replay remains |
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
