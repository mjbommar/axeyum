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
- proof calls delegate to `axeyum_solver::{prove, prove_minimized}`;
- scalar model lifting reads values from `Model`;
- typed unsigned BV overflow predicates expose the core overflow builders.

## Tasks
| id | task | exit |
|---|---|---|
| PROP.1 | Typed scalar proof SDK | DONE — Bool/BV/Int handles, assumptions, proof/minimized proof calls, scalar model lifting, overflow predicates |
| PROP.2 | Ergonomic expression syntax | TODO — operator traits or a small builder style that does not hide fallible construction |
| PROP.3 | `Symbolic` trait and derive | TODO — structs become typed symbolic inputs with deterministic field/objective order |
| PROP.4 | Counterexample-to-test layer | TODO — produce runnable `#[test]` snippets from typed disproving models |
| PROP.5 | Lean certificate surface | TODO — expose `EvidenceReport` plus best-effort standalone Lean module when available |
| PROP.6 | SDK measurement gate | TODO — committed graduated corpus and scoreboard vs proptest/Kani-style baselines, DISAGREE=0 |

## Guardrails
- The crate must remain solver-logic-free: it builds terms and delegates.
- Unsupported proof or minimization fragments must remain explicit `Unknown` or
  `Unsupported`, never a fake proof or fake minimum.
- Model lifting must stay replay-backed by the solver outcome; no independent
  interpretation of solver results.
