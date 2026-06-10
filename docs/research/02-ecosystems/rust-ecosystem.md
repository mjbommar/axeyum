# Rust Ecosystem

Status: draft
Last updated: 2026-06-10

## Purpose

Identify what Rust already has and where Axeyum can add value.

## Scope

In scope:

- Rust SAT solvers, solver bindings, verification tools, and rewriting libraries.

Out of scope:

- Full crate-by-crate API evaluation.

## Core Claims

- Rust has useful SAT solvers and SAT infrastructure.
- Rust has practical bindings to mature native SMT solvers.
- Rust does not yet have a broadly adopted, mature, pure Rust QF_BV SMT solver
  competitive with the leading native C/C++ engines.
- Axeyum can add value by connecting typed IR, rewrites, bit-blasting, SAT, models,
  proof checking, and backend abstraction in one coherent Rust-native stack.

## Pure Rust SAT And SAT Infrastructure

| Project | Notes | Relevance |
|---|---|---|
| RustSAT | SAT library ecosystem for encodings and solver interfaces. | Interop and inspiration. |
| varisat | SAT solver written in Rust with DRAT/LRAT proof output; effectively unmaintained (last release 2019). | Proof-output design reference; backend candidate with maintenance caveat. |
| splr | Modern Rust CDCL SAT solver inspired by Glucose/Kissat/CaDiCaL ideas. | Algorithmic reference. |
| batsat | MiniSat-derived Rust SAT solver. | Simpler design reference. |
| CreuSAT | Formally verified Rust SAT solver verified with Creusot. | Evidence/checking reference. |

## Rust SMT Bindings

| Project | Notes | Relevance |
|---|---|---|
| z3.rs | Rust bindings for Z3; 0.20 removed the `'ctx` lifetime API (contexts managed internally). | Primary native backend path. |
| cvc5-rs | Rust bindings for cvc5. | Alternative backend. |
| bitwuzla-sys | Low-level Bitwuzla bindings. | BV backend path. |
| boolector-rs | Rust bindings for Boolector. | Legacy/reference backend. |

## Rust Verification And Symbolic Tools

| Project | Notes | Relevance |
|---|---|---|
| Kani | Rust verifier based on model checking. | Client and comparison point. |
| Crux-MIR | Rust symbolic verification through Crucible. | Architecture reference. |
| Prusti/MIRAI/Creusot | Rust verification tools with different foundations. | Verification ecosystem context. |

## Rewriting And Equality Saturation

| Project | Notes | Relevance |
|---|---|---|
| egg | High-performance e-graph library. | Optional rewrite exploration engine. |
| egglog | Relational/e-graph style reasoning. | Future research path. |

## Design Implications

- Axeyum should not duplicate RustSAT's generic SAT infrastructure blindly; it
  should interoperate where useful.
- The first pure Rust backend can use an existing Rust SAT solver while Axeyum
  focuses on IR, rewriting, bit-blasting, CNF, and model lifting.
- A custom SAT core should come after benchmarks show the existing backends are
  the bottleneck.
- Native SMT bindings should be optional features, not base dependencies.

## Risks

- Rust solver crates vary in maintenance, API stability, proof support, and
  incremental solving support.
- Wrapping native solvers can leak lifetime and context constraints into public APIs
  unless isolated behind Axeyum-owned traits.

## Open Questions

- [ ] Which existing Rust SAT backend should be the first integration target?
- [ ] Should Axeyum expose RustSAT-compatible types or adapters?
- [ ] Should the first Z3 backend use `z3.rs` directly or a narrow internal wrapper?

## Source Pointers

- RustSAT: https://github.com/chrjabs/rustsat
- varisat: https://github.com/jix/varisat
- splr: https://github.com/shnarazk/splr
- batsat: https://github.com/c-cube/batsat
- CreuSAT: https://github.com/sarsko/CreuSAT
- z3.rs: https://github.com/prove-rs/z3.rs
- egg: https://github.com/egraphs-good/egg
- Kani: https://model-checking.github.io/kani/
- Crux-MIR: https://github.com/GaloisInc/crucible/tree/master/crux-mir

