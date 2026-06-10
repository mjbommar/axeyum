# Performance And Ergonomics

Status: draft
Last updated: 2026-06-10

## Purpose

Balance research flexibility, solver performance, and user ergonomics.

## Scope

In scope:

- API ergonomics, performance instrumentation, and debug surfaces.

Out of scope:

- Final benchmark numbers.

## Core Claims

- Research users need visibility into internal transformations.
- Production users need a simple facade and predictable resource limits.
- Performance work should be driven by real query corpora.
- Debuggability is a feature in solver infrastructure.

## User Modes

| Mode | Needs |
|---|---|
| Math/CS research | Inspect terms, rewrites, encodings, proofs, statistics. |
| Verification | Stable APIs, checkable evidence, reproducibility. |
| Infosec | Concrete witnesses, replay, byte-level models, timeouts. |
| Solver R&D | Low-level hooks, benchmark harnesses, traces. |

## Design Implications

- Provide both builder ergonomics and low-level arena APIs.
- Expose statistics at every major layer.
- Keep pretty-printing, SMT-LIB, DIMACS, AIGER, and internal serialization separate.
- Build a CLI for inspecting terms, CNF, models, and backend results.

## Risks

- A friendly API can hide performance traps such as accidental term duplication.
- Too much instrumentation can slow hot paths if not feature-gated or sampled.

## Open Questions

- [ ] What should the first CLI command inspect?
- [ ] Should query corpus replay be a separate binary?
- [ ] How should users attach names and source locations to symbols?

## Source Pointers

- CaDiCaL documentation style reference: https://github.com/arminbiere/cadical
- egg debug and explainability reference: https://github.com/egraphs-good/egg

