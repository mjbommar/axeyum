# User Guide

How to run Axeyum, read its answers, and stay inside what it actually supports.

```mermaid
flowchart LR
    I[Install / build] --> Q[Run a query]
    Q --> R[Read the result]
    R --> sat[sat → use &amp; trust the model]
    R --> unsat[unsat → checkable certificate]
    R --> unk[unknown → resource/incompleteness]
    Q --> L[Know the limits]
    classDef a fill:#eef,stroke:#557;
    class I,Q,R,L a;
```

| Page | What |
|---|---|
| installation.md *(planned)* | toolchain, `just check`, optional `z3` feature |
| [First SMT-LIB query](first-smtlib-query.md) | run a query from SMT-LIB text |
| first-rust-query.md *(planned)* | build a query with the typed IR |
| models-and-replay.md *(planned)* | read a model; what replay guarantees |
| unsat-evidence.md *(planned)* | DRAT/LRAT/Alethe and `recheck` |
| [Limitations](limitations.md) | what's experimental/incomplete — read before trusting support |
| [Benchmarks](benchmarks.md) | the measured Z3 head-to-head + how to reproduce |
| wasm.md *(planned)* | the browser build and the [playground](../playground/README.md) |

**Golden rule for users:** read [Limitations](limitations.md) and the
[capability matrix](../research/08-planning/capability-matrix.md) before relying
on any fragment. Axeyum is honest about `unknown`; make sure your integration is
too.
