# Internals

These pages explain the implementation contracts behind the public API. They
summarize current code; the durable rationale remains in
[`research/`](../research/README.md), and mutable session state remains only in
the root [`PLAN.md`](../../PLAN.md).

## Core path

| Page | Contract |
|---|---|
| [Architecture](architecture.md) | workspace boundaries, dataflow, and trust placement |
| [Term IR](term-ir.md) | typed nodes, arena ownership, and stable handles |
| [Ground evaluation](evaluator.md) | executable semantics and source-model replay |
| [Rewriting](rewriting.md) | preservation manifests and model reconstruction |
| [Bit-blasting](bit-blasting.md) | typed Bool/BV terms to AIG plus lift maps |
| [CNF and SAT](cnf-and-sat.md) | Tseitin bindings, solving modes, and propositional evidence |
| [Solver dispatch](solver-dispatch.md) | route admission, fallback, limits, and verdict discipline |
| [Proof and evidence](proof-stack.md) | model, certificate, Alethe, and Lean assurance routes |
| [Lean kernel](lean-kernel.md) | checked environment and fail-closed import boundary |
| [Documentation](documentation.md) | book structure, diagrams, playground, and validation |

For a narrative explanation before the implementation detail, start with
[How Axeyum solves a query](../learn/07-how-axeyum-solves-a-query.md). For exact
current fragment coverage, use the generated
[support matrix](../reference/support-matrix.md).
