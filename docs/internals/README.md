# Internals

Implementation architecture. These pages **summarize** the design; they do not
replace the deep design record in [`research/`](../research/README.md) or the
roadmap in [`plan/`](../plan/README.md) — they link to it.

| Page | What |
|---|---|
| [Architecture](architecture.md) | crate graph, pipeline→crate map, hard rules |
| term-ir.md *(planned)* | arena, hash-consing, ground evaluator |
| bit-blasting.md *(planned)* | term → AIG → CNF |
| cnf-and-sat.md *(planned)* | Tseitin, batsat, native CDCL, DRAT |
| proof-stack.md *(planned)* | DRAT → LRAT → Alethe |
| lean-kernel.md *(planned)* | the Rust Lean-grade kernel + reconstruction |
| [Documentation](documentation.md) | how these docs are built, and why |

Start with [Architecture](architecture.md).
