# axeyum-ir

Typed term IR for the [Axeyum](https://github.com/mjbommar/axeyum) automated
reasoning stack: sorts, symbols, terms stored as an interned DAG with compact
`u32` newtype IDs, typed builders, and the ground evaluator that serves as
the executable semantic reference for every other layer.

Pure Rust, no C/C++ dependencies.

Design rationale:

- [Term IR](../../docs/research/04-data-structures/term-ir.md) — arena,
  interning, ID design.
- [BV semantics](../../docs/research/01-foundations/bv-semantics-and-partial-operations.md)
  — the SMT-LIB edge-case semantics implemented verbatim.
- [API design](../../docs/research/06-rust-strategy/api-design-concurrency-and-stability.md)
  — lifetime-free `Copy` handles, append-only arena, determinism rules.

Status: pre-M0 stub. First contents are scoped by
[ADR-0001](../../docs/research/09-decisions/adr-0001-vertical-slice-first.md).

License: MIT OR Apache-2.0.
