# Arrays, Memory, And EUF

Status: draft
Last updated: 2026-06-10

## Purpose

Plan beyond scalar QF_BV toward arrays, memory, and uninterpreted functions.

## Scope

In scope:

- SMT arrays, symbolic memory overlays, select/store, and EUF abstraction.

Out of scope:

- Full array decision procedure implementation.

## Core Claims

- Arrays are the natural logical model for memory but not always the best first
  operational model.
- Practical symbolic engines often use concrete memory plus symbolic overlays and
  write logs before lowering to array constraints.
- EUF is useful for summaries and abstraction.
- Pure SAT lowering of arrays requires additional transformations such as
  Ackermannization or bounded memory expansion.

## Memory Model Pattern

```text
base concrete memory
  + symbolic writes
  + path conditions
  + read resolver
  -> value expression or array constraint
```

Read resolution:

```text
for recent writes newest to oldest:
  if must-alias: return write value
  if may-alias: return ite(alias_cond, write_value, older_value)
fall back to base memory or symbolic array select
```

## Design Implications

- Do not make arrays mandatory for first scalar BV backend.
- Keep array terms in the IR early so native SMT backends can support them.
- Add memory-specific helper encodings as client-side libraries or optional crates.
- Preserve alias constraints separately enough to slice queries.

## Risks

- Naive select/store chains can explode.
- Symbolic indices require careful concretization or bounding policies.
- EUF abstraction can be unsound if clients forget required axioms.

## Open Questions

- [ ] Should `Array` be in `axeyum-ir` 0.1 even if pure Rust backend does not support it?
- [ ] Should memory overlays be an Axeyum crate or left to program-analysis clients?
- [ ] What bounded array encoding should come first?

## Source Pointers

- Boolector arrays and BV: https://github.com/Boolector/boolector
- Bitwuzla arrays and BV: https://bitwuzla.github.io/docs/
- KLEE memory modeling reference: https://klee-se.org/

