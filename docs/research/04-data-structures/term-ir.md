# Term IR

Status: draft
Last updated: 2026-06-10

## Purpose

Define the core representation for logical terms.

## Scope

In scope:

- Sorts, terms, operators, arenas, IDs, interning, provenance.

Out of scope:

- Complete Rust API.

## Core Claims

- Terms should be stored as an interned DAG, not recursive owned trees.
- Every term must have an explicit sort.
- Compact IDs should be the public handles.
- Builder functions should enforce type correctness.
- Provenance should be optional but supported by the arena design.

## Candidate Types

```text
SortId(u32)
TermId(u32)
SymbolId(u32)

Sort =
  Bool
  Bv(width)
  Array(index_sort, value_sort)
  Uninterpreted(name)

Term =
  Const
  Symbol
  App(op, children)
  Binder(later)
```

## Operator Families

- Boolean: `not`, `and`, `or`, `xor`, `implies`, `ite`.
- Bit-vector: arithmetic, bitwise, compare, concat, extract, extend, shifts, rotates.
- Array: `select`, `store`, constant array.
- EUF: uninterpreted function application.

## Design Implications

- Do not use backend AST objects in the core.
- Avoid `Rc<Term>` in hot paths; use arenas and integer IDs.
- Hash-consing should use precomputed structural keys.
- Commutative ops should canonicalize child order where legal.
- N-ary ops should be considered for `and`, `or`, `add`, and bitwise ops to reduce tree depth.

## Risks

- Overly eager canonicalization can obscure provenance.
- Insufficient sort checking will create backend-specific failures later.

## Open Questions

- [ ] Should terms be immutable after interning?
- [ ] Should the arena support deletion/GC or only epoch-level dropping?
- [ ] Should provenance be stored inline or in side tables?
- [ ] Should `Bool` and `BV(1)` be distinct at all API layers?

## Source Pointers

- egg e-graphs for rewrite inspiration: https://github.com/egraphs-good/egg
- SMT-LIB standard: https://smt-lib.org/

