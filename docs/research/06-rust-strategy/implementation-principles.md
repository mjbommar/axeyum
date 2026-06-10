# Rust Implementation Principles

Status: draft
Last updated: 2026-06-10

## Purpose

Define implementation principles for a Rust-native reasoning stack.

## Scope

In scope:

- Ownership, IDs, arenas, features, dependencies, and public API discipline.

Out of scope:

- Detailed crate implementation.

## Core Claims

- High-performance reasoning code should be arena- and ID-oriented.
- Public APIs should be safe Rust, deterministic, and explicit about resource limits.
- Native solver backends should be feature-gated.
- The pure Rust core should have no C/C++ build dependency.

## Preferred Patterns

- `u32` newtype IDs for terms, sorts, symbols, wires, literals, variables, clauses.
- `Vec<T>` arenas and side tables.
- `SmallVec` or fixed arrays for common small child lists.
- `hashbrown` or `rustc_hash` after profiling justifies it.
- Immutable interned terms.
- Typed builder APIs.
- Explicit `Result<T, E>` for parse/build/backend errors.
- Feature gates for optional solvers and proof formats.

## Avoid

- Recursive `Box`/`Rc` term trees in hot paths.
- Backend ASTs in core IR.
- Stringly typed operators.
- Global mutable solver state.
- Silent sort coercions.
- Hidden nondeterminism in simplification or search.

## Design Implications

- Use `cargo bench` and query corpora before optimizing deeply.
- Keep debug renderers separate from canonical serialization.
- Add deterministic IDs and stable iteration order where possible.
- Make resource limits explicit: time, memory, conflict count, node count, rewrite fuel.

## Risks

- Over-abstracting traits can block low-level optimization.
- Under-abstracting can make backend experiments expensive.
- Unsafe code may eventually be justified in hot paths, but only behind narrow modules.

## Open Questions

- [ ] Which hash map should be default before benchmarking?
- [ ] Should arenas support generational IDs or plain dense IDs?
- [ ] Should no-std be a long-term goal for SAT/CNF crates?

## Source Pointers

- RustSAT: https://github.com/chrjabs/rustsat
- varisat: https://github.com/jix/varisat
- splr: https://github.com/shnarazk/splr

