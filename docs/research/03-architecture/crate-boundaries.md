# Crate Boundaries

Status: draft
Last updated: 2026-06-10

## Purpose

Propose an initial workspace layout that keeps Axeyum independent and reusable.

## Scope

In scope:

- Crate names, responsibilities, and dependency direction.

Out of scope:

- Final module-level API design.

## Core Claims

- Lower crates should never depend on application frontends.
- Native solver bindings should be optional leaf crates.
- The pure Rust path should be buildable without C or C++ dependencies.
- The public facade should be convenient, but core crates should remain separately usable.

## Proposed Workspace

```text
crates/axeyum-core
crates/axeyum-ir
crates/axeyum-rewrite
crates/axeyum-query
crates/axeyum-solver
crates/axeyum-solver-z3
crates/axeyum-solver-bitwuzla
crates/axeyum-sat
crates/axeyum-cnf
crates/axeyum-aig
crates/axeyum-bv
crates/axeyum-proof
crates/axeyum-cli
```

## Dependency Direction

```text
axeyum-ir
  <- axeyum-rewrite
  <- axeyum-query
  <- axeyum-solver
       <- native backend crates
       <- axeyum-bv
            <- axeyum-aig / axeyum-cnf / axeyum-sat
```

The exact arrows may change, but application-specific crates should remain
outside the lower solver stack.

## Crate Responsibilities

| Crate | Responsibility |
|---|---|
| `axeyum-core` | Shared small types, diagnostics, errors, feature flags. |
| `axeyum-ir` | Sorts, terms, operators, hash-consing, builders, SMT-LIB rendering/parsing later. |
| `axeyum-rewrite` | Simplification and canonicalization. |
| `axeyum-query` | Assertions, assumptions, scopes, slicing, cache keys. |
| `axeyum-solver` | Backend trait, model/result types, capability descriptions. |
| `axeyum-solver-z3` | Optional Z3 backend. |
| `axeyum-solver-bitwuzla` | Optional Bitwuzla backend. |
| `axeyum-sat` | SAT traits, literals, clauses, optional CDCL implementation. |
| `axeyum-cnf` | CNF builder, DIMACS I/O, Tseitin encodings. |
| `axeyum-aig` | Structural hashing circuit graph. |
| `axeyum-bv` | Bit-vector bit-blasting and model lifting. |
| `axeyum-proof` | Proof/certificate formats and checkers. |
| `axeyum-cli` | Debugging and research command-line tools. |

## Risks

- Splitting crates before APIs stabilize can create churn.
- A single facade crate may hide useful internal instrumentation from researchers.

## Open Questions

- [ ] Should `axeyum-core` exist or should small shared types live in their owning crates?
- [ ] Should the first implementation start as fewer crates and split after tests?
- [ ] Should `axeyum` be a facade crate from day one?

## Source Pointers

- Cargo workspaces: https://doc.rust-lang.org/cargo/reference/workspaces.html
- z3.rs backend reference: https://github.com/prove-rs/z3.rs

