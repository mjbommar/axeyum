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
       <- native backend features
       <- axeyum-bv
            <- axeyum-aig / axeyum-cnf / future axeyum-sat
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
| `axeyum-solver` | Backend trait, model/result types, capability descriptions, current pure Rust BV backend. |
| `axeyum-solver-z3` | Optional Z3 backend. |
| `axeyum-solver-bitwuzla` | Optional Bitwuzla backend. |
| `axeyum-sat` | SAT traits, literals, clauses, optional CDCL implementation. |
| `axeyum-cnf` | CNF builder, DIMACS I/O, Tseitin encodings. |
| `axeyum-aig` | Structural hashing circuit graph. |
| `axeyum-bv` | Bit-vector bit-blasting and model lifting. |
| `axeyum-proof` | Proof/certificate formats and checkers. |
| `axeyum-cli` | Debugging and research command-line tools. |

## Current Exercised Workspace

The implemented workspace is still deliberately smaller than the target list,
but Phase 5 now exercises the first composed pure Rust BV backend boundary:

- `axeyum-ir`: typed scalar Bool/BV term DAG, evaluator, and LSB-first
  value/bit conversion helpers
  ([ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md)).
- `axeyum-aig`: AIG circuit graph with deterministic structural hashing and
  evaluator
  ([ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md)).
- `axeyum-bv`: term-to-AIG bit lowering with explicit term-bit and
  symbol-input maps for the full scalar QF_BV operator set
  ([ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md)).
- `axeyum-cnf`: simple Tseitin encoding from AIG, DIMACS I/O, CNF evaluator,
  CNF-variable-to-AIG lift maps, and the first `rustsat-batsat` SAT adapter
  path
  ([ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md),
  [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md)).
- `axeyum-query`: assertions, assumptions, scopes, stable labels, structural
  cache keys, and replay-checked target-support slicing
  ([ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)).
- `axeyum-rewrite`: rewrite manifests plus the first denotation-preserving
  canonicalizer
  ([ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)).
- `axeyum-solver`: backend trait, models, results, capabilities, the
  native-free `SatBvBackend` for the supported QF_BV subset, and the
  feature-gated Z3 oracle.
- `axeyum-smtlib`: benchmark-slice parser and sharing-preserving writer.
- `axeyum-bench`: corpus harness with backend selection and evidence-producing
  JSON artifacts.

## Risks

- Splitting crates before APIs stabilize can create churn.
- A single facade crate may hide useful internal instrumentation from researchers.

## Open Questions

- [ ] Should `axeyum-core` exist or should small shared types live in their owning crates?
- [x] Should the first implementation start as fewer crates and split after tests?
  - Answer: yes. M0 started with `axeyum-ir` and `axeyum-solver`
    ([ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)); format,
    benchmark, query, and rewrite crates split after those boundaries were
    exercised by use
    ([ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)).
- [ ] Should `axeyum` be a facade crate from day one?

## Source Pointers

- Cargo workspaces: https://doc.rust-lang.org/cargo/reference/workspaces.html
- z3.rs backend reference: https://github.com/prove-rs/z3.rs
