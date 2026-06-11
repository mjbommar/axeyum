# CLAUDE.md

Guidance for Claude Code (and other agents) working in this repository.

## What This Project Is

Axeyum is a Rust-first automated reasoning stack: typed term IR → rewriting →
query planning → solver backends (native SMT oracles + a pure Rust
bit-blast-to-SAT path) → models, proofs, and checkable evidence. Identity in
one sentence: **untrusted fast search, trusted small checking.**

North star: a **complete framework for general reasoning, logic, and
proving** — the finite-domain core (SAT/QF_BV) is the foundation layer, and
the ladder continues through arithmetic, theory combination, quantifiers,
and proof production
([north-star note](docs/research/00-orientation/north-star.md)). Design
choices should not paint the IR, solver trait, or evidence formats into a
quantifier-free corner.

## Session Protocol

1. Read [PLAN.md](PLAN.md) **first** — it carries current status, the next
   actions, and the resume protocol. It is the only file with mutable session
   state.
2. Work against the current roadmap phase and its exit criteria:
   [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md).
3. Decisions are not made silently in code. Check
   [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md)
   and [docs/research/09-decisions/](docs/research/09-decisions/README.md);
   close questions with ADRs (template in the decisions README).
4. Before ending a session: update PLAN.md's **Status** and **Next Actions**
   sections.

## Commands

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
cargo doc --workspace --all-features --no-deps    # RUSTDOCFLAGS="-D warnings" in CI
cargo deny check                                  # needs cargo-deny installed
```

Local default toolchain may be nightly; CI runs stable plus an MSRV (1.85)
check. Edition 2024, resolver 3.

## Layout

- `crates/axeyum-ir` — sorts, terms, arena/interning, ground evaluator.
- `crates/axeyum-solver` — backend trait, results, models, capabilities;
  native backends behind feature flags (`z3` arrives with milestone M0).
- `docs/research/` — 35 research notes; the design rationale for everything.
  Folder map in [docs/research/README.md](docs/research/README.md).
- `references/` — gitignored shallow clones of reference solvers/checkers;
  repopulate with `scripts/fetch-references.sh`. Read these when implementing
  (e.g. CaDiCaL for clause arenas, varisat for Rust CDCL + proof output).
- Crate split is deliberately minimal (ADR-0001): do not add crates until a
  boundary is proven by use.
- The pure Rust stack including a custom CDCL SAT core is the product; the
  Z3 oracle is bootstrap scaffolding with a planned demotion path
  (ADR-0002). Never expand reliance on linked solvers beyond
  backend/differential-oracle/CI-cross-check roles without a new ADR.

## Hard Rules

- The default build must compile with **no C/C++ dependency**; native solver
  backends are feature-gated leaf dependencies only.
- `unsafe_code` is denied workspace-wide (workspace lints); exceptions need
  an ADR.
- `unknown` is a first-class solver result, never an error.
- Determinism is a public API promise: stable iteration order, explicit
  seeds, explicit resource limits. No hash-map iteration order in output.
- Every `sat` result must be checkable by evaluating the original term
  against the lifted model; never drop lowering/lift maps after solving.
- Term handles are lifetime-free `Copy` IDs; never let backend FFI types or
  lifetimes leak into public APIs.
- BV operator semantics follow SMT-LIB totality verbatim (e.g.
  `bvudiv x 0` = all-ones); see
  [docs/research/01-foundations/bv-semantics-and-partial-operations.md](docs/research/01-foundations/bv-semantics-and-partial-operations.md).

## Gotchas

- The `z3` crate ≥ 0.20 removed the old `'ctx` lifetime API; `Solver::new()`
  takes no arguments and contexts are managed internally
  (`with_z3_context`/`with_z3_config`). Don't copy pre-0.20 examples.
- varisat is effectively unmaintained (last release 2019) but is the only
  Rust SAT solver with DRAT/LRAT proof output; treat it as a design reference
  and benchmark candidate, not a guaranteed dependency.
- The custom CDCL core is settled identity (ADR-0002) but its *priority* is
  gated by
  [docs/research/08-planning/benchmarking-and-performance-methodology.md](docs/research/08-planning/benchmarking-and-performance-methodology.md);
  encodings come first until SAT time dominates on real corpora. Lazy
  techniques are likewise priority-gated.
