# AGENTS.md

Guidance for Codex (and other agents) working in this repository.

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
3. Before adding public operators, rewrites, encodings, backends, evidence
   artifacts, or logic fragments, check the foundational dependency DAG:
   [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md).
4. Decisions are not made silently in code. Check
   [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md)
   and [docs/research/09-decisions/](docs/research/09-decisions/README.md);
   close questions with ADRs (template in the decisions README).
5. Before ending a session: update PLAN.md's **Status** and **Next Actions**
   sections.

## Commands

```sh
just check          # fmt + clippy + test + doc + docs link check (preferred)
just bench-micro    # committed SMT-LIB micro corpus through axeyum-bench
just bench-public-qfbv-sat-bv-compare  # Phase 5 public sat-bv vs Z3 slice
just bench-public-qfbv-sat-bv-guarded  # Phase 5 node/CNF guarded run
just bench-public-qfbv-sat-bv-replay-refine  # replay-checked query refinement
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
cargo doc --workspace --all-features --no-deps    # RUSTDOCFLAGS="-D warnings" in CI
cargo deny check                                  # needs cargo-deny installed
./scripts/check-links.sh                          # docs relative-link check (CI job)
```

Local default toolchain may be nightly; CI runs stable plus an MSRV (1.85)
check. Edition 2024, resolver 3.

## Layout

- `crates/axeyum-ir` — sorts, terms, arena/interning, ground evaluator,
  LSB-first value/bit conversion helpers.
- `crates/axeyum-aig` — AIG circuit graph with deterministic structural
  hashing, evaluation, and ASCII AIGER debug export.
- `crates/axeyum-bv` — term-to-AIG bit lowering with explicit term-bit and
  symbol-input maps for the supported Bool/BV operator subset.
- `crates/axeyum-cnf` — simple Tseitin encoding from AIG, DIMACS I/O, CNF
  evaluation, BatSat-backed solving, and CNF-variable-to-AIG replay maps.
- `crates/axeyum-query` — query object: assertions, assumptions, scopes,
  stable labels.
- `crates/axeyum-rewrite` — rewrite manifest contracts and the first
  denotation-preserving canonicalizer.
- `crates/axeyum-solver` — backend trait, results, models, capabilities;
  default pure Rust SAT-backed BV backend plus native backends behind feature
  flags (`z3` is the oracle path).
- `crates/axeyum-smtlib` — SMT-LIB benchmark-slice parser and
  sharing-preserving writer.
- `crates/axeyum-bench` — corpus benchmark harness with backend selection,
  PAR-2 scoring, model replay, and JSON artifacts.
- `docs/research/` — research notes; the design rationale for everything.
  Folder map in [docs/research/README.md](docs/research/README.md).
- `references/` — gitignored shallow clones of reference solvers/checkers;
  repopulate with `scripts/fetch-references.sh`. Read these when implementing
  (e.g. CaDiCaL for clause arenas, varisat for Rust CDCL + proof output).
- Crate split is deliberately minimal (ADR-0001): add crates only after a
  boundary is proven by use (`axeyum-smtlib` and `axeyum-bench` are such
  exercised boundaries; `axeyum-query` and `axeyum-rewrite` are the Phase 3
  contract boundaries accepted in ADR-0005; `axeyum-aig`, `axeyum-bv`, and
  `axeyum-cnf` are the Phase 4 circuit/lowering/CNF boundaries accepted in
  ADR-0006; `rustsat-batsat` is the first pure-Rust SAT adapter accepted in
  ADR-0007).
- The pure Rust stack including a custom CDCL SAT core is the product; the
  Z3 oracle is bootstrap scaffolding with a planned demotion path
  (ADR-0002). Never expand reliance on linked solvers beyond
  backend/differential-oracle/CI-cross-check roles without a new ADR.

## Hard Rules

- The default build must compile with **no C/C++ dependency**; native solver
  backends are feature-gated leaf dependencies only.
- `unsafe_code` is denied workspace-wide (workspace lints); exceptions need
  an ADR.
- Semantics, model/proof lifting, and replay/checker routes must be explicit
  before a new operator, rewrite class, encoding, backend, or logic fragment
  becomes public surface.
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
- The first pure-Rust SAT adapter is `rustsat-batsat` through RustSAT
  (ADR-0007). Its UNSAT results are lower-assurance until a proof-producing
  route and checker exist.
- The custom CDCL core is settled identity (ADR-0002) but its *priority* is
  gated by
  [docs/research/08-planning/benchmarking-and-performance-methodology.md](docs/research/08-planning/benchmarking-and-performance-methodology.md);
  encodings come first until SAT time dominates on real corpora. Lazy
  techniques are likewise priority-gated.
