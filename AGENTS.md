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

## The Flywheel — what the increments are for

Every task here is one turn of a single cycle. Know which arrow you are on:

```
        library (proved ℕ, ℤ, …)
             │  gives the solver facts to reason with
             ▼
        solver (30 logics, CAS, quantifiers)
             │  decides goals the library needs
             ▼
        reconstruction  →  kernel term  →  admitted, axiom-free
             │  becomes a library theorem
             └──────────────────────────────┐
                                            │
        the concept DAG and the fact ledger ┘  say what to prove next
```

A proof library is normally a one-way pipeline: people write proofs, a kernel
checks them. This one is a cycle, and that is the architectural bet. **Every
arrow already exists and the cycle has closed end to end**; what it has never
been is *automatic*, and making it automatic is the point of the work — not
theorem count, not benchmark position. The argument and the measured production
rate are in
[`docs/formalized-math-2026-08/05-throughput.md`](docs/formalized-math-2026-08/05-throughput.md).

Two consequences for how you work:

- **The metric is the trusted base, not the output volume.** Assumptions
  remaining per prelude, and results the system established with nobody writing
  the proof. Read both from the kernel — `nat_theorem_inventory`,
  `int_theorem_inventory`, `theorem_axiom_footprint`, `nat_axiom_inventory` —
  never from source text. Grepping `Declaration::Theorem` returns 1 against 119
  real theorems, and three separate counts of this repository's theorems were
  wrong before anyone built the environment to look.
- **At N lanes the ledger IS the product, so a checker that cannot fail is worse
  than no checker.** It does not slow the flywheel; it makes it manufacture
  unfalsifiable claims at full speed. Audited 2026-08-15: 40 of 162 checker runs
  across 36 settled facts exit 0 on completion alone, including the inventory
  asserting axiom-freedom. Make a checker's exit status depend on what it found,
  and confirm a tool's *coverage* includes your subject before believing its
  zero.

The fact ledger is `artifacts/facts/` (schema `artifacts/ontology/fact.schema.json`,
gated by `python3 scripts/validate-facts.py`): one JSON file per mathematical
proposition, carrying a formal statement, a status, its evidence and its axiom
footprint. It is what the self-extension loop consumes — take an `open` fact
whose `depends_on` are established, dispatch `formal.statement`, reconstruct,
attach evidence, flip the status, record the footprint.

## Session Protocol

1. Read [PLAN.md](PLAN.md) **first** — it carries current status, the next
   actions, and the resume protocol. It is the only file with mutable session
   state. **It is generated** (`python3 scripts/gen-plan.py`, gated by
   `--check`): you never edit it. Your lane's state lives in
   [`docs/plan/status/<lane>.md`](docs/plan/status/README.md); project-wide
   sections are in [`docs/plan/global/`](docs/plan/global/README.md).
2. Work against the current roadmap phase and its exit criteria:
   [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md).
3. Before adding public operators, rewrites, encodings, backends, evidence
   artifacts, or logic fragments, check the foundational dependency DAG:
   [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md).
4. Decisions are not made silently in code. Check
   [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md)
   and [docs/research/09-decisions/](docs/research/09-decisions/README.md);
   close questions with ADRs (template in the decisions README). The ADR
   **index is generated** (`python3 scripts/gen-adr-index.py`): write the ADR
   file, including its optional `Index-summary:` / `Index-status:` front
   matter, and regenerate. Never append an index row by hand.
5. Before ending a session: update **your lane's** `docs/plan/status/<lane>.md`
   — its status block and any landed-changes rows — then run
   `python3 scripts/gen-plan.py` and commit both it and `PLAN.md`. Touch
   `docs/plan/global/` only for a genuinely project-wide change.

   These two files are generated because they were the repository's shared
   append points: `PLAN.md` was touched 67 times and the ADR index 60 times in
   24 hours by concurrent lanes on 2026-08-13/14, and four clobbering incidents
   lost real content in one day. The general rule: **per-lane state and
   per-lane identity belong in per-lane paths or per-process environment, never
   in one file or one config key every lane writes.**

## Commands

**These commands assume a gate-capable host.** Measured 2026-08-16, `lean` and
`just` existed on one fleet host of five and `cargo-deny` on none, so running
`just check` where `just` is absent silently degrades to the narrower
`check.sh`. The baseline, the provisioning script, and which gate needs which
toolchain are in
[docs/contributor-guide/fleet-hosts.md](docs/contributor-guide/fleet-hosts.md).

```sh
just check          # fmt + clippy + test + doc + foundational resources + docs link check (preferred)
just foundational-resources  # validates foundational atlas/example packs + generated dashboards
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

Local default toolchain may be nightly; CI runs stable plus an MSRV (1.88)
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
- `crates/axeyum-lean-kernel` — independent zero-dependency Rust Lean-core
  checker and reconstruction target.
- `crates/axeyum-lean-import` — separate fail-closed `lean4export` NDJSON wire
  reader; parsing and malformed-input handling stay outside the kernel TCB.
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
  ADR-0007; `axeyum-lean-import` is the exercised wire-format/checker boundary
  proposed in ADR-0345).
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
