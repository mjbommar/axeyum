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

## Working Stance — we ship toward Z3 + Lean parity

This is an ambitious, **achievable** build, and the job is to *complete it* — one
verifiable increment at a time, relentlessly. Adopt a builder's mentality:

- **There is always a next concrete task.** PLAN.md and `docs/plan/` decompose the
  whole goal into tracks → phases → tasks with paths, sizing, and exit criteria.
  When you finish one, pick the next and go. PLAN.md's standing rule is literal:
  **"We do not stop and we do not hand-wave; we advance the next task and record it."**
- **Big tasks get broken down, not deferred.** A "keystone" is not a reason to wait
  for "a future session" or "fresh context" — it's a signal to slice it into sound,
  bounded, testable pieces and land them one by one. Each slice that compiles, passes
  the gates, and adds real capability is progress. Ship it, then take the next slice.
- **Soundness is a method, not an excuse.** We never ship a wrong sat/unsat — and we
  achieve that by *conservative slicing + soundness-negative tests + independent
  re-validation + self-checking evidence*, NOT by avoiding hard work. "This is
  soundness-critical" means "test it harder," not "punt it."
- **Don't whine, don't stall, don't write essays about why something is hard.** Spend
  the words on the diff. Launch sub-agents for parallel/large work; review and
  re-validate what they produce; commit; continue.
- **Measure what matters.** Z3 parity is a *measured* claim — keep the head-to-head
  honest (Track 1, the public corpora). Lean parity is *every unsat/valid carries a
  machine-checkable proof*. Drive both fronts; record the pulse in STATUS.md.

Keep STATUS.md framed as an **active work queue**, never as an "exhausted frontier."
If you catch yourself concluding the work is done for now, you're wrong — re-read
PLAN.md and pick the next task.

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
just check          # fmt + clippy + test + doc + foundational resources + docs link check (preferred)
just foundational-resources  # validates foundational atlas/example packs + generated dashboards
./scripts/check.sh  # same aggregate gate without `just` (fresh-machine fallback)
just bench-micro    # committed SMT-LIB micro corpus through axeyum-bench
just bench-public-qfbv-sat-bv-compare  # Phase 5 public sat-bv vs Z3 slice
just bench-public-qfbv-sat-bv-guarded  # Phase 5 node/CNF guarded run
just bench-public-qfbv-sat-bv-replay-refine  # replay-checked query refinement
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
# PRE-MERGE GATE for any string-route change: the oracle-free :status corpus
# sweep (~6s). CI's copy of this caught a vacuous-sat harness hole two oracle
# fuzzes missed (f5b00c72) — after the SHA was already public. Related rule:
# string fuzz GENERATORS must cover the full SMT-LIB literal grammar,
# including \u{…}/\uXXXX escapes and >0xFF code points — every generator
# omitted escapes and a wrong-verdict class (ba0d9149) hid for weeks.
cargo test -p axeyum-solver --test corpus_regression
# PRE-MERGE GATE for any solver/decider/dispatch change: the capability
# ratchets (~60s when healthy). A 17-point nia_unsat frontier regression once
# shipped and needed an 829-commit bisect because only full sweeps ran this.
cargo test -p axeyum-solver --test progress_frontier
cargo doc --workspace --all-features --no-deps    # RUSTDOCFLAGS="-D warnings" in CI
cargo deny check                                  # needs cargo-deny installed
./scripts/check-links.sh                          # docs relative-link check (CI job)
# WebAssembly is a supported target (ADR-0017); the default library stack builds
# for browser and WASI. Native builds are unaffected (clock shim is wasm-only).
cargo build --target wasm32-unknown-unknown -p axeyum-solver
```

Local default toolchain may be nightly; CI runs stable plus an MSRV (1.88 —
let-chains are used workspace-wide) check. Edition 2024, resolver 3.

## Layout

- `crates/axeyum-ir` — sorts, terms, arena/interning, ground evaluator,
  LSB-first value/bit conversion helpers.
- `crates/axeyum-aig` — AIG circuit graph with deterministic structural
  hashing, evaluation, and ASCII AIGER debug export.
- `crates/axeyum-bv` — term-to-AIG bit lowering with explicit term-bit and
  symbol-input maps for the full scalar QF_BV operator set (bitwise, arithmetic
  incl. mul and signed/unsigned div/rem, shifts, comparisons, structural ops);
  one-shot `lower_terms` plus persistent `IncrementalLowering` (ADR-0009 st.2).
- `crates/axeyum-cnf` — simple Tseitin encoding from AIG, DIMACS I/O, CNF
  evaluation, BatSat-backed solving, CNF-variable-to-AIG replay maps, a warm
  `IncrementalSat` adapter (monotone clauses + native assumptions),
  `IncrementalCnf` (per-node Tseitin over the warm solver, ADR-0009), an
  independent DRAT UNSAT proof checker `check_drat` (RUP+RAT, ADR-0011), and a
  proof-producing CDCL SAT core `solve_with_drat_proof` (1-UIP conflict
  analysis + two-watched-literal propagation, emits DRAT, ADR-0012).
- `crates/axeyum-fp` — floating-point (IEEE 754) bit-vector formula builders
  (classification, comparison, abs/neg/min/max, arithmetic incl. rem/fma/sub,
  and int/real conversions) over the typed IR; the GPU/ML precisions are free
  from the generic `(exp_bits, sig_bits)` design (ADR-0023). Extracted from
  `axeyum-solver` so the SMT-LIB front-end can share it (depends only on
  `axeyum-ir`).
- `crates/axeyum-query` — query object: assertions, assumptions, scopes,
  stable labels.
- `crates/axeyum-rewrite` — rewrite manifest contracts, the first
  denotation-preserving canonicalizer, and `eliminate_arrays` (QF_ABV →
  QF_BV by read-over-write + Ackermann, ADR-0010).
- `crates/axeyum-solver` — backend trait, results, models, capabilities;
  default pure Rust SAT-backed BV backend (one-shot `SatBvBackend`, plus the
  warm `IncrementalBvSolver` with push/pop/assume, ADR-0009 st.2); the high-level
  `Solver` façade; `check_with_array_elimination` for QF_ABV (ADR-0010); native
  backends behind feature flags (`z3` is the oracle).
- `crates/axeyum-smtlib` — SMT-LIB benchmark-slice parser and
  sharing-preserving writer.
- `crates/axeyum-bench` — corpus benchmark harness with backend selection,
  PAR-2 scoring, model replay, and JSON artifacts; also the
  `scenario_pipeline_report` and `scenario_scaling` examples.
- `crates/axeyum-scenarios` — self-checking, oracle-free consumer workloads
  (SAT by concrete execution, UNSAT by bounded-verified identities) for testing
  and optimization (ADR-0008).
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
  ADR-0007; `axeyum-scenarios` is the self-checking consumer-workload boundary
  accepted in ADR-0008).
- The pure Rust stack including a custom CDCL SAT core is the product; the
  Z3 oracle is bootstrap scaffolding with a planned demotion path
  (ADR-0002). Never expand reliance on linked solvers beyond
  backend/differential-oracle/CI-cross-check roles without a new ADR.

## Multi-agent hygiene (multiple agents share this checkout)

- **Pathspec-only commits, always:** `git add <files>` then
  `git commit -m … -- <files>`. A bare `git commit` sweeps OTHER agents'
  staged files from the shared index (it has happened; recovery cost real
  work). Verify every commit with `git show --stat`.
- **Never** `git stash`, `git checkout`/`restore` on files you did not
  modify, or any history rewrite — another lane's uncommitted WIP lives in
  this tree. Treat dirty files you don't own as off-limits.
- Format single files with `rustfmt --edition 2024 <file>` — never
  `cargo fmt`/`cargo fmt -p` (workspace-wide; clobbers other lanes' WIP).
- One writer per worktree/area at a time; long-running background gates are
  run FOREGROUND by the agent that owns them (waiting on completion
  notifications has stalled agents repeatedly).
- Full details: [docs/contributor-guide/multi-agent-worktrees.md](docs/contributor-guide/multi-agent-worktrees.md).

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
