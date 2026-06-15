# Axeyum

A Rust-first automated reasoning stack: typed term IR, rewriting, query
planning, solver backends (native SMT oracles plus a growing pure Rust
bit-blast-to-SAT path), and checkable evidence — models verified by
evaluation, unsat claims backed by proof artifacts or independent oracles.

The north star is a **usable, ideally pareto-dominant system for constrained
program optimization and software verification**, reached in three destinations:
(1) the decidable + arithmetic **foundation** with checkable evidence — where the
project is today; (2) a **complete solver replacement** (Z3/cvc5 class), gated on
performance on real corpora, not theory breadth; (3) **Lean / angr as
first-class functionality** — binary frontend + symbolic execution/emulation and
kernel-checkable proving + proof-assistant interop
(see [north-star](docs/research/00-orientation/north-star.md)).

**Honest status:** destination (1) is built and broad. It is **not yet** a
performance-parity solver replacement (the pure-Rust path decides a slice of real
public QF_BV — performance is the open gate), **not yet** full SMT-LIB breadth
(unbounded strings, quantified arithmetic), and **not yet** Lean parity
(reductions are trusted, not yet certified into exportable proof terms). The
followable roadmap from here to 100% Z3 + Lean parity is in [PLAN.md](PLAN.md).

## What it does today

Pure Rust, no C/C++ in the default build, buildable for **WebAssembly**. The
authoritative, golden-tested inventory (capability × assurance × evidence) is the
[capability matrix](docs/research/08-planning/capability-matrix.md).

**Theories, each end to end** (typed IR → evaluator → decision procedure →
solver entry → SMT-LIB I/O):

- **QF_BV** — full scalar operator set, widths to 2¹⁶; `unsat` carries a
  DRAT-checked proof.
- **Arrays** (QF_ABV, eager elimination), **uninterpreted functions** (QF_UF,
  Ackermann), and their composition **QF_AUFBV**.
- **Linear arithmetic** — `QF_LRA` (exact-rational simplex, Farkas-certified
  `unsat`), `QF_LIA` (bit-blast + branch-and-bound simplex), mixed `QF_LIRA`
  (MILP); Boolean combinations via lazy SMT / DPLL(T).
- **Floating point** (QF_FP) — IEEE 754 arithmetic (add/sub/mul/div/fma/sqrt/
  rem/roundToIntegral/conversions) for **F16/F32/F64/F128** and ML formats,
  differentially validated against native `f32`/`f64` and `rustc_apfloat`.
- **Datatypes** (algebraic, recursive), **nonlinear** arithmetic (QF_NRA/NIA,
  sound-incomplete), **quantifiers** (finite-domain complete + E-matching/MBQI
  instantiation), and **bounded strings** (QF_S, BV-lowered).

**Symbolic execution & reachability** are first-class on the warm incremental
engine (`IncrementalBvSolver`): `push`/`pop`/`assume`, **assumption-core path
pruning** (`check_assuming_core`), **all-SAT reachable-state enumeration**
(`block_model`), and **symbolic memory** (`check_with_memory`). On top of these,
**bounded model checking** (`bounded_model_check` over a `TransitionSystem`,
and `bounded_model_check_with_memory` for array/symbolic-memory state) answers
reachability queries with a replay-checked counterexample trace, and
**k-induction** (`prove_safety_k_induction`) lifts that to *unbounded* safety
proofs — `Safe`, a counterexample, or an honest `Inconclusive` (never a wrong
`Safe`) — and `certify_safety_k_induction` returns a `Safe` verdict with a
`drat-trim`-checkable DRAT certificate for **each** induction obligation.

Everything routes through a few consumer entry points (`axeyum-solver`):

| Call | Purpose |
|---|---|
| `solve` / `solve_smtlib` | decide any supported query (terms or SMT-LIB 2 text) |
| `prove` | prove a goal by a **checkable refutation** of its negation |
| `produce_evidence` | decide *and* package a self-checking certificate |
| `export_qf_{bv,abv,uf,aufbv,lia}_unsat_proof`, `export_datatype_unsat_proof` | emit a `drat-trim`-checkable DIMACS+DRAT certificate |
| `IncrementalBvSolver` | warm push/pop/assume + path-pruning core + all-SAT + symbolic memory |
| `unsat_core` / `Evidence::check` | minimal core; independently re-validate any result |

**Trusted small checking** holds for every result: a `sat` model is replayed
through the ground evaluator; `unsat` over the bit-vector-reducible core
(QF_BV/ABV/UF/AUFBV/bounded-LIA/datatypes) carries an externally re-checkable
DRAT proof; `QF_LRA` `unsat` carries a Farkas refutation. Search is untrusted;
the checkers are small and independent.

**Status.** A broad, evidence-backed foundation (destination 1). The remaining
work — performance parity on real corpora, the rest of the SMT-LIB breadth, and
the Lean proof-export ladder — is the followable roadmap in [PLAN.md](PLAN.md).
30 ADRs (all accepted) record the design.

## Start Here

- [PLAN.md](PLAN.md) — master plan, current status, and the followable roadmap
  to 100% Z3 + Lean parity. The single entry point for resuming work.
- [docs/research/08-planning/capability-matrix.md](docs/research/08-planning/capability-matrix.md) —
  the authoritative, golden-tested inventory: capability × assurance × evidence.
- [docs/research/](docs/research/README.md) — the research foundation:
  notes covering foundations, architecture, data structures, algorithms,
  verification strategy, and planning.
- [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md) —
  the logic/math dependency DAG from semantics through evidence.
- [docs/research/09-decisions/](docs/research/09-decisions/README.md) —
  decision records (30 accepted ADRs).
- [bench-results/baselines/](bench-results/baselines/) —
  recorded benchmark baselines (public QF_BV `sat-bv` vs Z3 slices, rewrite
  measurement, replay-refinement diagnostics).

## Workspace

| Crate | Purpose |
|---|---|
| [`axeyum-ir`](crates/axeyum-ir) | Sorts, terms, interning, ground evaluation, LSB-first value/bit conversion. |
| [`axeyum-aig`](crates/axeyum-aig) | AIG circuit graph with deterministic structural hashing, evaluation, and ASCII AIGER debug export. |
| [`axeyum-bv`](crates/axeyum-bv) | Term-to-AIG bit lowering with explicit term-bit and symbol-input maps. |
| [`axeyum-cnf`](crates/axeyum-cnf) | Tseitin CNF encoding from AIG, DIMACS I/O, CNF evaluation, BatSat-backed solving, assignment replay, and a proof-producing CDCL core with an in-tree DRAT checker. |
| [`axeyum-fp`](crates/axeyum-fp) | IEEE 754 floating-point formula builders (F16–F128 + ML formats) over the typed IR. |
| [`axeyum-query`](crates/axeyum-query) | Query object, structural cache keys, conservative slicing, replay checks. |
| [`axeyum-rewrite`](crates/axeyum-rewrite) | Rewrite manifest contracts, the denotation-preserving canonicalizer, and array elimination (QF_ABV → QF_BV). |
| [`axeyum-scenarios`](crates/axeyum-scenarios) | Self-checking, oracle-free consumer workloads (SAT by concrete execution, UNSAT by bounded-verified identities) for testing and optimization. |
| [`axeyum-bench`](crates/axeyum-bench) | Corpus benchmark harness with PAR-2 scoring, backend selection, and JSON artifacts. |
| [`axeyum-smtlib`](crates/axeyum-smtlib) | SMT-LIB 2 reader/writer: benchmark ingestion, sharing-preserving export. |
| [`axeyum-solver`](crates/axeyum-solver) | Backend trait, results, models, capability ledger; high-level `solve`/`prove`/`produce_evidence`; warm incremental engine with symbolic-execution primitives; DRAT proof exporters; native backends behind feature flags. |

The pure Rust default build has no C or C++ dependency; native solver
backends (Z3 first) are optional features.

## Development

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
cargo run -p axeyum-bench -- corpus/micro --backend sat-bv --timeout-ms 1000 --out /tmp/axeyum-bench-micro-sat-bv.json
cargo run -p axeyum-bench --features z3 -- corpus/micro --backend z3 --timeout-ms 1000 --out /tmp/axeyum-bench-micro-z3.json
cargo run -p axeyum-bench --example scenario_pipeline_report   # per-stage pipeline report over the scenario corpus
cargo run -p axeyum-bench --example scenario_scaling           # scaling profile of the sat-bv pipeline
just bench-public-qfbv-baseline   # requires scripts/fetch-corpus.sh qf_bv first
just bench-public-qfbv-rewrite    # same public slice, with --rewrite default
just bench-public-qfbv-sat-bv-compare
just bench-public-qfbv-sat-bv-guarded
just bench-public-qfbv-sat-bv-replay-refine
just bench-public-qfbv-sat-bv-replay-refine-exact
just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive
just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-cnf8k5
just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest
just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest-cnf8k5
cargo deny check   # requires cargo-deny
```

Reference solver/checker sources can be cloned locally for study with
[`scripts/fetch-references.sh`](scripts/fetch-references.sh) (see
[references/README.md](references/README.md)).

## License

Dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at
your option. Contributions are accepted under the same terms.
