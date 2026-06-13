# Axeyum

A Rust-first automated reasoning stack: typed term IR, rewriting, query
planning, solver backends (native SMT oracles plus a growing pure Rust
bit-blast-to-SAT path), and checkable evidence — models verified by
evaluation, unsat claims backed by proof artifacts or independent oracles.

The north star is a complete framework for general reasoning, logic, and
proving; the decidable finite-domain core being built first is its
foundation layer
(see [north-star](docs/research/00-orientation/north-star.md)).

**Status: Phase 5 first pure-Rust backend slice.** M0, Phase 1, and the core
Phase 2 oracle path are complete: scalar QF_BV IR/evaluator, Z3 oracle
backend, SMT-LIB reader/writer, resource telemetry, micro-corpus benchmark
harness, and a recorded public QF_BV baseline. Phase 3 now has
query/rewrite/evidence contracts, the first denotation-preserving
canonicalizer, structural cache keys, conservative slicing, rewrite
measurement, and an exit audit. Phase 4 has an accepted bit-order/lowering
entry contract, shared LSB-first value-to-bits helpers, an AIG graph/evaluator
crate with ASCII AIGER debug export, and term-to-AIG lowering for constants,
symbols, Boolean connectives, BV bitwise operators, equality, `ite`, `bvcomp`,
concat/extract, and zero/sign extension, `bvneg`, `bvadd`, `bvsub`, and
unsigned/signed comparisons, `bvshl`, `bvlshr`, `bvashr`, and constant rotates,
with explicit term-bit and symbol-input maps. The first CNF layer adds simple
Tseitin encoding from AIG, DIMACS I/O, CNF evaluation, and
CNF-variable-to-AIG lift maps. The first SAT adapter path uses `rustsat-batsat`
through RustSAT, solves CNF through an Axeyum SAT trait/result surface, and
replay-checks satisfying assignments through CNF variables, AIG node values,
reconstructed symbol models, and the original evaluator. UNSAT through this path
is explicitly unchecked until proof output and proof checking land. Phase 5 now
has the first `SatBvBackend`: a native-free `SolverBackend` implementation for
the supported QF_BV subset that composes query terms, AIG lowering, Tseitin CNF,
BatSat, model reconstruction, and evaluator replay. `axeyum-bench` can run this
backend with `--backend sat-bv` and emits artifact version 7 records with
bit-blast/CNF layer stats, node and CNF admission budgets, submitted query-plan
mode, replay policy, replay-refinement limits, and optional Z3 oracle
comparison; artifact version 8 also records the harness `jobs` setting for
parallel corpus diagnostics, artifact version 9 records replay-refinement
batch size for exact-target diagnostic runs, artifact version 10 records
adaptive batch policy and backoff counts, and artifact version 11 records
refinement selection policy. Artifact version 12 records the bounded
plan-aware selection option and current root-direct assertion CNF encoder
behavior. The first public `sat-bv` vs Z3
baseline is recorded for the admitted supported slice: 1 public `sat` decision
agrees with Z3, 112 larger instances are structured node-budget `unknown`s,
and there are no unsupported/error/model-replay/oracle-disagreement alarms. A
guarded rerun raises the node budget only behind CNF variable/clause caps; it
keeps the same one public decision and classifies the next admitted candidate
as `EncodingBudget`. Replay-refinement diagnostics prove sliced query plans can
be iteratively replayed without weakening the full-query model contract. The
relaxed-admission public artifact now reaches 2 public `sat` decisions with Z3
agreement and no soundness alarms. The exact-target relaxed diagnostic keeps
the same 2 decisions, removes node-budget unknowns from that profile, and
leaves all 111 remaining unknowns as `EncodingBudget`; root-direct assertion
CNF and an 8.5k variable sweep still leave the supported public slice at 2
decisions, so encoding and SAT cost, not admission bookkeeping, remain the next
Phase 5 target.

## Start Here

- [PLAN.md](PLAN.md) — master plan, current status, and next actions. The
  single entry point for resuming work.
- [docs/research/](docs/research/README.md) — the research foundation:
  notes covering foundations, architecture, data structures, algorithms,
  verification strategy, and planning.
- [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md) —
  the logic/math dependency DAG from semantics through evidence.
- [docs/research/08-planning/phase3-exit-audit.md](docs/research/08-planning/phase3-exit-audit.md) —
  the Phase 3 rewrite/query-planning exit evidence and Phase 4 handoff.
- [docs/research/08-planning/phase4-exit-audit.md](docs/research/08-planning/phase4-exit-audit.md) —
  the Phase 4 circuit/CNF/SAT-adapter exit evidence and Phase 5 handoff.
- [docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md](docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md) —
  the Phase 4 bit-order, AIG, CNF, and lift-map entry contract.
- [docs/research/09-decisions/adr-0007-first-pure-rust-sat-adapter.md](docs/research/09-decisions/adr-0007-first-pure-rust-sat-adapter.md) —
  the first pure-Rust SAT adapter decision.
- [docs/research/09-decisions/](docs/research/09-decisions/README.md) —
  decision records (ADRs).
- [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json) —
  current public QF_BV baseline artifact.
- [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json) —
  Phase 3 rewrite-measurement artifact.
- [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json) —
  Phase 5 public `sat-bv` vs Z3 supported-slice artifact.
- [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json) —
  Phase 5 guarded-admission artifact with explicit CNF budgets.
- [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json) —
  Phase 5 replay-refinement diagnostic artifact.
- [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json) —
  Phase 5 exact-target relaxed replay-refinement diagnostic artifact.

## Workspace

| Crate | Purpose |
|---|---|
| [`axeyum-ir`](crates/axeyum-ir) | Sorts, terms, interning, ground evaluation, LSB-first value/bit conversion. |
| [`axeyum-aig`](crates/axeyum-aig) | AIG circuit graph with deterministic structural hashing, evaluation, and ASCII AIGER debug export. |
| [`axeyum-bv`](crates/axeyum-bv) | Term-to-AIG bit lowering with explicit term-bit and symbol-input maps. |
| [`axeyum-cnf`](crates/axeyum-cnf) | Tseitin CNF encoding from AIG, DIMACS I/O, CNF evaluation, BatSat-backed solving, and assignment replay. |
| [`axeyum-query`](crates/axeyum-query) | Query object, structural cache keys, conservative slicing, replay checks. |
| [`axeyum-rewrite`](crates/axeyum-rewrite) | Rewrite manifest contracts and the first denotation-preserving canonicalizer. |
| [`axeyum-scenarios`](crates/axeyum-scenarios) | Self-checking, oracle-free consumer workloads (SAT by concrete execution, UNSAT by bounded-verified identities) for testing and optimization. |
| [`axeyum-bench`](crates/axeyum-bench) | Corpus benchmark harness with PAR-2 scoring, backend selection, and JSON artifacts. |
| [`axeyum-smtlib`](crates/axeyum-smtlib) | SMT-LIB 2 reader/writer: benchmark ingestion, sharing-preserving export. |
| [`axeyum-solver`](crates/axeyum-solver) | Backend trait, results, models, capabilities; default pure Rust SAT-backed BV backend plus native backends behind feature flags. |

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
