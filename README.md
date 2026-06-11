# Axeyum

A Rust-first automated reasoning stack: typed term IR, rewriting, query
planning, solver backends (native SMT oracles plus a growing pure Rust
bit-blast-to-SAT path), and checkable evidence — models verified by
evaluation, unsat claims backed by proof artifacts or independent oracles.

The north star is a complete framework for general reasoning, logic, and
proving; the decidable finite-domain core being built first is its
foundation layer
(see [north-star](docs/research/00-orientation/north-star.md)).

**Status: Phase 2 hardening.** M0 and Phase 1 are complete; the current stack
has the scalar QF_BV IR/evaluator, Z3 oracle backend, SMT-LIB reader/writer,
resource telemetry, and a micro-corpus benchmark harness. Phase 2 public-corpus
baselines and later incrementality conformance remain active work.

## Start Here

- [PLAN.md](PLAN.md) — master plan, current status, and next actions. The
  single entry point for resuming work.
- [docs/research/](docs/research/README.md) — the research foundation: 35
  notes covering foundations, architecture, data structures, algorithms,
  verification strategy, and planning.
- [docs/research/09-decisions/](docs/research/09-decisions/README.md) —
  decision records (ADRs).

## Workspace

| Crate | Purpose |
|---|---|
| [`axeyum-ir`](crates/axeyum-ir) | Sorts, terms, interning, ground evaluation. |
| [`axeyum-bench`](crates/axeyum-bench) | Corpus benchmark harness with PAR-2 scoring and JSON artifacts. |
| [`axeyum-smtlib`](crates/axeyum-smtlib) | SMT-LIB 2 reader/writer: benchmark ingestion, sharing-preserving export. |
| [`axeyum-solver`](crates/axeyum-solver) | Backend trait, results, models, capabilities; native backends behind feature flags. |

The pure Rust default build has no C or C++ dependency; native solver
backends (Z3 first) are optional features.

## Development

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
cargo run -p axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json
cargo deny check   # requires cargo-deny
```

Reference solver/checker sources can be cloned locally for study with
[`scripts/fetch-references.sh`](scripts/fetch-references.sh) (see
[references/README.md](references/README.md)).

## License

Dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at
your option. Contributions are accepted under the same terms.
