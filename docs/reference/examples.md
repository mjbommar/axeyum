# Runnable Examples

This page inventories every Cargo example checked into the workspace. It keeps
three different things separate:

- **learning examples** are safe starting points and print to standard output;
- **artifact generators** intentionally create or refresh reports and require a
  reviewed output path or clean-tree check; and
- **maintainer diagnostics** are narrow measurement probes, not stable product
  interfaces.

An example being present under `examples/` means Cargo builds it under the
appropriate all-target gate. It does not make its arguments, output schema, or
performance a public compatibility promise. For library APIs, use
[Public API](public-api.md); for the supported SMT-LIB boundary, use
[SMT-LIB support](smtlib-support.md).

## Start with these

These commands have no external solver requirement and do not intentionally
write tracked files:

```sh
cargo run -p axeyum-solver --features full --example first_smtlib_query
cargo run -p axeyum-cas --example cas_tour
cargo run -p axeyum-cas --example certified_calculus
cargo run -p axeyum-bench --example curriculum_demo
```

| Example | Crate | What it demonstrates |
|---|---|---|
| [`first_smtlib_query`](../../crates/axeyum-solver/examples/first_smtlib_query.rs) | `axeyum-solver` | Parses one QF_BV script, obtains a typed model, and prints the wrapped 8-bit witness. Requires `--features full`. |
| [`geometry_portfolio`](../../crates/axeyum-solver/examples/geometry_portfolio.rs) | `axeyum-solver` | Compares the specialized LRA and incomplete NRA routes on the same small geometry goals. Requires `--features full`; timings are measurements, not API guarantees. |
| [`cas_tour`](../../crates/axeyum-cas/examples/cas_tour.rs) | `axeyum-cas` | Broad tour of exact and certified computer-algebra operations. |
| [`certified_calculus`](../../crates/axeyum-cas/examples/certified_calculus.rs) | `axeyum-cas` | Focused differentiate/integrate examples with explicit certification labels. |
| [`curriculum_demo`](../../crates/axeyum-bench/examples/curriculum_demo.rs) | `axeyum-bench` | Connects the concept DAG, rendered exercises, sound grading, checked QF_BV evidence, and curriculum coverage. |
| [`scenario_pipeline_report`](../../crates/axeyum-bench/examples/scenario_pipeline_report.rs) | `axeyum-bench` | Runs the self-checking scenario catalog through the BV pipeline and reports deterministic sizes plus informational timings. |
| [`scenario_scaling`](../../crates/axeyum-bench/examples/scenario_scaling.rs) | `axeyum-bench` | Sweeps a self-checking mixing workload to show AIG/CNF and solve-time scaling. |

Run the last three benchmark-oriented examples in release mode when the timing
numbers matter:

```sh
cargo run --release -p axeyum-solver --features full --example geometry_portfolio
cargo run --release -p axeyum-bench --example scenario_pipeline_report
cargo run --release -p axeyum-bench --example scenario_scaling
```

## Import and trust-boundary tools

| Example | Invocation after `--example <name> --` | Output and boundary |
|---|---|---|
| [`lean4export_import`](../../crates/axeyum-lean-import/examples/lean4export_import.rs) | `<export.ndjson\|->` | Imports one format-3.1 stream and prints an assurance-separated inventory. Admission does not authenticate the producer or imply complete Lean compatibility. |
| [`prelude_axiom_inventory`](../../crates/axeyum-lean-kernel/examples/prelude_axiom_inventory.rs) | no arguments | Prints the deterministic reconstruction-prelude axiom inventory as tab-separated, hex-delimited data. |
| [`proof_gap_shape_census`](../../crates/axeyum-smtlib/examples/proof_gap_shape_census.rs) | `<file.smt2>...` | Emits source-syntax and reachable parsed-IR censuses. This is diagnostic data, not a solver verdict. |
| [`probe_selected_evidence_lean`](../../crates/axeyum-bench/examples/probe_selected_evidence_lean.rs) | `<file.smt2>...` | Tests whether already-selected evidence reconstructs through an existing Lean route, avoiding query-only proof re-derivation. |

For example:

```sh
cargo run -p axeyum-lean-import --example lean4export_import -- export.ndjson
cargo run -p axeyum-lean-kernel --example prelude_axiom_inventory
cargo run -p axeyum-smtlib --example proof_gap_shape_census -- query.smt2
```

## Artifact generators

These examples can write JSON, Markdown, DIMACS, or committed consumer reports.
Use scratch output paths first. If a command intentionally refreshes a tracked
artifact, start from a clean tree and review the complete diff.

| Example | Invocation contract | Purpose / mutation boundary |
|---|---|---|
| [`audit_dominance`](../../crates/axeyum-bench/examples/audit_dominance.rs) | `<baseline.json> [timeout_ms] [limit] [out.json]` | Re-runs baseline-decided rows through evidence and Lean reconstruction. Omitting `out.json` prints the report. |
| [`cnf_core_bench`](../../crates/axeyum-bench/examples/cnf_core_bench.rs) | `<cnf-dir> <out.json> [repetitions] [kissat]` | Compares byte-identical DIMACS inputs across fresh SAT cores; the optional external solver includes process startup. |
| [`cnf_stream_bench`](../../crates/axeyum-bench/examples/cnf_stream_bench.rs) | `<profile.jsonl> <snapshot-dir> <out.json> [repetitions] [timeout_ms]` | Replays captured append-only CNF streams through persistent BatSat and Z3. Requires `--features z3` and a usable Z3 link. |
| [`cvc5_qfbv_timeout_sweep`](../../crates/axeyum-bench/examples/cvc5_qfbv_timeout_sweep.rs) | `<corpus-root> <manifest> <cvc5> <out.json> [repetitions] [timeouts_csv]` | Runs a hash-bound QF_BV manifest through fresh cvc5 processes. |
| [`cvc5_smt_stream_bench`](../../crates/axeyum-bench/examples/cvc5_smt_stream_bench.rs) | `<trace-dir> <cvc5> <out.json> [repetitions] [timeout_ms] [cold-reset\|retained-lcp]` | Replays an ordered, hash-bound SMT stream through one cvc5 process. |
| [`dump_dimacs`](../../crates/axeyum-bench/examples/dump_dimacs.rs) | `<file.smt2> <out.cnf>` | Applies the benchmark preprocessing/lowering path and writes DIMACS for an external SAT diagnostic. |
| [`measure_corpus`](../../crates/axeyum-bench/examples/measure_corpus.rs) | `<dir> [timeout_ms] [out.json]` | Head-to-head Axeyum/system-Z3 corpus measurement. Requires a `z3` executable; use release mode. |
| [`measure_graduated`](../../crates/axeyum-bench/examples/measure_graduated.rs) | `<dir> [timeout_ms] [out.json]` | Measures a construction-labeled graduated corpus against Axeyum and system Z3. Requires a `z3` executable; use release mode. |
| [`property_corpus_scoreboard`](../../crates/axeyum-property/examples/property_corpus_scoreboard.rs) | `<json\|markdown> [out]` | Regenerates or prints the property consumer scoreboard. Omit `out` for a non-mutating preview. |
| [`measure_evm`](../../crates/axeyum-evm/examples/measure_evm.rs) | no arguments | Regenerates the committed EVM consumer scoreboard and corpus. It is not a read-only tour. |
| [`measure_verify`](../../crates/axeyum-verify/examples/measure_verify.rs) | no arguments | Regenerates the committed Rust-verification scoreboard and corpus. It is not a read-only tour. |

The generic release-mode form is:

```sh
cargo run --release -p axeyum-bench --example <name> -- <arguments>
```

Do not retain a measurement merely because the command exited successfully.
Apply the [benchmark artifact contract](../contributor-guide/benchmark-artifacts.md):
bind the corpus and solver revision, keep limits/configuration, check verdict
agreement and replay, and separate diagnostics from credited results.

## Maintainer diagnostics

The remaining examples answer one narrow implementation question. They may
encode frozen paths, schemas, budgets, or experiment assumptions and should not
be presented as general solver CLIs.

| Example | Arguments | Question answered |
|---|---|---|
| [`clause_estimate_attribution`](../../crates/axeyum-bench/examples/clause_estimate_attribution.rs) | `<frozen-target.smt2>...` | Which operators and demanded multiplier bits account for the frozen QF_NIA pre-lowering clause estimate? |
| [`diagnose_evidence`](../../crates/axeyum-bench/examples/diagnose_evidence.rs) | `<file.smt2> [timeout_ms]` | Did evidence production spend time in decision search or post-decision certificate attempts? |
| [`explain_corpus`](../../crates/axeyum-bench/examples/explain_corpus.rs) | `<dir> [timeout_ms] [--json]` or `--list <file> [timeout_ms] [--json]` | Which route decided or declined each file, with persistable route traces in JSON mode? |
| [`pbls_probe`](../../crates/axeyum-bench/examples/pbls_probe.rs) | `<file.smt2> [timeout_s]` | Can pure-Rust word-level local search find a witness for a SAT-search-bound QF_BV case? It does not prove UNSAT. |
| [`preprocess_timing`](../../crates/axeyum-bench/examples/preprocess_timing.rs) | `<file.smt2>` | Which word-level preprocessing pass dominates one large QF_BV input? |
| [`qf_abv_probe`](../../crates/axeyum-bench/examples/qf_abv_probe.rs) | `<file.smt2>...` | How much does eager array elimination grow the reachable DAG? |
| [`replay_refine_profile`](../../crates/axeyum-bench/examples/replay_refine_profile.rs) | `<file.smt2>` | What operator mix and AIG/CNF counters result from one replay-refined BV plan? Environment variables select diagnostic policies. |
| [`smtcomp_cli`](../../crates/axeyum-bench/examples/smtcomp_cli.rs) | `<benchmark.smt2> [--timeout-ms N]` | Exercises the competition-style single-query wrapper. It is an example harness, not the finished interactive SMT-LIB product surface. |
| [`uf_pair_profile`](../../crates/axeyum-bench/examples/uf_pair_profile.rs) | `<file.smt2> [sample_limit]` | What same-function application-pair shapes would a lazy Ackermann pre-seed see? |
| [`uf_unknown_probe`](../../crates/axeyum-bench/examples/uf_unknown_probe.rs) | `<file.smt2> [timeout_ms]` | What full typed `UnknownReason` is hidden by the competition wrapper's one-word output? |
| [`uflia_online_probe`](../../crates/axeyum-bench/examples/uflia_online_probe.rs) | `<file.smt2> [timeout_ms]` | How does the online EUF+LIA combination route classify one query? |
| [`xor_cdcl_probe`](../../crates/axeyum-bench/examples/xor_cdcl_probe.rs) | `<file.cnf>` | Does the in-tree CDCL(XOR) core move a small-CNF SAT-search case? |

## Inventory and validation

The authoritative target list comes from Cargo metadata, including required
features:

```sh
cargo metadata --no-deps --format-version 1 |
  jq -r '.packages[] as $p | $p.targets[] |
    select(.kind | index("example")) |
    [$p.name, .name, ((.["required-features"] // []) | join(","))] | @tsv' |
  sort
```

`cargo test --workspace --all-targets --all-features --no-run` compiles the
complete target population without executing artifact-producing `main`
functions. The repository's full pre-merge and hosted CI gates include
all-target compilation; a focused documentation edit should not rerun every
measurement example.
