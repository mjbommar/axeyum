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
| [`prelude_axiom_inventory`](../../crates/axeyum-lean-kernel/examples/prelude_axiom_inventory.rs) | no arguments | Prints the deterministic reconstruction-prelude axiom inventory as tab-separated, hex-delimited data. Covers the `real`, `integer` and `string` preludes **only** — it never builds `nat` or `logic`, so zero rows for those means "not enumerated", not "axiom-free". |
| [`probe_add_structure`](../../crates/axeyum-lean-kernel/examples/probe_add_structure.rs) | no arguments | Dumps the structural `Declaration::Definition` value of `Nat.add` beside its rendered text. Built to separate a *printer* defect from a *kernel defeq divergence* when real Lean rejected an exported module — read the structure, never the printed text, when the printer is the thing under suspicion. |
| [`nat_axiom_inventory`](../../crates/axeyum-lean-kernel/examples/nat_axiom_inventory.rs) | no arguments | The same inventory for `nat` and `logic`, and over the FULL trusted surface (`Axiom`, `Opaque`, `Quotient`) rather than `Axiom` alone. Per-prelude counts go to stderr because an empty stdout is the expected result for an axiom-free prelude. |
| [`nat_theorem_inventory`](../../crates/axeyum-lean-kernel/examples/nat_theorem_inventory.rs) | `[name-substring]` | Every theorem the Nat prelude admits, with its canonical `render_lean` type — the paste-into-a-fact form. Declarations go through a helper taking an interned `NameId`, so this is the only way to read the inventory without building the environment. |
| [`theorem_axiom_footprint`](../../crates/axeyum-lean-kernel/examples/theorem_axiom_footprint.rs) | `[name-substring]` | Per-declaration axiom footprints (`Kernel::axiom_footprint`) for the `nat`, `integer` and `real` preludes — this kernel's `#print axioms`. Reports axioms alongside theorems, because `integer` and `real` declare no substantive theorems. |
| [`reconstruct_lean_certificate`](../../crates/axeyum-solver/examples/reconstruct_lean_certificate.rs) | `<file.cnf>` | DIMACS → DRAT → LRAT → Alethe → compact resolution reconstruction, emitting an externally checkable Lean certificate of a refutation. |
| [`reconstruct_ceiling_probe`](../../crates/axeyum-solver/examples/reconstruct_ceiling_probe.rs) | `<file.cnf>` | Characterises the ceiling of inlined resolution reconstruction on one instance. A measurement of where the route stops, not a verdict. |
| [`reconstruct_differential_probe`](../../crates/axeyum-solver/examples/reconstruct_differential_probe.rs) | `<file.cnf>` | Runs one instance through both inlined and compact clausal reconstruction and reports the difference. |
| [`kernel_equivalence`](../../crates/axeyum-fp/examples/kernel_equivalence.rs) | `[claim-name]` | Decides floating-point kernel-equivalence claims two independent ways — axeyum's SMT front door and an exhaustive `rustc_apfloat` enumeration sharing no code with the bit-blaster, CNF encoder or SAT core. Exhaustive at fp8/binary16 and (for binary32) 2^32 in ~51 s; ternary claims are already at the wall at 8 bits. |
| [`emit_telescoping_certificates`](../../crates/axeyum-cas/examples/emit_telescoping_certificates.rs) | no arguments | Writes `artifacts/cas-certificates/*.json` — Zeilberger certificates, emitted only through the checker so an unverifiable one cannot be published. |
| [`emit_geometry_certificates`](../../crates/axeyum-cas/examples/emit_geometry_certificates.rs) | no arguments | Writes `artifacts/geometry-certificates/*.json` — Nullstellensatz cofactor certificates with their non-degeneracy conditions and degenerate counterexamples. |
| [`telescoping_search_cost`](../../crates/axeyum-cas/examples/telescoping_search_cost.rs) | no arguments | Search-versus-check cost per identity. Reproduces the derived-degree-bound speedup (Chu-Vandermonde 18.5 s to 48.9 ms) and shows which sums still decline. |
| [`geometry_probe`](../../crates/axeyum-cas/examples/geometry_probe.rs) | `[budget-scale] [theorem-name]` | Per-condition-subset cost of a geometry certification, tracked and untracked, including the frontier decline — `euler-line` is unproved rather than unchecked, and this is how you see where it stops. `AXEYUM_MONOMIAL_ORDER=grevlex` selects the order. |
| [`geometry_order_audit`](../../crates/axeyum-cas/examples/geometry_order_audit.rs) | `[theorem-name]...` | Runs **every** non-degeneracy condition subset under both monomial orders, then compares the two certificates byte for byte. Answers the only question that makes changing the default order dangerous: whether a faster order lands a certificate on a *different* condition set, since those conditions are hypotheses in the facts' `formal.statement`. Also reports whether every subset was *decided*, which is what makes a reported condition set minimal absolutely rather than relative to the budget. Minutes, not seconds — `lex` pays the full cost of the theorems it cannot reach. |
| [`geometry_obstruction`](../../crates/axeyum-cas/examples/geometry_obstruction.rs) | `<theorem-name> [max-pairs]` | Why a reduction does not return, as a growth curve rather than a duration. Runs a ladder of S-pair ceilings and reports pairs processed and still queued, pairs that reduced to zero, pairs the product criterion would skip, basis size and widest intermediate polynomial. Use a theorem that *finishes* as the control — the numbers only mean something in comparison. |
| [`int_theorem_inventory`](../../crates/axeyum-lean-kernel/examples/int_theorem_inventory.rs) | `[name-substring]` | Every theorem the Int prelude admits with its canonical type — the Int counterpart of `nat_theorem_inventory`, and how you check which of the original 34 integer axioms are now derived. |
| [`infeasibility_iis`](../../crates/axeyum-solver/examples/infeasibility_iis.rs) | `<instance.smt2> [--expect-core N]` | Extracts an unsat core and MEASURES irreducibility by re-solving every leave-one-out subset, replaying each returned model through the IR evaluator. `unknown` is treated as failure, never as a pass. |
| [`infeasibility_farkas_lean`](../../crates/axeyum-solver/examples/infeasibility_farkas_lean.rs) | `<instance.smt2>` | Takes an LRA core to a Farkas certificate and on into the Lean kernel. Note `prove_unsat_to_lean_module` is NOT the route: it emits a structural shim containing no arithmetic. |
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
| [`recertify_rado`](../../crates/axeyum-search/examples/recertify_rado.rs) | `<claim-id> [artifact-root]` | Rechecks one committed Rado claim from its hash-bound witness or refutation artifact; it does not discover or strengthen claims. |
| [`sorting_network`](../../crates/axeyum-cnf/examples/sorting_network.rs) | `--n N --size K [--sym none\|first\|commute\|full\|max] [--drat] [--model]`, or `--sweep`, `--verify`, `--dimacs PATH`, `--cubes DIR [--depth D] [--jobs J] [--cube-sym none\|full\|subsume] [--keep-proofs]` | Decides `S(n)`, the optimal sorting-network size, as sat/unsat — no optimizer and no MaxSAT. Writes files only under `--dimacs` (one CNF) and `--cubes`, which streams one DRAT per branch and **deletes each after the backward checker accepts it** unless `--keep-proofs` is given (at `n = 7` a single branch's certificate reaches a gigabyte). `--verify` re-derives the committed `F:sorting-network-optimal-size-n{3,4,5,6}` facts; its `n = 6` leg is the monolithic 20-minute route, so prefer `--cubes` for a quick recheck. `--sweep` is the negative control against the published `S(n)`. Every `--sym`/`--cube-sym` setting weaker than the default must give the same verdict — that is the control against a wrong UNSAT. |

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
| [`drat_memory_probe`](../../crates/axeyum-cnf/examples/drat_memory_probe.rs) | `<cnf> <proof>` | What is the peak resident size of each DRAT checking route on a real certificate (ADR-0426)? |

### Rado-family campaign drivers

These seven encode a specific research campaign — `R_k(a(x-y) = bz)` — and carry
frozen instance parameters, output paths, and budget assumptions from it. They
are the most experiment-specific examples in the tree; read the file's own header
before running one, and do not treat any of them as a general search CLI.

| Example | Arguments | Question answered |
|---|---|---|
| [`akb2_frontier`](../../crates/axeyum-search/examples/akb2_frontier.rs) | see file header | Frontier driver for `R_k(a(x-y) = bz)` at `k >= 4` — the `a^k` line of Chang, De Loera and Wesley (ISSAC 2022, arXiv:2210.03262). |
| [`rado_adaptive_cover`](../../crates/axeyum-search/examples/rado_adaptive_cover.rs) | see file header | Adaptive cube-cover driver, built for `F_741`, for instances where a flat cover stops paying. |
| [`rado_certify_tree_cover`](../../crates/axeyum-search/examples/rado_certify_tree_cover.rs) | see file header | Offline certification of a dumped tree cover: reads every proof the search run deferred. |
| [`rado_cover_gaps`](../../crates/axeyum-search/examples/rado_cover_gaps.rs) | see file header | What a partial tree cover has NOT covered, written as a resumable pending file. |
| [`rado_dump_cnf`](../../crates/axeyum-search/examples/rado_dump_cnf.rs) | see file header | Writes the deciding CNF from the encoder the cover actually used, so a ledger's `unsat` can be re-derived rather than believed. |
| [`rado_replay_tree_cover`](../../crates/axeyum-search/examples/rado_replay_tree_cover.rs) | see file header | Independent re-validation of a tree cover from its ledger alone, for runs that checked inline and kept no DRAT bytes. |
| [`rado_sat_probe`](../../crates/axeyum-search/examples/rado_sat_probe.rs) | see file header | Bounded satisfiable-side probe. At `n = 741, k = 4` the expected outcome is that nothing is found. |

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
