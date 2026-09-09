# Harnesses, benchmarks, test suites, and gates — inventory (2026-09-09)

Scope: how the solver stack is exercised, measured, and consumed. Covers
`crates/axeyum-bench/` (corpus harness + research examples), `crates/axeyum-scenarios/`
(ADR-0008 self-checking workloads), `crates/axeyum-search/` (a combinatorial-search
consumer), the binding crates (`axeyum-py`, `axeyum-wasm`, `axeyum-property(-macros)`,
`axeyum-machine`), the full `axeyum-solver`/`axeyum-cnf`/`axeyum-rewrite`/`axeyum-smtlib`
integration-test census, the feature-gate-to-zero audit, the `justfile`/`check.sh`
divergence, and the committed corpora. Base commit `ea8515407`. No `cargo`/`git`-write
command was run; every count below comes from reading source, `Cargo.toml`, the
`justfile`, and shell/Python scripts.

## Summary

- `axeyum-bench` is the corpus harness: one 9,596-line `main.rs` (plus a 372-line
  isolated-worker module) driving backend selection, `:status` disagreement checks,
  PAR-2 scoring, and 39 versioned artifact fields (`ARTIFACT_VERSION = 39`). It also
  hosts 34 research-probe `examples/` (26,996 total src+examples lines), two of which
  — `scenario_pipeline_report` and `scenario_scaling` — are the only committed callers
  of `axeyum-scenarios` outside test code.
- `axeyum-scenarios` (ADR-0008) is 13,211 lines across 31 modules generating
  oracle-free SAT/UNSAT workloads. Its `self_check()` is the ground truth; it is a
  **dev/example-only** dependency of `axeyum-solver` (10+ `tests/*.rs` files) and
  `axeyum-bench` (2 examples), never linked into the shipped solver library.
- `axeyum-search` (18,455 lines, 18 src files) is **not** solver internals and **not**
  a consumer of the solver facade: its `Cargo.toml` depends only on `axeyum-cas` and
  `axeyum-cnf`, with zero references to `axeyum_solver`, `axeyum_ir`, or `axeyum_smtlib`
  anywhere in the crate. It is a standalone combinatorial-search application that
  hand-builds `CnfFormula`s (Rado numbers, graph colouring, job-shop, tensor
  decomposition, SIMD synthesis), drives them through `axeyum_cnf::solve_with_drat_proof`
  directly, and re-certifies every UNSAT with an independent DRAT recheck
  (`certify.rs`) plus a corruption-resistant status ledger (`ledger.rs`). No other
  workspace crate depends on it (`grep` across `crates/*/Cargo.toml` finds one hit:
  itself).
- **The feature-gate-to-zero audit is the headline finding.** 298 of 302
  `axeyum-solver/tests/*.rs` files (98.7%) carry a module-level `#![cfg(feature = "...")]`
  and compile to **zero** tests on default features: 268 need `full` alone, 28 need
  `full` **and** `z3` (two stacked `#![cfg(feature = ...)]` lines — satisfied together
  because `z3` implies `full` in `Cargo.toml`), and 2 need `full` **and**
  `batsat-reference`. Only 4 files (`api_namespaces.rs`, `lean_module_fixtures.rs`,
  `memory_budget.rs`, `qfbv_profile.rs`) run under the default `qfbv` feature. In
  `axeyum-cnf/tests/` only 1 of 11 is gated (`batsat-reference`); `axeyum-rewrite/tests/`
  (7) and `axeyum-smtlib/tests/` (2) are entirely ungated.
- The gating is not only at the test-file level. `crates/axeyum-solver/src/lib.rs:70-249`
  declares a `full_modules!()` macro (165 `mod` lines) invoked only under
  `#[cfg(feature = "full")]` at `lib.rs:251-252`; the default `qfbv` build compiles
  roughly a dozen core modules (`backend`, `config_registry`, `error`, `incremental`,
  `layers`, `lazy_smt_counters`, `live_instruments`, `memory_budget`, `model`,
  `portfolio`, `proof`, `sat_bv_backend`) plus the ungated `proofs` re-export
  namespace. The re-export namespaces `constraints`, `certificates`, `theories`,
  `verification`, `optimization`, `interpolation` are each separately
  `#[cfg(feature = "full")]`. So a test suite can compile cleanly on default features
  while the module it means to exercise was never built into the crate at all — a
  second, module-level face of the same zero-test problem the test-file gating causes.
- `just check` (the `check:` recipe, ~112 space-separated dependency names, `justfile:58`)
  and `scripts/check.sh` are **not the same gate** in the solver-relevant slice either.
  Read directly: `qfbv-profile`, `benchmark-repetition-tests`, and `glaurung-qfbv-regular`
  are named in `just check`'s dependency list but do **not** appear anywhere in
  `scripts/check.sh` (confirmed by `grep` returning nothing for all three patterns);
  `solver-module-graph` appears in both. `check.sh` additionally runs a handful of
  one-off solver probes `just check` does not name as top-level targets
  (`solver-reconstruct-sweep`, `evidence-lean-module-wrapper`, four
  `axiom-freedom-*` steps, `dominance-audit-harness-tests`,
  `explain-corpus-diagnostic-tests`). This is a narrower, solver-scoped confirmation
  of the CLAUDE.md-recorded 112-vs-61-step divergence, not a recount of the whole
  aggregate.
- **All `bench-public-qfbv-*` recipes (16 of them) target
  `corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen`, and `corpus/public/`
  is empty and gitignored in this tree** (`find corpus/public -type f` returns 0
  files; `corpus/README.md` marks it "No — gitignored; fetch with
  `scripts/fetch-corpus.sh`"). None of the 16 recipes are runnable from a fresh clone
  without a multi-GB external fetch. Likewise every `bench-glaurung-qfbv-*` recipe
  (client-tier, ~25 recipes) resolves its corpus through
  `scripts/check-glaurung-qfbv-regular.sh`'s pinned NAS path
  `/nas4/data/workspace-infosec/glaurung-captures/...` or an explicit env var — absent
  either, the gate prints `SKIP` and exits 0. Only `bench-micro` / `bench-micro-z3`
  (against the 6-file `corpus/micro/`) and `bench-qfbv-curated*` (against the
  committed 43-file `corpus/qfbv-curated/`) are runnable as committed, and
  `bench-micro-z3`/`bench-qfbv-curated*` additionally need `--features z3` (a C/C++
  leaf dependency, not built by default).
- Oracle-based vs. self-checking split: every `bench-*` recipe that names
  `--compare-z3` (all `bench-glaurung-qfbv-*`, all `bench-public-qfbv-*`,
  `bench-qfbv-curated*`, `bench-micro-z3`) measures against the Z3 oracle — the
  bootstrap-scaffolding trust source ADR-0002 plans to demote. `axeyum-scenarios`
  (ADR-0008) and the SMT-LIB `:status` field baked into `corpus/micro`,
  `corpus/regression`, `corpus/qfbv-curated`, and `corpus/public-curated` are the
  oracle-free routes: ground truth by concrete execution / bounded-verified identity,
  or by a benchmark author's pinned `:status`, never by re-asking another solver.
- Committed, runnable-today corpora: `corpus/micro` (6 files: 3 `.smt2` + 2 `.json`
  manifests + `.gitkeep`), `corpus/micro-cnf` (3 `.cnf`), `corpus/client` (1 file),
  `corpus/regression` (152 `.smt2` + 2 `.md`), `corpus/qfbv-curated` (43 `.smt2` + 1
  `.md`), `corpus/public-curated` (903 `.smt2` + 20 `.md`, subdivided into `named/`,
  `bvred/`, `iand/`, `synthetic/`, `non-incremental/`, `quantified/`). `corpus/public/`
  is the one gitignored, fetch-required directory.
- Only 16 of the 298 feature-gated-to-zero `axeyum-solver` test files (13 `test:*`
  entries plus `lib`) have an explicit minimum-test-count floor in
  `scripts/check-gate-liveness.sh`'s manifest — the mechanism that actually prevents
  a suite from silently emptying (the 15-day `corpus_regression` inertness this
  script's own header documents). The other ~285 gated files have no such floor.

## Inventory

### `axeyum-bench` — corpus harness and research probes

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| Main harness (`run` module) | `crates/axeyum-bench/src/main.rs` | 9,596 | Corpus walker: parses each `.smt2`, runs the solver trait, checks `:status` agreement, PAR-2 scores, emits versioned JSON (`ARTIFACT_VERSION = 39`) | WIRED — `default-run = "axeyum"` bin | `main.rs:1-30` doc comment, `Cargo.toml:31-34` |
| `certificate_process` | `crates/axeyum-bench/src/certificate_process.rs` | 372 | Isolated-worker process for end-to-end UNSAT certification (`--certify-end-to-end-unsat`) | WIRED from `main.rs:34-36` | `main.rs:30,34` |
| `axeyum` bin (`src/bin/axeyum.rs`) | — | — | ADR-0541 general SMT-LIB driver, promoted from example to named bin | WIRED | `Cargo.toml` `[[bin]] name = "axeyum"` |
| `glaurung-ordered-trace`, `qfbv-proof-export` | `src/bin/*.rs` | — | Auxiliary diagnostic binaries | WIRED (separate bins) | `find crates/axeyum-bench/src/bin` |
| 34 `examples/*.rs` | `crates/axeyum-bench/examples/` | 26,996 total (src+examples) | Research probes: rewrite ablation, corpus explanation, replay-refine profiling, `scenario_pipeline_report`, `scenario_scaling`, `cq_containment_certify`, `db_design_certify`, `cvc5_*` comparison probes, etc. README states explicitly these "are not all stable user interfaces" | Mixed: most TEST-ONLY (invoked only via `cargo run --example` in docs/justfile), `cnf_stream_bench` FEATURE-GATED on `z3`, `gate_b_sweep` FEATURE-GATED on `batsat-reference` | `Cargo.toml:39-56`, `README.md` |
| `certificate_process_isolation.rs`, `qfbv_proof_export.rs` | `crates/axeyum-bench/tests/` | — | Integration tests for the harness itself | TEST-ONLY (own crate's tests) | `ls crates/axeyum-bench/tests/` |

### `axeyum-scenarios` — ADR-0008 self-checking workloads

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| Crate root, `Scenario`/`Expectation`/`self_check` | `crates/axeyum-scenarios/src/lib.rs` | part of 13,211 total | Oracle-free ground truth: SAT by concrete execution (witness carried on `Expectation::Sat`), UNSAT by bounded-verified identity (`self_check` exhaustive or sampled) | WIRED as dev-dependency | `lib.rs:1-38`, `self_check` at `lib.rs:360` |
| 31 domain modules (`algebra`, `arithmetic`, `mixing`, `memory`, `dbdesign/*`, …) | `crates/axeyum-scenarios/src/*.rs` | 13,211 | Scenario families: mixing-function inversion, bit-twiddling identities, symbolic-execution-shaped path conditions, DB-design functional-dependency queries, etc. | TEST-ONLY / EXAMPLE-ONLY (see below) | `find crates/axeyum-scenarios/src` |
| Consumer: `axeyum-solver/tests/*.rs` | 10 files (`scenarios.rs`, `array_scenarios.rs`, `function_scenarios.rs`, `integer_scenarios.rs`, `real_scenarios.rs`, `pigeonhole_proof.rs`, `progress_frontier.rs`, `incremental.rs`, …) | — | Every scenario carries its own ground truth into the solver's own test suite | TEST-ONLY (dev-dependency, `crates/axeyum-solver/Cargo.toml:76`) | `grep -rn axeyum_scenarios crates/axeyum-solver/tests` |
| Consumer: `axeyum-bench/examples/scenario_pipeline_report.rs`, `scenario_scaling.rs` | — | — | Runs the whole catalog (or the `mixing_inversion` family swept over width/rounds) through `SatBvBackend` and reports AIG/CNF/timing stats | TEST-ONLY (example, `cargo run --example`) | `scenario_pipeline_report.rs:1-19`, `scenario_scaling.rs:1-20` |
| `dbdesign` submodule (armstrong, decomposition, normal_forms, cq, encode, parse) | `crates/axeyum-scenarios/src/dbdesign/*.rs` | part of 13,211 | Functional-dependency / conjunctive-query containment scenarios | TEST-ONLY (consumed only by `axeyum-bench/examples/{cq_containment_certify,db_design_certify}.rs`) | `cq_containment_certify.rs:40-45`, `db_design_certify.rs:42-52` |

`axeyum-scenarios` is never a dependency of `axeyum-solver`'s or `axeyum-bench`'s
non-test/non-example code (`Cargo.toml` for `axeyum-solver` lists it under no
`[dependencies]` section, only as a `[dev-dependencies]`-style path dep at line 76,
which the `[dependencies]` section on that line actually shows — see Gaps: the exact
`[dev-dependencies]` vs `[dependencies]` placement in `axeyum-solver/Cargo.toml` was
not independently re-verified beyond line 76's text match; `axeyum-bench` lists it as
an ordinary `[dependencies]` entry because its own `main.rs` binary does not use it —
only the `examples/` do).

### `axeyum-search` — combinatorial-search application layer (NOT solver internals)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| Crate root / cost model doc | `crates/axeyum-search/src/lib.rs` | 397 | States the crate's own identity: "the housed form of the tooling that computed and certified Rado-number bounds… Everything runs through `axeyum_cnf` and `std`. There is no external SAT solver and no external proof checker anywhere in this crate." | — | `lib.rs:1-9` |
| `colouring.rs` | `crates/axeyum-search/src/colouring.rs` | 1,428 | Encodes a graph-colouring / Rado-type instance to `CnfFormula` by hand (`axeyum_cnf::{CnfFormula, WeightedAtMostError, ...}` at line 52), calls `axeyum_cnf::solve_with_drat_proof`/`check_drat` directly at lines 1242, 1295, 1313, 1357 | WIRED within crate | `colouring.rs:52,1242,1295,1313,1357` |
| `cover.rs` | `crates/axeyum-search/src/cover.rs` | 1,157 | Cube-and-conquer branch cover; `verify_branch_clauses`, `verify_cell_set`, `certify_cover` — the four cover obligations | WIRED within crate | `lib.rs:29-43` |
| `certify.rs` | `crates/axeyum-search/src/certify.rs` | 346 | Offline re-certification of a dumped cover: re-derives augmenting unit clauses from the ledger's recorded `BranchPlan` choices (never trusts the proof file), re-verifies all four obligations from scratch via `certify_cover` | WIRED within crate | `certify.rs:1-17` |
| `ledger.rs` | `crates/axeyum-search/src/ledger.rs` | 401 | Crash-safe, duplicate-detecting per-cell status log (`create_new` instead of append; `parse_ledger` rejects repeated cell indices regardless of run id) — documents a real incident (Finding B2: a restarted run appended and produced 69 duplicate rows) | WIRED within crate | `ledger.rs:1-24` |
| `harness.rs`, `compose.rs`, `search.rs` | — | 1,803 / 245 / 326 | Run orchestration (`run_cover`), meta-argument→checked-DRAT composition (`compose_cover_proof`), local search for the SAT side (`min_conflicts`) | WIRED within crate | `lib.rs:17-49` |
| `job_shop.rs`, `tensor_decomposition.rs`, `multiplicative_circuit.rs`, `simd*.rs`, `vdw.rs`, `boolean_anf_cnf.rs`, `offdiag.rs`, `family.rs` | — | 4,011 / 1,330 / 2,295 / 753+569+777+487 / 651 / 914 / 565 | Other parameterised combinatorial families (job-shop scheduling, tensor decomposition, SIMD program synthesis, van der Waerden numbers) sharing the same encode→CDCL→DRAT-recheck shape | WIRED within crate | `find crates/axeyum-search/src` |
| 22 `examples/*.rs` (`rado_*`, `synthesize_*`, `job_shop_*`, `certify_job_shop`, `verify_colouring_witness`, …) | `crates/axeyum-search/examples/` | — | Standalone research/production runs | TEST-ONLY (own crate, `cargo run --example`) | `ls crates/axeyum-search/examples/` |
| `vdw.rs`, `offdiag_schur.rs`, `encoding_parity.rs` | `crates/axeyum-search/tests/` | — | 3 integration tests | TEST-ONLY (own crate) | `ls crates/axeyum-search/tests/` |

**Verdict on the coordinator's question:** `axeyum-search`'s `Cargo.toml` (`crates/axeyum-search/Cargo.toml:14-16`)
declares exactly two path/workspace dependencies — `axeyum-cas` and `axeyum-cnf` —
plus `serde`. `grep -rn 'axeyum_solver\|axeyum_ir\|axeyum_smtlib\|SolverBackend\|TermArena' crates/axeyum-search/{src,tests,examples}`
returns zero hits. So the crate has no path to a theory solver, no `TermArena`, no
`SolverBackend` — it reaches the propositional CDCL+DRAT layer (`axeyum-cnf`)
directly and bypasses the `axeyum-solver` facade entirely. It is a **downstream
application built on the SAT core**, functionally analogous to what a from-scratch
Rado-number/graph-colouring solver written against `axeyum-cnf`'s public API would
look like, complete with its own independent re-certification path
(`certify.rs`/`compose.rs`) so a bug in the *producing* run cannot silently become
the accepted answer. `axeyum-cas` is used for supporting algebra (the doc comments
reference number-theoretic bound computations), not for theory solving.

### Bindings and embedding

| Crate | Path | LOC | What it is | Solver surface exposed |
|---|---|---|---|---|
| `axeyum-py` | `crates/axeyum-py/` | 34,722 | PyO3 extension module built as `axeyum._native` (`Cargo.toml` `crate-type = ["cdylib","rlib"]`); imported by a pure-Python package (`python/axeyum/`). Its own doc comment states the constraint plainly: "No function exists here that does not exist in Rust, and no call through it can admit a fact, write a ledger, relax a checker, or change an axiom footprint" (`lib.rs:8-11`). Modules: `cas/` (24 files, CAS surface), `ir/` (7 files, term/arena/lowering), `kernel.rs` (Lean kernel), `machine/` (a0/rv64/x64), `smt.rs` (1,573 lines), `solver/` (5 files: `cnf.rs`, `core.rs`, `ledgers.rs`, `proofs.rs`, `results.rs`) | `smt.solve` wraps `axeyum_solver::smtlib::solve_smtlib` (ADR-0052) verbatim — "no logic selection the Rust call cannot make… no way to turn an `unknown` into anything other than an `unknown`" (`smt.rs:1-7`). `solver/` (tier P+C) binds decide-then-check: `CheckResult`, `Evidence.check_outcome()`/`check()`, `UnsatProof.recheck_lrat()`, `check_drat`'s third (budget-miss) answer, `UnsatProofOutcome.Inconclusive` (`solver/mod.rs:1-12`) |
| `axeyum-wasm` | `crates/axeyum-wasm/` | 181 | WebAssembly binding for a browser playground (`wasm-bindgen`); depends on `axeyum-solver` with `default-features = false, features = ["qfbv"]` — the minimal pure-Rust profile, no C/C++ | Exposes the default `qfbv`-profile `SolverBackend`/`SatBvBackend` surface plus `axeyum-smtlib` parsing to the browser; nothing behind `full` |
| `axeyum-property` + `axeyum-property-macros` | `crates/axeyum-property/`, `crates/axeyum-property-macros/` | 3,010 + 224 | "Typed prove-or-counterexample SDK" — a thin consumer wrapper: builds terms in a `TermArena`, "delegates proving to `axeyum_solver::prove` or `axeyum_solver::prove_minimized`… does not add solver logic or weaken the underlying evidence contract" (`lib.rs:1-6`). The macros crate supplies a `#[derive(Symbolic)]` proc-macro | `EvidenceReport`, `Model`, `ProofFragment`, `ProofOutcome`, `SolverConfig`, plus `prove`, `prove_minimized_with_objectives`, `prove_unsat_to_lean_module` (`lib.rs:18-23`); a `reproduce` module turns a counterexample into a runnable `#[test]` |
| `axeyum-machine` | `crates/axeyum-machine/` | 4,150 | Executable ISA semantics — `a0.rs` (teaching ISA), `x64.rs`, `rv64.rs`, `cross_isa.rs`. `Cargo.toml` has **no `[dependencies]` section at all**, and `grep -rn '^use axeyum' crates/axeyum-machine/src` returns nothing | None directly — this crate is std-only concrete-semantics code with zero coupling to the solver stack at the Rust-dependency level. It is consumed by `axeyum-py/src/machine/*.rs` (which does depend on `axeyum-solver`) and by the separate `axeyum-machine-evidence` crate (out of this lane's named scope) to build solver-checkable evidence routes on top |

## The test suite census

Exact counts (`ls crates/<c>/tests/*.rs | wc -l`): `axeyum-solver` **302**,
`axeyum-cnf` **11**, `axeyum-rewrite` **7**, `axeyum-smtlib` **2**. Total LOC:
128,128 / 4,054 / 2,550 / 6,593 respectively (`axeyum-smtlib`'s total is almost
entirely one file, `tests/smtlib.rs` at 6,506 lines, versus 87 for
`distinct_packed_sort_widths.rs`).

### `axeyum-solver/tests/` (302 files) by area

Grouping is mine (name/content keyword match over all 302 filenames; the brief's
nine suggested buckets plus three I found necessary to keep the largest bucket
from swallowing unrelated theories). Every file lands in exactly one bucket
(sum = 302).

| Group | Count | Note |
|---|---|---|
| Arithmetic (LIA/LRA/NIA/NRA, interpolation, DPLL(T)/CDCL(T), PDR/IC3, Gomory, simplex, Farkas, Sturm, Spivak, PB/MaxSat, Horn, induction) | 67 | Largest bucket; `nra_real_root.rs` (2,566 lines) and `math_resource_lra_routes.rs` (2,444) are the biggest single files |
| Proofs / evidence (proof export, evidence certs, Lean reconstruction, DRAT/Alethe/Carcara checking, trust ledger) | 62 | `lean_crosscheck.rs` (4,042), `carcara_crosscheck.rs` (3,369), `evidence.rs` (2,729) |
| Fuzz / differential (name contains `fuzz` or `differential`) | 39 | `bv_differential_fuzz.rs` (2,486), `quantified_uflia_model_finder_differential_fuzz.rs` (2,024) |
| Infra / harness (incremental, warm/cold, preprocessing, smtlib front door, symbolic execution, optimize, scenarios plumbing) | 38 | `symbolic_execution.rs` is the single largest test file in the crate at 5,652 lines |
| Quantifiers (`quant_*`, `mbqi`, instantiation, `qinst`) | 24 | `progress_frontier.rs` (2,611, the frontier ratchet) folds in here structurally though it spans theories |
| Strings (`string*`, `word*`, `qf_s*`, `slia`, regex, `stoi`, `from_code`) | 18 | `qf_slia_fixed_splice.rs` (2,960) is the single largest string-route file |
| BV core (`bv*`, bitblast, `xor_cdcl`, `sat_bv`) | 13 | `sat_bv.rs` (1,380) |
| Arrays (`array*`, `abv`, `aufbv`) | 13 | `aufbv_online_differential_fuzz.rs` (1,347) |
| EUF / datatypes (`euf*`, `datatype*`, `enums`, `records`, `distinct`, `cardinality`, `uninterpreted_sort_euf`) | 12 | — |
| Dispatch / routing (`route*`, `strategy`, `portfolio`, `front_door`, `capabilities`, `coercions`, `support_matrix`, `api_namespaces`) | 12 | — |
| Floating point (`fp*`, `fpa2bv`) | 3 | — |
| Regression corpora (`corpus_regression.rs`) | 1 | The `:status` sweep with the 15-day inertness incident (see below) |

### `axeyum-cnf/tests/` (11 files, 4,054 LOC)

`colouring_encoding_parity.rs` (536), `deterministic_work_budget.rs` (345),
`drat_backward_file_differential.rs` (428), `drat_memory_model.rs`,
`inprocess_proof_path.rs` (818, largest), `interpolant.rs`,
`math_resource_boolean_routes.rs`, `native_vs_batsat_differential.rs`
(feature-gated, see below), `propositional_interpolant_certified.rs`,
`theory_lemma_proof_contract.rs`, `vivify.rs`. These cover Tseitin/CNF
encoding, DRAT checking (forward and backward, ADR-0382), interpolation, and
inprocessing (subsumption/BVE/vivification).

### `axeyum-rewrite/tests/` (7 files, 2,550 LOC)

`elim_unconstrained_exhaustive.rs` (929, largest), `precondition_fuzz.rs` (420),
`quantifier_duality.rs` (355), `int_divmod_witness.rs` (343),
`function_abstraction_witness.rs` (293), `read_over_write_witness.rs` (158,
QF_ABV array elimination, ADR-0010), `datatypes.rs` (52).

### `axeyum-smtlib/tests/` (2 files, 6,593 LOC)

`smtlib.rs` (6,506 — the SMT-LIB benchmark-slice parser/writer round-trip
suite) and `distinct_packed_sort_widths.rs` (87).

## The feature-gate-to-zero audit

Method: `grep -lE '^#!\[cfg\(feature' crates/<c>/tests/*.rs` (module-level inner
attributes must precede all items in a Rust file, so wherever the line appears
it gates the whole compilation unit) plus a Python pass reading every matching
line per file to detect files with **two** stacked `#![cfg(feature = "...")]]`
lines (both must hold — an AND, not an OR).

### `axeyum-solver/tests/` — 298 of 302 files (98.7%) gated to zero

| Gate condition | File count | What's needed to run any test in these files |
|---|---|---|
| `#![cfg(feature = "full")]` only | 268 | `cargo test -p axeyum-solver --features full` |
| `#![cfg(feature = "full")]` **and** `#![cfg(feature = "z3")]` (stacked) | 28 | `cargo test -p axeyum-solver --features z3` (or `full,z3`) — `z3` implies `full` in `Cargo.toml`'s `[features]` block, so a single `--features z3` satisfies both | 
| `#![cfg(all(feature = "full", feature = "batsat-reference"))]` | 2 | `cargo test -p axeyum-solver --features full,batsat-reference` |
| **Ungated** (run on default `qfbv` features) | 4 | `api_namespaces.rs`, `lean_module_fixtures.rs`, `memory_budget.rs`, `qfbv_profile.rs` |

The 28 `full`+`z3` files are exactly the differential/oracle-comparison suites:
`abv_differential_fuzz.rs`, `bv_differential_fuzz.rs`, `differential.rs`,
`fp_differential_fuzz.rs`, `nia_differential_fuzz.rs`, `nra_differential_fuzz.rs`,
`qf_dt_differential_fuzz.rs`, `qf_lra_differential_fuzz.rs`,
`qf_nia_bounded_product_differential_fuzz.rs`,
`qf_nia_divmod_const_differential_fuzz.rs`,
`qf_nia_divmod_var_differential_fuzz.rs`, `qf_nia_iand_differential_fuzz.rs`,
`qf_nia_pow2_differential_fuzz.rs`, `qf_s_online_differential_fuzz.rs`,
`qf_uf_differential_fuzz.rs`, `qf_uflra_differential_fuzz.rs`,
`qf_ufnra_differential_fuzz.rs`, `query_planning.rs`, `rewrite_differential.rs`,
`seq_differential_fuzz.rs`, `simplex_lra_fallback_differential.rs`,
`string_differential_fuzz.rs`, `uflia_differential_fuzz.rs`,
`word_equation_differential_fuzz.rs`, `quantified_bv_differential_fuzz.rs`,
`quantified_uflia_model_finder_differential_fuzz.rs`,
`online_string_front_door_fuzz.rs`, `z3.rs`. This matches CLAUDE.md's explicit
listing of `qf_lra_differential_fuzz`, `simplex_lra_fallback_differential`, and
`qf_uflra_differential_fuzz` as the linear-arithmetic pre-merge z3 gate, plus the
strings/BV/NIA/quantifier differential suites CLAUDE.md does not enumerate by name.

The 2 `full`+`batsat-reference` files (`native_cdcl_baseline.rs`,
`xor_cdcl_curated_measure.rs`) are the ADR-1703 measurement-only suites: BatSat
is retired as the SAT engine (native CDCL is the engine on every path since
ADR-1703), and these two exist only to time the retired adapter as a comparison
point. `axeyum-solver/Cargo.toml`'s `batsat-reference` feature comment states
this in the source: "both suites compile to ZERO tests without it and exit 0."

### `axeyum-cnf/tests/` — 1 of 11 gated

Only `native_vs_batsat_differential.rs` carries `#![cfg(feature = "batsat-reference")]`
— the third ADR-1703 measurement-only suite (a sibling of the two in
`axeyum-solver`, comparing the native core against the retired BatSat adapter at
the CNF layer directly). The other 10 files run on `axeyum-cnf`'s default
features.

### `axeyum-rewrite/tests/` and `axeyum-smtlib/tests/` — 0 gated

All 7 rewrite suites and both smtlib suites are ungated; every test in them runs
under `cargo test -p <crate>` with no extra flags.

### Module-level gating (the second face, per the coordinator's note)

`crates/axeyum-solver/src/lib.rs:70` declares `macro_rules! full_modules!`
guarded by `#[cfg(feature = "full")]`; the macro body (`lib.rs:71-248`) contains
**165** `mod` declarations, and the macro is invoked once, also under
`#[cfg(feature = "full")]`, at `lib.rs:251-252`. Outside that macro, the crate's
own top-level `mod`/`pub mod` count is 20 lines (`grep -c '^mod \|^pub mod '
crates/axeyum-solver/src/lib.rs`), of which the re-export namespaces
`constraints` (`lib.rs:282-284`), `certificates` (`lib.rs:434-436`), `theories`
(`lib.rs:656-658`), `verification` (`lib.rs:760-762`), `optimization`
(`lib.rs:822-824`), and `interpolation` (`lib.rs:863-865`) are each individually
`#[cfg(feature = "full")]`, and `bench_internals` (`lib.rs:271-273`) is
`#[cfg(feature = "bench-internals")]`. Only `proofs` (`lib.rs:305`, re-exporting
from the always-built `mod proof;` at `lib.rs:67`) and the dozen core modules
listed in the Summary compile under plain `qfbv`. So the count that matters for
"does the default build even contain this code" is roughly 165 theory/route
modules behind one crate-wide flag, not 20 — a test suite gated on `full`
(or even one that is *not* gated) can be exercising code that literally does not
exist in a `qfbv`-only build, and `cargo check --workspace` on default features
would not catch a suite trying to reference it (the suite itself would fail to
compile, which is a visible error — the silent case is a *default-feature*
integration point, e.g. `axeyum-wasm`, that never sees the gap because it never
imports the gated names).

## Gates: what `justfile` and `scripts/check.sh` actually run

### `justfile`

`check:` (`justfile:58`) lists roughly 110 space-separated recipe names as
prerequisites, the large majority autogenesis/kernel/Lean/CAS-parity/curriculum
steps out of this lane's scope. The solver/harness-relevant subset: `clippy`
(→ `scripts/check-clippy-complete.sh`), `test` (→
`scripts/check-workspace-tests.sh`, `cargo test --workspace --all-features --
--skip frontier_`), `frontier` (→ `cargo test -p axeyum-solver --test
progress_frontier --features full -- --test-threads=1`), `gate-liveness` (→
`scripts/check-gate-liveness.sh`), `qfbv-profile` (→
`scripts/check-qfbv-profile.sh`), `benchmark-repetition-tests` (→ 18 named
`scripts/tests/test_*glaurung*` and `test_*bit_lowering*` Python unittest
modules), `glaurung-qfbv-regular` (→
`scripts/check-glaurung-qfbv-regular.sh`), `solver-module-graph` (→
`scripts/analyze_solver_module_graph.py --check`), `foundational-resources`.

Separately, `bench-*` recipes are **not** part of `check:` at all — they are
manually invoked measurement/reproduction commands (see below), not gates.

### `scripts/check.sh`

Confirmed by direct `grep -n 'step '` over the file: `step clippy
./scripts/check-clippy-complete.sh` (`check.sh:959`), `step test
./scripts/check-workspace-tests.sh` (`check.sh:1245`), `step frontier cargo
test -p axeyum-solver --test progress_frontier --features full --
--test-threads=1` (`check.sh:1256`), `step gate-liveness
./scripts/check-gate-liveness.sh` (`check.sh:1261`), `step doc cargo doc
--workspace --all-features --no-deps` (`check.sh:1335`), `step
solver-module-graph python3 scripts/analyze_solver_module_graph.py --check`
(`check.sh:1571`), plus targeted probes: `dominance-audit-harness-tests`
(`cargo test -p axeyum-bench --example audit_dominance`, `check.sh:1162`),
`explain-corpus-diagnostic-tests` (`cargo test -p axeyum-bench --example
explain_corpus`, `check.sh:1168`), `solver-reconstruct-sweep` (`cargo test -p
axeyum-solver --lib --features full reconstruct::`, `check.sh:1176`),
`evidence-lean-module-wrapper` (`check.sh:1180`), four `axiom-freedom-*` steps
(`check.sh:1188-1194`).

### Read divergence (solver-relevant slice, confirmed by direct grep, not by running either gate)

`qfbv-profile`, `benchmark-repetition-tests`, and `glaurung-qfbv-regular` are
named in `just check`'s dependency chain but **absent from `scripts/check.sh`**
— `grep -n "qfbv-profile\|benchmark-repetition-tests\|glaurung-qfbv-regular"
scripts/check.sh` returns nothing for all three. `solver-module-graph` is
present in both under the same name. This is consistent with, and gives
solver-specific evidence for, CLAUDE.md's recorded 112-vs-61-step measurement
(2026-08-14) and its claim that "check.sh skipped the Lean axiom ledger… while
`just check` skipped check-gate-liveness.sh" — except as read on 2026-09-09,
`gate-liveness` **is** present in both `justfile:58`'s dependency list and
`check.sh:1261`; that particular part of CLAUDE.md's claim no longer matches
what's on disk (see Doc drift). What is still true and newly confirmed here:
the two files' solver-harness step lists are not identical, and the specific
gap (three named recipes reachable only through `just check`) is exactly the
"each missing something the other had" shape CLAUDE.md warns about.

## Data flow (axeyum-bench harness)

1. `main::run::main()` parses CLI flags (`--backend`, `--rewrite`,
   `--query-plan`, `--compare-z3`, budgets, `--corpus-manifest`, …).
2. Walks the corpus directory, parses each `.smt2` via
   `axeyum_smtlib::parse_script`, extracts the declared `:status`.
3. Optionally canonicalizes (`axeyum_rewrite::canonicalize_terms`) and/or
   preprocesses (`propagate_values`, `solve_eqs_bounded`) per `--rewrite`/
   `--preprocess`.
4. Dispatches to the selected `SolverBackend` (`SatBvBackend`,
   `IncrementalBvSolver`, `LazyBvBackend`, or `Z3Backend` under `--features z3`)
   with a `QueryPlan` (full / first-assertion-support / replay-refine /
   replay-refine-exact).
5. On `sat`, replays the model against the original term arena
   (`check_model_with_assignment`) — a mismatch is `model_replay_failures` and
   triggers `eprintln!("SOUNDNESS ALARM: sat model replay failed")`
   (`main.rs:1824-1826`).
6. On `unsat` with `--prove-unsat`, exports and independently replays the DRAT
   proof; a missing replay is a second soundness alarm
   (`main.rs:1828-1830`).
7. If `--compare-z3`, runs Z3 (in-process or subprocess per
   `--require-in-process-z3`) on the same query and records `agree`/`DISAGREE`;
   a `DISAGREE` makes the harness exit nonzero (doc comment, `main.rs:1-7`).
8. Emits one JSON artifact per run: per-instance verdicts, PAR-2 score,
   layer-attributed timing (`BvLayerStats`), determinism/config hashes
   (`NATIVE_CDCL_ENGINE_ID`, `RESOURCE_PROFILE`, `DETERMINISM_PROFILE`), and
   (for the glaurung/public recipes) decided-rate and Axeyum/Z3 timing ratios.

## Entry points and public API

- **Binary**: `cargo run -p axeyum-bench -- <corpus_dir> [flags…]` (or the
  `axeyum` bin alias). Flags are enumerated in `main.rs`'s module doc comment.
- **`justfile` recipes**: `bench-micro`, `bench-micro-z3`, `bench-qfbv-curated*`
  (3 variants), `bench-public-qfbv-*` (16 recipes), `bench-glaurung-qfbv-*`
  (~25 recipes plus repeated/proof-check/demand-profile variants),
  `bench-cas-parity`, `generate-glaurung-manifest`,
  `compare-glaurung-qfbv-repeated*` (3 comparison scripts).
- **Examples**: `cargo run -p axeyum-bench --example <name>` for the 34
  research probes; `scenario_pipeline_report` and `scenario_scaling` are the
  ones that touch `axeyum-scenarios`.
- **`axeyum-scenarios` crate API**: `Scenario`, `Expectation`, `Family`,
  `catalog()`, plus per-family constructors (`mixing_inversion`,
  `full_adder_identity`, `pigeonhole`, `permutation_exists`,
  `memory_catalog`, `function_catalog`, `integer_catalog`, `real_catalog`, …)
  and `Scenario::self_check() -> Result<UnsatEvidence, SelfCheckError>`.
- **`axeyum-search` crate API**: `ColouringFamily`/`ColouringProblem`,
  `harness::run_cover`, `cover::certify_cover`/`certify_tree_cover`,
  `certify::certify_dumped_cover`, `compose::compose_cover_proof`,
  `ledger::{LedgerWriter, parse_ledger}`, plus per-family modules
  (`job_shop`, `tensor_decomposition`, `vdw`, `boolean_anf_cnf`,
  `multiplicative_circuit`, `simd*`).
- **`axeyum-py`**: Python package `axeyum` → `axeyum._native` extension;
  `axeyum.smt.solve(...)`, `axeyum.solver.*` (tier P+C), `axeyum.cas.*`,
  `axeyum.machine.*`.
- **`axeyum-wasm`**: `wasm-pack build` → browser bundle under
  `docs/playground/pkg`.
- **`axeyum-property`**: `axeyum_property::{prove-style helpers}` plus
  `#[derive(Symbolic)]`.

## Tests and gates

Covered in full above (test suite census + feature-gate audit). One additional
mechanism worth naming here: `scripts/check-gate-liveness.sh` is the only gate
that actively defends against the zero-test failure mode by pinning a **minimum**
test count per suite via `cargo test -- --list` (compiles, does not run). Its
manifest (`check-gate-liveness.sh:60-75`) names exactly 16 entries: 13
`axeyum-solver` `test:*` targets plus `axeyum-solver|lib` (floor 900),
`axeyum-cnf|lib` (floor 300), `axeyum-rewrite|lib` (floor 1) — all under
`--features full` where applicable. None of the 28 z3-gated differential
suites, none of the 2 batsat-reference suites, and roughly 285 of the other
298 `full`-gated solver test files have a floor here; the script's own header
explains why the z3 ones are intentionally excluded ("`z3` is a C/C++ leaf
dependency and the default build must not require it… a floor here would fail
on a machine without libz3") and directs the reader to CLAUDE.md's explicit
z3-gate list instead of a floor.

Which gates catch a **wrong** sat/unsat vs. only a crash/timeout:
- **Catches a wrong verdict**: `corpus_regression` (`:status` disagreement,
  the incident `check-gate-liveness.sh`'s header documents at length), the
  28 z3-differential-fuzz suites (`DISAGREE` is fatal in `axeyum-bench` and in
  the fuzz harnesses), `axeyum-scenarios`-backed suites (self-check fails on a
  wrong verdict by construction — no external comparison needed), the DRAT/
  Alethe/Carcara/Lean reconstruction suites (an independently-checked proof
  that doesn't check is a wrong-verdict signal, not a crash), and
  `axeyum-search`'s `certify.rs`/`compose.rs` (re-derive from scratch, not
  from the producing run's output).
- **Catches only a crash, hang, or budget miss**: `progress_frontier`
  (capability/timing ratchets — a regression here is "fewer instances decided
  in budget," which can mean either a real capability loss or just slower
  code; it does not by itself distinguish "returned `unknown` because it ran
  out of budget" from "would have returned the wrong answer"), most of the
  ~285 unfloored `full`-gated suites (they run-or-don't; a suite emptied by a
  new `cfg` and one that still runs and passes are visually identical unless
  something checks the count, which `check-gate-liveness.sh` does for only 13
  of them), and any bench recipe without `--compare-z3` (records timing/
  decided-rate only).

## Doc drift

- `crates/axeyum-bench/README.md` and this brief's own text both describe
  `qfbv-profile`/`benchmark-repetition-tests`/`glaurung-qfbv-regular` type
  gates only implicitly; no drift found there — the README correctly says the
  main binary does the corpus/PAR-2/model-replay work and the examples are
  "not all stable user interfaces."
- CLAUDE.md's Commands section states `just check` and `check.sh` are "NOT the
  same gate… each missing something the other had," citing `check.sh` skipping
  "the Lean axiom ledger" and `just check` skipping "check-gate-liveness.sh."
  As read on 2026-09-09, `check-gate-liveness.sh` **is** invoked by both
  (`justfile:58` lists `gate-liveness` in `check:`'s prerequisite chain, and
  `check.sh:1261` runs `step gate-liveness ./scripts/check-gate-liveness.sh`
  directly). This specific example in CLAUDE.md is stale relative to the
  current source; the broader claim (the two gates diverge, verified counts
  differ) still holds — this lane's own reading found a different, currently-
  true instance of the same divergence shape (`qfbv-profile`,
  `benchmark-repetition-tests`, `glaurung-qfbv-regular` present only in
  `justfile`'s `check:`).
- ADR-0008 and ADR-1703 both resolve to real files
  (`docs/research/09-decisions/adr-0008-consumer-scenario-models.md`,
  `docs/research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md`)
  and their content matches how they're cited in this document; no drift
  found.

## Gaps and open questions

- **Exact solver test counts under `--features full` were not run** (hard
  constraint: no `cargo`). All "298 gated to zero" claims are about
  compilation gating from source, not about how many tests each file contains
  when built; `check-gate-liveness.sh`'s pinned floors (e.g. `lib|full|900`)
  are the closest committed proxy for actual counts, but that manifest covers
  only 16 of the ~600+ (302+11+7+2) integration files across the four crates
  in scope.
- **`axeyum-solver/Cargo.toml`'s exact `[dependencies]` vs `[dev-dependencies]`
  placement for `axeyum-scenarios`** was confirmed only by a single `grep -n`
  hit at line 76 showing the path entry; I did not re-read the surrounding
  section headers to confirm which stanza line 76 falls under. A caller citing
  "axeyum-scenarios is a dev-dependency of axeyum-solver" should re-check
  `crates/axeyum-solver/Cargo.toml`'s section boundaries directly.
- **`axeyum-machine-evidence`** (referenced once, as the crate that pairs with
  `axeyum-machine` to produce solver-checkable evidence) is outside this
  lane's named scope (the brief lists `axeyum-machine`, not
  `axeyum-machine-evidence`) and was not inventoried; a reader wanting the
  machine-semantics-to-solver-evidence route should treat that crate as
  unexamined here.
- **Whether `corpus/public-curated`'s 903 files and `corpus/regression`'s 152
  files are consumed by any named `just`/`check.sh` gate, or are ad hoc/manual
  corpora**, was not fully traced — `bench-qfbv-curated*` names
  `corpus/qfbv-curated` explicitly; I found no recipe naming
  `corpus/public-curated` or `corpus/regression` by path in the `justfile`
  slice read. This would need a full-file grep for those two path strings
  across `justfile` and `scripts/*.sh`, which was not completed given time
  budget — flagging as unconfirmed rather than asserting absence.
- **The ~110-name `check:` prerequisite list in `justfile:58` was read as a
  single grep match, not diffed line-by-line against `check.sh`'s full `step`
  list** (over 100 steps in `check.sh` covering non-solver areas). This
  document's divergence claim is scoped to the solver/harness-relevant subset
  named in the brief, not a full recount of the aggregate-scope divergence
  (that recount is `scripts/check-aggregate-scope.sh`'s job, per CLAUDE.md,
  and was not run here).
