# SAT core, CNF, and bit-blasting — inventory (2026-09-09)

Scope: the propositional layer at the bottom of the stack — `crates/axeyum-cnf`
(34 source files, 48,355 lines), `crates/axeyum-aig` (1,046 lines),
`crates/axeyum-bv` (5,218 lines) — plus the caller seam in
`crates/axeyum-solver/src/sat_bv_backend.rs` (4,258 lines), which is inventoried
here only as far as it names this layer's entry points. Lane L3 owns the solver
crate; lane L8 owns the wider evidence story. Base commit `ea8515407`. This is a
source-reading pass: no build was run, and every claim that would need one is
marked `[unverified]`.

## Summary

- **The native CDCL core is the SAT engine on the default path, and there is no
  second engine in the default dependency graph.** `SatBvBackend` dispatches
  unconditionally to `solve_with_drat_proof_with_limits`
  (`sat_bv_backend.rs:2769-2780`). `SolverConfig::native_cdcl` is a documented
  no-op read by nobody (`backend.rs:249-260`). BatSat survives only behind the
  non-default `batsat-reference` feature, which gates one module and one test
  file (below). ADR-1703 is implemented as written for slice 1; slice 2 (delete
  the adapter and the flag) has not happened.
- **The single largest reachability finding: `crates/axeyum-cnf/src/inprocess.rs`
  — the proof-carrying inprocessing module of ADR-1750 — has no caller outside
  this crate's own tests and examples.** The shipping SMT path reimplements the
  same three passes by hand in `sat_bv_backend::inprocess`
  (`sat_bv_backend.rs:1827-2083`), calling `simplify`, `vivify` and `bve`
  directly and stitching the certificate together with `ReductionLink` instead.
  Two independent inprocessing pipelines with different proof stories.
- **And that hand-rolled pipeline is off by default**: `SolverConfig::default()`
  sets `cnf_inprocessing: false` (`backend.rs:390`). `cnf_vivify: true`
  (`backend.rs:391`) is a no-op without it. So on a default `Solver` call, no
  subsumption, no vivification, no BVE, no compaction, and no XOR propagation
  runs — the Tseitin output goes straight to search.
- Reachability tally for `axeyum-cnf`, all 34 source files classified:
  **14 WIRED** to the default SMT path or to another production crate
  (`lib`, `proof_sat`, `proof_sat/incremental`, `clause_db_policy`,
  `phase_policy`, `interrupt`, `drat`, `drat_backward`, `lrat`, `alethe`,
  `reduction_link`, `xor_extract`, `interpolant`, `weighted`);
  **3 internal helpers** reachable only through a WIRED parent
  (`drat_resource`, `gf2`, `pass_work`);
  **7 CONFIG-GATED**, reachable only with a non-default `SolverConfig` lever
  (`simplify`, `vivify`, `bve`, `compact`, `xor_propagate`, `xor_cdcl`,
  `xor_drat`);
  **3 FEATURE-GATED** (`batsat_reference` under `batsat-reference`;
  `proof_sat/theory` and `proof_sat/refutation` under `full`);
  **6 TEST/BENCH/EXAMPLE-ONLY** (`inprocess`, `ticks`, `cube`, `colouring`,
  `xor_matrix`, `xor_search`);
  **1 NO PRODUCTION CALLER FOUND** (`xor_dpll`).
  Every row below cites the caller site.
- Proof pipeline at this layer: the core emits DRAT by construction; `check_drat`
  (`drat.rs`, ADR-0011) and the backward checker `check_drat_backward`
  (`drat_backward.rs`, ADR-0382) consume it; `elaborate_drat_to_lrat*`
  (`lrat.rs`) turns it into LRAT for `check_lrat`; `lrat_to_alethe` +
  `check_alethe` (`alethe.rs`) is the Alethe leg. The default SMT `unsat` route
  checks DRAT **inline** in `solve_with_native_cdcl` and never re-derives
  (`sat_bv_backend.rs:2812`, `2874-2891`).
- Two doc-drift findings against `docs/internals/cnf-and-sat.md`, one nit against
  `docs/internals/bit-blasting.md` (details in **Doc drift**). One stale comment
  inside `inprocess.rs` itself.
- `ticks.rs` describes itself as the unit "every budget denominated in ticks"
  uses (`proof_sat.rs:1537`); no budget on any shipping path is denominated in
  ticks — every budget is in **conflicts**. `TickModel` has two consumers, both
  a test and an example.
- ADR numbers cited here were each confirmed to resolve to a file in
  `docs/research/09-decisions/`: 0006, 0007, 0009, 0011, 0012, 0035, 0300, 0381,
  0382, 1701, 1703, 1704, 1722, 1750.

## Inventory

### CDCL core and proof output

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `proof_sat` | `crates/axeyum-cnf/src/proof_sat.rs` | 8,333 | The CDCL core: flat clause arena, blocking-literal watches, 1-UIP analysis, VSIDS, Luby restarts, LBD tiers, `reduce_db`, DRAT emission (ADR-0012) | WIRED | `sat_bv_backend.rs:2780` calls `solve_with_drat_proof_with_limits`; that is the only primary search (`primary_sat_search`, `sat_bv_backend.rs:2669-2690`) |
| `proof_sat::incremental` | `crates/axeyum-cnf/src/proof_sat/incremental.rs` | 640 | `NativeIncrementalCdcl`: warm solver, `solve_assuming`, failed-assumption core, optional proof recording (ADR-1703 §1) | WIRED | `IncrementalSat` wraps it (`lib.rs:694`); `dpll_lia.rs` uses `IncrementalSat` (4 sites) |
| `proof_sat::theory` | `crates/axeyum-cnf/src/proof_sat/theory.rs` | 284 | `NativeTheory` / `NullTheory` / propagation queue / lazy explanation (ADR-1701) | FEATURE-GATED (`full`) | Only consumer is `axeyum-solver/src/native_cdclt.rs:41`, and `mod native_cdclt` sits under `#[cfg(feature = "full")]` (`axeyum-solver/src/lib.rs:70`, `:148`). Every non-theory entry point attaches `NullTheory`, so `THEORY_STEP_BUDGET` is compiled out on shipping paths (`proof_sat.rs:76`) |
| `proof_sat::refutation` | `crates/axeyum-cnf/src/proof_sat/refutation.rs` | 400 | `TheoryRefutation`: the ADR-1704 two-stream artifact (Boolean proof + enumerated theory lemmas) | FEATURE-GATED (`full`) | `native_cdclt.rs:75`, `:107`; `trust.rs:456` grades it |
| `SearchPolicies` | `proof_sat.rs:555-620` | — | Clause-DB and phase heuristics as objects | WIRED (default arm only) | `SearchPolicies::default()` = `ClauseDbPolicy::tiered()` + `PhasePolicy::pinned()` (`proof_sat.rs:563-579`). The non-default arms (`legacy`, `legacy_clause_db`, `scheduled_phase`, `releasing_phase`) have exactly one caller: `crates/axeyum-cnf/examples/clause_db_policy_ab.rs` (15 hits) |
| `clause_db_policy` | `crates/axeyum-cnf/src/clause_db_policy.rs` | 1,066 | Tier scheme, keep reasons, delete fraction, watch sweep | WIRED via `SearchPolicies::default` | `proof_sat.rs:28` imports it; `proof_sat.rs:571` selects `tiered()` |
| `phase_policy` | `crates/axeyum-cnf/src/phase_policy.rs` | 308 | Target/best phase split and rephase schedule | WIRED via `SearchPolicies::default`, **but the default arm never fires** | `PhasePolicy::pinned()` is the default (`proof_sat.rs:572`) and `pinned_policy_never_rephases` pins that `should_rephase` is always `false` (`phase_policy.rs:225-228`). `Cdcl::use_target_rephase` defaults `true` (`proof_sat.rs:2169`) but is gated on `should_rephase` at `proof_sat.rs:3053` |
| `interrupt` | `crates/axeyum-cnf/src/interrupt.rs` | 87 | Embedder-installed "stop now" `fn() -> bool` consulted alongside the deadline | WIRED | `axeyum-solver/src/portfolio.rs:405` installs `axeyum_ir::stop::stop_requested`; consumed at `proof_sat.rs:2954` and `:3217` |
| `ticks` | `crates/axeyum-cnf/src/ticks.rs` | 405 | `TickModel`: a cache-aware deterministic work proxy derived from `SearchCounters` | TEST-ONLY | Consumers: `crates/axeyum-cnf/tests/deterministic_work_budget.rs:26` and `crates/axeyum-cnf/examples/clause_db_policy_ab.rs:406`. Inside `proof_sat.rs` the only references are a doc comment and a `const _: () = assert!` on `Watch` width (`:1537`, `:1552-1557`) — no budget consumes ticks |
| `batsat_reference` | `crates/axeyum-cnf/src/batsat_reference.rs` | 306 | The retired `rustsat-batsat` adapter (ADR-0007), kept as a differential oracle (ADR-1703) | FEATURE-GATED (`batsat-reference`) | `#[cfg(feature = "batsat-reference")] pub mod batsat_reference;` (`lib.rs:44-45`); feature declared at `crates/axeyum-cnf/Cargo.toml:24` and forwarded by `axeyum-solver/Cargo.toml:49`, `axeyum-bench/Cargo.toml:33` |

### DRAT / LRAT / Alethe production and checking

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `drat` | `crates/axeyum-cnf/src/drat.rs` | 2,028 | `DratStep`, `DratSink` (`VecProofSink`/`TextProofSink`/`BinaryProofSink`), text + binary I/O, forward RUP/RAT checker `check_drat`, streaming checker, `CacheDroppingWriter` (unix) — ADR-0011, ADR-0381 | WIRED | `check_drat` at `sat_bv_backend.rs` (18 hits, incl. `:2253`), `axeyum-solver/src/proof.rs`, `trust.rs`, `evidence.rs`. `write_drat` at `sat_bv_backend.rs:2258` |
| `check_drat_streaming` | `drat.rs:111` | — | Iterator-fed bounded-memory checker | EXAMPLE-ONLY (direct callers) | Only direct caller found: `crates/axeyum-cnf/examples/drat_memory_probe.rs:152`. `check_drat` itself routes through it (`drat.rs:86`), so the code is exercised; the *streaming* entry is not called from production |
| `drat_backward` | `crates/axeyum-cnf/src/drat_backward.rs` | 2,866 | Backward, core-first DRAT checking and `trim_drat_proof` (ADR-0382) | WIRED | `check_drat_backward` in `axeyum-solver/src/proof.rs` (3 hits) and `axeyum-search/src/{simd,job_shop,multiplicative_circuit}.rs`. `trim_drat_proof`: **NO CALLER FOUND** — searched `grep -rn --include='*.rs' '\btrim_drat_proof\b' crates/`, the only hits are its own definition (`drat_backward.rs:1022`), two doc comments in the same file, and the `pub use` at `lib.rs:107` |
| `drat_resource` | `crates/axeyum-cnf/src/drat_resource.rs` | 1,000 | Proof-shape and memory model, route choice, budget decline (`DratMemoryModel`, `MemoryBudget`, `BackwardCheckOutcome`) | WIRED via `drat_backward` | `drat_backward.rs:61-63` imports it. Direct external use is test/example only: `tests/drat_memory_model.rs` (7), `examples/drat_memory_probe.rs`, plus a `config_registry.rs` prose reference |
| `lrat` | `crates/axeyum-cnf/src/lrat.rs` | 2,026 | LRAT checker (`check_lrat`, RUP **and** RAT) and DRAT→LRAT elaborators, forward and backward (`certify_unsat_via_lrat`, ADR-0382/0613/1722) | WIRED | `check_lrat` in `axeyum-solver/src/proof.rs` (20 hits) and `evidence.rs`; `certify_unsat_via_lrat` only in `proof.rs` (5) |
| `alethe` | `crates/axeyum-cnf/src/alethe.rs` | 5,152 | Alethe parse/write/check; resolution rules discharged by re-solving with the proof core and re-checking with `check_drat`; `lrat_to_alethe` | WIRED | `check_alethe` in `axeyum-solver/src/evidence.rs` (23), `euf_alethe.rs` (20), `smtlib.rs` (10); `write_alethe` in `smtlib.rs` (9) |
| `reduction_link` | `crates/axeyum-cnf/src/reduction_link.rs` | 762 | `ReductionLink`/`LiftingSink`/`ProofCoverage`: concatenates a reduction prefix with the search's steps and reports which formula the check covered | WIRED | `sat_bv_backend.rs:2811-2812` (`link.check_unsat(...)`), coverage recorded at `:2701-2730` |
| `xor_drat` | `crates/axeyum-cnf/src/xor_drat.rs` | 567 | `xor_gauss_drat_refutation`: DRAT refutation of a Gaussian conflict subset, width-capped by `MAX_XOR_WIDTH` (ADR-0035) | CONFIG-GATED + FEATURE-GATED | Production path: `sat_bv_backend.rs:2246` inside `pure_gauss_xor_unsat_certificate`, called from `certify_pure_gauss_xor_unsat` at `:2161`, which is inside `maybe_xor_cdcl_fallback` — gated on `config.xor_cdcl_fallback`, default `false` (`backend.rs:397`). Second route `pure_gauss_xor_unsat_certificate_for_query` is `#[cfg(feature = "full")]` (`sat_bv_backend.rs:2273`), used by `evidence.rs:2135` |

Note on a stale registry entry: `axeyum-solver/src/config_registry.rs:1407` says
`xor_gauss_drat_refutation` is "Not yet called from production dispatch (only
tests)". It *is* called from `sat_bv_backend.rs:2246`, behind a default-off
config lever. That file belongs to lane L3; recorded here because the claim is
about this layer.

### Inprocessing and simplification

The classification below is the highest-value part of this lane, so state the
gate once: **all five reducing passes are reachable from `SatBvBackend` only
through `maybe_inprocess`, which returns `None` immediately unless
`config.cnf_inprocessing` is set (`sat_bv_backend.rs:1221-1229`), and
`SolverConfig::default()` sets it `false` (`backend.rs:390`).** No front door in
`axeyum-solver` turns it on: `grep -rn 'with_cnf_inprocessing\|cnf_inprocessing
= true\|cnf_inprocessing: true' crates/` returns the builder definition itself,
`axeyum-solver/tests/sat_bv.rs` (8 sites), `axeyum-solver/src/sat_bv_backend.rs`
unit tests (2), `axeyum-bench/examples/inprocess_ab.rs`,
`axeyum-bench/examples/smtcomp_cli.rs:1595`/`:1600`, and the `--inprocess` CLI
flag at `axeyum-bench/src/main.rs:411`.

| Pass | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `inprocess` (the ADR-1750 module) | `crates/axeyum-cnf/src/inprocess.rs` | 485 | Runs subsume/vivify/BVE and emits one DRAT stream that checks against the **original** formula; `InprocessOptions`, `inprocess_into` | **TEST/EXAMPLE-ONLY** | `grep -rn '\binprocess_into\b' crates/` outside `axeyum-cnf/src`: `crates/axeyum-cnf/examples/inprocess_profile.rs:161`, `examples/inprocess_pass_cost.rs:149`/`:158`, `tests/inprocess_proof_path.rs` (5 sites). Inside the crate its only caller is `proof_sat.rs:696`/`:737` (`solve_with_drat_proof_counted_inprocessed` / `..._inprocessed`), and **those two entry points are themselves example/test-only**: `examples/inprocess_proof_check.rs:71`, `tests/inprocess_proof_path.rs:244`/`:269`/`:800` |
| `simplify` (subsumption + SSR) | `crates/axeyum-cnf/src/simplify.rs` | 1,132 | Forward subsumption and self-subsuming resolution, work-budgeted, optional step recording | CONFIG-GATED (`cnf_inprocessing`) | `sat_bv_backend.rs:1678` (`simplify_with_options`), `:1706` (`simplify_within_recorded`), both reached from `inprocess()` at `:1918-1924` |
| `vivify` | `crates/axeyum-cnf/src/vivify.rs` | 858 | Clause vivification, model-preserving, emits `Add`+`Delete` | CONFIG-GATED (`cnf_inprocessing` **and** `cnf_vivify`) | `sat_bv_backend.rs:1773` inside `maybe_vivify`, which returns early unless `config.cnf_vivify` (`:1770`); `maybe_vivify` is called only from `inprocess()` (`:1946`). Also used by `axeyum-search/examples/synthesize_primates_inverse.rs:393` |
| `bve` | `crates/axeyum-cnf/src/bve.rs` | 1,240 | Bounded variable elimination + `Reconstruction` model lift | CONFIG-GATED (`cnf_inprocessing`) | `sat_bv_backend.rs:1647` (`eliminate_variables_within`), `:1734` (`..._recorded`), from `inprocess()` at `:1954-1962` |
| `compact` | `crates/axeyum-cnf/src/compact.rs` | 430 | Dense renumbering of live variables + `CompactMap` lift | CONFIG-GATED (`cnf_inprocessing`) | `sat_bv_backend.rs:2020` |
| `pass_work` | `crates/axeyum-cnf/src/pass_work.rs` | 310 | `PassWork` meter shared by `simplify` and `bve` (work budget, progress marks, dead-entry compaction) | WIRED via those two passes only | `simplify.rs:58`, `bve.rs:82`. No caller outside `axeyum-cnf` — searched `grep -rn '\bPassWork\b' crates/`, all hits are in `pass_work.rs`, `simplify.rs`, `bve.rs`, `lib.rs:64` |

### XOR / Gaussian family

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `gf2` | `crates/axeyum-cnf/src/gf2.rs` | 758 | `Gf2System`: GF(2) Gaussian elimination, `unsat_reason_subset` provenance | WIRED via `xor_extract` | `xor_extract.rs:42`, `xor_search.rs:65`, `xor_propagate.rs:49` |
| `xor_extract` | `crates/axeyum-cnf/src/xor_extract.rs` | 531 | Recovers XOR gates from clause sets into a `Gf2System` | WIRED | `sat_bv_backend.rs:2134` (fallback admission) and `:2243` (certificate build) |
| `xor_propagate` | `crates/axeyum-cnf/src/xor_propagate.rs` | 393 | Gaussian-implied unit clauses appended to the formula | CONFIG-GATED (`cnf_inprocessing`) | `sat_bv_backend.rs:1858`, inside `inprocess()`; additionally capped at `XOR_PROPAGATE_MAX_CLAUSES = 20_000` (`:1188`) and **skipped entirely when `prove_unsat` is set**, because a Gaussian-implied unit is not RUP (`:1907-1917`) |
| `xor_cdcl` | `crates/axeyum-cnf/src/xor_cdcl.rs` | 1,543 | Competitive CDCL(XOR) search core (ADR-0035) | CONFIG-GATED (`xor_cdcl_fallback`, default `false`) | `sat_bv_backend.rs:2147`, reached from `:340-341` only when the primary search returned `Unknown` **and** `config.xor_cdcl_fallback`; capped at `XOR_CDCL_FALLBACK_MAX_CLAUSES = 50_000` (`:1196`). Also `axeyum-bench/examples/xor_cdcl_probe.rs:28` |
| `xor_dpll` | `crates/axeyum-cnf/src/xor_dpll.rs` | 662 | `solve_with_xor`: naive DPLL(XOR) reference decider | **NO PRODUCTION CALLER FOUND** | Searched `grep -rn '\bsolve_with_xor\b' crates/`. Hits: its own definition (`xor_dpll.rs:100`), the `pub use` (`lib.rs:154`), one doc comment (`xor_cdcl.rs:9`), and one `#[cfg(test)]` use as the differential reference for `xor_cdcl` (`xor_cdcl.rs:1070`, `:1473`) |
| `xor_search` | `crates/axeyum-cnf/src/xor_search.rs` | 881 | `xor_implications`: pure propagation oracle over a GF(2) system | TEST/BENCH-ONLY (transitively) | Its two consumers are `xor_dpll.rs:46` (no production caller, above) and `xor_matrix.rs:101` (bench-only, below). `grep -rn '\bxor_implications\b' crates/` finds no caller outside `axeyum-cnf` |
| `xor_matrix` | `crates/axeyum-cnf/src/xor_matrix.rs` | 1,595 | `IncrementalXorMatrix`: watched-row RREF over GF(2) with backtrackable steps | **BENCH-ONLY** | `grep -rn 'IncrementalXorMatrix' crates/` outside `xor_matrix.rs`: `lib.rs:157` (re-export), four doc references in `xor_drat.rs`, and `crates/axeyum-cnf/benches/xor_matrix_gauss.rs:125`/`:150`. That bench's own header says the module "had no bench" before 2026-09 and is the positive control for the `target-cpu` axis |

### The rest of `axeyum-cnf`

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `lib.rs` core types | `crates/axeyum-cnf/src/lib.rs` | 7,041 | `CnfVar`/`CnfLit`/`CnfClause`/`CnfFormula`/`CnfAssignment`, DIMACS I/O, `SatResult`/`SatError`, the Tseitin encoder and `CnfEncoding`, `IncrementalSat`, `IncrementalCnf` | WIRED | `tseitin_encode` at `sat_bv_backend.rs:164`; `IncrementalCnf` in `axeyum-solver/src/incremental.rs:797`, re-exported as `IncrementalBvSolver` (`axeyum-solver/src/lib.rs:928`) |
| `SatSolver` trait + `NativeCdclSolver` | `lib.rs:456`, `:565-591` | — | Capability-reporting object wrapper over `solve_with_native_core` | **NO CALLER FOUND** outside the crate | Searched `grep -rn '\bSatSolver\b\|\bNativeCdclSolver\b' crates/`. Hits: the trait and impl in `lib.rs`, the `impl` in `batsat_reference.rs:88` (feature-gated), and `lib.rs:6194` under `#[cfg(test)]`. `SatBvBackend` calls the free functions, not the trait |
| `cube` | `crates/axeyum-cnf/src/cube.rs` | 1,863 | Cube-and-conquer: augmented/covering formulas, refutation-tree checking incl. a parallel reader tree with progress | EXAMPLE + TEST-ONLY | `crates/axeyum-cnf/examples/{emit,check}_boolean_product_*.rs` (4 files); `axeyum-search/src/tensor_decomposition.rs:902` and `job_shop.rs:3342` are both inside `#[cfg(test)]` modules |
| `colouring` | `crates/axeyum-cnf/src/colouring.rs` | 1,354 | Ramsey/Schur/van-der-Waerden/Rado colouring encoders | TEST-ONLY (for this crate) | Only consumer of `axeyum_cnf::colouring` is `crates/axeyum-cnf/tests/colouring_encoding_parity.rs:38`, a differential gate against the generator. `axeyum-search` has its own separate `colouring` module (`axeyum-search/src/colouring.rs`) — do not confuse the two |
| `weighted` | `crates/axeyum-cnf/src/weighted.rs` | 355 | `encode_weighted_at_most`: weighted at-most-k CNF encoding | WIRED (into `axeyum-search`, not the SMT path) | `axeyum-search/src/colouring.rs`, `axeyum-search/src/simd_synthesis.rs`. No caller in `axeyum-solver` |
| `interpolant` | `crates/axeyum-cnf/src/interpolant.rs` | 694 | `propositional_interpolant{,_certified}`: McMillan interpolation from a resolution refutation | WIRED | `axeyum-solver/src/lra_interpolant_cnf.rs` (4), `bv_interpolant.rs` (3) |

### AIG layer (`crates/axeyum-aig`, 1,046 lines, single file)

| Component | Path | Role | Reachability | Evidence |
|---|---|---|---|---|
| `Aig` graph + `AndUniqueTable` | `crates/axeyum-aig/src/lib.rs:136`, `:270` | Structural hashing, constant folding, dense node IDs | WIRED | `axeyum-bv` builds every circuit through it; `axeyum-cnf::tseitin_encode(aig, roots)` reads it |
| Derived operators | `lib.rs:420` (`or`), `:425` (`xor`), `:450` (`mux`) | Built from the AND/inverter basis | WIRED | Used throughout `axeyum-bv`; e.g. equality is `xor(...).negated()` (`axeyum-bv/src/lib.rs:1601`, `:2140`, `:2750`) |
| `eval` / `eval_many` | `lib.rs:606`, `:617` | Circuit evaluation for replay | WIRED | `CnfEncoding::assignment_from_aig_inputs` (`axeyum-cnf/src/lib.rs:2713`) |
| `to_aiger_ascii` | `lib.rs:628` | ASCII AIGER debug export | WIRED (Python binding only) | Only caller: `axeyum-py/src/ir/lowering.rs:173` |
| `and_unique_table` bench | `crates/axeyum-aig/benches/and_unique_table.rs` | Micro-bench (2026-09-05) | BENCH | `Cargo.toml` `[[bench]]` |

There is **no `tests/` directory** in `axeyum-aig`; the crate's coverage is its
own `#[cfg(test)]` module plus whatever `axeyum-bv` and `axeyum-cnf` exercise.

### Bit lowering (`crates/axeyum-bv`, 5,218 lines, single file)

| Entry point | Path | Role | Reachability | Evidence |
|---|---|---|---|---|
| `lower_terms` | `lib.rs:55` | One-shot eager lowering | WIRED | `sat_bv_backend.rs:2283`; also `proof.rs`, `bv_interpolant.rs`, `axeyum-py/src/ir/lowering.rs` |
| `lower_terms_with_deadline` | `lib.rs:112` | Default backend route for `BitLoweringMode::Eager` | WIRED | `sat_bv_backend.rs:197` |
| `lower_terms_with_deadline_profiled` | `lib.rs:284` | Eager + demand profiling | CONFIG-GATED (`profile_bit_demand`) | `sat_bv_backend.rs:194-195` |
| `lower_terms_demanded_with_deadline` | `lib.rs:130` | Demand-sliced | CONFIG-GATED (`BitLoweringMode::DemandSliced`) | `sat_bv_backend.rs:191-192` |
| `lower_terms_range_demanded_with_deadline` | `lib.rs:253` | Range-sliced, `RangeDemandPolicy` | CONFIG-GATED (`BitLoweringMode::RangeSliced`) | `sat_bv_backend.rs:188-189` |
| `lower_terms_demanded`, `lower_terms_profiled`, `lower_terms_range_demanded` | `lib.rs:74`, `:91`, `:240` | Deadline-free variants | TEST/BENCH-ONLY | `grep -rn` finds callers only in `axeyum-bv/src/lib.rs` `#[cfg(test)]` (`:4507`, `:4726`, `:4758`, `:4988`) and `benches/bv_lowering.rs` |
| `IncrementalLowering` | `lib.rs:899` | Persistent AIG across related checks (ADR-0009 st.2) | WIRED | `axeyum-solver/src/incremental.rs:796`, `:842` |
| `eval_lowered_once` | `lib.rs:4069` | Ground evaluation helper | TEST-ONLY | Only caller: `axeyum-bv/src/lib.rs:5214`, inside `#[cfg(test)]` |
| `first_unsupported_op` / `first_unsupported_sort` | `lib.rs:298`, `:321` | Admission screen before lowering | WIRED | `sat_bv_backend.rs:104`, `:110` (in `check_with_replay_internal`) |
| `BitLowering` lift maps | `lib.rs:552-567`, `:673` | `aig()`, `roots()`, `term_bits()`, `symbol_inputs()`, `assignment_from_aig_values` | WIRED | `sat_bv_backend.rs:2376-2380` |

## Data flow

Default path, `SatBvBackend::check` → `check_with_replay_internal`
(`sat_bv_backend.rs:87-360`), in call order:

1. **Admission.** `first_unsupported_op` / `first_unsupported_sort`
   (`:104`, `:110`), `TermStats::compute` node budget (`:117-122`),
   `MemoryBudget::from_config` (`:131`), `oversized_encoding_refusal` (`:138`).
   Any failure is `unknown`, never a verdict.
2. **Bit lowering.** `axeyum-bv`, entry chosen by `config.bit_lowering_mode`
   (`:101-112`; default `Eager` → `lower_terms_with_deadline`). Produces a
   `BitLowering`: the `Aig`, one `LoweredTerm` per root, `term_bits`,
   `symbol_inputs`. Bit vectors are LSB-first (ADR-0006).
3. **Tseitin.** `tseitin_encode(lowering.aig(), &roots)` (`:164`), or
   `tseitin_encode_profiled_with_origins` under `profile_cnf_construction`
   (`:159`). Returns `CnfEncoding` = formula + `roots: Vec<CnfRoot>` +
   `reachable_nodes: Vec<bool>` + **`variable_bindings: Vec<CnfVarBinding>`**,
   which is the CNF-var → AIG-literal replay map (`axeyum-cnf/src/lib.rs:2680-2705`).
   Assertion-only roots may be folded into child clauses rather than getting a
   dedicated variable and unit clause (`lib.rs:2782-2789`).
4. **Inprocessing (skipped by default).** `maybe_inprocess` (`:204`) → `inprocess`
   (`:1827`) when `cnf_inprocessing`. Stage order inside: `xor_propagate` →
   `simplify` → `maybe_vivify` → `bve` → `compact`, each timed separately, with
   the reduction prefix recorded into a `ReductionLink` only when
   `config.prove_unsat` (`:1911`, `:1919-1923`, `:2015-2019`).
5. **Budget check.** `check_cnf_budgets` (`:209`) against
   `cnf_variable_budget` / `cnf_clause_budget`.
6. **Search.** `primary_sat_search` (`:235`) → `solve_with_native_cdcl`
   (`:2768`) → `axeyum_cnf::solve_with_drat_proof_with_limits` (`:2780`), whose
   budget is `config.resource_limit` in **conflicts**, defaulting to
   `DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000` (`proof_sat.rs:46`).
7. **XOR fallback (off by default).** On `Unknown` and `config.xor_cdcl_fallback`
   (`:340`), `maybe_xor_cdcl_fallback` runs `solve_with_xor_cdcl`; a pure-Gauss
   level-0 conflict is certified by `xor_gauss_drat_refutation` + `check_drat`
   and only then stamped `Checked` (`:2161-2172`).
8. **`unsat`.** The proof is verified in place by
   `ReductionLink::check_unsat(original, formula, &proof, MAX_LINKED_PROOF_STEPS)`
   (`:2812`, cap `8_000_000` at `:1179`), producing a `ProofCoverage` that says
   whether the check covered the caller's formula or only the reduced one
   (`:2701-2730`). A proof that fails to check downgrades to `Unknown`
   (`:2833`), never to an accepted `unsat`. `ensure_unsat_proof_checked`
   (`:2874`) short-circuits when the inline check already stamped `Checked`.
9. **`sat` replay.** `handle_sat_result` (`:2347`):
   `CnfEncoding::aig_node_values_from_assignment` first re-checks that the
   assignment satisfies the CNF, then lifts each bound CNF variable onto its AIG
   node and replays the remaining reachable AND gates
   (`axeyum-cnf/src/lib.rs:2749-2772`); then
   `BitLowering::assignment_from_aig_values` recovers typed source values;
   then `complete_model`; then `replay_model` evaluates the **original** terms
   (`:2424`). A model that cannot be evaluated becomes `Unknown`; a model that
   evaluates to `false` is a `SolverError`, not a verdict.

Proof-artifact flow at this layer, by route:

| Route | Producer | Consumer / checker |
|---|---|---|
| DRAT (in RAM) | `solve_with_drat_proof*` → `VecProofSink` | `check_drat` (`drat.rs:86`), or `check_drat_backward` (`drat_backward.rs`) |
| DRAT (streamed) | `solve_with_drat_proof_streaming` → `TextProofSink` / `BinaryProofSink` (ADR-0381) | `DratTextReader` + `check_drat_streaming*`; `check_drat_backward_reader*` for the file case |
| DRAT with a reduction prefix | `inprocess_into` prefix + search steps into one sink (ADR-1750), or `ReductionLink` on the solver side | `check_drat` against the **original** formula; `ReductionLink::check_unsat` reports coverage |
| LRAT | `elaborate_drat_to_lrat*` / `certify_unsat_via_lrat` (backward, ADR-0382) | `check_lrat` — hint-following, no search |
| Alethe | `lrat_to_alethe` | `check_alethe` / `check_alethe_with`; `CARCARA_CHECKED_RULES` marks which rules an external Carcara run covers |
| XOR Gaussian | `xor_gauss_drat_refutation` (ADR-0035) | `check_drat` on `CNF(S)` before the certificate is returned (`sat_bv_backend.rs:2248-2256`) |
| CDCL(T) two-stream | `TheoryRefutation` (ADR-1704) | `check_drat`/`check_lrat` over CNF **plus** the enumerated lemmas as input clauses; lemmas discharged per-theory |

## Entry points and public API

`axeyum-cnf` re-exports at `lib.rs:82-161`. The ones a caller outside the crate
actually uses today:

- **Solve, one-shot:** `solve_with_native_core{,_timeout,_limits}`,
  `solve_with_drat_proof{,_within,_with_limits,_streaming,_counted,...}`.
- **Solve, warm:** `IncrementalSat` (clauses + assumptions),
  `NativeIncrementalCdcl` (the raw object), `IncrementalCnf` (per-node Tseitin
  over the warm solver, ADR-0009).
- **Encode:** `tseitin_encode`, `tseitin_encode_profiled`,
  `tseitin_encode_profiled_with_origins`, `parse_dimacs`,
  `CnfFormula::to_dimacs`, `reachable_node_mask`.
- **Reduce:** `simplify*`, `vivify*`, `eliminate_variables*`, `compact`,
  `inprocess_into` (the last has no production caller).
- **Prove/check:** `check_drat*`, `check_drat_backward*`, `write_drat*`,
  `parse_drat*`, `check_lrat`, `elaborate_drat_to_lrat*`,
  `certify_unsat_via_lrat`, `check_alethe*`, `write_alethe`, `parse_alethe`,
  `lrat_to_alethe`, `ReductionLink`, `propositional_interpolant*`.
- **XOR:** `extract_xors`, `xor_propagate`, `solve_with_xor_cdcl`,
  `xor_gauss_drat_refutation`, `Gf2System`.
- **Control:** `interrupt::set_stop_hook`, `ticks::TickModel`,
  `DratMemoryModel`/`MemoryBudget`.

`axeyum-aig` exposes `Aig` and its constructors only — no feature flags, no
optional dependencies. `axeyum-bv` exposes the `lower_terms*` family,
`BitLowering`, `IncrementalLowering`, and the two admission screens; it depends
only on `axeyum-ir`, `axeyum-aig` and `web-time`, so ADR-0006's crate boundary
still holds (no reverse edge from `axeyum-bv` into `axeyum-cnf` or the solver).

## Tests and gates

| Suite | Path | Lines | What it covers | Gating |
|---|---|---|---|---|
| `inprocess_proof_path` | `crates/axeyum-cnf/tests/inprocess_proof_path.rs` | 818 | ADR-1750: every pass prefix checks against the original; LRAT elaboration of the concatenated stream | none |
| `colouring_encoding_parity` | `.../colouring_encoding_parity.rs` | 536 | Rust colouring encoder vs. the reference generator | none |
| `drat_backward_file_differential` | `.../drat_backward_file_differential.rs` | 428 | Backward file checker vs. the in-RAM route | none |
| `deterministic_work_budget` | `.../deterministic_work_budget.rs` | 345 | `SearchCounters` determinism and the `TickModel` breakdown | none |
| `drat_memory_model` | `.../drat_memory_model.rs` | 326 | `DratMemoryModel` estimates vs. observed route choice | none |
| `math_resource_boolean_routes` | `.../math_resource_boolean_routes.rs` | 321 | Committed math corpora through the DRAT/LRAT routes | none |
| `propositional_interpolant_certified` | `.../propositional_interpolant_certified.rs` | 309 | Interpolant certificate + DRAT | none |
| `theory_lemma_proof_contract` | `.../theory_lemma_proof_contract.rs` | 291 | ADR-1704 boundary: what a CDCL(T) `unsat` artifact must carry | none |
| `interpolant` | `.../interpolant.rs` | 271 | McMillan interpolation | none |
| `native_vs_batsat_differential` | `.../native_vs_batsat_differential.rs` | 245 | Native core vs. the retired adapter on identical CNF | **`#![cfg(feature = "batsat-reference")]` at line 42 — compiles to ZERO tests and exits 0 without `--features batsat-reference`**; the file's own header says so at lines 4-17 |
| `vivify` | `.../vivify.rs` | 164 | Vivification pass | none |

Benches (`harness = false`, criterion): `proof_sat_solve`, `tseitin_encode`,
`proof_pipeline`, `proof_sat_propagate`, `xor_matrix_gauss` in `axeyum-cnf`;
`and_unique_table` in `axeyum-aig`; `bv_lowering` in `axeyum-bv`. The last two
crates were added benches only in September 2026, per their own `Cargo.toml`
comments — `axeyum-bv` "had no benches at all before that date, despite ADR-0300
measuring bit lowering plus CNF encoding at ~84% of the cold pipeline"
(`crates/axeyum-bv/Cargo.toml:32-35`).

Fourteen examples ship in `axeyum-cnf/examples/`. Five of them
(`inprocess_profile`, `inprocess_pass_cost`, `inprocess_proof_check`,
`clause_db_policy_ab`, `boolean_core_profile`) are the **only** consumers of
several modules in the tables above, which is why those rows read
EXAMPLE-ONLY rather than WIRED.

Only one suite in this lane is feature-gated to zero tests
(`native_vs_batsat_differential`). `axeyum-cnf` has no `full` feature; the
`full`-gated pieces in scope are on the `axeyum-solver` side
(`native_cdclt`, `pure_gauss_xor_unsat_certificate_for_query`).

## Doc drift

### `docs/internals/cnf-and-sat.md` (146 lines, last touched 2026-09-06)

Mostly current — the ADR-1703 sections are accurate and specific. Two real
drifts and one soft one:

1. **Line 132-134 is wrong about the LRAT checker.** The doc says the crate can
   "elaborate supported **RUP-only** DRAT proofs into LRAT, check that
   positive-hint LRAT slice… RAT additions (negative hints) are outside the
   current LRAT checker **and** elaborator and are rejected rather than silently
   accepted." The checker gained RAT under ADR-1722: `LratStep::AddRat` with a
   pivot and per-candidate hint blocks exists at `lrat.rs:59-70`, and
   `verify_rat_addition` (`lrat.rs:325`) checks it — enforcing candidate
   exhaustiveness itself rather than trusting the proof (`lrat.rs:312-317`).
   The module header states the split plainly: `check_lrat` and
   `elaborate_drat_to_lrat` "support both RUP additions … and RAT additions",
   while only the **backward** elaborator
   (`elaborate_drat_to_lrat_backward`/`certify_unsat_via_lrat`) "still declines a
   RAT core lemma" (`lrat.rs:11-20`). The doc's sentence is right for the
   backward elaborator and wrong for the checker.

2. **Line 36's "EMA-glue implemented and selectable" overstates "selectable".**
   `Cdcl::use_ema_restart` defaults to `false` (`proof_sat.rs:2178`) and the only
   assignment to it anywhere is `proof_sat.rs:5425`, inside the crate's own
   `#[cfg(test)]` module. There is no public setter, no `SearchPolicies` field,
   and no `SolverConfig` lever: searched `grep -n 'use_ema_restart'
   crates/axeyum-cnf/src/proof_sat.rs`, which returns the field declaration, the
   default, two read sites (`:2686`, `:3235`), and the test. It is implemented,
   but not selectable by any caller outside this crate's tests.

3. **Softer, line 36 and lines 55-58.** "phase saving plus target rephasing" is
   true of the machinery and false of the default behaviour: the shipped
   `SearchPolicies::default()` uses `PhasePolicy::pinned()`, whose own test is
   named `pinned_policy_never_rephases` (`phase_policy.rs:225`), and
   `proof_sat.rs:566-573` says the pinned default "flips only when the
   measurement says it should". Likewise "CNF preprocessing includes bounded
   variable elimination, subsumption, vivification, and compaction" is true of
   the crate and misleading about the product: none of it runs unless a caller
   sets `cnf_inprocessing`, which `SolverConfig::default()` does not
   (`backend.rs:390`). Neither statement is false as written; both would mislead
   a reader trying to reason about a default run.

Also missing rather than stale: the doc does not mention `inprocess.rs` or
ADR-1750 at all, so a reader cannot tell that the crate has a proof-carrying
inprocessing entry point distinct from the solver's hand-rolled one.

### `docs/internals/bit-blasting.md` (61 lines, last touched 2026-08-07)

**No drift found.** Every structural claim checks out against source:
`AigLit` is a node plus an inversion bit (`axeyum-aig/src/lib.rs:50-56`); nodes
are constants, inputs, or two-input ANDs (`:109`); OR/XOR/MUX are derived
(`:420`, `:425`, `:450`); structural hashing and `x & true = x` folding live in
`AndUniqueTable` (`:136`) and `Aig::and` (`:345`); ASCII AIGER export exists
(`:628`); `BitLowering` retains the AIG and roots, `term_bits`, `symbol_inputs`,
and demand/memo statistics (`axeyum-bv/src/lib.rs:552-567`, `:409`, `:500`);
one-shot, incremental, demand-, range-, deadline- and profile-aware entry points
all exist (`:55`-`:298`); the admission screens are
`first_unsupported_op`/`first_unsupported_sort` (`:298`, `:321`).

One nit, not drift: line 11-12 lists "equality" as derived from the AND/inverter
basis. `Aig` has no `eq` constructor; equality is spelled `xor(lhs,
rhs).negated()` at the `axeyum-bv` call sites (`axeyum-bv/src/lib.rs:1601`,
`:2140`, `:2750`). The claim is true; the reader will not find a function by
that name.

### Inside the source: one stale comment

`crates/axeyum-cnf/src/inprocess.rs:138-140` says "The shipping SMT path enables
it by default with inprocessing (`SolverConfig::cnf_vivify`)". `cnf_vivify` does
default to `true` (`backend.rs:391`), but the same file's own doc says it is "**A
no-op unless `cnf_inprocessing` is set**" (`backend.rs:152`), and
`cnf_inprocessing` defaults to `false`. Read literally the sentence is defensible
("with inprocessing"); read as most people will read it, it says vivification
ships on, and it does not.

## Gaps and open questions

1. **Why two inprocessing pipelines?** `inprocess.rs` (ADR-1750) and
   `sat_bv_backend::inprocess` (`:1827`) run the same three passes with different
   certificate mechanics — the former concatenates into one DRAT sink, the latter
   builds a `ReductionLink` and lifts the search's steps out of the compacted
   variable space. Nothing in the tree says which is intended to survive.
   Determining it needs a decision, not a measurement; ADR-1750's text does not
   name `sat_bv_backend` as an adopter.
2. **Is the inprocessing default-off deliberate or drift?**
   `docs/research/03-measurements/inprocessing-admission-2026-09-08.md` is cited
   in `inprocess.rs:132-140` as measuring vivification a net win on the QF_BV
   parity corpus. If that measurement stands, `cnf_inprocessing: false` is a lever
   nobody flipped. I did not read that measurement note (out of scope for this
   lane); L3 or a measurement lane should reconcile it.
3. **Dead-weight candidates.** `xor_matrix.rs` (1,595 lines, bench-only),
   `xor_dpll.rs` (662, test-only reference), `xor_search.rs` (881, reachable only
   through those two), `cube.rs` (1,863, example/test-only), `colouring.rs`
   (1,354, one differential test) and `trim_drat_proof` (no caller) total roughly
   6,400 lines with no production consumer. Some of that is deliberate (a naive
   reference decider for a differential test earns its keep); `xor_matrix` and
   `trim_drat_proof` are not obviously in that category. Determining intent needs
   the ADR-0035 follow-up plan, which I did not locate.
4. **`ticks` has no consumer to be deterministic *for*.** The module and the
   `Watch`-width assertion are written as if budgets are denominated in ticks
   (`proof_sat.rs:1537-1557`); no shipping budget is. Either a tick budget was
   planned and not landed, or the model is measurement-only and the comment
   overstates it. `deterministic_work_budget.rs` would tell you which
   [unverified — I read its imports, not its assertions].
5. **`[unverified]` — the zero-test trap.** I did not run any suite, so "compiles
   to zero tests without `--features batsat-reference`" is read off
   `#![cfg(feature = "batsat-reference")]` at
   `tests/native_vs_batsat_differential.rs:42`, not observed. Confirming needs
   `cargo test -p axeyum-cnf --features batsat-reference --test
   native_vs_batsat_differential` and a **nonzero** test count.
6. **`[unverified]` — the default dependency graph.** `Cargo.toml:16-24` and
   `batsat_reference.rs:12-16` both assert that no `batsat`/`rustsat` crate is in
   the default graph. `cargo tree -e normal -p axeyum-cnf` would confirm it; I did
   not run it.
7. **Reachability method limits.** Every row above rests on
   `grep -rn --include='*.rs'` over `crates/` for the symbol name. That misses a
   caller reached through a trait object, a re-export under a different name, or
   a macro. Where a NO CALLER FOUND row appears I have stated the exact pattern
   searched so a reader can re-run it; `SatSolver`/`NativeCdclSolver` is the row
   most likely to be a trait-dispatch false negative, though the trait has no
   `dyn` use I could find either.
