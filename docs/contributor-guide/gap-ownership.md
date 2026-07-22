# Measured-gap ownership map

> **Generated; do not edit by hand.** Source: [`docs/plan/gap-ownership-v1.json`](../plan/gap-ownership-v1.json). Regenerate with `python3 scripts/gen-gap-ownership.py`; use `--check` in validation.

This is the contributor routing layer for the current G0-G10 gap program. It names the first code owner, committed evidence, executable gate, decision anchor, and next safe action. An absent gap-specific ADR is shown explicitly; it is decision debt, not permission to decide silently in code.

## Quick routing

| Gap | Research question | State | First owner |
|---|---|---|---|
| [G0](#g0) | Do live public claims still match the committed solver, proof, and protocol artifacts? | `prototype-landed` | [`scripts/check-parity-docs.py`](../../scripts/check-parity-docs.py) |
| [G1](#g1) | What source-balanced and deduplicated population does each solver score actually describe? | `partially-landed` | [`scripts/gen-measurement-provenance.py`](../../scripts/gen-measurement-provenance.py) |
| [G2](#g2) | Where do Axeyum, Z3, and Bitwuzla win across hard cold queries and retained embedded workloads? | `partially-landed` | [`crates/axeyum-bench/src/main.rs`](../../crates/axeyum-bench/src/main.rs) |
| [G3](#g3) | Do at least two independent external oracles agree with Axeyum in both verdict directions on every paper-claimed fragment? | `partially-landed` | [`crates/axeyum-solver/tests/bv_differential_fuzz.rs`](../../crates/axeyum-solver/tests/bv_differential_fuzz.rs) |
| [G4](#g4) | Which repeated unsupported or unknown shape names the next decision mechanism with measurable public-corpus leverage? | `open` | [`crates/axeyum-solver/tests/progress_frontier.rs`](../../crates/axeyum-solver/tests/progress_frontier.rs) |
| [G5](#g5) | Which exact definitive results lack serialized evidence, independent checking, trust closure, or Lean reconstruction? | `partially-landed` | [`crates/axeyum-solver/src/evidence.rs`](../../crates/axeyum-solver/src/evidence.rs) |
| [G6](#g6) | Does official Lean accept a visible representative and exhaustive population of generated solver proofs without sorryAx? | `partially-landed` | [`crates/axeyum-solver/tests/lean_crosscheck.rs`](../../crates/axeyum-solver/tests/lean_crosscheck.rs) |
| [G7](#g7) | Which versioned Lean-core profile does the Rust kernel accept identically to official Lean, independent of solver proof coverage? | `open` | [`crates/axeyum-lean-kernel/src/tc.rs`](../../crates/axeyum-lean-kernel/src/tc.rs) |
| [G8](#g8) | Which commands are parsed, ordered, executed, rendered, and independently checked as one transactional SMT-LIB session? | `prototype-landed` | [`crates/axeyum-smtlib/src/parse.rs`](../../crates/axeyum-smtlib/src/parse.rs) |
| [G9](#g9) | What time, memory, artifact-size, certificate-coverage, fallback, and decided-rate tradeoff does each real native/WASM consumer select? | `partially-landed` | [`crates/axeyum-solver/Cargo.toml`](../../crates/axeyum-solver/Cargo.toml) |
| [G10](#g10) | Can a new contributor find the owning module, evidence, checker, decision, and next safe action without reading PLAN/STATUS as battle logs? | `partially-landed` | [`docs/PROJECT-STATE.md`](../../docs/PROJECT-STATE.md) |

## Detailed ownership

<a id="g0"></a>

### G0 — Stop documentation from overruling measurements

**State:** `prototype-landed`

**Question:** Do live public claims still match the committed solver, proof, and protocol artifacts?

**Owner paths:**

- [`scripts/check-parity-docs.py`](../../scripts/check-parity-docs.py)
- [`scripts/gen-scoreboard.py`](../../scripts/gen-scoreboard.py)

**Evidence:**

- [`bench-results/SCOREBOARD.md`](../../bench-results/SCOREBOARD.md)
- [`docs/PROJECT-STATE.md`](../../docs/PROJECT-STATE.md)

**Executable gates:**

- `python3 scripts/check-parity-docs.py`

**Decision anchors:**

- No gap-specific ADR yet; use the source gap section and open an ADR before changing public behavior.

**Next safe action:** Add a derived marker whenever a new public quantitative claim gains one canonical machine-readable source.

<a id="g1"></a>

### G1 — Replace aggregate decide-rate with a coverage-weighted parity matrix

**State:** `partially-landed`

**Question:** What source-balanced and deduplicated population does each solver score actually describe?

**Owner paths:**

- [`scripts/gen-measurement-provenance.py`](../../scripts/gen-measurement-provenance.py)
- [`docs/plan/measurement-provenance-v1.json`](../../docs/plan/measurement-provenance-v1.json)
- [`scripts/gen-smtcomp-resume-contract.py`](../../scripts/gen-smtcomp-resume-contract.py)
- [`scripts/smtcomp_repro/resume_contract.py`](../../scripts/smtcomp_repro/resume_contract.py)
- [`scripts/smtcomp_repro/resume_fs.py`](../../scripts/smtcomp_repro/resume_fs.py)
- [`scripts/smtcomp_repro/resume_fs_fixture_worker.py`](../../scripts/smtcomp_repro/resume_fs_fixture_worker.py)
- [`scripts/smtcomp_repro/resume_runner.py`](../../scripts/smtcomp_repro/resume_runner.py)
- [`scripts/smtcomp_repro/runner.py`](../../scripts/smtcomp_repro/runner.py)
- [`docs/plan/smtcomp-resumable-run-contract-v1.json`](../../docs/plan/smtcomp-resumable-run-contract-v1.json)
- [`docs/plan/smtcomp-resumable-run-contract-v2.json`](../../docs/plan/smtcomp-resumable-run-contract-v2.json)
- [`scripts/smtcomp_repro/select_library.py`](../../scripts/smtcomp_repro/select_library.py)
- [`scripts/smtcomp_repro/compete.py`](../../scripts/smtcomp_repro/compete.py)
- [`scripts/smtcomp_repro/provenance.py`](../../scripts/smtcomp_repro/provenance.py)
- [`scripts/smtcomp_repro/scoring.py`](../../scripts/smtcomp_repro/scoring.py)
- [`scripts/check-smtcomp-resume.sh`](../../scripts/check-smtcomp-resume.sh)
- [`scripts/gen-scoreboard.py`](../../scripts/gen-scoreboard.py)

**Evidence:**

- [`docs/plan/generated/measurement-provenance-matrix.json`](../../docs/plan/generated/measurement-provenance-matrix.json)
- [`docs/plan/measurement-provenance-design-2026-07-21.md`](../../docs/plan/measurement-provenance-design-2026-07-21.md)
- [`docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md`](../../docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
- [`docs/plan/smtcomp-resumable-run-design-2026-07-21.md`](../../docs/plan/smtcomp-resumable-run-design-2026-07-21.md)
- [`docs/plan/smtcomp-resumable-filesystem-e1a-2026-07-21.md`](../../docs/plan/smtcomp-resumable-filesystem-e1a-2026-07-21.md)
- [`docs/plan/smtcomp-runner-e1b-audit-2026-07-21.md`](../../docs/plan/smtcomp-runner-e1b-audit-2026-07-21.md)
- [`docs/plan/smtcomp-resumable-runner-e1b-2026-07-22.md`](../../docs/plan/smtcomp-resumable-runner-e1b-2026-07-22.md)
- [`docs/plan/generated/smtcomp-resumable-run-contract.json`](../../docs/plan/generated/smtcomp-resumable-run-contract.json)
- [`bench-results/smtcomp-repro-20260721/inventory.json`](../../bench-results/smtcomp-repro-20260721/inventory.json)
- [`bench-results/smtcomp-repro-20260721/provenance.json`](../../bench-results/smtcomp-repro-20260721/provenance.json)
- [`bench-results/SCOREBOARD.md`](../../bench-results/SCOREBOARD.md)

**Executable gates:**

- `python3 scripts/gen-measurement-provenance.py --check`
- `python3 scripts/gen-smtcomp-resume-contract.py --check`
- `python3 -m unittest scripts.tests.test_gen_smtcomp_resume_contract`
- `./scripts/check-smtcomp-resume.sh`
- `PYTHONWARNINGS=error python3 -m unittest scripts.tests.test_smtcomp_resume_fs`
- `AXEYUM_FS_FIXTURE_PARENT=. PYTHONWARNINGS=error python3 -m unittest scripts.tests.test_smtcomp_resume_fs`
- `for t in test_scoring test_pipeline test_selection test_provenance; do python3 scripts/smtcomp_repro/tests/$t.py || exit 1; done`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0343-preregister-cross-regime-measurement-provenance.md`](../../docs/research/09-decisions/adr-0343-preregister-cross-regime-measurement-provenance.md)
- [`docs/research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md`](../../docs/research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

**Next safe action:** Review ADR-0343/0344 and the accepted E1b/E2 results; then implement E3 multi-host allocation, loss/recovery, and transfer durability before rerunning the 64,345-file candidate. The independent official eligibility/status/difficulty selection ledger also remains required.

<a id="g2"></a>

### G2 — Measure production depth, not isolated wins

**State:** `partially-landed`

**Question:** Where do Axeyum, Z3, and Bitwuzla win across hard cold queries and retained embedded workloads?

**Owner paths:**

- [`crates/axeyum-bench/src/main.rs`](../../crates/axeyum-bench/src/main.rs)
- [`scripts/run-glaurung-six-cell-neutral.py`](../../scripts/run-glaurung-six-cell-neutral.py)
- [`scripts/analyze-glaurung-paired-traces.py`](../../scripts/analyze-glaurung-paired-traces.py)

**Evidence:**

- [`bench-results/baselines/qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json`](../../bench-results/baselines/qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json)
- [`bench-results/baselines/qf-bv-p4dfa-z3-standalone-20s.json`](../../bench-results/baselines/qf-bv-p4dfa-z3-standalone-20s.json)
- [`bench-results/glaurung-six-cell-neutral-20260719/result-summary.json`](../../bench-results/glaurung-six-cell-neutral-20260719/result-summary.json)

**Executable gates:**

- `python3 scripts/check-parity-docs.py`
- `python3 -m unittest scripts.tests.test_analyze_glaurung_paired_traces`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md`](../../docs/research/09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md)

**Next safe action:** Add matched curves for at least three independently sourced QF_BV families, with RSS and decision-set overlap.

<a id="g3"></a>

### G3 — Broaden neutral correctness evidence

**State:** `partially-landed`

**Question:** Do at least two independent external oracles agree with Axeyum in both verdict directions on every paper-claimed fragment?

**Owner paths:**

- [`crates/axeyum-solver/tests/bv_differential_fuzz.rs`](../../crates/axeyum-solver/tests/bv_differential_fuzz.rs)
- [`crates/axeyum-solver/tests/abv_differential_fuzz.rs`](../../crates/axeyum-solver/tests/abv_differential_fuzz.rs)
- [`scripts/run-qfbv-independent-oracle-rounds.sh`](../../scripts/run-qfbv-independent-oracle-rounds.sh)

**Evidence:**

- [`bench-results/qfbv-four-oracle-independent-20260718-600s/aggregate.json`](../../bench-results/qfbv-four-oracle-independent-20260718-600s/aggregate.json)
- [`bench-results/qfbv-four-oracle-independent-20260718-600s/README.md`](../../bench-results/qfbv-four-oracle-independent-20260718-600s/README.md)

**Executable gates:**

- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --features z3 --test bv_differential_fuzz --test abv_differential_fuzz`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0224-standing-qfbv-multi-oracle-fuzz.md`](../../docs/research/09-decisions/adr-0224-standing-qfbv-multi-oracle-fuzz.md)
- [`docs/research/09-decisions/adr-0237-independent-edge-qfbv-four-oracle-fuzz.md`](../../docs/research/09-decisions/adr-0237-independent-edge-qfbv-four-oracle-fuzz.md)

**Next safe action:** Freeze neutral multi-oracle profiles for arrays/UF and LIA/LRA before widening to FP, strings, and quantified finite fragments.

<a id="g4"></a>

### G4 — Close the weak decide-rate frontiers before polishing their proofs

**State:** `open`

**Question:** Which repeated unsupported or unknown shape names the next decision mechanism with measurable public-corpus leverage?

**Owner paths:**

- [`crates/axeyum-solver/tests/progress_frontier.rs`](../../crates/axeyum-solver/tests/progress_frontier.rs)
- [`crates/axeyum-solver/src/backend.rs`](../../crates/axeyum-solver/src/backend.rs)
- [`crates/axeyum-solver/src/string_theory.rs`](../../crates/axeyum-solver/src/string_theory.rs)
- [`crates/axeyum-solver/src/uf_arith.rs`](../../crates/axeyum-solver/src/uf_arith.rs)

**Evidence:**

- [`bench-results/frontier/bv_reduction.json`](../../bench-results/frontier/bv_reduction.json)
- [`bench-results/frontier/lia_cuts.json`](../../bench-results/frontier/lia_cuts.json)
- [`bench-results/frontier/nia_unsat.json`](../../bench-results/frontier/nia_unsat.json)
- [`bench-results/frontier/nra_degree.json`](../../bench-results/frontier/nra_degree.json)
- [`bench-results/frontier/string_bound.json`](../../bench-results/frontier/string_bound.json)

**Executable gates:**

- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test progress_frontier`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0259-preregister-cold-cnf-construction-attribution.md`](../../docs/research/09-decisions/adr-0259-preregister-cold-cnf-construction-attribution.md)
- [`docs/research/09-decisions/adr-0261-preregister-private-parity-leaf-elision.md`](../../docs/research/09-decisions/adr-0261-preregister-private-parity-leaf-elision.md)

**Next safe action:** Select no implementation until a fresh residual-shape census identifies a repeated primitive and a preregistered row-level gate.

<a id="g5"></a>

### G5 — Make proof coverage a first-class denominator

**State:** `partially-landed`

**Question:** Which exact definitive results lack serialized evidence, independent checking, trust closure, or Lean reconstruction?

**Owner paths:**

- [`crates/axeyum-solver/src/evidence.rs`](../../crates/axeyum-solver/src/evidence.rs)
- [`crates/axeyum-solver/src/reconstruct.rs`](../../crates/axeyum-solver/src/reconstruct.rs)
- [`crates/axeyum-bench/examples/audit_dominance.rs`](../../crates/axeyum-bench/examples/audit_dominance.rs)

**Evidence:**

- [`docs/plan/generated/proof-gap-matrix.json`](../../docs/plan/generated/proof-gap-matrix.json)
- [`docs/plan/generated/proof-gap-shape-census.json`](../../docs/plan/generated/proof-gap-shape-census.json)
- [`docs/plan/evidence-route-provenance-design-2026-07-21.md`](../../docs/plan/evidence-route-provenance-design-2026-07-21.md)

**Executable gates:**

- `python3 scripts/gen-proof-gap-matrix.py --check`
- `python3 scripts/gen-proof-gap-shape-census.py --check`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0341-preregister-source-bound-evidence-route-telemetry.md`](../../docs/research/09-decisions/adr-0341-preregister-source-bound-evidence-route-telemetry.md)

**Next safe action:** Review proposed ADR-0341, then add verdict-invariant attempt and obligation provenance beginning with the four source-invalid QF_SEQ rows.

<a id="g6"></a>

### G6 — Turn external Lean checking into a required tiered gate

**State:** `partially-landed`

**Question:** Does official Lean accept a visible representative and exhaustive population of generated solver proofs without sorryAx?

**Owner paths:**

- [`crates/axeyum-solver/tests/lean_crosscheck.rs`](../../crates/axeyum-solver/tests/lean_crosscheck.rs)
- [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml)

**Evidence:**

- [`docs/plan/generated/proof-gap-matrix.json`](../../docs/plan/generated/proof-gap-matrix.json)
- [`docs/plan/lean-selected-evidence-prototype-2026-07-21.md`](../../docs/plan/lean-selected-evidence-prototype-2026-07-21.md)

**Executable gates:**

- `AXEYUM_REQUIRE_LEAN=1 AXEYUM_LEAN_BUDGET_SECS=0 AXEYUM_LEAN_JOBS=2 cargo test -p axeyum-solver --features full --test lean_crosscheck lean_crosscheck_representative -- --nocapture --exact`

**Decision anchors:**

- No gap-specific ADR yet; use the source gap section and open an ADR before changing public behavior.

**Next safe action:** Archive the first required remote duration, RSS, checked-family count, and declined manifest before sizing the exhaustive scheduled gate.

<a id="g7"></a>

### G7 — Separate Lean certificate goals from kernel-compatibility research

**State:** `open`

**Question:** Which versioned Lean-core profile does the Rust kernel accept identically to official Lean, independent of solver proof coverage?

**Owner paths:**

- [`crates/axeyum-lean-kernel/src/tc.rs`](../../crates/axeyum-lean-kernel/src/tc.rs)
- [`crates/axeyum-lean-kernel/src/inductive.rs`](../../crates/axeyum-lean-kernel/src/inductive.rs)
- [`crates/axeyum-lean-kernel/src/expr.rs`](../../crates/axeyum-lean-kernel/src/expr.rs)

**Evidence:**

- [`docs/prover-track/research/06-kernel-gap-analysis.md`](../../docs/prover-track/research/06-kernel-gap-analysis.md)
- [`crates/axeyum-lean-kernel/tests/real_lean_inductive_crosscheck.rs`](../../crates/axeyum-lean-kernel/tests/real_lean_inductive_crosscheck.rs)

**Executable gates:**

- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-lean-kernel --tests`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0036-lean-kernel-crate.md`](../../docs/research/09-decisions/adr-0036-lean-kernel-crate.md)
- [`docs/research/09-decisions/adr-0165-lean-compatible-prop-large-elimination.md`](../../docs/research/09-decisions/adr-0165-lean-compatible-prop-large-elimination.md)

**Next safe action:** Specify the compatibility corpus, then sequence bignum literals before literal typing, projections/eta, recursive inductives/positivity, quotients, and import format.

<a id="g8"></a>

### G8 — Measure the SMT-LIB and API compatibility surface

**State:** `prototype-landed`

**Question:** Which commands are parsed, ordered, executed, rendered, and independently checked as one transactional SMT-LIB session?

**Owner paths:**

- [`crates/axeyum-smtlib/src/parse.rs`](../../crates/axeyum-smtlib/src/parse.rs)
- [`crates/axeyum-solver/src/smtlib.rs`](../../crates/axeyum-solver/src/smtlib.rs)
- [`scripts/gen-smtlib-api-conformance.py`](../../scripts/gen-smtlib-api-conformance.py)
- [`scripts/gen-smtlib-session-contract.py`](../../scripts/gen-smtlib-session-contract.py)

**Evidence:**

- [`docs/plan/generated/smtlib-api-conformance.md`](../../docs/plan/generated/smtlib-api-conformance.md)
- [`docs/plan/generated/smtlib-session-contract.md`](../../docs/plan/generated/smtlib-session-contract.md)

**Executable gates:**

- `python3 scripts/gen-smtlib-api-conformance.py --check`
- `python3 scripts/gen-smtlib-session-contract.py --check`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0342-preregister-ordered-smtlib-session.md`](../../docs/research/09-decisions/adr-0342-preregister-ordered-smtlib-session.md)

**Next safe action:** Review proposed ADR-0342; if accepted, implement capture-only ordered command/event IR before rendering or adding command families.

<a id="g9"></a>

### G9 — Prove deployability claims with real consumer profiles

**State:** `partially-landed`

**Question:** What time, memory, artifact-size, certificate-coverage, fallback, and decided-rate tradeoff does each real native/WASM consumer select?

**Owner paths:**

- [`crates/axeyum-solver/Cargo.toml`](../../crates/axeyum-solver/Cargo.toml)
- [`crates/axeyum-wasm/src/lib.rs`](../../crates/axeyum-wasm/src/lib.rs)
- [`scripts/check-qfbv-profile.sh`](../../scripts/check-qfbv-profile.sh)
- [`scripts/measure-wasm-qfbv.cjs`](../../scripts/measure-wasm-qfbv.cjs)

**Evidence:**

- [`bench-results/wasm-qfbv-deployability-20260717/report.json`](../../bench-results/wasm-qfbv-deployability-20260717/report.json)
- [`bench-results/qfbv-proof-coverage-20260717/report.json`](../../bench-results/qfbv-proof-coverage-20260717/report.json)

**Executable gates:**

- `./scripts/check-qfbv-profile.sh`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0216-qfbv-default-and-explicit-consumer-profiles.md`](../../docs/research/09-decisions/adr-0216-qfbv-default-and-explicit-consumer-profiles.md)
- [`docs/research/09-decisions/adr-0227-executable-qfbv-webassembly-deployability.md`](../../docs/research/09-decisions/adr-0227-executable-qfbv-webassembly-deployability.md)

**Next safe action:** Generate one native/WASM Pareto table with cold/warm latency, RSS, bundle size, certificate coverage, fallback rate, and decided rate.

<a id="g10"></a>

### G10 — Reduce reviewer and contributor risk

**State:** `partially-landed`

**Question:** Can a new contributor find the owning module, evidence, checker, decision, and next safe action without reading PLAN/STATUS as battle logs?

**Owner paths:**

- [`docs/PROJECT-STATE.md`](../../docs/PROJECT-STATE.md)
- [`docs/contributor-guide/README.md`](../../docs/contributor-guide/README.md)
- [`crates/axeyum-solver/src/lib.rs`](../../crates/axeyum-solver/src/lib.rs)

**Evidence:**

- [`docs/plan/gap-ownership-v1.json`](../../docs/plan/gap-ownership-v1.json)
- [`docs/plan/gap-analysis-z3-lean-2026-07-21.md`](../../docs/plan/gap-analysis-z3-lean-2026-07-21.md)

**Executable gates:**

- `python3 scripts/gen-gap-ownership.py --check`
- `./scripts/check-links.sh`

**Decision anchors:**

- [`docs/research/09-decisions/adr-0307-theory-api-namespace.md`](../../docs/research/09-decisions/adr-0307-theory-api-namespace.md)

**Next safe action:** Use this map during the next gap increment; split the remaining monolith/API surfaces only behind behavior-preserving gates.
