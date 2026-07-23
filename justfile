# Canonical development commands. Run `just` to list.

default:
    @just --list

# Run every check CI runs (except cargo-deny, which needs the tool installed).
check: fmt clippy test doc qfbv-profile reflection-semantics-gate benchmark-repetition-tests glaurung-qfbv-regular foundational-resources rules-as-code smtcomp-resume parity-docs links

fmt:
    cargo fmt --all --check

clippy:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

test:
    cargo test --workspace --all-features

# Same as `test`, but under a hard 64 GiB memory cap (scripts/mem-run.sh) so a
# runaway allocation (e.g. an unbounded NRA / wide bit-blast blowup) aborts the
# test process instead of OOM-killing the host. Prefer this when touching solving
# paths. Override the cap with MEM_LIMIT_GB=N.
test-guarded:
    MEM_LIMIT_GB=64 ./scripts/mem-run.sh cargo test --workspace --all-features

# T6.0.3/TL2.15 seed: deterministic generated coverage of the four currently
# representable Lean-kernel seams. The workspace `test` recipe also discovers
# this integration test; this target is the bounded fast reproduction path.
lean-kernel-seams:
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test -p axeyum-lean-kernel --test kernel_seam_fuzz

# Corpus-scale ADR-0134/0135 Lean reconstruction.  This is deliberately a
# release-only scheduled stress gate: on the current reference host it takes
# about 105 seconds and peaks below 3 GiB; the 4 GiB envelope also accommodates
# a cold optimized solver build.
test-quant-bv-lean-stress:
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test --release -p axeyum-solver --features z3 --test evidence_quant_bv_instance_set public_psyco_107_bv_routes_through_source_instance_lean_reconstruction -- --ignored --exact

# Genuine typed ADR-0126 existential witnesses for all three public rows. The
# reference-host test takes 12.43 seconds; the 4 GiB envelope covers its roughly
# 1.9 GiB cold build-and-test peak.
test-quant-negated-exists-lean-stress:
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test --release -p axeyum-solver --test evidence_quant_negated_exists three_public_rows_gain_genuine_typed_lean_reconstruction -- --ignored --exact

# Genuine `Exists.rec` elimination plus typed ADR-0128 universal
# counterexample for the public 32-bit multiplier row.
test-quant-vacuous-exists-lean-stress:
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test --release -p axeyum-solver --test quant_closed_counterexample_lean issue2031_eliminates_vacuous_existentials_before_typed_counterexample -- --ignored --exact

# Source-bound ADR-0124/0125 alternation reconstruction, including exact
# direct-vs-router Lean module equality. The two public rows run separately so
# their peak arenas do not coexist; the reference host measures about 3.6 GiB
# for small-pipeline-fixpoint-3 and 2.1 GiB for bug802 under the 4 GiB envelope.
test-quant-bv-alternation-lean-stress:
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test --release -p axeyum-solver --test quant_bv_alternation_counterexample public_pipeline_reconstructs_from_the_full_alternating_source -- --ignored --exact
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh cargo test --release -p axeyum-solver --test quant_bv_alternation_counterexample bug802_reconstructs_all_530_quantified_binders -- --ignored --exact

doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps

qfbv-profile:
    ./scripts/check-qfbv-profile.sh

# T5.1.6: source-derived proof + deterministic fuzz ownership for every checked
# LLVM/MIR semantic variant, followed by the exact bounded evidence suites.
reflection-semantics-gate:
    python3 scripts/check-reflection-semantics-gate.py --run

benchmark-repetition-tests:
    python3 -m unittest scripts/tests/test_glaurung_benchmark_recipes.py scripts/tests/test_glaurung_regular_gate.py scripts/tests/test_summarize_glaurung_repetitions.py scripts/tests/test_summarize_glaurung_shards.py scripts/tests/test_summarize_glaurung_shard_repetitions.py scripts/tests/test_summarize_glaurung_native_profile.py scripts/tests/test_summarize_glaurung_warm_profile.py scripts/tests/test_compare_glaurung_repetitions.py scripts/tests/test_compare_glaurung_shard_repetitions.py scripts/tests/test_compare_glaurung_rewrite_ablation.py scripts/tests/test_compare_glaurung_native_replay.py scripts/tests/test_analyze_glaurung_paired_traces.py scripts/tests/test_analyze_glaurung_regime_features.py scripts/tests/test_analyze_glaurung_profiled_trace.py scripts/tests/test_analyze_qfbv_faithfulness.py scripts/tests/test_analyze_bit_lowering_memo_profile.py scripts/tests/test_analyze_bit_lowering_memo_timing.py scripts/tests/test_measure_glaurung_authoritative_findings.py

# Exercise the actual Glaurung lifter distribution when its access-controlled
# representative pack is available. The script auto-discovers the pinned NAS
# capture or accepts an explicit directory, and reports an explicit skip when
# neither is present. Explicitly configured but incomplete data fails closed.
glaurung-qfbv-regular:
    ./scripts/check-glaurung-qfbv-regular.sh

foundational-resources:
    ./scripts/check-foundational-resources.sh

rules-as-code:
    python3 scripts/gen-rules-as-code-dashboard.py
    python3 scripts/validate-rules-as-code.py
    python3 scripts/query-rules-as-code.py summary
    python3 scripts/query-rules-as-code.py packs --text procurement --require-any
    python3 scripts/query-rules-as-code.py checks --pack procurement_scoring_v0 --proof-status checked --require-any
    python3 scripts/query-rules-as-code.py families --pack procurement_scoring_v0 --text quality --require-any
    python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family bounded_awards --text 2026-08-02 --limit 3 --require-any
    python3 scripts/query-rules-as-code.py packs --pack grant_allocation_v0 --require-any
    python3 scripts/query-rules-as-code.py checks --pack grant_allocation_v0 --validation qf_lra_farkas_solver_regression --proof-status checked --require-any
    python3 scripts/query-rules-as-code.py families --pack grant_allocation_v0 --text balanced --require-any
    python3 scripts/query-rules-as-code.py rows --pack grant_allocation_v0 --family balanced_budget_allocations --text 1/2 --limit 3 --require-any
    python3 scripts/query-rules-as-code.py packs --pack category_equivalence_v0 --require-any
    python3 scripts/query-rules-as-code.py checks --pack category_equivalence_v0 --validation qf_uf_alethe_solver_regression --proof-status checked --require-any
    python3 scripts/query-rules-as-code.py families --pack category_equivalence_v0 --text equivalence --require-any
    python3 scripts/query-rules-as-code.py rows --pack category_equivalence_v0 --family equivalence_pair_rows --text emergency_housing --limit 3 --require-any
    python3 scripts/query-rules-as-code.py packs --pack workflow_reachability_v0 --require-any
    python3 scripts/query-rules-as-code.py checks --pack workflow_reachability_v0 --validation bool_qf_lia_solver_regression --proof-status checked --require-any
    python3 scripts/query-rules-as-code.py families --pack workflow_reachability_v0 --text reachability --require-any
    python3 scripts/query-rules-as-code.py rows --pack workflow_reachability_v0 --family two_step_reachability_rows --text '"final_state":"approved"' --limit 3 --require-any
    python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
    python3 scripts/query-rules-as-code.py families --text adjacent --require-any
    python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family quality_monotonicity_adjacent --limit 3 --require-any
    git diff --exit-code docs/rules-as-code/generated

# Guard live parity prose against the committed scoreboard, dominance audits,
# and paired p4dfa controls. This is intentionally much cheaper than rerunning
# the measurements it checks.
parity-docs:
    python3 -m unittest scripts.tests.test_parity_evidence
    python3 -m unittest scripts.tests.test_prototype_lean4export_reader
    python3 -m unittest scripts.tests.test_lean_compatibility
    python3 -m unittest scripts.tests.test_lean_u2_test_authority
    python3 scripts/gen-lean-u2-test-authority.py --check
    python3 -m unittest scripts.tests.test_lean_u2_official_ci_profiles
    python3 scripts/gen-lean-u2-official-ci-profiles.py --check
    python3 -m unittest scripts.tests.test_lean_u2_official_child_shards
    python3 scripts/gen-lean-u2-official-child-shards.py --check
    python3 -m unittest scripts.tests.test_lean_u2_native_surface_classification
    python3 scripts/gen-lean-u2-native-surface-classification.py --check
    python3 -m unittest scripts.tests.test_lean_u2_native_surface_content
    python3 scripts/gen-lean-u2-native-surface-content.py --check
    python3 -m unittest scripts.tests.test_lean_u2_native_dependency
    python3 scripts/gen-lean-u2-native-dependency.py --check
    python3 -m unittest scripts.tests.test_lean_u2_native_dependency_m2_1
    python3 scripts/lean_u2_native_dependency_m2_1.py check-contract
    python3 -m unittest scripts.tests.test_lean_execution_evidence
    python3 scripts/gen-lean-execution-evidence.py --check
    python3 -m unittest scripts.tests.test_lean_execution_process
    python3 scripts/lean_execution_process.py result --check
    python3 -m unittest scripts.tests.test_lean_execution_store
    python3 scripts/lean_execution_store.py result --check
    python3 -m unittest scripts.tests.test_lean_execution_acceptance
    python3 scripts/lean_execution_acceptance.py result --check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_r2
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_r3
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_r3_result
    python3 scripts/lean_u2_official_execution_r3_result.py result --check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2
    python3 scripts/lean_u2_official_execution_m2.py --check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_store
    python3 scripts/lean_u2_official_execution_m2_store.py --check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_run
    python3 scripts/lean_u2_official_execution_m2_run.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r2
    python3 scripts/lean_u2_official_execution_m2_r2.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r3
    python3 scripts/lean_u2_official_execution_m2_r3.py offline-check
    python3 scripts/lean_u2_official_execution_m2_r3.py validate-incomplete
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r4
    python3 scripts/lean_u2_official_execution_m2_r4.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r5
    python3 scripts/lean_u2_official_execution_m2_r5.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r5_diagnostic
    python3 scripts/lean_u2_official_execution_m2_r5_diagnostic.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r6
    python3 scripts/lean_u2_official_execution_m2_r6.py offline-check
    python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r6_result
    python3 scripts/lean_u2_official_execution_m2_r6_result.py result --check
    python3 -m unittest scripts.tests.test_lean_u2_normalization_contracts
    python3 scripts/lean_u2_normalization_contracts.py --check
    python3 -m unittest scripts.tests.test_lean_complete_parity
    python3 -m unittest scripts.tests.test_lean_official_construct_matrix
    python3 scripts/check-lean-official-construct-matrix.py --check
    python3 -m unittest scripts.tests.test_lean_strict_positivity
    python3 scripts/check-lean-strict-positivity.py --check
    python3 -m unittest scripts.tests.test_lean_strict_positivity_m3
    python3 scripts/check-lean-strict-positivity-m3.py --check
    python3 -m unittest scripts.tests.test_lean_recursive_induction_hypotheses
    python3 scripts/check-lean-recursive-induction-hypotheses.py --check
    python3 -m unittest scripts.tests.test_lean_mutual_inductive_groups
    python3 scripts/check-lean-mutual-inductive-groups.py --check
    python3 -m unittest scripts.tests.test_lean_nested_inductive_elimination
    python3 scripts/check-lean-nested-inductive-elimination.py --check
    python3 scripts/freeze-lean-official-construct-matrix-stage-b.py --check
    python3 scripts/freeze-lean-official-construct-matrix-product.py --check
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh python3 -m unittest scripts.tests.test_lean_axiom_ledger
    python3 scripts/gen-lean-compatibility.py --check
    python3 scripts/gen-lean-complete-parity.py --check
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh python3 scripts/gen-lean-axiom-ledger.py --check
    python3 scripts/gen-gap-ownership.py --check
    python3 scripts/gen-measurement-provenance.py --check
    python3 scripts/gen-smtcomp-resume-contract.py --check
    python3 scripts/gen-proof-gap-matrix.py --check
    python3 scripts/gen-proof-gap-shape-census.py --check
    python3 scripts/gen-smtlib-api-conformance.py --check
    python3 scripts/gen-smtlib-session-contract.py --check
    python3 scripts/check-parity-docs.py

# ADR-0344 E0-E2: contract generation, immutable filesystem recovery, active
# runner lifecycle/sidecars/lease/export, one-host aggregate cgroup evidence,
# portable plus opt-in N>=3 multi-host durability evidence, and the legacy
# scoring pipeline.
smtcomp-resume:
    ./scripts/check-smtcomp-resume.sh

# Current official construct-matrix product boundary: the direct-recursive
# control precedes each remaining typed decline, and all five rows repeat.
lean-construct-matrix-product:
    MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=1 ./scripts/mem-run.sh cargo test -p axeyum-lean-import --test official_construct_matrix

# TL2.13 M4: exact ordered-group import, named recursor comparison, selected
# non-indexed/indexed cross-family computation, and publication mutations.
lean-mutual-inductive-groups-product:
    MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=1 ./scripts/mem-run.sh cargo test -p axeyum-lean-import --test official_mutual_inductive_groups

deny:
    cargo deny check

links:
    ./scripts/check-links.sh

# Run the committed micro corpus through the pure Rust BV backend.
bench-micro:
    cargo run --release -p axeyum-bench -- corpus/micro --backend sat-bv --timeout-ms 1000 --out /tmp/axeyum-bench-micro-sat-bv.json

# Run the committed micro corpus through the Z3 oracle backend.
bench-micro-z3:
    cargo run --release -p axeyum-bench --features z3 -- corpus/micro --backend z3 --timeout-ms 1000 --out /tmp/axeyum-bench-micro-z3.json

# Deterministically bind a shadow-diff capture index's trusted verdict/family/tier
# facts to the exact `.smt2` bytes. The generator rejects missing or unlisted
# queries and validates its output through the benchmark's normal manifest path.
generate-glaurung-manifest corpus_dir capture_index out manifest_jobs="8":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench -- "{{ corpus_dir }}" --generate-corpus-manifest "{{ capture_index }}" --manifest-jobs "{{ manifest_jobs }}" --out "{{ out }}"

# Primary client-tier QF_BV gates. `corpus_dir` is an externally captured,
# redistributable Glaurung SMT-LIB query directory and its v1 manifest; the
# repository deliberately does not pretend that a synthetic substitute is the
# client workload. The manifest fixes exact membership, per-file content hashes,
# expected verdicts, families, and named representative/full tiers. Every
# selected file must produce a decision, operational errors fail the harness,
# verdicts are checked against in-process Z3 on the original query, and the
# versioned artifact records decided rate, original-query shape, formula/AIG/CNF
# p50/p95, cold-stage p50/p95, and the Axeyum/Z3 ratio. One worker avoids
# cross-query contention corrupting the layer attribution. The reproducible-run
# gate requires a clean source revision plus complete tool/hardware identity.
#
# Raw is the current Glaurung one-shot integration and the primary control.
# Canonical enables only the exact default rewriter. Configured enables the
# broader warm-oriented preprocessing pipeline. These are distinct experiment
# policies and must never share an artifact series.
bench-glaurung-qfbv corpus_dir manifest tier="full" out="bench-results/glaurung-qfbv-raw-sat-bv-vs-z3.json":
    just bench-glaurung-qfbv-raw "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out }}"

bench-glaurung-qfbv-raw corpus_dir manifest tier="full" out="bench-results/glaurung-qfbv-raw-sat-bv-vs-z3.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-canonical corpus_dir manifest tier="full" out="bench-results/glaurung-qfbv-canonical-sat-bv-vs-z3.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite default --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-configured corpus_dir manifest tier="full" out="bench-results/glaurung-qfbv-configured-sat-bv-vs-z3.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --preprocess --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Structural demand diagnostics are intentionally separate from client timing:
# the observational analysis is nested in bit blast and can dominate a run.
# Artifact v31 marks these profiles complete; production recipes above leave
# the diagnostic off and publish structural demand fields as unavailable.
bench-glaurung-qfbv-raw-demand-profile corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-raw-demand-profile.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --profile-bit-demand --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# ADR-0300's fail-closed v39 BTree baseline validator and dense-candidate
# structural comparison. Timing is authorized only by the second recipe.
analyze-glaurung-bit-lowering-memo-profile artifact out="bench-results/glaurung-bit-lowering-memo-profile-analysis.json":
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/analyze-bit-lowering-memo-profile.py --artifact "{{ artifact }}" --expected-representation btree-v1 --out "{{ out }}"

compare-glaurung-bit-lowering-memo-profile baseline candidate out="bench-results/glaurung-bit-lowering-memo-comparison.json":
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/analyze-bit-lowering-memo-profile.py --artifact "{{ baseline }}" --candidate "{{ candidate }}" --expected-representation btree-v1 --candidate-representation dense-v1 --out "{{ out }}"

# ADR-0300's exact B,C,C,B,B,C,C,B,B,C,C,B unprofiled process schedule and
# fail-closed timing/RSS analysis. Both scripts pin source and binary hashes.
run-glaurung-bit-lowering-memo-timing baseline_source candidate_source baseline_binary candidate_binary out:
    python3 scripts/run-bit-lowering-memo-timing.py --baseline-source "{{ baseline_source }}" --candidate-source "{{ candidate_source }}" --baseline-binary "{{ baseline_binary }}" --candidate-binary "{{ candidate_binary }}" --out "{{ out }}"

analyze-glaurung-bit-lowering-memo-timing run_root baseline_binary candidate_binary out="bench-results/glaurung-bit-lowering-memo-timing-analysis.json":
    python3 scripts/analyze-bit-lowering-memo-timing.py --run-root "{{ run_root }}" --baseline-binary "{{ baseline_binary }}" --candidate-binary "{{ candidate_binary }}" --out "{{ out }}"

bench-glaurung-qfbv-canonical-demand-profile corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-canonical-demand-profile.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite default --profile-bit-demand --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# ADR-0259/0260/0276's diagnostic-only cold CNF construction, duplicate-origin,
# and parity-leaf overlap profile. This is a separate monomorphized encoder and
# must not be used as a client timing baseline.
bench-glaurung-qfbv-raw-cnf-construction-profile corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-raw-cnf-construction-profile.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --profile-cnf-construction --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

analyze-glaurung-qfbv-raw-cnf-construction-profile artifact out="bench-results/glaurung-qfbv-raw-cnf-construction-profile-analysis.json":
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/analyze-cnf-construction-profile.py "{{ artifact }}" --expected-files 162 --expected-sat 88 --expected-unsat 74 --expected-manifest-sha256 7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064 --expected-same-owner-parity-duplicates 107000 --expected-baseline-analysis bench-results/glaurung-cnf-duplicate-origin-profile-20260719/analysis.json --expected-family arithmetic=36 --expected-family comparison=12 --expected-family mixed=7 --expected-family register-slice=52 --expected-family slice-partial=54 --expected-family trivial=1 --out "{{ out }}"

# GQ4's production experiment is a distinct policy from observational demand
# profiling. The first recipe measures the whole selected tier; the second
# isolates the capture's dominant register-slice family.
bench-glaurung-qfbv-demand corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-demand.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --demand-bit-slicing --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-demand-register-slice corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-demand-register-slice.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --families register-slice --backend sat-bv --rewrite off --demand-bit-slicing --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# ADR-0158 GQ4-v2 is a distinct, still-off-by-default experiment. All policy
# inputs are explicit and artifact-hashed so calibration runs are comparable.
bench-glaurung-qfbv-range-demand corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-range-demand.json" min_available="256" min_estimated_bits="128" min_estimated_percent="50" min_exact_bits="128" min_exact_percent="50" work_budget="50000":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --range-demand-slicing --range-demand-min-term-bits "{{ min_available }}" --range-demand-min-estimated-bits "{{ min_estimated_bits }}" --range-demand-min-estimated-percent "{{ min_estimated_percent }}" --range-demand-min-exact-bits "{{ min_exact_bits }}" --range-demand-min-exact-percent "{{ min_exact_percent }}" --range-demand-work-budget "{{ work_budget }}" --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-range-demand-register-slice corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-range-demand-register-slice.json" min_available="256" min_estimated_bits="128" min_estimated_percent="50" min_exact_bits="128" min_exact_percent="50" work_budget="50000":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --families register-slice --backend sat-bv --rewrite off --range-demand-slicing --range-demand-min-term-bits "{{ min_available }}" --range-demand-min-estimated-bits "{{ min_estimated_bits }}" --range-demand-min-estimated-percent "{{ min_estimated_percent }}" --range-demand-min-exact-bits "{{ min_exact_bits }}" --range-demand-min-exact-percent "{{ min_exact_percent }}" --range-demand-work-budget "{{ work_budget }}" --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Publishable short-run evidence requires process-level repetitions. Each trial
# gets a fresh process and independent artifact; the summarizer fails closed on
# config/environment/source drift or any decided/error/oracle/manifest/replay
# gate, then reports whole-corpus stage and Axeyum/Z3-ratio variance.
bench-glaurung-qfbv-repeated corpus_dir manifest tier="full" out_dir="bench-results/glaurung-qfbv-raw-repeated" repetitions="5":
    just bench-glaurung-qfbv-raw-repeated "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out_dir }}" "{{ repetitions }}"

bench-glaurung-qfbv-raw-repeated corpus_dir manifest tier="full" out_dir="bench-results/glaurung-qfbv-raw-repeated" repetitions="5":
    just _bench-glaurung-qfbv-repeated "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out_dir }}" "{{ repetitions }}" raw

bench-glaurung-qfbv-canonical-repeated corpus_dir manifest tier="full" out_dir="bench-results/glaurung-qfbv-canonical-repeated" repetitions="5":
    just _bench-glaurung-qfbv-repeated "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out_dir }}" "{{ repetitions }}" canonical

bench-glaurung-qfbv-configured-repeated corpus_dir manifest tier="full" out_dir="bench-results/glaurung-qfbv-configured-repeated" repetitions="5":
    just _bench-glaurung-qfbv-repeated "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out_dir }}" "{{ repetitions }}" configured

# GQ3 causal rewrite measurement alternates the unchanged default manifest and
# exact default-minus-one-rule ablation in fresh processes. The comparator
# pairs by manifest path and rejects every non-rewrite configuration drift.
bench-glaurung-qfbv-rewrite-ablation-repeated corpus_dir manifest rule tier="representative" out_dir="bench-results/glaurung-qfbv-rewrite-ablation" repetitions="5":
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ ! "{{ repetitions }}" =~ ^[0-9]+$ ]] || (( {{ repetitions }} < 2 )); then
        echo "repetitions must be an integer >= 2" >&2
        exit 2
    fi
    mkdir -p "{{ out_dir }}"
    rm -f "{{ out_dir }}/comparison.json"
    bases=()
    ablations=()
    for (( repetition = 1; repetition <= {{ repetitions }}; repetition++ )); do
        base="{{ out_dir }}/base-$(printf '%03d' "$repetition").json"
        ablation="{{ out_dir }}/ablation-$(printf '%03d' "$repetition").json"
        cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite default --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "$base"
        cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite default --rewrite-disable-rule "{{ rule }}" --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "$ablation"
        bases+=("$base")
        ablations+=("$ablation")
    done
    python3 scripts/compare-glaurung-rewrite-ablation.py --base "${bases[@]}" --ablation "${ablations[@]}" --out "{{ out_dir }}/comparison.json"

_bench-glaurung-qfbv-repeated corpus_dir manifest tier out_dir repetitions policy:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ ! "{{ repetitions }}" =~ ^[0-9]+$ ]] || (( {{ repetitions }} < 2 )); then
        echo "repetitions must be an integer >= 2" >&2
        exit 2
    fi
    case "{{ policy }}" in
        raw) policy_args=(--rewrite off) ;;
        canonical) policy_args=(--rewrite default) ;;
        configured) policy_args=(--rewrite off --preprocess) ;;
        *) echo "unknown Glaurung benchmark policy: {{ policy }}" >&2; exit 2 ;;
    esac
    mkdir -p "{{ out_dir }}"
    rm -f "{{ out_dir }}/summary.json"
    artifacts=()
    for (( repetition = 1; repetition <= {{ repetitions }}; repetition++ )); do
        artifact="{{ out_dir }}/run-$(printf '%03d' "$repetition").json"
        cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv "${policy_args[@]}" --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "$artifact"
        artifacts+=("$artifact")
    done
    python3 scripts/summarize-glaurung-repetitions.py "${artifacts[@]}" --out "{{ out_dir }}/summary.json"

# Compare repeated summaries from two distinct clean source revisions. Corpus,
# config, toolchain, hardware, and backends must match exactly; the report keeps
# raw Axeyum/Z3 controls next to the ratio and does not impose an unmeasured
# synthetic threshold.
compare-glaurung-qfbv-repeated baseline candidate out:
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/compare-glaurung-repetitions.py "{{ baseline }}" "{{ candidate }}" --out "{{ out }}"

# Provisional full-tier GQ10 thresholds established from five clean canonical
# trials at 0cfd6cdc (Axeyum/ratio CV ~0.51%, Z3 CV ~0.31%). These are same-
# environment regression alarms, not universal timing promises.
compare-glaurung-qfbv-repeated-guarded baseline candidate out:
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/compare-glaurung-repetitions.py "{{ baseline }}" "{{ candidate }}" --max-ratio-regression-percent 3 --max-axeyum-regression-percent 3 --max-z3-drift-percent 2 --out "{{ out }}"

# Compare two repeated, complete corrected-corpus shard sets. Child shards are
# process partitions, not samples; each input must already contain at least two
# fail-closed whole-composite repetitions.
compare-glaurung-qfbv-sharded-repeated-guarded baseline candidate out:
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/compare-glaurung-shard-repetitions.py "{{ baseline }}" "{{ candidate }}" --max-ratio-regression-percent 3 --max-axeyum-regression-percent 3 --max-rss-regression-percent 5 --max-z3-drift-percent 2 --out "{{ out }}"

# The same variance alarms for a deliberately changed default rewrite manifest.
# This stays fail-closed: both manifest identities and the one additive rule
# must match exactly; removals, reordering, or hidden additions are rejected.
compare-glaurung-qfbv-repeated-rewrite-guarded baseline candidate baseline_rule_set candidate_rule_set added_rule_id out:
    mkdir -p "$(dirname '{{ out }}')"
    python3 scripts/compare-glaurung-repetitions.py "{{ baseline }}" "{{ candidate }}" --expected-baseline-rule-set "{{ baseline_rule_set }}" --expected-candidate-rule-set "{{ candidate_rule_set }}" --expected-added-rewrite-rule "{{ added_rule_id }}" --max-ratio-regression-percent 3 --max-axeyum-regression-percent 3 --max-z3-drift-percent 2 --out "{{ out }}"

# High-assurance companion to the performance run. This switches to the slower
# proof-producing native core and fails closed unless every UNSAT has an inline
# checked DRAT proof. Its timings are proof-validation costs, not the batsat/Z3
# client ratio, so keep its artifact separate from the performance artifacts.
# The unsuffixed compatibility entry point follows the raw control.
bench-glaurung-qfbv-proof-check corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-raw-proof-check.json":
    just bench-glaurung-qfbv-raw-proof-check "{{ corpus_dir }}" "{{ manifest }}" "{{ tier }}" "{{ out }}"

bench-glaurung-qfbv-raw-proof-check corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-raw-proof-check.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 30000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Stronger real-query assurance companion. Every primary UNSAT remains in the
# denominator; a cooperative proof-search expiry or hard whole-worker timeout
# is recorded as not-certified, while a satisfiable contradiction, checker
# failure, malformed worker result, or operational error is fatal. Certificate
# construction/checking is separate from solver timing.
bench-glaurung-qfbv-real-faithfulness corpus_dir manifest tier="representative" deadline_ms="1000" process_timeout_ms="1500" out="bench-results/glaurung-qfbv-real-faithfulness.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --prove-unsat --certify-end-to-end-unsat --end-to-end-deadline-ms "{{ deadline_ms }}" --end-to-end-process-timeout-ms "{{ process_timeout_ms }}" --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 30000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --manifest-jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-canonical-proof-check corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-canonical-proof-check.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite default --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 30000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

bench-glaurung-qfbv-configured-proof-check corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-configured-proof-check.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --rewrite off --preprocess --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 30000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# GQ1/GQ10 ingestion-contract smoke only; never cite this micro tier as a client
# performance result.
bench-glaurung-manifest-smoke out="bench-results/glaurung-manifest-smoke.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- corpus/micro --corpus-manifest corpus/micro/manifest-v1.json --corpus-tier representative --backend sat-bv --preprocess --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 1000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Proof-gate plumbing smoke; still not client performance evidence.
bench-glaurung-manifest-proof-smoke out="bench-results/glaurung-manifest-proof-smoke.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- corpus/micro --corpus-manifest corpus/micro/manifest-v1.json --corpus-tier representative --backend sat-bv --preprocess --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --require-deterministic-resources --timeout-ms 1000 --resource-limit 2000000 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# P4.5: the committed curated QF_BV slice, sat-bv vs Z3 (oracle-enabled). The
# measured head-to-head gate for Track 1. Encoding budgets bound the bit-blast so
# a pathological instance returns a structured `unknown` instead of allocating
# gigabytes (some curated files have very wide terms). Wrap in `ulimit -v` (e.g.
# `( ulimit -v 64000000; just bench-qfbv-curated )`) so a runaway can't OOM the box.
bench-qfbv-curated:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/qfbv-curated --backend sat-bv --compare-z3 --timeout-ms 2000 --jobs 2 --node-budget 50000 --cnf-var-budget 200000 --cnf-clause-budget 1000000 --out bench-results/baselines/qfbv-curated-sat-bv-vs-z3-2s.json --logic QF_BV

# P1.1: the same curated QF_BV slice with CNF inprocessing (subsumption + BVE)
# enabled on the sat-bv encoding (`--inprocess`). Compare its decided/unknown/PAR-2
# against `bench-qfbv-curated` to read the inprocessing delta. Same memory caveat.
bench-qfbv-curated-inprocess:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/qfbv-curated --backend sat-bv --inprocess --compare-z3 --timeout-ms 2000 --jobs 2 --node-budget 50000 --cnf-var-budget 200000 --cnf-clause-budget 1000000 --out bench-results/baselines/qfbv-curated-sat-bv-inprocess-vs-z3-2s.json --logic QF_BV

# P1.2: the same curated QF_BV slice with word-level preprocessing (propagate_values
# + solve_eqs) enabled before bit-blasting (`--preprocess`). Model-sound via the
# reconstruction trail; compare decided/PAR-2 against `bench-qfbv-curated`.
bench-qfbv-curated-preprocess:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/qfbv-curated --backend sat-bv --preprocess --compare-z3 --timeout-ms 2000 --jobs 2 --node-budget 50000 --cnf-var-budget 200000 --cnf-clause-budget 1000000 --out bench-results/baselines/qfbv-curated-sat-bv-preprocess-vs-z3-2s.json --logic QF_BV

# Reproduce the Phase 2 public QF_BV baseline after `scripts/fetch-corpus.sh qf_bv`.
bench-public-qfbv-baseline:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --timeout-ms 1000 --out bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 3 rewrite-measurement baseline.
bench-public-qfbv-rewrite:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --timeout-ms 1000 --rewrite default --out bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 public pure-Rust BV vs Z3 supported-slice baseline.
bench-public-qfbv-sat-bv-compare:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --compare-z3 --timeout-ms 1000 --node-budget 1000 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Public QF_BV: P2.1 lazy bit-blasting (CEGAR) vs Z3 on the supported slice.
# No CNF/node budget — the abstraction sidesteps the eager mountain itself; the
# timeout bounds each file. DISAGREE must stay 0 (the hard soundness invariant).
bench-public-qfbv-lazy-vs-z3:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend lazy-bv --compare-z3 --timeout-ms 1000 --out bench-results/baselines/qf-bv-20221214-p4dfa-lazy-bv-z3-compare-1s.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Fair lazy-bv vs Z3 on the public p4dfa 113 slice at the SAME standing budgets as
# the eager `qf-bv-p4dfa-fair-sat-bv-vs-z3` baselines (apples-to-apples). 3 s tier.
bench-public-qfbv-lazy-fair-3s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend lazy-bv --compare-z3 --timeout-ms 3000 --jobs 2 --node-budget 200000 --cnf-var-budget 2000000 --cnf-clause-budget 5000000 --out bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-3s-n200k-cnf5M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Fair lazy-bv vs Z3, 20 s tier (node 300k, cnf 3M/8M) — matches the eager 20 s baseline.
bench-public-qfbv-lazy-fair-20s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend lazy-bv --compare-z3 --timeout-ms 20000 --jobs 2 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --out bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-20s-n300k-cnf8M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Fair sat-bv WITH word-level preprocessing (solve_eqs fuel-bounded) vs Z3, 3 s tier
# — same budgets as the eager fair baseline; measures the reduction lever.
bench-public-qfbv-preprocess-fair-3s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --preprocess --compare-z3 --timeout-ms 3000 --jobs 2 --node-budget 200000 --cnf-var-budget 2000000 --cnf-clause-budget 5000000 --out bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-3s-n200k-cnf5M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Fair sat-bv --preprocess vs Z3, 20 s tier — decides 7/113 vs eager's 3.
bench-public-qfbv-preprocess-fair-20s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --preprocess --compare-z3 --timeout-ms 20000 --jobs 2 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --out bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-20s-n300k-cnf8M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Fair sat-bv --preprocess --inprocess vs Z3, 3 s tier. CNF inprocessing
# (subsumption + bounded variable elimination, equisat + model reconstruction)
# is enabled and admitted up to the raised cap (4M vars / 16M clauses) so the
# public EncodingBudget band is actually reached. Measured 4/113 vs --preprocess's
# 3/113 (DISAGREE=0, 0 replay failures, par2 5.864→5.832) — the BVE pass runs
# truncated at 3 s, so var-bound cases await compaction + the 20 s tier.
bench-public-qfbv-preprocess-inprocess-fair-3s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --preprocess --inprocess --compare-z3 --timeout-ms 3000 --jobs 2 --node-budget 200000 --cnf-var-budget 2000000 --cnf-clause-budget 5000000 --out bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-inprocess-vs-z3-3s-n200k-cnf5M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Fair sat-bv --preprocess --inprocess vs Z3, 20 s tier — the budget where the
# (deadline-bounded) BVE pass can run closer to its full ~28% clause reduction on
# the EncodingBudget instances.
bench-public-qfbv-preprocess-inprocess-fair-20s:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --preprocess --inprocess --compare-z3 --timeout-ms 20000 --jobs 2 --node-budget 300000 --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --out bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-inprocess-vs-z3-20s-n300k-cnf8M.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV, Zenodo 11061097' --logic QF_BV

# Reproduce the Phase 5 guarded admission run with explicit CNF budgets.
bench-public-qfbv-sat-bv-guarded:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --compare-z3 --timeout-ms 1000 --node-budget 5000 --cnf-var-budget 7000 --cnf-clause-budget 20000 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 replay-refinement diagnostic run.
bench-public-qfbv-sat-bv-replay-refine:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine --refine-rounds 16 --compare-z3 --timeout-ms 1000 --node-budget 5000 --cnf-var-budget 7000 --cnf-clause-budget 20000 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 relaxed-admission replay-refinement diagnostic run.
bench-public-qfbv-sat-bv-replay-refine-relaxed:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine --refine-rounds 16 --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 7000 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 exact-target relaxed replay-refinement diagnostic run.
bench-public-qfbv-sat-bv-replay-refine-exact:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine-exact --refine-rounds 64 --refine-batch 64 --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 8000 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 exact-target adaptive-batch diagnostic run.
bench-public-qfbv-sat-bv-replay-refine-exact-adaptive:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine-exact --refine-rounds 64 --refine-batch 64 --refine-adaptive-batch --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 8000 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k-30k-r64-b64-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 adaptive-batch 8500-variable admission sweep.
bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-cnf8k5:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine-exact --refine-rounds 64 --refine-batch 64 --refine-adaptive-batch --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 8500 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k5-30k-r64-b64-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 smallest-DAG adaptive exact-target diagnostic run.
bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine-exact --refine-rounds 64 --refine-batch 64 --refine-adaptive-batch --refine-select smallest-dag --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 8000 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k-30k-r64-b64-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Reproduce the Phase 5 smallest-DAG adaptive 8500-variable admission sweep.
bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest-cnf8k5:
    mkdir -p bench-results/baselines
    cargo run --release -p axeyum-bench --features z3 -- corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen --backend sat-bv --query-plan replay-refine-exact --refine-rounds 64 --refine-batch 64 --refine-adaptive-batch --refine-select smallest-dag --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 8500 --cnf-clause-budget 30000 --jobs 8 --out bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k5-30k-r64-b64-j8.json --corpus-source 'SMT-LIB 2024 non-incremental QF_BV archive, Zenodo record 11061097, file QF_BV.tar.zst' --logic QF_BV --families '20221214-p4dfa-XiaoqiChen/Composition,20221214-p4dfa-XiaoqiChen/MobileDevice,20221214-p4dfa-XiaoqiChen/StringMatching,20221214-p4dfa-XiaoqiChen/TCP,20221214-p4dfa-XiaoqiChen/VideoConf'

# Repopulate gitignored reference clones.
references:
    ./scripts/fetch-references.sh

# Fetch public benchmark corpora into corpus/public/ (large downloads).
corpus:
    ./scripts/fetch-corpus.sh
