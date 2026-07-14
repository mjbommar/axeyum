# Canonical development commands. Run `just` to list.

default:
    @just --list

# Run every check CI runs (except cargo-deny, which needs the tool installed).
check: fmt clippy test doc qfbv-profile benchmark-repetition-tests foundational-resources rules-as-code links

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

doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps

qfbv-profile:
    ./scripts/check-qfbv-profile.sh

benchmark-repetition-tests:
    python3 -m unittest scripts/tests/test_summarize_glaurung_repetitions.py

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
generate-glaurung-manifest corpus_dir capture_index out:
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench -- "{{ corpus_dir }}" --generate-corpus-manifest "{{ capture_index }}" --out "{{ out }}"

# Primary client-tier QF_BV gate. `corpus_dir` is an externally captured,
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
bench-glaurung-qfbv corpus_dir manifest tier="full" out="bench-results/glaurung-qfbv-sat-bv-vs-z3.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --preprocess --compare-z3 --require-in-process-z3 --require-reproducible-run --timeout-ms 10000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Publishable short-run evidence requires process-level repetitions. Each trial
# gets a fresh process and independent artifact; the summarizer fails closed on
# config/environment/source drift or any decided/error/oracle/manifest/replay
# gate, then reports whole-corpus stage and Axeyum/Z3-ratio variance.
bench-glaurung-qfbv-repeated corpus_dir manifest tier="full" out_dir="bench-results/glaurung-qfbv-repeated" repetitions="5":
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ ! "{{ repetitions }}" =~ ^[0-9]+$ ]] || (( {{ repetitions }} < 2 )); then
        echo "repetitions must be an integer >= 2" >&2
        exit 2
    fi
    mkdir -p "{{ out_dir }}"
    rm -f "{{ out_dir }}/summary.json"
    artifacts=()
    for (( repetition = 1; repetition <= {{ repetitions }}; repetition++ )); do
        artifact="{{ out_dir }}/run-$(printf '%03d' "$repetition").json"
        cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --preprocess --compare-z3 --require-in-process-z3 --require-reproducible-run --timeout-ms 10000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "$artifact"
        artifacts+=("$artifact")
    done
    python3 scripts/summarize-glaurung-repetitions.py "${artifacts[@]}" --out "{{ out_dir }}/summary.json"

# High-assurance companion to the performance run. This switches to the slower
# proof-producing native core and fails closed unless every UNSAT has an inline
# checked DRAT proof. Its timings are proof-validation costs, not the batsat/Z3
# client ratio, so keep its artifact separate from `bench-glaurung-qfbv`.
bench-glaurung-qfbv-proof-check corpus_dir manifest tier="representative" out="bench-results/glaurung-qfbv-proof-check.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- "{{ corpus_dir }}" --corpus-manifest "{{ manifest }}" --corpus-tier "{{ tier }}" --backend sat-bv --preprocess --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --timeout-ms 30000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# GQ1/GQ10 ingestion-contract smoke only; never cite this micro tier as a client
# performance result.
bench-glaurung-manifest-smoke out="bench-results/glaurung-manifest-smoke.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- corpus/micro --corpus-manifest corpus/micro/manifest-v1.json --corpus-tier representative --backend sat-bv --preprocess --compare-z3 --require-in-process-z3 --require-reproducible-run --timeout-ms 1000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

# Proof-gate plumbing smoke; still not client performance evidence.
bench-glaurung-manifest-proof-smoke out="bench-results/glaurung-manifest-proof-smoke.json":
    mkdir -p "$(dirname '{{ out }}')"
    cargo run --release -p axeyum-bench --features z3 -- corpus/micro --corpus-manifest corpus/micro/manifest-v1.json --corpus-tier representative --backend sat-bv --preprocess --prove-unsat --compare-z3 --require-in-process-z3 --require-reproducible-run --timeout-ms 1000 --jobs 1 --min-decided-percent 100 --logic QF_BV --out "{{ out }}"

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
