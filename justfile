# Canonical development commands. Run `just` to list.

default:
    @just --list

# Run every check CI runs (except cargo-deny, which needs the tool installed).
check: fmt clippy test doc links

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

doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps

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
