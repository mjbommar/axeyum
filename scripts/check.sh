#!/usr/bin/env bash
# Plain-shell fallback for `just check`: runs the gates CI runs (except
# cargo-deny, which needs the tool installed) so an aggregate check is runnable
# on a fresh machine without `just`.
#
# It does NOT mirror the `check` recipe, and the claim that it did -- which lived
# in this header for the life of the file -- was false: measured 2026-08-14, this
# script ran 61 steps and `just check` ran 112, each missing something the other
# had. `scripts/check-aggregate-scope.sh` now measures the difference on every
# run and fails when it grows; the accepted difference is written down in
# `scripts/check-aggregate-scope.expected`. Treat `just check` as the gate and
# this as the no-`just` fallback that may lag it.
#
# Usage: ./scripts/check.sh
# Honor CARGO_BUILD_JOBS / a low -j on memory-constrained hosts, e.g.
#   CARGO_BUILD_JOBS=4 ./scripts/check.sh
set -uo pipefail

cd "$(dirname "$0")/.."

fail=0
ran=0
failed_steps=()

# `AXEYUM_CHECK_LIST=1 ./scripts/check.sh` enumerates the steps and exits without
# running any of them. That listing is this script's own answer to "what does
# this gate examine?", and it is what `scripts/check-aggregate-scope.sh` compares
# against the justfile's `check` recipe — the two ran 61 and 112 steps
# respectively on 2026-08-14 while both documents claimed they were the same
# gate.
list_only="${AXEYUM_CHECK_LIST:-0}"

step() {
  local name="$1"; shift
  ran=$((ran + 1))
  if [ "$list_only" = "1" ]; then
    printf '%s\t%s\n' "$name" "$*"
    return 0
  fi
  echo "=== $name ==="
  if "$@"; then
    echo "--- $name: ok"
  else
    echo "--- $name: FAILED"
    failed_steps+=("$name")
    fail=1
  fi
}

step fmt    cargo fmt --all --check
# `cargo fmt --all` finds files by walking `mod` declarations, and rustfmt does
# not expand macros -- so `axeyum-solver`'s module tree, declared inside
# `macro_rules! full_modules`, was invisible to the gate above: 156 modules /
# 221,445 lines including the whole trusted reconstruction layer. Fourteen
# source files had never been formatted while this step reported success.
# The step below enumerates from the filesystem instead. Keep both: they fail
# for different reasons, and a disagreement between them is itself a finding.
step fmt-all scripts/check-fmt-complete.sh
step facts  python3 scripts/validate-facts.py
step fact-dag-tests python3 -m unittest scripts.tests.test_check_fact_dag
step fact-dag python3 scripts/check-fact-dag.py --quiet
step fact-depends-tests python3 -m unittest scripts.tests.test_check_fact_depends_derived
# `fact-dag` measures the ledger's dependency graph; this one DERIVES it. A
# kernel-route fact's `depends_on` is read out of the admitted proof term
# (`Kernel::theorem_dependencies`) instead of being transcribed -- 18 real edges
# were missing when this first ran, including two facts proved the same day.
step fact-depends python3 scripts/check-fact-depends-derived.py --quiet
step fact-derived-numbers-tests python3 -m unittest scripts.tests.test_check_fact_derived_numbers
# Same ledger, its PROSE: every number a fact states about its own
# `axiom_footprint` is re-derived from the array instead of re-read. The fact it
# was built from said "the 30 axioms" for three days after the array became 26.
step fact-derived-numbers python3 scripts/check-fact-derived-numbers.py --quiet
step autogenesis-chain-catalog-tests python3 -m unittest scripts.tests.test_create_autogenesis_chain_catalog
step autogenesis-chain-catalog python3 scripts/create-autogenesis-chain-catalog.py --check
step autogenesis-nursery-tests python3 -m unittest scripts.tests.test_check_autogenesis_nursery
step autogenesis-mathlib-nursery-split-tests python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_split
step autogenesis-nursery-dispatch-baseline-tests python3 -m unittest scripts.tests.test_create_autogenesis_nursery_dispatch_baseline
step autogenesis-nursery python3 scripts/check-autogenesis-nursery.py
step autogenesis-mathlib-nursery-split python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
step autogenesis-nursery-dispatch-baseline python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
step autogenesis-statement-adapter-rust cargo test -p axeyum-lean-import --test statement_adapter
step autogenesis-statement-adapter-tests python3 -m unittest scripts.tests.test_check_autogenesis_statement_adapter
step autogenesis-statement-adapter python3 scripts/check-autogenesis-statement-adapter.py
step autogenesis-statement-reflexivity-rust cargo test -p axeyum-lean-import --test statement_reflexivity_operation
step autogenesis-statement-reflexivity-tests python3 -m unittest scripts.tests.test_check_autogenesis_statement_reflexivity
step autogenesis-statement-reflexivity python3 scripts/check-autogenesis-statement-reflexivity.py
step autogenesis-statement-reflexivity-admission-tests python3 -m unittest scripts.tests.test_check_autogenesis_statement_reflexivity_admission
step autogenesis-statement-reflexivity-admission python3 scripts/check-autogenesis-statement-reflexivity-admission.py
step autogenesis-factorial-zero-admission python3 scripts/check-autogenesis-statement-reflexivity-admission.py --manifest artifacts/autogenesis/mathlib-factorial-zero-admission-v1.json
step autogenesis-reflexivity-coverage-rust cargo test -p axeyum-lean-import --example statement_reflexivity_coverage
step autogenesis-reflexivity-coverage-input-tests python3 -m unittest scripts.tests.test_create_autogenesis_reflexivity_coverage_input
step autogenesis-reflexivity-coverage-tests python3 -m unittest scripts.tests.test_check_autogenesis_reflexivity_coverage
step autogenesis-reflexivity-coverage python3 scripts/check-autogenesis-reflexivity-coverage.py
step autogenesis-type-slice-feasibility-tests python3 -m unittest scripts.tests.test_analyze_autogenesis_type_slices scripts.tests.test_check_autogenesis_type_slice_feasibility
step autogenesis-type-slice-feasibility python3 scripts/check-autogenesis-type-slice-feasibility.py
step autogenesis-checked-type-slice-replay-tests python3 -m unittest scripts.tests.test_check_autogenesis_checked_type_slice_replay
step autogenesis-checked-type-slice-replay python3 scripts/check-autogenesis-checked-type-slice-replay.py
step autogenesis-auto-param-binder-replay-tests python3 -m unittest scripts.tests.test_check_autogenesis_auto_param_binder_replay
step autogenesis-auto-param-binder-replay python3 scripts/check-autogenesis-auto-param-binder-replay.py
step autogenesis-type-slice-producer-census-tests python3 -m unittest scripts.tests.test_check_autogenesis_type_slice_producer_census
step autogenesis-type-slice-producer-census python3 scripts/check-autogenesis-type-slice-producer-census.py
step autogenesis-factorial-zero-family-tests python3 -m unittest scripts.tests.test_check_autogenesis_factorial_zero_family
step autogenesis-factorial-zero-family python3 scripts/check-autogenesis-factorial-zero-family.py
step autogenesis-mathlib-source-tests python3 -m unittest scripts.tests.test_check_autogenesis_mathlib_source
step autogenesis-mathlib-source python3 scripts/check-autogenesis-mathlib-source.py
step autogenesis-mathlib-candidate-tests python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_candidates
step autogenesis-mathlib-candidates python3 scripts/create-autogenesis-mathlib-candidates.py --check
step autogenesis-mathlib-dependency-tests python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_dependency_components
step autogenesis-mathlib-dependencies python3 scripts/create-autogenesis-mathlib-dependency-components.py --check
step autogenesis-mathlib-review-tests python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_review
step autogenesis-mathlib-review python3 scripts/create-autogenesis-mathlib-nursery-review.py --check
step autogenesis-mathlib-fact-tests python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_fact_catalog
step autogenesis-mathlib-facts python3 scripts/create-autogenesis-mathlib-fact-catalog.py --check
step capability-assurance-tests python3 -m unittest scripts.tests.test_check_capability_assurance
# The mathematics strand's PRIMARY metric — "does a verdict come with an artifact
# a third party can check without trusting us?" — existed only as 101 prose
# `evidence` fields, so it drifted unmeasured from 4 areas to 11. Derived and
# floored now; a differential oracle is NOT counted as an external check.
step capability-assurance python3 scripts/check-capability-assurance.py --quiet
# The table names the function behind each capability; a row naming a route that
# no longer exists is a lie nothing else catches. Item A's "at minimum gated
# against the routes it describes".
step capability-routes python3 scripts/check-capability-routes.py
step capability-routes-controls python3 -m unittest scripts.tests.test_check_capability_routes
# A control that no gate RUNS cannot fail, so it is not a control. Measured
# 2026-08-17: 63 of 137 control modules were executed by nothing, and running the
# 51 that need no cargo found 6 that no longer even import. Ratchet, not a wall.
step control-tests-reachable python3 scripts/check-control-tests-reachable.py
step control-tests-reachable-controls python3 -m unittest scripts.tests.test_check_control_tests_reachable
# The mutation harness itself. Every "exactly one test died" in this repository
# rests on the mutant having been BUILT and RUN, and until 2026-08-18 nothing
# checked either: a mutation that broke compilation, and a suite that executed
# zero tests, both arrived as "not clean" and were scored as coverage. The four
# outcomes are now distinct, and `self-demo` produces one of each from a real
# mutation -- so a harness that cannot tell them apart fails here rather than
# reporting a number nobody measured.
step mutation-harness-controls python3 -m unittest scripts.tests.test_mutation_controls
step mutation-harness-four-outcomes python3 scripts/tests/mutation_controls.py self-demo
step adopted-controls scripts/check-adopted-controls.sh
# The trusted base, derived rather than eyeballed: the forward call-graph closure
# from every non-test caller of `Environment::insert_unchecked`. 5,129 function
# lines of 29,929 in axeyum-lean-kernel/src. Pins the admission gates and the SET
# of files on the path -- which is how `lean_export.rs` turned up inside it.
# The SMT-LIB -> rendered-statement transcription: item 3 of the residual trust
# surface, and the one it calls weaker than the kernel. Every hypothesis axiom a
# reconstructed module declares must bind back to an `(assert ...)` line of the
# query, with both sides normalized by independent Python parsers. Self-corrupts
# and requires the corruption to be caught.
step lra-hypothesis-binding python3 scripts/check-lra-hypothesis-binding.py
step lra-hypothesis-binding-controls python3 -m unittest scripts.tests.test_check_lra_hypothesis_binding
step kernel-trusted-core python3 scripts/check-kernel-trusted-core.py
step kernel-trusted-core-controls python3 -m unittest scripts.tests.test_check_kernel_trusted_core
step smt-evidence-tests python3 -m unittest scripts.tests.test_check_smt_evidence_certified
# Every settled SMT-route fact's own evidence command tests only the VERDICT
# (`... | tail -1` = unsat), which passes on an UNCERTIFIED refutation --
# demonstrated against a dedicated uncertified integer-square fixture. This
# requires certified=1. Two earlier live-fact controls became certifiable and
# were closed; the mutation control is now independent of ledger status.
step smt-evidence python3 scripts/check-smt-evidence-certified.py --quiet
# `facts` checks a fact against the SCHEMA; this checks its SMT-LIB
# `formal.statement` against the certificate it cites, by evaluating both at 400
# random rational configurations. The two are independent statements of the same
# theorem and nothing else compares them, which is how a fact's formal statement
# could drift from the artifact holding it up.
step facts-transcription python3 scripts/check-geometry-fact-transcription.py
# `facts` proves the ledger is self-consistent; this proves its evidence still
# holds. An unchecked certificate is not evidence, and `close-fact.py` enforces
# that at write time -- this is the same rule at gate time.
step facts-replay ./scripts/check-fact-evidence-replay.sh
# `cargo clippy --workspace --all-targets --all-features -- -D warnings` exits 0
# in two situations that look identical from outside: it linted everything and
# found nothing, or it linted NOTHING because cargo thought the cache was fresh.
# The second happened on 2026-08-13 over a cached example carrying
# `too_many_lines`. Cargo decides freshness by MTIME, and `git archive | tar -x`
# stamps every file with the commit time, so a snapshot build in a reused target
# dir hits this systematically. The wrapper reports how many of the workspace's
# targets it actually linted; the controls are
# `scripts/tests/test-gate-scope-controls.sh`.
step clippy ./scripts/check-clippy-complete.sh
step gate-controls ./scripts/tests/test-gate-scope-controls.sh
# Controls for two gates that check OTHER gates, which is where an agreeable
# checker does the most damage: the local-ci run recorder (a step that exits 0
# having run zero tests must record `vacuous`, and that guard was unreachable
# when written) and the fact scaffolder (a `checker_command` must be proved to
# fail before the fact exists). Seconds each, no workspace build.
step local-ci-record-controls ./scripts/tests/test-local-ci-record.sh
# Is the record itself still evidence of anything? A record can exist, be
# green, and describe a sha nobody has built on top of in days, or a branch
# that got rebased away, or a step array that disagrees with its own
# top-level verdict. ENFORCING as of 2026-08-19: it was `--report-only` while
# the only record in existence (a6ee37c6a-s4.json) was `verdict: FAIL`, since
# a gate that is red from the day it lands is a gate people learn to ignore.
# `57af69142-s4.json` is an all-pass record (5/5 steps, 7561 nextest + 179
# doctests, 6656 s) so the reason for report-only is gone.
#
# IF THIS REDS FOR YOU AND YOU CHANGED NOTHING RELEVANT, it is almost always
# STALE, not broken: the newest record is >48h old, and the fix is to run
# `scripts/local-ci.sh --record` (~110 min, one lock across the box) and
# commit the record it leaves in `artifacts/local-ci-runs/`. Do NOT re-add
# `--report-only` -- that turns the one gate that knows whether the
# authoritative sweep still passes back into a gate that cannot fail.
step local-ci-freshness ./scripts/check-local-ci-freshness.sh
step local-ci-freshness-controls ./scripts/tests/test-check-local-ci-freshness.sh
step new-fact-controls ./scripts/tests/test-new-fact-controls.sh
step lane-commit-controls ./scripts/tests/test-lane-commit.sh
step lane-push-controls ./scripts/tests/test-lane-push-target.sh
# The pre-push compile step must build examples/ and tests/. Without
# `--all-targets` it builds neither, and on 2026-08-20 a non-compiling
# workspace reached `main` under the hook's own "pushed SHA compiles" line.
step prepush-all-targets ./scripts/tests/test-prepush-checks-all-targets.sh
step prepush-worktree-controls ./scripts/tests/test-prepare-prepush-worktree.sh
step lean-golden-pin-controls ./scripts/tests/test-check-lean-golden-pins.sh
# ...and the ratchet that makes the two lines above impossible to forget. Both
# were written, both pass, and one of them was invoked by nothing for a day
# because registering a control is a manual step separate from writing it.
step control-registration ./scripts/check-control-registration.sh
# Ban the shell idioms that print a WRONG ANSWER while exiting 0. Both pinned
# patterns were real defects on 2026-08-20: `grep -q` piped under pipefail
# made the SAME tree report 7 orphans then 3, and `$?` after a pipeline
# reported exit=0 for a script that exits 1.
step shell-antipatterns ./scripts/check-shell-antipatterns.sh
# The Lean-reconstruction unit tests, moved OUT of `hooks/pre-push` on
# 2026-08-20. Measured idle: 268 tests, 294s, because each builds Lean
# preludes -- 90% of the hook's unit sweep and ~45% of every Rust push. They
# check that a Lean module is built correctly, not that a verdict is sound,
# so a daily gate is the right home. Neither aggregate gate ran the solver
# `--lib` sweep at all before this, so this is also the first time they are
# gated anywhere except the push hook and local-ci.
step solver-reconstruct-sweep cargo test -p axeyum-solver --lib --features full reconstruct::
# The one evidence test that builds Lean preludes: 292.973s of a 293.08s
# suite, measured idle. Skipped in `hooks/pre-push` for that reason, so this
# is where it runs.
step evidence-lean-module-wrapper cargo test -p axeyum-solver --features full --test evidence qf_nra_sos_certificate_wrapper_carries_lean_module
# The axiom-freedom measurements. `axreal: axiom=30` is the whole remaining
# trusted surface and the claim that the shipped route no longer reaches it
# rested, until 2026-08-18, on three examples that NO gate ran -- zero
# invocations across scripts/, justfile and .github/workflows/, while two ADRs
# cited them as evidence. Each `--require-*` flag makes the exit status depend
# on the finding. `--release` because they build the whole constructed
# N/Z/Q/setoid development: 509s release against multiples of that in debug.
step axiom-freedom-front-door cargo run --release -q -p axeyum-solver --features full \
    --example front_door_carrier -- --require-axiom-free
step axiom-freedom-interface-pin cargo run --release -q -p axeyum-solver --features full \
    --example ring_interface_pin -- --require-identical
step axiom-freedom-generalized cargo run --release -q -p axeyum-solver --features full \
    --example ordered_ring_refutation -- --require-empty
step axiom-freedom-constructed cargo run --release -q -p axeyum-solver --features full \
    --example ordered_ring_refutation -- --constructed-reals
step autogenesis-knowledge-controls ./scripts/check-autogenesis-knowledge-controls.sh
step autogenesis-proposer-isolation ./scripts/check-autogenesis-proposer-isolation.sh
step autogenesis-induction-search ./scripts/check-autogenesis-induction-search.sh
step autogenesis-apply-search ./scripts/check-autogenesis-apply-search.sh
# `frontier_*` runs in its own serialized step below: those ratchets are
# wall-clock-budget based, so contention from the rest of the suite shrinks the
# measured frontier and reports a false REGRESSION (measured 2026-07-30).
# Wrapped so the sweep prints the number of tests it ran (an emptied suite exits
# 0 printing "running 0 tests ... ok") and cannot replay a cached test binary
# over source it never compiled.
step test   ./scripts/check-workspace-tests.sh
step frontier cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1
# The gate-liveness ratchet: proves the gates above still RUN something. A suite
# emptied by a new `#![cfg(feature = ...)]` exits 0 and prints "running 0 tests
# ... ok"; the corpus `:status` sweep sat inert that way for 15 days. Compiles
# but does not execute (`--list`), so it is cheap.
step gate-liveness ./scripts/check-gate-liveness.sh
# The golden-Lean-module gate: every suite that pins a rendered Lean module's
# bytes, discovered from the source rather than listed, plus the banner pin that
# is the one place a module-header change is meant to be seen. Four of these were
# red on `main` for a day in 2026-08 because no pre-merge gate ran a `tests/*.rs`
# integration target of theirs; see the script's header.
step golden-lean-pins ./scripts/check-lean-golden-pins.sh
# The real-Lean gate. Every suite that hands a generated module to an EXTERNAL
# `lean` printed `ok` on a machine where Lean 4.30.0 was installed but not on
# `PATH` (elan keeps toolchains under ~/.elan/toolchains/), so nothing outside
# this repository had ever read our exported bytes -- and when one finally did,
# it REJECTED them (a5975725f). This discovers the toolchain, sets
# AXEYUM_REQUIRE_LEAN=1 so a missing binary FAILS, and prints how many Lean
# invocations actually happened. AXEYUM_ALLOW_NO_LEAN=1 for a machine with none.
# Every `crates/axeyum-lean-kernel/tests/*.rs` must be in EXACTLY ONE of {runs at
# push time, owned by the real-Lean gate below}. `hooks/pre-push` ran that crate
# wholesale, so its fifteen real-Lean suites ran twice on every push (2,396 s,
# measured 2026-08-19); running only the non-Lean half is safe exactly while the
# other half is provably owned, which is what this asserts. Membership is
# discovered from the source, so a new suite cannot land outside both halves.
step kernel-suite-partition-controls python3 -m unittest scripts.tests.test_check_kernel_suites
step kernel-suite-partition ./scripts/check-kernel-suites.sh --list
step lean-toolchain-policy ./scripts/tests/test-lean-toolchain-policy.sh
step lean-gate ./scripts/check-lean-gate.sh
export RUSTDOCFLAGS="-D warnings" # match CI's deny-warnings rustdoc
step doc    cargo doc --workspace --all-features --no-deps
step lean-u2-test-authority-tests python3 -m unittest scripts.tests.test_lean_u2_test_authority
step lean-u2-test-authority python3 scripts/gen-lean-u2-test-authority.py --check
step lean-u2-ci-profile-tests python3 -m unittest scripts.tests.test_lean_u2_official_ci_profiles
step lean-u2-ci-profiles python3 scripts/gen-lean-u2-official-ci-profiles.py --check
step lean-u2-child-shard-tests python3 -m unittest scripts.tests.test_lean_u2_official_child_shards
step lean-u2-child-shards python3 scripts/gen-lean-u2-official-child-shards.py --check
step lean-u2-native-surface-tests python3 -m unittest scripts.tests.test_lean_u2_native_surface_classification
step lean-u2-native-surface python3 scripts/gen-lean-u2-native-surface-classification.py --check
step lean-u2-native-content-tests python3 -m unittest scripts.tests.test_lean_u2_native_surface_content
step lean-u2-native-content python3 scripts/gen-lean-u2-native-surface-content.py --check
step lean-u2-native-dependency-tests python3 -m unittest scripts.tests.test_lean_u2_native_dependency
step lean-u2-native-dependency python3 scripts/gen-lean-u2-native-dependency.py --check
step lean-u2-native-header-contract-tests python3 -m unittest scripts.tests.test_lean_u2_native_dependency_m2_1
step lean-u2-native-header-contract python3 scripts/lean_u2_native_dependency_m2_1.py check-contract
step lean-execution-evidence-tests python3 -m unittest scripts.tests.test_lean_execution_evidence
step lean-execution-evidence python3 scripts/gen-lean-execution-evidence.py --check
step lean-execution-process-tests python3 -m unittest scripts.tests.test_lean_execution_process
step lean-execution-process python3 scripts/lean_execution_process.py result --check
step lean-execution-store-tests python3 -m unittest scripts.tests.test_lean_execution_store
step lean-execution-store python3 scripts/lean_execution_store.py result --check
step lean-u2-official-execution-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution
step lean-u2-official-execution-r2-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_r2
step lean-u2-official-execution-r3-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_r3
step lean-u2-official-execution-r3-result-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_r3_result
step lean-u2-official-execution-r3-result python3 scripts/lean_u2_official_execution_r3_result.py result --check
step lean-u2-official-execution-m2-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2
step lean-u2-official-execution-m2 python3 scripts/lean_u2_official_execution_m2.py --check
step lean-u2-official-execution-m2-store-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_store
step lean-u2-official-execution-m2-store python3 scripts/lean_u2_official_execution_m2_store.py --check
step lean-u2-official-execution-m2-run-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_run
step lean-u2-official-execution-m2-run python3 scripts/lean_u2_official_execution_m2_run.py offline-check
step lean-u2-official-execution-m2-r2 python3 scripts/lean_u2_official_execution_m2_r2.py offline-check
step lean-u2-official-execution-m2-r3-tests python3 -m unittest scripts.tests.test_lean_u2_official_execution_m2_r3
step lean-u2-official-execution-m2-r3 python3 scripts/lean_u2_official_execution_m2_r3.py offline-check
step lean-u2-official-execution-m2-r3-incomplete python3 scripts/lean_u2_official_execution_m2_r3.py validate-incomplete
step lean-complete-parity-tests python3 -m unittest scripts.tests.test_lean_complete_parity
step lean-complete-parity python3 scripts/gen-lean-complete-parity.py --check
step lean-construct-matrix-tests python3 -m unittest scripts.tests.test_lean_official_construct_matrix
step lean-construct-matrix python3 scripts/check-lean-official-construct-matrix.py --check
step lean-strict-positivity-tests python3 -m unittest scripts.tests.test_lean_strict_positivity
step lean-strict-positivity python3 scripts/check-lean-strict-positivity.py --check
step lean-strict-positivity-m3-tests python3 -m unittest scripts.tests.test_lean_strict_positivity_m3
step lean-strict-positivity-m3 python3 scripts/check-lean-strict-positivity-m3.py --check
step lean-recursive-ih-m0-tests python3 -m unittest scripts.tests.test_lean_recursive_induction_hypotheses
step lean-recursive-ih-m0 python3 scripts/check-lean-recursive-induction-hypotheses.py --check
step lean-mutual-groups-m0-tests python3 -m unittest scripts.tests.test_lean_mutual_inductive_groups
step lean-mutual-groups-m0 python3 scripts/check-lean-mutual-inductive-groups.py --check
step lean-nested-inductive-m0-tests python3 -m unittest scripts.tests.test_lean_nested_inductive_elimination
step lean-nested-inductive-m0 python3 scripts/check-lean-nested-inductive-elimination.py --check
step lean-construct-matrix-stage-b python3 scripts/freeze-lean-official-construct-matrix-stage-b.py --check
step lean-construct-matrix-product-freeze python3 scripts/freeze-lean-official-construct-matrix-product.py --check
# The axiom ledger: the SHA-256 binding of every prelude axiom type, and since
# ADR-0465 every count this project publishes about the trusted prelude surface.
# Axiom-freedom is this project's headline metric, and this step ran ONLY in
# `just check` until 2026-08-14 -- so the documented fresh-machine gate did not
# bind it. Found by `scripts/check-aggregate-scope.sh`, which now pins the
# remaining divergence between the two aggregate gates.
step lean-axiom-ledger-tests python3 -m unittest scripts.tests.test_lean_axiom_ledger
step lean-axiom-ledger python3 scripts/gen-lean-axiom-ledger.py --check
step foundational-resources ./scripts/check-foundational-resources.sh
# The claim ledger's structural gates ran ONLY from `just claims` (and the
# certificate pass, which needs the gitignored drat-trim clone, deliberately
# stays out of both). These two need nothing external and take seconds, so the
# no-`just` fallback had no reason to be blind to them -- and the dashboard was
# gated by nothing anywhere, which is how it came to report 38 claims against an
# actual 104. See docs/refactor-2026-08/gate-divergence-2026-08-14.md.
step claims-validate python3 scripts/validate-claims.py
step claims-dashboard python3 scripts/gen-claims-dashboard.py --check
step rules-as-code-generate python3 scripts/gen-rules-as-code-dashboard.py
step rules-as-code-validate python3 scripts/validate-rules-as-code.py
step rules-as-code-query-summary python3 scripts/query-rules-as-code.py summary
step rules-as-code-query-coverage-domain python3 scripts/query-rules-as-code.py coverage --by domain --require-any
step rules-as-code-query-coverage-validation python3 scripts/query-rules-as-code.py coverage --by validation --require-any
step rules-as-code-query-coverage-fragment-json python3 scripts/query-rules-as-code.py coverage --by fragment --format json --require-any
step rules-as-code-query-pack python3 scripts/query-rules-as-code.py packs --text procurement --require-any
step rules-as-code-query-checks python3 scripts/query-rules-as-code.py checks --pack procurement_scoring_v0 --proof-status checked --require-any
step rules-as-code-query-families python3 scripts/query-rules-as-code.py families --pack procurement_scoring_v0 --text quality --require-any
step rules-as-code-query-rows python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family bounded_awards --text 2026-08-02 --limit 3 --require-any
step rules-as-code-query-grant-pack python3 scripts/query-rules-as-code.py packs --pack grant_allocation_v0 --require-any
step rules-as-code-query-grant-checks python3 scripts/query-rules-as-code.py checks --pack grant_allocation_v0 --validation qf_lra_farkas_solver_regression --proof-status checked --require-any
step rules-as-code-query-grant-families python3 scripts/query-rules-as-code.py families --pack grant_allocation_v0 --text balanced --require-any
step rules-as-code-query-grant-rows python3 scripts/query-rules-as-code.py rows --pack grant_allocation_v0 --family balanced_budget_allocations --text 1/2 --limit 3 --require-any
step rules-as-code-query-monotonicity python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
step rules-as-code-query-adjacent python3 scripts/query-rules-as-code.py families --text adjacent --require-any
step rules-as-code-query-quality-rows python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family quality_monotonicity_adjacent --limit 3 --require-any
step rules-as-code-generated-clean git diff --exit-code docs/rules-as-code/generated
step smtcomp-resume ./scripts/check-smtcomp-resume.sh
# PLAN.md and the ADR index are generated views over per-lane sources. They are
# the two files concurrent lanes clobbered four times on 2026-08-14 (67 and 60
# touches in 24 hours), because the session protocol told every lane to append
# to them. These gates make a hand edit a failure instead of a lost line.
step autogenesis-proof-gap-source python3 scripts/gen-proof-gap-matrix.py --check
step autogenesis-baseline-tests python3 -m unittest scripts.tests.test_gen_autogenesis_baseline
step autogenesis-snapshot-tests python3 -m unittest scripts.tests.test_create_autogenesis_snapshot
step autogenesis-catalog-tests python3 -m unittest scripts.tests.test_create_autogenesis_proposer_catalog
step autogenesis-apply-proposer-tests python3 -m unittest scripts.tests.test_autogenesis_apply_proposer
step autogenesis-apply-verifier-tests python3 -m unittest scripts.tests.test_verify_autogenesis_apply_proposals
step autogenesis-induction-proposer-tests python3 -m unittest scripts.tests.test_autogenesis_induction_proposer
step autogenesis-induction-verifier-tests python3 -m unittest scripts.tests.test_verify_autogenesis_induction_proposals
step autogenesis-premise-evidence-tests python3 -m unittest scripts.tests.test_create_autogenesis_premise_evidence
step autogenesis-premise-transition-tests python3 -m unittest scripts.tests.test_create_autogenesis_premise_transition
step autogenesis-accepted-event-tests python3 -m unittest scripts.tests.test_create_autogenesis_accepted_event
step autogenesis-fact-transaction-tests python3 -m unittest scripts.tests.test_prepare_autogenesis_fact_transaction
step autogenesis-fact-admission-tests python3 -m unittest scripts.tests.test_apply_autogenesis_fact_transaction
step autogenesis-readiness-delta-tests python3 -m unittest scripts.tests.test_create_autogenesis_readiness_delta
step autogenesis-operation-registry python3 scripts/validate-autogenesis-operations.py
step autogenesis-operation-registry-tests python3 -m unittest scripts.tests.test_validate_autogenesis_operations
step autogenesis-authoritative-comparison-tests python3 -m unittest scripts.tests.test_compare_autogenesis_authoritative_chains
step autogenesis-result python3 scripts/check-autogenesis-1-result.py
step autogenesis-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_1_result
step fact-frontier-tests python3 -m unittest scripts.tests.test_fact_frontier
step autogenesis-operation-execution-tests python3 -m unittest scripts.tests.test_execute_autogenesis_operation
step autogenesis-fact-operation-tests python3 -m unittest scripts.tests.test_check_autogenesis_fact_operation
step autogenesis-baseline python3 scripts/gen-autogenesis-baseline.py --check
step gen-plan-tests python3 -m unittest scripts.tests.test_gen_plan
step gen-plan       python3 scripts/gen-plan.py --check
step adr-index-tests python3 -m unittest scripts.tests.test_gen_adr_index
step adr-index      python3 scripts/gen-adr-index.py --check
# The formalized-math strand's status block, re-derived from the tree.
step import-status-tests python3 -m unittest scripts.tests.test_check_import_status
step import-status  python3 scripts/check-import-status.py
# The `axeyum-solver` decomposition ratchet (docs/refactor-2026-08/03). The
# crate is 46% of the workspace and the plan is to cut crates out of it; a cut
# point with a dependency cycle across it is not a cut point. Fails when a
# module that was acyclic enters a cycle, or when anything outside the
# evidence/reconstruction layer starts depending on it. The measurement is not a
# grep -- doc links and `#[cfg(test)]` code invent edges, and the crate's own
# re-export facade hides 340 real ones -- so the unit tests pin all three.
step solver-module-graph-tests python3 -m unittest scripts.tests.test_analyze_solver_module_graph
step solver-module-graph python3 scripts/analyze_solver_module_graph.py --check
# Lean prelude reuse (ADR-0464) checked from outside the crate: byte-identical
# example output with the cache on and off, plus counter liveness so "the flag
# changed nothing" cannot pass as "the flag was ignored".
step prelude-reuse  ./scripts/check-prelude-reuse-equivalence.sh
# Do this script and `just check` still run the same gates? They ran 61 and 112
# steps on 2026-08-14 while both documents claimed they were the same gate. This
# does not sync them; it pins the divergence so it cannot GROW unnoticed.
step aggregate-scope ./scripts/check-aggregate-scope.sh
step plan-authority python3 scripts/check-plan-authority.py
step links         ./scripts/check-links.sh
# ADR numbers are a shared append point ACROSS CHECKOUTS, which `adr-index`
# above cannot see (it only reads this working tree): two lanes in two clones
# can each read "the highest number I can see", allocate the same one for two
# different decisions, and merge clean, because the filenames differ by slug
# so git never conflicts. Measured 2026-08-18: `origin/main` and this branch
# had claimed 0471-0474 twice, AND (found live, by this exact gate)
# 0468-0470 a second time. `--check-remote` diffs this tree's ADR numbers
# against `origin/main`'s and fails on a real collision, naming it and the
# next free number; it does NOT fail when `origin/main` is unresolvable (no
# fetch, no `origin`, not a git checkout) or, on a clean result, when the
# fetched ref is stale beyond `--max-staleness-hours` -- see `check_remote`'s
# docstring in gen-adr-index.py for why fail-open is the deliberate side of
# that trade in both cases, and how a found collision is NOT forgiven by
# either one. Unlike the justfile's `check` recipe, `step` here never aborts
# the run on a failing step, so this can stay next to `adr-index` without
# hiding whether `links` (or anything else) passed.
step adr-remote-collisions python3 scripts/gen-adr-index.py --check-remote

if [ "$list_only" = "1" ]; then
  echo "check: $ran steps" >&2
  exit 0
fi

# The step FLOOR. A gate that silently loses steps is the aggregate version of
# the "running 0 tests ... ok" trap: the exit status is identical whether it ran
# 61 steps or 2. Measured 2026-08-14: 89 steps here. The floor sits below that so
# ordinary churn does not trip it. Raising it as steps are added is expected;
# LOWERING it needs a reason in the commit message. Controls 4 and 6 in
# `scripts/tests/test-gate-scope-controls.sh` cover the listing and this floor.
STEP_FLOOR=80
echo "check: ran $ran steps (floor $STEP_FLOOR), ${#failed_steps[@]} failed"
if [ "$ran" -lt "$STEP_FLOOR" ]; then
  echo "check: only $ran steps ran, below the committed floor of $STEP_FLOOR --" \
       "steps have been removed. If that was deliberate, lower STEP_FLOOR in" \
       "this file and say why." >&2
  fail=1
fi
# NOT run here, and named rather than passed over silently: `cargo deny check`
# (needs cargo-deny installed), the z3 differential fuzzes (C/C++ leaf dependency,
# ADR-0002; CLAUDE.md lists them as the linear-arithmetic pre-merge gate), the
# wasm32 build, and every step `just check` has that this script does not --
# `scripts/check-aggregate-scope.sh` enumerates that divergence.
echo "check: not run here -- cargo deny, the z3 differential fuzzes, the wasm32" \
     "target build; run scripts/check-aggregate-scope.sh for the just-vs-check.sh divergence"

if [ "$fail" -ne 0 ]; then
  if [ ${#failed_steps[@]} -gt 0 ]; then
    printf 'check: FAILED steps: %s\n' "${failed_steps[*]}" >&2
  fi
  echo "check: one or more gates FAILED" >&2
  exit 1
fi
echo "check: all $ran gates passed"
