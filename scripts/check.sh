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
step capability-assurance-tests python3 -m unittest scripts.tests.test_check_capability_assurance
# The mathematics strand's PRIMARY metric — "does a verdict come with an artifact
# a third party can check without trusting us?" — existed only as 101 prose
# `evidence` fields, so it drifted unmeasured from 4 areas to 11. Derived and
# floored now; a differential oracle is NOT counted as an external check.
step capability-assurance python3 scripts/check-capability-assurance.py --quiet
step smt-evidence-tests python3 -m unittest scripts.tests.test_check_smt_evidence_certified
# Every settled SMT-route fact's own evidence command tests only the VERDICT
# (`... | tail -1` = unsat), which passes on an UNCERTIFIED refutation --
# demonstrated against neg-no-integer-square-is-minus-one.smt2. This requires
# certified=1. (The control was neg-barber-no-such-barber.smt2 until 2026-08-17,
# when that instance became certifiable and its fact was closed.)
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
# The real-Lean gate. Every suite that hands a generated module to an EXTERNAL
# `lean` printed `ok` on a machine where Lean 4.30.0 was installed but not on
# `PATH` (elan keeps toolchains under ~/.elan/toolchains/), so nothing outside
# this repository had ever read our exported bytes -- and when one finally did,
# it REJECTED them (a5975725f). This discovers the toolchain, sets
# AXEYUM_REQUIRE_LEAN=1 so a missing binary FAILS, and prints how many Lean
# invocations actually happened. AXEYUM_ALLOW_NO_LEAN=1 for a machine with none.
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
