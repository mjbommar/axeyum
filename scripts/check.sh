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

# THIS GATE TAKES A CARGO SLOT, and until 2026-08-27 it took none.
#
# CLAUDE.md's standing rule is "heavy cargo goes through
# scripts/cargo-serialized.sh". Measured that day, the three things that
# actually consume this box -- `hooks/pre-push`, this script, and the justfile's
# `check` recipe -- called it ZERO times between them; the only real callers in
# `scripts/` were `check-kernel-stack-envelope.sh` and the mutation harness. The
# semaphore was well built, documented, and unwired, so the admitted concurrency
# on this host was not five. It was unbounded, and the push battery starved.
#
# ONE slot for the whole run rather than one per `cargo` call: this script fires
# ~100 of them, and per-call acquisition would still let five aggregate gates run
# at once while adding 100 lock round-trips. The nested calls are re-entrant
# (`AXEYUM_CARGO_SLOT_HELD`), so a wrapped script calling a wrapped script does
# not deadlock -- which it would, silently and for 5,400 s, without that marker.
#
# `--batch` deliberately applies no memory scope to this script: it is a
# supervisor, and a `MemoryMax` on the aggregate would SIGKILL the gate at a
# threshold no individual step exceeded, reporting a failure that is not one.
# Each nested cargo job still gets its own ceiling.
#
# AXEYUM_CHECK_NO_SLOT=1 opts out (for a nested or already-admitted caller).
if [ "${AXEYUM_CHECK_LIST:-0}" != "1" ] \
   && [ "${AXEYUM_CHECK_NO_SLOT:-0}" != "1" ] \
   && [ "${AXEYUM_CARGO_SLOT_HELD:-0}" != "1" ] \
   && [ -x scripts/cargo-serialized.sh ]; then
  # `scripts/check.sh` and not `$0`: the `cd` above has already put us at the
  # repository root, so this path is correct however the script was invoked,
  # whereas a relative `$0` from another directory would not survive the `cd`.
  export AXEYUM_CHECK_NO_SLOT=1
  exec scripts/cargo-serialized.sh --batch scripts/check.sh "$@"
fi

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

# Set to `optional:` around a block whose steps need a toolchain this script
# does not require. List mode then emits `optional:<name>` in FIELD 1, which
# `scripts/check-aggregate-scope.sh` never reads (it does `cut -f2-`, so the
# scope comparison still sees the command and still counts the step) while
# `scripts/check-fast.sh` CAN read it and decline to run what this host cannot.
#
# Measured 2026-08-30. Making list mode host-independent was right for the scope
# question -- gating the LISTING on `.venv` made the comparison non-reproducible
# across developers. But `check-fast.sh` enumerates through this same list and
# RUNS every line with no toolchain guard of its own, so the same change turned
# six correctly-skipped steps into six failures. The two consumers are asking
# different questions -- "what does this gate cover?" versus "what can I run
# here?" -- and the list has to answer both.
step_prefix=""

# ---------------------------------------------------------------------------
# THE PER-STEP TIME CAP (ADR-0623). Until 2026-08-30 this gate had ZERO
# timeout-guarded steps, so ONE hung step hung the whole aggregate gate forever.
#
# That is not a hypothetical. A run started 16:43 was reaped at 02:51 the next
# morning -- over NINE HOURS, 0% CPU at every level of the process tree,
# reparented to init, its log last written at 17:33 and stopped mid
# `=== facts-replay ===`. Nothing timed it out and nothing noticed.
#
# The cost is not one lost run. A gate people cannot finish is a gate people
# stop running, and this repository has already measured what that produces: 64
# failing steps in one census, 32 of them pre-existing, and
# `scripts/check-local-ci-freshness.sh` -- the gate whose job is to notice the
# battery has gone stale -- sat RED for 265 h across 3,974 commits because its
# only caller was the battery that had gone stale.
#
# CHOOSING THE CAP. A cap that fires on a HEALTHY step is worse than no cap: a
# gate that reports spurious timeouts is one people learn to ignore, which is
# the exact failure being fixed here. So the default is generous, and the
# handful of steps with a recorded cost above it get a named override in
# `step_cap_for` rather than the default being raised for all 400.
#
# THE OUTCOME IS A THIRD ONE, never a pass. `scripts/check-fast.sh` established
# the contract -- ok / FAILED / DEFERRED, never two -- and this follows it: a
# timed-out step is UNCHECKED, is counted and named separately from a failure,
# and sets `fail`, so the gate can never go green by going blind.
# THE NUMBERS, and what each is anchored to. Every one is a repository
# measurement, cited so the next person can re-derive it rather than inherit it.
#
#   STEP_CAP        30 min   The non-cargo default. The whole non-cargo half of
#                            this gate -- all 355 of those steps -- extrapolates
#                            to ~45 minutes (docs/research/11-design-review/
#                            2026-08-29-process-retrospective.md:83, from a
#                            71-step sample measured at 549 s). So this cap says
#                            no single cheap step may take two thirds of what all
#                            of them together take. The heaviest 15 of that
#                            sample accounted for 528 s BETWEEN them; contention
#                            on this box is documented at 4-7x uniformly
#                            (2026-08-27-gate-throughput.md:22-26), and 30 min
#                            still clears the worst of those with room.
#
#   STEP_CAP_CARGO   2 h     Anything that builds. The heaviest measured cargo
#                            steps in THIS file are axiom-freedom-* at 509 s
#                            release (check.sh:533), solver-reconstruct-sweep at
#                            294 s (:516), evidence-lean-module-wrapper at 293 s
#                            (:523) and frontier at 216 s. At the documented 7x
#                            contention multiplier the worst of those projects to
#                            ~3,560 s, so 2 h is roughly 2x the worst credible
#                            contended run -- and it also has to absorb a COLD
#                            target directory, which in a fresh lane worktree
#                            lands entirely on whichever cargo step runs first.
#
#   STEP_CAP_TEST    4 h     `step test` -> check-workspace-tests.sh. This is the
#                            one step nobody has ever timed: docs/plan/notes/
#                            102-local-ci-run.md:136 says so outright and
#                            estimates ~2 h. Its closest recorded analogue is the
#                            workspace nextest sweep in
#                            artifacts/local-ci-runs/57af69142-s4.json at
#                            6,588 s, which is the highest-confidence single-step
#                            number in the repository because it is a recorded
#                            artifact rather than prose. 4 h is 2.2x that.
#
#   STEP_CAP_FACTS   3 h     The ledger sweep -- see step_cap_for below.
STEP_CAP="${AXEYUM_CHECK_STEP_CAP:-1800}"
STEP_CAP_CARGO="${AXEYUM_CHECK_CAP_CARGO:-7200}"
STEP_CAP_TEST="${AXEYUM_CHECK_CAP_TEST:-14400}"
STEP_CAP_FACTS="${AXEYUM_CHECK_CAP_FACTS_REPLAY:-10800}"
STEP_KILL_GRACE="${AXEYUM_CHECK_STEP_KILL_GRACE:-30}"

# Per-step overrides for steps whose RECORDED cost exceeds the default. Keep
# this list short and keep the evidence beside each entry: an override with no
# measurement behind it is how a cap silently becomes decoration.
#
# Takes the step NAME and its COMMAND, because neither alone is enough. The name
# is needed for `clippy`, `prelude-reuse` and `foundational-resources`, whose
# command strings never say "cargo" but which shell out to it; the command is
# needed because a `*cargo*` glob covers the 24 direct cargo steps AND any added
# later, so a new cargo step is not silently held to the cheap default.
step_cap_for() {
  local name="$1"; shift
  case "$name" in
    # The ledger sweep. 2,018 settled facts / 4,122 `checker_command`s, 4,064 of
    # which invoke cargo, and a row may declare `checker_seconds` up to 490 and
    # be granted 2x that -- 980 s for one row. Its own header records 251.8 s
    # idle and 747.7 s under contention, against a ledger roughly a fifth of
    # today's size; scaling that gives ~3,700 s, and this is ~3x it. The budget
    # exists to bound the pathology, not to discipline a slow run: if every row
    # timed out and retried, the per-row budgets sum to 993,952 s -- 11.5 days.
    facts-replay) echo "$STEP_CAP_FACTS"; return 0 ;;
    test)         echo "$STEP_CAP_TEST";  return 0 ;;
    clippy|prelude-reuse|foundational-resources|kernel-suite-partition)
                  echo "$STEP_CAP_CARGO"; return 0 ;;
  esac
  # A `case` glob and NOT `printf | grep -q`: CLAUDE.md's banned-idiom list is
  # explicit that `grep -q` consuming a pipeline under `set -o pipefail`
  # SIGPIPEs its producer for status 141, which `pipefail` then reports as "not
  # found" -- the same tree answering differently on consecutive runs.
  # `check-fast.sh` makes the same choice at the same decision for this reason.
  case "$*" in
    *cargo*) echo "$STEP_CAP_CARGO"; return 0 ;;
  esac
  echo "$STEP_CAP"
}

if [ "$list_only" != "1" ] && ! command -v timeout >/dev/null 2>&1; then
  # Running uncapped is the state this gate was just rescued from, so refuse
  # rather than fall back to it silently. Exit 2 is distinct from a step
  # failure, matching `check-fast.sh`'s vacuity guard.
  echo "check: FATAL -- coreutils \`timeout\` is not on PATH, so no per-step cap" \
       "can be applied. Running uncapped is how this gate hung for nine hours;" \
       "install coreutils rather than removing the cap." >&2
  exit 2
fi

timed_out_steps=()

step() {
  local name="$1"; shift
  ran=$((ran + 1))
  if [ "$list_only" = "1" ]; then
    printf '%s\t%s\n' "${step_prefix}${name}" "$*"
    return 0
  fi
  local cap; cap="$(step_cap_for "$name" "$@")"
  local t0=$SECONDS
  echo "=== $name (cap ${cap}s) ==="
  # `</dev/null` because a gate step must never block on stdin. It also matters
  # for the cap itself: without `--foreground`, `timeout` puts the child in its
  # OWN process group, so a step that read a terminal would take SIGTTIN and
  # stop rather than run. No step here reads stdin; this makes that explicit.
  #
  # NOT `--foreground`, deliberately. The default puts the child in a new
  # process group and signals the GROUP, so a step's children die with it.
  # Measured here: `timeout 2 sh -c 'sleeper | cat'` leaves 0 survivors where
  # the identical uncapped command leaves 2. A cap that kills only the direct
  # child leaves the grandchild holding whatever lock it holds -- which is
  # exactly the defect this same commit fixes in the ledger sweep.
  timeout --kill-after="$STEP_KILL_GRACE" "$cap" "$@" </dev/null
  local st=$?
  local el=$(( SECONDS - t0 ))
  if [ "$st" -eq 0 ]; then
    echo "--- $name: ok (${el}s)"
  elif { [ "$st" -eq 124 ] || [ "$st" -eq 137 ]; } && [ "$el" -ge "$cap" ]; then
    # THIRD OUTCOME. Not a pass, not a failure -- UNCHECKED.
    #
    # The elapsed test is load-bearing and not decoration: 124 and 137 are
    # ordinary exit codes a step is free to return on its own, and a step that
    # exits 124 in two seconds has FAILED, not timed out. Without the
    # conjunction a gate could be made green-ish by teaching a broken step to
    # exit 124.
    echo "--- $name: TIMED OUT after ${el}s (cap ${cap}s) -- UNCHECKED, neither passed nor failed"
    timed_out_steps+=("$name(cap ${cap}s)")
    fail=1
  else
    echo "--- $name: FAILED (exit $st, ${el}s)"
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
step validate-facts-tests python3 -m unittest scripts.tests.test_validate_facts
step validate-facts-allowlist-tests python3 -m unittest scripts.tests.test_validate_facts_allowlist
step shape-duplicates-tests python3 -m unittest scripts.tests.test_check_shape_duplicates
step theorem-inventory-completeness-tests python3 -m unittest scripts.tests.test_theorem_inventory_completeness
step absence-claims-tests python3 -m unittest scripts.tests.test_check_absence_claims
step settled-fact-statement-tests python3 -m unittest scripts.tests.test_settled_fact_statements
step settled-fact-statements python3 scripts/check-settled-fact-statements.py
# An `ml430` mirror's top-level `statement` is a prose reference BY NAME, so the
# Mathlib proposition lives only in `formal.statement`. Nineteen had it
# overwritten with our own `render_lean` output, and the mirror claim -- "we
# proved what Mathlib states" -- then could not be checked from the fact at all.
# The check is exact, not a token screen: 362 of 374 mirrors are hash-pinned by
# a preregistered catalog.
step mirror-statement-fidelity python3 scripts/check-mirror-statement-fidelity.py
step fact-dag-tests python3 -m unittest scripts.tests.test_check_fact_dag
step fact-dag python3 scripts/check-fact-dag.py --quiet
# ADR-0584. The kernel type checker recurses over the term with no bound, so a
# deep enough declaration exhausts the stack and the process ABORTS -- exit 134,
# which looks exactly like a broken tool or an absent declaration and has been
# read as both. This re-derives the required stack per prelude and reds when it
# outgrows the pin, with the number in the message. Placed HERE, before
# `fact-depends`, because that checker runs the full constructed environment
# build and is one of the things a blown envelope silently disables.
# Release profile (~30 s); `--profile debug` is the ~4 min form that matches
# where `cargo test` actually runs.
step kernel-stack-envelope-controls scripts/tests/test-kernel-stack-envelope.sh
step kernel-stack-envelope scripts/check-kernel-stack-envelope.sh --check --profile release
# Static regression guard: a `#[test]` reaching build_creal_prelude/
# build_complex_prelude/build_cpoint_prelude/build_creal_model_of_arith
# without an on_a_deep_stack guard on its local call path. Complements
# kernel-stack-envelope above (which re-measures the STACK REQUIREMENT) by
# catching the actual regression shape that hit three modules in one session:
# a new call site that never gets protected in the first place.
step deep-stack-call-sites-controls scripts/tests/test-deep-stack-call-sites.sh
step deep-stack-call-sites python3 scripts/check-deep-stack-call-sites.py
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
step autogenesis-holdout-isolation-tests python3 -m unittest scripts.tests.test_check_autogenesis_holdout_isolation
step autogenesis-holdout-isolation python3 scripts/check-autogenesis-holdout-isolation.py
# The nursery extension's reproduction gate. ADR-0615 left this deliberately
# unregistered because it was red on arrival from one fact's statement drift;
# that is resolved, and ADR-0616 made it load-bearing -- R3 now compares the
# UNATTESTED cohort against the attested one, so a hand-edit to
# `surface_validation` would change what the ceiling permits and this is what
# re-derives it. It also refuses a preregistered `formal.statement` that has
# been rewritten.
step autogenesis-nursery-refill-tests python3 -m unittest scripts.tests.test_gen_autogenesis_nursery_refill
step autogenesis-nursery-refill python3 scripts/gen-autogenesis-nursery-refill.py --check
# The flywheel's input queue. `fact-frontier.py` prints the bands but never a
# number that reaches zero, and exits 0 either way -- so a queue that has run
# out reads exactly like a queue being worked down. This one fails when the
# dispatchable set empties, and screens candidate mirrors for the four
# construction-level divergences before they are preregistered.
step dispatchable-frontier-tests bash scripts/tests/test-dispatchable-frontier.sh
step dispatchable-frontier python3 scripts/check-dispatchable-frontier.py
# ...and the question that comes NEXT, which the frontier cannot answer: can the
# queue be refilled at all? Measured 2026-08-30, a "draw" is a hand edit to
# gen-autogenesis-nursery-refill.py's FAMILY_MODULES/FAMILY_ROUTES, so
# re-running the generator adds nothing and nothing computed whether the pinned
# pool still HAS families to draw from. R3 makes the exit status depend on that.
# Host-independent: it reads a tracked snapshot whose freshness is re-derived
# from every screen input, because the 39 MB pool lives on /nas3.
step propose-nursery-refill-tests bash scripts/tests/test-propose-nursery-refill.sh
step propose-nursery-refill python3 scripts/propose-nursery-refill.py
# A name match against the kernel environment for an OPEN mirror -- necessary,
# not sufficient, for "already proved". Written 2026-08-29 by the lane that
# refused a draw, then archived by the orphan sweep because nothing invoked it.
# It is the 'good check nobody wired up' case, so it is wired up now.
step autogenesis-already-proved python3 ./scripts/check-autogenesis-already-proved.py
# ...and the POSITIVE screen, re-run over the preregistered refill on every
# invocation rather than only at the moment it was written. `screened-ok`
# against the divergence registry is necessary and NOT sufficient: it says
# nothing about whether a proposition can be stated over declarations this
# kernel actually has.
step dispatchable-frontier-statable python3 scripts/check-dispatchable-frontier.py \
    --statable artifacts/autogenesis/nursery-v2-extension.json
step autogenesis-holdout-contamination-tests python3 -m unittest scripts.tests.test_check_autogenesis_holdout_contamination
step autogenesis-holdout-contamination python3 scripts/check-autogenesis-holdout-contamination.py
step artifact-gate-provenance-tests python3 -m unittest scripts.tests.test_artifact_gate_provenance
step artifact-gate-provenance python3 scripts/check-artifact-gate-provenance.py
step development-partition-tests python3 -m unittest scripts.tests.test_development_partition
step development-partition python3 scripts/check-development-partition.py
step autogenesis-must-decline-population-tests python3 -m unittest scripts.tests.test_check_autogenesis_must_decline_population
# The must-decline population is 9 of the nursery's 12 generated-mutation rows
# (train/development; the other 3 are held-out and are never referenced here).
# Every one is FALSE by a concrete counterexample this gate independently
# recomputes -- see artifacts/autogenesis/must-decline-mutations-v1.json. If a
# producer census ever admits one, this VOIDS the census: admitting a false
# statement is a soundness failure, not a low conversion rate. Companion to
# `explain_corpus IS NOT AN ORACLE` and the checker-that-cannot-fail discipline
# in CLAUDE.md, applied one arrow upstream to the PRODUCER for the first time.
step autogenesis-must-decline-population python3 scripts/check-autogenesis-must-decline-population.py
step autogenesis-bounded-induction-family python3 scripts/check-autogenesis-bounded-induction-family.py
step autogenesis-modeq-family python3 scripts/check-autogenesis-modeq-family.py
step autogenesis-nat-modeq-family python3 scripts/check-autogenesis-nat-modeq-family.py
step autogenesis-nat-modeq-imported-bridge-assay python3 scripts/check-autogenesis-nat-modeq-imported-bridge-assay.py
step autogenesis-nat-modeq-remainder-contract python3 scripts/check-autogenesis-nat-modeq-remainder-contract.py
step autogenesis-nat-modeq-remainder-contract-v2 python3 scripts/check-autogenesis-nat-modeq-remainder-contract-v2.py
step autogenesis-nat-modeq-remainder-operation python3 scripts/check-autogenesis-nat-modeq-remainder-operation.py
step established-fact-bounded-truth python3 scripts/check-established-facts-bounded-truth.py
step lane-turn-controls ./scripts/tests/test-check-lane-turn.sh
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
step autogenesis-int-fib-neg-natcast-dependency-audit-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_neg_natcast_dependency_audit_result
step autogenesis-int-fib-of-odd-private-root-audit-plan-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_of_odd_private_root_audit_plan
step autogenesis-int-fib-of-odd-private-root-audit-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_of_odd_private_root_audit_result
step autogenesis-nat-fib-gcd-surface-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_surface_result
step autogenesis-nat-gcd-greatest-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_nat_gcd_greatest_result
step autogenesis-semantic-abstraction-census-tests python3 -m unittest scripts.tests.test_check_autogenesis_semantic_abstraction_census
step autogenesis-semantic-abstraction-census python3 scripts/check-autogenesis-semantic-abstraction-census.py
step autogenesis-semantic-function-contract-rust cargo test -p axeyum-lean-import --test semantic_function_contract
step autogenesis-semantic-contract-target-census-rust cargo test -p axeyum-lean-import --example semantic_contract_target_census
step autogenesis-semantic-contract-target-census-tests python3 -m unittest scripts.tests.test_check_autogenesis_semantic_contract_target_census
step autogenesis-semantic-contract-target-census python3 scripts/check-autogenesis-semantic-contract-target-census.py
step autogenesis-int-gcd-contract-residualization-rust-test cargo test -p axeyum-lean-import --test contract_residualization
step autogenesis-int-gcd-contract-residualization-rust-example cargo test -p axeyum-lean-import --example int_gcd_contract_residualization
step autogenesis-int-gcd-contract-residualization-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_residualization
step autogenesis-int-gcd-contract-residualization python3 scripts/check-autogenesis-int-gcd-contract-residualization.py
step autogenesis-int-gcd-source-delta-rust-test cargo test -p axeyum-lean-import --test source_delta_trace
step autogenesis-int-gcd-source-delta-rust-example cargo test -p axeyum-lean-import --example int_gcd_source_delta_trace
step autogenesis-int-gcd-source-delta-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_source_delta
step autogenesis-int-gcd-source-delta python3 scripts/check-autogenesis-int-gcd-source-delta.py
step autogenesis-int-gcd-trace-contract-receipt-rust-test cargo test -p axeyum-lean-import --test trace_contract_receipt
step autogenesis-int-gcd-trace-contract-receipt-rust-example cargo test -p axeyum-lean-import --example int_gcd_trace_contract_receipt
step autogenesis-int-gcd-trace-contract-receipt-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_trace_contract_receipt
step autogenesis-int-gcd-trace-contract-receipt python3 scripts/check-autogenesis-int-gcd-trace-contract-receipt.py
step autogenesis-int-gcd-contract-theorem-control-policy-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control_policy
step autogenesis-int-gcd-contract-theorem-control-policy python3 scripts/check-autogenesis-int-gcd-contract-theorem-control-policy.py
step autogenesis-int-gcd-contract-theorem-control-rust-test cargo test -p axeyum-lean-import --test trace_contract_theorem_receipt
step autogenesis-int-gcd-contract-theorem-control-rust-example cargo test -p axeyum-lean-import --example int_gcd_contract_theorem_control
step autogenesis-int-gcd-contract-theorem-control-tests python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control
step autogenesis-int-gcd-contract-theorem-control python3 scripts/check-autogenesis-int-gcd-contract-theorem-control.py
step autogenesis-nat-fib-gcd-premise-selection-policy-tests python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_premise_selection_policy
step autogenesis-nat-fib-gcd-premise-selection-policy python3 scripts/check-autogenesis-nat-fib-gcd-premise-selection-policy.py
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
# Two live control modules landed without a runner. Register them before the
# reachability ratchet so a regression in either boundary can fail this gate.
step statement-adapter-generator-controls python3 -m unittest scripts.tests.test_gen_statement_adapters
step external-certificate-controls python3 -m unittest scripts.tests.test_check_external_certificate
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
step mutation-anchors-are-fresh python3 scripts/tests/mutation_controls.py --check-anchors
step example-inventory-count python3 scripts/gen-example-inventory.py --check
step example-inventory-controls ./scripts/tests/test-gen-example-inventory.sh
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
# `bench-results/PARITY.md` is this repository's declared headline, and
# `scripts/parity-run.sh` -- the only thing that writes it -- was invoked by NO
# gate: not this script, not `just check`, not CI (measured 2026-08-21). The
# board consequently froze on 2026-08-06 through the steepest improvement in the
# project's history and nothing went red. This is the gate that reds.
step parity-freshness ./scripts/check-parity-freshness.py
step parity-freshness-controls ./scripts/tests/test-check-parity-freshness.sh
step new-fact-controls ./scripts/tests/test-new-fact-controls.sh
step lane-commit-controls ./scripts/tests/test-lane-commit.sh
# The gate-ADMISSION mechanism (2026-08-27): lane cargo work is niced so the
# push battery stops being starved by it, and this script takes a cargo slot.
# Scheduling changes are an easy place to write a check that cannot fail --
# "it went faster" is not an exit status -- so every assertion here is paired
# with the input that makes it fail, and each guard is mutation-verified by
# `scripts/tests/mutate-gate-admission.sh` to be killed by exactly its own case.
step gate-admission-controls ./scripts/tests/test-gate-admission-controls.sh
# ...and the mutation harness over those controls. It runs in the gate rather
# than by hand because a guard that stops discriminating does so silently: the
# suite above stays green either way. Safe here only because it mutates a
# four-file SCRATCH COPY -- these are shell scripts read fresh on every
# invocation, so an in-place mutant would be executed by any lane running a
# gate during the window.
step gate-admission-mutation ./scripts/tests/mutate-gate-admission.sh
step recount-pinned-inventory-controls ./scripts/tests/test-recount-pinned-inventory.sh
step commit-msg-trailer-controls ./scripts/tests/test-commit-msg-trailer.sh
step lane-merge-additive-controls python3 -m unittest scripts.tests.test_lane_merge_additive
step lane-push-controls ./scripts/tests/test-lane-push-target.sh
# The open-frontier axiom-freeness census bounds ONE route (reuse of a Mathlib
# proof term). Its guards are mutation-verified to kill exactly one case each,
# and its coverage guard derives the population from the LEDGER, so the census
# reds this gate when the frontier grows rather than going quietly stale.
step open-frontier-axiom-freeness-controls ./scripts/tests/test-open-frontier-axiom-freeness.sh
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
# A `#[test]` attribute separated from its function, or duplicated onto one.
# Measured 2026-08-29: a `lane-merge-additive.py splice` anchored on an item's
# `fn` line inserted the spliced items BETWEEN a `#[test]` and its function, so
# one test silently never ran -- while `cargo test` reported a healthy nonzero
# count throughout. The count is the check this repo leans on hardest and it
# CANNOT see this. FOUR separate lanes repaired the damage before it was gated.
step test-attribute-integrity python3 ./scripts/check-test-attribute-integrity.py
# ...and its controls, each mutation-verified to be killed by exactly one case,
# including a false-positive control (a multi-line `#[allow]` between the
# attribute and the fn), which the gate's own first draft failed.
step test-attribute-integrity-controls ./scripts/tests/test-check-test-attribute-integrity.sh
# The creal prelude-build ratio gate's controls. Written earlier in the same
# session as the gate and never registered -- caught by check-control-
# registration.sh, which is exactly the failure that script exists for.
step creal-prelude-build-ratio-controls ./scripts/tests/test-creal-prelude-build-ratio.sh
# Controls for THIS gate's own step normalizer. Its `./` strip was anchored at
# line start, so `python3 ./scripts/x.py` (check.sh's form) and `python3
# scripts/x.py` (the justfile's) normalized differently and one script was
# reported as two divergences -- 4 of 13 on 2026-08-30, burying the one real
# check.sh-only step. A gate that manufactures divergences is a gate nobody
# can act on, which is how this one came to sit red.
step aggregate-scope-controls ./scripts/tests/test-check-aggregate-scope.sh
# The registration gate's OWN controls. It had none until 2026-08-27 -- the gate
# whose subject is "a check nobody invokes cannot fail" was itself unverified,
# and its python half then pinned an unexplained floor of 188 unnamed suites.
# 15 cases, each mutation-verified to die when its guard is deleted.
step control-registration-controls ./scripts/tests/test-check-control-registration.sh
# `scripts/check-fast.sh` -- tier-0 of THIS gate, and its controls. Measured
# 2026-08-29: this script declares 379 steps; a 1-in-5 sample of its 355
# non-cargo steps took 549 s with 15 of 71 steps accounting for 528 s of it, so
# the aggregate is over an hour and the fast ~80% of it costs ~4% of the time.
# Neither `hooks/pre-push` nor `.github/workflows/ci.yml` names this script or
# `just check`, so its only caller is a human -- which is why
# `check-local-ci-freshness` above sat RED for 265 h. The tier-0 runner exists
# so something runnable in ~2 min can be run unconditionally. Its five guards
# are each mutation-verified to kill exactly one control, plus a
# false-positive control that survives all five; the load-bearing one is that
# DEFERRED is a third outcome and never folds into `ok`.
step check-fast-controls ./scripts/tests/test-check-fast.sh
# `scripts/brief-step0.py` -- the dispatcher-side retrieval step, and its
# controls. Measured 2026-08-29 over 272 lane status documents: mutation
# testing (harness + gate) is followed 46% of the time, `shape_search` (prose
# only) 4.8%. Compliance tracks MECHANIZATION, not emphasis, so the "does it
# already exist" step moved out of the lane and into the brief. Nine guards,
# each mutation-verified in a scratch copy to kill exactly one control, plus a
# false-positive control that survives all nine. The load-bearing ones: a
# snapshot that cannot retrieve the built-in probe is UNANSWERABLE rather than
# a source of ABSENT verdicts, and a snapshot from another kernel tree exits 4
# instead of reading as current.
step brief-step0-controls ./scripts/tests/test-brief-step0.sh
# ...and the catch-all that makes registration DERIVED rather than remembered.
# Measured 2026-08-27: 188 of 382 python control suites -- 49% -- were named by
# no caller at all, pinned as a numeric floor nobody had chosen. This runs every
# `scripts/tests/test_*.py` that no step above names, minus the reasoned
# exclusions in `scripts/control-optout.tsv`. 169 suites, 1193 tests, ~39s at 8
# jobs. It fails on a suite that FAILS and on a suite that runs ZERO tests --
# ten of those 188 were pytest-dialect files that `unittest` collects as nothing.
step python-controls ./scripts/run-python-controls.py
# Ban the shell idioms that print a WRONG ANSWER while exiting 0. Both pinned
# patterns were real defects on 2026-08-20: `grep -q` piped under pipefail
# made the SAME tree report 7 orphans then 3, and `$?` after a pipeline
# reported exit=0 for a script that exits 1.
step shell-antipatterns ./scripts/check-shell-antipatterns.sh
# ...and its controls. The gate had none and was RED on a FALSE POSITIVE: its
# pattern matched the second bar of a logical `||` as though it were a pipe, so
# `a || grep -q x file` -- reading a FILE, incapable of SIGPIPE -- was reported
# as the banned idiom. 12 cases, 4 real pipelines that must stay caught and 6
# shapes that must not be flagged.
step shell-antipatterns-controls ./scripts/tests/test-check-shell-antipatterns.sh
# `bench-results/DOMINANCE.md` is generated and had NO `--check` and no gate,
# so it sat SIX AUDITS behind its own inputs -- its QF_S row claimed 87
# decided against an artifact recording 93 -- while reading as current.
step dominance-scoreboard-tests python3 -m unittest scripts.tests.test_gen_dominance_scoreboard
step dominance-scoreboard python3 scripts/gen-dominance-scoreboard.py --check
# The dominance audit's OWN unit tests. `cargo test -p axeyum-bench --example
# audit_dominance` appeared in no script, so the harness that produces every
# committed dominance number carried a test that had been FAILING since
# ADR-0384 made `Evidence::check` three-valued -- invisibly, for as long as
# nobody typed the command. Expect a NONZERO count (10).
step dominance-audit-harness-tests cargo test -p axeyum-bench --example audit_dominance
# `explain_corpus`'s own unit tests, likewise in no script until now. They pin
# the 2026-08-21 divergence census: the tool disagrees with `solve_smtlib` on
# 134 of 397 committed benchmarks, so no verdict it prints may be a bare
# SMT-LIB token and the two structurally divergent shapes are refused. Expect a
# NONZERO count (21).
step explain-corpus-diagnostic-tests cargo test -p axeyum-bench --example explain_corpus
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
# ADR-0553. No artifact may declare a dependency on a repository this project
# does not own. `--self-test` runs first on purpose: it drives every rule over a
# synthetic violation and fails if any rule does NOT fire, so the zero the scan
# prints afterwards is a measurement rather than a no-op.
step external-coupling-tests python3 -m unittest scripts.tests.test_check_external_coupling
step external-coupling-selftest python3 scripts/check-external-coupling.py --self-test
step external-coupling python3 scripts/check-external-coupling.py
step autogenesis-knowledge-overlay-tests python3 -m unittest scripts.tests.test_validate_autogenesis_knowledge
step autogenesis-knowledge-coverage-tests python3 -m unittest scripts.tests.test_gen_autogenesis_knowledge_coverage
step autogenesis-knowledge-overlay python3 scripts/validate-autogenesis-knowledge.py
step autogenesis-knowledge-controls ./scripts/check-autogenesis-knowledge-controls.sh
step autogenesis-kernel-projection python3 -m unittest scripts.tests.test_validate_autogenesis_kernel_projection
step autogenesis-kernel-projection-content python3 scripts/validate-autogenesis-kernel-dependency-projection.py
step autogenesis-kernel-projection-fresh python3 scripts/gen-autogenesis-kernel-dependency-projection.py --check
step autogenesis-kernel-lemma-index-tests python3 -m unittest scripts.tests.test_gen_autogenesis_kernel_lemma_search_index
step autogenesis-kernel-lemma-index-fresh python3 scripts/gen-autogenesis-kernel-lemma-search-index.py --check
step autogenesis-obstruction-projection python3 -m unittest scripts.tests.test_validate_autogenesis_obstruction_projection
step autogenesis-obstruction-projection-content python3 scripts/validate-autogenesis-obstruction-projection.py
step autogenesis-obstruction-projection-fresh python3 scripts/gen-autogenesis-obstruction-projection.py --check
step autogenesis-transport-projection python3 -m unittest scripts.tests.test_validate_autogenesis_transport_projection
step autogenesis-transport-projection-content python3 scripts/validate-autogenesis-transport-projection.py
step autogenesis-transport-projection-fresh python3 scripts/gen-autogenesis-transport-projection.py --check
step autogenesis-capability-gap python3 -m unittest scripts.tests.test_validate_autogenesis_capability_gap_projection
step autogenesis-capability-gap-content python3 scripts/validate-autogenesis-capability-gap-projection.py
step autogenesis-capability-demand-tests python3 -m unittest scripts.tests.test_validate_autogenesis_capability_candidate_demand
step autogenesis-capability-demand-content python3 scripts/validate-autogenesis-capability-candidate-demand.py
step autogenesis-capability-gap-fresh python3 scripts/gen-autogenesis-capability-gap-projection.py --check
step autogenesis-concept-coverage python3 -m unittest scripts.tests.test_validate_autogenesis_concept_coverage_projection
step autogenesis-concept-coverage-content python3 scripts/validate-autogenesis-concept-coverage-projection.py
step autogenesis-concept-coverage-fresh python3 scripts/gen-autogenesis-concept-coverage-projection.py --check
step autogenesis-producer-outcomes python3 -m unittest scripts.tests.test_validate_autogenesis_producer_outcome_observations
step autogenesis-producer-outcomes-content python3 scripts/validate-autogenesis-producer-outcome-observations.py
step autogenesis-producer-outcomes-fresh python3 scripts/gen-autogenesis-producer-outcome-observations.py --check
step autogenesis-producer-evaluation-frontier python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_frontier
step autogenesis-producer-evaluation-frontier-content python3 scripts/validate-autogenesis-producer-evaluation-frontier.py
step autogenesis-producer-evaluation-frontier-fresh python3 scripts/gen-autogenesis-producer-evaluation-frontier.py --check
step autogenesis-producer-evaluation-protocol python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_protocol
step autogenesis-producer-evaluation-protocol-content python3 scripts/validate-autogenesis-producer-evaluation-protocol.py
step autogenesis-producer-evaluation-protocol-fresh python3 scripts/gen-autogenesis-producer-evaluation-protocol.py --check
step autogenesis-producer-evaluation-result-contract python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_result
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
step theorem-production-ledger-tests python3 -m unittest scripts.tests.test_gen_theorem_production_ledger
step theorem-production-ledger python3 scripts/gen-theorem-production-ledger.py --check
# Three doc claims of the shape "`X` is not proved/built here" were FALSE
# against the actual construction on 2026-08-22/23 -- `declare_X` sat later in
# the same file (or, in `int_prelude/gcd.rs`, the same module) and was wired
# into the build sequence. One shipped in three separate agent briefs before
# anyone read the code it contradicted. This catches the crispest, most
# literal sub-shape (a bare-name list immediately followed by a present-tense
# negation) with a same-Rust-module `declare_<name>` scope; see the script's
# own docstring for what it deliberately does not catch.
step stale-negative-claims-tests python3 -m unittest scripts.tests.test_check_stale_negative_claims
step stale-negative-claims python3 scripts/check-stale-negative-claims.py
step production-provenance-ledger-tests python3 -m unittest scripts.tests.test_gen_production_provenance_ledger
step production-provenance-ledger python3 scripts/gen-production-provenance-ledger.py --check
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
step autogenesis-producer-contracts python3 scripts/validate-producer-contracts.py
step autogenesis-producer-contracts-tests python3 -m unittest scripts.tests.test_validate_producer_contracts
step autogenesis-producer-contract-declines python3 scripts/validate-producer-contract-declines.py
step autogenesis-producer-contract-declines-tests python3 -m unittest scripts.tests.test_validate_producer_contract_declines
step autogenesis-authoritative-comparison-tests python3 -m unittest scripts.tests.test_compare_autogenesis_authoritative_chains
step autogenesis-result python3 scripts/check-autogenesis-1-result.py
step autogenesis-result-tests python3 -m unittest scripts.tests.test_check_autogenesis_1_result
step autogenesis-authoritative-fact-tests python3 -m unittest scripts.tests.test_run_autogenesis_authoritative_fact
step autogenesis-binomial-arrow-tests uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_binomial_arrow_capability
step autogenesis-binomial-arrow-capability uv run --no-sync python scripts/gen-autogenesis-binomial-arrow-capability.py --check
step autogenesis-binomial-connective-ranking uv run --no-sync python scripts/gen-autogenesis-binomial-connective-ranking.py --check
step autogenesis-binomial-arrow-measurement uv run --no-sync python scripts/check-autogenesis-binomial-arrow-measurement.py
step autogenesis-next-reusable-family-tests python3 -m unittest scripts.tests.test_gen_autogenesis_next_reusable_family_queue
step autogenesis-next-reusable-family python3 scripts/gen-autogenesis-next-reusable-family-queue.py --check
step fact-frontier-tests python3 -m unittest scripts.tests.test_fact_frontier
step autogenesis-operation-execution-tests python3 -m unittest scripts.tests.test_execute_autogenesis_operation
step autogenesis-fact-operation-tests python3 -m unittest scripts.tests.test_check_autogenesis_fact_operation
step autogenesis-baseline python3 scripts/gen-autogenesis-baseline.py --check
step gen-plan-tests python3 -m unittest scripts.tests.test_gen_plan
step gen-plan       python3 scripts/gen-plan.py --check
step adr-index-tests python3 -m unittest scripts.tests.test_gen_adr_index
step adr-index      python3 scripts/gen-adr-index.py --check
# ADR-0601 SS3: the import backlog (external-proved, epistemically-open facts)
# as a produced, deterministic artifact rather than a bare count in
# validate-facts.py's summary. docs/autogenesis/289-import-backlog-artifact.md.
step import-backlog-tests python3 -m unittest scripts.tests.test_gen_import_backlog
step import-backlog python3 scripts/gen-import-backlog.py --check
# docs/plan/status/141-ledger-6-backlog.md's own closing paragraph: nobody
# had ever measured the full diff of prelude_theorem_inventory's theorem
# list against artifacts/facts/'s registered names -- six ledger batches each
# hand-picked a short list instead. This is that measurement, permanent
# rather than one-off: fails when a kernel theorem lands unregistered and
# the artifact is not regenerated to match. docs/autogenesis/297-ledger-coverage-gate.md.
step ledger-coverage-tests python3 -m unittest scripts.tests.test_gen_ledger_coverage
step ledger-coverage python3 scripts/gen-ledger-coverage.py --check
# The generated half of that ledger. `gen-kernel-facts.py` writes facts
# mechanically for already-proved kernel theorems, and bulk generation is
# exactly how the "checker that cannot fail" defect gets manufactured at
# speed. `--audit` re-derives the prose every `provenance.curation:
# generated-unreviewed` fact would carry and requires a byte-identical match
# (so enriched prose must flip the marker to `curated` rather than sit under
# the generated one), requires `external_status` to be absent, and requires
# every checker_command to match a shape whose exit status depends on the
# finding. docs/autogenesis/298-mechanical-fact-registration.md.
step kernel-facts-tests python3 -m unittest scripts.tests.test_gen_kernel_facts
step kernel-facts-audit python3 scripts/gen-kernel-facts.py --audit
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
# Post-merge hygiene, ~2s: conflict markers in tracked files, duplicate ADR
# numbers, and stale generated files. Each corresponds to a defect that reached
# a commit here because the coordinator merges lane branches far more often than
# it runs this gate -- markers committed into ten fact JSONs and later into the
# ADR index, and 0617/0618 each allocated by two concurrent lanes on one day.
step merge-hygiene ./scripts/check-merge-hygiene.sh
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

# The Python binding gate (docs/python-2026-08/01-pyo3-maturin.md, S5), which
# `just py-check` runs as one recipe. Conditional on `uv`, and on the venv it
# manages, because this script's whole purpose is to run on a fresh host with
# nothing installed -- but a missing toolchain is SKIPPED, never passed: an
# absent gate that prints nothing is indistinguishable from a gate that ran.
#
# Every count-bearing step prints one (`PYTEST|collected=N`, `STUBS|compared=M`,
# `TYPES|...|control=N`) and fails on zero, because a Python gate is the easiest
# place here to build something that exits 0 while examining nothing. The type
# step checks a deliberately ill-typed file through the same path on every run
# and fails when THAT produces no diagnostic -- a type checker aimed at the
# wrong directory is silent, not red.
#
# TMPDIR off /tmp: `maturin develop` writes a wheel there per rebuild and /tmp
# on this fleet is a 62 G RAM tmpfs already implicated in OOM kills.
# LIST MODE IGNORES HOST STATE, DELIBERATELY. `AXEYUM_CHECK_LIST=1` answers
# "what does this gate examine?", not "what would it examine on this host right
# now" -- and `scripts/check-aggregate-scope.sh` compares that listing against
# the justfile's. Measured 2026-08-30: `.venv` was absent from this checkout, so
# the enumeration dropped all eight Python steps and the scope gate reported
# them as `just-only` divergences. They are not divergences; `just py-check` and
# this block run the same eight commands. Gating the LISTING on host state made
# the comparison non-reproducible -- a different developer would get a different
# divergence set from an identical tree.
if [ "$list_only" = "1" ] || { command -v uv >/dev/null 2>&1 && [ -d .venv ]; }; then
  step_prefix="optional:"
  export TMPDIR="${TMPDIR:-/data0/axeyum/scratch/py-tmp-$USER}"
  [ "$list_only" = "1" ] || mkdir -p "$TMPDIR"
  step py-maturin-develop uv run --no-sync maturin develop
  step py-pytest          uv run --no-sync pytest python/tests -q
  step py-stubs           uv run --no-sync python tools/gen_native_stub.py --check
  # The typed-stub pair. `py-stubs` above compares NAMES and ARITY against the
  # built extension and ignores annotations; these two are the type half.
  #   py-stub-types  every `typing.Any` in the generated stubs is on a committed
  #                  allowlist with a reason, and no entry names a site that has
  #                  stopped being `Any` -- a ratchet that can only go down.
  #   py-stubtest    mypy's `stubtest` imports the `.so` and the stubs and
  #                  compares them AS TYPES. It is the only checker here that can
  #                  see a stub claiming `-> int` for something returning `str`:
  #                  `ty` reads the stubs and believes them.
  step py-stub-types      uv run --no-sync python tools/check_stub_types.py
  step py-stubtest        uv run --no-sync python -m mypy.stubtest axeyum._native --ignore-missing-stub --ignore-positional-only --mypy-config-file tools/stubtest-mypy.ini --allowlist tools/stubtest-allowlist.txt --concise
  step py-types           uv run --no-sync python tools/check_types.py
  step py-ruff-check      uv run --no-sync ruff check python/ tools/
  step py-ruff-format     uv run --no-sync ruff format --check python/ tools/
step_prefix=""
elif [ "$list_only" != "1" ]; then
  # SKIPPED, not passed. Named on stdout so a reader of the log can see which
  # half of the gate did not run, and why.
  if command -v uv >/dev/null 2>&1; then
    echo "py-check: SKIPPED (no .venv -- run \`uv sync --dev\`)"
  else
    echo "py-check: SKIPPED (no uv)"
  fi
fi

# The Python coverage ledger (docs/python-2026-08/09-coverage-plan.md). Two
# steps, both printing a COUNT-bearing line, unit suite first.
#
# `gen-python-coverage.py` is what evaluates plan 02's exit criterion -- "every
# tier-R inventory row bound or a recorded deferral" -- which until 2026-08-24
# nothing could evaluate at all. It scans every crate's public surface, joins it
# to what `crates/axeyum-py` references (comments stripped: a doc comment naming
# a function is not a call) and to the three hand-written inventories, and
# prints `PYTHON_COVERAGE|crates=N|public=P|referenced=R|inventoried=I|
# tier_r_unreferenced=U|deferred=D`.
#
# Three ways it goes red, and only one of them is "the artifact is stale":
#   * `--check` staleness -- regenerate with `python3 scripts/gen-python-coverage.py`;
#   * exit 2, a deferral in `artifacts/python-coverage-deferrals.json` with no
#     reason (an unexplained deferral and a forgotten row are the same thing);
#   * exit 1, `U > 0` while some document CLAIMS the criterion is met. `U > 0`
#     alone is the normal state of an unfinished plan and passes.
step python-coverage-tests python3 -m unittest scripts.tests.test_gen_python_coverage
step python-coverage python3 scripts/gen-python-coverage.py --check

# The tactic catalog (docs/python-2026-08/04-tactic-catalog.md, slice A3): the
# strategy vocabulary the agent's Plan node resolves against. Two steps, both
# printing a COUNT. The validator re-derives every claim the catalog makes about
# the code (implementing file, symbol, DeclineReason variants, `const` budget
# values) and then fails on the CENSUS -- fewer than two distinct precondition
# shapes, or any tactic with zero measured reach rows -- which is the doc-228
# "an operation registry where every entry names one target is a dispatch table"
# finding moved one arrow upstream. Read `TACTIC_CATALOG|...`, not the status.
step tactic-catalog-tests python3 -m unittest scripts.tests.test_validate_tactic_catalog
step tactic-catalog python3 scripts/validate-tactic-catalog.py
step tactic-catalog-census python3 scripts/gen-tactic-catalog-census.py --check

# The agent-episode gate (docs/python-2026-08/03-agentic-layer.md, slice A1).
# `just episodes` runs the same two steps.
#
# An episode records one run of the agentic frontier loop, and it is the only
# thing between "a model ran" and "a model proved something". The checker
# re-derives what the document claims -- schema, snapshot and proposal digests
# re-hashed from disk, a generic string walk for held-out fact ids, and
# `ledger_writes` pinned to 0 -- and its exit status is nonzero when ZERO
# episodes were checked, because a check that checked nothing is not a pass.
# Read `EPISODES|checked=N|ok=K|failed=M`.
#
# Deliberately WITHOUT `--require-ancestor`: most CI jobs check out at the
# default `fetch-depth: 1`, where the episode's commit object is absent and
# every ancestor query answers "cannot resolve". The rule is tested in the
# unittest suite instead. See artifacts/episodes/README.md.
step episodes       python3 scripts/check-agent-episode.py artifacts/episodes --production-only
step episode-tests  python3 -m unittest scripts.tests.test_check_agent_episode

# Generated product populations, static aggregate-gate reachability, and the
# latest commit-bound provider receipt. Ancestor results remain non-transitive.
step ci-receipt            python3 scripts/check-ci-receipt.py
step product-health-tests python3 -m unittest scripts.tests.test_gen_product_health
step product-health       python3 scripts/gen-product-health.py --check

# The mobility census gate (docs/python-2026-08/07-mobility-census.md, slice A7).
# `just mobility-census` runs the same two steps.
#
# The census says which tactic preconditions reach which open facts, and its
# zero-match clusters are read as the capability backlog -- so it is exactly the
# artifact CLAUDE.md warns about, where the ledger IS the product. This step
# VALIDATES the committed file and never regenerates it: regenerating in a gate
# would make the gate agree with itself by construction, and the census needs a
# real kernel (it imports frozen Lean exports), which `scripts/` may not.
#
# The rule that carries the most weight is `evaluable > 0`: 187 of 191 open
# facts have no frozen statement export, and a boolean census would have
# reported all of them as zero-match. Read
# `MOBILITY_CENSUS|open=N|evaluable=E|...|violations=V`, not the status alone.
step mobility-census python3 scripts/check-mobility-census.py
step mobility-census-tests python3 -m unittest scripts.tests.test_check_mobility_census

# The obstruction graph (docs/python-2026-08/06-obstruction-graph.md, slice A5;
# Autogenesis F3). `just obstruction-graph` runs the same four steps.
#
# The graph is DERIVED from the committed episodes and decline records, so the
# first step is the one that can go red on a healthy-looking tree: `--check`
# fails when the committed artifact is not a regeneration, which is how a
# hand-edited cluster is caught. The generator also exits 1 when no obstruction
# was derived, when a decline record's shape matches no predicate, and when any
# held-out fact id reaches a population or the rendered bytes. Read
# `OBSTRUCTIONS|...` and `OBSTRUCTION_GRAPH_OK|...`, not the status alone.
step obstruction-graph        python3 scripts/gen-obstruction-graph.py --check
step obstruction-graph-valid  python3 scripts/validate-obstruction-graph.py
step obstruction-dashboard    python3 scripts/gen-obstruction-dashboard.py --check
step obstruction-graph-tests  python3 -m unittest scripts.tests.test_obstruction_graph

# Theorem correspondences (ADR-0546). `just correspondences` runs the same two
# steps.
#
# The claim being gated is "these two facts are the same idea", which is not a
# proof dependency and must not become one: the validator refuses any pair the
# fact ledger already connects through the TRANSITIVE `depends_on` closure, in
# either direction. It also refuses an empty population -- the whole file is a
# vocabulary, and a vocabulary with no instance cannot fail.
#
# The rule doing the most work is the structural one. `carrier-transport` is not
# taken on trust: erasing the carrier from both formal statements must leave the
# same string, and a fragment with no carrier spelling FAILS rather than skipping
# the check. Read `CORRESPONDENCES|checked=N|kinds=...|derivation=...`, not the
# status alone -- the per-kind counts include the ZEROES, so a vocabulary term
# nobody instantiated is visible instead of merely declared. Every guard is
# mutation-verified to kill exactly one test -- `python3
# scripts/tests/mutation_controls.py correspondences` (39 anchors, 39 killed).
step correspondences       python3 scripts/validate-correspondences.py
step correspondences-tests python3 -m unittest scripts.tests.test_validate_correspondences

# Mocked-subprocess unit controls for the Tock log2 capture/cache-prepare
# investigation tooling (bench-results/verify-tock-log2-20260721/). These only
# guard the committed scripts' own logic via subprocess mocks; the
# `prove-tock-log2*` generations are excluded because their frozen
# registration pins a SHA-256 of `crates/axeyum-verify/tests/tock_log2_external.rs`
# that has drifted since the freeze, so all four currently fail closed.
step tock-log2-capture-tests    python3 -m unittest scripts.tests.test_capture_tock_log2
step tock-log2-capture-v2-tests python3 -m unittest scripts.tests.test_capture_tock_log2_v2
step tock-log2-capture-v3-tests python3 -m unittest scripts.tests.test_capture_tock_log2_v3
step tock-log2-cache-v2-tests   python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v2
step tock-log2-cache-v3-tests   python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v3
step tock-log2-cache-v4-tests   python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v4
step tock-log2-cache-v5-tests   python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v5

# The 2026-08-29 orphan-script audit (docs/plan/status/308-orphan-script-audit.md)
# found these three well-formed, general-purpose checks with NO caller anywhere
# -- not this file, not the justfile, not a hook, not a fact. Each is exactly
# the "genuinely useful but never wired up" case CLAUDE.md warns is a gate
# waiting to be registered, not a deletion candidate, and each ran clean when
# tested standing them up here.
step shared-index      ./scripts/check-shared-index.sh
step sos-negative-controls ./scripts/check-sos-negative-controls.sh
step evidence-portability  ./scripts/check-evidence-portability.sh

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
echo "check: ran $ran steps (floor $STEP_FLOOR), ${#failed_steps[@]} failed," \
     "${#timed_out_steps[@]} timed out"
if [ ${#timed_out_steps[@]} -gt 0 ]; then
  # As loud as `check-fast.sh`'s DEFERRED banner, and for the same reason: a
  # step that hit its cap was NOT checked, and a reader who skims the summary
  # must not be able to mistake it for one that passed.
  echo "check: TIMED OUT -- these steps are UNCHECKED (neither passed nor failed):" >&2
  printf '  %s\n' "${timed_out_steps[@]}" >&2
  echo "check: a timeout is not evidence the step is broken. Re-run the named" \
       "step alone on an idle box before believing it; if it is genuinely this" \
       "slow, raise its entry in step_cap_for and say what you measured." >&2
fi
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
  if [ ${#timed_out_steps[@]} -gt 0 ]; then
    printf 'check: TIMED-OUT (unchecked) steps: %s\n' "${timed_out_steps[*]}" >&2
  fi
  echo "check: one or more gates FAILED or went UNCHECKED" >&2
  exit 1
fi
echo "check: all $ran gates passed"
