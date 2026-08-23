# Canonical development commands. Run `just` to list.

default:
    @just --list

# Run every check CI runs (except cargo-deny, which needs the tool installed).
# This is the THOROUGH pre-merge/CI gate (whole workspace, ~tens of minutes).
# While iterating, use `just check-scope` instead — it gates only what changed.

# THE AXIOM-FREEDOM MEASUREMENTS, which nothing ran until 2026-08-18.
#
# `real: axiom=30` is this repository's whole remaining trusted surface, and the
# claim that the shipped front door no longer reaches it rests on three
# examples. Grepped across `scripts/*.sh`, `justfile` and `.github/workflows/`
# on 2026-08-18: ZERO invocations. ADR-0509 and ADR-0515 both cite them as
# evidence; they were lane-run commands that happened to have been run once.
#
# Each carries a `--require-*` flag that makes its EXIT STATUS depend on the
# finding, which is the only reason putting them in a gate means anything:
#
#   front_door_carrier --require-axiom-free   the shipped `prove_unsat_to_lean_module`
#                                             reconstructs over the CONSTRUCTED reals,
#                                             carrier axioms 0/0/0 against the `Real`
#                                             control's 12/17/8, and the module's
#                                             `axiom` lines equal the kernel footprint
#   ring_interface_pin --require-identical    the 30-binder interface telescope read off
#                                             the axiomatized package and off the
#                                             axiom-free integers is the SAME statements
#   ordered_ring_refutation --require-empty   the generalized theorem's footprint is
#                                             empty, with the non-generalized one printed
#                                             beside it as a non-vacuity control
#   ordered_ring_refutation --constructed-reals   the same fixtures over `CReal`
#
# `--release` deliberately: measured 282 + 118 + 69 + 40 = 509 s in release
# against multiples of that in debug, and these build the whole constructed
# N/Z/Q/setoid development.
axiom-freedom:
    cargo run --release -q -p axeyum-solver --features full --example front_door_carrier -- --require-axiom-free
    cargo run --release -q -p axeyum-solver --features full --example ring_interface_pin -- --require-identical
    cargo run --release -q -p axeyum-solver --features full --example ordered_ring_refutation -- --require-empty
    cargo run --release -q -p axeyum-solver --features full --example ordered_ring_refutation -- --constructed-reals
# ORDERING NOTE, 2026-08-19: `just` aborts the whole chain at the FIRST failing
# dependency, so a gate that is red for real stretches of time silently prevents
# every gate after it from running. Measured today: `aggregate-scope` was #18 of
# 41 and red — inherited from main, which shipped 32 steps recorded in neither
# `check.sh` nor the justfile — so `just check` died there and **23 gates never
# ran**, including `test`, `frontier`, `lean-gate` and `doc`. `./scripts/check.sh`
# does not abort (it accumulates `fail=1`), which made the no-`just` FALLBACK the
# more complete gate.
#
# So the three gates whose red state is expected and slow to clear go LAST:
# `aggregate-scope` (until main's 32 steps are recorded on both sides),
# `adr-remote-collisions` (red whenever another checkout has claimed a number),
# and `local-ci-freshness` (red when the battery record is >48 h old). This does
# not hide any of them — the chain still fails — it stops them hiding everything
# else. Note the earlier claim that `adr-remote-collisions` was already last was
# wrong: it was #40 of 41, so `local-ci-freshness` sat behind it.
check: fmt fmt-all facts facts-replay clippy gate-controls axiom-freedom autogenesis-knowledge-controls autogenesis-proposer-isolation autogenesis-induction-search autogenesis-apply-search autogenesis-result autogenesis-nursery autogenesis-mathlib-source autogenesis-mathlib-dependencies autogenesis-mathlib-review autogenesis-mathlib-facts test frontier gate-liveness golden-lean-pins kernel-suite-partition lean-gate prelude-reuse moment-proofs doc qfbv-profile reflection-semantics-gate benchmark-repetition-tests glaurung-qfbv-regular foundational-resources rules-as-code smtcomp-resume parity-docs generated-trackers solver-module-graph plan-authority links aggregate-scope adr-remote-collisions local-ci-freshness parity-freshness

fmt:
    cargo fmt --all --check

# `cargo fmt --all` walks `mod` declarations and rustfmt does not expand
# macros, so `axeyum-solver`'s tree behind `macro_rules! full_modules` --
# 156 modules, 221,445 lines, the whole trusted reconstruction layer -- was
# invisible to `fmt` above. This enumerates from the filesystem instead.
fmt-all:
    scripts/check-fmt-complete.sh

# The `fact` ledger: a mathematical statement as a first-class object, with its
# status, dependencies and evidence. Semantic rules, not just structure -- a
# `proved` fact with nothing checked, or an `open` one carrying evidence, fails.
# 24 of 25 generated views under docs/plan/generated/ (840 KB of analysis) were
# referenced from NO entry point — measured 2026-08-17. The tooling was never the
# problem; reaching it was.
#
# Where the flywheel stands, in one screen: ledger, queue, proof gap, Lean split.
flywheel:
    ./scripts/flywheel-status.sh

# `fact-frontier.py` existed for a while and was referenced by NOTHING — not
# CLAUDE.md, not PLAN.md, not this file. A queue nobody can reach is a record,
# not a queue, so it gets a one-word name. It also warns when a fact is named by
# a gate script: a queue that says "dispatch it" about a gate's negative control
# is telling you to break the gate.
#
# What to prove next: frontier, import backlog, what is blocked and on what.
next:
    python3 scripts/fact-frontier.py

# Everything the queue knows, including which open facts each entry would unblock.
next-unlocks:
    python3 scripts/fact-frontier.py --unlocks

# Stable scheduler input. This can honestly select nothing: fragment reachability
# does not become a typed fact-to-producer/checker operation by implication.
next-json:
    python3 scripts/fact-frontier.py --json

# Proof-derived B -> A replay candidates. This intersects ledger edges with the
# kernel dependency inventory; a kernel-route label alone is not derivation.
next-chains:
    python3 scripts/fact-frontier.py --chains

next-chains-json:
    python3 scripts/create-autogenesis-chain-catalog.py --json

autogenesis-operations:
    python3 scripts/validate-autogenesis-operations.py
    python3 -m unittest scripts.tests.test_validate_autogenesis_operations

# Validate and exactly regenerate the frozen leakage-safe population contract.
autogenesis-nursery:
    python3 -m unittest scripts.tests.test_check_autogenesis_nursery
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_split
    python3 -m unittest scripts.tests.test_create_autogenesis_nursery_dispatch_baseline
    python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
    python3 -m unittest scripts.tests.test_check_autogenesis_holdout_isolation
    python3 scripts/check-autogenesis-holdout-isolation.py
    python3 -m unittest scripts.tests.test_development_partition
    python3 scripts/check-development-partition.py
    python3 -m unittest scripts.tests.test_check_autogenesis_must_decline_population
    python3 scripts/check-autogenesis-must-decline-population.py
    python3 scripts/check-autogenesis-bounded-induction-family.py
    python3 scripts/check-autogenesis-modeq-family.py
    python3 scripts/check-established-facts-bounded-truth.py
    python3 scripts/check-autogenesis-nursery.py
    python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
    cargo test -p axeyum-lean-import --test statement_adapter
    python3 -m unittest scripts.tests.test_check_autogenesis_statement_adapter
    python3 scripts/check-autogenesis-statement-adapter.py
    cargo test -p axeyum-lean-import --test statement_reflexivity_operation
    python3 -m unittest scripts.tests.test_check_autogenesis_statement_reflexivity
    python3 scripts/check-autogenesis-statement-reflexivity.py
    python3 -m unittest scripts.tests.test_check_autogenesis_statement_reflexivity_admission
    python3 scripts/check-autogenesis-statement-reflexivity-admission.py
    python3 scripts/check-autogenesis-statement-reflexivity-admission.py --manifest artifacts/autogenesis/mathlib-factorial-zero-admission-v1.json
    cargo test -p axeyum-lean-import --example statement_reflexivity_coverage
    python3 -m unittest scripts.tests.test_create_autogenesis_reflexivity_coverage_input
    python3 -m unittest scripts.tests.test_check_autogenesis_reflexivity_coverage
    python3 scripts/check-autogenesis-reflexivity-coverage.py
    python3 -m unittest scripts.tests.test_analyze_autogenesis_type_slices scripts.tests.test_check_autogenesis_type_slice_feasibility
    python3 scripts/check-autogenesis-type-slice-feasibility.py
    python3 -m unittest scripts.tests.test_check_autogenesis_factorial_zero_family
    python3 scripts/check-autogenesis-factorial-zero-family.py
    python3 -m unittest scripts.tests.test_check_autogenesis_semantic_abstraction_census
    python3 scripts/check-autogenesis-semantic-abstraction-census.py
    cargo test -p axeyum-lean-import --test semantic_function_contract
    cargo test -p axeyum-lean-import --example semantic_contract_target_census
    python3 -m unittest scripts.tests.test_check_autogenesis_semantic_contract_target_census
    python3 scripts/check-autogenesis-semantic-contract-target-census.py
    cargo test -p axeyum-lean-import --test contract_residualization
    cargo test -p axeyum-lean-import --example int_gcd_contract_residualization
    python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_residualization
    python3 scripts/check-autogenesis-int-gcd-contract-residualization.py
    cargo test -p axeyum-lean-import --test source_delta_trace
    cargo test -p axeyum-lean-import --example int_gcd_source_delta_trace
    python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_source_delta
    python3 scripts/check-autogenesis-int-gcd-source-delta.py
    cargo test -p axeyum-lean-import --test trace_contract_receipt
    cargo test -p axeyum-lean-import --example int_gcd_trace_contract_receipt
    python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_trace_contract_receipt
    python3 scripts/check-autogenesis-int-gcd-trace-contract-receipt.py
    python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control_policy
    python3 scripts/check-autogenesis-int-gcd-contract-theorem-control-policy.py
    cargo test -p axeyum-lean-import --test trace_contract_theorem_receipt
    cargo test -p axeyum-lean-import --example int_gcd_contract_theorem_control
    python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control
    python3 scripts/check-autogenesis-int-gcd-contract-theorem-control.py
    python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_premise_selection_policy
    python3 scripts/check-autogenesis-nat-fib-gcd-premise-selection-policy.py

# The bulk source is external and optional on CI. The first checker reports
# verified/unavailable without conflating them; the committed 240-row view is
# always structurally checked and is re-derived when the content-addressed
# source is mounted.
autogenesis-mathlib-source:
    python3 -m unittest scripts.tests.test_check_autogenesis_mathlib_source
    python3 scripts/check-autogenesis-mathlib-source.py
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_candidates
    python3 scripts/create-autogenesis-mathlib-candidates.py --check

# This evaluation-only pass may inspect upstream theorem values, but its
# external artifact and committed projection contain names and edges only.
# Whole weak components are indivisible future split units.
autogenesis-mathlib-dependencies:
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_dependency_components
    python3 scripts/create-autogenesis-mathlib-dependency-components.py --check

# Statement-only review removes aliases and internal surfaces, reserves simple
# calibrations, and binds one answer-free mutation to every source family.
autogenesis-mathlib-review:
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_review
    python3 scripts/create-autogenesis-mathlib-nursery-review.py --check

# Materialize only open facts. The exact Mathlib environment accepts every
# formal.statement as an axiom TYPE; that proves proposition well-formedness,
# not the proposition, and no imported theorem becomes local proof credit.
autogenesis-mathlib-facts:
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_fact_catalog
    python3 scripts/create-autogenesis-mathlib-fact-catalog.py --check

# Explicit external experiment: launch one complete B -> A authoritative chain
# from a clean checkout and retain its independently checkable receipts.
autogenesis-authoritative-chain output:
    python3 scripts/run-autogenesis-authoritative-chain.py "{{ output }}"

# Credit requires two independently retained runs from the same exact source.
autogenesis-authoritative-compare first second output:
    python3 scripts/compare-autogenesis-authoritative-chains.py \
        "{{ first }}" "{{ second }}" --output "{{ output }}"

facts:
    python3 scripts/validate-facts.py
    python3 -m unittest scripts.tests.test_settled_fact_statements
    python3 scripts/check-settled-fact-statements.py
    # The ledger's `depends_on` graph — the arrow CLAUDE.md's flywheel calls
    # "the DAG picks the next goal". 60% of facts are isolated, so proving one
    # usually unlocks nothing; the ratchet keeps that from getting worse.
    python3 -m unittest scripts.tests.test_check_fact_dag
    python3 scripts/check-fact-dag.py --quiet
    # The same arrow, DERIVED rather than transcribed: a kernel-route fact's
    # `depends_on` is read out of the admitted proof term, so an unrecorded
    # dependency is a failure rather than an indistinguishable silence.
    python3 -m unittest scripts.tests.test_check_fact_depends_derived
    python3 scripts/check-fact-depends-derived.py --quiet
    # The ledger's PROSE, re-derived rather than re-read: a number a fact states
    # about its own `axiom_footprint` is compared to the array. It caught the
    # instance it was built from -- a fact that said "the 30 axioms" for three
    # days after its footprint was corrected to 26, with the `--expect-axioms`
    # flag right beside it already correct.
    python3 -m unittest scripts.tests.test_check_fact_derived_numbers
    python3 scripts/check-fact-derived-numbers.py --quiet
    python3 -m unittest scripts.tests.test_create_autogenesis_chain_catalog
    python3 scripts/create-autogenesis-chain-catalog.py --check
    # The mathematics strand's primary metric, derived rather than read: how many
    # capabilities carry an artifact an EXTERNAL checker accepts. Agreement with
    # an oracle is not an external check and is tiered separately.
    python3 -m unittest scripts.tests.test_check_capability_assurance
    python3 scripts/check-capability-assurance.py --quiet
    # Item A's minimum: the table NAMES the function behind each capability, and a
    # row naming a route that no longer exists is its cheapest lie -- the
    # capability reads as real and nothing notices the rename. 42 routes, 0 missing
    # when this landed, so it is a ratchet rather than a repair.
    python3 -m unittest scripts.tests.test_check_capability_routes
    python3 scripts/check-capability-routes.py
    # The layer under every other checker: a control that NO gate runs cannot
    # fail, so it is not a control. Runners name modules one by one, so wiring a
    # new one is a separate forgettable step -- measured 2026-08-17, 63 of 137
    # control modules were executed by nothing, and 6 of them no longer import.
    python3 -m unittest scripts.tests.test_check_control_tests_reachable
    python3 scripts/check-control-tests-reachable.py
    # The mutation harness itself. Every "exactly one test died" in this repository
    # rests on the mutant having been BUILT and RUN, and until 2026-08-18 nothing
    # checked either: a mutation that broke compilation, and a suite that executed
    # zero tests, both arrived as "not clean" and were scored as coverage. The four
    # outcomes are now distinct, and `self-demo` produces one of each from a real
    # mutation -- so a harness that cannot tell them apart fails here rather than
    # reporting a number nobody measured.
    python3 -m unittest scripts.tests.test_mutation_controls
    python3 scripts/tests/mutation_controls.py self-demo
    python3 scripts/tests/mutation_controls.py --check-anchors
    python3 scripts/gen-example-inventory.py --check
    ./scripts/tests/test-gen-example-inventory.sh
    # 44 controls that were already written and already correct, but which no
    # gate ran. 257 tests, ~31s. The seven not adopted are listed in the script.
    scripts/check-adopted-controls.sh
    # How much code must be CORRECT for an admitted theorem to be true? Derived
    # from the only call that makes a declaration exist -- Environment::insert_unchecked
    # -- not from a list: 5,129 function-body lines across 9 files, forward
    # closure from the four admission gates. It found that lean_export.rs, filed
    # as "interop", owns `is_k_like_inductive` on the iota-reduction path.
    python3 -m unittest scripts.tests.test_check_kernel_trusted_core
    python3 scripts/check-kernel-trusted-core.py
    # The CLAIM ledger's structural pass, which `scripts/check.sh` has always run
    # and `just check` did not -- so the fallback gate checked something the
    # preferred one skipped, which is exactly the divergence
    # `check-aggregate-scope.sh` exists to catch (it was the only unrecorded one).
    #
    # Only this pass moves. The `claims` recipe stays out of `check` for the
    # reason written above it: its certificate pass re-verifies every stored UNSAT
    # proof, takes minutes, and needs the gitignored drat-trim clone that the
    # no-C-dependency default gate must not require. That recipe's own comment
    # calls the first two "a seconds-long structural gate"; this is the first.
    python3 scripts/validate-claims.py
    # A settled SMT-route fact's evidence command tests the VERDICT and not the
    # CERTIFICATION: `test "$(... | tail -1)" = unsat` exits 0 on an uncertified
    # refutation, verified against a dedicated uncertified integer-square fixture.
    # 18 of 18 such instances are certified today -- by practice, not enforcement.
    python3 -m unittest scripts.tests.test_check_smt_evidence_certified
    python3 scripts/check-smt-evidence-certified.py --quiet
    # A `cas-certificate` geometry fact states its theorem twice -- as SMT-LIB in
    # `formal.statement` and as polynomials in the certificate it cites -- and
    # nothing connected the two, so a transposed sign would leave a `proved` fact
    # claiming something its evidence does not establish. Sub-second; three lanes
    # did this by hand before it was a gate.
    python3 scripts/check-geometry-fact-transcription.py
    # THE WEAKEST LINK IN THE TRUST CHAIN, until this landed. A reconstructed
    # UNSAT declares the query's constraints as the Lean module's OWN axioms and
    # proves False from them -- and nothing checked that those axioms are what
    # the `.smt2` said. A dropped negation would typecheck, report a clean axiom
    # footprint, and be worthless
    # (docs/prover-track/research/13-residual-trust-surface.md item 3).
    #
    # Binds every rendered `lra.hyp._N`/`int_hyp._N` back to an `(assert ...)`
    # line, both sides parsed in Python so a bug in the renderer's normalizer
    # cannot cancel out. 105 instances, 248 hypotheses, ~31s + the example build.
    # Corrupts each hypothesis five ways on every run and requires the
    # corruptions to be caught, because a checker that cannot fail is worse than
    # none.
    python3 -m unittest scripts.tests.test_check_lra_hypothesis_binding
    python3 scripts/check-lra-hypothesis-binding.py

# Re-run the evidence behind every settled fact, route-agnostically. `facts`
# above checks the ledger is CONSISTENT; this checks it is still TRUE -- a fact
# can be correct the day it lands and rot as the code beneath it changes.
# ~330s, dominated by per-checker cargo startup rather than by the checkers.
facts-replay:
    ./scripts/check-fact-evidence-replay.sh

# Pin +stable so local clippy matches CI's stable toolchain: nightly and stable
# carry different lints, so a nightly-only local gate lets clippy breaks slip
# onto main. Run `rustup update stable` if a lint CI hits doesn't reproduce
# locally (toolchain drift).
#
# The example this comment used to give (`manual_assert_eq`) was wrong and is
# instructive: as of clippy 0.1.97 NEITHER the stable nor the nightly build here
# knows that lint, so the `#![allow(clippy::manual_assert_eq)]` in
# crates/axeyum-verify/tests/ was itself an `unknown lint` ERROR under
# `-D warnings` and had been failing this gate. Fixed in 451f9c50 by adding
# `#![allow(unknown_lints)]` ahead of it, which is toolchain-agnostic in both
# directions.
#
# Run through `check-clippy-complete.sh`, which reports how many workspace
# targets were actually linted and refuses to pass over content cargo never
# compiled. `cargo clippy` exited 0 over a CACHED example carrying
# `too_many_lines` on 2026-08-13, because cargo decides freshness by MTIME and
# `git archive | tar -x` stamps every file with the commit time.
clippy:
    scripts/check-clippy-complete.sh --toolchain stable

# Are this repository's two aggregate gates the same gate? `just check` and
# `./scripts/check.sh` ran 112 and 61 steps on 2026-08-14 while CLAUDE.md called
# them the same thing. This pins the divergence so it cannot grow in silence.
aggregate-scope:
    scripts/check-aggregate-scope.sh

# The negative controls for the two gate-scope fixes above: each shows the old
# gate green on a broken tree, the new gate red, and the new gate green again
# with its guard deleted (a mutation test on our own gate). ~30 s, no workspace
# build -- it runs against a throwaway one-crate workspace.
gate-controls:
    scripts/tests/test-gate-scope-controls.sh
    # Controls for the two gates that check other gates: the local-ci run
    # recorder (a step exiting 0 with zero tests must record `vacuous` -- that
    # guard was unreachable when written) and the fact scaffolder (a
    # `checker_command` must be proved able to FAIL before the fact exists).
    scripts/tests/test-local-ci-record.sh
    # Controls for `local-ci-freshness` below: a stale / non-ancestor / FAIL /
    # vacuous-step / unreadable-step / self-inconsistent record must each red
    # it by name, and a fresh all-pass ancestor record must go green. Every
    # guard was mutation-tested individually (delete one, exactly one control
    # dies) -- see the header of scripts/check-local-ci-freshness.sh.
    scripts/tests/test-check-local-ci-freshness.sh
    # Controls for `parity-freshness` below. Twelve cases, every guard
    # mutation-tested: a stale board, a board whose only fresh entry is VOIDED,
    # an unrecognised `## ` header and a near-empty parse must each red it, and
    # a fresh board -- including one whose freshest entry carries the trailing
    # `— EVIDENCE MODE` label -- must go green. Two of the twelve run against
    # the REAL committed ledger, because a parser never pointed at its subject
    # returns the same empty answer as a strong negative result.
    scripts/tests/test-check-parity-freshness.sh
    scripts/tests/test-new-fact-controls.sh
    scripts/tests/test-lane-commit.sh
    # `--to <branch>`: the range, the cost estimate and the fast-forward check
    # must follow the ref being PUSHED, not the current branch's remote copy.
    # Against a stale `origin/<branch>` the same doc-only landing reads FULL
    # BATTERY instead of FREE, and an estimate that errs expensive gets ignored.
    scripts/tests/test-lane-push-target.sh
    # The pre-push compile step must carry --all-targets: without it,
    # examples/ and tests/ are never compiled and the hook's
    # "pushed SHA compiles" line is false for half the tree.
    scripts/tests/test-prepush-checks-all-targets.sh
    scripts/tests/test-prepare-prepush-worktree.sh
    scripts/tests/test-check-lean-golden-pins.sh
    # ...and the ratchet that makes the two lines above impossible to forget.
    # Both were written, both pass, and one was invoked by NOTHING for a day,
    # because registering a control is a manual step separate from writing it.
    # A control nobody runs cannot fail, so it is not a control.
    scripts/check-control-registration.sh
    # `grep -q` in a pipeline under pipefail, and `$?` read after a pipeline:
    # both print a wrong answer while exiting 0, and both shipped here.
    scripts/check-shell-antipatterns.sh
    # DOMINANCE.md is generated; without a --check it sat six audits stale
    # while reading as current.
    python3 -m unittest scripts.tests.test_gen_dominance_scoreboard
    python3 scripts/gen-dominance-scoreboard.py --check
    # The dominance audit harness's own unit tests. No script ran them, so a
    # test broken by ADR-0384's three-valued `Evidence::check` sat red and
    # unseen. Expect a NONZERO count (10).
    cargo test -p axeyum-bench --example audit_dominance
    # explain_corpus's own tests: they pin the measured divergence from the
    # front door (134 of 397) as token discipline plus two refusals. Expect a
    # NONZERO count (21).
    cargo test -p axeyum-bench --example explain_corpus
    # Lean-reconstruction unit tests, moved out of hooks/pre-push (268 tests,
    # 294s, each building Lean preludes). They belong in a daily gate, not on
    # every push -- and before this neither aggregate gate ran them.
    cargo test -p axeyum-solver --lib --features full reconstruct::
    # The one evidence test that builds Lean preludes: 292.973s of a 293.08s
    # suite. Skipped in hooks/pre-push; this is where it runs.
    cargo test -p axeyum-solver --features full --test evidence qf_nra_sos_certificate_wrapper_carries_lean_module

# Is there a FRESH, PASSING, fully-measured `local-ci --record` for (an
# ancestor of) HEAD? A green record proves nothing on its own -- see
# scripts/check-local-ci-freshness.sh's header for what "fresh" means here and
# why. ENFORCING as of 2026-08-19 (it was `--report-only` only while the sole
# record in existence, a6ee37c6a-s4.json, was `verdict: FAIL`; 57af69142-s4
# is all-pass, 5/5 steps, 7561 nextest + 179 doctests).
#
# If this reds and your change is unrelated, it is almost certainly STALE:
# run `scripts/local-ci.sh --record` (~110 min, one lock across the box) and
# commit the record. Do not re-add `--report-only`.
local-ci-freshness:
    scripts/check-local-ci-freshness.sh

# Has the parity board been re-measured recently enough to still mean anything?
# `bench-results/PARITY.md` is the declared headline -- external list pinned by
# sha256 before each run, `DISAGREEMENTS > 0` voids an entry -- and the script
# that writes it, `scripts/parity-run.sh`, was invoked by NO gate until
# 2026-08-21. It froze on 2026-08-06 for fifteen days, through UF 32 -> 85 and
# QF_RDL 10 -> 105, and nothing went red.
#
# Budget is 14 days PER LOGIC (warning at 10), so the remedy for a red is one
# sweep -- `scripts/parity-run.sh <LOGIC>`, 1-3 h -- and not a board refresh.
# See scripts/check-parity-freshness.py's header for why 14 and not a rounder
# number. Do not soften it by editing the ledger: it is append-only so a number
# going down stays visible.
parity-freshness:
    scripts/check-parity-freshness.py

autogenesis-knowledge-controls:
    scripts/check-autogenesis-knowledge-controls.sh

autogenesis-proposer-isolation:
    scripts/check-autogenesis-proposer-isolation.sh

autogenesis-induction-search:
    scripts/check-autogenesis-induction-search.sh

autogenesis-apply-search:
    scripts/check-autogenesis-apply-search.sh

autogenesis-result:
    python3 -m unittest scripts.tests.test_compare_autogenesis_authoritative_chains
    python3 -m unittest scripts.tests.test_check_autogenesis_1_result
    python3 scripts/check-autogenesis-1-result.py

# `frontier_*` is skipped here and run by `frontier` instead. Those ratchets
# measure "the largest N decided within a fixed WALL-CLOCK budget", so running
# them alongside the rest of the workspace suite lets CPU contention shrink the
# measured frontier and report a false REGRESSION. That is worse than an ordinary
# flake: the failure text invites lowering the committed baseline, so a loaded
# run could ratchet the project down on a measurement artifact. Measured
# 2026-07-30 -- lia_cuts reported 24 < 26 under `check.sh` and passed 9/9
# standalone on the same commit, with no artifact actually moving.
#
# Run through `check-workspace-tests.sh`, which prints the number of tests that
# actually ran (a suite emptied by a `cfg` exits 0 printing "running 0 tests")
# and touches content whose hash changed so cargo cannot replay a cached test
# binary over source it never compiled (measured: `cargo test` printed
# "1 passed" for a test that must fail, after the file was stamped in the past).
test:
    scripts/check-workspace-tests.sh

# The capability ratchets, serialized and alone. Run nothing else concurrently.
frontier:
    cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1

# Proves the gates above still RUN something. `cargo test` exits 0 on an empty
# test binary, so a suite a new `#![cfg(feature = ...)]` has emptied looks
# exactly like a passing one -- the corpus `:status` sweep was inert that way for
# 15 days. This pins a MINIMUM test count per suite; `--list` compiles without
# executing, so it is cheap.
gate-liveness:
    ./scripts/check-gate-liveness.sh

# The golden-Lean-module gate. Every suite that pins a rendered module's bytes,
# DISCOVERED rather than listed: membership is "calls
# `lean_golden::assert_golden_module`", which is the same act as being a golden
# pin, so a new golden cannot be added outside the gate. It also refuses a
# hand-rolled whole-module `(len, fnv1a)` pin, which is how the banner got back
# under the pins three times (`0fc7cc357`, `b760fd6ae`, `46724faec`).
#
# These are `tests/*.rs` integration targets and NOTHING ran them: `--lib` skips
# integration targets, `hooks/pre-push` names six of the workspace's 465, and the
# only sweep that covers them is local-ci, which had never completed until
# 2026-08-18 -- when it found all four of them red.
golden-lean-pins:
    ./scripts/check-lean-golden-pins.sh

# The kernel's suite partition: every `crates/axeyum-lean-kernel/tests/*.rs` must
# be in EXACTLY ONE of {runs at push time, owned by `scripts/check-lean-gate.sh`}.
# `hooks/pre-push` ran the crate wholesale, so the fifteen real-Lean suites ran
# twice on every push -- 2,396 s of a ~900 s hook, measured 2026-08-19 -- and the
# fix for that (run only the non-Lean half) is only safe while the other half is
# provably owned. Membership is DISCOVERED from the source, never listed, so a
# new suite cannot land outside both halves. `--list` asserts and prints the
# split without building anything; the run itself belongs to the push gate.
kernel-suite-partition:
    python3 -m unittest scripts.tests.test_check_kernel_suites
    ./scripts/check-kernel-suites.sh --list

# The real-Lean gate: every suite that hands a generated module to an EXTERNAL
# `lean` binary, with the toolchain RESOLVED FROM THE PIN in `lean-toolchain`
# (`AXEYUM_LEAN_BIN`, then the pinned toolchain's elan directory, then PATH or
# any other elan toolchain ONLY IF its `--version` matches the pin) and
# `AXEYUM_REQUIRE_LEAN=1` set, so a missing binary fails instead of printing a
# skip note and passing. It prints the number of Lean invocations that actually
# happened and enforces a floor -- an exit status cannot tell "checked 40
# modules" from "checked none", and that is precisely how a real Lean rejection
# of our exported modules stayed invisible until 2026-08-14. On a machine with
# no Lean at all: AXEYUM_ALLOW_NO_LEAN=1.
#
# The policy controls run FIRST and are cheap (~30s): they point both entry
# points at a non-pinned toolchain and require the refusal, and they check that
# the shell gate and the Rust probe resolve the SAME binary. Until 2026-08-17
# they did not -- the gate took PATH's lean (4.30.0) and the probe took the
# newest installed name (4.34.0-rc1), under which 21 of 77 `lean_crosscheck`
# families were rejected. A gate whose answer depends on an unstated fact about
# the machine is this repository's signature defect.
lean-gate:
    ./scripts/tests/test-lean-toolchain-policy.sh
    ./scripts/check-lean-gate.sh

# Same as `test`, but under a hard 64 GiB memory cap (scripts/mem-run.sh) so a
# runaway allocation (e.g. an unbounded NRA / wide bit-blast blowup) aborts the
# test process instead of OOM-killing the host. Prefer this when touching solving
# paths. Override the cap with MEM_LIMIT_GB=N.
test-guarded:
    MEM_LIMIT_GB=64 ./scripts/mem-run.sh cargo test --workspace --all-features

# Scope-aware ITERATION gate: runs only the gates relevant to what changed vs a
# base ref (default `main`) — see scripts/check-scope.sh. Use this while
# iterating; `check` stays the authoritative pre-merge/CI gate. Feedback is
# proportional to the change (a Python-only or one-crate edit gates in seconds).
check-scope base="main":
    ./scripts/check-scope.sh {{base}}

# The order-255 certified-moment proofs (squared_binomial_{,falling_}moment_...),
# kept OFF the per-iteration hot path via #[ignore] (~15 min each). The `check`
# chain runs this so CI coverage is unchanged; run it yourself only when you
# touch moment / squared-binomial / falling-factorial code.
moment-proofs:
    cargo test -p axeyum-cas --lib -- --ignored

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
    # The formalized-math strand's status block, re-derived from the tree. It
    # went stale silently and routed the strand at a census that had already
    # been run twice; see scripts/check-import-status.py.
    python3 -m unittest scripts.tests.test_check_import_status
    python3 scripts/check-import-status.py
    python3 -m unittest scripts.tests.test_parity_evidence
    python3 -m unittest scripts.tests.test_parity_resume
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
    python3 -m unittest scripts.tests.test_gen_theorem_production_ledger
    MEM_LIMIT_GB=4 ./scripts/mem-run.sh python3 scripts/gen-theorem-production-ledger.py --check
    python3 -m unittest scripts.tests.test_gen_production_provenance_ledger
    python3 scripts/gen-production-provenance-ledger.py --check
    python3 scripts/gen-gap-ownership.py --check
    python3 scripts/gen-measurement-provenance.py --check
    python3 scripts/gen-smtcomp-resume-contract.py --check
    python3 scripts/gen-proof-gap-matrix.py --check
    python3 scripts/gen-proof-gap-shape-census.py --check
    python3 scripts/gen-smtlib-api-conformance.py --check
    python3 scripts/gen-smtlib-session-contract.py --check
    python3 scripts/gen-scoreboard.py --check
    python3 scripts/check-parity-docs.py

# ADR-0344 E0-E2: contract generation, immutable filesystem recovery, active
# runner lifecycle/sidecars/lease/export, one-host aggregate cgroup evidence,
# portable plus opt-in N>=3 multi-host durability evidence, and the legacy
# scoring pipeline.
smtcomp-resume:
    ./scripts/check-smtcomp-resume.sh

# PLAN.md and the ADR index are generated views over per-lane sources. They
# were the two files concurrent lanes clobbered four times on 2026-08-14 --
# 67 and 60 touches in 24 hours -- because the session protocol told every lane
# to append to them. These two gates make a hand edit a failure instead of
# somebody else's lost line.
#
# The claim dashboard is the third such view and was gated by NOTHING until
# 2026-08-16. It had been crashing (a `would_settle` written as a list, which
# claim.schema.json forbids and validate-claims.py did not type-check), so the
# committed file -- headed "Auto-generated. Do not edit by hand." -- still
# reported 38 claims across 1 family against an actual 104 across 3, and showed
# the flagship R_4(5(x-y)=4z) result as `open` at "> 740" when the ledger had it
# `computed` at exactly 741. Nobody edited it wrongly; nobody ran it at all.
generated-trackers:
    python3 scripts/validate-autogenesis-operations.py
    python3 -m unittest scripts.tests.test_validate_autogenesis_operations
    python3 -m unittest scripts.tests.test_fact_frontier
    python3 -m unittest scripts.tests.test_create_autogenesis_chain_catalog
    python3 -m unittest scripts.tests.test_execute_autogenesis_operation
    python3 -m unittest scripts.tests.test_check_autogenesis_fact_operation
    python3 -m unittest scripts.tests.test_gen_autogenesis_baseline
    python3 -m unittest scripts.tests.test_create_autogenesis_snapshot
    python3 -m unittest scripts.tests.test_create_autogenesis_proposer_catalog
    python3 -m unittest scripts.tests.test_autogenesis_apply_proposer
    python3 -m unittest scripts.tests.test_verify_autogenesis_apply_proposals
    python3 -m unittest scripts.tests.test_autogenesis_induction_proposer
    python3 -m unittest scripts.tests.test_verify_autogenesis_induction_proposals
    python3 -m unittest scripts.tests.test_create_autogenesis_premise_evidence
    python3 -m unittest scripts.tests.test_create_autogenesis_premise_transition
    python3 -m unittest scripts.tests.test_create_autogenesis_accepted_event
    python3 -m unittest scripts.tests.test_prepare_autogenesis_fact_transaction
    python3 -m unittest scripts.tests.test_apply_autogenesis_fact_transaction
    python3 -m unittest scripts.tests.test_create_autogenesis_readiness_delta
    python3 scripts/gen-autogenesis-baseline.py --check
    python3 -m unittest scripts.tests.test_gen_plan
    python3 scripts/gen-plan.py --check
    python3 -m unittest scripts.tests.test_gen_adr_index
    python3 scripts/gen-adr-index.py --check
    python3 scripts/gen-claims-dashboard.py --check

# The `axeyum-solver` decomposition ratchet (docs/refactor-2026-08/03).
# `axeyum-solver` is 46% of the workspace and the plan is to cut crates out of
# it. A cut point with a dependency cycle across it is not a cut point, so this
# measures the intra-crate module graph and fails when a module that was
# acyclic enters a cycle, or when anything outside the evidence/reconstruction
# layer starts depending on it.
#
# The measurement is not a grep. Three naive versions of it disagreed: rustdoc
# intra-doc links invent edges, `#[cfg(test)]` code invents more, and ignoring
# the crate's own 267-entry re-export facade -- through which its modules
# import each other -- HIDES 340. The unit tests pin all three behaviours on
# synthetic crates and prove the ratchet can fail.
solver-module-graph:
    python3 -m unittest scripts.tests.test_analyze_solver_module_graph
    python3 scripts/analyze_solver_module_graph.py --check

# Process-wide Lean prelude reuse (ADR-0464) checked from OUTSIDE the crate:
# every inventory example must print byte-identical stdout/stderr with the cache
# on and off, AND the counters must show the cache was actually exercised in one
# run and not the other -- "the flag changed nothing" and "the flag was ignored"
# are otherwise the same observation. Landed 2026-08-15 but unregistered,
# because `justfile` and `scripts/check.sh` both had another lane's uncommitted
# edits at the time.
prelude-reuse:
    ./scripts/check-prelude-reuse-equivalence.sh

# Prevent PLAN/STATUS/TODO from becoming competing project-level authorities.
plan-authority:
    python3 scripts/check-plan-authority.py

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

# ADR numbers are a shared append point ACROSS CHECKOUTS: `gen-adr-index.py
# --check` only ever reads this working tree, so two lanes in two clones can
# each read "the highest number I can see", allocate the same one for two
# different decisions, and merge clean (the filenames differ by slug, so git
# never conflicts) -- measured 2026-08-18, `origin/main` and this branch had
# claimed 0471-0474 twice AND (found live, by this gate) 0468-0470 a second
# time. `--check-remote` diffs this tree's ADR numbers against
# `origin/main`'s and fails on a real collision, naming it and the next free
# number. Deliberately does NOT fail when `origin/main` is unresolvable (no
# fetch, no `origin`, not a git checkout) -- see the docstring on
# `check_remote` in gen-adr-index.py for why fail-open there is the right
# side of the trade, and why a STALE fetch is handled differently again. Kept
# LAST in `check`'s dependency list, unlike `adr-index` above (folded into
# `generated-trackers`): `just` aborts a recipe chain at the first failing
# dependency, and this one is expected to fail for real stretches of time
# (fixing a live collision means renumbering every cross-reference to the
# ADRs it names, which is its own task) -- putting it last means a collision
# here does not hide whether fmt/clippy/tests/links/etc. passed.
adr-remote-collisions:
    python3 scripts/gen-adr-index.py --check-remote

# The ADR-0380 claim-ledger gates: structural/referential/epistemic validation of
# every artifacts/claims/**/claim.json, the negative fixtures that prove the
# validator actually rejects bad claims, and the independent semantic re-check of
# every `checked` evidence row (witness replay by a third enumerator; stored CNF
# regenerated byte-identically, then drat-trim on the DRAT).
#
# Deliberately NOT part of `check`: the certificate pass re-verifies every stored
# UNSAT proof and takes minutes, and it needs the gitignored drat-trim clone
# (`just references`), which the no-C-dependency default gate must not require.
# Run the first two alone for a seconds-long structural gate.
claims:
    python3 scripts/validate-claims.py
    python3 scripts/check-claim-negative-fixtures.py
    python3 scripts/check-claim-certificates.py --drat-checker references/drat-trim/drat-trim

# The propositional Craig interpolant's certificate, checked by an OUTSIDE
# implementation: the two DRAT refutations of the Craig conditions handed to
# Marijn Heule's drat-trim rather than to our own `check_drat`.
#
# `AXEYUM_REQUIRE_DRAT_TRIM=1` turns a missing binary into a FAILURE. Without it
# the suite skips the external half, which is the right default (drat-trim is a
# gitignored clone, `just references`) but the wrong thing for a gate that exists
# to prove a third party accepts our artifact -- a skip and a pass look identical.
interpolant-certificate:
    AXEYUM_REQUIRE_DRAT_TRIM=1 cargo test -p axeyum-cnf --test propositional_interpolant_certified

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
