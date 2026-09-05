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
check: fmt fmt-all facts facts-replay clippy gate-controls kernel-stack-envelope deep-stack-call-sites axiom-freedom external-coupling autogenesis-knowledge-controls tactic-catalog-controls autogenesis-proposer-isolation autogenesis-induction-search autogenesis-apply-search autogenesis-result autogenesis-nursery autogenesis-mathlib-source autogenesis-mathlib-dependencies autogenesis-mathlib-review autogenesis-mathlib-facts test frontier gate-liveness golden-lean-pins kernel-suite-partition lean-gate prelude-reuse moment-proofs ntheory-certificates doc py-check qfbv-profile reflection-semantics-gate benchmark-repetition-tests glaurung-qfbv-regular foundational-resources rules-as-code smtcomp-resume parity-docs generated-trackers solver-module-graph plan-authority links gate-step-timeout shared-index sos-negative-controls evidence-portability aggregate-scope adr-remote-collisions local-ci-freshness parity-freshness episodes product-health obstruction-graph mobility-census python-coverage lane-turn-controls correspondences autogenesis-kernel-projection autogenesis-kernel-lemma-index autogenesis-obstruction-projection autogenesis-transport-projection autogenesis-capability-gap autogenesis-concept-coverage autogenesis-producer-outcomes autogenesis-producer-evaluation-frontier autogenesis-binomial-arrow autogenesis-next-reusable-family autogenesis-producer-evaluation-protocol autogenesis-producer-evaluation-result-contract autogenesis-capability-demand autogenesis-nat-modeq-imported-bridge-assay autogenesis-nat-modeq-remainder-contract autogenesis-nat-modeq-remainder-contract-v2 autogenesis-nat-modeq-remainder-operation tock-log2-maestro-controls library-artifact-contract module-baseline module-baseline-controls kernel-differential declaration-graph graph-join infrastructure-frontier effort-taxonomy graph-dispatcher structural-index checked-interchange lean-adapter declaration-spec proof-plan absence-claims curriculum-bucket-cohesion curriculum-bucket-cohesion-controls

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

# `just next` picks the target; `just brief` is what you run BEFORE writing the
# brief for it. Same reasoning as `next` above, one arrow further along: a
# retrieval tool nobody reaches is prose, and prose is measured at 4.8%.
#
# Measured 2026-08-29 over 272 lane status documents -- mutation testing, which
# has a harness and a gate, appears in 125 (46%); `shape_search`, which has only
# instructions behind it, in 13 (4.8%). Compliance tracks MECHANIZATION, not
# emphasis, and thirteen-plus recorded instances of a lane re-deriving something
# that already existed are what the gap costs. So the step moves out of the lane
# (where it competes with the task for attention at the moment the lane is most
# eager to start) and into the dispatcher's hands, where it is one command.
#
# Prints, per target: whether a declaration with this statement's constants is
# ALREADY in the kernel environment (by rendered type, never by name); the
# `shape_search` near-miss query and its answer; every module basename the
# target could mean, BOTH paths when a basename lives in two preludes; and
# whether the target is held-out, a mutation control, or divergence-blocked.
#
# Sub-second against a warm snapshot. Non-zero exit means something is wrong
# with the ANSWER, not with the target: 3 = the snapshot cannot even retrieve
# the built-in control probe, so no negative in the run would have meant
# anything; 4 = the snapshot is stale, so every ABSENT is provisional.
#
# Step 0 of a brief: does the target already exist, and is it even dispatchable?
brief *targets:
    python3 scripts/brief-step0.py {{targets}}

# One 33 s read of `Kernel::environment()` into a snapshot addressed by the
# kernel tree sha. Needed after any kernel change that lands a declaration;
# `just brief` exits 4 and says so rather than answering from an old one.
#
# Re-read the kernel environment into the `just brief` snapshot (~2 min).
brief-refresh:
    python3 scripts/brief-step0.py --refresh --build

# The controls, plus the snapshot's own self-check, with no target.
brief-self-check:
    python3 scripts/brief-step0.py --self-check
    scripts/tests/test-brief-step0.sh

autogenesis-operations:
    python3 scripts/validate-autogenesis-operations.py
    python3 -m unittest scripts.tests.test_validate_autogenesis_operations

# ADR-0602: prospective producer contracts (a capability claim, never a
# completion claim) -- the separate artifact `fact-frontier.py` selects
# against alongside the operation registry above.
autogenesis-producer-contracts:
    python3 scripts/validate-producer-contracts.py
    python3 -m unittest scripts.tests.test_validate_producer_contracts

# Doc 291: contract-driven decline artifacts -- a real producer attempt
# against a matched contract that came back honestly negative. `fact-frontier.py`
# reads these back so the selector stops re-presenting a `(fact, contract)`
# pair a producer already declined; this validator is what keeps a decline
# from becoming a cheap way to make the selector shut up about a fact forever.
autogenesis-producer-contract-declines:
    python3 scripts/validate-producer-contract-declines.py
    python3 -m unittest scripts.tests.test_validate_producer_contract_declines

# Validate and exactly regenerate the frozen leakage-safe population contract.
autogenesis-nursery:
    python3 -m unittest scripts.tests.test_check_autogenesis_nursery
    python3 -m unittest scripts.tests.test_nursery_exemption_guards
    python3 -m unittest scripts.tests.test_rescope_nursery_exemption
    python3 -m unittest scripts.tests.test_create_autogenesis_mathlib_nursery_split
    python3 -m unittest scripts.tests.test_create_autogenesis_nursery_dispatch_baseline
    python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
    python3 -m unittest scripts.tests.test_check_autogenesis_holdout_isolation
    python3 scripts/check-autogenesis-holdout-isolation.py
    # ADR-0695. The isolation gate above reads `epistemic_status` and scans for
    # textual references; neither sees a held-out row that the kernel DECIDES BY
    # REDUCTION. `Nat.fermatNumber 0 = 3` closed by `Eq.refl` 21 minutes before
    # draw 7 preregistered it blind. Needs no cargo -- it reads the committed
    # environment snapshot -- and self-tests its classifier on every run,
    # because today's population is clean and would otherwise pass vacuously.
    python3 -m unittest scripts.tests.test_check_holdout_closed_evaluation
    python3 scripts/check-holdout-closed-evaluation.py
    # ADR-0763. ADR-0653's ADJACENCY rule, which no code enforced until
    # 2026-08-30: R9 compares a candidate's Mathlib NAME against the
    # environment, so a draw holding out `Init.Data.Nat.Bitwise.Lemmas`
    # beside the development family `natural-bitwise` returned GUARD
    # PASSED. `--self-test` carries accepting cases as well as refusals;
    # the population is clean today, so refusal-only tests would pass
    # vacuously and a screen that refuses everything would look correct.
    python3 -m unittest scripts.tests.test_check_holdout_adjacency
    python3 scripts/check-holdout-adjacency.py --self-test
    python3 scripts/check-holdout-adjacency.py
    # Registered here for the first time 2026-09-02 (mirrors scripts/check.sh):
    # this script had its own negative control but was invoked by NOTHING --
    # check-control-registration.sh derives its registry from
    # scripts/tests/*, so a top-level scripts/check-*.py with no matching
    # test file was invisible to it too.
    python3 scripts/check-draw7-frozen-families.py
    # ADR-0652. One producer per generated artifact: the statable vocabulary
    # had two writers and the poorer one deleted `bridge_provenance` and
    # `row_digest` at exit 0. Runs each non-owner producer in a sandboxed copy
    # and requires byte-identity; a planted second writer is its own control.
    python3 -m unittest scripts.tests.test_check_generated_artifact_ownership
    python3 scripts/check-generated-artifact-ownership.py
    # ADR-0615 left this unregistered because it was red on a fact's statement
    # drift; that is resolved, and ADR-0616 made it load-bearing -- R3 compares
    # the UNATTESTED cohort against the attested one, so `surface_validation` is
    # now something the ceiling depends on and this re-derives it.
    python3 -m unittest scripts.tests.test_gen_autogenesis_nursery_refill
    python3 scripts/gen-autogenesis-nursery-refill.py --check
    python3 -m unittest scripts.tests.test_check_autogenesis_holdout_contamination
    python3 scripts/check-autogenesis-holdout-contamination.py
    bash scripts/tests/test-dispatchable-frontier.sh
    python3 scripts/check-dispatchable-frontier.py
    # L3 D4: does an open obstruction actually compile into a falsifiable,
    # plural producer contract, or does classification stop at "blocked"?
    # `gen-obstruction-producers.py --check` re-derives both the
    # classification and every contract from primary sources on each run.
    bash scripts/tests/test-obstruction-producers.sh
    python3 scripts/check-obstruction-producers.py
    # ...and the CLASSIFICATION itself, which the checker above only compares
    # against a recomputation -- so a wrong classification that is stably wrong
    # passes it. ADR-1545: the `Nat.testBit` row claimed `new-construction` and
    # said the construction was not built, when it was built, axiom-free, and
    # had moved no mirror. Four mutations, each killing exactly one test.
    python3 -m unittest scripts.tests.test_gen_obstruction_producers
    # ...and the artifact S2/S3/S4 constrain. Those three pin every field of the
    # statable vocabulary to one value, so it is DERIVED (`--write`) rather than
    # maintained. This checks what no other gate reads: the row digest, which is
    # what makes the generator the only way a row gets in, plus the coverage
    # block, the source pin, and the environment-snapshot pointer.
    bash scripts/tests/test-gen-autogenesis-statable-vocabulary.sh
    python3 scripts/gen-autogenesis-statable-vocabulary.py
    # Can the queue be REFILLED? The frontier says how deep it is; a draw is a
    # hand edit to gen-autogenesis-nursery-refill.py, so re-running that adds
    # nothing and nobody was computing whether the pool still has families.
    bash scripts/tests/test-propose-nursery-refill.sh
    python3 scripts/propose-nursery-refill.py
    python3 scripts/check-autogenesis-already-proved.py
    python3 scripts/check-dispatchable-frontier.py --statable artifacts/autogenesis/nursery-v2-extension.json
    python3 -m unittest scripts.tests.test_artifact_gate_provenance
    python3 scripts/check-artifact-gate-provenance.py
    python3 -m unittest scripts.tests.test_development_partition
    python3 scripts/check-development-partition.py
    python3 -m unittest scripts.tests.test_check_autogenesis_must_decline_population
    python3 scripts/check-autogenesis-must-decline-population.py
    python3 scripts/check-autogenesis-bounded-induction-family.py
    python3 scripts/check-autogenesis-modeq-family.py
    python3 scripts/check-autogenesis-nat-modeq-family.py
    python3 scripts/check-established-facts-bounded-truth.py
    python3 scripts/check-autogenesis-nursery.py
    # The per-edge half of the same property (ADR-1550): the component gate
    # above runs only in this ~10-minute gate, the edge gate also runs in
    # hooks/pre-push and check-merge-hygiene.sh at 0.13s.
    python3 scripts/check-partition-edges.py --baseline
    python3 -m unittest scripts.tests.test_check_partition_edges
    # ADR-1551 refused option 1 and this enforces the five findings the
    # refusal rests on, so it can expire rather than go stale in a document.
    python3 scripts/nursery-components.py --check
    python3 -m unittest scripts.tests.test_nursery_components
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
    python3 -m unittest scripts.tests.test_check_autogenesis_checked_type_slice_replay
    python3 scripts/check-autogenesis-checked-type-slice-replay.py
    python3 -m unittest scripts.tests.test_check_autogenesis_auto_param_binder_replay
    python3 scripts/check-autogenesis-auto-param-binder-replay.py
    python3 -m unittest scripts.tests.test_check_autogenesis_type_slice_producer_census
    python3 scripts/check-autogenesis-type-slice-producer-census.py
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
    python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_neg_natcast_dependency_audit_result
    python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_of_odd_private_root_audit_plan
    python3 -m unittest scripts.tests.test_check_autogenesis_int_fib_of_odd_private_root_audit_result
    python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_surface_result
    python3 -m unittest scripts.tests.test_check_autogenesis_nat_gcd_greatest_result

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

# Run exactly the fact selected by the current authoritative frontier. The
# caller supplies no fact, operation, producer, checker, or admission metadata.
autogenesis-authoritative-fact output:
    python3 scripts/run-autogenesis-authoritative-fact.py "{{ output }}"

# Credit requires two independently retained runs from the same exact source.
autogenesis-authoritative-compare first second output:
    python3 scripts/compare-autogenesis-authoritative-chains.py \
        "{{ first }}" "{{ second }}" --output "{{ output }}"

facts:
    python3 scripts/validate-facts.py
    python3 -m unittest scripts.tests.test_validate_facts
    # Landed 2026-08-27 in `scripts/check.sh` only, so `just check` -- the gate
    # CLAUDE.md calls the preferred one -- did not run them. Two of the three
    # are the controls written that day BECAUSE a pair of tests could not fail;
    # a control that runs on one side of the aggregate gate runs for half the
    # people. `scripts/check-aggregate-scope.sh` is what surfaced the gap.
    python3 -m unittest scripts.tests.test_validate_facts_allowlist
    python3 -m unittest scripts.tests.test_check_shape_duplicates
    python3 -m unittest scripts.tests.test_theorem_inventory_completeness
    python3 -m unittest scripts.tests.test_check_absence_claims
    # ADR-0622: the `kernel-reconstructed` counter moved for an obligation
    # of the form `poly_expr(X) = 1 * poly_expr(X)`, because the classifier
    # read a PACKAGE NAME out of a checker_command. This derives what the
    # kernel was actually asked to check, from the certificate itself.
    # ADR-1300: a blank `C` (CAS, ADR-0603 row 3) cell in the Spivak spine
    # table is a failure, not a claim -- chapter 20 read "open" while
    # `taylor.rs` shipped Taylor's theorem with the Lagrange remainder.
    python3 scripts/check-spivak-cas-column.py
    python3 -m unittest scripts.tests.test_check_spivak_cas_column
    python3 scripts/check-cas-substance.py
    python3 -m unittest scripts.tests.test_check_cas_substance
    # W1-13: the ADR-0601 SS2 `cas-internal` residue itself -- distinct from
    # cas-substance above (which floors what the 14 kernel-reconstructed
    # facts' kernel obligations ESTABLISH). This floors which facts are
    # kernel-reconstructed AT ALL: a fact regressing to cas-internal (or
    # vanishing) is refused, a new cas-internal fact is not.
    python3 scripts/check-cas-internal-residue.py --report
    python3 -m unittest scripts.tests.test_check_cas_internal_residue
    # Math-department file 13, Next Ten item 10 (first half): a per-function
    # trust registry for axeyum-cas -- distinct from cas-internal-residue
    # above (which floors the fact ledger's classification). This floors the
    # SOURCE's own pub fn surface: whether each function's return type
    # carries a certificate at all.
    python3 scripts/check-cas-trust-registry.py --report
    python3 -m unittest scripts.tests.test_check_cas_trust_registry
    python3 -m unittest scripts.tests.test_settled_fact_statements
    python3 -m unittest scripts.tests.test_check_draw7_frozen_families
    python3 scripts/check-settled-fact-statements.py
    # S1 of the trusted-library safety roadmap (ADR-0763): the exit criterion,
    # executed rather than asserted. Constructs swapped binders, a changed
    # constant, an altered relation, source drift, and -- replayed from the
    # real damaged forms in `e79804fdd` -- an upstream statement overwritten
    # with our own `render_lean` output, then restores the ledger byte-exactly.
    # Records WHICH gate rejected each, because "something failed" is not
    # evidence that the right thing failed. ~2s, no cargo.
    python3 scripts/check-statement-identity-mutations.py
    # S0 of the trusted-library safety roadmap (ADR-0746): the facts x
    # protections census. Refuses on the committed matrix going stale -- a
    # fact or checker_command silently added, removed, or downgraded from an
    # own-subject checker to a shared prelude sweep -- and on a classifier
    # that has stopped discriminating, which would otherwise report a
    # cheerful zero for a whole protection column.
    python3 scripts/gen-safety-matrix.py --check
    # S3 of the same roadmap (ADR-0752): the retained semantic-control
    # fixture pack -- known-false, known-vacuous and known-valid statements,
    # each a real defect this repository produced or the valid control one
    # line away from it, plus statement mutations and the in-tree numerics
    # scripts. ZERO EXECUTED CASES IS ALWAYS FAILURE. A mutation that is not
    # falsified because it is also true is classified, never failed.
    python3 scripts/check-semantic-control-fixtures.py --check
    # D3 of the definition-discovery-efficiency roadmap (ADR-0890): the
    # counterexample-first falsification screen, one arrow upstream of S3 --
    # definitions and theorem PROPOSALS rather than settled statements. 2
    # retained false statements (new relative to S3's 13), 6 definitions
    # checked against independent references with a mutation each (verified
    # to move an observation, not silently accepted if vacuous), 2 review
    # obligations for unexecutable CReal constructions, and dispatch
    # ordering enforced via git merge-base --is-ancestor when both commits
    # resolve.
    python3 scripts/check-falsification-screen.py --check
    # ...and its controls: 17 guards, each verified to kill EXACTLY ONE test
    # when gutted in a scratch copy.
    python3 -m unittest scripts.tests.test_falsification_screen
    # ...and the mutation-kill verification ITSELF (registered 2026-08-31,
    # absence-and-orphans lane): it existed and passed since this section was
    # written but nothing had ever invoked it -- "a control nobody invokes
    # cannot fail, so it is not a control." ~2s, no cargo.
    ./scripts/tests/test-falsification-screen-mutation-verify.sh
    # S2 of the same roadmap: the universal trust and circularity audit, read
    # from the admitted term rather than from authored `depends_on`. Every
    # kernel-route settled fact is checked against its own transitive
    # `Kernel::declaration_dependencies` closure -- 1,953 subjects, against the
    # S0 census's measured `circularity 38 / 2117`. Four guards looking at four
    # different things, so target injection, indirect target injection, axiom
    # insertion and population deletion cannot all reject through one path.
    python3 scripts/check-trust-closure.py --quiet
    # ...and its controls: 17 cases, then 15 guard deletions each required to
    # kill EXACTLY ONE.
    bash scripts/tests/test-trust-closure.sh
    # S6 of the same roadmap (ADR-0785): a fault-injectable two-phase-commit
    # transaction over a fixture ledger (facts/pins/graph/dashboards/receipts).
    # Runs a crash-boundary sweep -- one full transaction is executed to count
    # every low-level write op (26, currently), then re-run once per op with a
    # fault injected at that exact op, and the recovered state must match
    # byte-for-byte OLD or NEW, never neither -- plus four staleness fixtures
    # (receipt pointer, source, graph, checker version) each rejecting with
    # its OWN exception class, a fresh-read demonstration, and an
    # idempotent-replay check. Fails closed on an empty sweep or fixture set.
    python3 scripts/check-credit-transaction.py
    # ...its own test suite (27 tests) and mutation table: 9 guard deletions
    # in a SCRATCH COPY, each required to kill EXACTLY its own canary.
    python3 scripts/tests/test-credit-transaction.py
    bash scripts/tests/test-credit-transaction-mutations.sh
    # ADR-0790: 15 of the identity classes above have BOTH members registered
    # as ledger facts -- 15 propositions counted as 2,121 proved facts twice.
    # Facts are never deleted (ADR-0542); one member of each pair carries a
    # new `equivalent_to` edge to a canonical survivor. This gate rejects any
    # NEW byte-identically-typed pair that enters the ledger unlabeled.
    python3 scripts/check-proposition-duplication.py
    # ...and its controls: 9 cases, then 8 guard deletions each required to
    # kill EXACTLY ONE.
    bash scripts/tests/test-proposition-duplication.sh
    # ADR-1170: the same defect one level up, in the KERNEL environment rather
    # than the ledger -- two declarations whose admitted types are identical up
    # to binder naming, which is what a lane that could not find an existing
    # lemma produces. This checker existed from 2026-08-27 and `check.sh`
    # registered only its UNIT TESTS, so it ran only when a human typed it;
    # its first automatic run found five unadjudicated groups, one of them a
    # real re-derivation of right-distributivity over Int. ~110s (shells out to
    # `cargo run --release --example shape_search -- --duplicates`).
    python3 scripts/check-shape-duplicates.py
    # ...AND THE COMPANION GATE FOR THE CASE THE SHAPE DETECTOR IS STRUCTURALLY
    # BLIND TO (ADR-1320). `shape_search --duplicates` groups declarations by
    # admitted TYPE. Every `CReal`-valued CONSTANT has the identical type `CReal`,
    # so a type-based detector over constants is either useless (one group holding
    # `zero`, `one`, `e`, `cosOne`, `sinOne`, ...) or blind -- measured 2026-08-31,
    # 15 duplicate groups and not one containing a constant. And `CReal.Equiv` is
    # undecidable, so there is no mechanical "is this the same real" test either.
    # So a second `CReal.pi` would land with nothing objecting. This gate derives
    # the constant population from `kernel_declaration_projection` (16 nullary
    # data-valued definitions over CReal/Complex/Int/Rat; the `Prop`-valued
    # exclusion is derived from the head symbol's own result sort, not exempted)
    # and requires each one to be adjudicated in
    # `artifacts/trust-closure/canonical-constants.tsv`, in BOTH directions.
    # ~40s: shells out to `cargo run --release --example
    # kernel_declaration_projection`.
    python3 scripts/check-constant-canonicity.py
    python3 -m unittest scripts.tests.test_check_constant_canonicity
    # ADR-1050: the eight L0 gates must be wired to something that runs
    # on its own. Measured 2026-08-31 they were in NO automated context
    # -- not ci.yml, not hooks/pre-push, not scripts/local-ci.sh.
    python3 scripts/check-l0-gate-enforcement.py
    # ...and its controls: 11 cases, six guards each required to kill
    # the test that names it.
    python3 -m unittest scripts.tests.test_l0_gate_enforcement
    # ADR-0810: the above engine wired into the REAL write set (measured, not
    # assumed) -- artifacts/facts/<id>.json, the pins manifest, and the
    # safety-matrix TSV/MD, all full rebuilds reusing validate-facts.py's
    # validate_one, check-settled-fact-statements.py's rewrite(), and
    # gen-safety-matrix.py's classify/render/run_controls UNMODIFIED. Crash
    # sweep over the real 23 write ops, four staleness dimensions against real
    # paths, idempotent replay. Never touches the live ledger -- every check
    # runs against a scratch copy it builds itself.
    python3 scripts/check-credit-transaction-ledger.py
    # ...its own test suite (22 tests) and mutation table: 9 guards this
    # wrapper owns, each required to kill EXACTLY its own canary.
    python3 scripts/tests/test-credit-transaction-ledger.py
    bash scripts/tests/test-credit-transaction-ledger-mutations.sh
    # An `ml430` mirror's top-level `statement` is a prose reference BY NAME, so
    # the Mathlib proposition lives only in `formal.statement`. Nineteen had it
    # overwritten with our own `render_lean` output, and the mirror claim -- "we
    # proved what Mathlib states" -- then could not be checked from the fact at
    # all. Exact, not a token screen: 362 of 374 mirrors are hash-pinned by a
    # preregistered catalog.
    python3 scripts/check-mirror-statement-fidelity.py
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
    # These controls were introduced with their tools but not registered in any
    # gate. Keep both proof-free adapter generation and external certificate
    # replay falsifiable before the reachability ratchet measures the tree.
    python3 -m unittest scripts.tests.test_gen_statement_adapters
    python3 -m unittest scripts.tests.test_check_external_certificate
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
    # The landmark count beside the raw total (W1-4, ADR-1600): proved AND a
    # curated (non-`[generated]`) title, against a committed baseline.
    python3 -m unittest scripts.tests.test_count_landmark_facts
    python3 scripts/count-landmark-facts.py --check
    # How much of the ledger CHARACTERISES itself (ADR-1605): a three-way split
    # (curated / [generated] / "Mathlib v4.30 source proposition"), a
    # title-vs-statement agreement guard, and a per-fragment RATCHET on the
    # curated count rather than an exact pin.
    python3 -m unittest scripts.tests.test_check_fact_characterisation
    python3 scripts/check-fact-characterisation.py --check
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
    # Controls for the cargo slot semaphore (scripts/cargo-serialized.sh): a job
    # must take any slot that frees rather than queue on slot 1. Private lock
    # files, ~15 s.
    scripts/tests/test-cargo-serialized-slots.sh
    # Controls for `check.sh`'s `py_native_installed` host guard: it must say
    # "absent" for a `.venv` whose site-packages is empty (the shape that
    # actually exists in a fresh lane worktree, and the one `[ -d .venv ]` gets
    # wrong) AND "present" for an installed package -- a guard that always
    # declines would silently drop two real steps on every host. Also pins the
    # listing invariant: `AXEYUM_CHECK_LIST=1` must enumerate all four binomial
    # steps regardless of host state, because check-aggregate-scope.sh compares
    # that listing against this file.
    scripts/tests/test-check-sh-py-native-guard.sh
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
    # Controls for the gate-ADMISSION mechanism (2026-08-27). The push battery
    # was starved because `scripts/cargo-serialized.sh` bounds MEMORY and
    # nothing bounded CPU, and because pre-push, check.sh and this file called
    # the wrapper zero times between them. Twelve cases, each paired with the
    # input that makes it fail -- notably a REAL deadlock probe: every slot is
    # held, and the re-entrant job must complete while the non-re-entrant one
    # must report 75. Without that second half the first would pass on a host
    # where slots were never contended. Guards mutation-verified individually
    # by scripts/tests/mutate-gate-admission.sh.
    scripts/tests/test-gate-admission-controls.sh
    # ...and the mutation harness over them, in the gate rather than by hand:
    # a guard that stops discriminating does so silently, and the suite above
    # stays green either way. It mutates a four-file scratch copy, never the
    # checkout -- these are shell scripts, so an in-place mutant would be run
    # by any lane invoking a gate during the window.
    scripts/tests/mutate-gate-admission.sh
    scripts/tests/test-new-fact-controls.sh
    # Controls for `kernel-stack-envelope` below. Six cases: an outgrown budget,
    # a budget so large it cannot fail, an empty ledger, a missing pin file, a
    # probe usage error that must NOT be read as "needs more stack", and the
    # committed pins passing. Each of the checker's five guards was mutated
    # individually in a scratch tree and kills exactly one control.
    scripts/tests/test-kernel-stack-envelope.sh
    # Controls for `deep-stack-call-sites` below. Six cases against a scratch
    # search root (`AXEYUM_DEEP_STACK_SEARCH_ROOT`): the committed tree passes,
    # a fresh unwrapped call is RED, the same call one hop through a same-file
    # helper is still RED, both `on_a_deep_stack` shapes (inline closure and
    # named `_body` function) are GREEN, and an empty search root is exit 2
    # rather than a vacuous pass.
    scripts/tests/test-deep-stack-call-sites.sh
    scripts/tests/test-lane-commit.sh
    scripts/tests/test-lane-merge-resolve.sh
    scripts/tests/test-recount-pinned-inventory.sh
    scripts/tests/test-open-frontier-axiom-freeness.sh
    # The lane stamp must PARSE as a git trailer, not merely appear as text:
    # `%(trailers:key=Agent,valueonly)` is the query every attribution check
    # runs, and two commits carried the text without parsing.
    scripts/tests/test-commit-msg-trailer.sh
    python3 -m unittest scripts.tests.test_lane_merge_additive
    # `--to <branch>`: the range, the cost estimate and the fast-forward check
    # must follow the ref being PUSHED, not the current branch's remote copy.
    # Against a stale `origin/<branch>` the same doc-only landing reads FULL
    # BATTERY instead of FREE, and an estimate that errs expensive gets ignored.
    scripts/tests/test-lane-push-target.sh
    # The pre-push compile step must carry --all-targets: without it,
    # examples/ and tests/ are never compiled and the hook's
    # "pushed SHA compiles" line is false for half the tree.
    scripts/tests/test-prepush-checks-all-targets.sh
    # ...and the L0 block must still run the gates it lists, one of which is
    # the partition-edge ratchet (ADR-1550).
    scripts/tests/test-prepush-l0-gates.sh
    scripts/tests/test-prepare-prepush-worktree.sh
    scripts/tests/test-check-lean-golden-pins.sh
    # ...and the ratchet that makes the two lines above impossible to forget.
    # Both were written, both pass, and one was invoked by NOTHING for a day,
    # because registering a control is a manual step separate from writing it.
    # A control nobody runs cannot fail, so it is not a control.
    scripts/check-control-registration.sh
    # G2 measured 2026-08-30: 3 of 4 hyphenated numeric-control scripts under
    # scripts/tests/ are already reachable via 7 facts' checker_command, but
    # this one -- the Nat.countRange bijection/CRT numeric control -- was cited
    # by nothing at all. Invoked directly by path.
    python3 scripts/tests/check-countrange-bijection-numerics.py
    # A `#[test]` separated from its function, or duplicated onto one. A splice
    # merge did exactly that on 2026-08-29 and ONE TEST SILENTLY NEVER RAN,
    # with `cargo test`'s count healthy the whole time. Four lanes repaired it.
    python3 scripts/check-test-attribute-integrity.py
    # ...and its controls, each mutation-verified, including the false-positive
    # case (multi-line `#[allow]`) that the gate's first draft failed.
    scripts/tests/test-check-test-attribute-integrity.sh
    # The creal prelude-build ratio gate's controls. Registered in
    # `scripts/check.sh` only until 2026-08-30, so the PREFERRED gate did not
    # run them -- found by `check-aggregate-scope.sh` once its normalizer
    # stopped manufacturing phantom divergences that buried the real one.
    scripts/tests/test-creal-prelude-build-ratio.sh
    # Controls for `check-aggregate-scope.sh`'s own step normalizer, which
    # reported ONE script as TWO divergences (`python3 ./scripts/x.py` vs
    # `python3 scripts/x.py`) because its `./` strip was anchored at line
    # start. 4 of 13 reported divergences were that artifact. Five guards,
    # each mutation-verified to kill exactly one control, plus two negative
    # controls so a normalizer returning "" cannot satisfy the suite.
    scripts/tests/test-check-aggregate-scope.sh
    # ...and its FAILURE-PATH controls, which it had none of: the
    # fail-on-new-divergence guard was deletable with all five green. 13
    # scenarios on a synthetic tree; every guard mutation-verified.
    python3 -m unittest scripts.tests.test_check_aggregate_scope
    # Post-merge hygiene: conflict markers in tracked files, duplicate ADR
    # numbers, stale generated files. ~2s. Each guard is a defect that reached a
    # commit because merges outnumber full-gate runs; positive-controlled, and a
    # fourth guard was RETIRED rather than shipped after it matched a pin
    # declaration quoted in a doc comment.
    scripts/check-merge-hygiene.sh
    # ...and its controls, which it shipped WITHOUT -- the 2026-08-30 audit's
    # first survivor. Ten scenarios drive the shipped script against a throwaway
    # git tree via `AXEYUM_MERGE_HYGIENE_ROOT`; every guard mutation-verified.
    python3 -m unittest scripts.tests.test_check_merge_hygiene
    # The registration gate's OWN controls -- it had none, which is the joke
    # this file exists to stop being. 15 cases, each mutation-verified.
    scripts/tests/test-check-control-registration.sh
    # Controls for `scripts/check-fast.sh`, tier-0 of this gate. Five guards,
    # each mutation-verified to kill exactly one control, plus a false-positive
    # control that survives all five. The load-bearing guard: an over-budget
    # step is DEFERRED, a third outcome, and never folds into `ok`.
    scripts/tests/test-check-fast.sh
    # Controls for `scripts/brief-step0.py`, the dispatcher-side retrieval
    # step. Nine guards, each mutation-verified to kill exactly one control,
    # plus a false-positive control that survives all nine. The load-bearing
    # guard: a snapshot that cannot retrieve the built-in probe is
    # UNANSWERABLE, never a source of ABSENT verdicts.
    scripts/tests/test-brief-step0.sh
    # ...and the catch-all that makes registration DERIVED rather than
    # remembered. 188 of 382 python control suites were named by no caller at
    # all on 2026-08-27 -- 49%, pinned as a floor nobody had chosen. This runs
    # every `scripts/tests/test_*.py` no step names, minus the reasoned
    # exclusions in `scripts/control-optout.tsv`, and fails both on a suite that
    # FAILS and on one that collects ZERO tests.
    scripts/run-python-controls.py
    # `grep -q` in a pipeline under pipefail, and `$?` read after a pipeline:
    # both print a wrong answer while exiting 0, and both shipped here.
    scripts/check-shell-antipatterns.sh
    # ...and its controls. The gate had none and was RED on a false positive:
    # it read the second bar of `||` as a pipe. 12 cases; each of the two
    # mutations kills a disjoint set.
    scripts/tests/test-check-shell-antipatterns.sh
    # ...and its SCOPE controls, a separate question that had none. The gate
    # scanned `git ls-files '*.sh'`, so neither hook was read and both violated.
    # Nine hermetic scenarios; every guard mutation-verified.
    python3 -m unittest scripts.tests.test_check_shell_antipatterns_scope
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

# L1 phase G0 (docs/plan/graph-directed-library-roadmap-2026-08-30.md): the
# Mathlib module-import baseline receipt. Re-parses the pinned mathlib4
# checkout TWICE (so "two runs reproduce the receipt" is checked mechanically
# on every invocation, not just asserted once) and fails naming SOURCE_DRIFT
# or PARSER_DRIFT independently -- see scripts/check-module-baseline.py's
# header. Vendors no Mathlib checkout; reads whatever
# scripts/provision-lean-import-toolchain.sh provisioned.
module-baseline:
    python3 scripts/check-module-baseline.py

module-baseline-controls:
    python3 scripts/tests/test-module-baseline.py
    scripts/tests/test-module-baseline-mutations.sh

autogenesis-knowledge-controls:
    python3 -m unittest scripts.tests.test_validate_autogenesis_knowledge
    python3 -m unittest scripts.tests.test_gen_autogenesis_knowledge_coverage
    python3 scripts/validate-autogenesis-knowledge.py
    scripts/check-autogenesis-knowledge-controls.sh

# ADR-0553. No artifact may declare a dependency on a repository this project
# does not own. `--self-test` runs first and deliberately: it drives every rule
# over a synthetic violation and fails if any rule does NOT fire, so the green
# zero the scan prints afterwards is a measurement rather than a no-op.
external-coupling:
    python3 -m unittest scripts.tests.test_check_external_coupling
    python3 scripts/check-external-coupling.py --self-test
    python3 scripts/check-external-coupling.py

# Controls for scripts/check-lane-turn.sh: whether a lane's own working tree is
# safe to act on, and whether a FAIL is this lane's own regression or
# pre-existing/another-lane's-in-flight work. Wired into `check` in
# scripts/check.sh already (`lane-turn-controls`); was missing here.
lane-turn-controls:
    ./scripts/tests/test-check-lane-turn.sh

# `artifacts/correspondences/*.json`: claims that two facts are the same
# mathematical idea, kept structurally distinct from `depends_on` (a proof
# dependency). Wired into `check` in scripts/check.sh already
# (`correspondences`/`correspondences-tests`); was missing here.
correspondences:
    python3 scripts/validate-correspondences.py
    python3 -m unittest scripts.tests.test_validate_correspondences

# Owner-lane freshness checks for derived Autogenesis knowledge snapshots.
# These are intentionally not part of `check`: construction lanes may advance
# the live theorem/fact sources while the additive sidecars lag safely. Run this
# before committing a knowledge-overlay refresh.
autogenesis-knowledge-derived-freshness:
    python3 scripts/gen-autogenesis-knowledge-coverage.py --check
    python3 scripts/gen-autogenesis-kernel-dependency-projection.py --check
    python3 scripts/gen-autogenesis-kernel-lemma-search-index.py --check
    python3 scripts/gen-autogenesis-kernel-semantic-review-queue.py --check
    python3 scripts/gen-autogenesis-obstruction-projection.py --check
    python3 scripts/gen-autogenesis-capability-candidate-demand.py --check
    python3 scripts/gen-autogenesis-transport-projection.py --check
    python3 scripts/gen-autogenesis-scheduler-observations.py --check
    python3 scripts/gen-autogenesis-capability-gap-projection.py --check
    python3 scripts/gen-autogenesis-concept-coverage-projection.py --check
    python3 scripts/gen-autogenesis-producer-outcome-observations.py --check
    python3 scripts/gen-autogenesis-producer-evaluation-frontier.py --check
    python3 scripts/gen-autogenesis-producer-evaluation-protocol.py --check
    python3 scripts/gen-autogenesis-open-lemma-candidate-ranking.py --check

autogenesis-open-lemma-candidate-ranking:
    python3 -m unittest scripts.tests.test_gen_autogenesis_open_lemma_candidate_ranking
    python3 scripts/gen-autogenesis-open-lemma-candidate-ranking.py --check

autogenesis-rewrite-support-ranking:
    python3 -m unittest scripts.tests.test_gen_autogenesis_rewrite_support_ranking
    python3 scripts/gen-autogenesis-rewrite-support-ranking.py --check

autogenesis-ranked-proposition-census:
    cargo build -q -p axeyum-lean-import --example proposition_compatibility_audit
    python3 scripts/gen-autogenesis-ranked-proposition-census.py --ranking artifacts/autogenesis/open-lemma-candidate-ranking-pre-reconciliation-v1.json --check
    python3 scripts/gen-autogenesis-ranked-proposition-census.py --ranking artifacts/autogenesis/open-lemma-candidate-ranking-post-reconciliation-v1.json --output artifacts/autogenesis/open-ranked-proposition-census-v2.json --allow-population-subset --check

autogenesis-open-fixed-palette-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/open-ranked-proposition-census-v2.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/open-fixed-palette-census-v2.json --check

autogenesis-open-ranked-application-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette scripts.tests.test_gen_autogenesis_open_lemma_candidate_ranking
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/open-ranked-proposition-census-v2.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --ranking artifacts/autogenesis/open-lemma-candidate-ranking-v1.json --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/open-ranked-application-census-v1.json --check

autogenesis-open-ranked-transport-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette scripts.tests.test_gen_autogenesis_open_lemma_candidate_ranking
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/open-ranked-proposition-census-v2.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --ranking artifacts/autogenesis/open-lemma-candidate-ranking-v1.json --transport-native-candidates --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/open-ranked-transport-application-census-v1.json --check

autogenesis-open-ranked-transport-induction-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette scripts.tests.test_gen_autogenesis_rewrite_support_ranking
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/open-ranked-proposition-census-v2.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --ranking artifacts/autogenesis/open-lemma-rewrite-support-ranking-v1.json --transport-native-candidates --retrieved-induction --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/open-ranked-transport-induction-census-v1.json --check

autogenesis-retrieved-induction-obstructions:
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_retrieved_induction_obstructions
    python3 scripts/gen-autogenesis-retrieved-induction-obstructions.py --check

autogenesis-retrieved-induction-type-slice:
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_retrieved_induction_type_slice_input scripts.tests.test_check_autogenesis_retrieved_induction_type_slice_replay
    python3 scripts/gen-autogenesis-retrieved-induction-type-slice-input.py --check
    python3 scripts/check-autogenesis-retrieved-induction-type-slice-replay.py

autogenesis-retrieved-induction-type-slice-reproduce:
    cargo run -q -p axeyum-lean-import --example type_slice_replay -- --streams /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --mapping artifacts/autogenesis/retrieved-induction-type-slice-input-v1.json --output artifacts/autogenesis/retrieved-induction-type-slice-replay-v1.json --auto-param-binders-v3
    python3 scripts/check-autogenesis-retrieved-induction-type-slice-replay.py --source-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1

autogenesis-semantic-contract-demand:
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_semantic_contract_demand
    python3 scripts/gen-autogenesis-semantic-contract-demand.py --check

autogenesis-imported-implementation-demand:
    uv run --no-sync python -m unittest scripts.tests.test_check_autogenesis_imported_implementation_demand
    python3 scripts/check-autogenesis-imported-implementation-demand.py
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_imported_implementation_frontier
    python3 scripts/gen-autogenesis-imported-implementation-frontier.py --check
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_bit_observation_contract_slice
    python3 scripts/gen-autogenesis-bit-observation-contract-slice.py --check
    uv run --no-sync python -m unittest scripts.tests.test_check_autogenesis_imported_testbit_bitwise_candidate
    python3 scripts/check-autogenesis-imported-testbit-bitwise-candidate.py
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_imported_candidate_index
    python3 scripts/gen-autogenesis-imported-candidate-index.py --check

autogenesis-imported-implementation-demand-reproduce streams="/nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1":
    cargo run -q -p axeyum-lean-import --example imported_implementation_demand -- --streams "{{ streams }}" --replay artifacts/autogenesis/retrieved-induction-type-slice-replay-v1.json --output artifacts/autogenesis/imported-implementation-demand-v1.json
    python3 scripts/check-autogenesis-imported-implementation-demand.py
    python3 scripts/gen-autogenesis-imported-implementation-frontier.py
    python3 scripts/gen-autogenesis-bit-observation-contract-slice.py

autogenesis-imported-testbit-bitwise-candidate-replay stream="/nas3/data/axeyum/autogenesis/reference-packs/imported-candidates-v1/Nat.testBit_bitwise.ndjson":
    python3 scripts/check-autogenesis-imported-testbit-bitwise-candidate.py --verify-external
    cargo run -q -p axeyum-lean-import --example lean4export_import -- "{{ stream }}" Nat.testBit_bitwise
    cargo run -q -p axeyum-lean-import --example imported_candidate_descriptor -- "{{ stream }}" Nat.testBit_bitwise

autogenesis-imported-testbit-bitwise-statement source="/nas3/data/axeyum/autogenesis/reference-packs/imported-candidates-v1/Nat.testBit_bitwise.ndjson" output="/nas3/data/axeyum/autogenesis/reference-packs/imported-candidate-goals-v1/Nat.testBit_bitwise.statement.ndjson":
    cargo run -q -p axeyum-lean-import --example imported_candidate_statement_capsule -- "{{ source }}" Nat.testBit_bitwise "{{ output }}" --emit-refuted-diagnostic
    cargo run -q -p axeyum-lean-import --example statement_adapter_import -- "{{ output }}" Axeyum.Autogenesis.ImportedCandidateGoal
    python3 scripts/check-autogenesis-imported-testbit-bitwise-candidate.py --verify-external

autogenesis-bitwise-semantic-law-demand:
    cargo run -q -p axeyum-lean-kernel --example nat_testbit_bool_bridge
    uv run --no-sync python -m unittest scripts.tests.test_check_autogenesis_bitwise_semantic_law_demand scripts.tests.test_check_autogenesis_imported_definition_reflexivity_footprint scripts.tests.test_gen_autogenesis_bitwise_family_projection scripts.tests.test_check_autogenesis_bitwise_clean_family_capsule
    python3 scripts/check-autogenesis-bitwise-semantic-law-demand.py
    python3 scripts/check-autogenesis-imported-definition-reflexivity-footprint.py
    python3 scripts/gen-autogenesis-bitwise-family-projection.py --check
    python3 scripts/check-autogenesis-bitwise-clean-family-capsule.py

autogenesis-bitwise-clean-family-capsule-replay output="/tmp/axeyum-bitwise-clean-family-replay.ndjson":
    cargo run -q -p axeyum-lean-kernel --example nat_testbit_bool_bridge -- --export "{{ output }}"
    cargo run -q -p axeyum-lean-import --example lean4export_import -- "{{ output }}" Axeyum.Autogenesis.testBitBool_bitwiseAnd
    cargo run -q -p axeyum-lean-import --example lean4export_import -- "{{ output }}" Axeyum.Autogenesis.testBitBool_bitwiseOr
    cargo run -q -p axeyum-lean-import --example lean4export_import -- "{{ output }}" Axeyum.Autogenesis.testBitBool_bitwiseDifference
    python3 scripts/check-autogenesis-bitwise-clean-family-capsule.py --verify-external

autogenesis-imported-definition-reflexivity-footprint-replay stream="/nas3/data/axeyum/autogenesis/reference-packs/imported-candidates-v1/Nat.testBit_bitwise.ndjson":
    cargo run -q -p axeyum-lean-import --example imported_definition_reflexivity_footprint -- "{{ stream }}"

autogenesis-imported-definition-descriptor stream="/nas3/data/axeyum/autogenesis/reference-packs/imported-candidates-v1/Nat.testBit_bitwise.ndjson" name="Nat.testBit":
    cargo run -q -p axeyum-lean-import --example imported_definition_descriptor -- "{{ stream }}" "{{ name }}"

autogenesis-non-equality-terminal-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette scripts.tests.test_gen_autogenesis_non_equality_population
    python3 scripts/gen-autogenesis-non-equality-population.py --check
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/non-equality-terminal-population-v1.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --ranking artifacts/autogenesis/open-lemma-rewrite-support-ranking-v1.json --transport-native-candidates --retrieved-induction --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/non-equality-retrieved-induction-census-v1.json --check

autogenesis-open-modeq-family-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_open_fixed_palette
    uv run --no-sync python scripts/measure-autogenesis-open-fixed-palette.py --population artifacts/autogenesis/open-ranked-proposition-census-v2.json --must-decline-population artifacts/autogenesis/must-decline-mutations-v1.json --modeq-family --capsule-directory /nas3/data/axeyum/autogenesis/reference-packs/open-fixed-palette-v1 --output artifacts/autogenesis/open-modeq-family-census-v1.json --check

autogenesis-proposition-reconciliation-proposals:
    python3 -m unittest scripts.tests.test_prepare_autogenesis_fact_transaction
    python3 scripts/check-autogenesis-proposition-reconciliation-result.py

autogenesis-proposition-reconciliation-result:
    python3 -m unittest scripts.tests.test_prepare_autogenesis_fact_transaction scripts.tests.test_apply_autogenesis_fact_transaction
    python3 scripts/check-autogenesis-proposition-reconciliation-result.py

autogenesis-kernel-projection:
    python3 -m unittest scripts.tests.test_validate_autogenesis_kernel_projection
    python3 scripts/validate-autogenesis-kernel-dependency-projection.py
    python3 scripts/gen-autogenesis-kernel-dependency-projection.py --check

autogenesis-kernel-lemma-index:
    python3 -m unittest scripts.tests.test_gen_autogenesis_kernel_lemma_search_index
    python3 scripts/gen-autogenesis-kernel-lemma-search-index.py --check

# Requires the installed Python extension because the census runs the real
# Rust producer and independently admits every accepted term in the kernel.
autogenesis-bounded-application-census:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_bounded_application_census
    uv run --no-sync python scripts/gen-autogenesis-bounded-application-census.py --check

autogenesis-candidate-capsule-controls:
    uv run --no-sync python -m unittest python.tests.test_autogenesis_candidate_capsule

autogenesis-obstruction-projection:
    python3 -m unittest scripts.tests.test_validate_autogenesis_obstruction_projection
    python3 scripts/validate-autogenesis-obstruction-projection.py
    python3 scripts/gen-autogenesis-obstruction-projection.py --check

autogenesis-transport-projection:
    python3 -m unittest scripts.tests.test_validate_autogenesis_transport_projection
    python3 scripts/validate-autogenesis-transport-projection.py
    python3 scripts/gen-autogenesis-transport-projection.py --check

autogenesis-scheduler-observations:
    python3 scripts/gen-autogenesis-scheduler-observations.py --check

autogenesis-capability-gap:
    python3 -m unittest scripts.tests.test_validate_autogenesis_capability_gap_projection
    python3 scripts/validate-autogenesis-capability-gap-projection.py
    python3 scripts/gen-autogenesis-capability-gap-projection.py --check

autogenesis-capability-demand:
    python3 -m unittest scripts.tests.test_validate_autogenesis_capability_candidate_demand
    python3 scripts/validate-autogenesis-capability-candidate-demand.py

autogenesis-family-concepts:
    python3 -m unittest scripts.tests.test_validate_autogenesis_family_concept_crosswalk
    python3 scripts/validate-autogenesis-family-concept-crosswalk.py

autogenesis-concept-coverage:
    python3 -m unittest scripts.tests.test_validate_autogenesis_concept_coverage_projection
    python3 scripts/validate-autogenesis-concept-coverage-projection.py
    python3 scripts/gen-autogenesis-concept-coverage-projection.py --check

autogenesis-nat-modeq-selection:
    python3 -m unittest scripts.tests.test_validate_autogenesis_nat_modeq_capability_selection
    python3 scripts/validate-autogenesis-nat-modeq-capability-selection.py

autogenesis-producer-outcomes:
    python3 -m unittest scripts.tests.test_validate_autogenesis_producer_outcome_observations
    python3 scripts/validate-autogenesis-producer-outcome-observations.py
    python3 scripts/gen-autogenesis-producer-outcome-observations.py --check

autogenesis-producer-evaluation-frontier:
    python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_frontier
    python3 scripts/validate-autogenesis-producer-evaluation-frontier.py
    python3 scripts/gen-autogenesis-producer-evaluation-frontier.py --check

autogenesis-next-reusable-family:
    python3 -m unittest scripts.tests.test_gen_autogenesis_next_reusable_family_queue
    python3 scripts/gen-autogenesis-next-reusable-family-queue.py --check

autogenesis-binomial-arrow:
    uv run --no-sync python -m unittest scripts.tests.test_gen_autogenesis_binomial_arrow_capability
    uv run --no-sync python scripts/gen-autogenesis-binomial-arrow-capability.py --check
    uv run --no-sync python scripts/gen-autogenesis-binomial-connective-ranking.py --check
    uv run --no-sync python scripts/check-autogenesis-binomial-arrow-measurement.py

autogenesis-producer-evaluation-protocol:
    python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_protocol
    python3 scripts/validate-autogenesis-producer-evaluation-protocol.py
    python3 scripts/gen-autogenesis-producer-evaluation-protocol.py --check

autogenesis-producer-evaluation-result-contract:
    python3 -m unittest scripts.tests.test_validate_autogenesis_producer_evaluation_result

autogenesis-proposer-isolation:
    scripts/check-autogenesis-proposer-isolation.sh

autogenesis-induction-search:
    scripts/check-autogenesis-induction-search.sh

autogenesis-apply-search:
    scripts/check-autogenesis-apply-search.sh

autogenesis-result:
    python3 -m unittest scripts.tests.test_compare_autogenesis_authoritative_chains
    python3 -m unittest scripts.tests.test_run_autogenesis_authoritative_fact
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

# ADR-0717 S5: the kernel differential (Axeyum vs. pinned Lean) across all
# eight named subsystems -- conversion, universes, inductives, recursors,
# projections, literals, quotient, proof irrelevance. Each of 32 cases is
# authored TWICE independently (this crate's kernel term-builder API, and
# plain Lean surface syntax), because `Kernel::render_lean_module` only
# walks an already-admitted closure and cannot express the nearly-well-typed
# half of the corpus at all. `check-kernel-differential.py` runs the suite
# with `AXEYUM_REQUIRE_LEAN=1` and independently re-derives pass/fail from
# the parsed output via six guards (corpus non-empty, every subsystem
# non-empty, Lean actually invoked, zero P0, zero unexplained
# incompleteness, process exit status) rather than trusting the exit code
# alone; its own six guards are each mutation-verified to kill exactly one
# fixture (`test-kernel-differential-gate.sh`). `check-kernel-differential-
# mutants.py` ratchets the accompanying kernel-source mutation kill table
# (`artifacts/kernel-differential/mutant-kill-table.json`, ADR-0780): 4 of 8
# targeted guards killed outright, the other 4 survivals named and explained
# (or, for `inductives`, explicitly left open). Any P0 (Axeyum accepts what
# Lean rejects) preempts all other work per ADR-0717.
kernel-differential:
    bash scripts/tests/test-kernel-differential-gate.sh
    python3 scripts/check-kernel-differential.py
    python3 scripts/check-kernel-differential-mutants.py

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

# The number-theory certificate checkers: Pratt primality, compositeness,
# factorization and CRT (ADR-0745). Runs the adversarial fixture suite and
# asserts a RATCHETED NONZERO count -- a bare `cargo test --lib <filter>` exits
# 0 when the filter matches nothing, so the count is the discriminator.
#
# The mutation sweep that measures whether each guard is load-bearing is
# `scripts/tests/test-ntheory-certificate-guards.sh` (~23 incremental builds,
# ~50s uncontended). Registered here 2026-08-31 (absence-and-orphans lane):
# it existed and passed since this recipe was written but nothing had ever
# invoked it automatically -- "a control nobody invokes cannot fail, so it is
# not a control."
ntheory-certificates:
    ./scripts/check-ntheory-certificates.sh
    ./scripts/tests/test-ntheory-certificate-guards.sh

# The order-255 certified-moment proofs (squared_binomial_{,falling_}moment_...),
# kept OFF the per-iteration hot path via #[ignore] (~15 min each). The `check`
# chain runs this so CI coverage is unchanged; run it yourself only when you
# touch moment / squared-binomial / falling-factorial code.
moment-proofs:
    cargo test -p axeyum-cas --lib -- --ignored

# ADR-0581: how much STACK the kernel needs to build each prelude, re-derived
# and checked against `artifacts/kernel-stack-envelope.tsv`.
#
# The kernel's type checker recurses over the term with no bound, so a deep
# enough declaration exhausts the stack and the process ABORTS (SIGABRT, exit
# 134) -- a symptom this repository has three times mistaken for a broken tool
# or an absent declaration. `CReal.e` landing is what silently stopped
# `every_creal_declaration_is_checked_and_axiom_free`, the guard behind the
# axiom-freedom claim, from running at all. This turns that into a red gate
# with the number in it.
#
# RELEASE by default because a debug `cpoint` probe is ~63 s against ~8 s. The
# debug rows are the ones that match where `cargo test` runs; check them with
# `scripts/check-kernel-stack-envelope.sh --profile debug` (~4 min) when a
# kernel change plausibly deepened a proof term.
kernel-stack-envelope:
    ./scripts/check-kernel-stack-envelope.sh --check --profile release

# Static companion to `kernel-stack-envelope` above: that recipe re-measures
# how much stack each prelude NEEDS; this one catches a `#[test]` that reaches
# a deep-recursion build (`build_creal_prelude`, `build_complex_prelude`,
# `build_cpoint_prelude`, `build_creal_model_of_arith`) without an
# `on_a_deep_stack` guard anywhere on its local call path -- the actual
# regression shape that hit `creal_tests.rs`, `creal_model_tests.rs` and
# `prelude_cache_tests.rs` reactively in one session, plus a fourth,
# previously-undetected instance this script found on its first run.
deep-stack-call-sites:
    python3 scripts/check-deep-stack-call-sites.py

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

# Mocked-subprocess unit controls for the Tock log2 capture/cache-prepare
# investigation tooling (bench-results/verify-tock-log2-20260721/). The
# underlying capture/prepare/prove pipeline needs a QEMU/LLVM toolchain and is
# not re-run here -- these controls only guard the committed scripts' own
# logic (namespace mounts, staging/publish atomicity, cache probing) via
# subprocess mocks, so they run everywhere `python3 -m unittest` does. The
# `prove-tock-log2*` generations are excluded: their frozen registration pins
# a SHA-256 of `crates/axeyum-verify/tests/tock_log2_external.rs` that has
# drifted since the freeze, so all four currently fail closed.
tock-log2-maestro-controls:
    python3 -m unittest scripts.tests.test_capture_tock_log2
    python3 -m unittest scripts.tests.test_capture_tock_log2_v2
    python3 -m unittest scripts.tests.test_capture_tock_log2_v3
    python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v2
    python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v3
    python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v4
    python3 -m unittest scripts.tests.test_prepare_tock_log2_cache_v5

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
    # Three doc claims of the shape "`X` is not proved/built here" were FALSE
    # against the actual construction on 2026-08-22/23 -- `declare_X` sat
    # later in the same file (or same Rust module) and was wired into the
    # build sequence. See the script's own docstring for the crisp sub-shape
    # it catches and what it deliberately does not.
    python3 -m unittest scripts.tests.test_check_stale_negative_claims
    python3 scripts/check-stale-negative-claims.py
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
    python3 scripts/validate-producer-contracts.py
    python3 -m unittest scripts.tests.test_validate_producer_contracts
    python3 scripts/validate-producer-contract-declines.py
    python3 -m unittest scripts.tests.test_validate_producer_contract_declines
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
    # `creal`'s STEPS table is generated from a measurement of its own source
    # (crates/axeyum-lean-kernel/src/creal/steps_generated.rs). --check: stale;
    # --strict: the measured graph contradicts it; --self-check: the positive
    # control. Pure Python, ~1.1s.
    python3 scripts/creal-declare-deps.py --check --strict --self-check
    # The Python binding's generated prelude field table. Registered in no
    # gate until 2026-09-01, which is how it reached main stale: the ADR-1512
    # registry split deleted 69 of creal's 606 names from the Python surface
    # and nothing noticed. ~0.3s, pure Python.
    # Its own controls: path-qualified registry fields used to be silently
    # skipped before classification ever ran (ADR-1613's live gap).
    python3 -m unittest scripts.tests.test_gen_py_prelude_fields
    python3 scripts/gen-py-prelude-fields.py --check
    # The ADR-1512 migration's consumer scan: it refuses a move that would
    # break a file outside the kernel crate. Mutation-verified.
    python3 -m unittest scripts.tests.test_creal_migrate_registry
    # ADR-0601 SS3: the import backlog as a produced artifact, not a bare
    # count. docs/autogenesis/289-import-backlog-artifact.md.
    python3 -m unittest scripts.tests.test_gen_import_backlog
    python3 scripts/gen-import-backlog.py --check
    # docs/plan/status/141-ledger-6-backlog.md's closing paragraph: the full
    # diff of the kernel's theorem inventory against artifacts/facts/'s
    # registered names had never been measured. Permanent gate, not a
    # one-off count. docs/autogenesis/297-ledger-coverage-gate.md.
    python3 -m unittest scripts.tests.test_gen_ledger_coverage
    python3 scripts/gen-ledger-coverage.py --check
    # The generated half of that ledger: `--audit` keeps every mechanically
    # written fact distinguishable from a curated one and refuses any whose
    # checker_command cannot fail.
    # docs/autogenesis/298-mechanical-fact-registration.md.
    python3 -m unittest scripts.tests.test_gen_kernel_facts
    python3 scripts/gen-kernel-facts.py --audit
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

# The 2026-08-29 orphan-script audit (docs/plan/status/308-orphan-script-audit.md)
# found these three well-formed, general-purpose checks with no caller anywhere.
# Registered rather than deleted: each ran clean when tested standing it up.
gate-step-timeout:
    ./scripts/check-gate-step-timeout.sh

shared-index:
    ./scripts/check-shared-index.sh

sos-negative-controls:
    ./scripts/check-sos-negative-controls.sh

evidence-portability:
    ./scripts/check-evidence-portability.sh

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

# Make an absence claim in prose EXPIRE (ADR-0611). A doc carries
# `<!-- absent: CReal.foo -->` and this fails the moment that declaration
# exists in `kernel.environment()`; `<!-- was-absent: ... -->` fails in the
# other direction, when a resolution record starts pointing at nothing.
#
# The authority is `kernel_declaration_projection --release`, which builds
# every constructed prelude (~20 s once warm, a full release build cold) and
# must never be a committed snapshot -- the committed one held 1,644
# declarations against a live 1,861 on 2026-08-27, and a stale index reports a
# newly-landed declaration as still absent, which is the exact failure this
# gate exists to catch.
#
# That cost was the stated reason this recipe was "deliberately NOT part of
# `check`". REVERSED 2026-08-31 (ADR-1190), because the consequence was worse
# than the cost: `scripts/check.sh` registered only
# `absence-claims-tests` -- the unit tests, which drive synthetic fixtures --
# so the 39 markers in the real tree were checked against the kernel only when
# a human typed this recipe by hand. That is ADR-1170's
# checker-that-cannot-fail defect exactly, and it was sitting one registration
# below ADR-1170's own retrospective in `check.sh`. Both gates run the checker
# now; ~20 s warm is a small price beside a whole expiry mechanism nothing
# invoked.
#
# `--list` prints the adoption worklist: every claim site, annotated or bare.
absence-claims:
    python3 scripts/check-absence-claims.py

# ADR-1215: is any kernel declaration attributed to the WRONG curriculum node?
#
# The residual counter in `measure-curriculum-kernel-coverage.py` catches a
# declaration attributed to NOTHING. It cannot catch one attributed to the
# wrong REAL bucket, because that declaration is attributed, counted, and
# plausible -- and the node's pinned `kernel_decls` stays unchanged and wrong.
# That happened twice in two days: ADR-1140 (`linear-algebra` matched the
# literal `det2|det3`, so 22 general-`n` determinant declarations fell into
# `rationals`) and ADR-1205 (`number-theory`'s only Gauss alternative was the
# literal `gauss_fold_injective`, so 29 quadratic-residue declarations fell
# into `naturals`/`integers`). Both were found by a lane told to check by
# hand; nothing in either gate would have.
#
# THE CHECKER runs here, not only its tests -- registering a suite of
# synthetic fixtures while the real subject goes unexamined is ADR-1170's and
# ADR-1190's defect, twice over, and this would have been the third.
# `--require-pin` refuses a missing `artifacts/curriculum/
# bucket-cohesion-pin.tsv` rather than reading it as "nothing to report".
curriculum-bucket-cohesion:
    python3 scripts/measure-curriculum-kernel-coverage.py --run-projection --require-pin

# Its controls, including the two historical incidents replayed against a
# slice of the REAL projection with the pattern tables `git show`n at
# `d2bb38a1e^` and `bd382566b^`, each required to fire and to name the
# affected declarations, plus the same-slice green control that makes those
# mean something. Mutation sweep:
#   python3 scripts/tests/mutation_controls.py curriculum-bucket-cohesion
curriculum-bucket-cohesion-controls:
    python3 -m unittest scripts.tests.test_curriculum_bucket_cohesion

# The controls for that gate, plus the seeded-claim demonstration: it rewrites
# `was-absent:` to `absent:` in a SCRATCH copy of the four seeded records --
# restoring each document to the state it was actually in the day it was
# written -- and requires the gate to report all eight declarations EXPIRED,
# with the unrewritten green control in the same run. A gate that always reds
# is the same as one that never does, so both halves are required.
absence-claims-controls:
    python3 -m unittest scripts.tests.test_check_absence_claims
    cargo run --release -q -p axeyum-lean-kernel --example kernel_declaration_projection \
      > "${TMPDIR:-/tmp}/absence-claims-projection.$USER.tsv"
    scripts/tests/demo-absence-expiry-seeds.sh "${TMPDIR:-/tmp}/absence-claims-projection.$USER.tsv"

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

# The Python binding gate (docs/python-2026-08/01-pyo3-maturin.md, S5).
#
# Six steps, and EVERY ONE PRINTS A COUNT, because a Python gate is the
# easiest place in this repository to build something that exits 0 while
# examining nothing: `pytest` prints "no tests ran" and exits 5, and a stub
# drift check with no floor reports "nothing differed" over an empty
# directory. `python/tests/conftest.py` fails a session that collected zero
# tests, and `tools/gen_native_stub.py --check` exits 1 when it compared zero
# stubs -- both verified by deleting the guard and watching exactly one test
# die. Read `PYTEST|collected=N` and `STUBS|compared=M`, not the exit status.
#
# `--no-sync`: the gate must not silently mutate `uv.lock` or the venv as a
# side effect of being run. `uv sync --dev` is the setup step, run once.
#
# TMPDIR: `maturin develop` writes a wheel there on every rebuild, and `/tmp`
# on this fleet is a 62 G RAM tmpfs already implicated in OOM kills
# (strand rule 5, docs/python-2026-08/README.md).

# Build the extension, run the Python tests, check stub drift, types and lint.
#
# `tools/check_types.py` runs Astral's `ty` over `python/axeyum/` against a
# budget of diagnostics that are NOT ours to fix (flat native-submodule stubs, a
# `setattr`-attached exception attribute, one pydantic-ai overload) -- each named
# in that file rather than silenced with an ignore comment, because an ignore is
# invisible in a count. It prints `TYPES|...|control=N` and fails when the
# control produced nothing, so a checker pointed at the wrong path cannot pass.
py-check:
    mkdir -p "${TMPDIR:-/data0/axeyum/scratch/py-tmp-$USER}"
    TMPDIR="${TMPDIR:-/data0/axeyum/scratch/py-tmp-$USER}" uv run --no-sync maturin develop
    uv run --no-sync pytest python/tests -q
    uv run --no-sync python tools/gen_native_stub.py --check
    uv run --no-sync python tools/check_stub_types.py
    uv run --no-sync python -m mypy.stubtest axeyum._native --ignore-missing-stub --ignore-positional-only --mypy-config-file tools/stubtest-mypy.ini --allowlist tools/stubtest-allowlist.txt --concise
    uv run --no-sync python tools/check_types.py
    uv run --no-sync ruff check python/ tools/
    uv run --no-sync ruff format --check python/ tools/

# The Python coverage ledger (docs/python-2026-08/09-coverage-plan.md).
#
# Two steps, unit suite FIRST, because the ledger's guards are what its census
# line rests on. `gen-python-coverage.py` derives every number from the
# workspace's own sources -- public items per crate, what `crates/axeyum-py`
# references with comments stripped, and the tier of every inventory row -- so
# a stale artifact means the surface moved, and regenerating is one command.
#
# Read `PYTHON_COVERAGE|...|tier_r_unreferenced=U|deferred=D`. `U > 0` is the
# normal state of an unfinished plan and is NOT a failure on its own; it
# becomes exit 1 the moment a document claims plan 02's tier-R exit criterion
# is met while the backlog says otherwise. A deferral with no reason is refused
# (exit 2): an unexplained deferral and a forgotten row are the same thing.
# Every guard is mutation-verified to kill exactly one test --
# `python3 scripts/tests/mutation_controls.py python-coverage` (11 anchors).
python-coverage:
    python3 -m unittest scripts.tests.test_gen_python_coverage
    python3 scripts/gen-python-coverage.py --check

# The tactic catalog gate (docs/python-2026-08/04-tactic-catalog.md, slice A3).
#
# Three steps. The unit suite is FIRST because the validator's own rules are
# what the census rests on, and the census is the rule that can fail on a
# healthy-looking file: fewer than two distinct precondition shapes means the
# catalog is a dispatch table, and a tactic with zero reach rows is a name
# rather than a capability. Every guard is mutation-verified to kill exactly
# one test -- `python3 scripts/tests/mutation_controls.py tactic-catalog`.
tactic-catalog-controls:
    python3 -m unittest scripts.tests.test_validate_tactic_catalog
    python3 scripts/validate-tactic-catalog.py
    python3 scripts/gen-tactic-catalog-census.py --check

# The agent-episode gate (docs/python-2026-08/03-agentic-layer.md, slice A1).
#
# `check-agent-episode.py` is the only thing between "a model ran" and "a model
# proved something": every episode is re-checked against the schema, its
# snapshot and proposal digests are re-hashed from disk, and the whole document
# is string-walked for held-out fact ids. Read `EPISODES|checked=N|ok=K|failed=M`,
# not the exit status -- though the exit status is nonzero when N is 0, because
# a check that checked nothing is not a pass.
#
# NO `--require-ancestor` here on purpose. The rule is real and tested, but most
# CI jobs check out at the default `fetch-depth: 1`, where the episode's commit
# object does not exist and every ancestor query answers "cannot resolve". A
# gate that is red on every CI run gets switched off. Default prints
# `EPISODE_WARN|...|rule=git-commit-ancestor`; pass the flag by hand in a full
# checkout to make it bite. Rationale: artifacts/episodes/README.md.

# Check every committed agent episode, then its own control suite.
episodes:
    python3 scripts/check-agent-episode.py artifacts/episodes --production-only
    python3 -m unittest scripts.tests.test_check_agent_episode

# Freshness-checked product populations plus the latest commit-bound runtime
# receipt. An ancestor receipt never becomes a current-head green claim.
product-health:
    python3 scripts/check-ci-receipt.py
    python3 -m unittest scripts.tests.test_gen_product_health
    python3 scripts/gen-product-health.py --check

# Imported Mathlib shortcut assay for the first three arithmetic Nat.ModEq
# targets. The external capsule is reproduction evidence; this offline gate
# checks the committed hash-bound result and its still-open fact population.
autogenesis-nat-modeq-imported-bridge-assay:
    python3 scripts/check-autogenesis-nat-modeq-imported-bridge-assay.py

# First empty-footprint behavior contract over the exact imported Nat.mod
# implementation. It records one conversion but grants no operation authority.
autogenesis-nat-modeq-remainder-contract:
    python3 scripts/check-autogenesis-nat-modeq-remainder-contract.py

# Expanded shared contract family: three independently admitted targets make
# the family operation-eligible, but no fact status changes at this gate.
autogenesis-nat-modeq-remainder-contract-v2:
    python3 scripts/check-autogenesis-nat-modeq-remainder-contract-v2.py

# Registered three-target operation; performs three fresh release-mode imports,
# transports, bounded constructions, and independent admissions.
autogenesis-nat-modeq-remainder-operation:
    python3 scripts/check-autogenesis-nat-modeq-remainder-operation.py

# The mobility census gate (docs/python-2026-08/07-mobility-census.md, slice A7).
#
# Two steps, and neither regenerates. `python -m axeyum.agent mobility --write`
# is what produces `artifacts/autogenesis/mobility-census-v1.json`; it needs the
# compiled kernel and the frozen `/nas3` exports, so it is run deliberately by a
# lane, never by a gate. A gate that regenerated its own subject would agree
# with itself whatever the tree said.
#
# `check-mobility-census.py` recomputes the catalog, nursery and export-index
# digests, string-walks the document for held-out ids, checks every fact id
# against `artifacts/facts/`, and voids a census whose `evaluable` is 0. Every
# guard is mutation-verified to kill exactly one test --
# `python3 scripts/tests/mutation_controls.py mobility-census`.
mobility-census:
    python3 scripts/check-mobility-census.py
    python3 -m unittest scripts.tests.test_check_mobility_census

# Regenerate the mobility census. Needs `uv sync --dev --extra agent`, a built
# `axeyum._native` (`uv run maturin develop`) and the frozen exports on this
# host. NOT part of `just check`.
mobility-census-regen:
    uv run --no-sync python -m axeyum.agent mobility --write

# The obstruction graph gate (docs/python-2026-08/06-obstruction-graph.md, slice
# A5; Autogenesis F3 in docs/autogenesis/243-knowledge-overlay-and-fill-plan.md).
#
# Four steps, and the regeneration is FIRST because everything after it rests on
# the artifact being derived rather than authored. The validator is separate
# from the generator on purpose: it recomputes every obstruction id from its own
# cluster key, re-hashes every evidence file from disk, and re-measures every
# `candidate_capability.exists` against the knowledge overlay, so a generator
# that was wrong does not get to certify itself. Every guard is mutation-verified
# to kill exactly one test -- `python3 scripts/tests/mutation_controls.py
# obstruction-graph` (26 anchors, 26 killed).
#
# Derive, validate and rank the typed-decline obstruction graph.
obstruction-graph:
    python3 scripts/gen-obstruction-graph.py --check
    python3 scripts/validate-obstruction-graph.py
    python3 scripts/gen-obstruction-dashboard.py --check
    python3 -m unittest scripts.tests.test_obstruction_graph

# L1 phase C0 -- the library-artifact record contract
# (docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md section C0,
# ADR-0800). Two independently-coded readers each recompute every digest and
# both transitive closures from a pack's own recorded fields and run five
# guards (MISSING against an external population registry, DUPLICATE,
# REORDERED, TRUNCATED, VALUE_EXPOSED against the type-only producer
# projection). `test-library-artifact-contract-mutations.sh` mutation-verifies
# all five guards in a scratch copy, one guard deletion killing exactly its
# own mutation's test.
library-artifact-contract:
    python3 scripts/check-library-artifact-contract.py
    python3 scripts/check-library-artifact-contract-reader-b.py
    python3 scripts/tests/test-library-artifact-contract.py
    bash scripts/tests/test-library-artifact-contract-mutations.sh

# L1 phase C1/G1 -- the Mathlib DECLARATION graph, below G0's module graph
# (docs/plan/graph-directed-library-roadmap-2026-08-30.md section G1,
# docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md section C1).
# `scripts/lib/declaration_graph.py` parses lean4export ndjson into rows
# shaped like ADR-0800 packs and reuses that contract's compute_closure/
# project_type_only rather than re-deriving them. The checker needs no Lean
# toolchain (it validates the committed graph): five guards reused verbatim
# from ADR-0800 (MISSING/DUPLICATE/REORDERED/TRUNCATED/VALUE_EXPOSED) plus
# three new ones -- ENDPOINT_RESOLUTION (a deleted ROW), EDGES_CONSISTENT (a
# deleted EDGE), CYCLE_CLASSIFICATION (an SCC not explained by any row's
# mutual_group) -- all eight mutation-verified 1:1.
declaration-graph:
    python3 scripts/check-declaration-graph.py
    python3 scripts/tests/test-declaration-graph.py
    bash scripts/tests/test-declaration-graph-mutations.sh

# L1 phase G2 -- join the Mathlib declaration graph (ADR-0820) to Axeyum's own
# state: ledger facts, kernel declarations, statement vocabulary, curriculum
# destination nodes, producers, declines, and trust footprints
# (docs/plan/graph-directed-library-roadmap-2026-08-30.md section G2,
# ADR-0835). Needs no Lean toolchain and no cargo run -- every input is
# already-committed JSON. `fact_ids`/`kernel_declarations` resolve ONLY
# through an exact match on an existing ledger fact's own title/evidence,
# never a bare name match; `name_coincidence_candidates` records every case
# where a name coincided with an unrelated fact and was NOT treated as an
# identity. Six guards (EMPTY_POPULATION, EMPTY_FACTS, ACCOUNTING,
# STALE_ARTIFACT, POSITIVE_CONTROL, BARE_NAME_BASIS), all mutation-verified
# 1:1 in test-graph-join-mutations.sh.
graph-join:
    python3 scripts/check-graph-join.py
    python3 scripts/tests/test-graph-join.py
    bash scripts/tests/test-graph-join-mutations.sh

# L2 phase G3 infrastructure frontier (docs/plan/graph-directed-library-
# roadmap-2026-08-30.md section G3, ADR-0845). Reads the L1 G2 graph join
# (read-only) and a hand-curated candidate list; re-validates every
# candidate against the live join at generation time and fails the whole
# gate if the committed artifact is stale. Seven guards (MISSING_JOIN,
# STALE_ARTIFACT, ROW_ID_UNIQUE, ROW_ID_PURITY, EMPTY_QUEUE_REASON,
# ROW_EVIDENCE_COMPLETE, CROSS_CHECK_PRESENT), all mutation-verified 1:1 in
# test-infrastructure-frontier-mutations.sh.
infrastructure-frontier:
    python3 scripts/check-infrastructure-frontier.py
    bash scripts/tests/test-infrastructure-frontier-mutations.sh

# L3-D0 effort taxonomy (docs/plan/definition-discovery-efficiency-roadmap-
# 2026-08-30.md, ADR-0870). Classifies 32 sampled completed/declined lane
# episodes into a 9-category taxonomy (the D0 spec's 8 plus
# infrastructure_maintenance) so the D1-D4 phase order is chosen from a
# measurement rather than an assumption. Corroboration for each
# "corroborated" episode is RE-VERIFIED here (a cited commit must resolve in
# this repo's object store, a cited ADR file must exist, a cited source file
# must exist), not merely trusted from the episode's own JSON. Nine guards,
# each mutation-verified to kill its own dedicated test(s) in
# test-effort-taxonomy.py's kill table (docs/plan/status/l3-d0-effort-
# taxonomy.md).
effort-taxonomy:
    python3 scripts/gen-effort-taxonomy.py --check
    python3 scripts/check-effort-taxonomy.py
    python3 scripts/tests/test-effort-taxonomy.py

# L2 phase G5 graph dispatcher (docs/plan/graph-directed-library-roadmap-
# 2026-08-30.md section G5, ADR-0885). Composes three read-only layers --
# curriculum.toml (destination), infrastructure-frontier (capability,
# ADR-0845), check-dispatchable-frontier.py (legal target) -- and is
# authoritative only for the exact (population, queue) pair ADR-0865
# measured. Ten guards, each mutation-verified 1:1 in
# test-graph-dispatcher-mutations.sh; a held-out fact can never be proposed
# (HELD_OUT_NEVER_PROPOSED, plus a live refusal-by-name demonstration in
# test-graph-dispatcher.py).
graph-dispatcher:
    python3 scripts/gen-graph-dispatcher.py --check
    python3 scripts/check-graph-dispatcher.py
    python3 scripts/tests/test-graph-dispatcher.py
    bash scripts/tests/test-graph-dispatcher-mutations.sh

# L3 phase D2 -- the structural theorem/proof index (docs/plan/definition-
# discovery-efficiency-roadmap-2026-08-30.md section D2, ADR-0905). A derived
# JSON index over kernel.environment() (namespace, binder roles,
# definitions/theorems/recursors used, a dependency-role proof-skeleton
# digest, a namespace-external dependency fingerprint aimed at the
# Int.prodRange_permute/Nat.countRange_permute case), a held-out-excluded
# join of Mathlib goal features from the fact ledger's formal.statement
# only, and three separately-reported ranking signals (identity, structural,
# lexical). Needs no cargo run -- validates the committed
# artifacts/structural-index/theorems.json. Six guards, all mutation-verified
# 1:1 in test-structural-index-mutations.sh.
structural-index:
    python3 scripts/check-structural-index.py
    bash scripts/tests/test-structural-index-mutations.sh

# L4 phase C2 -- universal checked interchange for credited roots
# (docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md section C2,
# ADR-0915). Validates artifacts/checked-interchange/census/*.census.json
# against the committed population snapshot AND a fresh read of the live
# graph-join (never the snapshot's own fields). Needs no Lean toolchain and
# no cargo run -- regeneration (which does need both) is
# `scripts/gen-checked-interchange.py`, deliberately NOT part of this gate,
# matching declaration-graph/graph-join's own gen/check split. Seven guards
# (MISSING, STALE_POPULATION, ACCOUNTING, MANDATORY_MISSING_ZERO,
# BARE_NAME_ACCEPT, BARE_TYPE_ACCEPT, DECLINE_PROBE_VACUOUS), all
# mutation-verified 1:1 in test-checked-interchange-mutations.sh.
checked-interchange:
    python3 scripts/check-checked-interchange.py
    python3 scripts/tests/test-checked-interchange.py
    bash scripts/tests/test-checked-interchange-mutations.sh

# L4 phase C3 -- the thin Lean adapter
# (docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md section C3).
# Validates artifacts/lean-adapter/results/*.result.json against the
# committed goal pack AND a fresh read of the live checked-interchange
# census's Lean toolchain identity (never this result's own fields). Needs
# no Lean toolchain and no cargo run -- regeneration (which needs both) is
# `cargo test --release -p axeyum-lean-import --test
# thin_lean_adapter_goal_pack`, deliberately NOT part of this gate, matching
# checked-interchange's own gen/check split. Seven guards (ABSENCE,
# LEAN_ACTUALLY_RAN, SUCCESS_ACCEPTED, MUTATIONS_REJECTED,
# DECLINES_TYPED_NONVACUOUS, EXPECTED_MATCHES_OBSERVED,
# ENVIRONMENT_TOOLCHAIN_STALE), all mutation-verified 1:1 in
# test-lean-adapter-mutations.sh.
lean-adapter:
    python3 scripts/check-lean-adapter.py
    python3 scripts/tests/test-lean-adapter.py
    bash scripts/tests/test-lean-adapter-mutations.sh

# declaration-spec (L3 phase D1, ADR-0965): the declarative declaration-spec
# pilot. Builds examples/declaration_spec_pilot (release -- debug SIGABRTs on
# kernel stack depth), dumps the real kernel's full name inventory, validates
# the pilot spec plus five adversarial negative fixtures each fail with the
# guard tag they exist to exercise (duplicate name in-corpus, cross-prelude
# duplicate, missing phase, dependency cycle, dependency/const_ref
# mismatch), then requires the pilot's own ExprId/digest comparison against
# the hand-written nat_prelude/squarefree.rs to report DIGESTS_IDENTICAL.
declaration-spec:
    python3 scripts/check-declaration-spec.py

# L3 phase D5 -- a bounded proof-plan IR
# (docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md). Runs the
# `proof_plan::` unit sweep, the digest probe over the six theorems whose
# proofs were rewritten to go through it (confirms footprint 0, i.e.
# unchanged from the pre-refactor commit), and the checker script's own
# in-process guard controls. No `gen-proof-plan.py` counterpart -- see
# `crates/axeyum-lean-kernel/src/proof_plan.rs`'s module doc for why this
# phase needed no code generation.
proof-plan:
    python3 scripts/check-proof-plan.py
    python3 scripts/tests/test-proof-plan-check.py
