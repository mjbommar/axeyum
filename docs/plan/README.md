# docs/plan/ — the end-to-end plan

This folder is the full engineering plan for Z3-class solving,
certified-result coverage, Lean-core compatibility, and Lean workflow
integration. It is intentionally long and built to be followed task-by-task
over weeks/months. Read the short [Project State](../PROJECT-STATE.md) first if
you are evaluating the current implementation rather than resuming engineering
work.

Start at the root [`PLAN.md`](../../PLAN.md) (map + standing rules) and
[`STATUS.md`](../../STATUS.md) (live state). Then this folder.

## Layout

- [`00-north-star.md`](00-north-star.md) — the long-horizon reference targets;
  operational status uses the separate parity axes below rather than one
  "Z3 + Lean" percentage.
- [`01-dependency-dag.md`](01-dependency-dag.md) — the cross-track dependency DAG,
  the two keystones, the critical paths, and the recommended execution order.
- [`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md) —
  **current** scoped evidence map and ranked research program. It separates
  fragment decision parity, production Z3 replacement, certified-result
  coverage, Lean-kernel compatibility, and Lean workflow integration.
- [`parity-target-evidence-audit-2026-07-21.md`](parity-target-evidence-audit-2026-07-21.md) —
  executable-evidence correction to the word “parity”: 78 adjudicated public
  agreements plus four unadjudicated decisions, exact 6/2/2 p4dfa solved-set
  overlap, unmeasured general Z3 solving-power distance, directly measured
  production-compatibility gaps, and the then-unexecuted official-Lean gate.
- [`official-lean-ci-gate-audit-2026-07-21.md`](official-lean-ci-gate-audit-2026-07-21.md) —
  primary-source diagnosis of the Lake-action setup failure, checksum-pinned
  non-Lake installer, missing-binary fail-closed repair, initial 67/71 external
  rejection result, narrow export corrections, and bounded local 71/71 rerun.
- [`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md) —
  evidence-backed separation of independent kernel checking from the missing
  Lean frontend/workflow/mathlib surfaces, a real format-3.1 `lean4export`
  prototype, three-profile architecture, and staged L0-L10 import, kernel,
  tactic, source, Lake, editor, compiler, and mathlib gates.
- [`lean-system-implementation-plan-2026-07-21.md`](lean-system-implementation-plan-2026-07-21.md) —
  active implementation-grade L0-L10 work breakdown: K0-K6 capability
  profiles, common gates, ownership boundaries, dependency graph, TL task IDs,
  milestones, native parser/elaborator/tactics/Lake/LSP/compiler/`.olean` and
  full pinned-mathlib paths, plus the exact resume queue.
- [`lean-compatibility-v1.json`](lean-compatibility-v1.json) and generated
  [`Lean compatibility matrix`](generated/lean-compatibility.md) — TL0.2's
  executable eight-field assurance contract, K0-K6 profile gates, registered
  importer decline codes, exact current artifacts, and fail-closed implication
  checks preventing parser/oracle evidence from becoming independent admission.
- [`lean-axiom-ledger-v1.json`](lean-axiom-ledger-v1.json) and generated
  [`Lean prelude-axiom ledger`](generated/lean-axiom-ledger.md) — TL0.4's
  runtime-derived 65-row population (real 30, integer 34, string 1), with each
  admitted name bound to its canonical kernel-rendered type digest, source,
  owner, classification, and discharge state. The gate rejects added, removed,
  renamed, or type-mutated assumptions; semantic classification remains TL3.2.
- [`lean-kernel-seam-fuzz-seed-2026-07-21.md`](lean-kernel-seam-fuzz-seed-2026-07-21.md) —
  T6.0.3/TL2.15's deterministic 768-case seed across the four currently
  representable kernel seams, including exact corner denominators, `False`
  admission/rollback invariants, reproduction seeds, and explicit non-credit
  for projection/eta, quotients, typed literals, and official-Lean differential
  fuzzing.
- [`lean-projection-representation-tl2.2-2026-07-21.md`](lean-projection-representation-tl2.2-2026-07-21.md) —
  TL2.2 result: first-class projection terms across all structural operations
  and renderers, with exhaustive mutation/traversal tests and the historical
  fail-closed boundary before TL2.3.
- [`lean-projection-inference-tl2.3-2026-07-21.md`](lean-projection-inference-tl2.3-2026-07-21.md) —
  TL2.3 result: checked structure metadata and dependent projection inference,
  including malformed-shape and Prop-elimination controls, while reduction,
  eta, and importer translation remain explicitly uncredited.
- [`lean-projection-reduction-tl2.4-2026-07-21.md`](lean-projection-reduction-tl2.4-2026-07-21.md) —
  TL2.4 result: constructor projection computation, validated wire translation,
  exact official-root admission/computation, mutation controls, and the explicit
  separation from TL2.5 structure eta.
- [`lean-structure-eta-tl2.5-2026-07-21.md`](lean-structure-eta-tl2.5-2026-07-21.md) —
  TL2.5 result: checked one-constructor/zero-index/non-recursive eligibility,
  symmetric native structure eta, false-equality and malformed-family controls,
  and a required positive/rejecting differential against pinned Lean 4.30.
- [`lean-system-roadmap-completion-audit-2026-07-21.md`](lean-system-roadmap-completion-audit-2026-07-21.md) —
  requirement-by-requirement audit of the parser/macro, elaborator/unifier,
  tactic, compiler, Lake, LSP, mathlib, and import objective; revalidated local
  and pinned-upstream inventories; prototype evidence; and the explicit
  distinction between a complete roadmap objective and the continuing Lean
  implementation program.
- [`lean4export-rust-import-prototype-2026-07-21.md`](lean4export-rust-import-prototype-2026-07-21.md) —
  first independent declaration-import results: separate Rust wire crate, exact
  format/topology/resource contract, 5-record to 8-declaration flat admission,
  5-record to 11-declaration direct-recursive admission, binder-correct
  generated-recursor comparison, exact 9-declaration projection-root
  admission/computation, 28 importer cases across three binaries, and explicit
  literal/quotient/harder-inductive declines.
- [`lean-official-construct-matrix-plan-2026-07-22.md`](lean-official-construct-matrix-plan-2026-07-22.md) —
  proposed source-first/wire-second execution plan for the remaining
  recursive-indexed, reflexive/higher-order, mutual, nested, and well-founded
  official cases, with direct-recursive controls, generated assurance classes,
  retention/resource bounds, stop conditions, and the post-matrix TL2.11--TL2.14
  trajectory.
- [`lean-official-construct-matrix-stage-a-2026-07-22.md`](lean-official-construct-matrix-stage-a-2026-07-22.md)
  and [`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json) —
  completed M0/Stage A evidence and the fail-closed seven-case source
  registration: exact pins, source/control hashes, official positive/negative
  outcomes, resource/retention bounds, and an enforced absence of Stage B wire
  or Rust product observations.
- [`lean-official-construct-matrix-stage-b-2026-07-22.md`](lean-official-construct-matrix-stage-b-2026-07-22.md) —
  two-run byte-identical official exports and independent declaration/group
  inventories for recursive-indexed, reflexive, mutual, nested, and well-
  founded roots, with 116,636 retained bytes and every Rust product field still
  absent.
- [`lean-official-construct-matrix-product-2026-07-22.md`](lean-official-construct-matrix-product-2026-07-22.md) —
  M3's unmodified current-importer measurement: ten passing direct-recursive
  controls, two exact typed outcomes per new row, no partial publication, and
  the explicit nested-format misclassification and well-founded `Acc`
  dependency stop.
- [`lean-official-construct-matrix-m4-2026-07-22.md`](lean-official-construct-matrix-m4-2026-07-22.md)
  and the generated [`official Lean construct matrix`](generated/lean-official-construct-matrix.md) —
  seven assurance-separated selected-family rows, implication checks against
  false parser/admission/computation promotion, and the explicit TL1.8/TL2.16
  partial boundary.
- [`lean-official-construct-matrix-final-2026-07-22.md`](lean-official-construct-matrix-final-2026-07-22.md) —
  M5's exact final gates, accepted ADR-0351, environmental rustdoc diagnosis,
  selected-family completion boundary, and TL2.11-first handoff.
- [`lean-strict-positivity-tl2.11-plan-2026-07-22.md`](lean-strict-positivity-tl2.11-plan-2026-07-22.md) —
  preregistered Lean 4.30 WHNF/`Pi`/valid-family-application rule, typed error
  boundary, pre-insertion ordering, adversarial grammar, official differential,
  and M0--M4 gates for TL2.11/T6.0.2.
- [`lean-strict-positivity-m0-2026-07-22.md`](lean-strict-positivity-m0-2026-07-22.md)
  and [`lean-strict-positivity-v1.json`](lean-strict-positivity-v1.json) —
  four hash-frozen sources, six ordered rule classes, bounded command/resource
  registration, and eight fail-closed tests with no premature observation.
- [`lean-strict-positivity-m1-2026-07-22.md`](lean-strict-positivity-m1-2026-07-22.md)
  — trusted single-family positivity preflight, typed polarity/application
  failures, pre-insertion ordering evidence, and bounded 182-test kernel gate.
- [`lean-strict-positivity-m2-2026-07-22.md`](lean-strict-positivity-m2-2026-07-22.md)
  — twelve-row public admission contract plus a fixed-seed 840-case grammar
  repeated byte-identically across profiles, sorts, contexts, and ordering.
- [`lean-strict-positivity-m3-2026-07-22.md`](lean-strict-positivity-m3-2026-07-22.md)
  and [`lean-strict-positivity-m3-v1.json`](lean-strict-positivity-m3-v1.json)
  — eight bounded pinned-Lean observations, mandatory CI differential,
  explicitly synthetic importer propagation, and unchanged frozen construct
  matrix.
- [`lean-strict-positivity-final-2026-07-22.md`](lean-strict-positivity-final-2026-07-22.md)
  — M4 final bounded gates, accepted ADR-0352, completed TL2.11/T6.0.2, exact
  non-claims, and the preregistration-first TL2.12 handoff.
- [`lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md`](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)
  — accepted ADR-0353's unified `Pi telescope, motive indices (field args)`
  rule, native/official computation gates, mutation grammar, resource bounds,
  stop conditions, and M0--M5 commit/push sequence for TL2.12.
- [`lean-recursive-induction-hypotheses-m0-2026-07-22.md`](lean-recursive-induction-hypotheses-m0-2026-07-22.md)
  and [`lean-recursive-induction-hypotheses-v1.json`](lean-recursive-induction-hypotheses-v1.json)
  — M0's twice-compiled explicit-recursor source, two byte-identical official
  root streams, independent wire inventories, fail-closed ten-test contract,
  exact non-claims, and M1 shared-representation handoff.
- [`lean-recursive-induction-hypotheses-m1-2026-07-22.md`](lean-recursive-induction-hypotheses-m1-2026-07-22.md)
  — shared WHNF classifier/reopener, stable recursive-field metadata, exact
  direct-recursive identities, unchanged feature declines, retained negative
  observations, and the M2 native-semantics handoff.
- [`lean-recursive-induction-hypotheses-m2-2026-07-22.md`](lean-recursive-induction-hypotheses-m2-2026-07-22.md)
  — unified native IH/iota semantics, fourteen named rows, ten native mutation
  classes, the 768-case recursive grammar, and the retained positivity control.
- [`lean-recursive-induction-hypotheses-m3-2026-07-22.md`](lean-recursive-induction-hypotheses-m3-2026-07-22.md)
  — exact official Vector/Acc recursor comparison, descriptive reflexive
  metadata, completion-only publication, and retained mutual/nested boundaries.
- [`lean-recursive-induction-hypotheses-m4-2026-07-22.md`](lean-recursive-induction-hypotheses-m4-2026-07-22.md)
  — pinned-Lean and independent Axeyum computation at the registered Vector/Acc
  normal forms plus the machine-validated current assurance overlay.
- [`lean-recursive-induction-hypotheses-final-2026-07-22.md`](lean-recursive-induction-hypotheses-final-2026-07-22.md)
  — M5 final bounded gates, accepted ADR-0353, completed TL2.12, exact
  non-claims, and the TL2.13 mutual-group handoff.
- [`lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md`](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)
  — accepted ADR-0354's atomic ordered group rule, shared parameter/universe and
  group-wide positivity checks, complete motive/minor and target-recursion
  construction, native/mutation/generated/official gates, resource bounds,
  stop conditions, and P0--M5 commit/push sequence for TL2.13.
- [`lean-mutual-inductive-groups-m0-2026-07-22.md`](lean-mutual-inductive-groups-m0-2026-07-22.md)
  and [`lean-mutual-inductive-groups-v1.json`](lean-mutual-inductive-groups-v1.json)
  — M0's twice-compiled explicit-recursor source, two byte-identical official
  streams, complete group/recursor inventories, source-family versus wire-
  dependency order distinction, fail-closed eleven-test contract, exact
  non-claims, and M1 representation/singleton handoff.
- [`lean-mutual-inductive-groups-m1-2026-07-22.md`](lean-mutual-inductive-groups-m1-2026-07-22.md)
  — M1's public ordered family/group representation, common-parameter/result-
  universe and name preflight, per-family index opening, insertion-log
  transaction, exact singleton identity/error/computation preservation, typed
  multi-family policy decline, bounded gates, non-claims, and M2 handoff.
- [`lean-mutual-inductive-groups-m2-2026-07-22.md`](lean-mutual-inductive-groups-m2-2026-07-22.md)
  — M2's complete-group positivity and native atomic admission, globally
  ordered motives/minors, target-family induction hypotheses and recursor
  calls, mutual-`Prop` restriction, 18-row public matrix, mutation/late-rollback
  teeth, retained singleton/768/840 controls, and M3 grammar handoff.
- [`lean-mutual-inductive-groups-m3-2026-07-22.md`](lean-mutual-inductive-groups-m3-2026-07-22.md)
  — M3's 720-case independent public-path grammar, byte-identical repetition,
  direct recursor-telescope order oracle, target-family rule signatures, 432
  positive iota contracts, 288 typed rollbacks, generated mutation teeth,
  retained 768/840 controls, and M4 importer handoff.
- [`lean-mutual-inductive-groups-m4-2026-07-22.md`](lean-mutual-inductive-groups-m4-2026-07-22.md)
  — M4's atomic ordered-group import, name-based official recursor comparison,
  twice-repeated exact construct/non-indexed/indexed streams, two registered
  cross-family normal forms, 22 rejecting wire/publication mutations, retained
  720/768/840 controls, and M5 assurance/closure handoff.
- [`lean-mutual-inductive-groups-final-2026-07-22.md`](lean-mutual-inductive-groups-final-2026-07-22.md)
  — M5's append-only assurance overlay, synchronized compatibility contract,
  final bounded gates, accepted ADR-0354, completed TL2.13, exact non-claims,
  and the historical TL2.14 handoff later corrected by the dependency audit.
- [`lean-post-tl2.13-dependency-audit-2026-07-22.md`](lean-post-tl2.13-dependency-audit-2026-07-22.md)
  — source-backed correction separating kernel-side nested-inductive
  elimination from elaborator-side well-founded source recursion, with the
  exact current nested and already-passing well-founded product boundaries.
- [`lean-nested-inductive-elimination-resume.md`](lean-nested-inductive-elimination-resume.md)
  — **single resume entry point** for TL2.14 work: exact pushed state,
  completed P0/M0/M1/M2 evidence, M3's frozen bounded task, remaining M3--M6 work,
  validation commands, ownership rules, resource caps, and stop conditions.
- [`lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md`](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)
  — proposed ADR-0355's trusted expansion/restoration rule, source/wire freeze,
  native/importer/mutation/generated gates, P0-M6 milestones, resource bounds,
  stop conditions, and exact source-elaboration non-claims.
- [`lean-nested-inductive-elimination-m0-2026-07-22.md`](lean-nested-inductive-elimination-m0-2026-07-22.md)
  and [`lean-nested-inductive-elimination-v1.json`](lean-nested-inductive-elimination-v1.json)
  — M0's twice-reproduced positive/negative sources, three byte-identical
  auxiliary-recursor streams, exact nested group inventories and variable wire
  order, frozen future populations, and fail-closed no-product boundary.
- [`lean-nested-inductive-elimination-m1-2026-07-22.md`](lean-nested-inductive-elimination-m1-2026-07-22.md)
  — M1's group-wide `numNested`/recursor-shape preflight, exact typed nested
  decline before admission, malformed singleton/mutual mutation coverage,
  retained well-founded/720/768/840 controls, and M2 native-semantics handoff.
- [`lean-nested-inductive-elimination-m2-2026-07-22.md`](lean-nested-inductive-elimination-m2-2026-07-22.md)
  — M2's native structural discovery, complete container-group copying,
  fixed-point expansion, unchanged atomic checking, recursive source-surface
  restoration, exact `.rec_N` publication, 23-case matrix, cross-boundary
  computation, transactional rollback, and M3 generated-grammar handoff.
- [`lean-nested-inductive-elimination-m3-plan-2026-07-22.md`](lean-nested-inductive-elimination-m3-plan-2026-07-22.md)
  — M3's pre-run frozen schema/seed, exact 640-case construction, complete
  registered range coverage, independent public observer, private forced
  mutation registry, retained descriptors, resources, and stop conditions.
- [`lean-import-transactional-publication-tl1.3-2026-07-22.md`](lean-import-transactional-publication-tl1.3-2026-07-22.md),
  [`lean-import-mutation-corpus-tl1.4-2026-07-22.md`](lean-import-mutation-corpus-tl1.4-2026-07-22.md),
  and [`lean-declaration-identity-tl1.7-2026-07-22.md`](lean-declaration-identity-tl1.7-2026-07-22.md) —
  owned completion-only publication, the deterministic 226-case format
  mutation corpus with explicit no-footer boundary, and versioned canonical
  axiom/declaration/direct-dependency identities.
- [`lean4export-official-blocker-census-2026-07-21.md`](lean4export-official-blocker-census-2026-07-21.md) —
  exact official projection/Nat/String/quotient dependency closures, committed
  small streams and hashes, assurance-separated admission matrix, and the
  measured decision to implement projection before literals.
- [`gap-ownership-v1.json`](gap-ownership-v1.json) and the generated
  [contributor ownership map](../contributor-guide/gap-ownership.md) — G0-G10
  routing from each research question to owning code, committed evidence,
  executable gates, ADRs, and the next safe action.
- [`measurement-provenance-design-2026-07-21.md`](measurement-provenance-design-2026-07-21.md),
  the [shared schema](measurement-provenance-v1.json), and generated
  [53-row matrix](generated/measurement-provenance-matrix.md) — G1's common
  raw/path/content/selection/scoring/oracle vocabulary across the separately
  scored regression and partial-public regimes, including their exact overlap
  and explicit non-official/non-neutral boundaries.
- [`smtcomp-full-library-candidate-run-handoff-2026-07-21.md`](smtcomp-full-library-candidate-run-handoff-2026-07-21.md) —
  frozen first full-tree selection/run attempt: exact external manifest/list
  hashes, 438,631-to-64,345 candidate selection, incomplete 52-shard execution,
  zero raw-result credit, and the checkpoint/resume prerequisite to any rerun.
- [`smtcomp-resumable-run-design-2026-07-21.md`](smtcomp-resumable-run-design-2026-07-21.md),
  the active [machine-readable v2 contract](smtcomp-resumable-run-contract-v2.json),
  preserved [v1 sketch](smtcomp-resumable-run-contract-v1.json), and
  generated [failure/recovery matrix](generated/smtcomp-resumable-run-contract.md) —
  G1's E0 prototype for immutable result checkpoints, exact run identity,
  attempt/completion accounting, strict merge, aggregate resource enforcement,
  and interruption/restart equivalence. It is a prerequisite design, not an
  authorization to rerun the candidate.
- [`smtcomp-resumable-filesystem-e1a-2026-07-21.md`](smtcomp-resumable-filesystem-e1a-2026-07-21.md) —
  bounded local E1a result: 8/8 forced-kill recoveries across tmpfs and the
  worktree's ext-family filesystem, with no-overwrite install, orphan/conflict
  quarantine, strict filename/key validation, and explicit power-loss/NFS/
  solver/remote declines.
- [`smtcomp-runner-e1b-audit-2026-07-21.md`](smtcomp-runner-e1b-audit-2026-07-21.md) —
  source-backed integration audit that supersedes the thin v1 process schema,
  separates observed from scoring-admitted responses, replaces signal-to-OOM
  guessing with typed termination, attributes results to attempts, and freezes
  the opt-in one-solver E1b seams without changing the active runner.
- [`smtcomp-resumable-runner-e1b-2026-07-22.md`](smtcomp-resumable-runner-e1b-2026-07-22.md) —
  fixture-only active-runner integration with exact preflight, immutable
  attempts/results/sidecars, typed termination, lease recovery, and
  completion-gated raw export.
- [`smtcomp-one-host-resource-enforcement-e2-2026-07-22.md`](smtcomp-one-host-resource-enforcement-e2-2026-07-22.md) —
  one-host user-systemd/cgroup-v2 aggregate memory, swap, CPU, and PID
  enforcement with bounded workers, immutable counter evidence, and destructive
  host-runner kill/resume tests; E3 multi-host durability remains open.
- [`smtcomp-multi-host-durability-e3-plan-2026-07-22.md`](smtcomp-multi-host-durability-e3-plan-2026-07-22.md) —
  preregistered three-host shared-NFS allocation, exact host-loss recovery,
  content-bound source staging, completion, and canonical-equivalence gates.
- [`generated/proof-gap-matrix.md`](generated/proof-gap-matrix.md) — generated
  per-instance/per-evidence proof pipeline: baseline UNSAT, evidence-audit
  outcome, certification, independent checking, trust holes, Lean
  reconstruction, and the exact residual blockers.
- [`generated/proof-gap-shape-census.md`](generated/proof-gap-shape-census.md) —
  source-hash-bound, parser-backed, exact-content-deduplicated census of the
  uncertified UNSAT population. It retains source syntax and reachable parsed
  IR plus bounded/string side-channel presence while refusing to infer a proof
  mechanism from operator presence alone.
- [`evidence-route-provenance-design-2026-07-21.md`](evidence-route-provenance-design-2026-07-21.md) —
  causal instrumentation design for the four bare-UNSAT exits, including the
  completed dominance-v2 population refresh and vacuous-check correction,
  measured decision-backend prevalence, stable route IDs, obligation
  fingerprints, and the gate for selecting actual proof mechanisms.
- [`lean-selected-evidence-prototype-2026-07-21.md`](lean-selected-evidence-prototype-2026-07-21.md) —
  bounded eight-row prototype showing five direct existing-consumer successes
  (including all three QF_NIA Alethe proofs through EUF) and three distinct
  quantified-BV kernel-closure, compact-spooling, and CPS-reconstruction cost
  cases measured under hard wall/memory bounds.
- [`categorical-engine-depth-audit-2026-07-21.md`](categorical-engine-depth-audit-2026-07-21.md) —
  source/API/decline/test audit correcting interpolation, CHC/Horn, and abduction
  from “absent” to measured seed/selected-fragment status while keeping general
  SyGuS, textual conformance, production depth, corpora, and certification open.
- [`smtlib-api-conformance-v1.json`](smtlib-api-conformance-v1.json) and the
  generated [`SMT-LIB/API matrix`](generated/smtlib-api-conformance.md) —
  checked 30-row command/protocol inventory separating parser state, execution,
  output representation, assurance, exact tests, and residuals. It prevents
  parser no-ops and direct Rust helpers from being reported as an ordered
  interactive SMT-LIB implementation.
- [`smtlib-session-contract-design-2026-07-21.md`](smtlib-session-contract-design-2026-07-21.md),
  the [machine-readable contract](smtlib-session-contract-v1.json), and its
  generated [transcript matrix](generated/smtlib-session-contract.md) — pinned
  SMT-LIB 2.7 state-machine design with 14 invariants and 20 executable abstract
  fixtures / 107 commands. The audit exposes scoped declarations,
  reset-assertions signature behavior, query snapshots, and error atomicity as
  prerequisites to textual output; proposed ADR-0342 gates implementation.
- [`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) —
  historical pre-neutral-baseline leverage analysis; its p4dfa premise and
  scoreboard totals are superseded by the 2026-07-21 map
  ([`gap-analysis-z3-cvc5-2026-06-22.md`](gap-analysis-z3-cvc5-2026-06-22.md)
  is the still-earlier baseline).
- [`provable-security-integration.md`](provable-security-integration.md) — how
  provable-security/game-based cryptography ideas should feed Track 5,
  proof-cookbook work, scenario corpora, and finite-field demand without
  reordering the current parity queue.
- [`track-1-engine/`](track-1-engine/README.md) — Engine & Performance.
- [`track-2-theories/`](track-2-theories/README.md) — Theories & Breadth.
- [`track-3-proof-lean/`](track-3-proof-lean/README.md) — Proofs & Lean.
- [`track-4-usecases-frontend/`](track-4-usecases-frontend/README.md) — Use Cases
  & Frontend.
- [`track-5-verified-systems/`](track-5-verified-systems/README.md) — Verified
  Systems (IR reflection): the seL4-inspired application trajectory — reflect
  compiled Rust (MIR + LLVM IR) into the solver, discharge panic-freedom /
  memory-safety / constant-time / equivalence / protocol obligations
  push-button with certificates (adopted by
  [ADR-0056](../research/09-decisions/adr-0056-verified-systems-track.md)).
- [`references/`](references/README.md) — the distilled top-down review of the
  reference solvers this plan is built on (Z3, cvc5, bitwuzla, CaDiCaL, Kissat,
  Carcara, lean4, nanoda_lib, lean-smt, drat-trim).

## Conventions

- **Phase IDs** are `P<track>.<n>` (e.g. `P1.4`). **Task IDs** are
  `T<track>.<n>.<m>` (e.g. `T1.4.2`).
- Each phase file has: **Goal**, **Why / leverage**, **Dependencies**,
  **Tasks** (a table: id, task, key references, size, exit), **Phase exit
  criteria**, and **References**.
- Reference file paths are given relative to the repo root (e.g.
  `references/z3/src/sat/sat_solver.cpp`) so they are clickable and exact.
- **Sizing:** `S` ≈ ≤2 days · `M` ≈ ~1 week · `L` ≈ ~2–4 weeks · `XL` ≈ multi-month.
- **Status:** `TODO` / `WIP` / `DONE` / `BLOCKED` (tracked in
  [`STATUS.md`](../../STATUS.md), not duplicated here).

## Principles carried from the project identity

- **Untrusted fast search, trusted small checking.** Every new `unsat` route
  either gets an independent checker or is recorded in the
  [trust ledger](track-3-proof-lean/P3.0-trust-ledger.md) as an explicit,
  countable trust assumption — never an implicit gap.
- **Measure before tuning.** Performance phases are gated by the benchmarking
  harness ([P4.5](track-4-usecases-frontend/P4.5-benchmarking.md)); we change one
  thing and re-measure against Z3 on a committed slice.
- **Eager → lazy is the recurring upgrade.** Most theories work today by eager
  one-shot reduction; parity means moving them onto the incremental
  e-graph + CDCL(T) loop. That loop is the keystone (Track 1).
