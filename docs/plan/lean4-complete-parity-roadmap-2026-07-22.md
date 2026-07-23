# Complete Lean 4 parity execution roadmap

Status: **active roadmap; complete Lean 4.30 parity is not established**

Date: 2026-07-22

Target: Lean `v4.30.0`, `lean4export` format `3.1.0`, and mathlib
`v4.30.0`, at the exact commits in the
[`complete-parity contract`](lean4-complete-parity-contract-2026-07-22.md).

This is the execution-oriented companion to the terminal contract and the
[`machine-readable registry`](lean-complete-parity-v1.json). It answers three
questions: what the current evidence actually proves, what complete parity
still means, and in what dependency order the missing system must be built and
measured.

## 1. Bounded verdict

Axeyum is not close to an honest unqualified “100% Lean parity” claim. The
independent Rust kernel/importer has important bounded coverage, including the
completed TL2.14 nested-inductive population, but native source parsing,
elaboration, tactics, projects, the language server, compilation/runtime,
bootstrap, complete `Init`/`Std`, and mathlib remain incomplete or unstarted at
the complete-parity level.

Current machine-derived state:

| Surface | Current evidence | What it does not prove |
|---|---|---|
| K0 independent checker | 1/1 profile rows | source-language or workflow compatibility |
| K1 versioned import | 4/5 profile rows | String/quotient closure or complete official construct coverage |
| K2-K6 | 0 satisfied rows | parser/elaborator, tactics, project/editor, runtime, or ecosystem parity |
| U0-U9 | 0 complete authorities | a complete executable denominator for any terminal population |
| A0-A11 | 0 complete axes | end-to-end native behavior on any complete required population |
| G1-G10 | 0 satisfied terminal gates | any terminal parity claim |
| U2 official execution/classification | 8 consumed processes, 66 official outcomes, 65 passes / 1 failure over **65 unique cases**; execution M1 derives 5 exact memberships and 289 physical shards, one locally complete; TL0.6.4 M0 gives all 3,723 cases a harness floor, M1 inspects 7,004 tracked files / 90,909 spans, M2.0 freezes an empty typed graph across 408,374 factored case/variant occurrences, M2.1-M2.7 have source-first dependency/merge semantics, and M3.0 now defines exhaustive independent case/cell review without executing or accepting those programs | the 3,678/3,723-case parents, all 111 full attempts, any resolved dependency node/edge/closure, configured provider/runner/Lake/compiler/runtime/FFI/editor edge, any closed or reviewed case/variant cell, accepted TL0.6.4 classification, an Axeyum outcome, a pair, or performance |

The accepted
[`R3 result`](lean-u2-official-execution-tl0.6.3-m0-r3-result-2026-07-22.md)
is useful because it qualifies one real local official-case path. The later R6
authority adds 64 disjoint local cases, so aggregate unique coverage is now
65/3,678 rather than the historical singleton's 1/3,678. There are still zero
native Axeyum U2 outcomes and zero paired cells.

The pushed
[`R7 current-source identity result`](lean-complete-parity-current-source-identity-r7-result-2026-07-23.md)
repairs the only post-integration Lean/SMT source-pin drift without changing
those counts. Historical store/acceptance/U2 authorities retain the exact
evidence-producing filesystem primitive, current validators freeze the exact
reviewed SMT successor, and both owning-root and detached-root terminal checks
pass. Integration to current `main` and a post-merge replay remain required
before M2.1 authorization; the repair itself adds no execution credit.

The accepted
[`M1 shard result`](lean-u2-official-execution-tl0.6.3-m1-shard-result-2026-07-22.md)
closes immediate action 2's scheduling derivation only: eight official
selections reduce to five exact ordered memberships and 289 bounded physical
shards. The 461 selection-expanded and 6,451 attempt-expanded occurrences are
reference multiplicities, not completed executions. All 111 attempts remain
`not-run`, and no derived shard or ordered prefix is a representative sample.
The separately pushed
[`M2 plan`](lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md)
selects the lowest-ordinal zero-history shard (64 cases) and freezes one local
attempt. The pushed
[`offline implementation checkpoint`](lean-u2-official-execution-tl0.6.3-m2-implementation-2026-07-22.md)
records commit `9783ba93` and its exact spec/harness/discovery/JUnit/artifact/
credit contract, with no live execution surface and zero outcome or terminal
credit. Commit `57dcf343` subsequently adds and pushes the exact 64-case
completion-last store. Commit `d1f144d4` corrects the frozen evidence order,
and commit `431d3959` implements and pushes the one-shot runner. The command
exists, but its first invocation stopped during selected-source preflight
because the official compile-bench runner is a pinned link rather than a
regular manifest row. No harness, discovery, prelaunch, evidence root, or child
process exists, so the process attempt remains unconsumed. The
[`R1 correction plan`](lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-plan-2026-07-22.md)
freezes safe one-hop relative manifest resolution, exact link/target identities,
mutation gates, and a fresh work root before another read-only preflight. The
[`R1 implementation checkpoint`](lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-implementation-2026-07-22.md)
records pushed commit `9d5d40c8`, fifteen fail-closed mutation variants, and
no new work root or live process at publication. Exact preflight then passed
and the attempt ran once. The
[`R1 result`](lean-u2-official-execution-tl0.6.3-m2-r1-result-2026-07-22.md)
retains exact 64-row JUnit (30 pass / 34 fail), but family-blind docparse
artifact closure stopped before completion. The attempt is consumed, all rows
remain diagnostic, and M2 credit is zero pending publication of the invalid
evidence/result and any later source-first recovery decision. The evidence is
now published, and the
[`R2 diagnostic-closure plan`](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-plan-2026-07-22.md)
freezes a zero-process/zero-credit storage split: all 124 generated rows remain
bound, 67 outcome/log payloads are retained, and 56 large reproducible
intermediates remain metadata-only. The accepted
[`R2 result`](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-result-2026-07-22.md)
installs that append completion last with 69 new files, zero processes, zero
outcomes, and unchanged invalid R1 credit. The separately source-first
[`R3 attempt-002 plan`](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-plan-2026-07-23.md)
now assigns new run/work/evidence identities and freezes universal
`LEAN_STACK_SIZE_KB=524288`, the same 64-case/8 GiB/one-worker/hour lane, and
R2's tiered family-specific store. It permits at most one new process only
after implementation and offline gates are committed and pushed; no R3
harness, discovery, or process exists at preregistration. The pushed
[`R3 implementation checkpoint`](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-implementation-2026-07-23.md)
now records commit `d47dacc6`, the exact runner/store, 6/6 focused and 264
aggregate Lean tests, and a harmless direct-runtime stack probe. No selected
harness, discovery, or process exists at the checkpoint; final external
preflight precedes the one permitted invocation. Preflight subsequently passed
at `0a4d5daa`, and attempt 002 ran once. The accepted
[`R3 result`](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-result-2026-07-23.md)
retains a 3,600,038 ms watchdog timeout: seven CTest rows printed pass, then
`compile_bench/channel.lean` failed dedicated-thread creation and deadlocked.
The group was reaped, but no JUnit/case/post/projection/completion exists; R3 is
consumed and grants zero M2 credit.
The source-first
[`R4 attempt-003 plan`](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-plan-2026-07-23.md)
now selects the larger-address-space branch of that decision: one 16 GiB local
lane, unchanged 512 MiB stack and exact shard/command/store, a harmless
nine-dedicated-thread control, one selected process, and no retry or terminal
promotion. The separately published implementation and one-token control
correction reached the
[`R4 control result`](lean-u2-official-execution-tl0.6.3-m2-r4-control-result-2026-07-23.md):
the direct stack probe passed, but the corrected nine-task control reached a
16,504,496,128-byte `VmPeak`, emitted `failed to create thread`, and timed out
under the exact 16 GiB limit. Cleanup left no selected root or process, so
attempt 003 remains unconsumed and R4 adds zero credit. The immediate U2 path
is therefore a new source-first larger-lane qualification with retained failed
control evidence, not selected execution under R4. The preregistered
[`R5 plan`](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-plan-2026-07-23.md)
selects one 32 GiB resource-only doubling and makes both control success and
failure completion-grade evidence. It reuses selected attempt 003 only because
R4 created no selected root/process. The subsequent
[`R5 incomplete result`](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-incomplete-result-2026-07-23.md)
records a passed control and clean 64/64 selected JUnit, but fail-closed post
capture rejected the absent all-pass `LastTestsFailed.log`. Attempt 003 is
consumed with zero credit. The subsequent
[`R5 diagnostic closure`](lean-u2-official-execution-tl0.6.3-m2-r5-diagnostic-closure-result-2026-07-23.md)
appends 68 files / 149,513 bytes completion-last with zero processes and binds
the 64 passes, 123 generated rows, 66 retained payloads, 56 metadata rows, and
conditional failure-log absence without promoting any outcome. R5 is closed;
the source-first
[`R6 attempt-004 plan`](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-plan-2026-07-23.md)
now freezes fresh roots and one selected process on the unchanged qualified
lane. It selects the 123-row all-pass or 124-row any-failure artifact shape
only after exact JUnit validation. Next implement/test/push R6 and a fresh
completion-grade control; no selected process is yet authorized. The separate
[`R6 implementation checkpoint`](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-implementation-2026-07-23.md)
is now pushed at `ff2406b1`, with both branches and inversion mutations tested.
After publication, the direct stack probe passed but delegated control history
preflight recursed before root creation. The source-first
[`R1 correction`](lean-u2-official-execution-tl0.6.3-m2-r6-control-history-r1-plan-2026-07-23.md)
freezes captured-original R5 validation/restoration; attempt 004 remains
unconsumed. The separate
[`R1 implementation`](lean-u2-official-execution-tl0.6.3-m2-r6-control-history-r1-implementation-2026-07-23.md)
is pushed at `70268f2d` and tests the exact temporary binding path. Next publish
that checkpoint and repeat one fresh control; selected execution remains
unauthorized. The corrected control then passed at `dc588033` and attempt 004
ran once. Its
[`pending-validation result`](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-pending-validation-result-2026-07-23.md)
retains clean 64/64 JUnit and completion last, but replay used pre-install
completion mode. The
[`R2 plan`](lean-u2-official-execution-tl0.6.3-m2-r6-completion-replay-r2-plan-2026-07-23.md)
authorizes only validator-mode correction over the unchanged root. R6 remains
zero-credit until exact replay passes; no selected retry exists. Its
[`R2 implementation`](lean-u2-official-execution-tl0.6.3-m2-r6-completion-replay-r2-implementation-2026-07-23.md)
is pushed at `ce319a9d` with an unchanged-inventory copied-root test. Next
publish the checkpoint and perform one qualifying read-only replay. That replay
passed, and the
[`accepted R6 result`](lean-u2-official-execution-tl0.6.3-m2-r6-result-2026-07-23.md)
credits 64/64 local official outcomes plus one physical shard. Aggregate local
U2 is now 66 outcomes / 65 unique cases; all full official attempts, parent,
provider, Axeyum, pairing, and parity remain incomplete. Next execute another
source-first child shard. TL0.6.4 M0 has since accepted a bounded
[harness-floor classification](lean-u2-native-surface-classification-tl0.6.4-m0-result-2026-07-23.md):
all 3,723 registered cases map exactly once to ten stable native surfaces, but
all source-content refinement, exact dependency closure, native outcomes,
pairs, and parity credit remain `not-run` or zero. This was the pre-M1 boundary:
M1-M3 had to refine and review the complete population before TL0.6.4 could
close. The accepted
[M1 result](lean-u2-native-surface-classification-tl0.6.4-m1-result-2026-07-23.md)
now inspects all 7,004 tracked files and retains 90,909 exact/candidate spans
over all 3,723 case projections. It is still source-only: 3,670 cases retain a
generated-wrapper residual, all exact dependency closures/native outcomes are
`not-run`, and pairs/parity remain zero. M2 and M3 remain open.

The accepted
[M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md)
now freezes the typed dependency/provider schema for all 3,723 cases, eight
selection sets, 111 official variants, and 408,374 factored case/variant
occurrences. It is deliberately an empty graph: providers are unbound,
resolver milestones and case closures are `not-run`, node/edge lists are
empty, no external process ran, and native/pair/parity credit remains zero.
M2.1-M2.7 exact closure and M3 review remain open.

M2.1's
[pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md)
now freezes 4,092 exact Lean source rows / 9,697,571 bytes, 32 deterministic
batches, 14 fast/full controls, and 39 sequential no-retry processes. The
runner and immutable-evidence verifier are pushed and gated, but attempt 001
has not run and its evidence root is absent. The preregistered R1 correction
adds live file-backed stream ceilings and sealed launch failures without
changing the frozen process program. Consequently no header edge or process
observation has been added; explicit authorization, evidence
validation, and offline promotion remain the next M2.1 steps.

M2.2's
[source-first resolution plan](lean-u2-native-dependency-tl0.6.4-m2.2-plan-2026-07-23.md)
is now preregistered. It freezes Lean 4.30 first-prefix candidate behavior,
the distinction between candidate selection and leaf existence/content,
absent-versus-empty search paths, the released source/artifact universe,
transitive module-data closure, the complete CLI process formula, and 18
controls. It deliberately freezes no M2.2 input authority or process budget
and records no observations, resolutions, native outcomes, pairs, or parity
credit. M2.2 may be bound only after M2.1 evidence is accepted under a
separate source-first checkpoint.

The subsequent
[M2.2 R1 correction](lean-u2-native-dependency-tl0.6.4-m2.2-effective-import-r1-plan-2026-07-23.md)
prevents the later implementation from equating that raw graph with Lean's
effective load behavior. The pinned loader joins `public`/`meta`/`all` state
across repeated paths, revisits upgraded descendants, can require IR without
module data, and reads exported/server/private `.olean` data only as an
ordered incremental prefix. R1 freezes those states, bounded cycle declines,
and added controls, but still supplies no M2.2 input, process, observation, or
credit.

M2.3's
[configured-runner/generated-artifact plan](lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md)
now freezes the next non-executing boundary. It reproduces the exact 3,670
generated-wrapper / 52 inline Lake / one direct-lint dispatch partition and
distinguishes configured CMake/CTest facts, shell-source/shared-state facts,
statically proved edges, observed trace edges, and downstream Lake/runtime/RPC
ownership. The wrapper route binds 41 registered paths resolving to 39 regular
runners through two tracked symlinks. No M2.3 input authority, process formula,
provider configuration, trace, edge, outcome, pair, or credit exists before
accepted M2.1/M2.2 results and a separate M2.3.1 authority.

M2.4's
[Lake workspace/project plan](lean-u2-native-dependency-tl0.6.4-m2.4-lake-project-plan-2026-07-23.md)
now preregisters executable configuration, manifest/override/materialization,
target/facet/job, query/setup, artifact/cache/network, and downstream ownership
semantics. The current read-only floor is 52 direct Lake cases with 70 tracked
configuration roots plus 28 wrapper-directory lexical candidates; M2.3 must
prove which candidates transfer. No M2.4 authority, process formula,
configured workspace, package/target edge, observation, outcome, pair, or
credit exists before accepted M2.1-M2.3 results and a separate M2.4.1
authority.

M2.5's
[compiler/runtime/FFI plan](lean-u2-native-dependency-tl0.6.4-m2.5-compiler-runtime-ffi-plan-2026-07-23.md)
now preregisters distinct frontend/compiler, `#eval`, IR-interpreter, C/LLVM,
native toolchain/artifact, ABI/symbol/initialization, runtime-effect, and
platform routes. Its source-only floor is 841 direct / 860 closure
compiler-runtime cases plus 24 provisional FFI cases, not an executable
denominator. No M2.5 authority, process, artifact, observation, outcome, pair,
performance row, or credit exists before accepted M2.1-M2.4 transfers and a
separate M2.5.1 authority.

M2.6's
[editor/server/RPC plan](lean-u2-native-dependency-tl0.6.4-m2.6-editor-rpc-plan-2026-07-23.md)
preserves accepted M1 as history while applying a downstream correction
overlay: eleven generic Lake JSON `version` fields had provisionally promoted
four non-server cases, so the qualified source floor is 143 rather than 147.
Of those, 137 have a server-process harness and six only compile or elaborate
server/RPC APIs. The plan binds raw duplex transport, lifecycle/capabilities,
document/version/edit schedules, snapshots/publication, cancellation,
watchdog/worker processes, restart, RPC sessions/references/widgets,
normalization, and the new `idbg` cross-boundary. No M2.6 authority, process,
transcript, observation, outcome, pair, performance row, or credit exists
before accepted M2.1-M2.5 transfers and a separate M2.6.1 authority.

M2.7's
[variant-merge and M3-handoff plan](lean-u2-native-dependency-tl0.6.4-m2.7-variant-merge-plan-2026-07-23.md)
freezes how accepted M2.1-M2.6 evidence must be joined without losing any of
the 408,374 exact case/variant identities. Structural content may deduplicate,
but ownership, conditions, assurance dimensions, declines, residuals, and
evidence remain per cell. Union, intersection, delta, and explicitly proved
equivalence are non-crediting views; no maximum-state merge can overwrite
static/configured/runtime provenance. The plan also retains M2.6's four-case
correction overlay and defines a deterministic all-row M3 queue. No M2.7 input
authority, accepted parent transfer, merged graph, closed cell, M3 acceptance,
outcome, pair, performance row, or credit exists.

M3.0's
[complete-row independent-review plan](lean-u2-native-surface-classification-tl0.6.4-m3-review-plan-2026-07-23.md)
now freezes the acceptance-review boundary without pretending the missing M2
parent exists. It requires explicit primary dispositions for all 3,723 case
rows and 408,374 applicable cells, plus independent secondary concurrence for
declines, corrections, equivalence proofs, intentionally-online routes, and
resolved contradictions. The campaign may resume across validated append-only
prefixes, but cannot sample, silently replay, or approve by representative.
Any evidence defect returns to a new M2 correction/result. No M3 authority,
assignment, event, disposition, TL0.6.4 acceptance, outcome, pair, performance
row, or credit exists.

TL0.6.5's
[matched official/Axeyum execution plan](lean-u2-matched-execution-tl0.6.5-plan-2026-07-23.md)
now fixes the comparison contract before either required parent exists. It
separates 3,723 case rows, 408,374 candidate execution slots, and the later
layer-expanded comparison-obligation denominator; represents official Lean and
native Axeyum as independent execution records; and makes normalization a
third completed comparison object. Typed absent/invalid sides keep `not-run`
and `invalid-run` rows visible. Exact per-population count/ID/cell-seal
authorities mean one all-agree subset cannot satisfy G3. R1 recomputes every
record/cell/population seal; R2 adds typed complete-side result classes and
separate official/Axeyum normalized-observable identities, then derives all
eight outcomes. Completion alone can no longer claim agreement. The accepted
[R3 normalization result](lean-u2-matched-execution-tl0.6.5-normalization-r3-result-2026-07-23.md)
adds nine sealed layer contracts, 68 selected semantic fields, 18 explicit ignored-field
rules, and exact-field canonical projection; paired cells must cite a current
registered same-layer contract. Raw extractors and semantic canonicalizers
remain zero. This is schema/validator/projection progress only: no comparison
obligation authority, Axeyum process, native outcome, pair,
performance row, or credit exists before complete accepted TL0.6.3 and
TL0.6.4 parents.

## 2. What the SMT-LIB comparison actually says

The solver program supplies a mature measurement warning for Lean parity:
multiple correct-looking totals can describe different populations, different
overlaps, or invalid runs.

| Evidence layer | Retained result | Credit boundary | Lean-roadmap lesson |
|---|---|---|---|
| Committed curated scoreboard | 992 files, 753 Axeyum decisions, 680 oracle comparisons, zero recorded disagreement; weak rows include QF_S 87/134, QF_SLIA 18/50, and QF_SEQ 26/33 | Credited only for those named baselines; not representative of all SMT-LIB | Never turn a bounded fixture aggregate into a whole-language percentage. |
| Hard public QF_BV p4dfa slice | Axeyum and the Z3 crate each decide 8/113 at the matched 20-second point, but overlap is six, with two Axeyum-only and two Z3-only; the separate Z3 CLI control decides nine | Bounded head-to-head; equal totals do not imply equal behavior | Publish exact paired identities and direction, not just totals. |
| Accepted official selection | 45,905 files / 15,148,369,947 bytes selected from the 450,472-file official corpus; S0-S4 complete | No solver score until S5 harness admission and a completed E1-E3 run | Population authority, execution authority, and outcome authority are separate gates. |
| Final stale diagnostic run | stopped at 33,305/64,345 cases (51.8%); no raw shard artifact; 56 literal wrong markers, split 25 `sat -> unsat` and 31 `unsat -> sat` | Zero correctness, coverage, or performance credit; only the first two markers were adjudicated | An incomplete run may discover bugs but cannot establish a rate. Wrong results outrank breadth and speed. |
| Checked finite-profile MBQI | accepted one-binder matrix: 256 direct-Z3 cases, 130 jointly decided, 110 replayed Axeyum SAT results, zero disagreement | The registered finite-profile fragment only | Search results count only after source-level replay/checking; focused differential matrices are not general quantifier parity. |
| Multi-binder MBQI follow-up | 64/64 focused direct-Z3 agreements, 32 SAT / 32 UNSAT, with SAT replay; branch-wide acceptance was still pending at the inspected snapshot | At most 16 `Int`/`Real` binders and 4,096 Cartesian tuples; no alternation, arbitrary repair, or Lean reconstruction | Name caps and declines as part of the supported profile instead of hiding them in a success total. |

The committed sources are the generated
[`SCOREBOARD.md`](../../bench-results/SCOREBOARD.md), the
[`p4dfa comparison`](gap-analysis-z3-lean-2026-07-21.md), and the
[`official S4 authority`](smtcomp-official-selection-final-s4-2026-07-22.md).
The final stale-run and current MBQI snapshots were inspected at repository
revision `2ca18c781f8147faa2c2af880f4662d3181cff3f`; see the immutable
[`full-workstream snapshot`](https://github.com/mjbommar/axeyum/blob/2ca18c781f8147faa2c2af880f4662d3181cff3f/docs/plan/smtcomp-full-library-workstream/README.md),
[`one-binder result`](https://github.com/mjbommar/axeyum/blob/2ca18c781f8147faa2c2af880f4662d3181cff3f/docs/plan/checked-finite-profile-quantified-uf-models-2026-07-22.md),
and
[`multi-binder result`](https://github.com/mjbommar/axeyum/blob/2ca18c781f8147faa2c2af880f4662d3181cff3f/docs/plan/checked-multi-binder-quantified-uf-models-2026-07-22.md).

This discipline matches external competition practice. SMT-COMP's Single Query
track presents one selected benchmark per solver process, permits `unknown`,
and uses a 20-minute wall limit per solver/benchmark pair
([2025 rules](https://smt-comp.github.io/2025/rules.pdf)); published results
report solved, unsolved, abstained, timeout, memory, correctness, and time
separately ([2025 results](https://smt-comp.github.io/2025/results/),
[2024 results](https://smt-comp.github.io/2024/results/)). Axeyum's Lean
comparison should be at least as explicit about selection, abstention,
termination, error, and correctness.

## 3. Claim levels

Keep these names distinct in code, dashboards, release notes, and discussion:

| Claim | Required meaning |
|---|---|
| bounded kernel/import compatibility | named K-profile and construct population only |
| official-adapter compatibility | official Lean performs the missing source/elaboration/workflow behavior; never fills a native cell |
| native subsystem compatibility | one named A-axis over named U-population subsets, with exact residuals |
| complete Lean 4.30 functional parity | all complete U0-U9 authorities and A0-A11 functional exits, with every terminal pair classified and no blocking mismatch |
| complete Lean 4.30 assurance parity | functional parity plus independent checking, trust/axiom closure, replay, malformed-input, and failure/recovery evidence |
| performance profile | separate matched time/RSS/artifact curves; never repairs a semantic disagreement or missing case |
| maintained Lean 4 parity | the pinned result plus current/current-minus-one release migration, regression, packaging, and support policy |

Lean 4.30.0 was released on 2026-05-26 and included material compiler, tactic,
server, and Lake changes
([v4.30.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/)).
The current release index already lists v4.31.0, v4.32.0, and v4.33.0-rc1
([release index](https://lean-lang.org/doc/reference/latest/releases/)).
Therefore this roadmap deliberately targets **complete v4.30 parity first**;
it cannot support a maintained-parity claim until the migration lane catches up.

## 4. Dependency-ordered implementation program

The phases below are cumulative. A phase may ship a bounded profile before its
terminal exit, but may not borrow completion from a later layer or from the
official adapter.

| Phase | Primary populations / axes | Prerequisites | Required deliverables | Exit and non-credit boundary |
|---|---|---|---|---|
| R0 — identity and evidence spine | all U; A0 | accepted target tuple and ADRs | complete population schemas, content identities, executable/environment/resource/attempt/completion records, paired taxonomy, generated dashboards, claim guard | Continues until every U row is authoritative. Inventory counts, source trees, or hand-written totals earn no terminal credit. |
| R1 — official execution breadth | U2, U8, U9; A0 | TL0.6.1/.2 registration and TL0.7 process/store policy | child-shard derivation, every active official profile/provider, immutable JUnit/log/artifact closure, retry/invalid-run accounting, failure campaigns | TL0.6.3 closes only when every selected official case has a valid completion. Retries do not increase unique coverage; an official pass has no native-pair credit. |
| R2 — kernel and import closure | U1, U3, U8; A1/A2/A9 | K0 plus fail-closed exporter boundary | String and quotient roots, complete declaration/core-term authority, invalid mutations, construct closure, `.olean`/export equivalence, large-stream durability, axiom classification | K1 closes with no supported official construct decline and zero unexplained admission/type/value difference. Exporter delegation still does not satisfy parsing or elaboration. |
| R3 — source, parser, syntax, macros | U2/U3/U7/U8; A3 | stable source maps and native term/environment targets | lexer/layout/UTF-8, dynamic syntax tables, Pratt parser, quotations, hygiene, macros, extensions, recovery, pretty-print normalization, incremental parse cases | Same normalized syntax/diagnostic results on the complete registered source profile. Parsing success alone cannot fill elaboration cells. |
| R4 — elaboration and declarations | U1/U2/U3/U7/U8; A4 | R2 core semantics and R3 syntax | metavariables, unification, coercions, typeclasses, commands, inductives, equations, structural/mutual/nested/well-founded recursion, termination, normalized diagnostics | Same core/environment/reject result, with every accepted declaration independently admitted. Fixture-level elaboration is not module or tactic parity. |
| R5 — goals, tactics, metaprograms | U2/U3/U7/U8; A5/A9 | R4 elaborator, explicit trust/evidence route | goal/metavariable state, tactic language, primitive/composite tactics, simplification/automation, metaprogram execution, proof-term/certificate production, replay | Registered goals have matching closure/open state and independently checked proof terms with explicit axioms. Oracle-produced proof success does not satisfy native tactics. |
| R6 — modules, artifacts, Lake | U0/U2/U3/U4/U7/U8/U9; A2/A6/A11 | R3-R5 plus stable environment serialization | module scopes/imports, `.olean`/`.ilean`, dependency graph, invalidation, clean/incremental/offline/cache builds, lockfiles, facets, package failure/recovery | Pinned project matrix reproduces without stale acceptance. A clean build alone does not establish incremental, offline, cache, or recovery behavior. |
| R7 — server, editor, RPC | U2/U5/U8/U9; A7 | R3-R6 incremental frontend/project state | snapshots, cancellation, diagnostics, info trees, goals, navigation, completion, semantic tokens, actions, widgets, stale-publication/security schedules | Normalized request/transcript matrix agrees with no stale result. Batch compiler output is not an LSP substitute. |
| R8 — evaluator, compiler, runtime, bootstrap | U0/U2/U3/U6/U7/U8/U9; A8/A11 | R2-R6 semantic and module closure | evaluator, erasure, IR/LCNF, passes, RC/object runtime, C/native/WASM, FFI, effects/exceptions, metaprograms, stage0/1/2 bootstrap equivalence | Observable outputs agree across declared backends/platforms and the selected toolchain rebuilds natively. Calling official `lean`/`leanc` is adapter evidence only. |
| R9 — libraries and mathlib | U3/U7/U8/U9; A9/A10 | R4-R8 usable language/toolchain | complete `Init`/`Std`/Lean-module closures, zero unclassified prelude assumptions, pinned mathlib modules/build/tests/tactics/declarations/resources | Full pinned tags build/test with no unclassified failure, trust gap, or missing population completion. A selected theorem suite is not mathlib parity. |
| R10 — platform, release, security, maintenance | U8/U9; A6-A11 | terminal candidates from R1-R9 | official support tiers, install/package/offline assets, malformed/adversarial/resource campaigns, reproducible distributions, migrations, current/current-minus-one policy | G1-G10 all derive satisfied from retained evidence. One pinned release does not become maintained parity without the rolling release matrix. |

## 5. Critical path and parallel lanes

The critical semantic path is:

`R2 kernel/import -> R3 parser/macros -> R4 elaborator -> R5 tactics -> R6 modules/Lake -> R8 compiler/runtime -> R9 mathlib`

Three lanes should proceed alongside it without claiming to shorten that
dependency chain:

- R1 expands official U2 execution. TL0.6.4 M0 supplies every case's
  conservative harness floor and accepted M1 supplies the complete tracked-
  source census. Accepted M2.0 supplies only the typed empty-graph/provider
  contract; M2.1's input/process authority is ready but unexecuted, and
  M2.1-M2.7 must still derive exact closure before M3 review.
- R0 keeps identities, completion rules, pair schemas, and dashboards ready so
  new capabilities become auditable evidence rather than anecdotes.
- R7 and R10 preregister editor, adversarial, platform, package, and migration
  populations before the dependent implementation is ready.

The best next implementation priority remains the deepest blocker shared by
many populations, not the easiest count increase. The current shared blockers
are K1 import closure, the native parser/elaborator boundary, complete U2
execution, and content/dependency-complete U2 classification.

## 6. Immediate next ten actions

1. Treat the R3 singleton and accepted R6 shard as closed immutable history;
   never rerun either to manufacture coverage.
2. Select and preregister the next fresh deterministic child shard, preserving
   exact unique-case accounting and the one-process/no-retry discipline.
3. Retain accepted TL0.6.4 M1's 7,004-file/3,723-case source census and M2.0's
   typed empty-graph/provider contract as provisional evidence; do not
   reinterpret lexical signals, schema rows, or variant counts as reachability.
4. Explicitly authorize, execute once, and validate TL0.6.4 M2.1's exact
   39-process fast/full header pass; then bind and execute M2.2-M2.7 module,
   generated-artifact, runtime, library, FFI, request, and project closures.
   M2.2-M2.7 plans freeze semantics only: none is an accepted input authority,
   parent transfer, closure result, or execution permission. Do not infer FFI
   absence from M0 or closure from M2.0/pre-execution M2.1.
5. After an accepted M2.7 result, bind M3.1 and review every case and applicable
   variant under the preregistered independent-review contract. Accept TL0.6.4
   only when every disposition/concurrence is complete and no provisional
   field, unknown surface, or silent official-Lean delegation remains.
6. Repair and attest the remote official-Lean executable identity across
   changed working directories without converting official evidence into
   native parity credit.
7. Close K1's String-literal and quotient-package roots, regenerate the
   construct matrix, and preserve fail-closed decline codes for anything still
   unsupported.
8. Register the dependency-closed U3 `Init`/`Std`/Lean-module population and
   classify/discharge the 65 prelude assumptions instead of treating import
   counts as trust closure.
9. Land the native source/syntax substrate and first end-to-end
   source-to-independent-kernel cell before widening tactics or mathlib.
10. After complete accepted TL0.6.3/TL0.6.4 parents, derive TL0.6.5's exact
    comparison-obligation count, sorted-ID digest, and sorted cell-seal digest
    before any native launch;
    then form the first official/Axeyum U2 pair with separate side identities,
    exact normalization, assurance, resources, and raw comparison evidence.
    Report overlap direction even when both totals are equal, retain every
    missing/invalid obligation, and keep the public complete/full/100% guard
    closed until its switch derives true.

## 7. The terminal claim switch

An unqualified complete Lean 4.30 parity statement is permitted only when the
registry derives this conjunction; none may be overridden by prose:

- G1: all U0-U9 populations are complete, reproducible authorities;
- G2: all A0-A11 axes satisfy their complete-population exits;
- G3: every terminal paired cell is complete and classified as
  `agree-success` or `agree-reject`, with no missing, invalid, unadjudicated, or
  mismatched cell;
- G4: the complete Lean build/test/bootstrap profile passes;
- G5: the complete pinned mathlib profile passes;
- G6: every accepted declaration/proof has the required independent checking,
  replay, axiom, and trust evidence;
- G7: malformed-input, resource, interruption, retry, cache, and stale-state
  campaigns pass without unsafe acceptance or publication;
- G8: every declared official platform/support-tier profile passes;
- G9: functional, assurance, and separately reported performance evidence are
  published from the same paired identities; and
- G10: reproducible release artifacts, limitations, migrations, support, and
  maintenance policy are published.

Until all ten derive true, the correct summary is: **complete Lean 4.30 parity
not established**.
