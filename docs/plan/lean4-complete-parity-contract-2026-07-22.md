# Complete Lean 4.30 parity contract and execution roadmap

Status: **active terminal definition under accepted ADR-0345; implementation
incomplete**

Date: 2026-07-22

Pinned target:

- Lean `v4.30.0` at
  `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- `lean4export` `v4.30.0`, format `3.1.0`, at
  `a3e35a584f59b390667db7269cd37fca8575e4bf`; and
- mathlib `v4.30.0` at
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Parent strategy:
[Lean-system compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md)
and [ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md).

Executable task graph:
[Lean 4.30 system implementation plan](lean-system-implementation-plan-2026-07-21.md).

Dependency-ordered parity program:
[complete Lean 4 parity execution roadmap](lean4-complete-parity-roadmap-2026-07-22.md).

Executable terminal registry:
[`lean-complete-parity-v1.json`](lean-complete-parity-v1.json), its generated
[human-readable status](generated/lean-complete-parity.md), and the generated
[content-identified report](generated/lean-complete-parity.json).

## 1. Verdict and purpose

Axeyum is **not 100% done with Lean parity**. TL2.14 completed one important
kernel/import slice: the registered nested-inductive population now admits and
computes through the independent Rust checker. That result does not implement
Lean source parsing, macro expansion, elaboration, tactics, module builds,
Lake, the compiler/runtime, the language server, or mathlib.

This document defines what an eventual unqualified claim of **complete Lean
4.30 parity** would require. It does not replace the useful lower profiles in
the existing K0-K6 matrix, and it does not delay shipping them. It supplies the
terminal contract that those profiles accumulate toward.

The central rule is:

> Complete parity is a conjunction of versioned behavioral profiles over a
> complete, content-identified population. It is never inferred from one
> passing fixture, one subsystem, equal totals, source-file counts, or an
> adapter that delegates the missing behavior to official Lean.

## 2. Current bounded state

The generated
[Lean compatibility matrix](generated/lean-compatibility.md) currently records:

| Profile | Meaning | Satisfied rows | Total rows |
|---|---|---:|---:|
| K0 | independent checker | 1 | 1 |
| K1 | versioned declaration import | 4 | 5 |
| K2 | native source parsing and elaboration | 0 | 2 |
| K3 | native goals and checked tactics | 0 | 1 |
| K4 | project and editor workflow | 0 | 1 |
| K5 | evaluator/compiler/runtime | 0 | 1 |
| K6 | pinned ecosystem/mathlib | 0 | 1 |

The complete-parity registry derives the current implementation-ledger counts
directly from the task table instead of copying a second aggregate here. Those
counts are an **unweighted task inventory**, not a percentage of Lean. A
two-day contract task and a multi-month compiler task both count as one row.

The same registry currently reports zero complete U0-U9 authorities, zero
complete A0-A11 axes, zero registered terminal paired cells, and zero satisfied
terminal gates. It separately retains the bounded K-profile, selected-
construct, and axiom-ledger facts below. That is deliberate: making the
terminal denominator explicit must not promote the evidence already in hand.

The current positive evidence remains valuable:

- the independent kernel and importer pass exact K0/K1 fixture profiles;
- the selected official construct matrix has seven rows, six independently
  admitted rows, four computation-checked rows, and zero current transactional
  declines;
- the local official-Lean solver-proof gate accepts 71/71 representative
  generated modules; and
- TL2.11-TL2.14 close strict positivity, recursive induction hypotheses,
  mutual groups, and nested-inductive expansion for their registered
  populations.

The current negative evidence is equally binding:

- String literals and the quotient package remain unsupported K1 roots;
- no K2-K6 row is satisfied;
- all 65 reconstruction-prelude assumptions remain semantically unclassified;
  and
- the first post-repair remote Lean job did not reach the representative
  solver-proof sweep. It failed in the strict-positivity cross-check because
  `AXEYUM_LEAN_BIN` named an elan shim that had no default toolchain when the
  test changed working directory. The retained
  [job log](https://github.com/mjbommar/axeyum/actions/runs/29951909263/job/89031426984)
  is a failed remote gate, not 71/71 remote credit.

## 3. What the SMT-LIB comparison teaches this roadmap

Axeyum's SMT-LIB evidence already demonstrates why a single parity percentage
is unsafe:

- the 35-row regression scoreboard decides 753/992 files with 680 oracle
  comparisons and zero recorded disagreements, but it is not a representative
  SMT-LIB population;
- the harder 228-file convenience inventory has 78 known-status agreements,
  four unadjudicated decisions, 144 declines, and two no-answer outcomes;
- Axeyum and the Z3 crate both decide 8/113 p4dfa files at 20 seconds, but the
  actual overlap is six joint, two Axeyum-only, and two Z3-only decisions;
- the 30-row command/API matrix has direct engines and helpers while still
  reporting zero complete interactive textual-session rows; and
- the accepted official selection contains 45,905 files / 15,148,369,947 bytes
  from a 450,472-file corpus, but still needs S5 harness admission before any
  solver run can receive score credit; and
- the old 64,345-file run stopped at 33,305 cases without a raw shard artifact
  and contains 56 literal wrong markers. It remains useful bug-discovery input,
  but receives zero correctness, coverage, or performance credit because its
  selection and E1-E3 execution evidence were incomplete.

Focused quantifier evidence has the same boundary. The accepted one-binder
finite-profile MBQI gate retained 256 direct-Z3 cases, 130 jointly decided
outcomes, 110 replayed Axeyum SAT models, and zero disagreement. A later
multi-binder matrix retained 64/64 focused agreements, but caps the fragment at
16 `Int`/`Real` binders and 4,096 Cartesian tuples. Neither focused result is a
general-quantifier or Lean-reconstruction claim. The execution
[roadmap](lean4-complete-parity-roadmap-2026-07-22.md#2-what-the-smt-lib-comparison-actually-says)
records the exact evidence layers and immutable source revisions.

The Lean program adopts the same rules:

| SMT-LIB lesson | Lean parity rule |
|---|---|
| Equal solved counts can hide different solved sets. | Compare the exact same source, declaration, project, request, and runtime cases; publish overlap and direction, not only totals. |
| Parser/API helpers do not imply an ordered textual session. | Kernel/import success does not imply parser, elaborator, tactic, Lake, LSP, or runtime compatibility. |
| A convenience corpus is not an official selection. | Small fixtures and 71 generated modules are bounded profiles, not the Lean or mathlib population. |
| Raw paths, normalized paths, exact contents, and source families are different denominators. | Source files, modules, declarations, dependency closures, test cases, tactic invocations, and request transcripts remain separate identities. |
| A diagnostic run without selection/resource/attempt evidence earns no score. | An official-Lean observation without exact pins, artifacts, completion, resources, and retained outcomes earns no compatibility credit. |
| Known-status agreement and unadjudicated decisions must be separated. | Independent kernel admission, official admission, source elaboration, proof checking, workflow reproduction, and runtime reproduction stay separate assurance fields. |
| Wrong verdicts outrank performance. | Unsound acceptance, stale publication, or semantic mismatch blocks parity before coverage or speed is discussed. |

This methodology is stricter than “run the upstream tests and count green.” It
first defines the population and observable equivalence, then runs both systems
under matched conditions, and retains every disagreement or unclassified row.

## 4. Meaning of complete parity

### 4.1 Complete Lean 4.30 parity

For the pinned release, Axeyum has complete behavioral parity only when its
**native** profile can consume the registered official inputs and reproduce the
registered observable behavior across every axis in section 6, while every
accepted declaration and proof is independently checked by Axeyum's Rust
kernel.

Implementation identity is not required. Axeyum need not use Lean's internal
data structures, C++ kernel, compiler passes, memory layout, or undocumented
byte encodings. Where exact bytes are not a public contract, the roadmap uses a
declared semantic normalization instead.

The optional official-Lean adapter remains useful, but it cannot fill a native
parity cell. It receives a separate `official-adapter` profile and serves as an
oracle, exporter, and early workflow bridge.

### 4.2 Maintained Lean 4 parity

“Complete Lean 4.30 parity” is one pinned-release result. The stronger phrase
“maintained Lean 4 parity” additionally requires:

- current and current-minus-one release profiles;
- explicit source/export/cache migrations;
- a reproducible upgrade/downgrade matrix;
- no unclassified regression between supported releases; and
- published compatibility and deprecation policy.

Passing v4.30.0 once does not establish perpetual compatibility with later Lean
releases.

### 4.3 Functional, assurance, and performance parity

These remain three distinct claims:

- **Functional parity:** matched accepted/rejected behavior and observable
  results over the complete registered population.
- **Assurance parity:** every accepted proof/declaration has the declared
  independent checking, axiom, trust, and replay evidence.
- **Performance parity:** matched time/RSS/artifact-size curves under the same
  hardware and limits.

Complete functional parity does not mean identical speed. Performance is
reported separately and must still satisfy usable release budgets; it is never
allowed to erase a semantic disagreement or unexecuted case.

## 5. Pinned upstream authority and populations

The upstream tag is an authority only after its executable populations are
derived and content-bound. A Git tree count is useful inventory, not a test
denominator.

Fresh GitHub API inspection of the pinned Lean tree records:

| Inventory | Pinned tree count | Interpretation |
|---|---:|---|
| `src/Lean/Parser/` | 17 blobs | parser implementation scale, not parser cases |
| `src/Lean/Elab/` | 300 blobs | elaboration implementation scale |
| `src/Lean/Meta/` | 417 blobs | meta/unification/tactic support scale |
| `src/Lean/Server/` | 45 blobs | server implementation scale |
| `src/Lean/Compiler/` | 117 blobs | compiler implementation scale |
| `src/lake/` | 160 blobs | Lake implementation scale |
| `stage0/` | 2,561 blobs | bootstrap artifact/source inventory |
| `tests/` | 6,931 blobs, including 4,035 `.lean` files | raw test-tree inventory; not 6,931 test cases |
| mathlib tag | 8,606 `.lean` files | 8,094 under `Mathlib/`, 375 under `MathlibTest/` |

The Lean test suite explicitly distinguishes test directories from test piles;
the executable denominator must therefore be derived from CMake registration,
`run_test.sh`, pile extensions, per-test configuration, and expected-output
files rather than by counting files. The authoritative full-profile populations
are:

| Population | Required identity and outcome |
|---|---|
| U0 — toolchain/bootstrap | source tag/commit, stage0 inputs, stage1/stage2 build graph, compiler/runtime identities, tests, and bootstrap equivalence |
| U1 — kernel/core | complete supported declaration/core-term corpus, positive and invalid mutations, normalized types/values, accept/reject result, axiom/trust identity |
| U2 — official Lean tests | exact CTest/test-pile manifest, source/support/expected-output hashes, command, environment, exit/output class, and both-system outcome |
| U3 — core libraries | complete dependency-closed `Init`, `Std`, and Lean implementation module manifests with declaration/environment identities |
| U4 — Lake/projects | complete pinned Lake test manifest plus clean, incremental, offline, dependency, cache, and failure/recovery project cells |
| U5 — server/editor | complete pinned server and server-interactive request manifests, normalized transcripts, versions, cancellation/edit schedules, and stale-result checks |
| U6 — runtime/compiler | interpreter, compiled C/native, WASM, effects, exceptions, allocation, FFI, metaprogram, and executable-output comparisons |
| U7 — mathlib | all pinned mathlib modules, dependency closures, `lake build`, `lake test`, tactic profiles, declarations, axioms, runtime/build outcomes, and resources |
| U8 — adversarial/security | malformed source/export/cache/protocol inputs, resource exhaustion, crash/panic, stale publication, and checker-disagreement campaigns |
| U9 — platforms/releases | every official platform at its pinned-release support tier, published release-asset shapes, packaging/install/offline cells, and current/current-minus-one migration profiles |

### 5.1 U2 registration and workflow-profile checkpoints

The first U2 derivation is now retained in the
[official-test registration authority](lean-u2-test-authority-2026-07-22.md),
its [machine-readable case manifest](lean-u2-test-authority-v1.json), and its
generated [summary](generated/lean-u2-test-authority.md). Pinned Lean's own
CMake registration yields 3,678 default cases and 3,723 cases with
`LAKE_CI=ON`; the latter adds 45 Lake directories. The 3,723-case selection is
content-bound to 7,004 Git-tracked test/example files, exact normalized CTest
commands and properties, primary and sidecar identities, output policies, and
over-approximating support subtrees. The 3,660 pile glob candidates close as
3,639 registered, seven `.no_test` exclusions, three runner-name exclusions,
and eleven benchmark-only cases with no test runner.

This advances U2 from raw inventory to a bounded registration profile only.
The follow-up [TL0.6.2 result](lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md),
[machine-readable profile authority](lean-u2-official-ci-profiles-v1.json), and
generated [summary](generated/lean-u2-official-ci-profiles.md) now derive the
pinned dynamic workflow into 17 official-repository contexts, nine active job
literals, 153 candidate cells, 111 not-run CTest attempts, and eight exact
factored selection sets. Disabled/commented/packaging jobs, primary versus
unfiltered stage-1 rebootstrap commands, presets, filters, stage-3/benchmark
flags, and configuration identities remain distinct. In particular, release
check level 3 does not imply `LAKE_CI=ON`; that switch is controlled separately
by the `lake-ci` pull-request label.

Both registration authorities deliberately record zero official executions,
zero completed official cases, zero Axeyum executions, and zero paired cells.
Executable,
environment, resource, attempt, completion, log, JUnit, and artifact evidence
belongs to TL0.6.3 after TL0.7; native surface classification and matched
Axeyum execution belong to TL0.6.4/TL0.6.5. U2 cannot become
`complete_authority` until the complete declared profile matrix and matched
native outcomes are retained case by case and reviewed under TL0.6.6.

TL0.6.3 has since retained the first bounded local official-case history. The
accepted [R3 result](lean-u2-official-execution-tl0.6.3-m0-r3-result-2026-07-22.md)
contains four process attempts, two incomplete attempts, and two official
outcomes for the same unique `compile/534.lean` case: one adapter-induced
failure and one pass with the released bundled compiler/linker. Unique parent
coverage remains 1/3,678. No provider profile is complete, and Axeyum outcomes,
paired cells, performance rows, complete axes, terminal gates, and parity credit
remain zero.

The initial unqualified full profile requires the official Tier-1 test matrix
for the pinned release and build/package cells for every official Tier-2
target, with the weaker upstream support tier preserved rather than silently
promoted. The v4.30.0 release publishes macOS x86-64/AArch64, Linux
x86-64/AArch64, and Windows x86-64 archives; WebAssembly remains a separately
declared cross-build/runtime cell. A narrower platform set may be useful and
shippable, but must be named and cannot use the unqualified word “complete.”

## 6. Complete parity axes

Every axis has an independent denominator and exit. A green lower axis never
fills a higher one.

| Axis | Required behavior | Existing owner | Terminal exit |
|---|---|---|---|
| A0 — identity and measurement | pins, complete population manifests, exact contents, normalized identities, commands, resources, attempts, completion | L0 | every U0-U9 row is generated from retained evidence; no hand-copied aggregate controls status |
| A1 — kernel semantics | levels, expressions, declarations, reduction, definitional equality, proof irrelevance, inductives, quotients, literals, safety flags | L2/T6.0 | complete registered core differential has zero unexplained accept/reject/type/value differences and no `False` admission |
| A2 — import and serialization | fail-closed `lean4export`, environment identity, large-stream durability, `.olean` adapter equivalence | L1/TL7.9 | complete pinned wire population translates/admit-or-declines stably; full profile has no supported official construct decline |
| A3 — parser, syntax, macros | UTF-8/source maps, dynamic Pratt tables, quotations, hygiene, builtin/user extensions, recovery, printing | L6 | normalized syntax/macro corpus agrees, including incremental and failing sources |
| A4 — elaboration and declarations | metavariables, unification, coercions, typeclasses, commands, inductives, equations, structural/mutual/nested/well-founded recursion, termination | L4 | normalized core/environment/diagnostic results agree for the complete source profile |
| A5 — goals, tactics, automation | tactic state, primitive/composite tactics, source tactic elaboration, certificate tactics, metaprograms | L5/Track 6 | same registered goals close or remain open; emitted proof terms independently check; axiom/trust sets agree |
| A6 — modules, caches, Lake | imports, public/private/meta scopes, initialization, artifacts, dependency resolution, facets, lockfiles, offline builds, `.olean`/`.ilean` behavior | L7 | clean/incremental/offline project matrix reproduces with correct invalidation and no stale acceptance |
| A7 — editor and RPC | snapshots, cancellation, diagnostics, info trees, goals, navigation, completion, tokens, actions, widgets | L8 | normalized official/native transcript matrix has no stale result or unexplained response difference |
| A8 — evaluator, compiler, runtime | interpreter, erasure, IR/LCNF, passes, RC/object runtime, C/native/WASM, FFI, metaprograms, bootstrap | L9 | observable outputs agree across declared backends/platforms and selected Lean components rebuild through the native stack |
| A9 — libraries and trust closure | reconstruction preludes, `Init`, `Std`, selected theorem bases, axiom classification/discharge | L3 | dependency-closed profiles admit; zero unclassified assumptions; retained axioms are explicit profile inputs |
| A10 — mathlib ecosystem | complete source/build/test/tactic/module profile for the pinned mathlib release | L10 | full tag builds and tests with zero unclassified failures and exact axiom/trust/resource dashboards |
| A11 — toolchain, CLI, platform, release | `lean`/`lake`/checker-compatible user workflows, install/package artifacts, supported platforms, migrations, maintenance | L0/L7/L9/L10 | fresh and offline distributions pass U9; version policy and current/current-minus-one matrix are published |

## 7. Paired comparison record

Every comparison cell must retain at least:

- target release/commit and population ID;
- normalized case ID, exact source bytes, dependency-closure digest, and source
  family;
- official and Axeyum executable/configuration identities;
- command, environment, platform, resource envelope, attempt, and completion
  identities;
- layer being compared and the declared normalization;
- official outcome, Axeyum outcome, assurance fields, diagnostics, duration,
  peak RSS, and artifact sizes; and
- links to raw output and independently checked artifacts.

The result taxonomy is:

| Class | Meaning | Parity consequence |
|---|---|---|
| `agree-success` | both systems succeed and normalized observables agree | positive functional credit; assurance credit remains separate |
| `agree-reject` | both reject the invalid/unsupported input with compatible class and state | negative compatibility credit |
| `official-only` | official Lean succeeds; Axeyum rejects, declines, times out, or exhausts resources | missing capability; blocks full profile |
| `axeyum-only` | Axeyum accepts while official Lean rejects | compatibility disagreement; soundness-critical at kernel/admission boundaries |
| `semantic-mismatch` | both succeed but core, environment, proof, output, state, or transcript differs beyond the registered normalization | blocks parity |
| `unadjudicated` | the oracle/equivalence rule cannot decide whether outputs agree | no parity credit |
| `not-run` | identity, preflight, execution, or completion is absent | no parity credit |
| `invalid-run` | pin, population, environment, resource, attempt, or artifact evidence is inconsistent | retain diagnostically; zero parity credit |

Totals are always accompanied by exact overlap. `agree-success = N` alone is
insufficient without the `official-only`, `axeyum-only`, mismatch,
unadjudicated, and not-run denominators.

### 7.1 TL0.7.1 execution-evidence checkpoint

The [TL0.7.1 result](lean-execution-evidence-tl0.7.1-2026-07-22.md),
[machine authority](lean-execution-evidence-v1.json), and generated
[summary](generated/lean-execution-evidence.md) now make the resource/attempt/
completion portion of this record executable as a contract. Two explicit
local lane templates cover 4 GiB standard and 8 GiB official-export processes;
twelve termination classes distinguish exit, signal, wall/CPU timeout,
memory/PID/disk limit, cancellation, runner loss, launch/preflight failure, and
unknown termination. Limit classes require matching enforcement evidence.

Run identity precedes launch; attempts, cases, and raw artifacts are immutable;
resume retains terminal-less attempts; completion is installed last over exact
record-set digests. CTest/JUnit, logs, runner labels, provider conclusions, and
expiring artifacts do not independently prove completion. Five synthetic
controls and nineteen mutation classes validate representation only. Every real
run/outcome/pair/performance counter remains zero, so TL0.7.1 grants no U2 or
terminal credit. TL0.7.2 and TL0.7.3 prove bounded process and local
process-interruption behavior; TL0.7.4 now exercises the complete path with
two no-credit real controls and satisfies the local prerequisite to TL0.6.3.

TL0.7.2 is now complete under its
[source-first process-adapter plan](lean-execution-process-adapter-tl0.7.2-plan-2026-07-22.md)
and [bounded result](lean-execution-process-tl0.7.2-2026-07-22.md). Eight of
eight synthetic controls retain 40 exact files and sixteen raw streams across
both registered `RLIMIT_AS` lanes, including a descendant-bearing timeout with
no live group member after cleanup. The result still has zero case/completion
records, U2 outcomes, paired cells, performance rows, and parity credit.
TL0.7.4 subsequently satisfied the remaining local policy prerequisite.

TL0.7.3 is now complete under its
[source-first checkpoint-store plan](lean-execution-store-tl0.7.3-plan-2026-07-22.md)
and [bounded result](lean-execution-store-tl0.7.3-2026-07-22.md). Sixteen of
sixteen dependency/completion persistence-boundary cells reaped their workers
by `SIGKILL` across the observed ext4 worktree and `/dev/shm` tmpfs classes;
every interrupted/resumed canonical projection equals its uninterrupted
reference. The authority retains 65 exact files and still records zero real
outcomes, completed U2 cases, paired cells, performance rows, and parity
credit. This is local process-interruption evidence, explicitly not power or
host loss, NFS, provider, object, or distributed durability. TL0.7.4
subsequently satisfied the remaining local policy prerequisite.

TL0.7.4 is now governed by a
[source-first acceptance plan](lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md).
It freezes two empty-selection, no-credit external controls before execution:
compile the committed flat probe with the exact pinned Lean binary under the
4 GiB lane, then export the owned `.olean` with source-built official
`lean4export` v4.30.0 under the 8 GiB lane and require byte equality with the
committed 65-line stream. The exact official exporter preparation build has
completed from a clean tree; a preregistration amendment corrects a
62-character flat-source digest transcription. The first compile control ran,
failed before `.olean` creation because default task-stack reservations
exceeded the 4 GiB address-space envelope, and installed no completion. The
exporter did not run. Its [failed result](lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md)
and source-first [R1 plan](lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md)
freeze the exact diagnosis, `-s524288` retry, and terminal-before-artifact
retention. The [final result](lean-execution-acceptance-tl0.7.4-2026-07-22.md)
then completed both R1 controls from published source revision `679f4b9d`:
the 4 GiB compile produced a 9,672-byte `.olean`, the 8 GiB official exporter
produced the exact committed 3,849-byte/65-line stream, and all process groups
were reaped. The [authority](lean-execution-acceptance-v1.json) retains the
failed attempt plus both completions as 67 files / 142,523 bytes. None of
these processes creates a U2/Axeyum outcome, denominator, paired cell,
performance row, or terminal credit. TL0.7 is complete and TL0.6.3 is
unblocked; the parity scoreboard remains at zero complete populations, axes,
paired cells, and terminal gates.

TL0.6.3 M0 is now governed by a
[source-first official-case plan](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md).
It selects `compile/534.lean` as a singleton child shard of the exact
release-tag Linux-release 3,678-case selection and registers a separate local
8 GiB/one-worker CTest lane. The [R1 result](lean-u2-official-execution-tl0.6.3-m0-r1-result-2026-07-22.md)
retained two process attempts and one decided local official failure: the
adapter forced `leanc` through system `cc`, while the released toolchain
compiler links the retained generated C successfully. The
[R2 plan](lean-u2-official-execution-tl0.6.3-m0-r2-plan-2026-07-22.md)
removed only that override, but attempt 003 failed before importing the runner
because direct-file Python execution exposed the script directory instead of
the repository root. The preregistered R3 correction then executed attempt 004
once and passed the exact singleton with the released bundled compiler/linker.
The accepted [R3 authority](lean-u2-official-execution-tl0.6.3-m0-r3-v1.json),
[result](lean-u2-official-execution-tl0.6.3-m0-r3-result-2026-07-22.md), and
generated [summary](generated/lean-u2-official-execution-tl0.6.3-m0-r3.md)
retain four process attempts, two incomplete attempts, one failed and one
passed official outcome, but only one unique observed case. That does not
complete the parent official profile, claim its provider, create an Axeyum
outcome or pair, publish performance evidence, or advance any complete
population, axis, or terminal gate.

The source-first [M1 shard plan](lean-u2-official-execution-tl0.6.3-m1-shard-plan-2026-07-22.md)
and accepted [result](lean-u2-official-execution-tl0.6.3-m1-shard-result-2026-07-22.md)
now derive a complete scheduling projection without executing a test. The
[machine authority](lean-u2-official-child-shards-v1.json) factors the eight
selection identities into five exact ordered memberships and partitions them
into 289 contiguous physical shards capped at 64 cases: 461
selection-expanded and 6,451 attempt-expanded shard occurrences. All 111
attempt bindings and every new shard remain `not-run`. The historical M0 case
is annotation only, so this derivation changes no U2 outcome, pair,
performance, population, axis, gate, or parity credit.

The pushed [M2 execution plan](lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md)
now selects the lowest-ordinal 64-case shard with no historical observation and
freezes one local attempt. The pushed
[offline implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-implementation-2026-07-22.md)
records commit `9783ba93`: a pure fail-closed spec/harness/discovery/JUnit/
artifact/credit contract with thirteen focused tests and deliberately no live
execution command. Commit `57dcf343` adds the pushed 64-case completion-last
immutable store and four focused store tests, also without a launch command.
No live harness discovery or process has run; these checkpoints therefore
change none of the preceding outcome counts or claims. Commit `d1f144d4`
corrects case-before-post ordering, and commit `431d3959` implements, tests,
commits, and pushes the one-shot runner. Its first invocation stopped during
selected-source preflight before harness construction, discovery, prelaunch,
or child process because the official compile-bench runner is the pinned
`tests/compile_bench/run_test.sh -> ../compile/run_test.sh` link rather than a
regular manifest row. No evidence root exists and the process attempt remains
unconsumed. The source-first
[R1 correction plan](lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-plan-2026-07-22.md)
freezes exact manifest-only one-hop relative-link resolution, mutation gates,
a fresh work root, and no other execution or credit change before another
read-only preflight. The separately pushed
[R1 implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-implementation-2026-07-22.md)
records commit `9d5d40c8`, exact link/target binding, fifteen mutation
variants, complete offline validation, and no new work root or live surface at
that checkpoint. The subsequent
[R1 result](lean-u2-official-execution-tl0.6.3-m2-r1-result-2026-07-22.md)
retains one consumed process and exact 64-row JUnit (30 pass / 34 fail), but a
family-blind docparse artifact rule stopped before post/projection/completion.
All 64 rows remain diagnostic and M2 case/shard credit is zero.
The published
[R2 diagnostic-closure plan](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-plan-2026-07-22.md)
authorizes no process and no retroactive credit. It binds the exact 124-row /
950,327,258-byte generated manifest, retains only 67 outcome/log payloads /
106,610 bytes, and records 56 reproducible C/executable intermediates /
950,219,754 bytes as metadata-only evidence. The accepted
[R2 result](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-result-2026-07-22.md)
records the completion-last zero-process append: 69 new files / 159,346 bytes,
152 whole-root files / 5,307,372 bytes, and unchanged invalid R1 credit. The
source-first
[R3 attempt-002 plan](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-plan-2026-07-23.md)
now freezes new run/work/evidence roots, universal
`LEAN_STACK_SIZE_KB=524288`, the unchanged 64-case/8 GiB/one-worker/hour lane,
and the family-specific tiered store. It authorizes at most one new process
only after its implementation and offline gates are separately committed and
pushed. The separately pushed
[R3 implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-implementation-2026-07-23.md)
records commit `d47dacc6`, the exact stack-aware runner and tiered store, 6/6
focused and 264 aggregate Lean tests, and a harmless released-Lean probe that
observed `524288` without constructing the selected harness. Final clean,
tracking, remote, root, and hash preflight remains before the one allowed
invocation. That preflight subsequently passed at revision `0a4d5daa`, and R3
ran once. The accepted
[R3 result](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-result-2026-07-23.md)
retains a 3,600,038 ms wall timeout after seven diagnostic CTest passes and a
dedicated-thread-creation/channel-deadlock symptom. The group was reaped; the
17-file evidence root has no JUnit, cases, post, projection, or completion.
R3 is consumed with no retry and zero M2 case/shard credit. All
parent/provider/Axeyum/pair/performance/parity counters remain zero.

## 8. Layer-specific equivalence

One byte-comparison rule cannot cover the entire system:

- **Parser/macros:** compare canonical syntax kind/payload/source relationships
  and hygiene after an explicit scope-ID normalization; retain recovery nodes
  and diagnostics.
- **Elaboration:** compare declarations and core expressions modulo alpha-
  renaming and other preregistered non-semantic identifiers; separately compare
  messages, source ranges, info trees, and environment extensions.
- **Kernel:** compare accept/reject, inferred type, definitional equality,
  normal forms, recursor/projection rules, and axiom/trust closure. Axeyum's
  independent checker is authoritative for Axeyum admission.
- **Tactics:** compare final goals and independently checked theorem terms.
  Search traces and timing are separate unless the profile makes them public.
- **Modules/caches:** compare dependency and declaration/environment identities,
  visibility, initialization, and invalidation. `.olean` bytes are versioned
  implementation artifacts, not presumed canonical semantic bytes.
- **Runtime/compiler:** compare exit, stdout/stderr, declared files/effects,
  values, exceptions, and resource termination across interpreter and compiled
  routes.
- **LSP/RPC:** compare normalized request/response transcripts at exact document
  versions, including cancellation and stale-result suppression. Timing and
  transport-generated IDs are normalized separately.
- **Lake/projects:** compare resolved dependency graph, revisions, build targets,
  artifact identities, command exits, incremental invalidation, and offline
  behavior.
- **Mathlib:** compare complete module/build/test outcomes, declaration and
  axiom closures, tactic results, and runtime tests. File presence is inventory
  only.

Every normalization requires a mutation test proving that semantic changes are
not erased.

## 9. Terminal “100%” gate

The unqualified statement “Axeyum has complete Lean 4.30 parity” is permitted
only when all of the following are true at one published revision:

1. U0-U9 have complete, content-addressed, independently reproducible
   manifests and no selection is inferred from an incomplete run.
2. A0-A11 all pass; no axis is `TODO`, `PARTIAL`, `BLOCKED`, or substituted by
   the official adapter.
3. Every registered paired cell is `agree-success` or `agree-reject`; there are
   zero `official-only`, `axeyum-only`, `semantic-mismatch`, `unadjudicated`,
   `not-run`, or `invalid-run` cells.
4. The complete pinned Lean build/test/bootstrap population passes, including
   positive, expected-failure, compiler/interpreter, Lake, package, and server
   tests.
5. The complete pinned mathlib build and declared test/tactic/runtime profile
   passes with zero unclassified dependency, axiom, or failure rows.
6. Every accepted declaration and proof has the declared independent kernel,
   axiom, trust, and replay evidence; parser/oracle success never substitutes
   for checking.
7. Clean, incremental, offline, cancellation, crash/restart, and stale-cache/
   stale-document campaigns pass under explicit resource envelopes.
8. Fresh install/package/runtime cells pass on every platform in the full
   profile at its official tier: Tier-1 targets are tested and Tier-2 targets
   build/package with their limitation explicit.
9. Functional, assurance, and performance dashboards are generated from the
   same retained evidence, with performance curves reported separately.
10. A release artifact, reproduction manifest, limitations statement, and
    current/current-minus-one maintenance policy are published.

Any scoped result may still ship earlier. Its name must carry the profile and
population, such as “K1 declaration-import parity for the pinned construct
matrix” or “K3 parity for the selected certificate-tactic corpus.”

## 10. Execution waves

The existing TL task graph remains authoritative. The companion
[execution roadmap](lean4-complete-parity-roadmap-2026-07-22.md#4-dependency-ordered-implementation-program)
maps it into R0-R10 phases with prerequisites, required deliverables, exits,
and explicit non-credit boundaries. At contract level, the waves are:

1. **Measurement and official execution:** keep R0 evidence identities current,
   finish the complete official U2 profile under R1, and classify every case by
   its native dependency without retrying one singleton for coverage.
2. **Kernel/import closure:** finish K1 String/quotient and dependency-closed
   core/library roots under R2 before promoting broader trust claims.
3. **Native source and proof assistant:** build R3 parser/macros, R4 elaboration,
   and R5 tactics in semantic dependency order; every accepted output must end
   in the independent checker.
4. **Projects and editor:** close R6 modules/artifacts/Lake before R7
   incremental server/editor transcripts and stale-state campaigns.
5. **Runtime and bootstrap:** close R8 evaluator/compiler/runtime behavior and
   native bootstrap across the declared backends/platforms.
6. **Ecosystem and release:** close R9 `Init`/`Std`/mathlib and R10
   adversarial/platform/package/migration evidence, then derive G1-G10.

P1-P3 may advance while the source substrate begins, but no later wave receives
credit for an unmet dependency. Large campaigns follow the repository rule:
prove identity, interruption, and recovery on a tiny population before the full
run.

## 11. Immediate documentation and measurement work

Before another broad implementation claim:

1. retain the R3 singleton as closed and derive fresh deterministic U2 child
   shards from the registered parent/profile authorities;
2. repair the remote Lean job so `AXEYUM_LEAN_BIN` resolves to the installed
   versioned executable from any working directory, then archive the first true
   71/71 remote attestation, duration, RSS, and axiom summary;
3. execute and classify new U2 shards with unique-case accounting, then form the
   first native official/Axeyum semantic pair;
4. extend TL0.6's generated registry seed from bounded K0/K1 and selected-
   construct evidence to content-identified complete construct, source, tactic,
   project, editor, runtime, ecosystem, and platform authorities;
5. freeze separate official populations for elaboration success, elaboration
   failure, compile+interpret, Lake, package, server, and benchmark suites;
6. record normalized per-layer equivalence rules and mutation tests before
   running those populations;
7. add content/dependency/source-family identities and exact paired overlap to
   every Lean scoreboard;
8. retain adapter, official-oracle, and native outcomes as separate columns;
9. complete the String and quotient K1 roots and regenerate the dependency-
   closed blocker ranking;
10. classify all 65 prelude assumptions before reporting broader proof parity;
11. turn the pinned mathlib tree inventory into module/declaration/dependency/
    tactic/test manifests before assigning any coverage percentage; and
12. keep the landed documentation claim guard enforced and expand its live
    claim-surface list when a new public status surface is introduced.

## 12. Primary sources

- [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean source files and modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
- [Lean macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/)
- [Lean elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
- [Lean build tools and Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/)
- [Lean proof validation and external checking](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Lean supported platforms](https://lean-lang.org/doc/reference/latest/platforms/)
- [Lean v4.30.0 test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
- [Lean v4.30.0 source tree](https://github.com/leanprover/lean4/tree/v4.30.0)
- [Lean v4.30.0 release assets](https://github.com/leanprover/lean4/releases/tag/v4.30.0)
- [Lean v4.30.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/)
- [Current Lean release index](https://lean-lang.org/doc/reference/latest/releases/)
- [mathlib v4.30.0 source/build instructions](https://github.com/leanprover-community/mathlib4/tree/v4.30.0)
- [`lean4export` v4.30.0](https://github.com/leanprover/lean4export/tree/v4.30.0)
- [SMT-LIB 2.7](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf)
- [SMT-COMP 2024 rules](https://smt-comp.github.io/2024/rules.pdf)
- [SMT-COMP 2025 rules](https://smt-comp.github.io/2025/rules.pdf)
- [SMT-COMP 2025 results](https://smt-comp.github.io/2025/results/)

## 13. Non-claims

This contract does not claim that:

- exact source/tree/test counts measure semantic completeness;
- byte-identical `.olean`, `.ilean`, generated C, or native binaries are
  necessary when a stronger semantic normalization is registered;
- official-Lean acceptance grants independent checking credit;
- a full mathlib build alone establishes parser, tactic, runtime, editor, or
  platform parity;
- finite differential testing proves universal soundness; or
- completing this roadmap is a short-term solver requirement.

It makes complete Lean 4 parity a real long-horizon project target while
preserving the small-checker product and honest scoped milestones on the way.
