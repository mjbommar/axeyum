# Axeyum project state

**As of 2026-07-22:** Axeyum is a working, research-grade automated-reasoning
stack with competitive results on selected fragments and substantial checked
proof coverage. It is not a drop-in Z3 replacement or a replacement for the
Lean system.

This page is the short answer to three questions: what exists, what has been
measured, and what remains open. The large [PLAN](../PLAN.md) and
[STATUS](../STATUS.md) files are engineering records, not the recommended first
read.

## What exists now

- A pure-Rust default solver path from typed terms through rewriting,
  bit-blasting, CNF, and SAT. Native solvers are optional oracle/benchmark
  backends, not default dependencies.
- Solver routes for bit-vectors, arrays, uninterpreted functions, linear
  arithmetic, floating point, datatypes, bounded strings/sequences, selected
  nonlinear and quantified fragments, and several combinations. Maturity varies
  by route; the [capability matrix](research/08-planning/capability-matrix.md)
  records the assurance attached to each one.
- Replay checking for returned SAT models and multiple UNSAT evidence routes,
  including DRAT, Farkas, Alethe, specialized certificates, an in-tree Lean-style
  kernel, and generation of self-contained Lean modules for supported proof
  families.
- Rust, WASM, symbolic-execution, bounded-verification, EVM, property, and
  proof-carrying-CAS consumers over the shared typed core.

These are real implementations, not roadmap placeholders. They are also not all
equally complete, certified, fast, or exposed through conformant SMT-LIB text.

## What has been measured

The committed regression scoreboard currently contains 35 rows over 24 logic
labels:

- **753 / 992** files are decided and **680 oracle-compared** decisions have
  **0 recorded disagreements**.
- **25 / 35** rows meet the project's `>= 80%` decide-strong threshold.
- **23 / 35** audited rows meet their complete dominance definition; a paired
  timing refresh is still required before publication because the proof refresh
  changed timing-derived flags without changing verdicts.

Those figures describe the committed slices, not the SMT-LIB universe. The
file-backed rows contain 927 occurrences, 837 unique normalized paths, and only
778 unique byte contents; 58 exact-alias groups remove 59 additional path
identities. Two synthetic rows expose 65 aggregate-only cases with no file
identity. Zero observed disagreement is strong regression evidence; it is not a
proof of universal soundness.

A separate, harder 228-file public convenience inventory gives the less
flattering and equally important view. Its legacy scorer reports **82 / 228**
decisions, but direct status-aware audit partitions those into **78 known-status agreements**
and **4 unadjudicated decisions**; it also records **144 explicit declines**,
**2 no-answer outcomes**, and **0 wrong verdicts** against known
statuses. It is not an official or population-weighted SMT-COMP selection.

A later runner audit found that this local reproduction path suppresses a
parsed response if its watchdog fires, whereas SMT-COMP 2026 counts a response
even after timeout or abnormal termination. The committed raw artifact does not
retain stdout/termination evidence, so the two no-answer rows
cannot be retroactively classified. The counts above remain exact artifact counts, not a
claim that this execution path was fully competition-faithful.

The two regimes are also not independent: **99 exact contents** appear in both,
covering 43.4% of the public inventory and 12.7% of the scoreboard's unique
file-backed contents. Their decide rates describe different weightings of an
overlapping convenience population and must not be averaged.

A later 64,345-file cap/family candidate is **not a result**: its first
52-shard execution stopped after 2,041 progress lines and produced zero raw
shards. The cause is unknown. The failed attempt is frozen with zero credit,
and a checked resumable-run contract now precedes any retry; production atomic
checkpoint and multi-host recovery tests are still open. The local checkpoint
primitive has passed forced-process-kill recovery on tmpfs and ext-family
storage, but it is not yet wired into the runner and says nothing about NFS,
power loss, aggregate resources, or remote recovery.

For UNSAT assurance, the 327 baseline UNSAT decisions partition as follows:

- **259 / 327** are certified, independently checked, free of declared trust
  holes, and Lean-reconstructed.
- **58 uncertified** occurrences remain.
- **8 certified** and independently checked occurrences still lack Lean
  reconstruction.
- **2 proof-production errors** remain in the audited QF_NIA evidence run.

The authoritative sources are the generated
[scoreboard](../bench-results/SCOREBOARD.md),
[measurement-provenance matrix](plan/generated/measurement-provenance-matrix.md),
[proof-gap matrix](plan/generated/proof-gap-matrix.md), and
[scoped parity analysis](plan/gap-analysis-z3-lean-2026-07-21.md).

## How close is it to Z3?

There are three different answers:

1. **Selected-fragment parity:** achieved on several measured rows and bounded
   controls. In the registered 20-second p4dfa control, Axeyum and the Z3 crate
   each decide **8 / 113**. Exact pairing finds six jointly decided and two
   unique decisions per solver, with no joint disagreement. In a separate 24-file
   QF_BV comparison, Axeyum, cvc5, and Bitwuzla each decide **19 / 24**, with Axeyum
   third on PAR-2.
2. **General solving-power distance:** not measured. The successful cells are
   bounded or convenience samples, while the larger full-tree attempt yielded
   no admissible result. The repository does not yet justify a global distance.
3. **Production Z3 replacement:** not close. Public-corpus depth is uneven;
   strategy portfolios and broad performance characterization remain immature;
   and the checked 30-row SMT-LIB/API audit finds six absent command families,
   seven accepted no-ops, and **zero interactive textual-session rows**.

The fair Glaurung six-cell experiment reinforces the distinction: warm Axeyum
beats warm Z3 on three named drivers and loses on DptfDevGen, while warm
Bitwuzla wins all four. Axeyum therefore has a characterized competitive regime,
not a general performance-leadership result.

See the [benchmark guide](user-guide/benchmarks.md) and generated
[SMT-LIB/API conformance matrix](plan/generated/smtlib-api-conformance.md).

## How close is it to Lean?

Again, there are distinct targets:

- **Solver proof export:** substantial and useful today. Supported refutations
  become kernel-checked terms and self-contained Lean modules. The harness
  registers 71 proof-family builders and CI is configured to send one module
  per family to official Lean. A repaired checksum-pinned local run now records
  **71/71 accepted, zero skipped, zero failed** after exposing and correcting
  four hidden quantified-BV export failures. The first corrected remote job is
  retained but earns no acceptance credit: it failed before the representative
  sweep because the explicit Lean path resolved to an elan shim without a
  default toolchain outside the repository working directory. The exhaustive
  every-module sweep is not a required per-change gate.
- **Lean-core compatibility:** partial. The in-tree kernel implements dependent
  core terms, universes, declarations, WHNF, definitional equality, proof
  irrelevance, useful inductives, recursors, iota reduction, dependent
  projections, constructor projection reduction, arbitrary-precision checked
  Nat literals, structure eta, recursive-indexed/higher-order fields, atomic
  mutual groups, and nested-inductive expansion/restoration. Major kernel
  residuals include String literals and quotient computation; native mutual,
  nested, and well-founded **source elaboration** remains a separate frontend
  gap rather than a kernel decline. A new
  format-3.1 Rust importer independently admits one official
  flat fixture as eight kernel declarations and one direct-recursive
  `MiniNat`/`MiniList` fixture as 11 declarations with zero axioms. This proves
  those exact profiles, but `Init`/`Std`/mathlib and the declined kernel
  constructs remain open. A four-root official export census now makes
  projection the measured first kernel blocker for structure, Nat-literal, and
  String-literal closures; this orders work but is not broad `Init` coverage.
  The reconstruction preludes have a runtime-derived 65-row axiom ledger whose
  names and canonical type digests are checked, but whose statements have not
  yet been semantically classified or discharged. A deterministic 768-case
  seam-fuzz seed now covers the four representable kernel interactions and
  rejects `False` admission in every case; this is adversarial regression
  evidence, not a consistency proof. Projection terms are structurally
  represented and rendered; the native kernel infers dependent field types and
  reduces constructor projections. The exact official projection root now
  translates, independently admits nine declarations, and computes. Structure
  eta now passes seven native control families plus a pinned-Lean 4.30 positive/
  rejecting differential. Arbitrary-precision Nat literals now type only
  against a checked canonical bootstrap; constructor/literal equality,
  successor reduction, and recursor conversion close the exact official Nat
  root as ten declarations with zero axioms and a second required pinned-Lean
  differential. The importer now stages in a private kernel and returns an
  owned `CompletedImport` only after the entire stream succeeds, so late parser,
  resource, I/O, unsupported, or kernel failures expose no partial environment.
  A deterministic 226-case mutation corpus covers every official record plus
  ID/reference/field/depth/Unicode/integer/cycle/version families. It records 64
  complete-record prefixes as `published-unsealed`, not full artifacts, because
  upstream format 3.1 has no footer or expected count. Successful imports now
  also publish TL0.4-compatible axiom identities plus versioned structural
  content and direct-dependency digests for every admitted declaration. Five
  focused tests freeze the exact flat-fixture identities and prove record-order
  invariance plus type/body/dependency mutation sensitivity.
  A completed source-first/wire-second official construct matrix freezes
  recursive-indexed, reflexive, mutual, nested, and well-founded exports before
  product measurement. Append-only TL2.12, TL2.13, and TL2.14 overlays retain
  each historical pre-widening view while the current matrix records seven
  rows, six independently admitted rows, four independently computation-
  checked rows, one official-source rejection, and zero transactional declines.
  TL2.11
  supplies the semantic prerequisite: a pre-insertion Lean 4.30 single-family
  strict-positivity guard
  with exact typed failures, twelve public rows, a twice-repeated 840-case
  grammar, eight pinned-Lean observations, mandatory CI, and synthetic importer
  propagation without publication. Accepted ADR-0353 and TL2.12 then implement
  one telescope/index-aware induction-hypothesis and iota-rule construction for
  direct, recursive-indexed, higher-order/reflexive, and combined fields. The
  frozen `MiniVector` and `MiniAcc` construct streams complete twice with exact
  generated/exported recursor comparison; separate computation streams reduce
  to the registered Vector and Acc normal forms in both official Lean and
  Axeyum. Kernel-side nested-inductive elimination is now complete for the
  registered native and official population under accepted ADR-0355, while
  broad Lean admission and native nested/well-founded source elaboration remain
  separately staged in TL4.9/TL4.10. Mutual groups are complete under accepted
  ADR-0354:
  the unit is one
  atomic ordered
  group with shared parameters, complete-group positivity, all motives/minors,
  target-family recursive calls, and all-or-nothing publication. Its M0
  source/wire freeze is complete: a
  twice-compiled explicit-recursor source and two byte-identical-per-root
  official streams are machine-bound without any new Axeyum observation. The
  wire inventories also show why later comparison cannot use array position:
  families are source-ordered `Even, Odd`, but recursors are dependency-ordered
  `Odd.rec, Even.rec`. M1 now adds the ordered group input, common parameter/
  result-universe preflight, scalable atomic rollback, and identity-preserving
  singleton delegation. M2 now replaces the native policy decline with one
  complete-group algorithm. Eighteen public rows cover cross, indexed, higher-
  order, mixed, empty-constructor, and mutual-`Prop` shapes; two private
  mutation tests exercise recursor contracts and late whole-group rollback.
  M3 now repeats 720 unique public-path cases byte-identically with 432
  positive admission/inference/iota contracts, 288 exact typed rollbacks,
  motive/minor order read from recursor telescopes, and target-family rule
  signatures. Generated group-order/target-family mutations reject and the
  768/840 controls remain exact. M4 now parses one exact ordered official group,
  calls the atomic gate once, compares dependency-ordered wire recursors by
  checked name, and imports the construct plus both computation streams twice.
  Both selected cross-family recursor applications normalize to the registered
  two-successor result, and 22 rejecting importer/publication mutation classes
  pass. M5 preserves the historical assurance record while adding the current
  TL2.13 overlay: five rows are admitted, three are independently computation-
  checked, and one retains a typed decline. Every bounded final gate passes,
  the obsolete live mutual decline is removed, and TL2.13 is DONE. A source-
  backed dependency audit corrects the next task: TL2.14 is kernel-side nested-
  inductive expansion/restoration under accepted ADR-0355; well-founded source
  recursion remains native-elaborator task TL4.10. The already elaborated
  well-founded root imports as 35 declarations with zero axioms; that remains a
  core control rather than frontend credit.
  TL2.14 M0 now freezes three explicit main/auxiliary recursor computations,
  one exact negative kernel diagnostic, and 114,596 bytes of twice-identical
  official streams without product observation. M1 parses the claimed
  group-wide auxiliary count before recursor policy and moves the exact nested
  row to typed `inductive-nested` non-admission before the kernel gate, while
  malformed count variants and the well-founded/720/768/840 controls remain
  exact. M2 now implements native structural discovery, complete container-
  group copying, fixed-point expansion, unchanged atomic checking, recursive
  source-surface restoration, deterministic `.rec_N` publication, and
  transaction/cache rollback. Twenty-three focused native tests include exact
  final inference and `main -> rec_1 -> main` computation. Official importer
  admission and frozen-stream computation remain M4/M5 work. M3 now repeats
  the exact 640-case public grammar twice at descriptor digest
  `a20fe056c9443a37`, independently checks exact public declarations,
  per-rule recursor dependency maps, and 320 main plus 462 auxiliary typed iota
  reductions, and closes 16 transactional restoration mutations. A bounded
  stop-review amendment validates the already-checked temporary surface after
  copied-constructor metadata mutants survived M2 restoration. Complete
  kernel/importer suites, strict tooling, M0 contracts, and retained
  720/768/840 populations pass. M4 now derives auxiliary identity from checked
  motives, imports the construct and all three frozen computation streams twice
  at 22/34/34/34 declarations and zero axioms, compares exact main/auxiliary
  contracts, and closes 20 wire/publication classes plus order non-authority.
  M5 confirms all three registered theorem proofs and 3/3/5-successor normal
  forms twice, appends a history-preserving TL2.14 overlay at seven rows / six
  admitted / four computation-checked / zero current declines, and removes only
  the obsolete live nested decline. M6 maps every ADR exit and repeats the
  bounded positive/negative pinned-Lean, complete kernel/importer, exact
  640/720/768/840, well-founded 35/0, strict tooling, contract, generated-
  document, parity, foundational-resource, and link gates. ADR-0355 is accepted
  and TL2.14 is DONE: containing commit `1d848ad4` was pushed with local,
  tracking, and remote refs equal before integration.
  Quotient and String literals are still absent. These are exact K0/K1 slices,
  not general kernel parity.
- **Lean language and ecosystem compatibility:** absent today, but now staged
  rather than dismissed. Axeyum does not currently reproduce Lean's parser,
  macros, elaborator, unifier, tactic language, compiler, package ecosystem,
  language server, or mathlib. The near-term product goal is a fail-closed,
  versioned `lean4export` import path plus certificate tactics and optional
  official-Lean/Lake/editor adapters. Full native compatibility is a separately
  gated long-horizon program, not a claim about today's product and not a
  prerequisite for the checker/import profiles. The current generated matrix
  has one satisfied K0 row and four of five K1 rows, with **zero** satisfied K2
  source, K3 tactic, K4 workflow, K5 runtime, or K6 ecosystem rows. The
  [complete Lean 4.30 parity contract](plan/lean4-complete-parity-contract-2026-07-22.md)
  reserves an unqualified “100%” claim for the native A0-A11 conjunction over
  complete content-identified U0-U9 populations; adapters and bounded fixtures
  cannot fill that terminal gate. The first U2 measurement slice now derives
  [3,678 default / 3,723 full-Lake official registrations](plan/lean-u2-test-authority-2026-07-22.md)
  from pinned CMake/CTest semantics and content-binds all selected commands,
  sources, sidecars, output policies, and support trees. It records zero
  official executions, zero Axeyum executions, and zero paired cells, so U2 is
  a bounded registration profile rather than evidence of language or ecosystem
  compatibility. The next [workflow-profile result](plan/lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md)
  derives 17 event contexts, 153 matrix cells, 111 declared CTest attempts, and
  eight exact selection sets. Every attempt remains `not-run`; this closes
  configuration identity, not Lean execution or Axeyum parity. The subsequent
  [TL0.7.1 contract](plan/lean-execution-evidence-tl0.7.1-2026-07-22.md)
  defines explicit 4/8 GiB local lanes, twelve typed termination classes, and
  immutable completion-last evidence. Its five controls are synthetic and all
  real execution counters remain zero. The subsequent
  [TL0.7.2 result](plan/lean-execution-process-tl0.7.2-2026-07-22.md) retains
  8/8 bounded synthetic process attempts with exact raw output, descendant
  cleanup, and evidence-backed exit/signal/timeout/memory/launch/preflight
  classes. It still records zero cases, completions, official/Axeyum outcomes,
  paired cells, performance rows, or parity credit. The subsequent
  [TL0.7.3 result](plan/lean-execution-store-tl0.7.3-2026-07-22.md) retains
  16/16 reaped dependency/completion persistence-boundary `SIGKILL` cells
  across observed ext4/tmpfs, with exact completion-last recovery and 16/16
  uninterrupted projection equality. It still records zero real/U2/parity
  credit and explicitly does not qualify power/host loss or network/object
  durability. TL0.7.4 remains the prerequisite to official U2 execution.
  Its source-first
  [acceptance plan](plan/lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md)
  freezes one pinned-Lean compile preflight and one exact official-export
  control, both empty-selection and structurally unable to receive U2/parity
  credit. Attempt 001's 4 GiB compile failed before `.olean` creation because
  Lean's default task-stack reservation exhausted address space; the exporter
  did not run. The [R1 plan](plan/lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md)
  preregisters exact `-s524288` and terminal-before-artifact retention.

See the source-backed [kernel gap audit](prover-track/research/06-kernel-gap-analysis.md)
and [proof reconstruction plan](plan/track-3-proof-lean/P3.7-lean-reconstruction.md),
plus the [Lean-system compatibility roadmap](plan/lean-system-compatibility-roadmap-2026-07-21.md),
the [implementation plan](plan/lean-system-implementation-plan-2026-07-21.md),
and the [complete-parity contract](plan/lean4-complete-parity-contract-2026-07-22.md).
The exact official-test selection checkpoint is the
[U2 registration authority](plan/lean-u2-test-authority-2026-07-22.md), and its
official execution-profile derivation is the
[TL0.6.2 result](plan/lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md).
The exact first import result and negative matrix are in the
[`lean4export` Rust prototype report](plan/lean4export-rust-import-prototype-2026-07-21.md).

## What is not claimed

Axeyum does not currently claim:

- universal soundness from finite differential tests;
- complete proof coverage for every returned UNSAT in every supported route;
- general Z3 performance parity or leadership;
- full SMT-LIB 2.7 session conformance;
- full Lean-kernel, mathlib, tactic, or ecosystem compatibility;
- completeness for general nonlinear arithmetic, unbounded strings, or
  unrestricted quantifiers.

Unsupported, incomplete, or resource-bounded paths are expected to return
`unknown` or an explicit decline. The exact boundary belongs in the capability,
support, trust, and conformance ledgers—not in an unqualified product slogan.

## Where to go next

| Reader | Next page |
|---|---|
| Evaluating the project | [Limitations](user-guide/limitations.md) and [Benchmarks](user-guide/benchmarks.md) |
| Running it | [User guide](user-guide/README.md) |
| Reviewing assurance | [Capability matrix](research/08-planning/capability-matrix.md), [trust ledger](research/08-planning/trust-ledger.md), and [proof-gap matrix](plan/generated/proof-gap-matrix.md) |
| Contributing | [Measured-gap ownership map](contributor-guide/gap-ownership.md), [contributor guide](contributor-guide/README.md), and [scoped gap program](plan/gap-analysis-z3-lean-2026-07-21.md) |
| Resuming engineering work | [PLAN](../PLAN.md), then [STATUS](../STATUS.md) |
