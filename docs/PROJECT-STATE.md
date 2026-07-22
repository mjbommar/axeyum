# Axeyum project state

**As of 2026-07-21:** Axeyum is a working, research-grade automated-reasoning
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
  four hidden quantified-BV export failures. Remote CI acceptance is still
  pending. The exhaustive every-module sweep is not a required per-change gate.
- **Lean-core compatibility:** partial. The in-tree kernel implements dependent
  core terms, universes, declarations, WHNF, definitional equality, proof
  irrelevance, useful inductives, recursors, and iota reduction. Major residuals
  include projections/structure eta, arbitrary-precision literal support,
  quotient computation, recursive indexed families, and mutual/nested/reflexive
  inductives. A new format-3.1 Rust importer independently admits one official
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
  evidence, not a consistency proof, and projection/eta plus quotient seams are
  still absent.
- **Lean language and ecosystem compatibility:** absent today, but now staged
  rather than dismissed. Axeyum does not currently reproduce Lean's parser,
  macros, elaborator, unifier, tactic language, compiler, package ecosystem,
  language server, or mathlib. The near-term product goal is a fail-closed,
  versioned `lean4export` import path plus certificate tactics and optional
  official-Lean/Lake/editor adapters. Full native compatibility is a separately
  gated long-horizon program, not a claim about today's product and not a
  prerequisite for the checker/import profiles.

See the source-backed [kernel gap audit](prover-track/research/06-kernel-gap-analysis.md)
and [proof reconstruction plan](plan/track-3-proof-lean/P3.7-lean-reconstruction.md),
plus the [Lean-system compatibility roadmap](plan/lean-system-compatibility-roadmap-2026-07-21.md)
and [implementation plan](plan/lean-system-implementation-plan-2026-07-21.md).
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
