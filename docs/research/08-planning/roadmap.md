# Roadmap

Status: draft
Last updated: 2026-06-11

## Purpose

Turn the research notes into an implementation sequence with explicit exit
criteria and decision gates, so "done" and "justified" are checkable rather
than felt.

## Scope

In scope:

- Phased plan from empty repo to useful reasoning stack.
- Exit criteria per phase and gates for expensive bets.

Out of scope:

- Time estimates and release commitments.

## Core Claims

- A thin end-to-end vertical slice comes before broadening any layer
  (see [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)).
- Checkability and differential testing are continuous workstreams present in
  every phase, not phases themselves.
- Expensive bets (custom CDCL, lazy techniques) are gated on the benchmarking
  methodology note, not on enthusiasm.

## Continuous Workstreams

These run through every phase below:

- Evidence: every new layer ships with its check (evaluator, CNF evaluator,
  round trips, lift-map validation).
- Differential testing: every transformation gains an oracle comparison when
  an oracle exists.
- Benchmarks: the harness and corpora grow with each layer
  (see [benchmarking methodology](benchmarking-and-performance-methodology.md)).
- Decisions: questions close as ADRs in `09-decisions/` as phases force them.

## Phase 0: Repository Foundation

- Workspace skeleton, license, README, contribution conventions.
- CI for formatting, linting, tests.
- Decision: start with two crates (`axeyum-ir`, `axeyum-solver`); split later.

Exit criteria: CI green on an empty workspace; ADR process in place.

## Milestone M0: Vertical Slice

- IR subset (Bool, BV constants/symbols, core ops), arena, sort checking.
- Ground evaluator.
- Solver trait plus Z3 feature backend with model lifting to Axeyum symbols.
- Model check-by-evaluation on every `sat`.

Exit criteria: doctest asserts `x + 1 == 5` over `BV(8)`, solves via Z3,
lifts the model, and the evaluator confirms it. Cancellation/timeout plumbing
exists in the trait.

## Phase 1: Typed Term Core (Broaden)

- Full scalar QF_BV operator set with SMT-LIB edge-case semantics
  (see [BV semantics note](../01-foundations/bv-semantics-and-partial-operations.md)).
- Pretty printer and stable debug format.
- Exhaustive small-width evaluator tests for div/rem/shift/rotate.

Exit criteria: every operator has evaluator tests; exhaustive width <= 8
coverage for edge-case operators runs in CI.

## Phase 2: Native Solver Oracle (Harden)

- Backend conformance suite (results, models, state retention, cancellation).
- SMT-LIB export for debugging; SMT-LIB benchmark import for the QF_BV slice
  (see [formats note](../02-ecosystems/formats-and-interchange.md)).
- Optional second backend (Bitwuzla) to validate the trait is not Z3-shaped.

Exit criteria: conformance suite passes on Z3; SMT-LIB QF_BV benchmarks
ingest and solve through the trait; benchmark harness records baseline runs.

## Phase 3: Rewriting And Query Planning

- `axeyum-rewrite` cheap canonicalizer with rule IDs and per-rule tests.
- Query object with assertions, assumptions, scopes
  (assumptions-first; see [incrementality note](../03-architecture/incrementality-and-solver-lifecycle.md)).
- Constraint slicing and structural cache keys.
- Differential rewrite tests against the oracle on ingested corpora.

Exit criteria: rewriter is evaluator-equivalent on random inputs and
oracle-equisatisfiable on the public corpus; measured rewrite win (size or
solve time) is recorded, not assumed.

## Phase 4: Circuit And CNF Layers

- AIG layer with structural hashing; AIGER export for debugging.
- `axeyum-cnf` with Tseitin encoding and DIMACS I/O.
- Model lifting from SAT vars to wires to terms; CNF evaluator.

Exit criteria: round-trip and lift-map tests pass; DIMACS corpus solves via
an adapted Rust SAT solver behind the SAT trait.

## Phase 5: Pure Rust BV Backend

- Bit-blasting for the scalar subset; per-operator lowering pluggable.
- Existing Rust SAT adapter (evaluate batsat/splr/varisat against the
  methodology note's criteria; varisat's proof output weighs in its favor).
- Differential tests against the native backend on all corpora.

Exit criteria: pure Rust path agrees with the oracle on the public QF_BV
slice it supports; layer-attributed timing identifies the dominant cost.

## Phase 6: SAT Core (Identity; Priority Gated)

The custom CDCL core is part of the project identity
([ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md)):
it will be built. The methodology note's gate decides *when* — it takes
priority over encoding work only once SAT time dominates end-to-end time on
the corpus tiers.

- SAT trait stabilization with proof-logging hook (IPASIR-superset shape).
- Clause arena, propagation, CDCL prototype with DRAT output.
- Profiling against the adapters that justified the work.

Exit criteria: prototype beats the best adapter on the client tier or the
attempt is written up as an ADR documenting why not.

## Phase 7: Arrays, EUF, And Client Libraries

- Array and UF terms in IR; native backend support for QF_ABV/QF_AUFBV.
- Bounded/lazy memory encodings; lemmas-on-demand research per the
  [beyond-bit-blasting note](../05-algorithms/beyond-bit-blasting.md).
- Client examples for math, verification, and infosec workflows.

Exit criteria: one real client example per audience runs end to end with
checked evidence.

## Beyond Phase 7: The Proving Horizon

The phases above build the decidable finite-domain foundation. The north
star ([north-star note](../00-orientation/north-star.md)) continues past it;
these are direction markers, not commitments, sequenced only loosely:

- Arithmetic theories (QF_LIA/QF_LRA): simplex core, branch and bound.
- Theory combination (Nelson-Oppen style) once two real theories exist.
- Quantified fragments: E-matching over the term index, then MBQI-style
  model checking; enumerative instantiation as the simple baseline.
- Proof production grows with each rung: every new engine ships with its
  evidence story, extending the layered-certificate pattern.
- Proof-assistant interop (export obligations to / import lemmas from
  Lean-class systems) as the bridge to full proving.

Entering any horizon item gets its own ADR with prerequisites and exit
criteria; none may begin while it would starve a foundation phase.

## Open Questions

- [ ] Should Phase 2 include the second backend or defer it to Phase 5's
      differential needs?
- [x] Where does the SMT-LIB parser crate boundary land (`axeyum-smtlib` vs
      CLI module)?
      Answer: `axeyum-smtlib`, now exercised by solver tests and
      `axeyum-bench`.
- [ ] Should proof logging (DRAT from adapters that support it) be surfaced
      before Phase 6?

## Source Pointers

- Cargo workspaces: https://doc.rust-lang.org/cargo/reference/workspaces.html
- z3.rs: https://github.com/prove-rs/z3.rs
- RustSAT: https://github.com/chrjabs/rustsat
- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
