# Consumer Scenario Models

Status: draft
Last updated: 2026-06-13

## Purpose

Record why Axeyum generates its own self-checking consumer workloads, how their
ground truth is established without a native oracle, and how this corpus drives
the interface and optimization-architecture work that follows. This note backs
[ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md) and frames a
short iteration plan for working backwards from real consumers (symbolic
execution and emulation in the spirit of angr/unicorn; trusted checking in the
spirit of Lean).

## Scope

In scope:

- The self-checking scenario contract in `axeyum-scenarios`.
- How SAT and UNSAT ground truth is produced and verified by the evaluator.
- The role of scenarios as an optimization-measurement substrate.
- The iteration plan for the consumer-models, interfaces, and
  abstraction/optimization themes.

Out of scope:

- Public SMT-LIB corpus selection (see
  [benchmarking methodology](../08-planning/benchmarking-and-performance-methodology.md)).
- New solver operators, rewrites, or encodings (foundational-DAG gated).

## Core Claims

- The Phase 5 stall was measured against one academic public slice whose ground
  truth is the Z3 oracle. That couples progress to an unrepresentative corpus
  and leans on the very dependency ADR-0002 plans to demote.
- A consumer scenario is a self-contained `(TermArena, Query, Expectation)`
  whose status is known *by construction* and verified *by evaluation*:
  - **SAT by concrete execution.** Choose concrete inputs from a seed, run the
    computation concretely, and assert constraints the run satisfies. The
    concrete input is the witness; `self_check` evaluates every query term under
    it and requires `true`.
  - **UNSAT by bounded-verified identity.** Assert the negation of a bit-vector
    theorem; `self_check` confirms no assignment satisfies the conjunction,
    exhaustively below `EXHAUSTIVE_BIT_LIMIT` (a real finite-domain proof) and
    by deterministic sampling above it (recorded as lower assurance).
- This ground truth is independent *in kind* of the bit-blast-to-SAT search
  path, so backend agreement is a genuine cross-check, not a tautology against
  another solver. It is the testing-side analogue of "trusted small checking".
- The first families (`mixing`, `machine`, `identity`) stay strictly inside the
  `axeyum-bv` lowering subset, so they exercise the pure-Rust backend end to end
  rather than bouncing off unsupported operators, and they scale with width and
  depth for optimization measurement.

## Design Implications

- Scenario generators are themselves code under test; the self-check *is* the
  test, and it already caught a generator bug during bring-up.
- The catalog runs in default CI with no native dependency, giving a
  fast, deterministic, oracle-free regression and measurement set.
- Optimization passes should be measured against this scalable corpus (and the
  public slice), not tuned to a single frontier instance.

## Iteration Plan

This note opens a short, checkable sequence (each step: research, design,
implement, test, document):

1. **Consumer models (done, 2026-06-13).** `axeyum-scenarios` with the three
   self-checking families, a deterministic catalog, and a differential test
   through `SatBvBackend` (all decided, zero soundness alarms). ADR-0008.
2. **Interfaces (done, 2026-06-13).** A high-level incremental `Solver` façade
   in `axeyum-solver` (assert / push / pop / check / check_assuming, with
   `last_stats` and capability passthrough) plus ergonomic `SolverConfig`
   builders. Incremental at the interface level over a still-one-shot backend,
   so a future incremental backend drops in without changing consumer code.
   Tested via push/pop scoping, assumption non-persistence, and driving the
   whole catalog through the façade.
3. **Abstraction and optimization architecture (done, 2026-06-13).** Typed
   `BvLayerStats` lifts the stringly-typed per-stage counters into a first-class
   view (bit-blast, cnf-encode, solve, model-lift; AIG/CNF sizes; clause
   density). The `scenario_pipeline_report` bench example gives a deterministic
   per-stage, per-family measurement over the corpus.
4. **Integrate and iterate (done, 2026-06-13).** The `scenario_scaling` bench
   example sweeps `mixing` rounds at widths 16/32/64 and records the pipeline
   scaling profile (see Measured Baselines below).

## Measured Baselines (2026-06-13)

From `scenario_pipeline_report` over the deterministic catalog: the pure-Rust
backend decides every scenario (9 mixing, 8 machine, 8 identity) with no
unknowns and no soundness alarms; mean clause density is ~3 clauses/variable;
the de-Morgan and two's-complement identities collapse to 0 CNF variables
(constant-folded away before SAT).

From `scenario_scaling` (mixing inversion, satisfiable by construction):
AIG and CNF size grow linearly in the round count, clause density converges to
~3.5 clauses/variable (plain Tseitin's ~3 clauses per AND node), and `sat-bv`
solve time scales near-linearly with size on these instances — e.g. width 64 /
64 rounds yields 16,040 AIG nodes, 7,942 CNF variables, 27,676 clauses, decided
in ~29 ms. This is the oracle-free, frontier-scalable baseline future encoding
or SAT-cost optimizations should move.

Reproduce with `cargo run -p axeyum-bench --example scenario_pipeline_report`
and `cargo run -p axeyum-bench --example scenario_scaling`.

## Risks

- Generators can encode a wrong "known" status. Mitigation: exhaustive
  self-check at small widths; sampled self-check otherwise; soundness assertions
  in the backend differential test.
- A self-checking corpus can drift toward what the backend already solves.
  Mitigation: scale width/depth past the current frontier and keep the public
  slice in the loop.
- Sampled UNSAT evidence is not a proof. Mitigation: it is labelled
  `Sampled` and never reported as `Exhaustive`.

## Open Questions

- [ ] Should scenarios gain a concrete-execution *trace* artifact (closer to
      unicorn-style emulation) for richer path-condition families?
- [ ] When incremental solving lands, scenarios should emit multi-check
      sequences (one check per path prefix); what is the contract for that?

## Source Pointers

- ADR-0008: ../09-decisions/adr-0008-consumer-scenario-models.md
- Evidence and checking: ./evidence-and-checking.md
- Benchmarking methodology: ../08-planning/benchmarking-and-performance-methodology.md
