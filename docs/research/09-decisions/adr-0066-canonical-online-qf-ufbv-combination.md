# ADR-0066: Canonical Online QF_UFBV Combination

Status: accepted
Date: 2026-07-09

## Context

The theory-combination question in the
[research register](../08-planning/research-questions.md) chooses canonical
`CdclT` plus `TheorySolver` adapters over a second production Boolean loop.
QF_UFLIA and QF_UFLRA already follow that rule, but QF_UFBV still depended on
eager Ackermann implications or an outer functional-consistency CEGAR loop.
That left the e-graph and the exact finite-domain BV engine unable to exchange
equalities on one backtrackable trail.

[P1.6](../../plan/track-1-engine/P1.6-theory-combination.md) requires a live
interface-equality bus while preserving the project's replay and evidence
contracts. ADR-0013's new abstraction-only function rewrite provides the
necessary starting formula without constructing the quadratic Ackermann set.

## Decision

Admit bounded scalar QF_UFBV through canonical `CdclT`, combining the
backtrackable e-graph with a warm incremental BV solver over explicit
argument/result interface equalities.

- Start from `abstract_functions`: each application becomes a fresh scalar, but
  no Ackermann implication is materialized.
- Track every semantic atom in both its original and function-abstracted form.
  For every pair of applications of the same function, add one equality atom
  per argument position and one result-equality atom.
- Drive `EufTheory` and the warm `IncrementalBvSolver` in lockstep through one
  `TheorySolver`. The e-graph explains congruence conflicts and propagates
  result equality; the BV solver decides exact Bool/BV feasibility and reports
  the full active atom assignment as a sound, deliberately non-minimal conflict
  core.
- Give every warm BV check only the remaining absolute query deadline. Failures
  and exhausted construction/search limits become first-class `Unknown`.
- Accept `Sat` only after projecting the fresh result symbols into `FuncValue`
  tables and replaying every original assertion.
- Route admitted scalar QF_UFBV through `check_auto` before the offline/eager
  paths. Unsupported logical shape may fall through; timeout and resource-limit
  outcomes remain terminal so a later route cannot mask the budget cause.
  Retain eager Ackermann elimination as the conservative fallback,
  differential oracle, and unchanged proof/evidence route.

The initial route is intentionally bounded: 16,384 input DAG nodes, depth
4,096, 1,024 semantic atoms, 512 generated interface atoms, 8,192 Boolean
variables, and 32,768 Boolean clauses. It admits only Bool/BV terms; arrays,
arithmetic, floating point, datatypes, and uninterpreted carrier sorts decline
to their existing routes.

## Evidence

- Five direct mechanism tests cover BV-implied argument equality, congruent
  results flowing into BV ordering, projected-model replay, zero-timeout
  classification, and the interface-cap boundary.
- Three deterministic 512-case matrices compare direct-online with eager pure
  Rust, front-door with eager pure Rust, and direct-online with Z3 over the eager
  reduction. All 1,536 comparisons agree and the direct admitted matrices have
  no `Unknown`.
- Existing function, scenario, SMT-LIB, e-graph, and QF_UF Z3 differential gates
  remain green.
- The public curated QF_UFBV corpus decides 6/6 (3 sat, 3 unsat), agrees with Z3
  on all six, and has zero model-replay failures at a 5 s limit.

This is a capability and architecture result, not a performance claim. The
six-row run has mean PAR-2 wall time 0.061 s, while `bug520` takes about 0.332 s
online versus about 0.009 s in Z3. The next optimization evidence must come from
BV propagation, lazy/relevant interface generation, and broader corpus timing.

## Alternatives

- **Keep eager Ackermann as the production route.** Rejected as the destination:
  it preserves quadratic construction and cannot serve as the shared equality
  bus required by later theories. It remains the fallback and proof route.
- **Keep the outer functional-consistency CEGAR loop.** Rejected as the canonical
  architecture because it owns a second search loop and exchanges no theory
  propagation on the live CDCL trail.
- **Merge BV semantics directly into the e-graph.** Rejected because equality
  congruence and finite-domain bit-vector feasibility have distinct ownership
  and checking contracts.
- **Use a native solver for combined UFBV.** Rejected by the pure-Rust default
  requirement and ADR-0002's oracle-only role for linked solvers.

## Consequences

- Scalar QF_UFBV now exercises the same canonical Boolean/conflict-learning
  spine as EUF, strings, and arithmetic combination.
- Congruence and exact BV implications can constrain each other before a total
  model, while every accepted model still replays in the original semantics.
- The full-active-trail BV core is simple and checkable but can learn wide
  clauses; core minimization and BV theory propagation are performance work.
- Pairwise interface generation is still quadratic, but it is bounded and now
  consists only of equality atoms rather than eager semantic implications.
  Relevance-driven generation is the next scale step.
- QF_AUFBV and mixed BV+arithmetic combination remain on existing reduction
  stacks. Arrays must join the live bus under a separate measured increment.
- Unsat evidence is unchanged: proof production re-runs the established eager
  certifying reduction rather than trusting online theory state.
