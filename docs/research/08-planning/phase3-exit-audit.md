# Phase 3 Exit Audit

Status: recorded
Last updated: 2026-06-11

## Purpose

Record the evidence that the Phase 3 rewrite/query-planning layer is ready to
be treated as a foundation for Phase 4 bit-order, circuit, and CNF work.

## Scope

In scope:

- Default denotation-preserving rewrite rules and their validation routes.
- Query structural cache keys, conservative target-support slicing, and replay
  checks.
- Benchmark artifact fields that make rewrite/query effects visible on corpus
  runs.

Out of scope:

- Phase 4 bit lowering, AIG, Tseitin CNF, SAT adapters, and lift maps.
- Equisatisfiability-only rewrites; they remain disabled until model
  projection exists and has replay tests.
- Proof artifacts for `unsat`; Phase 3 still relies on oracle comparison, not
  a proof checker.

## Core Claims

- The default Phase 3 canonicalizer is an exact-denotation transformation:
  every enabled rule has identity model projection and no public
  equisatisfiability-only rewrite is enabled.
- Query slicing is a solver fast path, not a semantic weakening: any `sat`
  model from a sliced plan must replay against the original assertions and
  assumptions before acceptance.
- The benchmark harness now records both rewrite effect and query-plan
  cache/slice metrics, so future size or solve-time claims can be tied to
  artifacts rather than assumptions.

## Exit Criteria Evidence

| Criterion | Current evidence | Status |
|---|---|---|
| Rewriter evaluator-equivalent on generated inputs | `generated_canonicalized_terms_are_evaluator_equivalent` builds 128 deterministic Bool/BV terms over width 3, requires many nested rewrite applications, and exhausts all assignments for `x`, `y`, `p`, and `q`. | Satisfied for the default exact-denotation rule set. |
| Per-rule focused coverage | `default_rules_fire_on_focused_examples` proves every enabled default manifest rule fires on an intended example. | Satisfied. |
| Non-denotational rewrites disabled by default | Manifest validation rejects default equisatisfiable rules without implemented projection and model-projection replay tests; `default_manifest_enables_only_denotation_identity_projection_rules` checks the default table. | Satisfied. |
| Oracle-equivalence on rewritten queries | Z3 differential tests cover handcrafted sat/unsat queries and the committed micro corpus; the public QF_BV rewrite artifact records 0 rewrite decision changes, 0 sat/unsat conflicts, and 0 model replay failures. | Satisfied for the Phase 3 public slice. |
| Measured rewrite effect recorded | The public QF_BV artifact records 255,551 applications, DAG nodes reduced from 8,706,521 to 8,450,857, and tree nodes reduced from 58,335,915 to 57,824,813. | Satisfied; this is a size win, not a solve-time win. |
| Structural cache keys independent of arena IDs/labels | Query tests compare separately built equivalent arenas and show assertion/assumption roles produce distinct keys. | Satisfied. |
| Conservative slicing plus replay | Query tests prove target-support slicing drops only disjoint non-ground support, keeps ground terms, and rejects sliced `sat` models that do not satisfy the original query. Z3 integration tests cover sliced `sat` replay and sliced-`unsat` subset behavior. | Satisfied. |
| Query metrics exercised on corpus artifacts | The micro corpus benchmark records `summary.query_plan`: 3 files, 1 sliced instance, 1 dropped term, original DAG 14 to sliced DAG 12, and original tree 15 to sliced tree 12. The regenerated public QF_BV artifacts record 113 sliced first-assertion probes, 755,480 dropped terms, original DAG 8,706,521 to sliced DAG 336,691, and original tree 58,335,915 to sliced tree 2,307,699. | Satisfied. |

## Design Implications

- Phase 4 may start from rewritten/planned terms only if it preserves the
  replay discipline: models must lift back to the original query, not merely
  the last lowered form.
- The first Phase 4 note must record bit order before implementing public
  lowering APIs. Input and output wires need one shared value-to-wires
  convention so evaluator-vs-bits tests and SAT model lifting cannot diverge.
- Query-plan artifact fields are baseline telemetry, not an optimization
  promise. Slicing remains conservative until a broader query lifecycle and
  projection story exists.

## Risks

- The generated rewrite test is deterministic and broad for the current rule
  set, but it is not a proof. New rewrite classes still need their own focused
  and generated cases.
- The public QF_BV slice is useful corpus evidence, but it is not a replacement
  for later client-tier or adversarial corpora.
- Sliced `unsat` is only sound because the submitted constraints are a subset
  of the original conjunction. Future scopes, assumptions, activation
  literals, or cores must preserve that invariant explicitly.

## Open Questions

- [ ] What exact bit-order convention should Phase 4 use for value-to-wire and
      wire-to-value conversion?
- [ ] Should proof logging from adapters be surfaced before Phase 6?

## Source Pointers

- [Roadmap](roadmap.md)
- [Foundational DAG](foundational-dag.md)
- [Benchmarking methodology](benchmarking-and-performance-methodology.md)
- [ADR-0005 Phase 3 query/evidence/rewrite contracts](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)
- [Phase 3 rewrite-measurement artifact](../../../bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json)
