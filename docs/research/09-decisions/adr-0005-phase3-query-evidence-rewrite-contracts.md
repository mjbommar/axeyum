# ADR-0005: Phase 3 Query, Evidence, And Rewrite Contracts

Status: accepted
Date: 2026-06-11

## Context

Phase 3 starts after the public QF_BV oracle baseline. The next roadmap layer is
rewriting and query planning, but the foundational DAG requires a query contract,
rewrite preservation contract, model-projection story, and evidence envelope
before default rewrites or slicing can become public behavior.

This closes the first Phase 3 entry questions about query shape, evidence
envelope shape, rewrite obligations, and whether equisatisfiability-only
rewrites may be enabled before projection exists.

## Decision

Add the Phase 3 contract boundary before adding rewrite rules:

1. `axeyum-query` owns the first-class query object. A `Query` is an owned,
   cheap-to-clone value over lifetime-free `TermId`s, with stable assertion,
   assumption, and scope IDs. Public query shape is assumptions-first; one-shot
   backends may enforce active assumptions as ordinary assertions, while future
   incremental backends may override `check_query` to use native assumption
   literals without changing query semantics.
2. `axeyum-rewrite` owns rewrite manifests before it owns rewrite algorithms.
   Each rule must declare a stable ID, name, sort/width/operator precondition,
   preservation class, model-projection obligation, required test routes, and
   whether it is enabled by default.
3. Default rewrites may be denotation-preserving immediately. A
   non-denotational, equisatisfiability-only rule may be recorded in the manifest
   while disabled, but it may not become a default rule until model projection is
   implemented and tested with projection replay.
4. The evidence envelope is layered. Every generated evidence artifact must be
   versioned and carry enough provenance to replay the result against the
   original query:
   - source query or corpus identity and hash;
   - selected logic and semantics/theory version;
   - query schema version and active assertion/assumption/scope labels;
   - rewrite rule-set version and applied rule IDs;
   - later layer versions for bit lowering, circuit, CNF, SAT backend, and proof
     checker;
   - seed and resource limits;
   - model replay result for every `sat`;
   - projection and lift-map references when a layer changes model shape;
   - proof/checker references for high-assurance `unsat`;
   - unsupported/error/soundness triage separated from ordinary `unknown`.

Do not create a separate evidence/proof crate yet. The envelope shape is recorded
as the artifact contract; concrete shared evidence types arrive when a second
artifact producer needs them.

## Evidence

- The benchmark artifact version 3 records source provenance, logic, selected
  families, hashes, backend version, seed, resource limits, rewrite
  provenance when enabled, per-instance shape metrics, unsupported/error
  triage, and model replay failures.
- `axeyum-query` now validates Boolean assertions and assumptions, preserves
  stable scope/term order, and is bridged into `SolverBackend::check_query`.
- `axeyum-rewrite` now rejects duplicate rule IDs, missing preconditions, missing
  test routes, and default equisatisfiability-only rules without implemented
  projection and replay tests.
- These choices preserve the project identity: fast search may transform and
  plan, but the trusted path remains the original query plus small replayable
  checks.

## Alternatives

- Implement the first rewrite rules directly in `axeyum-ir` or `axeyum-solver`.
  This was rejected because it would blur the query/rewrite contract and make
  evidence provenance retrofitted rather than designed.
- Add a full `axeyum-proof` or `axeyum-evidence` crate now. This was rejected as
  premature: the first concrete evidence artifact is still model replay and the
  benchmark JSON artifact, while proof and lift-map artifacts have not landed.
- Expose push/pop scopes as the first query API. This was rejected because
  assumptions are the more general primitive and can express both one-shot and
  future incremental behavior.

## Consequences

Phase 3 can now implement the first default canonicalizer rules, but only
denotation-preserving rules should be enabled until model projection is real.
Query slicing and cache-key work has a stable object to target, and every future
rewrite result has a manifest route into logs, benchmark artifacts, and
certificates.
