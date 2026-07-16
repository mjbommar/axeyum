# ADR-0189: Replay-checked same-arena SAT duplicate cache

Status: accepted
Date: 2026-07-16

## Context

GQ8 asks whether Axeyum may reuse verdicts for repeated Glaurung queries. The
ordered corpus measures 957 exact duplicate occurrences, including 439 within
one lineage, but it also measures 2,192 strict prefix extensions. Those are
different semantic cases: an exact duplicate may reuse evidence, while a
strictly stronger or weaker query may only reuse retained lowering, CNF, and
SAT state.

Axeyum's ordinary incremental SAT result carries a model that can be checked
against the untouched source terms. Its ordinary incremental UNSAT result does
not carry a source-bound proof. A structural hash is likewise insufficient as
evidence identity: it is an index accelerator and may collide. The cache
boundary must therefore be fixed before performance code can influence solver
results.

This closes “What may an exact-verdict cache reuse without weakening
evidence?” in the
[research-question register](../08-planning/research-questions.md).

## Decision

The first GQ8 verdict cache is an explicit, disabled-by-default,
per-`IncrementalBvSolver` cache for exact scalar Bool/QF_BV SAT duplicates in
the same `TermArena`; every hit is accepted only after the cached model replays
against every current original assertion and one-shot assumption.

The contract is:

- cache identity is the exact ordered active assertion `TermId` sequence plus
  the exact ordered one-shot assumption sequence. Term IDs are structural only
  within the solver's lifetime-bound arena, so the cache cannot move between
  solvers, arenas, lineages, threads, processes, or artifacts;
- any digest or [`StructuralCacheKey`](../../../crates/axeyum-query/src/planning.rs)
  may accelerate lookup but never replaces exact equality;
- the owning solver/configuration and active scope are implicit namespace
  boundaries. Every future operation that changes the solution set without
  changing the exact term sequences must invalidate the cache or advance an
  explicit semantic revision;
- only `Sat(Model)` is inserted. `Unsat`, `Unknown`, errors, assumption cores,
  and strict prefixes are never cached as verdicts by this implementation;
- a SAT hit calls the same original-term replay used by a fresh incremental
  solve. False or non-Boolean replay is a soundness error. Evaluation failure
  degrades to `Unknown`; neither outcome is returned as a cache hit;
- UNSAT may enter a future cache only as source-bound proof evidence that is
  rechecked against the current original terms, for example with
  `UnsatProof::recheck_for_bool_terms`. Ordinary `CheckResult::Unsat` is not
  sufficient;
- strict prefix extensions, contractions, and siblings reuse only the existing
  scoped AIG/CNF/SAT state. Satisfiability is not monotone in a direction that
  authorizes returning the predecessor's verdict and model;
- capacity, model-value budget, eviction order, invalidation, hits, misses,
  insertions, evictions, replay failures, and declined non-SAT results are
  deterministic and observable; and
- Glaurung may not enable the cache by default until same-stream measurements
  clear the existing verdict, original-model replay, finding, memory, and
  performance gates.

This is a result accelerator outside the trusted reasoning base. Original-term
replay remains the SAT acceptance boundary, and no cached result upgrades the
assurance of the evidence it contains.

## Evidence

`IncrementalBvSolver` is documented and implemented as bound to one
`TermArena`. It retains every original assertion in its scope frames and its
`replay` routine evaluates every active original assertion plus every one-shot
assumption before returning SAT. The ordered Glaurung tier establishes enough
same-stream duplication to justify a bounded experiment without conflating
the much larger prefix-reuse population.

Conversely, `CheckResult::Unsat` contains no proof object. Axeyum's separate
`UnsatProof` API demonstrates the stronger required route: its source-bound
checker deterministically rederives term-to-CNF lowering before accepting the
proof. Returning an ordinary cached UNSAT verdict would bypass that boundary.

## Alternatives

A process-global cache keyed only by SMT-LIB bytes or a 64-bit structural hash
was rejected because symbol/model identity, configuration semantics, collision
checking, and source evidence would be ambiguous. Cross-arena reuse was
rejected for v1 because `Model` is keyed by arena-local `SymbolId`; it requires
a canonical structural serialization and checked symbol remapping. Caching
ordinary UNSAT was rejected because rerunning proof checking is not currently
available on that result path. Treating prefix extensions as verdict hits was
rejected as unsound.

## Consequences

Implementation can now be small and fail closed: an opt-in cache lives inside
one incremental solver, stores only replayable scalar SAT models, uses exact
term-sequence equality, and has deterministic bounded storage and telemetry.
Pop may reactivate a prior exact query and soundly reuse its replayed model;
`block_model` changes the assertion sequence and therefore changes identity.

The design deliberately leaves performance headroom unclaimed. Cross-lineage
or persistent caches need a new canonical identity/model-remapping ADR. UNSAT
reuse needs proof production and source-bound rechecking on the production
path. Prefix performance remains GQ7 retained-state work, not GQ8 verdict
caching.
