# ADR-0112: Revision-checked e-match index and candidate queues

Status: accepted
Date: 2026-07-11

## Context

ADR-0111 retains one ground e-graph and interns trigger patterns, but each
propagation round still reconstructs the complete root-to-class-members index,
rescans every application, and executes every pattern. When one newly asserted
source instance introduces terms under a single trigger root, unrelated
patterns cannot gain a match, yet they are rematched anyway.

Z3's MAM queues relevant added nodes and processes merge-dependent inverted
paths; cvc5 retains operator-indexed term lists and resets only the generators
needed for a round. Both avoid treating an add-only update as a fresh database.

Axeyum's indexes are keyed by current e-class roots. Appending nodes without a
merge preserves every old root, so indexes can be extended with only the new
node suffix. A real equality merge may change roots, class membership,
congruence, nested-pattern reachability, and cached substitutions. Narrowing
that invalidation requires the inverted parent/path dependency machinery that
has not landed yet.

## Decision

Add a revision-checked [`EMatchIndex`] to `axeyum-egraph` and root-symbol dirty
queues to the retained quantifier session.

The e-graph contract is:

1. maintain a monotone merge epoch that changes whenever a real class merge or
   scope pop can invalidate root-keyed data;
2. let an `EMatchIndex` own class members, operator-indexed applications,
   congruence de-dup sets, indexed node count, and observed merge epoch;
3. extend the index from the new node suffix when node count grows and the merge
   epoch is unchanged;
4. rebuild the index from scratch after a merge epoch change or node-count
   rollback; and
5. expose matching only through an API that refreshes the index before use, so a
   stale index cannot be queried accidentally.

The quantifier-session contract is:

1. map every interned pattern root declaration to its pattern indexes;
2. cache each pattern's latest complete substitution set;
3. on added application nodes without a real merge, mark only patterns with a
   matching root declaration dirty;
4. on any real merge, mark every pattern dirty and rely on the e-graph epoch to
   rebuild the index;
5. execute only dirty patterns, update their cached complete sets, and join all
   quantifiers against the cache; and
6. keep every pattern dirty initially, preserving first-round completeness.

This is a sound intermediate step toward Z3-style `on_merge`: add-only
propagation is selective, while merge propagation deliberately over-invalidates.
Inverted parent paths, relevance/generation filters, and bytecode remain open.

## Acceptance

- Incremental-index matching is extensionally identical to fresh `ematch_many`
  before and after add-only extension, direct merges, congruence cascades, and
  scope rollback; output remains deterministic.
- An add-only stress target with many unrelated trigger roots appends one
  application, executes only the affected root pattern, and returns exactly the
  same complete per-quantifier tuples as a full ADR-0111 rematch.
- A merge-dependent nested-pattern target invalidates all patterns and recovers
  the same newly enabled match as a fresh full rematch.
- Optimized second-round matching materially improves over ADR-0111's full
  rematch on the committed target, including index-refresh and tuple-join cost.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; existing evidence/public witness APIs remain unchanged.
- E-graph, solver, bounded-instance, evidence, Clippy, rustdoc, links,
  foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. The persistent index is exact against fresh matching
across add-only extension, direct/nested congruence merges, and scope rollback.
The committed queue target retains 64 unrelated trigger roots and 4,096 ground
applications, then appends one application under one root. It returns the same
complete tuples as an ADR-0111-style full rebuild while executing 1 pattern
instead of 64. Five optimized runs measured full/queued microseconds as
2569/307, 2652/315, 2527/290, 2524/311, and 2555/317: medians 2.555/0.311 ms,
an 87.8% reduction and 8.2x speedup including index refresh and tuple joining.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46905 s. Three quantified-LIA runs remain 12/12 and have PAR-2 means
0.11789/0.11688/0.11682 s. The direct Z3 differential suites agree on all 1,000
quantified-BV cases. The Bitwuzla slice retains four expected UNSAT decisions
and its pre-existing SAT model-replay failure. All acceptance gates passed.

## Alternatives

- **Keep rebuilding one index per round.** Rejected: it leaves the dominant
  add-only cost linear in the complete retained graph.
- **Reuse root-keyed indexes across merges without invalidation.** Rejected as
  unsound/incomplete: class roots and nested reachability can change.
- **Mark only root-symbol patterns dirty after merges.** Rejected: merging an
  argument class can enable an old nested or repeated-variable match under a
  different root declaration.
- **Implement inverted parent paths in the same slice.** Deferred: conservative
  merge invalidation gives a correctness baseline and isolates the measured
  value of selective add queues first.

## Consequences

- Add-only rounds become proportional to new nodes plus affected patterns,
  instead of all retained nodes and all patterns.
- Merge-heavy workloads retain ADR-0111 behavior rather than risking missed
  instances; this slice cannot claim full incremental-on-merge MAM completion.
- The merge epoch is an invalidation generation, not proof state and not output;
  it may advance conservatively without affecting determinism or explanations.
- ADR-0113 can add inverted parent paths and selective merge queues, measured
  against this revision-checked fallback.
