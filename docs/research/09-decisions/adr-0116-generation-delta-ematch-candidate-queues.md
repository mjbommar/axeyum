# ADR-0116: Generation-delta e-match candidate queues

Status: accepted
Date: 2026-07-11

## Context

ADR-0112 through ADR-0115 identify which patterns can gain matches after an
add or merge, but executing one dirty pattern still scans every retained
application with its root declaration. The same-shape filter target therefore
reaches one pattern yet scans all 4,096 outer applications.

Z3's MAM queues relevant enodes, records their generation, and carries the
maximum generation of a match into instantiation scheduling. Its relevance
predicate excludes terms internalized by the SAT/SMT context but not active in
the current search. Axeyum's retained quantifier bridge currently contains only
active asserted ground terms and their recursively required subterms, and grows
monotonically within one refutation attempt. Every bridge node is therefore
relevant by construction; adding a relevance bit would not reject a candidate.

The useful equivalent generation boundary is the retained e-graph's node suffix
plus the merge path terminal. An add-only match that was not previously cached
must have a newly created top application. A merge-created match must have a top
application reached by the occurrence-to-root path that witnesses the match.

## Decision

Retain complete pattern-match caches and update them from exact top-application
deltas:

1. expose candidate-restricted indexed e-matching that accepts explicit top
   application ids and otherwise uses the same class index and recursive matcher;
2. during initial matching or index rollback, scan the complete root-declaration
   application set and replace the cache;
3. on add-only growth, queue each new application for patterns with the same root
   declaration;
4. on a merge, extend the ADR-0115 filtered path walk to return each reached
   `(pattern, top application)` terminal;
5. match only queued top applications and append sorted/deduplicated
   substitutions to the retained pattern cache;
6. keep cached substitutions across monotonic unions and canonicalize them only
   when joining or lifting witnesses; and
7. retain full-pattern and pattern-only invalidation as test baselines.

No public result or evidence format changes. Relevance metadata remains deferred
until a retained bridge can contain inactive terms; at that point relevance must
be backtrackable and activation must enqueue the newly relevant application.
Generation numbers for cost scheduling are separate from this exact delta
ownership slice.

### Completeness argument

Adds and equality unions are monotonic, so a previously valid match remains
valid modulo newer roots. If an add creates a new match, the match's top
application is new: existing immutable applications and existing equalities
could already have produced it. If a union creates a new match, ADR-0113's
parent-path argument and ADR-0114/0115's exact filtered trie reach a top
application witnessing that match. Candidate-restricted matching runs the
unchanged recursive matcher at that application. Appending those substitutions
to the retained cache therefore yields the same canonical witness tuples as a
fresh full rematch.

Multi-pattern joins need no extra candidate when a merge only makes two cached
substitutions compatible: joins compare current e-class roots. Explicitly equal
top applications with unequal arguments retain both cached substitutions.

## Acceptance

- Candidate-restricted matching is extensionally equal to filtering a full
  indexed match by the same top applications.
- Initial, add-only, direct merge, congruence-cascade, nested, repeated-variable,
  ground-subpattern, ground-sibling, multi-pattern, equal-top-application,
  recursive-cycle, and rollback paths match fresh full-rematch witnesses.
- Add-plus-merge rounds consume the union of new and merge-reached candidates.
- A many-application target executes one affected pattern in both modes but
  candidate-delta matching scans materially fewer top applications and improves
  optimized complete-round time.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; public witness/evidence APIs remain unchanged.
- E-graph, solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc,
  links, foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. `EGraph` now exposes deterministic application-node
suffixes and candidate-restricted batched matching through the same persistent
class index and recursive matcher. The retained quantifier session performs one
complete initialization, then appends matches from new top applications or
ADR-0115-filtered merge-path terminals. Full-pattern replacement remains a
test-only baseline. Cached substitutions survive monotonic unions and are
canonicalized only at joins and witness lifting.

Candidate/full parity passes for initial, add-only, direct and nested merge,
repeated-variable, ground-subpattern/sibling, add-plus-merge, multi-round,
current-root join, and explicitly equal top-application cases. The generic
e-graph candidate API independently checks duplicate/wrong-declaration
candidates and post-merge roots. Every retained bridge term remains relevant by
construction, so no relevance bit was added.

The committed target retains one affected pattern over 4,096 outer
applications. Both modes execute that pattern and return the same one-tuple
result; full matching scans 4,096 top applications while delta matching scans
one. Five optimized complete-round full/delta measurements in microseconds were
370/116, 346/114, 381/125, 378/129, and 361/122. Medians are 0.370/0.122 ms, a
67.0% reduction and 3.03x speedup including equality registration, congruence
closure, filtered path traversal, index refresh, matching, cache append, and
tuple lifting.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46919 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11871/0.11815/0.11828 s (median 0.11828 s). All 1,000 direct-Z3 quantified-BV
and 900 bounded-instance cases agree. The Bitwuzla slice retains four expected
UNSAT decisions and its pre-existing SAT model-replay rejection.

E-graph 35/35, quantifier matching 42/42, solver library 846/846, evidence
69/69, MBQI 13/13, and bench 7/7 pass, as do workspace all-target/all-feature
Clippy, warning-denied rustdoc, links, formatting/diff, generated capability and
support matrices, and 137-concept/174-pack foundational resources. All 26
configured reference checkouts remain present.

## Alternatives

- **Add a relevance bit now.** Deferred: every retained bridge node is active by
  construction, so the bit would add state without filtering work.
- **Replace cached matches after every delta.** Rejected: candidate matching is
  intentionally incomplete for old top applications; its results must append.
- **Use node creation ids alone for merge rounds.** Rejected: a merge can enable
  a match at an old application, so the filtered parent path must supply it.
- **Store only canonical substitutions.** Rejected: later unions would lose the
  distinct `f(a)`/`f(b)` bindings required while `a` and `b` remain unequal.
- **Add generation-cost scheduling simultaneously.** Deferred so exact scanning
  reduction is measured independently from heuristic instance ordering.

## Consequences

- Dirty-pattern execution becomes dirty-application execution after the initial
  scan, while using the same matcher and evidence route.
- Per-session state gains deterministic candidate sets and append-only match
  caches.
- Relevance remains an explicit measured no-op boundary; generation-based cost
  scheduling and bytecode remain later, separately measured layers.
