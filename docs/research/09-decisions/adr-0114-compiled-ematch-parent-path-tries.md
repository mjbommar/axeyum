# ADR-0114: Compiled e-match parent-path tries

Status: accepted
Date: 2026-07-11

## Context

ADR-0113 follows transitive e-class parents after a merge and dirties patterns
by their top declaration. This is exact when trigger roots differ, but patterns
that share a root symbol are all rematched even when only one nested declaration
and argument path is reachable from the changed classes.

Z3's MAM compiles paths such as `g.0 -> f.1` into shared inverted path trees.
Its merge callback walks e-node parents only along compatible declaration and
argument-position transitions, then queues code trees at terminal paths. Z3
adds approximate class-label, ground-argument, relevance, and generation
filters around this core path structure. ADR-0113 corresponds to the unshaped
transitive-parent baseline; the next isolated optimization is the exact path
structure itself.

Axeyum patterns are already recursively compiled and interned for one retained
session. The e-graph already maintains deterministic class-root parent use
lists. A shared trie over `(parent declaration, argument index)` transitions can
therefore select pattern ids without rescanning pattern trees or unrelated
parent branches at merge time.

## Decision

Compile every interned pattern's child-to-root application paths into one flat,
shared transition trie and use it for merge invalidation.

The contract is:

1. expose the current root class's parent application use list read-only from
   `EGraph`; mutation remains owned by the e-graph;
2. for every non-root pattern occurrence, compile its outward path as ordered
   `(declaration, argument index)` steps to the trigger root;
3. share common prefixes in a deterministic flat trie whose terminal lists are
   sorted, deduplicated pattern ids;
4. after a real merge, start at each changed class and follow only parent edges
   accepted by trie transitions, pairing visited e-classes with trie-node ids so
   recursive equalities terminate without dropping distinct paths;
5. dirty terminal patterns reached by the walk, then retain ADR-0113's current-
   root cached-substitution joins and merge-journal index refresh;
6. keep add-node invalidation operator-indexed, since a new top application can
   match any pattern with that root declaration; and
7. retain declaration-level and blanket invalidation only as test baselines.

Paths are compiled for immediate nested children as well as deeper leaves. For
`f(g(x))`, merging a class with an existing `g` application can enable the
suffix `f.0`, while merging `x`-candidate classes follows `g.0 -> f.0`.
Repeated variables compile each occurrence path independently. Ground
subpatterns use the same conservative path shape; exact class-label/ground-term
filters remain a later layer.

### Completeness argument

ADR-0113 establishes that every semantically new match caused by a merge has a
parent path from a changed class to the trigger root, except effects handled by
current-root cached joins. The compiled trie contains the path from every
pattern occurrence to that root. The query walks every actual parent argument
whose current root is the reached class and advances only when declaration and
argument index equal the compiled step. Therefore the path witnessing any new
match reaches its pattern terminal. Rejecting a parent edge absent from the trie
cannot remove a match for any registered pattern.

This is exact for declaration/argument path shape, not for class labels,
relevance, or generation. Patterns with identical path shapes but different
ground constants or expected nested class labels may still be over-dirtied.

## Acceptance

- Path-trie selection is a subset of ADR-0113 declaration-level selection and
  returns exactly the same complete tuples as declaration and blanket full
  rematching for direct, nested, repeated-variable, ground-subpattern,
  congruence-cascade, multi-pattern, and equal-application cases.
- Shared prefixes, divergent declaration steps, divergent argument positions,
  duplicate paths, multiple merge roots, and recursive e-class cycles are
  deterministic and complete.
- A round that both adds a root and merges another class dirties the union of
  operator-add and path-terminal pattern ids.
- A many-pattern target with one shared top declaration and divergent nested
  paths executes only the reached pattern and materially improves optimized
  complete-round time over ADR-0113 declaration-level invalidation.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; public witness/evidence APIs remain unchanged.
- E-graph, solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc,
  links, foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. The flat path trie shares prefixes, preserves sorted
deduplicated terminals, distinguishes both declaration and argument-position
transitions, handles duplicate registrations and multiple merge starts, and
terminates on recursive e-class parents using `(class, trie-node)` visited
states. Existing direct, nested, repeated-variable, ground-subpattern,
add-plus-merge, equal-application, current-root join, and declaration/full-
rematch parity targets remain exact.

The committed target retains 64 patterns with one shared outer trigger
declaration, 64 distinct nested binary declarations, and 4,096 ground
applications. Merging one argument pair reaches one nested path. Exact lookup
executes 1 pattern instead of ADR-0113's 64-pattern top-declaration set and
returns identical complete tuples. Five optimized complete-round
declaration/exact measurements in microseconds were 12759/403, 12777/396,
12848/383, 12794/379, and 12699/386: medians 12.777/0.386 ms, a 97.0% reduction
and 33.1x speedup including equality registration, congruence closure, path
lookup, merge-journal refresh, matching, and tuple joining.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46935 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11801/0.11791/0.11715 s (median 0.11791 s). All 1,000 direct-Z3 quantified-BV
and 900 bounded-instance cases agree. The Bitwuzla slice retains four expected
UNSAT decisions and its pre-existing SAT model-replay rejection.

E-graph 33/33, quantifier matching 40/40, solver library 844/844, evidence
69/69, MBQI 13/13, and bench 7/7 pass, as do workspace all-target/all-feature
Clippy, warning-denied rustdoc, links, formatting/diff, generated capability and
support matrices, and 137-concept/174-pack foundational resources. All 26
configured reference checkouts remain present.

## Alternatives

- **Keep top-declaration invalidation.** Rejected: it is needlessly linear in
  every pattern sharing a popular function symbol.
- **Compile one path vector per pattern and test them independently.** Rejected:
  common prefixes would repeatedly traverse the same e-class parent use lists.
- **Fold labels, relevance, generations, and bytecode into this slice.**
  Deferred: measuring the path trie independently identifies whether each later
  filter removes meaningful remaining work.
- **Store solver pattern ids in the e-graph.** Rejected: the e-graph remains a
  generic equality keystone; quantifier-specific compilation belongs to the
  retained solver session.

## Consequences

- Merge invalidation cost becomes proportional to compatible parent paths and
  reached terminals rather than all ancestors sharing a top declaration.
- The public e-graph gains a read-only current-class parent-use API; no solver
  pattern or quantifier state enters the e-graph crate.
- Class-label/ground-argument filters and relevance/generation controls remain
  the next MAM depth. Bytecode remains measurement-gated against the recursive
  matcher, followed by detached-literal online justifications.
