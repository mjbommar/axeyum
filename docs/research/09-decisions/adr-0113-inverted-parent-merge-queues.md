# ADR-0113: Inverted-parent merge queues

Status: accepted
Date: 2026-07-11

## Context

ADR-0112 makes add-only e-matching incremental, but every real e-class merge
still rebuilds the complete matching index and executes every pattern. This is
correct but discards the e-graph's existing inverted use lists: each class root
already owns the applications that use a member of that class as an argument.

Z3's MAM `on_merge` follows pattern-indexed inverted parent paths from both
merged classes and queues only candidate applications reached at compatible
path endpoints. Its path trees also account for repeated variables and ground
arguments. cvc5 retains operator-indexed ground-term lists and receives equality
engine merge notifications, avoiding a fresh term database per merge.

Axeyum currently caches complete substitution sets per interned pattern. A
merge can affect those caches in three ways:

1. a repeated-variable or ground constraint can become true in an existing
   application;
2. a nested application can enter an argument class and enable an existing
   outer candidate; or
3. substitutions from separate patterns can become compatible after their
   bound classes merge.

The first two effects have an application ancestor of a merged class. The third
does not require rematching either pattern if cached substitutions are compared
through current e-class roots.

## Decision

Retain a merge journal in `EGraph`, update `EMatchIndex` incrementally from that
journal, and dirty patterns through transitive inverted parent declarations.

The e-graph/index contract is:

1. record every real union, including congruence-cascade unions, as its retained
   root and absorbed root in deterministic processing order;
2. let an index remember its union-journal cursor and rollback generation;
3. on a normal merge refresh, move the absorbed class's indexed members into
   the retained class and advance the cursor instead of rebuilding the graph;
4. retain raw application-node lists by declaration, visit every application,
   canonicalize arguments only for declarations actually matched in the round,
   and deduplicate final substitutions rather than application classes (equal
   applications can still have unequal arguments);
5. rebuild fully after scope rollback, node-count rollback, or cross-graph
   reuse; and
6. expose a deterministic transitive parent-declaration walk from merge
   endpoints, cycle-safe under asserted recursive equalities.

The quantifier-session contract is:

1. collect every explicit equality endpoint that changes the e-graph;
2. after congruence closure, walk current parents transitively from those
   endpoints and dirty only patterns whose top declaration is reached;
3. independently dirty roots of newly added applications, since one source
   instance may both add terms and merge classes;
4. compare and combine every cached substitution through current roots, so
   simple-variable patterns and multi-pattern joins remain complete without
   blanket rematching; and
5. keep complete source instances and all public witness/evidence contracts
   unchanged.

### Completeness argument

Consider a pattern whose match set gains a substitution after a merge with no
new e-nodes. If the top application contains only unconstrained variables, the
same application already produced the corresponding cached substitution; root
canonicalization accounts for the merge. Otherwise, some equality-sensitive
check changed from false to true: a repeated variable, a ground subpattern, or
membership of a nested application in an argument class. Following the pattern
from that changed class outward traverses actual e-graph parent applications
and reaches the pattern's top declaration. The inverted-parent walk therefore
dirties that pattern. Cross-pattern variable compatibility is the same
root-canonical comparison applied during the join. Thus patterns outside the
reached top declarations cannot gain a semantically new substitution.

This slice indexes dependency by declaration rather than by exact pattern path,
so it may over-dirty patterns sharing a top symbol. That is conservative and is
the measurement baseline for later path-shape and relevance/generation filters.

## Acceptance

- Indexed matching remains extensionally identical to fresh `ematch_many`
  across add-only growth, direct merges, congruence cascades, recursive parent
  cycles, scope rollback, and cross-graph reuse.
- Direct, nested, repeated-variable, ground-subpattern, congruence-cascade, and
  multi-pattern-join merge targets return exactly the full-rematch tuples.
- A many-root merge target executes only the affected root pattern, performs no
  full index rebuild after the merge, and materially improves optimized
  second-round matching over ADR-0112 blanket invalidation including tuple join.
- A round that both adds an unrelated application and merges another class
  dirties the union of add- and merge-affected roots.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; public witness/evidence APIs remain unchanged.
- E-graph, solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc,
  links, foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. `EMatchIndex` consumes direct and
congruence-cascade unions without a full rebuild, while rollback and cross-graph
reuse retain the conservative rebuild boundary. Fresh/indexed parity covers
suffix growth, direct and nested merges, cascades, cycles, pop, and owner
changes. Session parity covers repeated variables, nested triggers, ground
subpatterns, simultaneous add-plus-merge roots, current-root substitution
joins, and explicitly equal applications with distinct argument bindings.

The committed target retains 64 repeated-variable trigger roots over 4,096
ground applications, then merges one argument pair under one root. The
selective path executes 1 pattern instead of 64 and returns the exact blanket
full-rebuild tuples. Five optimized complete-round full/selective measurements
in microseconds were 2232/143, 2231/152, 2230/151, 2223/160, and 2272/150:
medians 2.231/0.151 ms, a 93.2% reduction and 14.8x speedup including equality
registration, congruence closure, parent traversal, index refresh, matching, and
tuple joining.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46912 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11713/0.11646/0.11789 s (median 0.11713 s). All 1,000 direct-Z3 quantified-BV
and 900 bounded-instance cases agree. The Bitwuzla slice retains four expected
UNSAT decisions and its pre-existing SAT model-replay rejection.

E-graph 33/33, quantifier matching 37/37, solver library 841/841, evidence
69/69, MBQI 13/13, and bench 7/7 pass, as do workspace all-target/all-feature
Clippy, warning-denied rustdoc, links, formatting/diff, generated capability and
support matrices, and 137-concept/174-pack foundational resources. All 26
configured reference checkouts remain present.

## Alternatives

- **Continue full invalidation on merge.** Rejected: merge-heavy rounds remain
  linear in all retained patterns and nodes despite the e-graph use lists.
- **Dirty only declarations of the merged nodes.** Rejected: nested and repeated
  constraints change in parent applications, often several levels above the
  merged classes.
- **Reuse cached substitutions without root canonicalization.** Rejected:
  multi-pattern joins can miss bindings that become equal after a merge.
- **Compile exact Z3-style path trees immediately.** Deferred: declaration-level
  transitive paths establish a simpler exact baseline and expose the remaining
  over-dirty cost before adding path-shape filters or bytecode.
- **Discard the persistent index and scan the graph for each selected pattern.**
  Rejected: it forfeits ADR-0112's add-only performance and makes merge cost
  proportional to all nodes again.

## Consequences

- Merge rounds become proportional to union-journal updates, reachable parent
  paths, and affected root declarations rather than the whole pattern set.
- Application candidates are canonicalized lazily per matched declaration;
  this moves work from global rebuilds to the selected roots.
- The union journal is private invalidation/search metadata, not proof state or
  output. Scope rollback conservatively clears it and forces index rebuilds.
- Exact path-shape filters plus relevance/generation controls remain the next
  MAM optimization. Bytecode remains measurement-gated against recursive
  matching, and detached-literal justifications remain the next evidence step.
