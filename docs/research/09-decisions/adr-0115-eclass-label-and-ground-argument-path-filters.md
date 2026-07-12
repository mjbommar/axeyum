# ADR-0115: E-class label and ground-argument path filters

Status: accepted
Date: 2026-07-11

## Context

ADR-0114 compiles exact `(declaration, argument-index)` parent paths, but paths
with identical shape still share terminals even when their expected nested
subpattern declarations or ground sibling arguments differ. For example,
`f(g(x), c)` and `f(h(x), d)` both have the immediate path `f.0`; merging an
arbitrary class into an `f` argument currently dirties both patterns.

Z3's MAM associates approximate declaration labels with e-classes and path-tree
nodes. It also stores one available ground sibling per path step and requires
the candidate parent's corresponding argument to be equal to that ground term.
These filters prune candidates before bytecode interpretation while remaining
conservative under equality merges.

Axeyum can make the first version exact rather than approximate. Every e-node
has a stable declaration id, and union-by-size already owns backtrackable class
state. Pattern nullary applications represent exact free constants in the
retained bridge, so their declaration labels are sufficient to test equality
modulo the e-graph. Compound ground siblings need structural/class witnesses
and remain outside this slice.

## Decision

Maintain exact declaration-label sets on e-class roots and compile two filters
into the ADR-0114 path trie:

1. **start-class label:** a terminal reached from a non-variable pattern
   occurrence requires the changed starting class to contain that occurrence's
   top declaration;
2. **ground sibling:** each path step records the first nullary ground argument
   of its parent pattern application, if any, and requires the candidate
   parent's corresponding argument class to contain that declaration.

The e-graph contract is:

1. initialize each new class with its node declaration;
2. merge sorted unique declaration sets at every direct or congruence union;
3. trail and restore the retained root's prior set on pop;
4. expose only `class_has_declaration(node, declaration)` as the stable query
   surface; and
5. keep labels out of equality, proof, output, and hash-cons semantics.

The path-index contract is:

1. transitions are keyed by declaration, argument index, and optional nullary
   ground-sibling filter;
2. terminals carry pattern id plus an optional required starting declaration;
3. shared prefixes remain deterministic; terminals are sorted and deduplicated;
4. query state retains the canonical starting class so terminal labels are
   checked at any path depth;
5. filtered transitions advance only when the candidate sibling class contains
   the required ground declaration; and
6. unfiltered, label-only, ground-only, declaration-level, and blanket modes
   remain test-only baselines.

### Soundness and completeness

If a nested or ground pattern occurrence matches the changed class, that class
contains an e-node with the occurrence's top declaration, so its start-label
test passes. If a nullary ground sibling is part of a matching parent, the
candidate sibling class contains that exact declaration, so the ground filter
passes. Variables carry no start label. Filters are omitted for compound ground
siblings that cannot be proved by one declaration. Therefore every path that
can witness a new match remains traversable; failed filters can reject only
patterns whose required class membership/equality is absent.

## Acceptance

- Class declaration membership is exact through add, direct merge, congruence
  cascade, nested scopes, pop, and recursive equalities; it does not affect
  congruence explanations or deterministic output.
- Filtered path selection is a subset of ADR-0114 unfiltered path selection and
  returns exactly the same complete witness tuples as unfiltered,
  declaration-level, and blanket rematching.
- Variables, nested applications, nullary ground occurrences, ground siblings,
  repeated variables, shared prefixes, duplicate filters, multiple starts, and
  cycles have focused positive and negative gates.
- A round that adds applications and merges classes still dirties the union of
  root-add and filtered path terminals.
- A matrix target with shared path shape but distinct nested labels and ground
  constants separately measures unfiltered, label-only, ground-only, and
  combined modes; each filter reduces pattern executions and the combined mode
  materially improves optimized complete-round time over ADR-0114.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; public witness/evidence APIs remain unchanged.
- E-graph, solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc,
  links, foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. E-class roots now maintain sorted declaration sets
through add, direct and congruence unions, nested scopes, and rollback. The
retained path trie checks the original changed class's expected nested label at
terminals and one direct nullary ground sibling on transitions. Variable starts
and compound ground siblings remain unfiltered. Existing direct, nested,
repeated-variable, ground, add-plus-merge, equal-application, shared-prefix,
multi-start, cycle, current-root join, and full/declaration-rematch parity gates
remain exact.

The committed matrix has eight nested declarations, eight nullary constants,
64 same-shape patterns, and 4,096 applications. One merge reaches 64 unfiltered,
8 class-only, 8 ground-only, and 1 combined terminal, and every mode returns the
same complete tuples. Five optimized complete-round measurements in
microseconds were 13589/2282/2044/409, 13453/2326/1981/401,
13387/2314/1918/403, 13500/2265/1991/415, and 13441/2354/2050/404. Medians are
13.453/2.314/1.991/0.404 ms: class labels reduce time 82.8% (5.81x), ground
arguments 85.2% (6.76x), and the combined route 97.0% (33.3x) relative to
unfiltered exact-path lookup.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46935 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11882/0.11863/0.11889 s (median 0.11882 s). All 1,000 direct-Z3 quantified-BV
and 900 bounded-instance cases agree. The Bitwuzla slice retains four expected
UNSAT decisions and its pre-existing SAT model-replay rejection.

E-graph 34/34, quantifier matching 41/41, solver library 845/845, evidence
69/69, MBQI 13/13, and bench 7/7 pass, as do workspace all-target/all-feature
Clippy, warning-denied rustdoc, links, formatting/diff, generated capability and
support matrices, and 137-concept/174-pack foundational resources. All 26
configured reference checkouts remain present.

## Alternatives

- **Use hashed approximate labels immediately.** Rejected for this scale: exact
  sorted declaration sets avoid false negatives and give a clear baseline.
- **Scan all class members when filtering.** Rejected: it makes every path check
  linear in class size and discards the value of retained class metadata.
- **Require only the child declaration encoded in the next path step.**
  Rejected: immediate nested-class merges use a path suffix that does not
  traverse the nested application itself.
- **Filter arbitrary compound ground siblings by top declaration.** Rejected as
  too weak to prove equality; different `g(a)` and `g(b)` terms share a label.
- **Add relevance and generation in the same slice.** Deferred so their
  independent workload reduction can be measured after exact semantic filters.

## Consequences

- E-class roots gain a compact exact declaration set with backtracking cost
  proportional to declarations introduced by unions.
- Same-shape path terminals can be pruned by semantic class membership and
  exact nullary ground equality before any pattern rematch.
- Compound-ground structural filters, relevance, and generation remain the next
  MAM layers. Bytecode remains measurement-gated, followed by detached-literal
  online justifications.
