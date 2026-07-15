# ADR-0161: Opt-in incremental CNF gate-mix attribution

Status: accepted
Date: 2026-07-15

## Context

ADR-0160 attributes 37.58% of the first native Glaurung profile to
incremental CNF construction and pairs exact queries with the standalone
one-shot encoder: both routes retain the same AIG, but the incremental route
emits substantially more clauses. GQ5 therefore needs to know which
polarity-specific definitions and directly asserted root shapes create the
inflation before porting a one-shot fusion. Aggregate variables and clauses
cannot distinguish an XOR opportunity from a positive AND tree or an ordinary
binary AND.

The production incremental path must not pay for recursive shape discovery or
diagnostic counters. Attribution also has to preserve the existing lazy
Plaisted-Greenbaum encoding, scope selectors, deterministic traversal, and
model-replay contract; it is a measurement boundary, not a solver policy.

## Decision

Add an opt-in `IncrementalCnf::with_profiling` constructor and monotone
`IncrementalCnfStats`, surfaced through the already opt-in
`IncrementalBvSolver` profile. Ordinary constructors keep all new counters at
zero and do not run direct-root shape scans.

Partition every emitted lazy definition half into exactly one structural
family: XOR, negated ITE, inverted-AND, positive AND-tree, or ordinary binary
AND. Separately count constant, definition, and root clauses, synchronized AND
nodes, and direct-root opportunities. A positive-AND opportunity scan flattens
the root deterministically while treating structural XOR and negated-ITE
patterns as leaves; it reports root count, traversed AND nodes, unique leaves,
and specialized leaves. Negative AND roots are counted separately. The scan
does not change emitted clauses.

Add the explicit benchmark backend `incremental-bv-raw-profile`. It uses a
fresh profiled incremental solver per instance, preserves the raw assertion
policy, and exports the gate-mix counters in the ordinary benchmark artifact.
The existing `incremental-bv-batch` backend remains unprofiled and unchanged.

## Evidence

Focused CNF tests prove that definition halves form an exact partition, direct
root discovery stops at parity leaves rather than flattening their helper
shape, snapshot deltas are monotone, and the ordinary constructor leaves every
profile counter at zero. Solver tests cover profile propagation and the
ordinary zero-counter path. Strict all-target/all-feature Clippy is green for
`axeyum-cnf`, `axeyum-solver`, and `axeyum-bench` under the 4 GiB wrapper.

The release profile of the pinned 128-query representative Glaurung corpus is
100% decided, agrees with all 128 manifest outcomes and all 128 in-process Z3
oracle outcomes, and has zero errors, disagreements, or model-replay failures.
Across the corpus it records 450,498 AIG nodes, 422,034 synchronized AND nodes,
450,497 CNF variables, and 782,716 clauses. Clause accounting reconciles to
127 constant, 778,534 definition, and 4,055 root clauses.

The 508,729 emitted definition halves partition as follows:

| Structural family | Definition halves | Share |
|---|---:|---:|
| positive AND-tree | 253,274 | 49.79% |
| inverted-AND | 141,670 | 27.85% |
| XOR | 95,780 | 18.83% |
| binary AND | 18,003 | 3.54% |
| negated ITE | 2 | <0.01% |

There are 1,789 direct positive-AND roots spanning 109,358 tree nodes and
111,147 unique leaves; 90,149 of those leaves are structural XORs and none is
a negated ITE. There are also 804 negative-AND roots. The same-revision
standalone raw artifact retains the same 450,498 AIG nodes but emits 545,905
clauses. The profiled incremental encoder therefore emits 236,811 additional
clauses (+43.38%). Its one-shot comparison reports 50,434 XOR gates, 35,125
inverted-AND gates, 2,047 AND-tree gates, 73,049 binary gates, 1,911 direct
roots, and 259,547 skipped helper nodes.

This is structural attribution, not a timing acceptance result: profiling adds
shape scans and counter updates, and the benchmark's 1.272 Axeyum/Z3 ratio
must not replace the ordinary GQ10 baseline.

## Alternatives

- **Port every one-shot fusion at once.** Rejected: selectors and later reuse
  make incremental correctness distinct, and the measured distribution should
  select a bounded first slice.
- **Count only syntactic AIG node shapes.** Rejected: lazy encoding cost is
  polarity-specific; an available gate is not necessarily a definition half
  or a directly asserted opportunity.
- **Make gate-mix counters always on.** Rejected: recursive positive-root scans
  would tax every production assertion and corrupt the client boundary being
  optimized.
- **Prioritize negated ITE or ordinary binary AND.** Rejected for the first
  slice: the measured direct-root population contains no negated-ITE leaves,
  while positive AND trees and XOR leaves dominate.

## Consequences

GQ5's first implementation target is a scope-safe direct positive-root
encoder: flatten asserted positive AND trees and encode structural XOR leaves
directly, while guarding every root-derived clause with the active selector.
It must leave the AIG unchanged, retain lazy ordinary definitions for any node
later reused under another polarity or scope, preserve model lifting/replay,
and be accepted only if both clause count and unprofiled native Glaurung time
fall. Negative-root fusion and broader global single-use reasoning remain
separate measured slices.

The profiling backend remains attribution-only. Future fusion counters must
distinguish opportunities from transformations actually applied, so a missed
or unprofitable shape cannot be reported as a saving.
