# ADR-0162: Incremental direct positive-root fusion

Status: accepted
Date: 2026-07-15

## Context

ADR-0160 finds that native Glaurung incremental CNF owns 37.58% of attributed
time while exact overlap preserves the standalone AIG but emits more clauses.
ADR-0161 then measures the pinned 128-query gate: the incremental path emits
782,716 clauses versus 545,905 one-shot clauses over the same 450,498 AIG
nodes. Positive AND trees own 49.79% of lazy definition halves, and 1,789
asserted positive roots expose 109,358 AND nodes plus 90,149 structural XOR
leaves.

The one-shot encoder's global fusion plan cannot be copied wholesale: use
counts can change as a warm AIG grows, and scopes can deactivate assertions.
The bounded question is whether an assertion-local equivalence can remove the
dominant definitions without assuming that a node remains private.

## Decision

Enable assertion-local direct encoding for every positive incremental AND
root. Flatten positive AND edges into a deterministic set of conjunct leaves,
stopping at recognized XOR/XNOR and negated-ITE shapes. Emit one root-derived
clause per ordinary leaf and the exact two truth clauses per structural XOR
leaf. Guard every root-derived clause with the assertion's active selector.

Do not mark the flattened root, helper, or XOR node definitions as emitted.
If a later assertion reuses any bypassed node under another polarity or scope,
the existing lazy Plaisted-Greenbaum `require` path emits the ordinary
unconditional definition then. This makes the transformation independent of
global single-use counts and monotone under future AIG growth.

Keep negative roots, general internal mux/not-AND/AND-tree fusion, and global
clause deduplication out of this slice. Profiling reports opportunities and
actually fused roots/nodes/XOR leaves separately; ordinary constructors retain
zero diagnostic counters.

## Evidence

Focused tests cover exact clause reduction, positive-tree flattening,
structural XNOR truth, selector activation/deactivation, later
opposite-polarity reuse, monotone profile deltas, and the zero-counter ordinary
constructor. The existing brute-force incremental-versus-one-shot AIG suite,
randomized eager/lazy QF_BV differential, push/pop, one-shot assumptions,
symbolic-execution path exploration, and 34 SAT-BV model/proof replay tests are
green. Strict all-target/all-feature Clippy is green for the affected CNF,
solver, and benchmark crates under the 4 GiB wrapper.

The complete 4 GiB-capped `just check` gate is green: formatting, strict
workspace all-target/all-feature Clippy, all-feature tests and doctests,
warning-denied Rustdoc, the QF_BV feature profile, 31 Glaurung harness tests,
the pinned regular capture gate, foundational resources, generated-artifact
drift, and documentation links. The regular gate decides and manifest-matches
all 128 queries with zero errors, disagreements, or replay failures; this run's
raw/canonical Axeyum/Z3 ratios are 1.192x/0.349x.

On the pinned 128-query representative Glaurung corpus, all 128 queries decide
and agree with both the manifest and in-process Z3, with zero errors,
disagreements, or model-replay failures. The AIG stays at 450,498 nodes. All
1,789 positive roots, 109,358 positive AND nodes, and 90,149 structural XOR
leaves take the bounded path. Incremental clauses fall from 782,716 to 615,537:
167,179 fewer clauses, or 21.36%. The remaining incremental excess over the
same-revision one-shot artifact is 69,632 clauses (12.75%). The diagnostic
Axeyum/Z3 ratio moves from 1.272x to 1.197x, but remains timing-directional
only because profiling performs extra scans and counter updates.

The unprofiled native acceptance gate uses Glaurung commit `f56ffa8`, the
Z3-authoritative `win10-vwififlt.sys` stream, and isolated release builds of
Axeyum baseline `aa8ec437` versus the fused working revision. Two alternating
pairs each execute 13,126 identical queries with 13,126 agreements, zero
confident disagreements, and zero unknowns:

| Build | Axeyum mean | Z3 mean | Mean Axeyum/Z3 |
|---|---:|---:|---:|
| baseline | 18.484 s | 6.400 s | 2.888x |
| direct-root fusion | 17.648 s | 6.367 s | 2.772x |

Axeyum native time improves 4.52%; Z3 changes 0.52%; the normalized ratio
improves 4.0%. The same findings, severity counts, SAT count, and
Z3-authoritative exploration are preserved in every run.

## Alternatives

- **Enable the complete one-shot fusion planner incrementally.** Rejected:
  global private-use assumptions are not stable under later assertions.
- **Guard definitions as well as root clauses.** Rejected: unconditional
  definitions are reusable facts; guarding them would complicate polarity and
  scope bookkeeping without improving logical deactivation.
- **Only fuse roots currently seen once.** Rejected: the direct assertion
  equivalence is sound under sharing, and a current use count does not predict
  future reuse.
- **Treat the 21.36% clause reduction as sufficient.** Rejected: the roadmap
  requires lower unprofiled native client time as well as structural savings.
- **Fuse negative roots in the same change.** Rejected: their disjunctive
  encoding and measured population require a separate bounded gate.

## Consequences

The default incremental path now performs a deterministic assertion-local
root traversal, but avoids substantially more primitive definition work and
passes the real native client gate. Scope selectors, retained AIG structure,
SAT learned state, input-based AIG reconstruction, and original-term replay are
unchanged.

GQ5 remains open: 615,537 incremental clauses are still 12.75% above one-shot,
and the native fresh-client ratio remains about 2.77x on this driver. Attribute
the residual before selecting another fusion. The measured candidates are
negative roots/inverted-AND definitions, repeated guarded root clauses, and
other assertion-local patterns; do not infer a winner from syntactic counts.
GQ7 retained per-lineage warm state remains the structural route to reuse
across the 46.18% duplicate occurrences measured by ADR-0160.
