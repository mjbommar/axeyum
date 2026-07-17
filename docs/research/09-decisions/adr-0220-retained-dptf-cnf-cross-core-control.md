# ADR-0220: Retained Dptf CNF cross-core control

Status: accepted
Date: 2026-07-17

## Context

ADR-0219 shows that retained Dptf UNSAT checks are Axeyum's clearest losing
stratum and spend most internal time in CNF plus SAT. The profile exposes
counts, not the exact clause database or active selector assumptions. Rebuilding
each SMT-LIB query cold would change lowering, sharing, selectors, and learned
state and therefore would not test the selected mechanism.

## Decision

Add an opt-in diagnostic snapshot boundary to the incremental CNF stack.
`IncrementalSat` copies only its persistent input clauses. `IncrementalCnf`
materializes the exact active positive selector assumptions as unit clauses.
`IncrementalBvSolver` exposes that standalone formula only for profiled checks
and returns invariant failures explicitly. Learned clauses remain excluded
because the BatSat adapter does not expose a stable portable representation.

Add a Glaurung direct-delta hook that writes one hash-bound DIMACS/metadata pair
after every warm UNSAT when explicitly configured. Output failure turns the
diagnostic result into an operational error. Rendering and I/O occur after the
timed solve and invalidate outer benchmark timing.

Compare every snapshot through five fresh import/solve repetitions of BatSat,
Axeyum's proof-producing core, Z3's Boolean engine, and the current official
Kissat 4.0.4 release (`8af8e56f174b778aef3aa45af9f739b2a5f492c2`). Recheck the proof core's DRAT
output independently in a separate measured cell. Treat Z3 AST import and
Kissat subprocess startup as part of those diagnostic cells, not as fair
core-only performance.

## Evidence

The fixed Dptf run preserves 561 decisions: 317 SAT and 244 UNSAT. It emits 244
valid snapshots spanning 3--39,566 variables and 5--70,665 clauses. All four
cores return UNSAT on all 1,220 repetitions per core; all 1,220 proof-generation
plus self-recheck repetitions also pass.

Using one median per instance, BatSat totals 541.366 ms and the proof core
totals 220.913 ms. The geometric mean BatSat/proof-core ratio is 2.627x.
Proof generation plus independent DRAT checking totals 816.789 ms and has a
0.911x BatSat/rechecked-proof geometric ratio. Z3 fresh Boolean import/solve
totals 12,649.858 ms; the Kissat subprocess totals 1,849.164 ms. Those last two
cells include non-core overhead and are not publication speed comparisons.

Exact evidence is committed under
[`bench-results/glaurung-dptf-identical-cnf-20260717/`](../../../bench-results/glaurung-dptf-identical-cnf-20260717/README.md).

## Alternatives

- Re-lower standalone SMT-LIB queries: rejected because it loses retained
  sharing and selector topology.
- Export learned clauses: unavailable through the current BatSat adapter and
  not portable across cores.
- Call the Z3/Kissat cells fair speed baselines: rejected because AST import and
  subprocess startup dominate their fresh cells.
- Infer that BatSat alone explains the warm Z3 loss: rejected. The in-tree proof
  core beats BatSat on fresh identical CNF, while fresh Z3 is much slower; the
  warm cross-solver reversal therefore requires retained-state/integration
  evidence.

## Consequences

The exact-CNF verdict boundary is closed and yields a concrete DRAT deployment
case. The default fresh BatSat core is not the strongest in-tree UNSAT engine on
this slice, but replacing an incremental core with a fresh proof core is not an
admissible product change.

The next mechanism experiment must replay the ordered persistent clause stream
through matched retained cores or otherwise measure learned-state/topology
effects. Neutral end-to-end SMT baselines, multi-oracle fuzzing, timeout-sensitive
workloads, and authoritative finding parity remain publication blockers.
