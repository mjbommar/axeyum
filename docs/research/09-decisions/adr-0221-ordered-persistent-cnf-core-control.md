# ADR-0221: Ordered persistent CNF core control

Status: accepted
Date: 2026-07-17

## Context

ADR-0220 sends each retained Dptf UNSAT CNF through fresh cores. That rejects a
simple fresh-core explanation for warm native Z3's end-to-end win, but it omits
the ordered SAT/UNSAT history that creates incremental learned state. An
UNSAT-only persistent replay was also invalid: skipping the intervening SAT
calls made BatSat approximately 3.6x faster than its profiled UNSAT population,
so it did not preserve the selected mechanism.

The replay-checked SAT cache is a second boundary. Cache hits can extend the
persistent clause database but do not invoke the SAT core and must not be
invented as solver calls in the control.

## Decision

Extend the opt-in Glaurung hook to snapshot every SAT-core decision, not only
UNSAT. Explicitly exclude replay-cache hits, while allowing their accumulated
clauses to appear in the next solver-call snapshot. Bind each DIMACS file to
outcome, path, query hash, process-local order, shape, and content hash.
Snapshot failures remain operational errors.

Add a fail-closed Axeyum runner that joins the snapshots to the warm profile,
rejects identity/cardinality/hash/shape drift, verifies active selectors are
positive units, and requires every per-path persistent clause database to be an
append-only prefix. Replay the complete ordered solver-call stream N=5 through
one persistent BatSat instance and one persistent Z3 Boolean instance per path.
Both cores receive a 250 ms per-call timeout; Z3 uses `random_seed=0`. Record
clause-add and solve time separately and require every verdict to match.

Each core retains its own learned clauses. Do not claim identical learned
state: BatSat learned clauses have no stable portable export, and clauses
learned by different algorithms are not expected to match. The controlled
variables are the Boolean input encoding, clause order, active assumptions,
solver-call order, path topology, timeout, and repetition schedule.

## Evidence

The corrected Dptf run has 561 decided queries: 317 SAT and 244 UNSAT. There
are 130 replay-cache hits and exactly 431 SAT-core calls/snapshots, comprising
187 SAT and 244 UNSAT calls across seven path-owned sessions. All 2,155 calls
per core over five replays agree with the captured outcome; no unknown,
operational, identity, prefix, or hash failure occurs.

Using one median per call, retained BatSat's clause-add/solve totals are
8.031/128.141 ms; retained Z3 Boolean's are 91.801/429.009 ms. Median/p95 solve
latencies are 0.109/1.405 ms for BatSat and 0.441/4.121 ms for Z3. The geometric
mean Z3/BatSat solve ratio is 3.5527x, favoring BatSat. Both outcome partitions
agree: 3.0401x on UNSAT and 4.3537x on SAT.

Exact evidence is committed under
[`bench-results/glaurung-dptf-persistent-cnf-20260717/`](../../../bench-results/glaurung-dptf-persistent-cnf-20260717/README.md).

## Alternatives

- Persist only the 244 UNSAT calls: rejected because it removes 187 SAT calls
  from the learned-state trajectory and produced an artificially easy stream.
- Treat all 561 decisions as SAT-core calls: rejected because 130 are
  replay-cache hits. The first prototype correctly failed rather than silently
  pairing stale snapshots; the capture was then narrowed to actual core calls.
- Export BatSat learned clauses into Z3: unavailable and conceptually
  asymmetric. The cores instead learn independently from the same ordered
  inputs.
- Compare absolute replay time directly with the Glaurung fair cells: rejected.
  This diagnostic omits all word-level and consumer work, and snapshot capture
  perturbs the producer run.

## Consequences

The retained-state/core hypothesis is closed for Axeyum's Boolean encoding:
Z3's persistent Boolean engine does not outrun BatSat on the same ordered CNF
stream. Warm native Z3's Dptf advantage must arise at the remaining
representation/integration boundary, where Z3 consumes word-level SMT and
Axeyum consumes its own bit-blasted CNF, or in work outside this core control.
This is evidence against prioritizing a custom SAT-core rewrite from the Dptf
result.

Proceed to a neutral end-to-end SMT baseline before making a cross-solver
performance claim. Multi-oracle fuzzing, timeout-sensitive workload evidence,
authoritative finding parity, and measured deployability remain publication
blockers.
