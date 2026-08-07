# QF_NIA A3 clause-estimate attribution v2 preregistration — 2026-08-07

## Repair boundary

V1 correctly stopped when the copied dense-demand stack generated 8,000,001
requests. It may not be rescued by raising that frozen limit. V2 changes only
the analysis algorithm: compute the same least fixed point with eager duplicate
suppression, schedule every unique term bit at most once, and propagate the
identical full-child demand of a non-local arithmetic barrier once per term.

The v1 result and failure remain immutable. V2 must begin from the commit that
contains the v1 reproducer/result and this preregistration. Production solver,
bit-lowering, integer-blasting, route, budget, deadline, verdict, and replay code
remain out of scope.

## Frozen population and measurements

V2 retains verbatim the two targets, SHA-256 values, width 32 blast, expected
clause estimates, per-operator/per-width accounting, multiplier classifications,
20% disposition thresholds, and complete-record requirements from the
[`v1 preregistration`](qf-nia-a3-clause-estimate-attribution-v1-preregistration-2026-08-07.md).
It still accepts only the frozen basenames, refuses digest or estimate drift,
and never calls an AIG/CNF lowerer or solver.

## Exact fixed-point algorithm and work bounds

Maintain one 128-bit demand mask per arena term. `schedule(term, bit)` sets a
previously absent bit and enqueues it; an already-set bit does no work. Process
each queued unique term bit with the existing demand-local transfer rule:
extract, concat, extensions, bitwise operators, Boolean operators, ITE, and
rotates retain their bit-local mappings. For any other application, all bits of
every operand are demanded. Because that mapping is identical for every output
bit, a per-term `barrier_propagated` flag performs it once. This is a work-list
optimization of the same monotone equations, not a weaker demand relation.

Fail closed if any of these independent ceilings is exceeded:

- 2,000,000 reachable shared nodes;
- 2,000,000 scheduled unique term bits;
- 8,000,000 attempted transfer edges; or
- any lowerable sort wider than the diagnostic's 128-bit mask.

The program may retain demand masks, the barrier flags, term IDs, work lists,
and aggregate counters only. It may not allocate AIG literals/gates, CNF state,
solver state, or models. Output remains all-or-nothing JSONL.

Add tests proving duplicate scheduling is idempotent, a partially demanded
arithmetic result still fully demands its operands, and repeated output-bit
requests propagate a non-local barrier once. Retain the v1 class, sharing,
width, reconciliation, and deterministic-serialization tests.

## Decision and stop rules

Both records must pass source, estimate, accounting, demand-completeness, and
work-bound invariants. Classify each target using the frozen 20% rules. A v2
budget failure, invariant mismatch, or wrong estimate closes this diagnostic
route without a production edit; do not create v3 merely to raise a limit.

Only two complete records selecting the same nontrivial candidate class may
authorize a separately preregistered production mechanism. That later protocol
must still preserve the absolute 64,000,000 pre-allocation ceiling, fail closed
when its proof is unavailable, avoid materializing a circuit to measure it,
retain original-integer SAT replay, decide at least one target in two of three
observations, and remove the mechanism completely if the target gate fails.
