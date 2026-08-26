# ADR-0574: Job-shop detectable precedences close to a fixpoint

Status: accepted
Date: 2026-08-26
Index-summary: Propagate only logically forced machine precedences and expose their deterministic closure

## Context

ADR-0572 made exact job-chain windows and semantic machine-order selectors public. On
`abz7@655`, 256 of 2,850 machine pairs already have only one ordering compatible with those
windows, but the SAT encoding previously left the corresponding selector implication
implicit. More generally, adding one forced machine edge can tighten downstream earliest and
latest starts and expose another forced edge. Axeyum needed a reusable propagation result,
not a benchmark-specific list of selector units or an unproved scheduling heuristic.

## Decision

Add deterministic precedence propagation over the typed job-shop problem. Start with every
job-chain edge, compute a stable topological order and exact longest-path earliest/latest
windows, then inspect every same-machine pair in semantic order. If one non-overlap direction
cannot fit those windows, add the opposite edge because it is necessary in every schedule.
Repeat until no edge is added. A cycle, empty window, or pair with neither feasible direction
returns `infeasible` rather than continuing search.

Expose the windows, pair statuses, round count, and infeasibility result as
`JobShopPrecedencePropagation`. Add one-pass and fixpoint encoding routes. Both retain every
pair selector and its semantic identity; entailed selector units are additive constraints,
and SAT results still lift and replay through the independent schedule checker.

## Evidence

- Baseline, exact-window, one-pass, and closure encodings agree on satisfiability for bounds
  zero through five of the two-job/two-machine control; every SAT model lifts and replays.
- An explicitly forced pair has the documented selector polarity. A control in which neither
  order fits reports infeasible and its formula has a backward-checked DRAT refutation.
- Exhaustive enumeration of all 64 two-job/two-machine routing and duration patterns at bounds
  zero through eight gives 576 baseline/closure parity checks with replay for every SAT case.
- On `abz7@655`, propagation forces 256 selectors (128 in each direction). The result is
  stable after one productive round, so closure produces the same formula as one pass:
  175,170 variables and 1,690,226 clauses. At 656 it forces 254 selectors and produces
  175,770 variables and 1,697,028 clauses.
- A matched 180-second CaDiCaL run at 655 increased conflicts from 1,347,464 to 1,411,621 but
  reduced peak RSS from 453,772 KiB to 414,856 KiB and increased propagation throughput. It
  remained unknown; no lower bound is credited.
- A redundant per-time machine-capacity sequential-counter experiment was rejected after it
  expanded the formula to 2.27 million variables / 7.97 million clauses and raised a matched
  run to 2.12 GiB RSS. No such API was retained.

## Consequences

Consumers can ask Axeyum for a complete, sound preprocessing receipt and distinguish free,
forced-left, forced-right, and infeasible machine pairs without depending on CNF allocation.
The algorithm is classical detectable-precedence propagation and carries no novelty claim.
Its exhaustion on `abz7` is informative: the next lower-bound route needs stronger global
scheduling reasoning or proof-producing search, not repeated applications of the same local
window test.
