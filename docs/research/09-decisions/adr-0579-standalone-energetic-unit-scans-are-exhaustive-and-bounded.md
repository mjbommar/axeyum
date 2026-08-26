# ADR-0579: Standalone energetic unit scans are exhaustive and bounded

Status: accepted
Date: 2026-08-26
Index-summary: Exhaust all machine intervals for strongest independently replayed start-bound units

## Context

ADR-0578 produced one checked conditional energetic clause from the strongest root interval, but
that single probe did not establish whether other standalone unit deductions existed. Selecting
promising intervals by utilization would leave an unmeasured gap: a weaker-looking interval may
support a stronger operation bound. Repeated formula cloning would also make bulk admission
needlessly expensive.

## Decision

Add an exhaustive standalone-unit scanner over every integer interval on every machine for a
selected checked domain derivation. For each flexible operation and both bound polarities, compute
the task's exact base contribution and test the extreme one-sided narrowing. When it overloads,
use monotone binary search to find the weakest conflicting assumption. Its semantic negation is
the strongest unit deduction supported by that interval. Retain only the strongest checked
artifact for each operation/polarity in stable order.

Count every interval, candidate bound, and exact task-energy evaluation. Refuse work beyond
explicit horizon, interval, task-check, or retained-artifact ceilings. A root overload is not
silently converted into a conditional unit; callers must use the root certificate route.

Add bulk clause admission to `JobShopEncoding`: clone the exact formula once, independently replay
every conflict in caller order, translate semantic assumptions through existing prefix variables,
and insert only non-tautological clauses. Expose deterministic JSON and strengthened-DIMACS output
through a dedicated example CLI.

## Evidence

At the feasible `ft06 = 55` boundary, the complete precedence-closure scan checks 9,240 intervals,
110,880 polarity candidates, and 277,248 task contributions. It finds exactly two strongest
standalone units. Both are replayed and inserted; the strengthened formula remains satisfiable,
and its lifted schedule independently replays at makespan 55.

At `abz7@655`, the scan checks all 3,222,600 intervals, 128,904,000 polarity candidates, and
322,261,348 task contributions in 7.49 seconds with 396,636 KiB peak RSS. Exactly two strongest
standalone units survive:

- job 2 operation 10 must start after 532, from machine 5 interval `[0,538)` at 539/538;
- job 7 operation 0 must start before 24, from machine 5 interval `[24,537)` at 514/513.

The exact precedence-closure formula grows from 1,690,226 to 1,690,228 clauses at unchanged
175,170 variables. A matched 30-second CaDiCaL seed-401 run remains unknown. Its last sample is
230,543 conflicts at 29.91 seconds, versus 255,432 at 28.79 seconds for the no-unit baseline; this
is not a speedup claim and does not prove infeasibility.

## Alternatives

- Scan only the strongest root interval: rejected because it cannot establish completeness of the
  standalone-unit layer.
- Linearly test every possible bound: rejected because monotonicity supports an exact bounded
  binary search without weakening the result.
- Retain every interval-specific duplicate: rejected because identical semantic units add no
  evidence and obscure the strongest conclusion.
- Treat fewer conflicts in a bounded SAT run as progress toward UNSAT: rejected because both runs
  are unknown and their trajectories are not comparable proofs.

## Consequences

The standalone energetic-unit layer is now complete for the selected precedence-closure domains,
and it yields only two deductions on `abz7@655`. More scans of the same kind cannot close the
lower bound. The next reusable capability must propagate already checked bounds through job and
machine precedences and produce contextual multi-assumption explanations, or compose conditional
leaves under a checked cover.

Energetic propagation, explanations, and lazy clause generation remain prior art. This decision
claims a bounded, replayable Axeyum assurance boundary and an exact negative/positive measurement,
not a novel scheduling algorithm or result.
