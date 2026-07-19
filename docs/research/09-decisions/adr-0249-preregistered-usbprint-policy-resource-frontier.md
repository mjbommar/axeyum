# ADR-0249: Preregister the usbprint policy-resource frontier

Status: accepted
Date: 2026-07-19

Result state: executed; rejected at the protocol gate

## Context

ADR-0244's complete-usbprint cell is a retained resource failure, not a finding
or solver disagreement. AnyModel completed 18 of 21 reachable functions with
zero high-confidence rows and 16,537 solves per authority/repetition. All four
minimum-policy processes hit the fixed 300-second in-process deadline, so the
campaign correctly stopped before maximum and both site-hash policies.

ADR-0245 moved usbprint out of the all-policy sweep rather than raising an
observed deadline. ADR-0247 subsequently accepted all five scalar policies on
the positive and tcpip strata, and ADR-0248 found no independent primitive in
their complete source-backed difference. Usbprint therefore remains only a
policy-resource frontier. It cannot reopen the coverage or symbolic-memory
lane.

## Decision

Preregister a point-major frontier at deterministic reachable-function prefixes
5, 10, and 15. At each point run the five accepted scalar policies in their
standing order. Every cell uses two order-balanced sole-authority repetitions,
the existing 250 ms per-check limit, a 300,000-solve/300-second per-function
ceiling, an 1,800-second in-process safety deadline, and a 1,920-second process
timeout.

The 5/10/15 points are fixed arithmetic prefixes below the known AnyModel
complete boundary of 18; 15 also matches the established tcpip fixed-function
boundary. They were selected before observing a new usbprint cell.

Run from final corrected Glaurung `7f682e5` with the exact v3 Z3/Axeyum
authority binaries. The runner stops at the first non-complete cell. An exact
four-run in-process deadline outcome is a resource-bound observation; every
other process, parser, identity, work, policy, coverage, partition, or report
failure is a protocol failure. Point-major order ensures that a stop at 15 can
still establish a common prefix of 10 across all policies.

The machine-readable protocol is
`corpus/glaurung-finding-populations/usbprint-policy-frontier-v1.json`.
The runner and analyzer refuse source/hash/work drift and output overwrite.

## Acceptance

A complete cell must have exact fixed-work-limit coverage, stable repeated
high-confidence output, exact authority parity, zero high-confidence rows,
correct policy telemetry, and complete solve/time/RSS counters. Raw diagnostics
remain descriptive.

The aggregate accepts either:

1. all 15 cells complete, establishing a common prefix of 15; or
2. all five policies complete at one or more lower points followed by an exact
   resource-bound stop, establishing the largest complete common prefix and an
   upper resource bracket.

No complete common prefix, a protocol failure, or identity/hash/work drift
rejects the result.

## Consequences

This closes the explicitly deferred bounded usbprint protocol without changing
the failed complete-driver experiment. It measures policy integration cost and
coverage under deterministic function prefixes, not solver speed, real-driver
recall, or complete-driver equivalence.

The prior AnyModel-complete/minimum-deadline reports remain historical anchors
at Glaurung `b79f269`; they are not cells in the new `7f682e5` matrix. No
usbprint frontier result can by itself admit symbolic memory, multi-successor
policies, or a different scalar default.

## Result

The exact clean-detached Axeyum
`f951152517a6bdcf0410d88c48c2cc3a167cac6a` execution against clean
Glaurung `7f682e5` ran all 15 point-major cells. Fourteen cells completed, all
five policies established a common prefix of 10, and four policies completed
prefix 15. The final prefix-15/site-hash-one cell rejected because the two
Axeyum repetitions did not reproduce canonical-model work exactly:

- repetition 1: 522,032 solves, 7,951 attempts, 7,825 completed choices,
  126 infeasible choices, and 516,576 probes;
- repetition 2: 522,296 solves, 7,955 attempts, 7,829 completed choices,
  126 infeasible choices, and 516,840 probes.

Both Axeyum repetitions and both Z3 repetitions still emitted the same 91 raw
diagnostic findings and zero high-confidence findings. The Z3 repetitions were
work-stable at 541,685 solves, 8,257 attempts, 8,120 completed choices, 137
infeasible choices, and 536,057 probes. This is therefore neither a finding
disagreement nor the preregistered four-run resource-bound outcome. The
aggregate correctly reports `accepted=false`, `matrix_complete=false`, common
completed prefix 10, no resource bound, and a protocol failure. The rejected
result is preserved under
`bench-results/glaurung-concretization-policy-sweep-20260718/usbprint-policy-resource-frontier-v1/`.

## Post-result diagnosis

The preregistered Glaurung revision reported the outer analyzed-function count
but did not partition inner symbolic-worklist termination. A post-result-only
instrumentation candidate on isolated Glaurung branch
`axeyum-concretization-policy-a0` at `ff3c0a7` added explicit completed,
state-budget, solve-budget, timeout-budget, and wall-deadline stop counts. An
otherwise identical diagnostic Axeyum run reported:

```text
[canonical-model-choice] policy=glaurung-site-hash-1-v1 attempts=7957 completed=7831 infeasible=126 probes=516972 inconclusive=0 error=0 unsupported_width=0 no_solver=0 unknown=0 final_unsat=0
[exploration-limits] runs=40 completed=36 state_budget=3 solve_budget=0 timeout_budget=0 deadline=1
[solver] backend=axeyum solves=522428 solver_time=903801.9ms avg=1730.0us check_timeout_ms=250
```

The unchanged 91/0 raw/high output plus one deadline-terminated inner worklist
explains the repeated-work drift. Each additional completed canonical attempt
accounts for 66 probes/solves, matching the observed increments. This
diagnostic attributes the rejection; it does not rehabilitate the cell or enter
the preregistered aggregate.

Future fixed-work evidence must record this stop partition and reject any
deadline- or timeout-terminated worklist. An outer analyzed-function count is
not sufficient evidence that the inner work boundary reproduced. Do not rerun
ADR-0249 with adapted bounds and call it the same experiment. The result makes
no solver-speed, recall, symbolic-memory, or default-policy claim.
