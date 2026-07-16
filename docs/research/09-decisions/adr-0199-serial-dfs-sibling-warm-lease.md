# ADR-0199: Serial DFS sibling warm lease

Status: accepted
Date: 2026-07-16

## Context

ADR-0196 transfers a terminal parent's retained solver to the
last-pushed/next-executed child. The earlier sibling remains fresh. ADR-0197
shows those fresh owners still consume 78.4% of warm bit blast and 70.7% of
warm CNF, while ADR-0198 rejects retaining a third solver because RSS rises
7.66%.

An immutable prefix artifact is not currently a cheap boundary. `TermArena`
and the AIG are cloneable, but `IncrementalCnf` owns an opaque mutable BatSat
instance. A useful fork artifact would need to copy lowering and encoder maps,
rebuild the SAT database clause by clause, preserve every lift/replay map, and
define invalidation for scopes, arrays/UF projections, cache entries, and
future encodings. That is a large API and memory commitment before evidence
that copying is cheaper than reconstruction.

Glaurung's worklist offers a narrower option. It is single-threaded and LIFO
within one exploration. Siblings are never checked concurrently. The existing
snapshot adapter already restores a complete assertion vector by popping to
its structural longest common prefix and adding only the divergent suffix;
selector-guarded inactive clauses and learned state remain sound under that
contract.

## Decision

Add a Glaurung serial-sibling policy with an explicit off control. At a symbolic
fork, both feasible children become continuations of the parent's warm owner,
but only the state popped from the DFS worklist may actively use it. A
reference-counted lease keeps the session alive while sibling continuations
remain queued. Parent, infeasible child, terminal child, state-budget cleanup,
solver-budget cleanup, deadline cleanup, and stateful restart each release
exactly one reference. The solver closes, and all cache gauges are subtracted,
only when the final reference is released.

The policy is serial reuse, not concurrent mutable sharing. It does not clone
SAT state, expose an Axeyum public snapshot, reuse a verdict without checking,
or permit one owner to execute on multiple threads. Every check still submits
the complete current assertion snapshot, runs the ordinary Axeyum check, lifts
the model, and replays every original root. Sibling transitions use the same
already-tested LCP/pop/push path as snapshot mode.

Add explicit telemetry for share events, tracked owner references, peak
references, and terminal zero gauges. Invalid environment values fail closed to
off. The policy is the adaptive downstream default after the gates below;
ADR-0196's exclusive-transfer policy remains the explicit control.

## Required evidence

Focused tests must prove:

1. both sibling continuations name the same logical owner only under the
   explicit serial policy;
2. parent and infeasible-child release cannot close a solver while a feasible
   sibling continuation remains;
3. nested forks close exactly once after their final continuation;
4. sibling divergence pops to the exact structural prefix and produces
   isolated SAT/UNSAT outcomes with original replay;
5. exact SAT-cache hits remain replay checked and all cache/session/reference
   gauges reach zero on every terminal/budget/deadline/restart route;
6. no state clone used solely for stateful carry releases an unregistered
   lease;
7. policy parsing is explicit and invalid values fail closed.

The first performance gate is the exact SurfacePen profile: created-owner root,
AIG, CNF, and time must fall without increasing total internal time or losing
any occurrence. The production gate is the repeated adaptive/cache-on
SurfacePen plus NETwtw10 artifact with exact decisions, findings, traffic,
replay, and lifecycle telemetry, and the existing 3% time, 3% ratio, 5% RSS,
and 2% Z3-drift alarms.

## Rejection conditions

Reject and remove the candidate if persistent cross-sibling arena/AIG/CNF
growth exceeds the memory alarm, if selector/LCP transitions require weakening
replay or cache ownership, if a cleanup route leaves a reference/session alive,
or if bookkeeping costs erase construction savings. Do not respond to failure
by enabling concurrent solver access or silently increasing the path cap.

## Acceptance evidence

Four focused serial tests and all 36 Axeyum-backend tests pass under the 4 GiB
wrapper. They cover fail-closed policy parsing, nested reference release,
single-owner fork identity, SAT-left/UNSAT-right/SAT-left structural LCP
transitions, model replay, and the existing backend semantics/proof suite. An
unset-environment release smoke selects the accepted policy and finishes with
43 created/closed sessions, peak one live session, 165 share events, peak 11
logical references, and zero session/cache/reference gauges.

The diagnostic SurfacePen profile demonstrates the intended mechanism against
ADR-0196's no-fallback lineage control: created sessions fall 79.2%, added AIG
nodes 88.0%, clauses 77.0%, bit-blast time 82.4%, CNF time 66.8%, and internal
total 15.2%. SAT rises 36.2% in the larger retained database and becomes 47.2%
of candidate time, so future warm and cold bottleneck rankings must remain
separate.

The clean repeated adaptive/cache-on artifact executes 185,442 checks with
identical decisions, findings, exact warm/cache/lease traffic, and zero replay
failures. SurfacePen mean Axeyum time and normalized ratio improve
17.08%/18.53%, median RSS falls 6.11%, and Z3 drifts +1.79%. NETwtw10 improves
0.72%/0.35%, median RSS falls 13.36%, and Z3 drifts -0.37%. Every alarm passes.
The accepted artifact is `lineage-adaptive-serial-sibling-v1.json`, SHA-256
`3218a1cd6ac4119647b3b4572b909bc3fd868077282cf0802dfede4f9161a362`, at
Glaurung commit `f17dc08`.

New traversal policies, parallel execution, or driver families must revalidate
the serial-execution premise and every lifecycle/resource alarm. Parallel path
exploration must use independent owners; it may not reuse this serial lease
across workers.
