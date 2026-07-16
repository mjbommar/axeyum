# ADR-0204: Source-identity direct sibling prefixes

Status: accepted
Date: 2026-07-16

## Context

ADR-0203 keeps Glaurung's first-class direct-delta route opt-in because its
sound exclusive-owner topology loses time or RSS against serial snapshot reuse.
The original attempt to combine direct deltas with serial siblings produced
497/2,551 wrong verdicts: a retained assertion depth cannot distinguish two
equal-depth siblings with opposite final roots. Numeric `ExprId` values also
cannot be treated as global source identity because Glaurung clones expression
pools and lets them grow independently.

The missing topology must retain one exclusive mutable Axeyum session, avoid
whole-snapshot translation, and prove the exact common source prefix without a
probabilistic hash.

## Decision

Accept Glaurung ADR-013/`aee3418` as the opt-in source-identity contract for the
next GQ7 candidate.

Each persistent source assertion append creates an immutable ancestry node
whose parent is the exact previous prefix. Forks clone only an `Arc` to that
node; divergent appends allocate distinct nodes even if their cloned pools use
the same numeric expression handle. The direct adapter retains its current
ancestry, computes the exact common ancestor by pointer identity, pops the one
mutable solver to that depth, and translates only the target suffix. Confirmed
depth remains telemetry and admission input, never identity.

The solver stays worker-local and serially leased. No AIG/CNF/SAT state is
cloned or concurrently shared. Prefix-depth inconsistency and operational
errors fail closed. The feature remains behind Glaurung's explicit direct-delta
switch until repeated production gates accept it.

## Evidence

The adapter RED/GREEN test materializes siblings ending in `x=5` and `x=7`,
then deliberately submits the right sibling with stale retain depth two. The
source chain finds their one-root ancestor, pops once, adds the right root, and
returns `x=7`. A separate explorer test proves that equal numeric expression
IDs in cloned pools do not alias divergent source nodes.

The Glaurung Axeyum-backend group passes 42/42 and explorer group 12/12 under a
4 GiB serialized build. The direct adapter and stale-sibling regression both
pass with combined Z3+Axeyum features. Targeted Clippy confirms the refactor
adds no argument-count violation; the broader repository retains unrelated
pre-existing lint debt.

## Alternatives

- Retained depth: rejected by the measured wrong-verdict failure.
- Numeric expression IDs: rejected because independently growing cloned pools
  can alias.
- Structural hashes: rejected because collision handling would enter the
  soundness boundary and still require full-source work.
- Clone mutable solver state: rejected by Axeyum's exclusive session contract
  and the production RSS objective.
- Rebuild LCP from complete translated snapshots: rejected because it restores
  the entry work direct deltas remove.

## Consequences

The GQ7 implementation prerequisite selected by ADR-0203 is complete, but its
production acceptance is not. Next extend the fail-closed lineage gate with an
explicit direct+serial policy, calibrate exact traffic on SurfacePen, and run
the repeated SurfacePen/NETwtw10 time, ratio, RSS, correctness, replay, finding,
and lifecycle comparisons. Serial snapshot remains the default meanwhile.
