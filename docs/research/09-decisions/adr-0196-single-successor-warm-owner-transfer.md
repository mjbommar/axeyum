# ADR-0196: Single-successor warm-owner transfer

Status: accepted
Date: 2026-07-16

## Context

ADR-0195 removes empty warm-theory projection work and exposes construction as
the accepted-current residual. On the post-change 2,551-check SurfacePen v6
profile, 358 path-creation checks are only 14.0% of checks but consume 82.2% of
CNF time, 89.0% of bit-blast time, 88.0% of added clauses, and 89.7% of root
encodings. Each newly owned path currently materializes its complete assertion
prefix into a fresh `IncrementalBvSolver`.

Glaurung's symbolic branch implementation terminates the parent after creating
two children. Nevertheless both children receive fresh warm-owner IDs and the
parent's retained solver is closed. That discards an exact prefix state even
though one child can become its unique successor. Reusing it for both siblings
would be unsound mutable-state sharing; transferring it to exactly one child is
an ownership move, not sharing.

## Decision

At a symbolic two-way fork, let exactly the last-pushed successor inherit the
parent's warm-owner ID. Glaurung's DFS worklist executes that successor next.
Give every other successor a fresh ID exactly as before. Swap an unused fresh
ID into the terminal parent so ordinary parent cleanup does not close the
transferred solver. The inheriting child adds its branch assertion on its next
feasibility check; the sibling materializes an independent solver and cannot
observe the inherited solver's scopes, clauses, learned state, cache, model,
or replay memo.

If the inheriting child is UNSAT, errors, or otherwise terminates, its ordinary
terminal cleanup closes the transferred owner. If feasibility is skipped for
an independent branch, the child still uniquely owns the unchanged parent
prefix and adds its branch assertion at its first later check. Stateful restart
continues to close the current owner and mint a fresh one.

This is downstream scheduling over Axeyum's existing per-solver ownership
boundary. It adds no shared global solver, cloneable SAT state, verdict reuse,
proof shortcut, or change to Axeyum's public API.

The policy is on by default in Glaurung. Setting
`GLAURUNG_AXEYUM_WARM_OWNER_TRANSFER` to `off`, `false`, or `0` restores the
fresh-owner control. Invalid values fail closed to off, and non-Axeyum builds
retain fresh owners for both children.

## Required evidence

Acceptance requires tests proving:

1. exactly one child inherits the parent's owner and its sibling does not;
2. ending the forked parent does not close the transferred owner;
3. an infeasible or terminal inheriting child closes it exactly once;
4. sibling constraints remain isolated and both SAT/UNSAT outcomes replay;
5. restarts still mint a new owner and no terminal session/cache survives;
6. ordered trace identity and findings remain unchanged.

The real gate must show fewer created sessions and less path-birth root/AIG/CNF
work on the v6 SurfacePen profile, then pass the clean adaptive/cache-on
two-driver gate with 100% agreement, zero replay failures, exact findings,
valid warm/cache partitions, bounded 9/512 ownership, and the existing 3% time,
3% ratio, 5% RSS, and 2% absolute-Z3 alarms. A correctness-only or path-count-
only change is insufficient.

## Alternatives

Cloning `IncrementalBvSolver` was rejected because duplicating mutable SAT and
cache state would require a new explicit snapshot/proof/invalidation contract
and could multiply memory. Sharing one solver between siblings was rejected
because scopes and learned state would cross logical owners. A global prefix-
CNF cache remains a separate GQ8 design requiring stable lift-map and replay
provenance. The single-successor move uses ordinary exclusive ownership and
therefore has the smallest trust surface.

## Consequences

The first implementation transferred ownership to the earlier child. It
reduced construction in an isolated lineage profile, but the owner then sat
dormant behind the sibling subtree. That increased adaptive pressure, exceeded
SurfacePen's RSS alarm, and regressed NETwtw10 Axeyum time by about 9.4%. It was
reverted before acceptance. This failure makes worklist order part of the
accepted policy rather than an incidental implementation detail.

The LIFO-aligned implementation passes the clean repeated adaptive/cache-on
two-driver gate against the committed ADR-0195 current baseline. Across
185,442 checks, every decision, finding, transfer counter, cache partition,
and terminal-cleanup invariant is exact, with zero replay failures.
SurfacePen mean Axeyum time falls 14.71% and its Axeyum/Z3 ratio falls 15.04%;
median RSS rises 0.76% and Z3 drifts 0.39%. NETwtw10 mean Axeyum time falls
34.77% and its ratio falls 34.36%; median RSS falls 0.36% and Z3 drifts -0.62%.
Every time, ratio, RSS, and environment alarm passes. The accepted artifact is
`lineage-adaptive-owner-transfer-v1.json`, SHA-256
`7478f60827e2cedbabb2bbe2c8ba07ae7d3b024f5676b61728c5dfc98a137de2`, in the
Glaurung capture directory.

The optimization deliberately benefits at most one successor per fork and
does not eliminate all path creation. New traversal policies or driver
families must revalidate the next-executed-successor assumption and the full
correctness, traffic, time, ratio, RSS, and Z3-drift gates. The explicit off
control remains part of the production contract.
