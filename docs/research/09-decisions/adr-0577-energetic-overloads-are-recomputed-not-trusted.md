# ADR-0577: Energetic overloads are recomputed, not trusted

Status: accepted
Date: 2026-08-26
Index-summary: Recompute cumulative compulsory energy and admit only strict overload certificates

## Context

The proof-producing `abz7@655` routes remain much slower than a current OptalCP reproduction:
four failure-directed workers raised the solver's internal lower bound to 656 in 59.877 seconds,
but exported no inference trace. Axeyum's existing scheduling propagation covered exact job-chain
windows and pairwise detectable precedences. It did not expose energetic reasoning, a classical
cumulative-resource inference that can detect contradictions involving more than one pair.

Trusting an external `proof: true` status or accepting producer-computed energy would violate the
project's evidence boundary. Conversely, embedding an optimizer-specific data structure would not
provide the small reusable checker needed by job shop, RCPSP, and future cumulative frontends.

## Decision

Add a typed cumulative task-window input and an exact checker for the classical energetic
inequality over a half-open integer interval. For every non-preemptive task the checker recomputes
the minimum processing time that must occur in the interval,

`max(0, min(duration, width, earliest_completion - start, end - latest_start))`,

multiplies it by demand, sums with checked arithmetic, and admits a conflict only when required
energy strictly exceeds `capacity * width`. Zero duration, demand, or capacity; reversed domains;
duplicate task identifiers; malformed intervals; and overflow fail closed.

The job-shop adapter reconstructs operation membership, unit demand, and domains from the typed
instance. A portable conflict names only the domain derivation, machine, interval, and redundant
expected totals. Replay supports either defining job-chain windows or ADR-0574's deterministic
precedence closure, recomputes both layers, and rejects a wrong schema, bound, machine, interval,
total, or non-strict inequality.

Expose deterministic exhaustive integer-interval scans behind explicit horizon, interval, and
task-check ceilings. The scan ranks intervals by exact cross-multiplied utilization, without
floating point, and can serialize only a conflict that the same checker accepts.

## Evidence

Focused controls cover a genuine two-task overload, a merely tight boundary, partial compulsory
energy, demands greater than one, serialization/replay, duplicate identifiers, resource decline,
and mutations of schema, machine, interval, and required energy. Twelve focused job-shop tests and
all-target/all-feature Clippy are green. The CLI produces and independently replays the tiny
conflict with verdict `unsat-energetic-checked`.

On exact `abz7@655`, exhaustive scans evaluate 3,222,600 machine intervals and 64,452,000 task
contributions in 0.75 seconds from job-chain domains. The strongest interval is machine 5,
`[0,538)`, with required/capacity energy 533/538. Repeating after all 256 detectable-precedence
consequences gives the same interval and ratio. Thus root energetic reasoning does not establish
the target lower bound and no conflict artifact is manufactured.

## Alternatives

- Trust OptalCP's internal optimum flag: rejected because no portable proof or operation values
  are exported.
- Add an unchecked energetic cut directly to CNF: rejected because search acceleration cannot
  enlarge the trusted base.
- Implement only a job-shop-specific overload loop: rejected because the semantic inequality is
  a cumulative-resource capability shared by other scheduling problems.
- Call a tight interval a contradiction: rejected; overload requires a strict inequality.

## Consequences

Axeyum now has a small independently replayable energetic-conflict boundary and an exhaustive
diagnostic scan. It does not yet reproduce failure-directed search: `abz7@655` requires conditional
conflicts under branch domains plus a checked cover or learned-clause composition. The negative
root measurement makes that next dependency explicit and prevents further time being spent on an
already exhausted shortcut. Energetic reasoning and its explanation literature are prior art; no
technique-novelty claim is made.
