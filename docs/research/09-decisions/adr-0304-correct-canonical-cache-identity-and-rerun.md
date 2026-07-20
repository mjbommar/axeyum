# ADR-0304: Correct canonical cache identity and rerun the factorial

Status: accepted
Date: 2026-07-20

Result state: successor accepted; mixed per-driver additivity, warm cache-on
regresses every variance-qualified driver; ADR-0303 timing campaign rejected

## Context

ADR-0303 defined one exact engine-cache key as the sorted, duplicate-elided set
of assertion identities. Its implementation follows that rule. The earlier
read-only opportunity analyzer did not: it keyed exact hits by the ordered
textual query SHA-256, while using the canonical assertion set only for SAT-
superset and UNSAT-subset lookup.

The discrepancy was not hidden. The first cold pilot exposed and corrected an
unrelated owner-lifecycle defect before publishing any report. The corrected
campaign then completed all 120 processes and every producer report passed its
verdict, model replay, synchronization, terminal-state, capacity, and telemetry
gates. The frozen analyzer nevertheless rejected immediately at the independent
classification gate:

```text
cold-exact: cache classification differs without eviction/bypass
```

There were zero evictions, oversize bypasses, and SAT replay failures. Therefore
ADR-0303 gate 3 required exact agreement and disqualified all raw timing. The
campaign SHA-256 is
`d0b44696c263834892b3f70f69eac60b540ccc993e11f0c48b11abf998a310cb`;
the [rejection summary](../../../bench-results/glaurung-engine-cache-factorial-20260720/rejected-campaign.json)
retains no ratio, interval, or driver conclusion.

## Decision

Add an explicit compatibility mode to the opportunity analyzer:

- `textual-query` remains the default and reproduces the v1 artifact's identity;
- `canonical-constraint-set` implements the already-preregistered cache identity
  and emits the v2 schema.

Preregister one fresh 120-process successor campaign against the corrected v2
opportunity artifact. Change nothing else: retain Glaurung `202786c`, Axeyum
`da24b016`, replay executable `5e230ba7...65d92e1`, all 20 traces, the six
mode order, five repetitions, cache capacities, model replay, environment,
CPU 2, 4 GiB cgroup, runner/analyzer, 10,000-sample bootstrap, 3% CV limit,
and every ADR-0303 correctness and acceptance rule.

Do not reuse, merge, warm-start from, or report timing from the rejected
campaign. The successor uses fresh empty processes and a fresh empty output
directory. Its exact versioned registration is
[`bench-results/glaurung-engine-cache-factorial-v2-20260720/registration.json`](../../../bench-results/glaurung-engine-cache-factorial-v2-20260720/registration.json).

## Corrected read-only opportunity

The v2 result is bound at SHA-256
`23d32e734cb38da9338ffae2215a4fef7198ec03d91ebf70c39a21d9f087ac85`.
Per four-driver process:

| Driver | Checks | Canonical exact | Implication only | Structural total | Misses |
|---|---:|---:|---:|---:|---:|
| DptfDevGen | 603 | 255 | 24 | 279 | 324 |
| vwififlt | 5,182 | 2,609 | 392 | 3,001 | 2,181 |
| IntcSST | 2,309 | 1,196 | 57 | 1,253 | 1,056 |
| SurfacePen | 4,808 | 3,941 | 89 | 4,030 | 778 |
| **Total** | **12,902** | **8,001 (62.01%)** | **562 (4.36%)** | **8,563 (66.37%)** | **4,339** |

The structural total is identical to v1. Exactly 2,133 occurrences move from
implication to exact; no verdict or addressable/not-addressable boundary changes.
All five repetitions are classification-stable within every driver. This is
still opportunity, not performance evidence.

## Acceptance

The unchanged ADR-0303 analyzer must pass without modification. In particular,
when bounds do not bind, each exact and structural class must equal this v2
artifact. If it rejects, the successor is closed negative and no timing ratio
is reported. If it passes, only then may its per-driver contrasts and variance-
qualified additivity labels be reported.

## Accepted successor result

The fresh successor completed 120/120 processes and 387,060 checks. Every
producer report and the unchanged frozen analyzer passed. There were zero
wrong verdicts, unknowns, errors, SAT replay failures, evictions, oversize
bypasses, resource failures, or terminal owner leaks. The campaign is bound at
SHA-256
`3ea7216cd9cbb10623605f3fb4573eed15ec2550e1cb39df8e78a351197893b2`;
the committed [analysis](../../../bench-results/glaurung-engine-cache-factorial-v2-20260720/analysis.json)
is bound at
`4e4a2b64379de8ad2875f65dffdf7400a56853337e259ea917594f06ef156fc7`.

Warm solver state remains additive under exact caching on vwififlt (1.655,
95% CI [1.624, 1.687]) and SurfacePen (1.112, [1.101, 1.124]). DptfDevGen and
IntcSST have point estimates above one but fail the preregistered variance gate.
Under structural caching, warm state is additive on vwififlt (1.506, [1.480,
1.533]), IntcSST (1.213, [1.186, 1.242]), and SurfacePen (1.074, [1.064,
1.085]); DptfDevGen again fails the variance gate. This is a mixed bounded
answer, not universal additivity.

The second interaction is negative for cache promotion: among the three
drivers whose warm contrasts meet the variance gate, cache-off beats both
exact and structural cache-on. Warm-off/cache-on ratios are 0.405/0.405 on
vwififlt, 0.670/0.677 on IntcSST, and 0.262/0.261 on SurfacePen, with every
interval wholly below one. DptfDevGen is inconclusive on variance. Cache-on
raises mean maximum RSS by 7.6%--67.3%, depending on driver and mode.

The cache improves cold execution on every variance-qualified cache contrast,
but the existing warm solver is the measured product choice for these fixed
streams. Structural implication contributes only 562 additional hits after
canonical exact caching already handles 8,001 of 12,902 checks. Therefore the
Glaurung experiment remains an experiment; it is not promoted into Axeyum core.

## Consequences

The fail-closed classification gate worked: a superficially clean 120-process
run did not become a paper number because its independent oracle implemented a
different identity. The correction is narrower than a policy change and was
fixed before fresh timing. ADR-0303 remains rejected evidence. ADR-0304 closes
PLAN item 9 with a bounded mixed result: warm state is sometimes independently
additive, while the cache is not beneficial around the already-warm path on any
conclusive driver. No pooled performance statement follows.
