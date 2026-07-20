# Corrected canonical-identity factorial result

This is ADR-0304's successor to the rejected ADR-0303 campaign. It changes
exactly one scientific input: the opportunity artifact implements ADR-0303's
already-written exact identity, the sorted duplicate-elided set of assertion
identities. The producer, executable, 20 traces, six modes, cache bounds,
environment, cgroup, CPU, process order, runner, analyzer, statistical method,
and acceptance thresholds are unchanged.

The rejected predecessor remains immutable and contributes no ratios or driver
conclusions. This registration started with zero timing rows and binds both
that rejection and the corrected read-only opportunity artifact. It was
committed and pushed before execution.

The fresh successor completed all 120 processes and 387,060 check executions.
Every producer and analyzer correctness/work gate passed: no wrong verdict,
unknown, error, SAT-model replay failure, resource failure, eviction, oversize
bypass, or terminal owner leak occurred. The campaign SHA-256 is
`3ea7216cd9cbb10623605f3fb4573eed15ec2550e1cb39df8e78a351197893b2`.
The committed [analysis](analysis.json) has SHA-256
`4e4a2b64379de8ad2875f65dffdf7400a56853337e259ea917594f06ef156fc7`.

## Result

Ratios are paired per-check geometric means after collapsing five repetitions;
values greater than one favor the denominator. Intervals are deterministic
10,000-sample bootstrap 95% intervals. `Inconclusive` means at least one
process-geomean CV exceeded the preregistered 3% limit, even when the interval
does not cross one.

| Driver | Cold exact / warm exact | Exact additivity | Cold structural / warm structural | Structural additivity |
|---|---:|---|---:|---|
| DptfDevGen | 1.463 [1.375, 1.557] | inconclusive variance | 1.488 [1.399, 1.583] | inconclusive variance |
| vwififlt | 1.655 [1.624, 1.687] | warm faster | 1.506 [1.480, 1.533] | warm faster |
| IntcSST | 1.219 [1.190, 1.250] | inconclusive variance | 1.213 [1.186, 1.242] | warm faster |
| SurfacePen | 1.112 [1.101, 1.124] | warm faster | 1.074 [1.064, 1.085] | warm faster |

Warm solver state is therefore additive under exact caching on 2/4 drivers and
under structural caching on 3/4. The experiment does not establish universal
additivity.

The cache is not an independent win for the already-warm configuration. On
each variance-qualified driver, warm cache-off is faster than warm exact and
warm structural cache-on:

| Driver | Warm off / warm exact | Warm off / warm structural | Result |
|---|---:|---:|---|
| DptfDevGen | 0.744 [0.706, 0.786] | 0.803 [0.753, 0.858] | inconclusive variance |
| vwififlt | 0.405 [0.394, 0.416] | 0.405 [0.394, 0.416] | cache-on slower |
| IntcSST | 0.670 [0.650, 0.690] | 0.677 [0.657, 0.697] | cache-on slower |
| SurfacePen | 0.262 [0.252, 0.272] | 0.261 [0.251, 0.270] | cache-on slower |

The cache helps the cold configuration on every variance-qualified contrast,
but retained-state overhead raises mean maximum RSS by 7.6%--67.3% depending on
driver and mode. Structural implication adds only 562 hits beyond 8,001
canonical exact hits per four-driver pass; its warm result is not distinguished
from exact on vwififlt, 1.1% faster on IntcSST, 0.4% slower on SurfacePen, and
inconclusive on DptfDevGen.

## Scope

This is fixed-stream Axeyum evidence on four real Glaurung drivers. It supports
keeping warm solver reuse as the default integration mechanism and treating an
engine-level cache as a workload-specific cold-solver option, not promoting the
experimental cache into Axeyum core. It is not a pooled speed headline and does
not generalize to live exploration, other backends, other cache bounds, or
different query streams.
