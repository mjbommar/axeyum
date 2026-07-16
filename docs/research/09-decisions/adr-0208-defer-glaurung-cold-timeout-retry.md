# ADR-0208: Defer Glaurung cold timeout retry

Status: deferred
Date: 2026-07-16

## Context

ADR-0207 isolates nine distinct post-fix tcpip formulas that cold Axeyum
decides correctly under a diagnostic cap, while the production 250 ms cap
times out on four. Glaurung needs to know whether rebuilding a fresh one-shot
solver after a synchronized retained-session timeout improves exploration
completeness cheaply enough to become policy.

## Decision

Retain Glaurung ADR-017/`35b25ab` only as an explicit diagnostic. The opt-in
`GLAURUNG_AXEYUM_WARM_TIMEOUT_COLD_RETRY=1` retries exactly one synchronized
direct-warm `Unknown` through a fresh Axeyum solver with the same 250 ms cap.
It never retries decided, unsynchronized, error, or existing one-shot fallback
checks. A retry decision is returned; retry `Unknown`/error preserves the
original `Unknown`. Process counters partition retries into recoveries,
repeated unknowns, and errors.

Do not enable it by default. The first tcpip gate fails the memory alarm and
does not recover enough decisions.

## Evidence

The tcpip candidate executes 71,909 queries with zero SAT/UNSAT disagreements,
warm resets, or retry errors. Its counter partition is exact: 15 retries = 4
recoveries + 11 repeated unknowns + 0 errors. Relative to the post-fix
single-process reference, Axeyum time rises 128,281.6→131,335.4 ms (+2.38%),
inside the 3% alarm, but RSS rises 447,888→494,728 KiB (+10.46%), failing the
5% alarm. Eleven Axeyum nondecisions remain, and query-count drift prevents a
causal performance comparison.

The dxgkrnl no-timeout control performs zero retries and preserves the exact
17,712-query structural traffic, zero Axeyum nondecisions/disagreements, and
nearly identical time/RSS (9,190.0→9,220.9 ms; 341,732→341,680 KiB). The
candidate is inert when retained solving decides.

The focused backend suite is 44/44 and the real footer satisfies the required
counter partition under the 4 GiB wrapper.

## Alternatives

- Admit on partial recovery: rejected because memory exceeds the production
  alarm and most timeouts remain.
- Increase every Axeyum timeout: rejected because it taxes every query and
  changes the common resource contract.
- Implicit Z3 fallback: rejected because it expands the dependency/policy
  boundary and cannot represent the pure-Rust deployment.
- Treat timeouts as agreement: rejected because `Unknown` is first-class.

## Consequences

The next timeout experiment should avoid whole-snapshot reconstruction: measure
a bounded second check on the already-synchronized retained solver (if the SAT
adapter preserves useful state), or admit retries only with a pre-solve
predictor that is validated against the exact nine-formula pack. Add profile
schema coverage before a profiled policy claim. Full-budget and repeated
tcpip/dxgkrnl DriverSpec admission remain pending.
