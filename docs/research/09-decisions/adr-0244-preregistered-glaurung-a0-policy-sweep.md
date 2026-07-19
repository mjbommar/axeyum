# ADR-0244: Preregister the corrected Glaurung A0 policy sweep

Status: proposed
Date: 2026-07-18

Result state: protocol preregistered; results pending

## Context

ADR-0243 supplies a nonzero source-backed positive control after ADR-0240 and
ADR-0242 invalidated tcpip and usbprint as recall denominators. The remaining
publication question is not whether one solver returns the same SAT/UNSAT
verdict on an isolated query. Model choice changes concretization, which can
change successor states, later queries, and emitted findings. That effect must
be measured under sole solver authority.

Glaurung branch `axeyum-concretization-policy-a0` at
`b79f26959378f9b8ea51eee6f1b3809a4a234c84` exposes one policy surface at both
concretization seams. Five scalar settings are executable: the AnyModel default,
unsigned minimum, unsigned maximum, and two complementary site-hash extremum
schedules. `BoundarySet` and `DiverseEnum` are conceptually settings of the same
surface, but they are not executable at this revision because a set-valued
choice requires bounded successor forking. Collapsing a set to one value would
not measure either policy.

The reviewer feedback requires finding parity, not just verdict parity, while
the corrected evidence requires a strict distinction between raw producer
diagnostics, producer-high rows, and independently validated findings.

## Decision

Preregister `glaurung-a0-five-policy-sweep-v1` before observing any new cell.
The committed machine-readable protocol fixes:

- the five executable policies and their order;
- corrected Glaurung revision `b79f269`;
- the exact Z3- and Axeyum-authoritative binary hashes;
- all 11 driver hashes in three strata;
- two order-balanced repetitions and every deadline, solve, process, function,
  and per-check bound for each stratum; and
- the acceptance gates and claim limits.

The strata are:

1. the nine-driver, 14-row source-backed positive control, which every policy
   must preserve exactly with no unexpected high-confidence row;
2. the fixed-first-15-functions tcpip population, reported as unlabeled
   discovery output; and
3. the complete usbprint population, also reported as unlabeled discovery
   output.

Use `GLAURUNG_CONCRETIZATION_POLICY` for every nondefault cell. Keep AnyModel an
unset/default control so its compatibility route is measured rather than
aliased to a new selector. The harness must scrub both preferred and legacy
policy variables before constructing each child environment.

Run from one clean detached Axeyum commit containing the unchanged registration,
runner, harness, validator, and analyzer. Fail closed on source, binary, driver,
manifest, environment, order, coverage, repetition, policy, telemetry, work,
partition, hash, or post-run identity drift. Preserve partial artifacts after a
failed command; never overwrite or adapt the remaining campaign in response to
an outcome.

The analyzer accepts only exact high-confidence authority parity. It also
requires each repeated raw/high/diagnostic population to be stable and each
confidence partition to be an exact disjoint union. For the positive stratum,
the independently validated join must remain 14/14 with zero false negatives
and zero unexpected high rows for every policy. No direction or size of
real-driver policy variation is a gate.

## Pre-run evidence

The registration resolves hash-exactly against IOCTLance revision
`905629a773f191108273a55924accd9f31145a8d`: all nine positive binaries match the
ADR-0243 manifest. The tcpip and usbprint inputs match their preregistered
SHA-256 identities. Both authority binaries match the corrected `b79f269`
builds.

The focused unit suite covers preferred-versus-legacy policy selection,
environment scrubbing, exact command construction, default AnyModel selection,
output overwrite refusal, manifest/discovery input joins, missing policy cells,
source and binary drift, work/coverage drift, positive misses, report-hash
drift, confidence-partition corruption, population-hash corruption, and missing
cost telemetry. The pre-run checkpoint has 39 passing tests across the runner,
analyzer, authority harness, and source-backed validator.

No sweep result has been observed at this decision point. Update this ADR only
after the exact committed protocol either completes or fails closed.

## Consequences

The campaign tests a configurable mechanism rather than presenting five model
selection algorithms as separate contributions. Results can establish bounded
policy-dependent finding behavior and authority parity. They cannot establish
representative real-world recall, exploration equivalence, solver speed, or
exhaustive model coverage.

`BoundarySet`/`DiverseEnum` may extend this same experiment only after bounded
multi-successor execution exists and receives a separate preregistered cell.
They do not block the executable scalar sweep. Symbolic or symcrete memory is
memory-model work and begins only if independently validated evidence leaves a
coverage gap after the cheap policy experiment.

The live dirty Glaurung checkout remains untouched. Measurement uses the clean
isolated branch. Integration of `b79f269` into the active Glaurung development
line still requires coordination with its owner and is distinct from accepting
this evidence protocol.

## Alternatives

- Add a fake BoundarySet cell that chooses one boundary: rejected because it
  would relabel scalar selection as set-valued exploration.
- Gate on raw findings being at least AnyModel: rejected because ADR-0240 and
  ADR-0242 show raw and producer-high rows can be stable false diagnostics.
- Use tcpip or usbprint as recall ground truth: rejected because both corrected
  populations are unlabeled/zero-positive.
- Tune the policy set or work bounds after viewing partial output: rejected as
  outcome-adaptive measurement.
- Start symbolic-memory implementation before this run: rejected because the
  cheaper policy surface has not yet been measured against the validated gate.
