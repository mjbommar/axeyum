# ADR-0247: Preregister corrected Glaurung A0 policy sweep v3

Status: accepted
Date: 2026-07-18

Result state: preregistered; no v3 cell observed

## Context

ADR-0244's v1 sweep correctly stopped when minimum unsigned could not complete
the complete-usbprint resource boundary. ADR-0245's two-stratum v2 sweep then
correctly stopped when maximum unsigned exposed the model-dependent stack-region
false positive repaired by ADR-0246. AnyModel and minimum have accepted partial
cells, and maximum has a separate accepted post-repair positive control, but no
single corrected-source campaign has observed all five policies.

The research question is still a policy sweep, not five algorithms and not a
symbolic-memory project.

## Decision

Preregister `glaurung-a0-five-policy-sweep-v3` in
`corpus/glaurung-finding-populations/concretization-sweep-v3.json` before
observing any v3 cell. Run all five scalar policies in the fixed order AnyModel,
minimum unsigned, maximum unsigned, site-hash-zero, and site-hash-one over:

1. the complete nine-driver source-backed positive population, with exact
   14/14 validation and no unexpected high-confidence row; and
2. the fixed first-15-function tcpip discovery boundary, with no preselected
   finding direction or magnitude.

Bind execution to clean Glaurung `7f682e5`, Z3 authority binary SHA-256
`027dad8802083021a278216ad471fc85f73c2a2aeeb228b08d6ebe6e9ea8031e`,
Axeyum authority binary SHA-256
`ee7ef0f84000080700129fe12d49f34396f6be8aeae4d36b35bdb2a4912ae6cd`,
the unchanged source manifest and driver hashes, N=2 order balancing, and every
work/check/process bound copied from v2. Run from one clean detached Axeyum
commit containing the registration, runner, analyzer, validator, rejected v1/v2
artifacts, and ADR-0246 correction evidence.

Complete usbprint remains outside this matrix as the separately documented
policy-resource frontier. Do not raise its observed deadline, count it as a
zero-finding cell, or infer validated coverage from it.

## Acceptance

The existing fail-closed runner and analyzer must reject any source, binary,
driver, policy, environment, work, order, coverage, partition, cost, stability,
or report-hash drift. Every positive-control cell must retain the exact validated
set. Every authority pair must have stable exact high-confidence parity.

Tcpip output remains unlabeled discovery evidence. Preserve raw,
high-confidence, diagnostic, solve-count, policy-telemetry, time, and RSS
partitions, but do not turn their direction into an acceptance criterion.

## Consequences

V3 reruns AnyModel, minimum, and maximum despite valid partial evidence because
cross-policy conclusions require one clean corrected source identity. It also
observes both site-hash policies for the first time under the source-backed
precision gate.

BoundarySet and DiverseEnum remain configurations of the A0 mechanism that need
bounded multi-successor explorer support before they are executable. Symbolic
memory remains the one architectural item and starts only if this cheap sweep
leaves independently validated coverage headroom.

## Alternatives

- Append site-hash cells to v2: rejected because v2 used the defective detector.
- Reuse the post-repair maximum control as the v3 maximum cell: rejected because
  the campaign requires one committed Axeyum source identity and complete
  analyzer state.
- Restore complete usbprint to the matrix: rejected because its fixed resource
  boundary already failed under minimum.
- Start symbolic memory now: rejected because no validated residual gap has
  survived the scalar-policy sweep.
