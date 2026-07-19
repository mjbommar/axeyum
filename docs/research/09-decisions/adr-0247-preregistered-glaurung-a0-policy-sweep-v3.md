# ADR-0247: Preregister corrected Glaurung A0 policy sweep v3

Status: accepted
Date: 2026-07-18

Result state: accepted; all five policies and both strata complete

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

## Result

The exact clean-detached Axeyum `f2af8b40` run against clean Glaurung
`7f682e5` completes the full matrix and the aggregate analyzer accepts every
gate. All five policies return all 14 source-backed findings with precision and
recall 1.0, zero false negatives, zero unexpected high-confidence rows, stable
repetitions, and exact sole-authority parity.

The complete positive-control raw/work populations per authority and
repetition are:

| Policy | Raw rows | Validated high rows | Solves |
|---|---:|---:|---:|
| AnyModel | 122 | 14/14 | 2,312 |
| minimum | 81 | 14/14 | 59,800 |
| maximum | 68 | 14/14 | 60,456 |
| site-hash-zero | 77 | 14/14 | 59,791 |
| site-hash-one | 72 | 14/14 | 60,465 |

Tcpip has zero producer-high rows in every cell and remains unlabeled discovery
output. AnyModel preserves its expected backend-dependent raw population (128
Z3 / 126 Axeyum). Every deterministic policy has exact authority parity:
minimum 110, maximum 84, site-hash-zero 95, and site-hash-one 98. Their solve
counts are respectively 80,563, 34,659, 28,258, and 79,950 per authority and
repetition, versus AnyModel's 3,079 Z3 / 2,991 Axeyum. These are policy and
integration costs, not a solver-speed comparison.

The cost frontier is material. On tcpip, site-hash-one takes about 68 seconds
and 147 MiB peak under Z3 versus 264 seconds and 235 MiB under Axeyum; minimum
takes about 68/150 MiB versus 160/186 MiB. Site-hash-zero is substantially
cheaper at about 21/139 MiB versus 19/140 MiB. No direction is promoted to a
performance headline because these cells exercise policy probing inside the
consumer and tcpip findings are unvalidated diagnostics.

Artifact identities:

- preregistration:
  `6cf0f41c8fd0f0024c8189ae59812943f8c119738bd8f8b26a087d2abec56300`;
- execution manifest:
  `8a2caae84e0cdf8fe0703e9fc7eea8b9220756e165ee74b48faed5c74e71e3e0`;
- accepted analysis:
  `6de0c7592f00d90711f4a4b7dbb5a381bfe663c914094aa55c069c355dfdcb99`.

## Consequences

V3 reran AnyModel, minimum, and maximum despite valid partial evidence because
cross-policy conclusions require one clean corrected source identity. It also
observed both site-hash policies for the first time under the source-backed
precision gate.

BoundarySet and DiverseEnum remain configurations of the A0 mechanism that need
bounded multi-successor explorer support before they are executable. Symbolic
memory remains the one architectural item, but v3 does not supply its gate: the
only labeled population is invariant at 14/14, while all policy-varying tcpip
rows are diagnostics without ground truth. Keep symbolic memory deferred.
Before broadening exploration, independently label a bounded sample of
policy-varying real-driver output or add a real source-backed population capable
of measuring a residual coverage gap. Track usbprint's resource frontier
separately.

## Alternatives

- Append site-hash cells to v2: rejected because v2 used the defective detector.
- Reuse the post-repair maximum control as the v3 maximum cell: rejected because
  the campaign requires one committed Axeyum source identity and complete
  analyzer state.
- Restore complete usbprint to the matrix: rejected because its fixed resource
  boundary already failed under minimum.
- Start symbolic memory now: rejected because no validated residual gap has
  survived the scalar-policy sweep.
