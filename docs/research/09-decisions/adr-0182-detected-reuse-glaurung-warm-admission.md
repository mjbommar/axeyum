# ADR-0182: Detected-reuse Glaurung warm admission candidate

Status: accepted
Date: 2026-07-16

## Context

ADR-0181 closes GQ9's clean-baseline prerequisite. Fixed lineage is fast, but
it eagerly creates retained solver state for paths that may issue only one
query. Formula-size prediction would repeat GQ4's failed analysis-cost gamble;
Glaurung already has a cheaper causal signal: whether the same live,
explorer-owned path actually reaches a second solve.

## Decision

Accept Glaurung `GLAURUNG_AXEYUM_WARM_REUSE=auto` as an explicit measurement
candidate, while keeping the production default off.

The first check retains only its path ID and solves one-shot. A second check on
that same live path initializes the existing bounded 9/512 lineage session from
the current complete snapshot; later checks reuse deltas. Terminal/restarted
paths erase probe and solver state. Separate probe/activation counters preserve
exact accounting. Existing one-shot fallback, original-term model replay, path
ownership, and sibling isolation remain unchanged.

## Evidence

The TDD admission test fails before implementation and passes after it; all 24
Axeyum-backend tests pass. The dual-backend release client builds under 4 GiB,
and default Clippy completes with only established repository warnings.

Single-process real calibration keeps every finding, decides every check, and
has zero disagreements or unknown splits.

- SurfacePen: off is 1.995 seconds / 64,228 KiB; auto is 1.154 seconds /
  65,136 KiB with 358 probes and 191 activations; lineage is 1.062 seconds /
  82,480 KiB.
- Fixed-budget NETwtw10 auto partitions all 28,356 checks into 17,669 warm
  checks plus 10,687 probes, activates 4,099 paths, and measures 19.595 seconds
  / 216,016 KiB. Clean lineage is 18.751 seconds / 257,632 KiB.

Thus auto sacrifices about 4.5--8.7% Axeyum time versus eager lineage while
reducing RSS 16--21%, and preserves much of the cold-to-warm gain. Glaurung
`4ae5469` commits the opt-in candidate and telemetry.

## Alternatives

Eager retention cannot distinguish singleton paths. Formula-size thresholds do
not measure reuse. Sharing mutable state across siblings violates the accepted
ownership/replay contract. Making auto the default from one run was rejected;
the clean gate requires repeated exact-work evidence.

## Consequences

Extend the versioned lineage runner with auto-policy identity, its exact
probe/warm/fallback partition, and repeated SurfacePen/NETwtw10 comparisons.
Accept a default only if correctness remains exact and the time/RSS tradeoff
passes an explicit production objective against both off and lineage. GQ8 and
GQ4 remain unchanged.
