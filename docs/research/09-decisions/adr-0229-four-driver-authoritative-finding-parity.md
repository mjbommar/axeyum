# ADR-0229: Four-driver authoritative finding parity

Status: accepted
Date: 2026-07-17

## Context

Same-query verdict agreement is necessary but does not show that a symbolic
executor finds the same bugs when a different solver chooses models and drives
concretization. Earlier Glaurung experiments showed large both-SAT model
divergence and finding-count changes under different historical policies. The
publication review therefore requires each backend to run as sole exploration
authority and compares stable finding output, not only SAT/UNSAT decisions.

A canonical model-selection policy would be justified if backend-valid model
choices caused durable output divergence. Imposing one before measuring the
current integration could instead hide useful solver freedom and add policy
cost without evidence that the user-visible result needs it.

## Decision

Compile separate Z3-only and Axeyum-only Glaurung binaries and run each as sole
authority over DptfDevGen, vwififlt, IntcSST, and SurfacePen. Enable all raw
finding output, use identical explicit work and time bounds, alternate backend
order for three repetitions, and reject any coverage-bound hit or unstable
within-backend output.

Accept this bounded tier only if the ordered raw finding lists are byte
identical, not merely equal in count or high-confidence display subset. Do not
require canonical model selection when the measured user-visible output is
already identical. Reopen that decision if a timeout-sensitive or wider tier
produces a stable backend-only sink.

## Evidence

All 24 processes are stable, and every driver has exact backend-authority
finding parity:

| Driver | Z3 solves | Axeyum solves | Raw findings | Backend-only sinks |
|---|---:|---:|---:|---:|
| DptfDevGen | 561 | 561 | 17 | 0 / 0 |
| vwififlt | 4,742 | 4,734 | 104 | 0 / 0 |
| IntcSST | 1,672 | 1,668 | 116 | 0 / 0 |
| SurfacePen | 2,551 | 2,551 | 65 | 0 / 0 |

The 302 canonical raw sinks remain byte-identical across all three repetitions
and both authorities, for 1,812 stable emitted rows. Every run preserves its
driver's analyzed/root coverage and stays below all declared bounds.

Exact canonical output, input/source/binary hashes, configurations, arrays,
and exclusions are committed under
[`bench-results/glaurung-authoritative-finding-parity-20260717/`](../../../bench-results/glaurung-authoritative-finding-parity-20260717/README.md).

## Consequences

The publication may state that current four-driver finding output is invariant
to Z3 versus Axeyum authority on the measured bounded tier. It need not add a
canonical model-selection mechanism merely to reproduce these findings.

It may not claim identical exploration: Axeyum makes eight fewer solve calls on
vwififlt and four fewer on IntcSST. Nor may it generalize to timeout-sensitive
or unmeasured driver families. Those differences are reported precisely rather
than normalized away.

The Axeyum-only build cannot emit Glaurung's dual-feature-gated warm lifecycle
footer. This limits the artifact's warm-policy observability but not its sink
comparison; ADR-0228 remains the separate warm hit/fallback/RSS control. The
standalone authority timings also are not substitutes for the fair four-cell
performance statistics in ADR-0215/0217.

## Alternatives

- Compare only finding counts: rejected because distinct sinks can have equal
  cardinality.
- Keep Z3 authoritative and compare shadow verdicts: rejected because it fixes
  exploration before Axeyum can influence it.
- Add canonical model selection immediately: rejected because current exact
  output parity provides no measured need on this tier.
- Generalize four drivers to all Glaurung workloads: rejected; timeout and
  wider-driver evidence remain open.
